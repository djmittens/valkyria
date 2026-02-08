#include "memory.h"

#include <string.h>

#if defined(__linux__)
#include <sys/resource.h>
#include <unistd.h>

void valk_process_memory_collect(valk_process_memory_t *pm) {
  if (pm == nullptr) return;
  memset(pm, 0, sizeof(*pm));

  // LCOV_EXCL_BR_START - OS syscall success checks
  long page_size = sysconf(_SC_PAGESIZE);

  long phys_pages = sysconf(_SC_PHYS_PAGES);
  if (phys_pages > 0 && page_size > 0) {
    pm->system_total_bytes = (u64)phys_pages * page_size;
  }

  FILE *f = fopen("/proc/self/statm", "r");
  if (f) {
    unsigned long size, resident, shared, text, lib, data, dirty;
    if (fscanf(f, "%lu %lu %lu %lu %lu %lu %lu",
               &size, &resident, &shared, &text, &lib, &data, &dirty) >= 4) {
      pm->vms_bytes = size * page_size;
      pm->rss_bytes = resident * page_size;
      pm->shared_bytes = shared * page_size;
      pm->data_bytes = data * page_size;
    }
    fclose(f);
  }

  struct rusage ru;
  if (getrusage(RUSAGE_SELF, &ru) == 0) {
    pm->page_faults_minor = ru.ru_minflt;
    pm->page_faults_major = ru.ru_majflt;
  }
  // LCOV_EXCL_BR_STOP
}

#elif defined(__APPLE__)
#include <mach/mach.h>
#include <sys/resource.h>
#include <sys/sysctl.h>

void valk_process_memory_collect(valk_process_memory_t *pm) {
  if (pm == nullptr) return;
  memset(pm, 0, sizeof(*pm));

  // LCOV_EXCL_BR_START - OS syscall success checks
  int mib[2] = {CTL_HW, HW_MEMSIZE};
  u64 memsize = 0;
  size_t len = sizeof(memsize);
  if (sysctl(mib, 2, &memsize, &len, nullptr, 0) == 0) {
    pm->system_total_bytes = (u64)memsize;
  }

  mach_task_basic_info_data_t info;
  mach_msg_type_number_t count = MACH_TASK_BASIC_INFO_COUNT;

  if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO,
                (task_info_t)&info, &count) == KERN_SUCCESS) {
    pm->rss_bytes = info.resident_size;
    pm->vms_bytes = info.virtual_size;
  }

  struct rusage ru;
  if (getrusage(RUSAGE_SELF, &ru) == 0) {
    pm->page_faults_minor = ru.ru_minflt;
    pm->page_faults_major = ru.ru_majflt;
  }
  // LCOV_EXCL_BR_STOP
}

#else
void valk_process_memory_collect(valk_process_memory_t *pm) {
  if (pm == nullptr) return;
  memset(pm, 0, sizeof(*pm));
}
#endif

// =============================================================================
// Detailed smaps breakdown (Linux only)
// =============================================================================

#if defined(__linux__)

typedef enum {
  SMAPS_REGION_HEAP,
  SMAPS_REGION_STACK,
  SMAPS_REGION_ANON,
  SMAPS_REGION_FILE,
  SMAPS_REGION_URING,
  SMAPS_REGION_SPECIAL,
} smaps_region_type_e;

// LCOV_EXCL_BR_START - depends on /proc/self/smaps content
static smaps_region_type_e categorize_smaps_region(const char *name) {
  if (strstr(name, "[heap]")) {
    return SMAPS_REGION_HEAP;
  }
  if (strstr(name, "[stack]") || strstr(name, "stack:")) {
    return SMAPS_REGION_STACK;
  }
  if (strstr(name, "[vdso]") || strstr(name, "[vvar]") || strstr(name, "[vsyscall]")) {
    return SMAPS_REGION_SPECIAL;
  }
  if (strstr(name, "io_uring")) {
    return SMAPS_REGION_URING;
  }
  if (name[0] == '\0') {
    return SMAPS_REGION_ANON;
  }
  if (name[0] == '/') {
    return SMAPS_REGION_FILE;
  }
  return SMAPS_REGION_SPECIAL;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - depends on /proc/self/smaps content
static const char *extract_smaps_pathname(const char *line, char *out_name, sz out_size) {
  out_name[0] = '\0';
  int spaces = 0;
  const char *name_start = nullptr;
  for (const char *p = line; *p; p++) {
    if (*p == ' ') {
      spaces++;
      if (spaces == 5) {
        while (*p == ' ') p++;
        name_start = p;
        break;
      }
    }
  }
  if (name_start) {
    sz len = strlen(name_start);
    if (len > 0 && name_start[len - 1] == '\n') len--;
    if (len >= out_size) len = out_size - 1;
    memcpy(out_name, name_start, len);
    out_name[len] = '\0';
  }
  return out_name;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - depends on /proc/self/smaps content and file access
void valk_smaps_collect(valk_smaps_breakdown_t *smaps) {
  if (smaps == nullptr) return;
  memset(smaps, 0, sizeof(*smaps));

  FILE *f = fopen("/proc/self/smaps", "r");
  if (!f) return;

  char line[512];
  char current_name[256] = {0};
  smaps_region_type_e region_type = SMAPS_REGION_SPECIAL;

  while (fgets(line, sizeof(line), f)) {
    if (line[0] != ' ' && strchr(line, '-')) {
      extract_smaps_pathname(line, current_name, sizeof(current_name));
      region_type = categorize_smaps_region(current_name);

      if (region_type == SMAPS_REGION_ANON) {
        smaps->anon_regions++;
      } else if (region_type == SMAPS_REGION_FILE) {
        smaps->file_regions++;
      }
    }

    if (strncmp(line, "Rss:", 4) == 0) {
      u64 rss_kb = 0;
      if (sscanf(line, "Rss: %llu kB", &rss_kb) == 1) {
        u64 rss_bytes = rss_kb * 1024;
        switch (region_type) {
          case SMAPS_REGION_HEAP:   smaps->heap_rss += rss_bytes; break;
          case SMAPS_REGION_STACK:  smaps->stack_rss += rss_bytes; break;
          case SMAPS_REGION_URING:  smaps->uring_rss += rss_bytes; break;
          case SMAPS_REGION_ANON:   smaps->anon_rss += rss_bytes; break;
          case SMAPS_REGION_FILE:   smaps->file_rss += rss_bytes; break;
          case SMAPS_REGION_SPECIAL: smaps->other_rss += rss_bytes; break;
        }
        smaps->total_rss += rss_bytes;
      }
    }

    if (strncmp(line, "Shmem:", 6) == 0) {
      u64 shmem_kb = 0;
      if (sscanf(line, "Shmem: %llu kB", &shmem_kb) == 1) {
        smaps->shmem_rss += shmem_kb * 1024;
      }
    }
  }

  fclose(f);
}
// LCOV_EXCL_BR_STOP

#elif defined(__APPLE__)
#include <mach/mach.h>
#include <mach/mach_vm.h>

void valk_smaps_collect(valk_smaps_breakdown_t *smaps) {
  if (smaps == nullptr) return;
  memset(smaps, 0, sizeof(*smaps));

  task_t task = mach_task_self();
  mach_vm_address_t address = 0;
  mach_vm_size_t size = 0;
  vm_region_basic_info_data_64_t info;
  mach_msg_type_number_t info_count;
  mach_port_t object_name;

  while (1) {
    info_count = VM_REGION_BASIC_INFO_COUNT_64;
    kern_return_t kr = mach_vm_region(task, &address, &size,
                                       VM_REGION_BASIC_INFO_64,
                                       (vm_region_info_t)&info,
                                       &info_count, &object_name);
    if (kr != KERN_SUCCESS) break;

    u64 region_size = (u64)size;

    if (info.shared) {
      smaps->shmem_rss += region_size;
    } else {
      smaps->anon_rss += region_size;
      smaps->anon_regions++;
    }

    smaps->total_rss += region_size;
    address += size;
  }

  // LCOV_EXCL_BR_START - macOS memory region heuristics
  if (smaps->anon_rss > 0) {
    smaps->heap_rss = smaps->anon_rss / 20;
    smaps->anon_rss -= smaps->heap_rss;
  }
  // LCOV_EXCL_BR_STOP
}

#else
void valk_smaps_collect(valk_smaps_breakdown_t *smaps) {
  if (smaps == nullptr) return;
  memset(smaps, 0, sizeof(*smaps));
}
#endif
