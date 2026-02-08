#include "valk_thread.h"

#ifdef VALK_PLATFORM_POSIX

#include <errno.h>

int valk_mutex_init(valk_mutex_t* mutex) {
  return pthread_mutex_init(mutex, nullptr);
}

int valk_mutex_destroy(valk_mutex_t* mutex) {
  return pthread_mutex_destroy(mutex);
}

int valk_mutex_lock(valk_mutex_t* mutex) {
  return pthread_mutex_lock(mutex);
}

int valk_mutex_unlock(valk_mutex_t* mutex) {
  return pthread_mutex_unlock(mutex);
}

int valk_cond_init(valk_cond_t* cond) {
  return pthread_cond_init(cond, nullptr);
}

int valk_cond_destroy(valk_cond_t* cond) {
  return pthread_cond_destroy(cond);
}

int valk_cond_signal(valk_cond_t* cond) {
  return pthread_cond_signal(cond);
}

int valk_cond_broadcast(valk_cond_t* cond) {
  return pthread_cond_broadcast(cond);
}

int valk_cond_wait(valk_cond_t* cond, valk_mutex_t* mutex) {
  return pthread_cond_wait(cond, mutex);
}

int valk_cond_timedwait(valk_cond_t* cond, valk_mutex_t* mutex, u32 timeout_ms) {
  struct timespec ts;
  clock_gettime(CLOCK_REALTIME, &ts);
  ts.tv_sec += timeout_ms / 1000;
  ts.tv_nsec += (timeout_ms % 1000) * 1000000;
  if (ts.tv_nsec >= 1000000000) { // LCOV_EXCL_BR_LINE
    ts.tv_sec += 1;
    ts.tv_nsec -= 1000000000;
  }
  return pthread_cond_timedwait(cond, mutex, &ts);
}

int valk_thread_create(valk_thread_t* thread, valk_thread_attr_t* attr,
                       valk_thread_fn fn, void* arg) {
  return pthread_create(thread, attr, fn, arg);
}

int valk_thread_join(valk_thread_t thread, void** retval) {
  return pthread_join(thread, retval);
}

valk_thread_t valk_thread_self(void) {
  return pthread_self();
}

bool valk_thread_equal(valk_thread_t a, valk_thread_t b) {
  return pthread_equal(a, b) != 0;
}

#endif
