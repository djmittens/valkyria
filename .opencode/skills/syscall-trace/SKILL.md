---
name: syscall-trace
description: System call tracing with strace (Linux) and dtrace/dtruss (macOS) - trace file I/O, network, signals, and process activity
license: MIT
metadata:
  platform: linux,macos
  category: debugging
---

# System Call Tracing for Valkyria

Trace system calls to understand how the program interacts with the OS - file operations, networking, process management, and more.

## Linux: strace

strace traces system calls and signals on Linux.

### Basic Usage

```bash
# Trace all syscalls
strace build/valk src/prelude.valk

# Trace with output to file
strace -o trace.log build/valk src/prelude.valk

# Attach to running process
strace -p $(pgrep valk)
```

### Filtering Syscalls

```bash
# Trace only specific syscalls
strace -e open,read,write,close build/valk src/prelude.valk

# Trace by category
strace -e trace=file build/valk        # File operations
strace -e trace=network build/valk     # Network operations
strace -e trace=process build/valk     # Process management
strace -e trace=signal build/valk      # Signal operations
strace -e trace=memory build/valk      # Memory mapping
strace -e trace=ipc build/valk         # IPC operations

# Exclude specific syscalls
strace -e trace=!brk,mmap build/valk
```

### Useful Options

```bash
# Timing information
strace -T build/valk          # Time spent in each syscall
strace -t build/valk          # Wall clock time
strace -tt build/valk         # With microseconds
strace -ttt build/valk        # Unix timestamp

# Show strings fully
strace -s 1000 build/valk     # Increase string limit

# Follow forks
strace -f build/valk          # Follow child processes

# Count and summarize
strace -c build/valk          # Summary statistics
strace -C build/valk          # Combined output + summary

# Decode file descriptors
strace -y build/valk          # Show paths for FDs
strace -yy build/valk         # Show socket details too
```

### Practical Examples

```bash
# See what files are being opened
strace -e openat,open -y build/valk src/prelude.valk 2>&1 | grep -v ENOENT

# Trace network activity
strace -e socket,connect,bind,listen,accept,send,recv,read,write \
  -yy build/valk src/prelude.valk

# Find why program is slow (timing)
strace -T -c build/valk src/prelude.valk
# Look for syscalls with high "seconds" or "calls" count

# Trace memory allocations (brk/mmap)
strace -e brk,mmap,munmap,mremap build/valk src/prelude.valk

# Debug signal handling
strace -e signal build/valk src/prelude.valk

# Watch a specific file
strace -e trace=file -P /path/to/watched/file build/valk
```

### Output Format

```
openat(AT_FDCWD, "src/prelude.valk", O_RDONLY) = 3
^^^^^  ^^^^^^^^  ^^^^^^^^^^^^^^^^^^  ^^^^^^^    ^
|      |         |                   |          |
|      |         |                   flags      return value
|      |         path argument
|      first argument
syscall name
```

### Interpreting Errors

```bash
# Common error codes
# ENOENT  = No such file or directory
# EACCES  = Permission denied
# EAGAIN  = Resource temporarily unavailable
# EINTR   = Interrupted system call
# EPERM   = Operation not permitted
# EEXIST  = File exists

# Find failing syscalls
strace build/valk 2>&1 | grep '= -1'
```

## macOS: dtruss/dtrace

macOS uses DTrace for system call tracing. `dtruss` is a wrapper script.

### dtruss (Simple Interface)

```bash
# Basic tracing (requires sudo)
sudo dtruss build/valk src/prelude.valk

# With elapsed time
sudo dtruss -e build/valk src/prelude.valk

# Follow children
sudo dtruss -f build/valk src/prelude.valk

# Trace running process
sudo dtruss -p $(pgrep valk)

# Just one syscall type
sudo dtruss -t open build/valk src/prelude.valk
```

### dtrace (Full Power)

```bash
# Trace all syscalls for a process
sudo dtrace -n 'syscall:::entry /execname == "valk"/ { @[probefunc] = count(); }'

# Trace with arguments
sudo dtrace -n 'syscall::open*:entry /execname == "valk"/ { 
  printf("%s %s", execname, copyinstr(arg0)); 
}'

# Trace file reads with size
sudo dtrace -n 'syscall::read:entry /execname == "valk"/ {
  self->fd = arg0;
}
syscall::read:return /execname == "valk" && self->fd/ {
  printf("read(%d) = %d bytes", self->fd, arg1);
  self->fd = 0;
}'

# System call latency
sudo dtrace -n 'syscall:::entry /execname == "valk"/ { 
  self->ts = timestamp; 
}
syscall:::return /self->ts/ { 
  @[probefunc] = quantize(timestamp - self->ts);
  self->ts = 0; 
}'
```

### dtrace One-Liners

```bash
# Count syscalls by type
sudo dtrace -n 'syscall:::entry /execname=="valk"/ { @[probefunc]=count(); }'

# Show open files
sudo dtrace -n 'syscall::open*:entry /execname=="valk"/ { printf("%s", copyinstr(arg0)); }'

# Network connections
sudo dtrace -n 'syscall::connect:entry /execname=="valk"/ { trace(arg0); }'

# Slow syscalls (>1ms)
sudo dtrace -n 'syscall:::entry /execname=="valk"/ { self->ts=timestamp; }
  syscall:::return /self->ts && (timestamp-self->ts)>1000000/ {
  printf("%s took %d us", probefunc, (timestamp-self->ts)/1000); self->ts=0; }'
```

### macOS SIP Note

System Integrity Protection (SIP) limits DTrace on macOS. For full tracing:
1. Boot to Recovery Mode (Cmd+R at startup)
2. Run: `csrutil enable --without dtrace`
3. Reboot

Or trace only your own processes (works without SIP changes).

## Common Debugging Scenarios

### File Not Found

```bash
# Linux
strace -e openat,access,stat build/valk 2>&1 | grep -E "(ENOENT|No such)"

# macOS
sudo dtruss -t open build/valk 2>&1 | grep -i "no such"
```

### Permission Denied

```bash
# Linux
strace -e openat,access build/valk 2>&1 | grep EACCES

# macOS
sudo dtruss build/valk 2>&1 | grep -i "permission"
```

### Network Issues

```bash
# Linux - trace all network syscalls
strace -e socket,connect,bind,listen,accept4,sendto,recvfrom,setsockopt \
  -yy build/valk 2>&1

# macOS
sudo dtrace -n 'syscall::connect:entry /execname=="valk"/ { trace(arg0); }'
```

### Hanging Process

```bash
# Linux - attach to hung process
strace -p $(pgrep valk)
# See what syscall it's blocked on

# macOS
sudo dtruss -p $(pgrep valk)
```

### Slow Performance

```bash
# Linux - find slow syscalls
strace -c build/valk src/prelude.valk
# Look at "seconds" column

# More detail on slow calls
strace -T build/valk 2>&1 | awk '$NF > 0.01'  # Calls taking >10ms

# macOS
sudo dtrace -n 'syscall:::entry /execname=="valk"/ { self->ts=timestamp; }
syscall:::return /self->ts/ { @[probefunc]=sum(timestamp-self->ts); self->ts=0; }
END { printa(@); }'
```

## Project-Specific Examples

### Debug libuv Event Loop

```bash
# Trace epoll/kqueue operations (Linux)
strace -e epoll_create,epoll_ctl,epoll_wait,epoll_pwait build/valk src/prelude.valk

# macOS (kqueue)
sudo dtrace -n 'syscall::kevent*:entry /execname=="valk"/ { trace(arg0); }'
```

### Debug File Loading

```bash
# See what files valk loads
strace -e openat,read,close -y build/valk src/prelude.valk test/test_prelude.valk 2>&1 \
  | grep -E "\.valk|prelude"
```

### Debug Memory Mapping

```bash
# Linux
strace -e mmap,munmap,mprotect,brk build/valk src/prelude.valk

# macOS
sudo dtruss -t mmap build/valk src/prelude.valk
```

## Tips

1. **Always redirect strace output** - use `-o file` or `2>trace.log`
2. Use `-f` to follow child processes
3. Use `-y` to decode file descriptors
4. Use `-T` to find slow syscalls
5. Use `-c` for a quick summary
6. Filter early with `-e` to reduce noise
7. On macOS, dtruss requires sudo
8. DTrace scripts can be saved to `.d` files for reuse
9. Combine with grep to find specific patterns
10. Use `-s 1000` to see full string arguments
