# Debugging

# GDB
Use this example `.gdbinit` file to setup debugging such that it stays attached
both to parent and forked processes, this doesnt happen by default

```bash
set debuginfod enabled on

# Debug child process
#set follow-fork-mode child
#set breakpoint pending on

#Debug both parent and child
set follow-fork-mode parent      # stay with the original PID
set detach-on-fork off           # OR stay attached to *both* ends
set schedule-multiple on         # (if you want to examine both tasks concurrently)
#break aio_uv.c:130
```
