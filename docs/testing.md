# Test Framework

For testing the C runtime, i have created a fun framework and now i get to
implement whatever features i need

- [x] Capturing stderr / stdout only on failure tests
    - Intercept these for the process, and only print it on error
- [ ] ASAN integration
    - [ ] Swap in malloc instead of custom allocators
    - [ ] Disable process forking, run everything in the parent process one at
        a time
- [ ] Valk Test runner
    - [ ] Animated spinner
    - [ ] Pooled execution
    - [ ] Argument parsing and printing I would like to have proper argument
        support, i dont know how to implement it necessarily
    - [ ] Globbing
        -  Just a simple implementation to hold us over. And shit.
        - [ ] Filter tests based on a regular expression (and the name).
    - [ ] Test tagging
        - Slow tests should be disabled by default, only enabled in CI
    - [ ] Standard junit output
    - [ ] C code coverage
    - [ ] Valk code coverage
- [ ] Distributed test runner
    - [ ] Run tests over network (maybe internet?)
    - [ ] pub / sub queue
- [ ] Animated progress while running
    - [ ] Can i detect the terminal, and if its used as stdin /stdout pipe,
    turn animations off
- [ ] Test parametrization through runtime
    - [ ] Accept custom arguments from the user
    - [ ] Accept random seed from user.
- [ ] Sandboxed processes that can crash and report on segfaults.
- [ ] Distributed workers (maybe even remote workers / runners?)
- [ ] Dynamic test conditions such that for parametrized tests we can stress,
    random numbers for a period and report on any failures found
    - For this specifically i would like to have 2 modes, fail fast and try X
    times, or collect at least X errors or timeout reached
    - This will aid in concurrency based test runs over time.
- [ ] Benchmarking support for tests. (maybe a special mode for that with
    parameters?)
- [ ] Randomness and selection routines
    - Test should be reproducible and random see should be configured globally
    for the run for it to be reproducible.
    - should be passable through the test harness arguments
- [ ] Support for regression seeds, to be run at every test run
- [ ] My own random algorithm to make tests extra deterministic across
    platforms
