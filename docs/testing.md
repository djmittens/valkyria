# Test Framework

For testing the C runtime, i have created a fun framework and now i get to
implement whatever features i need

- [ ] Distributed test runner
    - Using ipc be able to run other test artifacts
- [ ] Argument parsing and printing I would like to have proper argument
    support, i dont know how to implement it necessarily
- [ ] Globbing
    -  Just a simple implementation to hold us over. And shit.
- [ ] Central test runner
- [ ] Filter tests based on a regular expression (and the name).
- [ ] Animated progress while running
    - [ ] Can i detect the terminal, and if its used as stdin /stdout pipe,
    turn animations off
- [ ] Test parametrization through runtime
    - [ ] Accept custom arguments from the user
    - [ ] Accept random seed from user.
- [ ] Sandboxed processes that can crash and report on segfaults.
- [ ] Distributed workers (maybe even remote workers / runners?)
- [ ] Capturing stderr / stdout only on failure tests
    - Intercept these for the process, and only print it on error
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
