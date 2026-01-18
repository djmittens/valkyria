# Coverage Improvement

## Requirements
- **90% line coverage** 
- **85% branch coverage**

## Current Status

Run `make coverage` to see current state. Focus on files failing branch coverage.

## Strategy

1. Use `python3 scripts/find-uncovered-branches.py <file.c>` to find uncovered branches
2. Read source at those lines to understand the condition
3. Write tests that hit the UNTESTED branch specifically
4. Verify branch % increased with `make coverage`

## Acceptance Criteria

- [ ] All src/ files ≥90% line coverage
- [ ] All src/ files ≥85% branch coverage  
- [ ] `make coverage` shows 0 failing files
