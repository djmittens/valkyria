# Valkyria Development Roadmap

## Current Status: Phase 0 - Shift/Reset Continuations

The project is 75-80% complete. We're replacing the ARC-based async system with delimited continuations for simpler, more powerful concurrency.

## Phases

### [Phase 0: Shift/Reset Continuations](phase0_continuations.md) (6 weeks) - **CURRENT**
Replace futures/promises with delimited continuations

### [Phase 1: Complete Networking](phase1_networking.md) (2 weeks)
Finish HTTP/2 server and validate with production app

### [Phase 2: Bytecode Compiler](phase2_bytecode.md) (3 weeks)
Complete bytecode compilation for 10-100x performance

### [Phase 3: Production Ready](phase3_production.md) (4 weeks)
Module system, standard library, developer tools

## Quick Links

- [Current Phase Details](phase0_continuations.md)
- [Technical Decisions](decisions.md)
- [Migration Guide](migration.md)

## Timeline

- **Now - Week 6**: Phase 0 (Continuations)
- **Week 7-8**: Phase 1 (Networking)
- **Week 9-11**: Phase 2 (Bytecode)
- **Week 12-15**: Phase 3 (Production)

**Target**: Production ready in 15 weeks