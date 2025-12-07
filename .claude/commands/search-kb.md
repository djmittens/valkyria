---
description: Search expert knowledge bases - automatically routes to the right KB (compiler or dashboard)
---

Search the knowledge bases for: {{query}}

## Routing Instructions

Analyze the query and determine which knowledge base to search:

### For compiler/language topics:
(parser, AST, IR, LLVM, JIT, codegen, optimization, type system, GC, runtime, bytecode, VM)
```bash
~/src/expert-lab/.venv/bin/python ~/src/expert-lab/bin/almanac-rag "{{query}}" --expert valkyria-compiler --top-k 10
```

### For dashboard/frontend topics:
(UI, CSS, JavaScript, React, chart, visualization, WebGL, canvas, DOM, component, design)
```bash
~/src/expert-lab/.venv/bin/python ~/src/expert-lab/bin/almanac-rag "{{query}}" --expert frontend-dashboard-design --top-k 10
```

### If unclear, search both:
```bash
~/src/expert-lab/.venv/bin/python ~/src/expert-lab/bin/almanac-rag "{{query}}" --expert valkyria-compiler --top-k 5
~/src/expert-lab/.venv/bin/python ~/src/expert-lab/bin/almanac-rag "{{query}}" --expert frontend-dashboard-design --top-k 5
```

State which expert(s) you searched and display the results.
