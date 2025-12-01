---
description: Ask the valkyria-compiler expert using RAG (search knowledge base and provide context)
---

You are helping the user with compiler development questions using the valkyria-compiler knowledge base.

IMPORTANT: Follow these steps to answer the question:

1. **Search the knowledge base** using the almanac-rag tool:
   ```bash
   ~/src/expert-lab/.venv/bin/python ~/src/expert-lab/bin/almanac-rag "{{question}}" --top-k 10
   ```

2. **Analyze the search results** to understand what information is available

3. **Answer the user's question** concisely using the context from the search results. Include:
   - Direct answer to their question (2-3 paragraphs max)
   - Most relevant code snippet (if applicable)
   - 2-3 key file references (format: `file:line`)
   - If multiple approaches exist, briefly explain tradeoffs

4. **If search results are insufficient**:
   - Clearly state what information is missing
   - Suggest related topics that were found
   - Ask clarifying questions if needed

## Response Format

Structure your response like this:

### Answer
[Your direct answer using the search results]

### Relevant Code/Context
[Show the most relevant snippets with file references]

### Additional References
- `file:line` - brief description
- `file:line` - brief description

---

**User's Question**: {{question}}
