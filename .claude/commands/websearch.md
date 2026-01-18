---
description: Search the web using DuckDuckGo
---

Search the web for: {{query}}

## Instructions

Use WebFetch to search DuckDuckGo HTML:

1. Fetch `https://html.duckduckgo.com/html/?q={{query}}` (replace spaces with +)
2. Parse the HTML response to extract search results:
   - Look for `<a rel="nofollow" class="result__a" href="...">Title</a>` for titles and URLs
   - Look for `<a class="result__snippet"...>` for snippets
   - URLs contain `uddg=ENCODED_URL` - decode to get the actual URL
3. Present the top 10 results with title, URL, and snippet
4. If the user needs more details, fetch specific result URLs

Example result format:
1. **Title Here**
   https://example.com/page
   Brief description from the search snippet...
