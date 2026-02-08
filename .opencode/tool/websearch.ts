import { tool } from "@opencode-ai/plugin"

export default tool({
  description: `Search the web using DuckDuckGo.

Returns a list of search results with titles, URLs, and snippets.
Use this to find documentation, tutorials, GitHub repos, or any web content.`,
  args: {
    query: tool.schema.string().describe("The search query"),
    max_results: tool.schema
      .number()
      .optional()
      .describe("Maximum number of results to return (default: 10, max: 20)"),
  },
  async execute(args, context) {
    const { query, max_results = 10 } = args
    const limit = Math.min(max_results, 20)

    const encodedQuery = encodeURIComponent(query)
    const url = `https://html.duckduckgo.com/html/?q=${encodedQuery}`

    const response = await fetch(url, {
      headers: {
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
      },
    })

    if (!response.ok) {
      return `Error: DuckDuckGo returned status ${response.status}`
    }

    const html = await response.text()

    // Parse search results from HTML
    const results: { title: string; url: string; snippet: string }[] = []

    // Match result blocks - DuckDuckGo uses class="result" divs
    const resultRegex = /<a rel="nofollow" class="result__a" href="([^"]+)"[^>]*>([^<]+)<\/a>[\s\S]*?<a class="result__snippet"[^>]*>([\s\S]*?)<\/a>/g

    let match
    while ((match = resultRegex.exec(html)) !== null && results.length < limit) {
      const rawUrl = match[1]
      const title = match[2].trim()
      const snippet = match[3]
        .replace(/<\/?b>/g, "")
        .replace(/&amp;/g, "&")
        .replace(/&lt;/g, "<")
        .replace(/&gt;/g, ">")
        .replace(/&quot;/g, '"')
        .replace(/&#x27;/g, "'")
        .replace(/\s+/g, " ")
        .trim()

      // Extract actual URL from DuckDuckGo redirect
      let finalUrl = rawUrl
      const uddgMatch = rawUrl.match(/uddg=([^&]+)/)
      if (uddgMatch) {
        finalUrl = decodeURIComponent(uddgMatch[1])
      }

      results.push({ title, url: finalUrl, snippet })
    }

    if (results.length === 0) {
      return `No results found for: ${query}`
    }

    // Format results
    const formatted = results
      .map((r, i) => `${i + 1}. **${r.title}**\n   ${r.url}\n   ${r.snippet}`)
      .join("\n\n")

    return `## Search Results for: ${query}\n\n${formatted}`
  },
})
