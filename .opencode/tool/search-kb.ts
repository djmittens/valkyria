import { tool } from "@opencode-ai/plugin"

export default tool({
  description: `Search expert knowledge bases - automatically routes to the right KB.

Available knowledge bases:
- valkyria-compiler: parser, AST, IR, LLVM, JIT, codegen, optimization, type system, GC, runtime, bytecode, VM
- frontend-dashboard-design: UI, CSS, JavaScript, React, chart, visualization, WebGL, canvas, DOM, component, design`,
  args: {
    query: tool.schema.string().describe("The search query"),
    expert: tool.schema
      .enum(["valkyria-compiler", "frontend-dashboard-design", "both"])
      .optional()
      .describe(
        "Which knowledge base to search. If not specified, will be auto-detected from the query."
      ),
    top_k: tool.schema
      .number()
      .optional()
      .describe("Number of results to return (default: 10)"),
  },
  async execute(args, context) {
    const { query, expert, top_k = 10 } = args
    const ragCmd = `~/src/expert-lab/.venv/bin/python ~/src/expert-lab/bin/almanac-rag`

    let selectedExpert = expert

    // Auto-detect expert if not specified
    if (!selectedExpert) {
      const compilerKeywords =
        /compiler|parser|lexer|ast|ir|llvm|jit|codegen|optimization|type|inference|generics|garbage|collection|runtime|bytecode|vm|interpreter|memory|gc|allocat/i
      const frontendKeywords =
        /dashboard|frontend|ui|ux|css|javascript|typescript|react|chart|graph|visualization|webgl|webgpu|canvas|rendering|browser|dom|component|design|layout|responsive/i

      const isCompiler = compilerKeywords.test(query)
      const isFrontend = frontendKeywords.test(query)

      if (isCompiler && isFrontend) {
        selectedExpert = "both"
      } else if (isFrontend) {
        selectedExpert = "frontend-dashboard-design"
      } else {
        selectedExpert = "valkyria-compiler" // default
      }
    }

    const results: string[] = []

    if (selectedExpert === "both") {
      const k = Math.ceil(top_k / 2)
      const proc1 = Bun.spawn(["bash", "-c", `${ragCmd} "${query}" --expert valkyria-compiler --top-k ${k}`])
      const proc2 = Bun.spawn(["bash", "-c", `${ragCmd} "${query}" --expert frontend-dashboard-design --top-k ${k}`])

      const [out1, out2] = await Promise.all([
        new Response(proc1.stdout).text(),
        new Response(proc2.stdout).text(),
      ])

      results.push(`## Compiler KB Results\n\n${out1}`)
      results.push(`## Frontend KB Results\n\n${out2}`)
    } else {
      const proc = Bun.spawn(["bash", "-c", `${ragCmd} "${query}" --expert ${selectedExpert} --top-k ${top_k}`])
      const output = await new Response(proc.stdout).text()
      results.push(`## ${selectedExpert} KB Results\n\n${output}`)
    }

    return results.join("\n\n---\n\n")
  },
})
