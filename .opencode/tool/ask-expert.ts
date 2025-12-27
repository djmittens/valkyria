import { tool } from "@opencode-ai/plugin"

export default tool({
  description: `Ask an expert using RAG - automatically routes to the right knowledge base.

Available experts:
- valkyria-compiler: Compilers, interpreters, LLVM, JIT, type systems, parsing, AST, IR, code generation, optimization, garbage collection, memory management, bytecode, virtual machines, language design
- frontend-dashboard-design: Frontend development, dashboards, UI/UX, data visualization, WebGL, WebGPU, Canvas, CSS, JavaScript, TypeScript, React patterns, design systems

The tool will route your question to the appropriate expert(s) based on the content.`,
  args: {
    question: tool.schema.string().describe("The question to ask the expert"),
    expert: tool.schema
      .enum(["valkyria-compiler", "frontend-dashboard-design", "both"])
      .optional()
      .describe(
        "Which expert to query. If not specified, will be auto-detected from the question."
      ),
    prioritize_docs: tool.schema
      .boolean()
      .optional()
      .describe(
        "Set to true for conceptual/design questions (how/why/explain/tradeoffs)"
      ),
  },
  async execute(args, context) {
    const { question, expert, prioritize_docs } = args
    const docsFlag = prioritize_docs ? " --prioritize-docs" : ""
    const ragCmd = `~/src/expert-lab/.venv/bin/python ~/src/expert-lab/bin/almanac-rag`

    let selectedExpert = expert

    // Auto-detect expert if not specified
    if (!selectedExpert) {
      const compilerKeywords =
        /compiler|parser|lexer|ast|ir|llvm|jit|codegen|optimization|type|inference|generics|garbage|collection|runtime|bytecode|vm|interpreter|memory|gc|allocat/i
      const frontendKeywords =
        /dashboard|frontend|ui|ux|css|javascript|typescript|react|chart|graph|visualization|webgl|webgpu|canvas|rendering|browser|dom|component|design|layout|responsive/i

      const isCompiler = compilerKeywords.test(question)
      const isFrontend = frontendKeywords.test(question)

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
      const proc1 = Bun.spawn(["bash", "-c", `${ragCmd} "${question}" --expert valkyria-compiler --top-k 25${docsFlag}`])
      const proc2 = Bun.spawn(["bash", "-c", `${ragCmd} "${question}" --expert frontend-dashboard-design --top-k 25${docsFlag}`])

      const [out1, out2] = await Promise.all([
        new Response(proc1.stdout).text(),
        new Response(proc2.stdout).text(),
      ])

      results.push(`## Compiler Expert Results\n\n${out1}`)
      results.push(`## Frontend Expert Results\n\n${out2}`)
    } else {
      const proc = Bun.spawn(["bash", "-c", `${ragCmd} "${question}" --expert ${selectedExpert} --top-k 50${docsFlag}`])
      const output = await new Response(proc.stdout).text()
      results.push(`## ${selectedExpert} Expert Results\n\n${output}`)
    }

    return results.join("\n\n---\n\n")
  },
})
