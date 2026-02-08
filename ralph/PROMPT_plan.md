# PLAN Stage: Gap Analysis for {{SPEC_FILE}}

## Step 1: Understand Current State

1. Run `ralph query` to see current state
2. Read the spec file: `ralph/specs/{{SPEC_FILE}}`

## Step 2: Research with Subagents

Your context window is LIMITED. Do NOT read many files yourself.

**Launch subagents in parallel to research different aspects. Each subagent MUST return structured findings:**

```
Task: "Research [requirement] for spec {{SPEC_FILE}}

Analyze the codebase and return a JSON object:
{
  \"requirement\": \"<spec requirement being researched>\",
  \"current_state\": \"<what exists now - implemented/partial/missing>\",
  \"files_to_modify\": [
    {\"path\": \"src/foo.py\", \"lines\": \"100-150\", \"what\": \"extract X function\", \"how\": \"move to new module Y\"}
  ],
  \"files_to_create\": [
    {\"path\": \"src/bar.py\", \"template\": \"similar to src/existing.py\", \"purpose\": \"new module for Z\"}
  ],
  \"imports_needed\": [\"from X import Y\", \"from Z import W\"],
  \"dependencies\": {
    \"internal\": [\"requires module A to exist first\"],
    \"external\": [\"needs package X installed\"]
  },
  \"patterns_to_follow\": \"<reference similar existing code>\",
  \"spec_section\": \"<which section of spec defines this requirement>\",
  \"risks\": [\"could break if X\", \"depends on Y being complete\"],
  \"verification\": \"<how to verify this works: specific command + expected output>\"
}"
```

Launch multiple Task calls in a single message to parallelize research.

## Step 3: Create Tasks from Research

For each gap identified, create a task that **captures the research findings**:

```
ralph task add '{"name": "Short task name", "notes": "<DETAILED>", "accept": "<MEASURABLE>", "deps": ["t-xxxx"], "research": {"files_analyzed": ["path:lines"], "spec_section": "Section"}}'
```

## Task Field Requirements

### `notes` (required) - MUST INCLUDE ALL OF:

1. **Source locations**: Exact file paths with line numbers (e.g., "Source: src/foo.py lines 100-150")
2. **What to do**: Specific actions with targets
3. **How to do it**: Implementation approach or pattern to follow
4. **Imports/Dependencies**: What's needed
5. **Spec reference**: Which spec section
6. **Risks/Prerequisites**: What could go wrong

**Notes Template:**
```
Source: <file> lines <N-M>. <What to extract/modify>. 
Imports needed: <list>. Pattern: follow <similar code>. 
Spec ref: <section>. Prerequisites: <deps>. 
Risk: <what to watch for>.
```

### `accept` (required) - MUST BE:

1. **Specific**: Name exact files, commands, outputs
2. **Measurable**: Has concrete pass/fail condition
3. **Executable**: Can run command and check result

**Good examples:**
- `test -f ralph/tui/fallback.py && python3 -c "from ralph.tui.fallback import X" exits 0`
- `pytest ralph/tests/unit/test_parser.py passes`
- `grep -c 'pattern' file.py returns 1`

**Bad examples (WILL BE REJECTED):**
- "works correctly" - not measurable
- "tests pass" - which tests?

### `research` (optional but recommended)

Structured research findings:
```json
{"files_analyzed": ["file:lines"], "patterns_found": "...", "spec_section": "..."}
```

## Validation

Tasks are validated. REJECTED if:
- Notes < 50 chars or missing file paths
- Modification tasks without line numbers or function names
- Acceptance criteria is vague ("works correctly", "is implemented")

## Output

When done:
```
[RALPH] PLAN_COMPLETE: Added N tasks for {{SPEC_FILE}}
```
