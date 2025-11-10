# CI System Path

## Vision: Programmable CI/CD in Lisp

Build a CI/CD system where pipelines are **real programs**, not YAML configuration. Enable dynamic pipelines, composable workflows, and live debugging of build processes.

## Why CI Systems?

**CI validates different requirements:**
- Async I/O (webhooks, API calls)
- Process execution (running build commands)
- File system operations (workspaces, artifacts)
- String processing (log parsing, output formatting)
- JSON/YAML parsing (configs, API responses)
- Error handling (build failures, retries)

**If Valkyria works for CI, it validates server/automation use cases.**

## Target Experience

```lisp
; pipeline.valk - CI pipeline as real code

(pipeline "valkyria-ci"
  :triggers [:push :pull-request]
  :env {:RUST_VERSION "1.75"
        :NODE_VERSION "20"}

  :steps [
    (step "checkout"
      (git/clone (env "REPO_URL") "/workspace")
      (git/checkout (env "BRANCH")))

    (step "build"
      :parallel [
        (exec "cargo" "build" "--release")
        (exec "npm" "run" "build")])

    (step "test"
      :timeout 600
      (let [result (exec "cargo" "test")]
        (when (failed? result)
          (notify/slack "#eng" (format "Tests failed: ~a" (stderr result)))
          (fail! "Tests failed"))))

    (step "deploy"
      :when (and (== (env "BRANCH") "main")
                 (== (env "EVENT") "push"))
      (docker/push "myapp:latest")
      (k8s/deploy "production" "myapp:latest"))])
```

**In REPL (while pipeline running):**
```lisp
> (pipeline/status "valkyria-ci")
{:status :running :step "test" :elapsed 45.2}

> (pipeline/logs "valkyria-ci" "test")
"running tests... test_parser ... ok\ntest_vm ... ok\n..."

> ; Cancel running pipeline
> (pipeline/cancel "valkyria-ci")
```

## Phases

### Phase 1: Networking Foundation (Current)
**Status**: In progress
**Timeline**: 3 weeks
**See**: `NETWORKING_BRANCH_TASKS.md`

**Deliverables:**
- HTTP server/client (for webhooks and APIs)
- Async I/O with futures
- Test framework
- REPL safety basics

**Why needed for CI**: Receive GitHub/GitLab webhooks, call APIs to report status.

---

### Phase 2: Systems Primitives (CRITICAL FOR CI)
**Timeline**: 3-4 weeks after Phase 1
**Estimated effort**: 15-20 days

#### Task 2.1: Process Execution (4-5 days)

**Goal**: Run external commands from Lisp.

**Lisp API:**
```lisp
; Synchronous execution
(def {result} (exec "ls" "-la" "/tmp"))
(print (process-stdout result))
(print (process-stderr result))
(print (process-exit-code result))

; Async execution (returns future)
(def {future} (spawn "npm" "test"))
(def {result} (await future))

; With options
(exec "cargo" "build"
      :cwd "/workspace"
      :env {:RUST_VERSION "1.75"}
      :timeout 300)

; Streaming output
(exec-stream "pytest" "--verbose"
  (fn [line] (print ">>> " line)))
```

**C implementation:**
```c
// src/process.c - New file
typedef struct {
    pid_t pid;
    int stdin_fd;
    int stdout_fd;
    int stderr_fd;
    int exit_code;
    bool running;
} valk_process_t;

valk_process_t* valk_process_spawn(const char* cmd, char** args, char** env);
int valk_process_wait(valk_process_t* proc);
void valk_process_kill(valk_process_t* proc);
```

**Builtin functions:**
- `valk_builtin_exec()` - Synchronous execution
- `valk_builtin_spawn()` - Async execution
- `valk_builtin_process_stdout()`
- `valk_builtin_process_stderr()`
- `valk_builtin_process_exit_code()`
- `valk_builtin_process_kill()`

**Platform considerations:**
- Unix: fork/exec, pipe, waitpid
- Windows: CreateProcess, pipes
- Handle signals (SIGCHLD)

**Testing:**
- Execute simple commands (echo, ls)
- Capture stdout/stderr
- Test exit codes
- Test timeouts
- Test process killing
- Test environment variables

---

#### Task 2.2: File System Operations (3-4 days)

**Goal**: Read, write, and manipulate files from Lisp.

**Lisp API:**
```lisp
; Read files
(def {content} (file/read "config.yaml"))
(def {lines} (file/read-lines "log.txt"))
(def {exists} (file/exists? "build.log"))

; Write files
(file/write "output.txt" "Hello, World!")
(file/append "log.txt" "New log entry\n")

; File info
(def {size} (file/size "binary.exe"))
(def {mtime} (file/modified-time "src/main.c"))

; Directory operations
(def {files} (dir/list "/workspace"))
(dir/create "/tmp/build")
(dir/delete "/tmp/old-build")

; Path operations
(def {abs} (path/absolute "relative/path"))
(def {joined} (path/join "/workspace" "src" "main.c"))
(def {basename} (path/basename "/foo/bar/baz.txt"))  ; "baz.txt"
(def {dirname} (path/dirname "/foo/bar/baz.txt"))     ; "/foo/bar"
```

**C implementation:**
```c
// Use existing valk_aio_read_file, extend with:
valk_future* valk_aio_write_file(valk_aio_system_t* sys,
                                   const char* path, const char* content);
bool valk_file_exists(const char* path);
int64_t valk_file_size(const char* path);
char** valk_dir_list(const char* path, int* count);
int valk_dir_create(const char* path);
```

**Builtin functions:**
- `valk_builtin_file_read()`
- `valk_builtin_file_write()`
- `valk_builtin_file_exists()`
- `valk_builtin_dir_list()`
- `valk_builtin_path_join()`

**Platform considerations:**
- Unix: open, read, write, stat, opendir, readdir
- Windows: CreateFile, ReadFile, WriteFile, FindFirstFile

**Testing:**
- Read existing files
- Write new files
- Append to files
- List directories
- Create/delete directories
- Path manipulation

---

#### Task 2.3: JSON Parsing (2-3 days)

**Goal**: Parse and generate JSON for API integration.

**Lisp API:**
```lisp
; Parse JSON to Lisp data structures
(def {data} (json/parse "{\"name\": \"valkyria\", \"version\": 1}"))
; => {:name "valkyria" :version 1}

; Generate JSON from Lisp
(def {json-str} (json/stringify {:status "success" :code 0}))
; => "{\"status\":\"success\",\"code\":0}"

; Pretty print
(def {pretty} (json/stringify data :pretty true))
```

**C implementation:**
- Use `cJSON` library (lightweight, ~500 LOC, single file)
- Or write custom parser (recursive descent, ~300 lines)

**Type mapping:**
```
JSON Type     Lisp Type
null          nil
true          1
false         0
number        LVAL_NUM
string        LVAL_STR
array         LVAL_QEXPR (list)
object        LVAL_QEXPR (alist: {{"key" value} {"key2" value2}})
```

**Builtin functions:**
- `valk_builtin_json_parse()`
- `valk_builtin_json_stringify()`

**Testing:**
- Parse valid JSON
- Parse nested objects/arrays
- Generate JSON
- Round-trip (parse -> stringify -> parse)
- Error handling (invalid JSON)

---

#### Task 2.4: String Utilities (2-3 days)

**Goal**: String manipulation for log parsing and formatting.

**Lisp API:**
```lisp
; String operations
(def {parts} (str/split "a,b,c" ","))           ; => {"a" "b" "c"}
(def {joined} (str/join parts " | "))           ; => "a | b | c"
(def {trimmed} (str/trim "  hello  "))          ; => "hello"
(def {upper} (str/upper "hello"))               ; => "HELLO"
(def {lower} (str/lower "HELLO"))               ; => "hello"
(def {replaced} (str/replace "foo" "o" "a"))    ; => "faa"

; String predicates
(def {contains} (str/contains? "hello world" "world"))  ; => 1
(def {starts} (str/starts-with? "hello" "hel"))         ; => 1
(def {ends} (str/ends-with? "hello" "lo"))              ; => 1

; Formatting
(def {msg} (str/format "User ~a has ~d points" "alice" 100))
; => "User alice has 100 points"

; Regular expressions (optional, later)
(def {matches} (str/match "v1.2.3" "v(\\d+)\\.(\\d+)\\.(\\d+)"))
; => {"1" "2" "3"}
```

**C implementation:**
- Most are simple string.h operations
- Format can reuse printf-style formatting
- Regex needs POSIX regex or PCRE library (optional)

**Builtin functions:**
- `valk_builtin_str_split()`
- `valk_builtin_str_join()`
- `valk_builtin_str_trim()`
- `valk_builtin_str_upper()`
- `valk_builtin_str_lower()`
- `valk_builtin_str_replace()`
- `valk_builtin_str_contains()`
- `valk_builtin_str_format()`

**Testing:**
- Split strings on various delimiters
- Join lists of strings
- Trim whitespace
- Case conversion
- String searching
- Format strings

---

#### Task 2.5: Environment Variables (1 day)

**Goal**: Access and modify environment.

**Lisp API:**
```lisp
(def {home} (env/get "HOME"))
(env/set "MY_VAR" "value")
(def {all} (env/list))  ; => {{"PATH" "/usr/bin"} {"HOME" "/home/user"} ...}
```

**C implementation:**
```c
const char* valk_env_get(const char* name);  // getenv
void valk_env_set(const char* name, const char* value);  // setenv
```

**Builtin functions:**
- `valk_builtin_env_get()`
- `valk_builtin_env_set()`
- `valk_builtin_env_list()`

---

#### Task 2.6: Git Integration (2-3 days)

**Goal**: Git operations for repository management.

**Approach 1: Shell out (simple, no dependencies)**
```lisp
(defun git/clone [url dest]
  (exec "git" "clone" url dest))

(defun git/checkout [branch]
  (exec "git" "checkout" branch))

(defun git/commit-hash []
  (process-stdout (exec "git" "rev-parse" "HEAD")))
```

**Approach 2: libgit2 (native, more features)**
```lisp
(def {repo} (git/open "/workspace"))
(git/checkout repo "main")
(def {hash} (git/head-hash repo))
(def {commits} (git/log repo :limit 10))
```

**Recommendation**: Start with Approach 1 (shell out), add Approach 2 later if needed.

---

### Phase 3: CI Core (Build the System)
**Timeline**: 2-3 weeks after Phase 2
**Estimated effort**: 10-15 days

#### Task 3.1: Pipeline DSL (3-4 days)

**Goal**: High-level API for defining pipelines.

**Implementation in Lisp:**
```lisp
; src/prelude_ci.valk

(def {*pipelines*} {})  ; Global pipeline registry

(fun {pipeline name & config}
  ; Parse config (triggers, env, steps)
  ; Register pipeline
  (= {*pipelines*}
     (cons {{name config}} *pipelines*)))

(fun {step name & body}
  {:type :step :name name :body body})

(fun {run-pipeline name context}
  (let [pipeline (pipeline-get name)]
    (for-each step (:steps pipeline)
      (run-step step context))))
```

**Testing:**
- Define simple pipeline
- Run pipeline
- Check step execution order
- Test failure handling

---

#### Task 3.2: Webhook Server (2-3 days)

**Goal**: Receive GitHub/GitLab webhooks to trigger pipelines.

**Implementation:**
```lisp
; CI webhook server
(def {server} (http/server 8080
  (fn [req]
    (if (== (http2/request-path req) "/webhook")
      {
        (let [payload (json/parse (http2/request-body req))
              event (http2/request-header req "X-GitHub-Event")]

          (select
            [(== event "push")
             (do
               (trigger-pipeline "main-ci" payload)
               (http2/response :status 202 :body "Pipeline triggered"))]

            [(== event "pull_request")
             (do
               (trigger-pipeline "pr-ci" payload)
               (http2/response :status 202 :body "PR pipeline triggered"))]

            [otherwise
             (http2/response :status 200 :body "Event ignored")]))
      }
      {
        (http2/response :status 404 :body "Not found")
      }))))
```

**Testing:**
- Send test webhooks
- Verify pipeline triggering
- Test different event types
- Test payload parsing

---

#### Task 3.3: Pipeline Execution Engine (4-5 days)

**Goal**: Execute pipeline steps with proper isolation and error handling.

**Features:**
- Sequential step execution
- Parallel step support
- Timeout handling
- Error recovery
- Artifact management
- Log capture

**Implementation:**
```lisp
(defun run-step [step context]
  (let [start-time (time/now)
        log-file (path/join (:workspace context)
                            (str "logs/" (:name step) ".log"))]

    ; Setup step environment
    (dir/create (:workspace context))

    ; Execute step body
    (def {result}
      (with-timeout (:timeout step)
        (with-error-handler
          (fn [err] {:status :failed :error err})
          (do
            (print "Running step:" (:name step))
            (eval (:body step))
            {:status :success}))))

    ; Record results
    (= (:elapsed result) (- (time/now) start-time))
    (file/write log-file (str result))

    ; Handle failure
    (when (== (:status result) :failed)
      (notify-failure step result))

    result))
```

---

#### Task 3.4: Status API & Dashboard (2-3 days)

**Goal**: Query pipeline status and view results.

**API endpoints:**
```lisp
; Status endpoint
(http/route "/api/status/:pipeline-id"
  (fn [req]
    (let [id (get-param req :pipeline-id)
          status (pipeline-status id)]
      (http2/response :status 200
                     :json status))))

; Logs endpoint
(http/route "/api/logs/:pipeline-id/:step"
  (fn [req]
    (let [id (get-param req :pipeline-id)
          step (get-param req :step)
          logs (pipeline-logs id step)]
      (http2/response :status 200
                     :body logs))))
```

**Simple HTML dashboard (optional):**
```lisp
(http/route "/"
  (fn [req]
    (http2/response
      :status 200
      :headers {:content-type "text/html"}
      :body (render-dashboard (pipeline-list)))))
```

---

### Phase 4: Integrations & Polish
**Timeline**: After Phase 3
**Pick based on needs**

#### Option A: GitHub/GitLab API Integration
```lisp
; Set commit status
(github/status owner repo sha
  :state :success
  :description "All tests passed"
  :context "ci/valkyria")

; Post comment on PR
(github/comment owner repo pr-number
  "Build succeeded! 🎉")
```

#### Option B: Docker Integration
```lisp
(docker/build "." :tag "myapp:latest")
(docker/push "myapp:latest")
(docker/run "myapp:latest" :ports {"8080" "80"})
```

#### Option C: Kubernetes Deployment
```lisp
(k8s/apply "deployment.yaml")
(k8s/set-image "deployment/myapp" "myapp:latest")
(k8s/wait-ready "deployment/myapp" :timeout 300)
```

#### Option D: Notification Integrations
```lisp
(slack/send "#engineering" "Build failed!")
(email/send "dev@company.com" "Pipeline status" body)
(discord/webhook url {:content "Deployment complete"})
```

---

## Milestones & Demos

### Milestone 1: "Hello CI" (End of Phase 2)
```lisp
; Simple script that runs a command
(def {result} (exec "echo" "Hello from CI!"))
(print (process-stdout result))
```
**Proves**: Process execution works

### Milestone 2: "Basic Pipeline" (End of Phase 3.1)
```lisp
(pipeline "test"
  :steps [
    (step "build" (exec "make" "build"))
    (step "test" (exec "make" "test"))])

(run-pipeline "test" {:workspace "/tmp/build"})
```
**Proves**: Pipeline DSL works

### Milestone 3: "Webhook CI" (End of Phase 3.2)
- Webhook server running
- Receives GitHub push event
- Triggers pipeline automatically
**Proves**: Integration with Git platforms works

### Milestone 4: "Self-Hosting" (End of Phase 3.3)
Valkyria's own CI runs on Valkyria:
```lisp
(pipeline "valkyria-ci"
  :triggers [:push]
  :steps [
    (step "checkout"
      (git/clone (env "REPO_URL") "/workspace"))
    (step "build"
      (exec "make" "build"))
    (step "test"
      (exec "make" "test"))
    (step "report"
      (github/status "anthropic" "valkyria" (env "COMMIT_SHA")
        :state (if (all-passed?) :success :failure)))])
```
**Proves**: Valkyria can build Valkyria - dogfooding works!

---

## Success Metrics

**Technical:**
- Execute 100+ pipelines without crashes
- Handle parallel pipeline execution
- Process webhook in <100ms
- Pipeline startup overhead <1s
- Log streaming with <500ms latency

**Features:**
- Support GitHub + GitLab webhooks
- Run arbitrary shell commands
- Capture stdout/stderr/exit codes
- Timeout support
- Error recovery
- Status reporting

**Demo:**
- Push code to GitHub
- Webhook triggers Valkyria CI
- Pipeline clones, builds, tests
- Status posted back to GitHub
- REPL shows live pipeline status

---

## Resources Required

**Dependencies:**
- cJSON (JSON parsing) or custom implementation
- PCRE (regex, optional)
- libgit2 (optional, can shell out instead)

**New code:**
- `src/process.c/h` - Process execution (~400 lines)
- `src/file.c/h` - File operations (~300 lines)
- `src/json.c/h` - JSON parser (~200 lines or use cJSON)
- `src/string.c` - String utilities (~300 lines)
- `src/prelude_ci.valk` - CI DSL (~500 lines)
- `examples/ci/` - Example pipelines (~300 lines)

**Total new code:** ~2000-2500 lines

**Timeline:** 5-7 weeks of focused work

---

## Comparison to Existing CI Systems

| Feature | GitHub Actions | Jenkins | Valkyria CI |
|---------|---------------|---------|-------------|
| Language | YAML | Groovy/XML | Lisp |
| Live debugging | No | No | **Yes (REPL)** |
| Composability | Limited | Limited | **Full (functions)** |
| Dynamic pipelines | No | Partial | **Yes** |
| Error recovery | No | Limited | **Yes (conditions)** |
| Hot reload | No | No | **Yes** |

**Key differentiator**: Valkyria CI pipelines are **real programs**, not configuration.

---

## Next Steps After CI System

Once CI system works, you've validated:
- ✅ Async I/O
- ✅ Process execution
- ✅ File system operations
- ✅ JSON parsing
- ✅ HTTP integration
- ✅ Real-world automation

**Then you can tackle:**
1. More complex workflows (multi-stage pipelines, matrix builds)
2. Distributed execution (multiple worker nodes)
3. Artifact caching
4. Container orchestration
5. Full DevOps platform

**Or pivot to:**
- Infrastructure as Code (Terraform-like)
- Log aggregation and analysis
- Monitoring and alerting
- Deployment automation

---

**Last Updated**: 2025-11-09
**Status**: Planning
**Dependencies**: Networking branch completion
