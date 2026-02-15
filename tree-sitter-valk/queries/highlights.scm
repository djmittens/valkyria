; Valkyria tree-sitter highlight queries
; =======================================
; Ordered from most specific to least specific.
; Tree-sitter uses LAST match, so generic rules go first, specific ones last.

; ---------------------------------------------------------------------------
; Fallback: any symbol is a variable
; ---------------------------------------------------------------------------
(symbol) @variable

; ---------------------------------------------------------------------------
; Any symbol in function position of a generic sexpr is a function call
; ---------------------------------------------------------------------------
(sexpr . (symbol) @function.call)

; ---------------------------------------------------------------------------
; Literals
; ---------------------------------------------------------------------------
(number) @number
(string) @string
(boolean) @boolean
(nil) @constant.builtin
(comment) @comment

; Keywords (:foo :bar) — like Clojure keywords
(keyword) @string.special.symbol

; ---------------------------------------------------------------------------
; Brackets and delimiters
; ---------------------------------------------------------------------------
(sexpr "(" @punctuation.bracket ")" @punctuation.bracket)
(qexpr "{" @punctuation.bracket "}" @punctuation.bracket)
(def_form "(" @punctuation.bracket ")" @punctuation.bracket)
(fun_form "(" @punctuation.bracket ")" @punctuation.bracket)
(lambda_form "(" @punctuation.bracket ")" @punctuation.bracket)
(if_form "(" @punctuation.bracket ")" @punctuation.bracket)
(do_form "(" @punctuation.bracket ")" @punctuation.bracket)
(let_form "(" @punctuation.bracket ")" @punctuation.bracket)
(load_form "(" @punctuation.bracket ")" @punctuation.bracket)

; Reader macros
(quote "'" @punctuation.special)
(quasiquote "`" @punctuation.special)
(unquote "," @punctuation.special)
(unquote_splicing ",@" @punctuation.special)

; ---------------------------------------------------------------------------
; Operators — math, comparison, logic in function position
; ---------------------------------------------------------------------------
(sexpr . (symbol) @operator
  (#any-of? @operator "+" "-" "*" "/" ">" "<" ">=" "<=" "==" "!=" "not" "and" "or"))

; Variadic marker
(symbol) @operator
  (#eq? @operator "&")

; ---------------------------------------------------------------------------
; Special form keywords
; ---------------------------------------------------------------------------
(keyword_def) @keyword
(keyword_fun) @keyword.function
(keyword_lambda) @keyword.function
(keyword_if) @keyword.conditional
(keyword_do) @keyword
(keyword_let) @keyword
(keyword_load) @keyword.import

; select/case — still generic sexprs
(sexpr . (symbol) @keyword.conditional
  (#any-of? @keyword.conditional "select" "case"))

; quote/eval/read as keywords
(sexpr . (symbol) @keyword
  (#any-of? @keyword "quote" "quasiquote" "unquote" "unquote-splicing" "eval" "read"))

; Monadic binding operator
(sexpr . (symbol) @keyword
  (#eq? @keyword "<-"))

; Async control flow
(sexpr . (symbol) @keyword
  (#any-of? @keyword "aio/let" "aio/do"))

; otherwise — used in select branches
(symbol) @constant.builtin
  (#eq? @constant.builtin "otherwise")

; ---------------------------------------------------------------------------
; Structured form: def — binding names
; ---------------------------------------------------------------------------
; (def {name} value) — single binding is a variable definition
(def_form
  binding: (qexpr (symbol) @variable.definition))

; ---------------------------------------------------------------------------
; Structured form: fun — name + parameters
; ---------------------------------------------------------------------------
; (fun {name params...} body) — first sym is function name, rest are params
(fun_form
  signature: (qexpr . (symbol) @function.definition))

(fun_form
  signature: (qexpr (symbol) @variable.parameter))

; Override: first symbol in fun signature is function name, not param
; (tree-sitter last-match-wins)
(fun_form
  signature: (qexpr . (symbol) @function.definition))

; ---------------------------------------------------------------------------
; Structured form: lambda — parameters
; ---------------------------------------------------------------------------
(lambda_form
  params: (qexpr (symbol) @variable.parameter))

; ---------------------------------------------------------------------------
; Structured form: let — binding names
; ---------------------------------------------------------------------------
(let_form
  binding: (qexpr (symbol) @variable.definition))

; ---------------------------------------------------------------------------
; Load form — path string
; ---------------------------------------------------------------------------
(load_form (string) @string.special.path)

; ---------------------------------------------------------------------------
; Namespaced builtin families — function position
; ---------------------------------------------------------------------------
(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^aio/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^http2/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^req/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^stream/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^sse/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^metrics/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^mem/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^vm/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^test/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^plist/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^str/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^trace/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^async/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^ctx/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^sys/"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^source-"))

(sexpr . (symbol) @function.builtin
  (#match? @function.builtin "^coverage-"))

; ---------------------------------------------------------------------------
; Core builtins — function position
; ---------------------------------------------------------------------------
(sexpr . (symbol) @function.builtin
  (#any-of? @function.builtin
    "list" "head" "tail" "join" "cons" "len" "init" "range" "repeat"
    "print" "println" "printf" "str" "make-string" "type"
    "ord" "str->num"
    "list?" "ref?" "nil?" "handle?" "error?"
    "read-file"
    "map" "filter" "foldl" "reverse" "sum" "product"
    "nth" "fst" "snd" "trd" "last" "take" "drop" "split" "exists"
    "id" "flip" "comp" "curry" "uncurry" "pack" "unpack"
    "time-us" "sleep" "stack-depth"
    "exit" "shutdown" "get"))

; Error handling — function position
(sexpr . (symbol) @function.builtin.exception
  (#any-of? @function.builtin.exception "error" "error?"))

; ---------------------------------------------------------------------------
; Context flow — aio/let bindings with <- syntax
; ---------------------------------------------------------------------------
(sexpr . (symbol) @keyword
  (#any-of? @keyword "aio/let" "aio/do"))
