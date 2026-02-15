; Scope and definition tracking for Valkyria

; Structured forms create scopes
(fun_form) @local.scope
(lambda_form) @local.scope
(let_form) @local.scope

; def creates a global definition
(def_form
  binding: (qexpr (symbol) @local.definition))

; = creates a local definition
(let_form
  binding: (qexpr (symbol) @local.definition))

; fun defines a function name and parameters
(fun_form
  signature: (qexpr (symbol) @local.definition))

; Lambda formals are definitions
(lambda_form
  params: (qexpr (symbol) @local.definition))

; Symbol references
(symbol) @local.reference
