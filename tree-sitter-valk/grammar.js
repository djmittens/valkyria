/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

// Valkyria Lisp grammar for tree-sitter
// Syntax: S-expressions (...), Q-expressions {...}, reader macros, keywords

const SYMBOL_CHARS = /[a-zA-Z0-9_+\-*\\/=<>!&?:]/;

module.exports = grammar({
  name: "valk",

  extras: ($) => [/\s/, $.comment],

  rules: {
    source_file: ($) => repeat($._form),

    _form: ($) =>
      choice(
        $.def_form,
        $.fun_form,
        $.lambda_form,
        $.if_form,
        $.do_form,
        $.let_form,
        $.load_form,
        $.sexpr,
        $.qexpr,
        $.quote,
        $.quasiquote,
        $.unquote_splicing,
        $.unquote,
        $._atom,
      ),

    // (def {name} value) or (def {a b c} v1 v2 v3)
    def_form: ($) =>
      seq("(", alias("def", $.keyword_def), field("binding", $.qexpr), repeat($._form), ")"),

    // (fun {name params...} body)
    fun_form: ($) =>
      seq("(", alias("fun", $.keyword_fun), field("signature", $.qexpr), repeat($._form), ")"),

    // (\ {params...} body)
    lambda_form: ($) =>
      seq("(", alias("\\", $.keyword_lambda), field("params", $.qexpr), repeat($._form), ")"),

    // (if cond then else)
    if_form: ($) =>
      seq("(", alias("if", $.keyword_if), repeat($._form), ")"),

    // (do expr...)
    do_form: ($) =>
      seq("(", alias("do", $.keyword_do), repeat($._form), ")"),

    // (= {name} value)
    let_form: ($) =>
      seq("(", alias("=", $.keyword_let), field("binding", $.qexpr), repeat($._form), ")"),

    // (load "path")
    load_form: ($) =>
      seq("(", alias("load", $.keyword_load), $.string, ")"),

    // S-expression: (fn arg1 arg2 ...)
    sexpr: ($) => seq("(", repeat($._form), ")"),

    // Q-expression: {data1 data2 ...}
    qexpr: ($) => seq("{", repeat($._form), "}"),

    // Reader macros
    quote: ($) => seq("'", $._form),
    quasiquote: ($) => seq("`", $._form),
    unquote_splicing: ($) => seq(",@", $._form),
    unquote: ($) => seq(",", $._form),

    // Atoms
    _atom: ($) =>
      choice($.number, $.string, $.keyword, $.boolean, $.nil, $.symbol),

    // Numbers: integers only, base-10, optionally negative
    number: ($) => token(seq(optional("-"), /[0-9]+/)),

    // Strings: double-quoted with escape sequences
    string: ($) =>
      token(
        seq(
          '"',
          repeat(
            choice(
              /[^"\\]/,
              seq("\\", /[abfnrtv\\'"]/),
            ),
          ),
          '"',
        ),
      ),

    // Boolean literals
    boolean: ($) => token(choice("true", "false")),

    // Nil literal
    nil: ($) => token("nil"),

    // Keywords: symbols starting with ':'
    keyword: ($) => token(seq(":", repeat1(SYMBOL_CHARS))),

    // Symbols: identifiers, operators, namespaced names
    // Must not match bare numbers (handled by number rule)
    symbol: ($) => token(repeat1(SYMBOL_CHARS)),

    // Comments: ; to end of line
    comment: ($) => token(seq(";", /[^\n]*/)),
  },
});
