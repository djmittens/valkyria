Module Refactor:

I want to change the model behind how modules, namespaces, files and so on work.
It is true that the load order matters for a programming language for how the program and its symbols are interpreted.

right now to load a file you need to use the (load "file") builtin

there is a module macro and all that that allows you to create  a namespace.

I want to do a deep refactor, and total cleaning of the whole codebase to work like this:

0. File semantics
The semantic meaning of a file is basically wrapping the whole thing in a (do ... ) expression, taking the result of the last statement and replacing (load "file") expression with the result.

1. Resolution order:
check the env for presence of file://{path} its value would be the processed AST of an S expression, which would then just be placed as replacement of load
- This feature will allow repl to override a file or provide a custom file inline, that can be loaded adhoc by other modules.
check files local directory (based on the current working file, thats loading it)
check cwd
check valks binary path (if different)

2. Namespacing.
when loading an ast of an s-expression all defs and so on should be namespaced to (module ...) so for example, when encountering (module lsp/io) every def after that point this file will prepend lsp/io

so if you are defining a function (fun 'foo) you get lsp/io/foo  in the global env.
same thing as references, if you see something in the same file referring to (foo ) and so on, it should internally be rewritten to (lsp/io/foo )


3. Nesting
Since macros can change the semantics of the file being loaded based on where they are loaded from. There needs to be some sort of nesting,

so a file that defines lsp/io module imported from a file defining (module bar)

like so:
(module bar)

(load "lsp/io.valk")

it should nest it like bar/lsp/io, so within bar you could 


so lets say we have:

:root/

  (load "stdlib/io.valk")
  stldib/
    io/
      (fun foo)

  (load "lsp.valk")
  lsp/
    (load "stdlib/io.valk")
    io/
      (fun foo)

  (lsp/io/foo "wooh")
  (io/foo "wooh")

i think this is a pretty reasonable design but i want the system to be simple and generic.
and obviously hooked up across lsp and all the other subsystems.
