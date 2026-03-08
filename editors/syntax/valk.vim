if exists('b:current_syntax')
  finish
endif

syn match valkComment ";.*$"
syn region valkString start=+"+ skip=+\\"+ end=+"+
syn match valkNumber "\<-\?\d\+\>"
syn match valkPlistKey "\s\zs:[a-zA-Z0-9_/\-]\+"

syn match valkKeyword "(\s*\zs\(def\|fun\|if\|do\|select\|case\|load\|eval\|quote\|let\)\>"
syn match valkKeyword "(\s*\zs\(aio/let\|aio/do\)\>"
syn match valkKeyword "(\s*\zs<-\>"
syn match valkLambda "(\s*\zs\\\ze\s"

syn match valkSpecial "\<true\>\|\<false\>\|\<nil\>\|\<otherwise\>"
syn match valkOperator "(\s*\zs[=<>!+\-*/&|]\{1,2}\>"

syn match valkBuiltin "(\s*\zs\(println\|print\|printf\|str\|make-string\|read-file\|error\|error?\)\>"
syn match valkBuiltin "(\s*\zs\(list\|head\|tail\|join\|cons\|len\|init\|range\|repeat\|nth\|fst\|snd\|take\|drop\)\>"
syn match valkBuiltin "(\s*\zs\(map\|filter\|foldl\|reverse\|sum\|product\|flip\|comp\|id\)\>"
syn match valkBuiltin "(\s*\zs\(list?\|nil?\|handle?\|ref?\|error?\)\>"
syn match valkBuiltin "(\s*\zs\(not\|and\|or\)\>"
syn match valkBuiltin "(\s*\zs\(time-us\|sleep\|exit\|penv\|get\)\>"
syn match valkBuiltin "(\s*\zs\(test\|test-async\)\>"
syn match valkBuiltin "(\s*\zsaio/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zshttp2/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zsreq/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zsstream/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zssse/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zsmetrics/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zsmem/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zstest/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zsplist/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zsstr/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zsctx/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zsvm/[a-z/\-]*\>"
syn match valkBuiltin "(\s*\zstrace/[a-z/\-]*\>"

hi def link valkComment Comment
hi def link valkString String
hi def link valkNumber Number
hi def link valkKeyword Keyword
hi def link valkLambda Keyword
hi def link valkSpecial Constant
hi def link valkOperator Operator
hi def link valkPlistKey Identifier
hi def link valkBuiltin Function

let b:current_syntax = 'valk'
