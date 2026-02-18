#!/usr/bin/env python3
"""Extract C builtin signatures for the LSP.

Scans all valk_lenv_put_builtin() registrations in C source, then extracts
arity, parameter names, parameter types, and return types from function bodies.

.valk functions (prelude, user code) are handled dynamically by the LSP's
load-graph resolver and analyze_document() at runtime — not here.

Generates src/lsp/lsp_builtins_gen.h with:
  - LSP_BUILTINS[] : name, arity, signature, param_types[], ret_type, is_special_form
"""

import re
import sys
from pathlib import Path
from dataclasses import dataclass, field

@dataclass
class Param:
  name: str
  types: list[str] = field(default_factory=list)
  variadic: bool = False

@dataclass
class Builtin:
  lisp_name: str
  c_func: str = ""
  source_file: str = ""
  min_arity: int = -1
  max_arity: int = -1
  params: list[Param] = field(default_factory=list)
  doc: str = ""
  is_special_form: bool = False
  ret_type: str = "BRET_ANY"

LVAL_TYPE_NAMES = {
  "LVAL_NUM": "Num",
  "LVAL_STR": "Str",
  "LVAL_SYM": "Sym",
  "LVAL_FUN": "Fun",
  "LVAL_CONS": "List",
  "LVAL_NIL": "Nil",
  "LVAL_QEXPR": "QExpr",
  "LVAL_REF": "Ref",
  "LVAL_HANDLE": "Handle",
  "LVAL_ERR": "Err",
}

SPECIAL_FORMS = {
  "def", "=", "\\", "fun", "if", "do", "select", "case",
  "quote", "load", "eval", "read", "let",
  "aio/let", "aio/do", "<-",
  "type", "match",
}

# Return type for each builtin (derived from C source analysis).
# Omitted builtins default to BRET_ANY.
RETURN_TYPES: dict[str, str] = {
  # Arithmetic -> Num
  "+": "BRET_NUM", "-": "BRET_NUM", "*": "BRET_NUM", "/": "BRET_NUM",
  ">": "BRET_NUM", "<": "BRET_NUM", ">=": "BRET_NUM", "<=": "BRET_NUM",
  "==": "BRET_NUM", "!=": "BRET_NUM", "ord": "BRET_NUM",
  "str->num": "BRET_NUM", "len": "BRET_NUM",
  # Memory/system -> Num
  "time-us": "BRET_NUM", "stack-depth": "BRET_NUM",
  "mem/heap/usage": "BRET_NUM", "mem/heap/hard-limit": "BRET_NUM",
  "mem/heap/set-hard-limit": "BRET_NUM",
  "mem/gc/collect": "BRET_NUM", "mem/gc/threshold": "BRET_NUM",
  "mem/gc/set-threshold": "BRET_NUM", "mem/gc/usage": "BRET_NUM",
  "mem/gc/min-interval": "BRET_NUM", "mem/gc/set-min-interval": "BRET_NUM",
  "mem/arena/usage": "BRET_NUM", "mem/arena/capacity": "BRET_NUM",
  "mem/arena/high-water": "BRET_NUM",
  "http2/server-port": "BRET_NUM",
  "source-line": "BRET_NUM", "source-column": "BRET_NUM",
  # Predicates -> Num (0/1)
  "error?": "BRET_NUM", "list?": "BRET_NUM", "ref?": "BRET_NUM",
  "aio/on-loop-thread?": "BRET_NUM",
  # String operations -> Str
  "str": "BRET_STR", "make-string": "BRET_STR",
  "str/replace": "BRET_STR", "str/slice": "BRET_STR",
  "read-file": "BRET_STR", "source-file": "BRET_STR",
  "http2/response-body": "BRET_STR", "http2/response-status": "BRET_STR",
  "aio/metrics-json": "BRET_STR", "aio/metrics-json-compact": "BRET_STR",
  "aio/systems-json": "BRET_STR",
  "aio/diagnostics-state-json": "BRET_STR",
  "aio/diagnostics-state-json-compact": "BRET_STR",
  "vm/metrics-json": "BRET_STR", "vm/metrics-json-compact": "BRET_STR",
  "vm/metrics-prometheus": "BRET_STR",
  "sys/log/set-level": "BRET_STR",
  "metrics/delta-json": "BRET_STR", "metrics/prometheus": "BRET_STR",
  "metrics/json": "BRET_STR", "metrics/registry-json": "BRET_STR",
  # Nil-returning side effects
  "def": "BRET_NIL", "=": "BRET_NIL",
  "print": "BRET_NIL", "printf": "BRET_NIL", "println": "BRET_NIL",
  "load": "BRET_NIL", "sleep": "BRET_NIL",
  "aio/run": "BRET_NIL", "aio/stop": "BRET_NIL",
  "mem/stats": "BRET_NIL", "mem/gc/stats": "BRET_NIL",
  "http2/request-add-header": "BRET_NIL", "http2/server-handle": "BRET_NIL",
  "http2/connect": "BRET_NIL",
  "metrics/counter-inc": "BRET_NIL", "metrics/gauge-set": "BRET_NIL",
  "metrics/gauge-inc": "BRET_NIL", "metrics/gauge-dec": "BRET_NIL",
  "metrics/histogram-observe": "BRET_NIL",
  "coverage-mark": "BRET_ANY", "coverage-record": "BRET_ANY",
  "coverage-branch": "BRET_NUM",
  # List-returning
  "cons": "BRET_LIST", "list": "BRET_LIST",
  "range": "BRET_LIST", "repeat": "BRET_LIST",
  "str/split": "BRET_LIST",
  "http2/response-headers": "BRET_LIST",
  "penv": "BRET_LIST", "mem/checkpoint/stats": "BRET_LIST",
  "tail": "BRET_LIST_OR_NIL", "init": "BRET_LIST_OR_NIL",
  "join": "BRET_LIST_OR_NIL",
  # Handle-returning (async)
  "aio/start": "BRET_HANDLE",
  "aio/schedule": "BRET_HANDLE", "aio/interval": "BRET_HANDLE",
  "aio/sleep": "BRET_HANDLE", "aio/then": "BRET_HANDLE",
  "aio/catch": "BRET_HANDLE", "aio/finally": "BRET_HANDLE",
  "aio/all": "BRET_HANDLE", "aio/race": "BRET_HANDLE",
  "aio/any": "BRET_HANDLE", "aio/all-settled": "BRET_HANDLE",
  "aio/within": "BRET_HANDLE", "aio/retry": "BRET_HANDLE",
  "aio/pure": "BRET_HANDLE", "aio/fail": "BRET_HANDLE",
  "aio/never": "BRET_HANDLE", "aio/scope": "BRET_HANDLE",
  "aio/bracket": "BRET_HANDLE", "aio/traverse": "BRET_HANDLE",
  "aio/on-cancel": "BRET_HANDLE",
  "aio/cancelled?": "BRET_NUM",
  "http2/server-listen": "BRET_HANDLE", "http2/server-stop": "BRET_HANDLE",
  "http2/client-request": "BRET_HANDLE",
  "http2/client-request-with-headers": "BRET_HANDLE",
  "stream/closed": "BRET_HANDLE",
  # Ref-returning
  "http2/request": "BRET_REF", "http2/mock-response": "BRET_REF",
  "test/capture-start": "BRET_REF",
  "metrics/counter": "BRET_REF", "metrics/gauge": "BRET_REF",
  "metrics/histogram": "BRET_REF", "metrics/baseline": "BRET_REF",
  "metrics/collect-delta": "BRET_REF",
  "metrics/collect-delta-stateless": "BRET_REF",
  # Error constructor
  "error": "BRET_ERR",
  # Lambda constructor
  "\\": "BRET_FUN",
  # Special forms with known return types
  "quote": "BRET_LIST",
}

# Map from param type display strings to C enum values
PARAM_TYPE_TO_ENUM: dict[str, str] = {
  "Num": "BPTY_NUM",
  "Str": "BPTY_STR",
  "Sym": "BPTY_SYM",
  "Fun": "BPTY_FUN",
  "Nil": "BPTY_NIL",
  "List": "BPTY_LIST",
  "Ref": "BPTY_REF",
  "Ref(aio)": "BPTY_REF",
  "Handle": "BPTY_HANDLE",
  "QExpr": "BPTY_LIST",
}

# Compound param type patterns
COMPOUND_PARAM_TYPES: dict[tuple[str, ...], str] = {
  ("List", "Nil"): "BPTY_LIST_OR_NIL",
  ("Nil", "List"): "BPTY_LIST_OR_NIL",
  ("List", "QExpr"): "BPTY_LIST_OR_QEXPR",
  ("QExpr", "List"): "BPTY_LIST_OR_QEXPR",
  ("List", "QExpr", "Nil"): "BPTY_LIST_OR_QEXPR_OR_NIL",
  ("List", "Nil", "QExpr"): "BPTY_LIST_OR_QEXPR_OR_NIL",
  ("QExpr", "List", "Nil"): "BPTY_LIST_OR_QEXPR_OR_NIL",
  ("QExpr", "Nil", "List"): "BPTY_LIST_OR_QEXPR_OR_NIL",
  ("Nil", "List", "QExpr"): "BPTY_LIST_OR_QEXPR_OR_NIL",
  ("Nil", "QExpr", "List"): "BPTY_LIST_OR_QEXPR_OR_NIL",
}


def find_registrations(src_dir: Path) -> dict[str, tuple[str, str]]:
  """Find all valk_lenv_put_builtin calls. Returns {lisp_name: (c_func, file)}."""
  reg_re = re.compile(
    r'valk_lenv_put_builtin\s*\(\s*env\s*,\s*"([^"]+)"\s*,\s*(\w+)\s*\)')
  result = {}
  for f in src_dir.rglob("*.c"):
    text = f.read_text()
    for m in reg_re.finditer(text):
      lisp_name, c_func = m.group(1), m.group(2)
      lisp_name = lisp_name.replace('\\\\', '\\')
      result[lisp_name] = (c_func, str(f.relative_to(src_dir.parent)))
  return result


def extract_c_function_body(text: str, func_name: str) -> str | None:
  """Extract the body of a C function by name."""
  pattern = re.compile(
    rf'(?:static\s+)?valk_lval_t\s*\*\s*{re.escape(func_name)}\s*\([^)]*\)\s*\{{')
  m = pattern.search(text)
  if not m:
    return None
  start = m.end()
  depth = 1
  i = start
  while i < len(text) and depth > 0:
    if text[i] == '{':
      depth += 1
    elif text[i] == '}':
      depth -= 1
    i += 1
  return text[m.start():i]


def parse_arity(body: str) -> tuple[int, int]:
  """Extract min/max arity from multiple validation patterns.

  Patterns found in the codebase:
    A) LVAL_ASSERT_COUNT_EQ/GT/GE/LE/LT macros
    B) LVAL_ASSERT(a, valk_lval_list_count(a) == N, ...) — head, tail
    C) if (valk_lval_list_count(a) != N) { return valk_lval_err(...) } — aio/*
    D) argc >= N && argc <= M — server builtins
    E) UNUSED(a) with no other checks — 0 args
  """
  # --- Pattern A: LVAL_ASSERT_COUNT_* macros (must check `a, a` not inner) ---
  m = re.search(r'LVAL_ASSERT_COUNT_EQ\s*\(\s*a\s*,\s*a\s*,\s*(\d+)\)', body)
  if m:
    n = int(m.group(1))
    return n, n

  min_a, max_a = 0, -1

  # Only match when checking against `a` (the args list), not inner elements
  m = re.search(r'LVAL_ASSERT_COUNT_GT\s*\(\s*a\s*,\s*a\s*,\s*(\d+)\)', body)
  if m:
    min_a = int(m.group(1)) + 1

  m = re.search(r'LVAL_ASSERT_COUNT_GE\s*\(\s*a\s*,\s*a\s*,\s*(\d+)\)', body)
  if m:
    min_a = max(min_a, int(m.group(1)))

  m = re.search(r'LVAL_ASSERT_COUNT_LE\s*\(\s*a\s*,\s*a\s*,\s*(\d+)\)', body)
  if m:
    max_a = int(m.group(1))

  m = re.search(r'LVAL_ASSERT_COUNT_LT\s*\(\s*a\s*,\s*a\s*,\s*(\d+)\)', body)
  if m:
    max_a = int(m.group(1)) - 1

  if min_a > 0 or max_a >= 0:
    return min_a, max_a

  # --- Pattern B: LVAL_ASSERT(a, valk_lval_list_count(a) == N, ...) ---
  m = re.search(r'LVAL_ASSERT\s*\([^,]+,\s*valk_lval_list_count\s*\(\s*\w+\s*\)\s*==\s*(\d+)', body)
  if m:
    n = int(m.group(1))
    return n, n

  # --- Pattern C: if (valk_lval_list_count(a) != N) ---
  m = re.search(r'if\s*\(\s*valk_lval_list_count\s*\(\s*\w+\s*\)\s*!=\s*(\d+)\s*\)', body)
  if m:
    n = int(m.group(1))
    return n, n

  # Also: if (valk_lval_list_count(a) < N)
  m = re.search(r'if\s*\(\s*valk_lval_list_count\s*\(\s*\w+\s*\)\s*<\s*(\d+)\s*\)', body)
  if m:
    min_a = int(m.group(1))
    return min_a, -1

  # --- Pattern D: argc >= N && argc <= M ---
  m = re.search(r'argc\s*>=\s*(\d+)\s*&&\s*argc\s*<=\s*(\d+)', body)
  if m:
    return int(m.group(1)), int(m.group(2))

  m = re.search(r'argc\s*==\s*0\s*\|\|\s*argc\s*==\s*1', body)
  if m:
    return 0, 1

  # --- Pattern E: UNUSED(a) with no count checks at all ---
  if re.search(r'UNUSED\s*\(\s*a\s*\)', body):
    if not re.search(r'valk_lval_list_count|LVAL_ASSERT_COUNT', body):
      return 0, 0

  # Variadic fallback: uses list_count for iteration but no constraint
  if re.search(r'valk_lval_list_count\s*\(\s*a\s*\)', body):
    return 0, -1

  return 0, -1


def parse_param_types(body: str) -> dict[int, list[str]]:
  """Extract parameter type constraints from LVAL_ASSERT_TYPE calls."""
  result = {}
  type_re = re.compile(
    r'LVAL_ASSERT_TYPE\s*\([^,]+,\s*(?:valk_lval_list_nth\s*\(\s*\w+\s*,\s*(\d+)\s*\)|(\w+))\s*,'
    r'\s*((?:LVAL_\w+(?:\s*,\s*LVAL_\w+)*))\s*\)')
  for m in type_re.finditer(body):
    idx_str = m.group(1)
    types_str = m.group(3)
    types = [LVAL_TYPE_NAMES.get(t.strip(), t.strip())
             for t in types_str.split(',')]
    if idx_str is not None:
      result[int(idx_str)] = types
    elif m.group(2):
      varname = m.group(2)
      nth_re = re.compile(
        rf'{re.escape(varname)}\s*=\s*valk_lval_list_nth\s*\(\s*\w+\s*,\s*(\d+)\s*\)')
      nm = nth_re.search(body)
      if nm:
        result[int(nm.group(1))] = types

  aio_re = re.compile(
    r'LVAL_ASSERT_AIO_SYSTEM\s*\([^,]+,\s*(?:valk_lval_list_nth\s*\(\s*\w+\s*,\s*(\d+)\s*\)|(\w+))\s*\)')
  for m in aio_re.finditer(body):
    idx_str = m.group(1)
    if idx_str is not None:
      result[int(idx_str)] = ["Ref(aio)"]
    elif m.group(2):
      varname = m.group(2)
      nth_re = re.compile(
        rf'{re.escape(varname)}\s*=\s*valk_lval_list_nth\s*\(\s*\w+\s*,\s*(\d+)\s*\)')
      nm = nth_re.search(body)
      if nm:
        result[int(nm.group(1))] = ["Ref(aio)"]

  return result


def parse_param_names(body: str) -> dict[int, str]:
  """Extract parameter names from variable assignments."""
  result = {}
  nth_re = re.compile(
    r'valk_lval_t\s*\*\s*(\w+)\s*=\s*valk_lval_list_nth\s*\(\s*\w+\s*,\s*(\d+)\s*\)')
  for m in nth_re.finditer(body):
    varname = m.group(1)
    idx = int(m.group(2))
    clean = varname
    for suffix in ('_arg', '_val', '_lval', '_v'):
      if clean.endswith(suffix):
        clean = clean[:-len(suffix)]
        break
    if clean.startswith('arg') and clean[3:].isdigit():
      continue
    if clean in ('a', 'v', 'x', 'y'):
      continue
    result[idx] = clean.replace('_', '-')
  return result


def build_params(builtin: Builtin, body: str) -> None:
  """Build parameter list from extracted info."""
  types = parse_param_types(body)
  names = parse_param_names(body)

  if builtin.lisp_name in PARAM_TYPE_OVERRIDES:
    for idx, tys in PARAM_TYPE_OVERRIDES[builtin.lisp_name].items():
      types[idx] = tys

  if builtin.max_arity == 0:
    return

  n = builtin.max_arity if builtin.max_arity >= 0 else max(
    builtin.min_arity, max(list(types.keys()) + list(names.keys()) + [-1]) + 1)

  for i in range(n):
    pname = names.get(i, f"arg{i}")
    ptypes = types.get(i, [])
    builtin.params.append(Param(name=pname, types=ptypes))

  if builtin.max_arity < 0 and builtin.params:
    builtin.params[-1].variadic = True


def format_signature(b: Builtin) -> str:
  """Generate a human-readable signature string."""
  parts = [b.lisp_name]
  for p in b.params:
    type_str = "|".join(p.types) if p.types else ""
    if p.variadic:
      if type_str:
        parts.append(f"{p.name}:{type_str}...")
      else:
        parts.append(f"{p.name}...")
    else:
      if type_str:
        parts.append(f"{p.name}:{type_str}")
      else:
        parts.append(p.name)
  return "(" + " ".join(parts) + ")"


def find_delegated_body(body: str, c_files_text: dict[str, str]) -> str | None:
  """If a function is a thin wrapper that delegates to another, find that body.

  Matches patterns like:
    return valk_builtin_ord_op(a, ORD_GT);
    return valk_builtin_math(a, MATH_PLUS);
  """
  m = re.search(r'return\s+(valk_builtin_\w+)\s*\(', body)
  if not m:
    return None
  delegate = m.group(1)
  for text in c_files_text.values():
    dbody = extract_c_function_body(text, delegate)
    if dbody:
      return dbody
  return None


# Manual param type overrides for builtins where the extraction heuristics
# can't determine types (e.g., loop-based validation instead of per-arg asserts).
# Format: {lisp_name: {param_index: [type_strings]}}
PARAM_TYPE_OVERRIDES: dict[str, dict[int, list[str]]] = {
  "+": {0: ["Num"]},
  "-": {0: ["Num"]},
  "*": {0: ["Num"]},
  "/": {0: ["Num"]},
  "==": {},
  "!=": {},
}

def param_types_to_enum(types: list[str]) -> str:
  """Convert a list of type display strings to a C param type enum."""
  if not types:
    return "BPTY_ANY"
  if len(types) == 1:
    return PARAM_TYPE_TO_ENUM.get(types[0], "BPTY_ANY")
  key = tuple(types)
  return COMPOUND_PARAM_TYPES.get(key, "BPTY_ANY")

EVAL_INTRINSICS = [
  Builtin("if", min_arity=2, max_arity=3, is_special_form=True,
          params=[Param("cond"), Param("then"), Param("else")],
          ret_type="BRET_ANY"),
  Builtin("fun", min_arity=2, max_arity=-1, is_special_form=True,
          params=[Param("name-params", types=["QExpr"]),
                  Param("body", variadic=True)],
          ret_type="BRET_FUN"),
  Builtin("case", min_arity=2, max_arity=-1, is_special_form=True,
          params=[Param("val"), Param("clauses", variadic=True)],
          ret_type="BRET_ANY"),
  Builtin("let", min_arity=2, max_arity=-1, is_special_form=True,
          params=[Param("bindings", types=["QExpr"]),
                  Param("body", variadic=True)],
          ret_type="BRET_ANY"),
  Builtin("quote", min_arity=1, max_arity=1, is_special_form=True,
          params=[Param("expr")],
          ret_type="BRET_LIST"),
  Builtin("<-", min_arity=1, max_arity=2, is_special_form=True,
          params=[Param("handle")],
          ret_type="BRET_ANY"),
  Builtin("type", min_arity=2, max_arity=-1, is_special_form=True,
          params=[Param("name-params", types=["QExpr"]),
                  Param("variants", types=["QExpr"], variadic=True)],
          ret_type="BRET_NIL"),
  Builtin("match", min_arity=2, max_arity=-1, is_special_form=True,
          params=[Param("val"), Param("clauses", variadic=True)],
          ret_type="BRET_ANY"),
  Builtin("ctx/with-deadline", min_arity=2, max_arity=-1, is_special_form=True,
          params=[Param("timeout-ms", types=["Num"]),
                  Param("body", variadic=True)],
          ret_type="BRET_ANY"),
  Builtin("ctx/with", min_arity=3, max_arity=-1, is_special_form=True,
          params=[Param("key", types=["Sym"]),
                  Param("value"),
                  Param("body", variadic=True)],
          ret_type="BRET_ANY"),
  Builtin("sig", min_arity=2, max_arity=2, is_special_form=True,
          params=[Param("name", types=["Sym"]),
                  Param("type-expr")],
          ret_type="BRET_NIL"),
]


def extract_all(project_root: Path) -> list[Builtin]:
  src_dir = project_root / "src"
  registrations = find_registrations(src_dir)

  c_files_text: dict[str, str] = {}
  for f in src_dir.rglob("*.c"):
    c_files_text[str(f)] = f.read_text()

  builtins: list[Builtin] = []

  for lisp_name, (c_func, rel_file) in sorted(registrations.items()):
    b = Builtin(lisp_name=lisp_name, c_func=c_func, source_file=rel_file)
    b.is_special_form = lisp_name in SPECIAL_FORMS
    b.ret_type = RETURN_TYPES.get(lisp_name, "BRET_ANY")

    body = None
    for path, text in c_files_text.items():
      body = extract_c_function_body(text, c_func)
      if body:
        break

    if body:
      b.min_arity, b.max_arity = parse_arity(body)
      # If the function is a thin wrapper (no arity found), follow delegation
      if b.min_arity == 0 and b.max_arity == -1:
        dbody = find_delegated_body(body, c_files_text)
        if dbody:
          b.min_arity, b.max_arity = parse_arity(dbody)
          # Also get params from delegate if we have none
          build_params(b, dbody)
        else:
          build_params(b, body)
      else:
        build_params(b, body)
    else:
      sys.stderr.write(f"WARNING: Could not find body for {c_func} ({lisp_name})\n")

    builtins.append(b)

  # Add evaluator intrinsics (special forms not registered via put_builtin)
  registered = {b.lisp_name for b in builtins}
  for intrinsic in EVAL_INTRINSICS:
    if intrinsic.lisp_name not in registered:
      builtins.append(intrinsic)

  return builtins


def c_escape(s: str) -> str:
  return s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n')


def generate_header(builtins: list[Builtin]) -> str:
  lines = []
  lines.append("// AUTO-GENERATED by scripts/gen_lsp_builtins.py — DO NOT EDIT")
  lines.append("#pragma once")
  lines.append("")
  lines.append("typedef struct {")
  lines.append("  const char *name;")
  lines.append("  int min_arity;")
  lines.append("  int max_arity;")
  lines.append("  const char *signature;")
  lines.append("  const char *doc;")
  lines.append("  int is_special_form;")
  lines.append("} lsp_builtin_entry_t;")
  lines.append("")
  lines.append("static const lsp_builtin_entry_t LSP_BUILTINS[] = {")

  for b in sorted(builtins, key=lambda x: x.lisp_name):
    sig = format_signature(b)
    doc = c_escape(b.doc) if b.doc else ""
    name = c_escape(b.lisp_name)
    sf = 1 if b.is_special_form else 0

    lines.append(f'  {{"{name}", {b.min_arity}, {b.max_arity}, '
                 f'"{c_escape(sig)}", "{doc}", {sf}}},')

  lines.append(f"  {{0, 0, 0, 0, 0, 0}}")
  lines.append("};")
  lines.append("")

  return "\n".join(lines) + "\n"


def main():
  if len(sys.argv) < 2:
    project_root = Path(__file__).parent.parent
  else:
    project_root = Path(sys.argv[1])

  builtins = extract_all(project_root)

  out_path = project_root / "src" / "lsp" / "lsp_builtins_gen.h"
  header = generate_header(builtins)
  out_path.write_text(header)

  with_arity = [b for b in builtins if b.min_arity >= 0]
  with_params = [b for b in builtins if b.params]
  with_ret = [b for b in builtins if b.ret_type != "BRET_ANY"]
  with_pty = [b for b in builtins
              if any(param_types_to_enum(p.types) != "BPTY_ANY" for p in b.params)]

  sys.stderr.write(f"Generated {out_path}:\n")
  sys.stderr.write(f"  C builtins:      {len(builtins)}\n")
  sys.stderr.write(f"  With arity:      {len(with_arity)}\n")
  sys.stderr.write(f"  With params:     {len(with_params)}\n")
  sys.stderr.write(f"  With ret type:   {len(with_ret)}\n")
  sys.stderr.write(f"  With param types: {len(with_pty)}\n")

  return 0


if __name__ == "__main__":
  sys.exit(main())
