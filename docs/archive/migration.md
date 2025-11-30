# Migration Guide

## From Futures to Continuations

### Old Way (Futures/Promises)

```c
// C code
valk_future* fut = valk_aio_read_file(path);
valk_future_and_then(fut, &(struct valk_future_and_then){
    .cb = handle_result,
    .arg = user_data
});
valk_arc_release(fut);

// Callback
void handle_result(void* arg, valk_arc_box* result) {
    // Process result
    valk_arc_release(result);
}
```

### New Way (Continuations)

```lisp
; Lisp code
(reset
  (let ((data (await (read-file path))))
    (process data)))  ; Direct, linear flow
```

## Compatibility During Transition

### Temporary Shim

```c
// Convert old future-based code
valk_lval_t* future_compat(valk_future* fut) {
    return valk_builtin_shift(env,
        valk_list2(valk_lval_sym("k"),
                  adapt_future_to_cont(fut, k)));
}
```

### Gradual Migration

1. **Keep both systems** initially
2. **Convert internals** first
3. **Update examples** next
4. **Deprecate futures**
5. **Remove after grace period**

## Common Patterns

### Sequential Operations

```lisp
; Old (callback hell)
(read-file "a.txt"
  (lambda (a)
    (read-file "b.txt"
      (lambda (b)
        (process a b)))))

; New (linear)
(reset
  (let ((a (await (read-file "a.txt")))
        (b (await (read-file "b.txt"))))
    (process a b)))
```

### Error Handling

```lisp
; Old (complex)
(future-catch
  (future-then fut handle-success)
  handle-error)

; New (simple)
(reset
  (try
    (await operation)
    (catch e
      (handle-error e))))
```

### Timeouts

```lisp
; Old (manual)
(let ((fut (make-future)))
  (set-timer timeout (lambda ()
    (complete-future fut 'timeout)))
  (async-op (lambda (r)
    (complete-future fut r)))
  fut)

; New (built-in)
(reset
  (with-timeout 5000
    (await operation)))
```

## Code Changes Needed

### Remove ARC Calls

```diff
- valk_arc_retain(value);
- valk_arc_release(value);
+ // No longer needed, GC handles it
```

### Update Async Functions

```diff
- valk_future* my_async_op() {
-     valk_promise* p = promise_new();
-     start_operation(p);
-     return promise_future(p);
- }

+ valk_lval_t* my_async_op() {
+     return valk_shift(k,
+         start_operation_with_cont(k));
+ }
```

### Update Tests

```diff
- valk_future* fut = async_op();
- valk_arc_box* result = valk_future_await(fut);
- assert(result->type == VALK_SUC);
- valk_arc_release(fut);

+ valk_lval_t* result = valk_eval(env,
+     parse("(reset (await (async-op)))"));
+ assert(LVAL_TYPE(result) != LVAL_ERR);
```

## Timeline

**Week 1-2**: Both systems coexist
**Week 3-4**: Internal migration
**Week 5**: User code migration
**Week 6**: Remove old system

## Getting Help

- See [Phase 0 Documentation](phase0_continuations.md)
- Check examples in `test/test_continuations.c`
- Ask questions in issues