# Codestyle

## C
Im new to C, so the coding style is going to be rather simple. I want to keep
things loosey goosey for now but eventually will need to enforce it somehow.


### Clang formatting
- [ ] Make a clang-format file to make formatting consistent, it seems like its
randomly changing causing unnecessary changes over time

### Namespacing
### Types
### Structs 

### Arc References
Arc reference counting is used primarily for async code. Its the job of the
function called with a reference to grab it for the duration of processing. And
then release it on result.

It will Pooo Pooo on performance as it will disable certain hardware
optimization on the value, so use with care

#### Caller
##### Ownersherip
When instantiating a new box, programmer must decide if you want to retain
ownership of the reference or pass it on to something else. When the shit gets
instaniated and there will without a doubt have the only reference, if freeing
it at the end it will be reaped

#### Callee
```c
static void __aio_client_connect_cb(valk_aio_system *sys, valk_arc_box *box,
                                    valk_promise *promise) {
  int r;
  struct sockaddr_in addr;

  valk_arc_retain(box);
//// DO stuff
    
  valk_arc_release(box);
```

#### Async
When using in the async scenario there is a transfer of ownership so, you
should document the omission To adhere to the above rule of Callee having the
responsibility for grabbing itself a reference , when resolving a future it
will also grab a second reference


