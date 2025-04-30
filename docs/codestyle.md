# Codestyle

## C
Im new to C, so the coding style is going to be rather simple. I want to keep
things loosey goosey for now but eventually will need to enforce it somehow.

### Namespacing
### Types
### Structs 

### Arc References
Arc reference counting is used primarily for async code. Its the job of the
function called with a reference to grab it for the duration of processing. And
then release it on result.

#### Caller
##### Instantiating
When instantiating a new box, you must decide if you want to retain ownership
of the reference or pass it on to something else When the shit gets instaniated
you will without a doubt have the only reference, if you free it at the end it
will be reaped

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


