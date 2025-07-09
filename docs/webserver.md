- [ ] Webserver
    - [ ] Async IO
        - [x] Event loop
        - [x] Sockets
        - [ ] Files
        - [-] GZip (is this even needed? im pretty sure SSL has stream
            compression)
    - [ ] URI
    - [ ] Logging
    - [ ] Regex
    - [ ] REST
        - [ ] Routing
        - [ ] Chunking
    - [x] Contiuations / green threads
    - [ ] Json Parsing
    - [ ] Html
        - [ ] Templating
    - [ ] Telemetry
    - [x] TLS 
    - [ ] mTLS
    - [ ] Caching
        - Memcache?
    - [x] HTTP Support
        - [ ] 1.1
        - [x] 2.0
        - [?] 3.0
            This thing i based On QUIC and requires UDP, so im not going to
            implement it unless i absolutely must. NGHttp3 is experimental, and
            doesnt even support most of it.
    - [ ] gRPC
    - [ ] MQTT
- [ ] DB drivers
    - [ ] SQLite
    - [ ] MySQL
- [ ] GraphQL
- [ ] Redis
- [ ] OAuth
- [ ] Websockets

## Steps for hello world implmenetation
- [x] Http webserver
- [x] Submit request to a thread pool, echo 
- [x] nghttp 2 library request handler
- [x] Http client
- [💀] liburing files
- [💀] liburing sockets

# HTTP2 Server
- [ ] Lisp FFI interface
- [ ] Redirect to https if the request is http 1.1
- [ ] Handle server errors 
    - [x] Tcp
        - [x] Gracefully handle disconnects
        - [ ] Handle too many concurrent connections
    - [ ] TLS
        - [ ] Invalid certs
        - [x] Handshake re-negotiation
        - [x] Invalid packets
    - [ ] Http
        - [ ] Handle timeouts
        - [ ] Handle too many streams
        - [ ] Handle request cancellations

- [ ] Replace OpenSSL with a lighter TLS library, like WolfSSL
- [ ] Send 2 MB worth of html data to the browser
- [ ] Dynamic flow control 
    - [ ] Initial window size with BDP (bandwidth - delay protocol)
    - [ ] Stream level window
    - [ ] Connection level window
- [ ] Figure out the proper allocation size for a session.
    I get a vey eerie feeling that nghttp2 will allocate state on every message, in the session memory pool.
    If thats the case, i might need to consider on moving that memory alloc to request level or at least consider timeout or something like that

- [x] Send `Hello World` over http 2 to the browser
    - [x] Figure out why the buffer grows indefinitely
        ```txt
        Starting server
        Listening on 0.0.0.0:6969
        Accepted connection from IP: 127.0.0.1:38714
        Feeding data to http 103
        Not sending a response ??
        Not sending a response ??
        >>> Received HTTP/2 request (stream_id=1)
        HDR: :method: GET
        HDR: :scheme: http
        HDR: :authority: 127.0.0.1:6969
        HDR: :path: /
        HDR: user-agent: curl/8.12.1
        HDR: accept: */*
        WE ARE sending a response ??
        Sending some shit
        Sending some shit 0 15
        Sending some shit
        Sending some shit 15 9
        Sending some shit
        Sending some shit 24 19
        Sending some shit
        Sending some shit 43 44
        Sending some shit
        Sending some shit 87 44
        Sending some shit
        Sending some shit 131 44
        Sending some shit
        ```
        > I didnt set a very important flag signfiying the end of stream for the response
        > you can see it like 
        ```c
          // This marks that with this call we reached the end of the file, and dont
          // call us back again
          *data_flags |= NGHTTP2_DATA_FLAG_EOF;
        ```
        - [x] Why does the buffer keep getting resized in the first place ?
    - [x] Send text/html in a single frame through a buffer
    - [x] Send it only a single time
    - [x] Setup ALPN with TLS
        Turns out i cant just have the browser talk to myserver, its too stupid to know that its http2
        Only way is with openssl
    - [x] Get browser to recognize html markup
        Only needed `text/html; charset=utf-8` as the content type.
    - [x] Upgrade http to https.
    - [x] Fix buffer sizes so that its not busted 
        ```
            Accepted connection from IP: 127.0.0.1:33292
            memory.c:51:valk_buffer_append || Buffer too small !!!  capacity [2048] :: count [0] :: new bytes [2385]
            i^Cmake: *** [Makefile:68: test] Interrupt
        ```
        Max frame size for http2 is negotiated by the protocol, on connection
        startup, so based on that we will know the size to allocate to it.
        Thats not something we want.  We want a set size by the server, and let
        the client know that is what we are working with to avoid dynamic
        allocation of said buffers
    - [x] Randomly broke curl again, hopefully this will be caught by some of my regression testing in the future 

- [ ] Arenas for futures,  (to avoid mutex alloc with pthreads, should make things much faster)

- [ ] Handle memory allocation
    - [x] Slab allocate buffers
    - [x] Slab allocate arenas
        - [x] Connection slab
            - [x] valk_aio_http_conn
            - [x] NGHttp session Arena
            - [x] OpenSSL Arena
        - [x] Random uv buffer objects (ring buffer ???)
            - write buffers
                - uv_write_t
                - uv_buf_t
                - SSL3_RT_MAX_PACKET_SIZE
            - read buffers
                - since those dont need requets or handles, i can just use raw
    - [ ] Arenas for requests

## Architecture
Ok so kindly i want to think through, what the architecture for a server could
look like.

ChatGPT as usual is giving me some fire advice for using a `Reactor` pattern
for async callbacks and stuff. Also suggesting for using command buffers to
communicate with my languages vm. Does that mean i have to get a vm for my
language now ? I really would like it to be a native llvm language.

 ┌───────────────────────────────────────────────┐
 │ 7. Lisp “surface” ▸ routers / middle-ware     │
 │    (λ (GET "/users/:id") …)                   │
 ├───────────────────────────────────────────────┤
 │ 6. Async Abstractions ▸ promise / await       │
 │    Lisp objects backed by C futures           │
 ├───────────────────────────────────────────────┤
 │ 5. FFI Shims ▸ thin C ↔ Lisp glue             │
 │    – convert GC handles <--> C pointers       │
 ├───────────────────────────────────────────────┤
 │ 4. Scheduler Bridge ▸ “green-thread” runtime  │
 │    runs inside the VM, drives event loop      │
 ├───────────────────────────────────────────────┤
 │ 3. Event Loop ▸ libuv / io_uring / kqueue     │
 │    non-blocking sockets, timers, signals      │
 ├───────────────────────────────────────────────┤
 │ 2. Protocol Engine ▸ HTTP/1.1 & (opt) H2      │
 │    parsing, HPACK, keep-alive, chunking       │
 ├───────────────────────────────────────────────┤
 │ 1. OS Layer ▸ epoll/kqueue/sendfile etc.      │
 └───────────────────────────────────────────────┘

This while thing hinges around:
1. MPSC (multiple publishers single subscriber) Queue
2. Reactor(thats the server in my architecture) and handles
3. Continuations and lisp shit


## Settings
- [ ] Dynamic settings
- [ ] Static configuration loading

## Admin Endpoints
- [ ] Visualizations
    - [ ] Slab Allocators
        - [ ] Heatmap of memory changes
        - [ ] Timelapse of changes
        - [ ] Configurable resolution
    - [ ] Arena Allocatttors
        - [ ] Request Arena
        - [ ] Heatmap of memory changes
        - [ ] Timelapse of changes
        - [ ] Configurable resolution
- [ ] Metrics
    - [ ] Prometheus endpoint
        - [ ] Counters
        - [ ] Gauges

## 🫃 URL Investigation `Remote peer returned unexpected data while we expected SETTINGS frame` 
### Bisect 

Using git bisect was totally fun, and i actually found the commit at which it started breaking: 
```git 
    d1afe4ec72ec5474056e8527d92700a53c16d179 is the first bad commit commit 
    Author: XyZyX <xzyx99@gmail.com> 
    Date:   Mon Apr 7 00:12:54 2025 -0700

    Small refactor to reduce buffering and copies

     src/aio_ssl.c | 102 +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++---------------------------------------
     src/aio_ssl.h |  32 +++++++++-----------------------
     src/aio_uv.c  |  61 +++++++++++++++++++++++++++++++------------------------------
     src/memory.c  |   4 ++++
     src/memory.h  |   1 +
     5 files changed, 108 insertions(+), 92 deletions(-)
```


Not so small of a refactor afterall

Problem: When curling my endpoint, it says there is some sort of a problem with http2 protocol. 
It seems like its not receiving an expected settings data frame.
I have never seen this error before

```
13:07:16.195164 [0-0] * SSL connection using TLSv1.3 / TLS_AES_256_GCM_SHA384 / secp256r1 / RSASSA-PSS
13:07:16.195204 [0-0] * ALPN: server accepted h2
13:07:16.195243 [0-0] * Server certificate:
13:07:16.195293 [0-0] *  subject: C=US; ST=SomeState; L=SomeCity; O=MyOrg; CN=localhost
13:07:16.195337 [0-0] *  start date: Apr 13 08:44:23 2025 GMT
13:07:16.195376 [0-0] *  expire date: Apr 13 08:44:23 2026 GMT
13:07:16.195421 [0-0] *  issuer: C=US; ST=SomeState; L=SomeCity; O=MyOrg; CN=localhost
13:07:16.195450 [0-0] *  SSL certificate verify result: self-signed certificate (18), continuing anyway.
13:07:16.195481 [0-0] *   Certificate level 0: Public key type RSA (2048/112 Bits/secBits), signed using sha256WithRSAEncryption
13:07:16.195512 [0-0] * [HTTPS-CONNECT] connect+handshake h2: 4ms, 1st data: 1ms
13:07:16.195560 [0-0] * [HTTP/2] [0] created h2 session
13:07:16.195592 [0-0] * [HTTP/2] [0] -> FRAME[SETTINGS, len=18]
13:07:16.195627 [0-0] * [HTTP/2] [0] -> FRAME[WINDOW_UPDATE, incr=1048510465]
13:07:16.195666 [0-0] * [HTTP/2] cf_connect() -> 0, 1,
13:07:16.195694 [0-0] * [HTTPS-CONNECT] connect -> 0, done=1
13:07:16.195722 [0-0] * [HTTPS-CONNECT] Curl_conn_connect(block=0) -> 0, done=1
13:07:16.195754 [0-0] * Connected to 127.0.0.1 (127.0.0.1) port 6969
13:07:16.195801 [0-0] * using HTTP/2
13:07:16.195852 [0-0] * [HTTP/2] [1] OPENED stream for https://127.0.0.1:6969/
13:07:16.195884 [0-0] * [HTTP/2] [1] [:method: GET]
13:07:16.195914 [0-0] * [HTTP/2] [1] [:scheme: https]
13:07:16.195944 [0-0] * [HTTP/2] [1] [:authority: 127.0.0.1:6969]
13:07:16.195975 [0-0] * [HTTP/2] [1] [:path: /]
13:07:16.196004 [0-0] * [HTTP/2] [1] [user-agent: curl/8.13.0]
13:07:16.196046 [0-0] * [HTTP/2] [1] [accept: */*]
13:07:16.196078 [0-0] * [HTTP/2] [1] submit -> 76, 0
13:07:16.196111 [0-0] * [HTTP/2] [1] -> FRAME[HEADERS, len=30, hend=1, eos=1]
13:07:16.196167 [0-0] * [HTTP/2] [0] egress: wrote 103 bytes
13:07:16.196210 [0-0] * [HTTP/2] [1] cf_send(len=76) -> 76, 0, eos=1, h2 windows 65535-65535 (stream-conn), buffers 0-0 (stream-conn)
13:07:16.196260 [0-0] > GET / HTTP/2
13:07:16.196260 [0-0] > Host: 127.0.0.1:6969
13:07:16.196260 [0-0] > User-Agent: curl/8.13.0
13:07:16.196260 [0-0] > Accept: */*
13:07:16.196260 [0-0] >
13:07:16.196499 [0-0] * TLSv1.3 (IN), TLS handshake, Newsession Ticket (4):
13:07:16.196587 [0-0] * TLSv1.3 (IN), TLS handshake, Newsession Ticket (4):
13:07:16.196650 [0-0] * [HTTP/2] [0] ingress: read 88 bytes
13:07:16.196682 [0-0] * Remote peer returned unexpected data while we expected SETTINGS frame.  Perhaps, peer does not support HTTP/2 properly.
13:07:16.196721 [0-0] * [HTTP/2] [0] progress ingress: inbufg=0
13:07:16.196762 [0-0] * [HTTP/2] [0] progress ingress: done
13:07:16.196794 [0-0] * [HTTP/2] [0] -> FRAME[GOAWAY, error=1, reason='SETTINGS expected', last_stream=0]
13:07:16.196825 [0-0] * nghttp2 shuts down connection with error 1: PROTOCOL_ERROR
13:07:16.196872 [0-0] * [HTTP/2] [0] egress: wrote 34 bytes
13:07:16.196913 [0-0] * [HTTP/2] [1] cf_recv(len=102400) -> -1 81, window=0/65535, connection 1048576000/1048576000
13:07:16.196960 [0-0] * Request completely sent off
13:07:17.198027 [0-0] * [HTTP/2] progress ingress, session is closed
13:07:17.198113 [0-0] * [HTTP/2] [1] cf_recv(len=102400) -> -1 16, window=0/65535, connection 1048576000/1048576000
13:07:17.198150 [0-0] * [HTTP/2] [1] premature DATA_DONE, RST stream
13:07:17.198194 [0-0] * closing connection #0
curl: (16) Remote peer returned unexpected data while we expected SETTINGS frame.  Perhaps, peer does not support HTTP/2 properly.
```


and the server logs were as follows


```
Listening on 0.0.0.0:6969
Accepted connection from IP: 127.0.0.1:36178
Feeding data to OpenSSL 517
SSL-State: before SSL initialization
SSL-State: TLSv1.3 early data
Buffed frame data 15 :: 15 :: capacity 17733
Found no data to send Skipping CB
Sending 99 bytes
Freeing 0x7bb0c000a120
Receiving on write CB
Freeing 0x7bb0c001a130
Freeing 0x7bb0c000a0c0
Freeing 0x7bb0c0030330
Feeding data to OpenSSL 523
SSL-State: TLSv1.3 early data
SSL-State: TLSv1.3 early data
Found no data to send Skipping CB
Sending 1509 bytes
Freeing 0x7bb0c000a120
Receiving on write CB
Freeing 0x7bb0c001a130
Freeing 0x7bb0c00369d0
Freeing 0x7bb0c002a530
Feeding data to OpenSSL 74
SSL-State: TLSv1.3 early data
SSL-State: SSL negotiation finished successfully
Found no data to send Skipping CB
Sending 510 bytes
Freeing 0x7bb0c000a120
Receiving on write CB
Freeing 0x7bb0c001a130
Freeing 0x7bb0c0008470
Freeing 0x7bb0c002a530
Feeding data to OpenSSL 125
Not sending a response ??
Not sending a response ??
>>> Received HTTP/2 request (stream_id=1)
HDR: :method: GET
HDR: :scheme: https
HDR: :authority: 127.0.0.1:6969
HDR: :path: /
HDR: user-agent: curl/8.13.0
HDR: accept: */*
WE ARE sending a response ??
Buffed frame data 9 :: 9 :: capacity 17733
Buffed frame data 30 :: 39 :: capacity 17733
Looking to get 16384 bytes
Buffed frame data 49 :: 88 :: capacity 17733
Found no data to send Skipping CB
Sending 110 bytes
Freeing 0x7bb0c000a120
Receiving on write CB
Freeing 0x7bb0c001a130
Freeing 0x7bb0c0008470
Freeing 0x7bb0c002a530
Feeding data to OpenSSL 56
Received GO AWAY frame
Not sending a response ??
Found no data to send Skipping CB
Nothing to send 0 
Freeing 0x7bb0c001a130
Freeing 0x7bb0c000a120
EOF infact
```

Not very helpful...

### The error

Rude 
    > Perhaps, peer does not support HTTP/2 properly


    > Remote peer returned unexpected data while we expected SETTINGS frame.

Server sent  GOAWAY frame, is there any way to log that in my http shit ?
    > 13:07:16.196794 [0-0] * [HTTP/2] [0] -> FRAME[GOAWAY, error=1, reason='SETTINGS expected', last_stream=0]


ok so i think  i can now log it inmy shit

```c
  if (frame->hd.type == NGHTTP2_GOAWAY) {
    printf("Received GO AWAY frame\n");
  }
```


Ok so what data DID we send ?
well turns out that since i got rid of staging the logic is more complicated now for managing the buffers

when connection is initialized i generate the settings frame in here

```c
    // Send settings to the client
    __http_send_server_connection_header(conn->session);
```

```c
  int status = valk_aio_ssl_on_read(&conn->ssl, &In, &Out, conn,
                                    __http_tcp_unencrypted_read_cb);

  // Only do this if ssl is established:
  if (!status) {
    // Flushies
    In.count = 0;
    memset(In.items, 0, In.capacity);
    __http2_flush_frames(&In, conn);

    // Encrypt the new data n stuff
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);
  }
```

essentially if ssl connection is not established  we cannot flush the buffer,
which means that when i try to do that it will essentially endup in /dev/null
and dissapear.  Browser is chill about not receiving settings, as the immediate
next data will come through with the response, but curl is really anal about
the protocol because settings frame is required from both parties in the
beginning of the session

# Http2 Client
- [x] TCP
    - [x] connection
    - [💀] pooling ? 
        - is that even necessary anymore?
- [ ] SSL connection
    - [x] handshake
    - [x] ALPN upgrade
    - [ ] Cert validation
- [x] Http2 session
    - [x] Initialization, with simple settings frame
- [x] Http2 request response
- [ ] Lisp FFI
    - [x] Lval reference counting
        - [x] Lenv reference counting
    - [ ] Refactor lvals to arenas
        - Right now the memory management is all fucked up...
    - [x] Pointers / References support
    - [ ] Async API for awaiting on futures / promises
    - [ ] Continuation support
    - [ ] Request / Response hanlders
    - [ ] Lisp api for making web requests
    - [ ] Test with a lisp client
- [ ] Streaming callback
- [ ] Upload 2MB worth of data
- [ ] Download 2MB worth of data
- [ ] Connection pooling
- [ ] Request cancellation
- [ ] Retries

# Testing
## nghttpx proxy
In order to debug the protocol handling for various conditions it might be
useful to setup a reverse proxy to google or another website thats already setup.
That way you can log the interaction for ssl and the http2 frames.

This can be done using the nghttp2 utility as follows:

```bash
    nghttpx -L INFO -b 'google.com,443;;tls' build/server.key build/server.crt
```

this will start a server on `localhost:3000` by default, and then you can use
it like normal



1. Connection slabs per thread
2. Server ARC


- Start connection
    - Create SSL instance from context
    - Create HTTP session
    - Begin ssl handshake / read loop
    - Call `onConnect` callback

- Kill connection
    - [Do i want connection drain ?] -- not initially, lets just drop
        everything
    - Complete or cancel inflight requests
        - Terminate HTTP session
        - Terminate SSL session
        - Terminate TCP connection
    - Cleanup 
    - Call the handler with `onDisconnect`

