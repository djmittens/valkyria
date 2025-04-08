- [ ] Webserver
    - [ ] Async IO
        - [x] Event loop
        - [x] Sockets
        - [ ] Files
        - [ ] GZip
    - [ ] Logging
    - [ ] Regex
    - [ ] URI
    - [ ] HTTP Support
        - [ ] 1.1
        - [x] 2.0
        - [?] 3.0
            This thing i based On QUIC and requires UDP, so im not going to implement it unless i absolutely must.
            NGHttp3 is experimental, and doesnt even support most of it.
    - [ ] REST
        - [ ] Routing
        - [ ] Chunking
    - [ ] CoRoutines / green threads
    - [ ] Json Parsing
    - [ ] Html
        - [ ] Templating
    - [ ] Telemetry
    - [ ] TLS / mTLS
    - [ ] Caching
- [ ] DB drivers
    - [ ] SQLite
    - [ ] MySQL
- [ ] GraphQL
- [ ] Redis
- [ ] OAuth
- [ ] Websockets


## Steps for hello world implmenetation
- [ ] liburing files
- [ ] liburing sockets
- [ ] Submit request to a thread pool, echo 
- [ ] nghttp 2 library request handler
- [ ] Http webserver
- [ ] kqueue

# HTTP2 Server
- [ ] Send `Hello World` over http 2 to the browser
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
            memory.c:51:valk_buffer_append || Buffer too small !!!  capacity [2048] :: count [0] :: new bytes [2385]i^Cmake: *** [Makefile:68: test] Interrupt
        ```
        Max frame size for http2 is negotiated by the protocol, on connection startup, so based on that we will know the size to allocate to it.
        Thats not something we want.  We want a set size by the server, and let the client know that is what we are working with to avoid dynamic allocation of said buffers


- [ ] Handle memory allocation
    - [x] Slab allocate buffers
    - [ ] Slab allocate arenas
        - [ ] Connection slab
            - [ ] NGHttp connection 
            - [ ] Random uv buffer objects (ring buffer ???)
                - write requests
                    - uv_write_t
                    - uv_buf_t
                    - SSL3_RT_MAX_PACKET_SIZE
                - write buffers
    - [ ] Arenas for requests
- [ ] Send 2 MB worth of html data to the browser
- [ ] Handle errors 
    - [ ] Handle timeouts
    - [ ] Handle request cancellations
    - [ ] Handle too many connections
    - [ ] Handle too many requests

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

