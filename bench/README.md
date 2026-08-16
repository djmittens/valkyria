# bench

HTTP/2 load-testing and benchmarking tools, written in Valk against the
runtime's own `http2/` client and `aio/` system.

## Layout

| File | Purpose |
|---|---|
| `bench.valk` | Benchmarking tool: per-request latency tracking, min/max/mean, bucketed latency distribution, connection reuse |
| `hey.valk` | Simple load generator (hey-style): configurable host/port/path, request count, concurrency |
| `test_server.valk` | Local HTTP/2 server on :18443 to point the tools at |
| `test_client.valk` | Minimal single-request client smoke test |

## Usage

```sh
build/valk bench/test_server.valk   # terminal 1
build/valk bench/hey.valk           # terminal 2 (or bench/bench.valk)
```

Configuration lives in `cfg-*` defs at the top of each tool.
