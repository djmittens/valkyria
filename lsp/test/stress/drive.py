#!/usr/bin/env python3
"""Drive valk-lsp over stdio: rapid didChange + hover/semanticTokens.

Reproduces in seconds the "3-second stall" corruption chain that CI hit
rarely (vanished bindings -> id:null responses -> workers spinning).

On stall (no response for STALL_S while requests outstanding), gdb-attach
and dump all thread stacks, then kill. Everything is bounded.

Usage:
    python3 lsp/test/stress/drive.py [workspace-dir]

Environment:
    KEYS=500          number of keystrokes to simulate
    CADENCE_MS=25     delay between keystrokes
    STALL_S=10        request timeout before declaring a stall
    OUT=<tmpdir>      output directory for logs and stack dumps
    KEEP_ALIVE_S=0    keep server alive after stall for inspection
    VALK_GC_VERIFY / VALK_GC_VERIFY_ROOTS / VALK_GC_CONCURRENT
                      passed through to the server unchanged
"""
import io, json, os, subprocess, sys, tempfile, threading, time, shutil, signal

REPO = os.path.dirname(os.path.abspath(os.path.join(__file__, "..", "..", "..")))
N_KEYS = int(os.environ.get("KEYS", "500"))
CADENCE_S = float(os.environ.get("CADENCE_MS", "25")) / 1000.0
STALL_S = float(os.environ.get("STALL_S", "10"))
OUT = os.environ.get("OUT") or tempfile.mkdtemp(prefix="lsp-stress-")
WS = sys.argv[1] if len(sys.argv) > 1 else os.path.join(OUT, "ws")

os.makedirs(OUT, exist_ok=True)
if os.path.exists(WS): shutil.rmtree(WS)
shutil.copytree(f"{REPO}/lsp/test/uat/fixtures", WS)
print(f"[driver] out={OUT}", flush=True)

stderr_f = open(f"{OUT}/server-stderr.log", "wb")
T0 = time.monotonic()
rxlog = open(f"{OUT}/rx.log", "w")
proc = subprocess.Popen([f"{REPO}/build/valk-lsp"], cwd=WS,
                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                        stderr=stderr_f)
assert isinstance(proc.stdin, io.BufferedWriter) and isinstance(proc.stdout, io.BufferedReader)
srv_in, srv_out = proc.stdin, proc.stdout

server_died = threading.Event()
wlock = threading.Lock()
def send(msg):
    data = json.dumps(msg).encode()
    try:
        with wlock:
            srv_in.write(b"Content-Length: %d\r\n\r\n" % len(data) + data)
            srv_in.flush()
    except BrokenPipeError:
        server_died.set()

responses = {}          # id -> (msg, t)
resp_cv = threading.Condition()
notifications = []
corruption = []

def reader():
    buf = b""
    while True:
        while b"\r\n\r\n" not in buf:
            chunk = srv_out.read1(65536)
            if not chunk:
                server_died.set()
                with resp_cv: resp_cv.notify_all()
                return
            buf += chunk
        head, buf = buf.split(b"\r\n\r\n", 1)
        clen = 0
        for line in head.split(b"\r\n"):
            if line.lower().startswith(b"content-length:"):
                clen = int(line.split(b":")[1])
        while len(buf) < clen:
            chunk = srv_out.read1(65536)
            if not chunk:
                server_died.set()
                with resp_cv: resp_cv.notify_all()
                return
            buf += chunk
        body, buf = buf[:clen], buf[clen:]
        msg = json.loads(body)
        rxlog.write(f"{time.monotonic()-T0:9.3f} {json.dumps(msg)[:200]}\n"); rxlog.flush()
        if "id" in msg and "method" in msg:
            # server->client request: answer null (like a permissive client)
            send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
        elif "id" in msg and msg["id"] is not None:
            with resp_cv:
                responses[msg["id"]] = (msg, time.monotonic())
                resp_cv.notify_all()
        elif "error" in msg:
            print(f"[driver] CORRUPTION EVENT: {json.dumps(msg)[:300]}", flush=True)
            corruption.append(msg)
        else:
            notifications.append(msg.get("method"))

threading.Thread(target=reader, daemon=True).start()

def dump_stacks(tag):
    rc = proc.poll()
    if rc is not None or server_died.is_set():
        print(f"[driver] STALL ({tag}) - server ALREADY DEAD "
              f"(exit={rc}); see {OUT}/server-stderr.log", flush=True)
        stderr_f.flush()
        subprocess.run(["tail", "-40", f"{OUT}/server-stderr.log"])
        return
    print(f"[driver] STALL ({tag}) - dumping stacks of pid {proc.pid}", flush=True)
    for s in range(3):
        with open(f"{OUT}/stall-stacks-{tag}-s{s}.txt", "w") as f:
            subprocess.run(["gdb", "-p", str(proc.pid), "-batch",
                            "-ex", "set pagination off",
                            "-ex", "info threads",
                            "-ex", "thread apply all bt"],
                           stdout=f, stderr=subprocess.STDOUT, timeout=60)
        time.sleep(2)
    keep = float(os.environ.get("KEEP_ALIVE_S", "0"))
    if keep > 0:
        print(f"[driver] keeping pid {proc.pid} alive {keep}s for inspection", flush=True)
        end = time.monotonic() + keep
        k = 0
        while time.monotonic() < end and not server_died.is_set():
            time.sleep(15)
            k += 1
            r2, e2 = request("textDocument/hover", {"textDocument": {"uri": uri}, "position": {"line": 5, "character": 6}}, 5)
            print(f"[driver] keepalive probe {k}: {'ok %.0fms' % (e2*1000) if r2 is not None else 'TIMEOUT'}", flush=True)

rid = [0]
def request(method, params, timeout):
    rid[0] += 1
    i = rid[0]
    t0 = time.monotonic()
    send({"jsonrpc": "2.0", "id": i, "method": method, "params": params})
    with resp_cv:
        while i not in responses:
            if server_died.is_set():
                return None, time.monotonic() - t0
            remaining = timeout - (time.monotonic() - t0)
            if remaining <= 0:
                return None, time.monotonic() - t0
            resp_cv.wait(min(remaining, 0.25))
    return responses.pop(i)[0], time.monotonic() - t0

uri = f"file://{WS}/medium.valk"
text = open(f"{WS}/medium.valk").read()

r, el = request("initialize", {
    "processId": os.getpid(), "rootUri": f"file://{WS}",
    "capabilities": {"general": {"positionEncodings": ["utf-8", "utf-16"]},
                     "workspace": {"semanticTokens": {"refreshSupport": True}}},
}, 15)
assert r, "initialize timed out"
send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
    "textDocument": {"uri": uri, "languageId": "valk", "version": 1, "text": text}}})

# find blank line after line 30 (mimic the UAT)
lines = text.split("\n")
target = next(i for i in range(30, len(lines)) if lines[i].strip() == "")

sample = "(def {scratch} (+ 1 2 3)) "
version = 1
lat = []
timeouts = 0
t_start = time.monotonic()
for i in range(N_KEYS):
    ch = sample[i % len(sample)]
    col = i  # keep appending on the same line
    version += 1
    send({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
        "textDocument": {"uri": uri, "version": version},
        "contentChanges": [{"range": {"start": {"line": target, "character": col},
                                       "end": {"line": target, "character": col}},
                            "text": ch}]}})
    time.sleep(CADENCE_S)
    method = "textDocument/hover" if i % 2 == 0 else "textDocument/semanticTokens/full"
    params = ({"textDocument": {"uri": uri}, "position": {"line": target, "character": max(0, col)}}
              if i % 2 == 0 else {"textDocument": {"uri": uri}})
    r, el = request(method, params, STALL_S)
    lat.append(el * 1000)
    if corruption:
        print("[driver] stopping on corruption event", flush=True)
        dump_stacks(f"corrupt{i}")
        break
    if r is None:
        timeouts += 1
        dump_stacks(f"iter{i}")
        if not server_died.is_set():
            pr, pel = request("textDocument/hover", {"textDocument": {"uri": uri}, "position": {"line": 5, "character": 6}}, 5)
            print(f"[driver] post-stall probe: {'ANSWERED in %.0fms' % (pel*1000) if pr is not None else 'TIMED OUT'}", flush=True)
            pr2, pel2 = request("textDocument/semanticTokens/full", {"textDocument": {"uri": uri}}, 5)
            print(f"[driver] post-stall tokens probe: {'ANSWERED in %.0fms' % (pel2*1000) if pr2 is not None else 'TIMED OUT'}", flush=True)
        break
    if i % 50 == 0:
        print(f"[driver] iter {i}: {el*1000:.0f}ms  (max so far {max(lat):.0f}ms)", flush=True)

lat.sort()
if lat:
    p = lambda q: lat[min(len(lat)-1, int(len(lat)*q/100))]
    print(f"[driver] n={len(lat)} timeouts={timeouts} p50={p(50):.0f}ms p95={p(95):.0f}ms p99={p(99):.0f}ms max={lat[-1]:.0f}ms total={time.monotonic()-t_start:.1f}s", flush=True)

if server_died.is_set() or timeouts or corruption:
    print("[driver] RESULT: STALL", flush=True)
    rc = 1
else:
    print("[driver] RESULT: CLEAN", flush=True)
    rc = 0

if proc.poll() is None:
    proc.send_signal(signal.SIGTERM)
    try: proc.wait(5)
    except subprocess.TimeoutExpired: proc.kill()
sys.exit(rc)
