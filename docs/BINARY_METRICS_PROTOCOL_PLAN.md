# Binary Metrics Protocol Plan

## Overview

Replace JSON encoding for SSE metrics deltas with a binary protocol to reduce bandwidth by ~50-70%.

## Current State Analysis

### Current JSON Format (`src/metrics_delta.c:301-382`)

```json
{"ts":40551668053,"interval_us":100223,"changed":2,"counters_changed":1,"gauges_changed":1,"histograms_changed":0,"deltas":[{"n":"event_loop_iterations","t":"c","d":1,"l":{"loop":"main"}},{"n":"event_loop_idle_us","t":"g","v":9394464,"l":{"loop":"main"}}]}
```

**Size breakdown for typical idle update:**
- Header/metadata: ~80 bytes
- Per counter delta: ~60 bytes (`{"n":"event_loop_iterations","t":"c","d":1,"l":{"loop":"main"}}`)
- Per gauge delta: ~55 bytes
- Total typical update: ~200 bytes

### Bandwidth Impact

| Scenario | JSON (current) | Binary (projected) | Savings |
|----------|---------------|-------------------|---------|
| Idle (3 metrics) | 200 bytes | 60-80 bytes | 60-70% |
| Light load (8 metrics) | 500 bytes | 150-200 bytes | 60-70% |
| Heavy load (15 metrics) | 1000 bytes | 300-400 bytes | 60-70% |

---

## Protocol Options Comparison

### Option A: MessagePack

**Pros:**
- Self-describing (like JSON but binary)
- Wide language support
- Simple API
- Single header library available (cmp.h)

**Cons:**
- Larger than custom binary (schema overhead)
- ~30% overhead vs custom format

**Estimated size:** 80-100 bytes for typical update

### Option B: Custom Binary Format

**Pros:**
- Minimal size (no schema overhead)
- Zero dependencies
- Full control over encoding

**Cons:**
- Must maintain encoder/decoder in sync
- No tooling for debugging
- More code to write

**Estimated size:** 50-70 bytes for typical update

### Option C: Protocol Buffers (protobuf)

**Pros:**
- Industry standard
- Schema evolution support
- Excellent tooling

**Cons:**
- Requires code generation
- Complex build integration
- Overkill for this use case

**Estimated size:** 70-90 bytes for typical update

---

## Recommendation: Custom Binary Format

For a debug dashboard with simple, stable schema, a custom binary format provides the best size reduction with minimal complexity.

---

## Binary Format Specification

### Header (12 bytes fixed)

```
Offset  Size  Type      Field
------  ----  --------  -----
0       4     uint32    magic (0x564D4454 = "VMDT")
4       4     uint32    timestamp_us (lower 32 bits, wraps every ~71 minutes)
8       2     uint16    interval_us (max 65ms, sufficient for 100ms intervals)
10      1     uint8     delta_count
11      1     uint8     flags (bit 0: has_counters, bit 1: has_gauges, bit 2: has_histograms)
```

### Delta Entry (variable size)

```
Offset  Size  Type      Field
------  ----  --------  -----
0       1     uint8     type (0=counter, 1=gauge, 2=histogram)
1       1     uint8     name_id (index into string table, 0-255)
2       1     uint8     label_count
3+      var   labels[]  label entries (key_id:uint8, value_id:uint8 pairs)
N       var   value     type-specific value encoding
```

### Value Encoding

**Counter (type=0):**
```
Size  Type      Field
----  --------  -----
1-5   varint    delta (1-5 bytes depending on magnitude)
```

**Gauge (type=1):**
```
Size  Type      Field
----  --------  -----
1-9   varsint   value (signed varint, 1-9 bytes)
```

**Histogram (type=2):**
```
Size  Type      Field
----  --------  -----
1-5   varint    count_delta
1-5   varint    sum_delta_micros
```

### String Table

Sent once on connection, referenced by index:
```
Offset  Size  Type      Field
------  ----  --------  -----
0       2     uint16    table_size
2       var   entries[] null-terminated strings
```

### Example Encoding

Current JSON (193 bytes):
```json
{"ts":40551668053,"interval_us":100223,"changed":2,"counters_changed":1,"gauges_changed":1,"histograms_changed":0,"deltas":[{"n":"event_loop_iterations","t":"c","d":1,"l":{"loop":"main"}},{"n":"event_loop_idle_us","t":"g","v":9394464,"l":{"loop":"main"}}]}
```

Binary equivalent (26 bytes):
```
Header (12 bytes):
  56 4D 44 54          magic "VMDT"
  55 A3 2B 02          timestamp (lower 32 bits)
  7F 87                interval_us (100223 as uint16... or use scaling)
  02                   delta_count = 2
  03                   flags = has_counters | has_gauges

Delta 0 - Counter (6 bytes):
  00                   type = counter
  00                   name_id = 0 (event_loop_iterations)
  01                   label_count = 1
  00 00                label: key_id=0 (loop), value_id=0 (main)
  01                   delta = 1 (varint)

Delta 1 - Gauge (9 bytes):
  01                   type = gauge
  01                   name_id = 1 (event_loop_idle_us)
  01                   label_count = 1
  00 00                label: key_id=0 (loop), value_id=0 (main)
  E0 B4 8D 09          value = 9394464 (varint, 4 bytes)
```

**Savings: 193 → 27 bytes = 86% reduction**

---

## Implementation Tasks

### Phase 1: Infrastructure (C side)

#### Task 1.1: Add string table to SSE connection state
**File:** `src/aio_sse_stream_registry.c`
**Lines:** Add to `valk_sse_stream_t` struct (~line 25)

```c
// Add to valk_sse_stream_t struct
typedef struct {
  // ... existing fields ...

  // Binary protocol string table
  const char *string_table[256];
  uint8_t string_count;
  bool string_table_sent;
} valk_sse_stream_t;
```

**Test case:**
```c
void test_string_table_init(void) {
  valk_sse_stream_t stream = {0};
  assert(stream.string_count == 0);
  assert(!stream.string_table_sent);
}
```

#### Task 1.2: Implement varint encoding
**File:** `src/metrics_delta.c`
**Lines:** Add after line 25 (after timestamp utilities)

```c
// Varint encoding (protobuf-style, 7 bits per byte, MSB = continuation)
static size_t encode_varint(uint64_t value, uint8_t *buf) {
  size_t i = 0;
  while (value >= 0x80) {
    buf[i++] = (value & 0x7F) | 0x80;
    value >>= 7;
  }
  buf[i++] = value & 0x7F;
  return i;
}

// Signed varint (zigzag encoding)
static size_t encode_varsint(int64_t value, uint8_t *buf) {
  uint64_t zigzag = (value << 1) ^ (value >> 63);
  return encode_varint(zigzag, buf);
}

static uint64_t decode_varint(const uint8_t *buf, size_t *bytes_read) {
  uint64_t result = 0;
  size_t shift = 0;
  size_t i = 0;
  while (buf[i] & 0x80) {
    result |= (uint64_t)(buf[i] & 0x7F) << shift;
    shift += 7;
    i++;
  }
  result |= (uint64_t)(buf[i] & 0x7F) << shift;
  *bytes_read = i + 1;
  return result;
}
```

**Test cases:**
```c
void test_varint_encoding(void) {
  uint8_t buf[16];

  // Single byte values (0-127)
  assert(encode_varint(0, buf) == 1 && buf[0] == 0x00);
  assert(encode_varint(1, buf) == 1 && buf[0] == 0x01);
  assert(encode_varint(127, buf) == 1 && buf[0] == 0x7F);

  // Two byte values (128-16383)
  assert(encode_varint(128, buf) == 2);
  assert(encode_varint(300, buf) == 2);

  // Larger values
  assert(encode_varint(9394464, buf) == 4);  // typical idle_us value

  // Round-trip
  size_t bytes_read;
  assert(decode_varint(buf, &bytes_read) == 9394464);
  assert(bytes_read == 4);
}

void test_varsint_encoding(void) {
  uint8_t buf[16];

  // Positive values
  assert(encode_varsint(0, buf) == 1);
  assert(encode_varsint(1, buf) == 1);

  // Negative values (zigzag encoded)
  assert(encode_varsint(-1, buf) == 1 && buf[0] == 0x01);
  assert(encode_varsint(-64, buf) == 1);
}
```

#### Task 1.3: Implement binary delta encoder
**File:** `src/metrics_delta.c`
**Lines:** Add after `valk_delta_to_json` (~line 382)

```c
#define VALK_BINARY_MAGIC 0x564D4454  // "VMDT"

typedef struct {
  const char **strings;
  uint8_t count;
} valk_string_table_t;

static uint8_t get_or_add_string(valk_string_table_t *table, const char *str) {
  // Check if string already in table
  for (uint8_t i = 0; i < table->count; i++) {
    if (table->strings[i] == str || strcmp(table->strings[i], str) == 0) {
      return i;
    }
  }
  // Add new string
  if (table->count < 255) {
    table->strings[table->count] = str;
    return table->count++;
  }
  return 0;  // Fallback to first entry on overflow
}

size_t valk_delta_to_binary(const valk_delta_snapshot_t *snap,
                            uint8_t *buf, size_t buf_size,
                            valk_string_table_t *strings,
                            bool *strings_changed) {
  if (buf_size < 12) return 0;

  uint8_t *p = buf;
  uint8_t *end = buf + buf_size;
  uint8_t initial_string_count = strings->count;

  // Header (12 bytes)
  *(uint32_t *)p = VALK_BINARY_MAGIC;
  p += 4;
  *(uint32_t *)p = (uint32_t)(snap->timestamp_us & 0xFFFFFFFF);
  p += 4;
  *(uint16_t *)p = (uint16_t)(snap->interval_us > 65535 ? 65535 : snap->interval_us);
  p += 2;
  *p++ = (uint8_t)(snap->delta_count > 255 ? 255 : snap->delta_count);
  *p++ = (snap->counters_changed > 0 ? 0x01 : 0) |
         (snap->gauges_changed > 0 ? 0x02 : 0) |
         (snap->histograms_changed > 0 ? 0x04 : 0);

  // Deltas
  for (size_t i = 0; i < snap->delta_count && p < end - 16; i++) {
    const valk_metric_delta_t *d = &snap->deltas[i];

    // Type
    switch (d->type) {
      case VALK_DELTA_INCREMENT: *p++ = 0; break;
      case VALK_DELTA_SET:       *p++ = 1; break;
      case VALK_DELTA_OBSERVE:   *p++ = 2; break;
      default: continue;
    }

    // Name (string table index)
    *p++ = get_or_add_string(strings, d->name);

    // Labels
    uint8_t label_count = d->labels ? d->labels->count : 0;
    *p++ = label_count;
    for (uint8_t j = 0; j < label_count; j++) {
      *p++ = get_or_add_string(strings, d->labels->labels[j].key);
      *p++ = get_or_add_string(strings, d->labels->labels[j].value);
    }

    // Value
    switch (d->type) {
      case VALK_DELTA_INCREMENT:
        p += encode_varint(d->data.increment, p);
        break;
      case VALK_DELTA_SET:
        p += encode_varsint(d->data.value, p);
        break;
      case VALK_DELTA_OBSERVE:
        p += encode_varint(d->data.histogram.count_delta, p);
        p += encode_varint(d->data.histogram.sum_delta_micros, p);
        break;
    }
  }

  *strings_changed = (strings->count != initial_string_count);
  return p - buf;
}

size_t valk_string_table_to_binary(const valk_string_table_t *table,
                                   uint8_t *buf, size_t buf_size) {
  uint8_t *p = buf;
  uint8_t *end = buf + buf_size;

  // Magic for string table
  *(uint32_t *)p = 0x564D5354;  // "VMST"
  p += 4;

  // Count
  *(uint16_t *)p = table->count;
  p += 2;

  // Strings (null-terminated)
  for (uint8_t i = 0; i < table->count && p < end - 64; i++) {
    size_t len = strlen(table->strings[i]);
    if (p + len + 1 >= end) break;
    memcpy(p, table->strings[i], len + 1);
    p += len + 1;
  }

  return p - buf;
}
```

**Test cases:**
```c
void test_binary_delta_encoding(void) {
  valk_delta_snapshot_t snap = {0};
  snap.timestamp_us = 40551668053;
  snap.interval_us = 100223;
  snap.delta_count = 2;
  snap.counters_changed = 1;
  snap.gauges_changed = 1;

  // Setup deltas
  valk_metric_delta_t deltas[2];
  valk_label_set_v2_t labels = {
    .labels = {{.key = "loop", .value = "main"}},
    .count = 1
  };

  deltas[0] = (valk_metric_delta_t){
    .name = "event_loop_iterations",
    .type = VALK_DELTA_INCREMENT,
    .labels = &labels,
    .data.increment = 1
  };
  deltas[1] = (valk_metric_delta_t){
    .name = "event_loop_idle_us",
    .type = VALK_DELTA_SET,
    .labels = &labels,
    .data.value = 9394464
  };
  snap.deltas = deltas;

  // Encode
  uint8_t buf[256];
  const char *string_ptrs[256];
  valk_string_table_t strings = {.strings = string_ptrs, .count = 0};
  bool strings_changed;

  size_t len = valk_delta_to_binary(&snap, buf, sizeof(buf), &strings, &strings_changed);

  // Verify size reduction
  assert(len < 40);  // Should be ~27 bytes vs 193 bytes JSON
  assert(strings_changed);
  assert(strings.count == 4);  // "event_loop_iterations", "event_loop_idle_us", "loop", "main"

  // Verify magic
  assert(*(uint32_t *)buf == VALK_BINARY_MAGIC);
}
```

#### Task 1.4: Add header declaration
**File:** `src/metrics_delta.h`
**Lines:** Add after line 120 (after `valk_delta_to_json` declaration)

```c
// Binary encoding
typedef struct {
  const char **strings;
  uint8_t count;
} valk_string_table_t;

size_t valk_delta_to_binary(const valk_delta_snapshot_t *snap,
                            uint8_t *buf, size_t buf_size,
                            valk_string_table_t *strings,
                            bool *strings_changed);

size_t valk_string_table_to_binary(const valk_string_table_t *table,
                                   uint8_t *buf, size_t buf_size);
```

---

### Phase 2: SSE Integration

#### Task 2.1: Add binary format negotiation
**File:** `src/aio_sse_diagnostics.c`
**Lines:** Modify `handle_diagnostics_request` (~line 1450)

Check for `Accept: application/octet-stream` header to enable binary mode:

```c
// In request handler, check accept header
bool use_binary = false;
const char *accept = /* get Accept header */;
if (accept && strstr(accept, "application/octet-stream")) {
  use_binary = true;
}

// Store in stream state
stream->use_binary = use_binary;
```

#### Task 2.2: Modify delta emission
**File:** `src/aio_sse_diagnostics.c`
**Lines:** Modify `emit_diagnostics_delta` (~line 1580)

```c
if (stream->use_binary) {
  // Binary encoding
  uint8_t binary_buf[4096];
  bool strings_changed;

  size_t len = valk_delta_to_binary(modular_delta, binary_buf, sizeof(binary_buf),
                                    &stream->strings, &strings_changed);

  // If string table changed, send it first
  if (strings_changed) {
    uint8_t table_buf[2048];
    size_t table_len = valk_string_table_to_binary(&stream->strings,
                                                    table_buf, sizeof(table_buf));
    // Send as binary SSE event
    emit_binary_event(stream, "strings", table_buf, table_len);
  }

  // Send delta
  emit_binary_event(stream, "delta", binary_buf, len);
} else {
  // Existing JSON path
  size_t modular_len = valk_delta_to_json(modular_delta, modular_buf, sizeof(modular_buf));
  // ...
}
```

#### Task 2.3: Add binary SSE event helper
**File:** `src/aio_sse_diagnostics.c`
**Lines:** Add helper function (~line 1400)

```c
static void emit_binary_event(valk_sse_stream_t *stream,
                              const char *event_type,
                              const uint8_t *data, size_t len) {
  // SSE format with base64-encoded binary data
  // Or use raw binary with custom content-type
  char header[128];
  int header_len = snprintf(header, sizeof(header),
                            "event: %s\ndata: ", event_type);

  // Base64 encode the binary data for SSE compatibility
  char *b64 = base64_encode(data, len);

  // Send: header + base64 + "\n\n"
  valk_sse_send(stream, header, header_len);
  valk_sse_send(stream, b64, strlen(b64));
  valk_sse_send(stream, "\n\n", 2);

  free(b64);
}
```

---

### Phase 3: JavaScript Decoder

#### Task 3.1: Add binary decoder to dashboard
**File:** `src/modules/aio/debug/script.js`
**Lines:** Add after line 50 (utility functions section)

```javascript
// Binary protocol decoder
var BinaryDecoder = {
  MAGIC_DELTA: 0x564D4454,   // "VMDT"
  MAGIC_STRINGS: 0x564D5354, // "VMST"

  stringTable: [],

  decodeVarint: function(view, offset) {
    var result = 0;
    var shift = 0;
    var byte;
    var bytesRead = 0;
    do {
      byte = view.getUint8(offset + bytesRead);
      result |= (byte & 0x7F) << shift;
      shift += 7;
      bytesRead++;
    } while (byte & 0x80);
    return {value: result, bytesRead: bytesRead};
  },

  decodeVarsint: function(view, offset) {
    var v = this.decodeVarint(view, offset);
    // Zigzag decode
    v.value = (v.value >>> 1) ^ -(v.value & 1);
    return v;
  },

  decodeStringTable: function(buffer) {
    var view = new DataView(buffer);
    var magic = view.getUint32(0, true);
    if (magic !== this.MAGIC_STRINGS) return false;

    var count = view.getUint16(4, true);
    var offset = 6;
    var decoder = new TextDecoder();

    this.stringTable = [];
    for (var i = 0; i < count; i++) {
      var start = offset;
      while (view.getUint8(offset) !== 0) offset++;
      this.stringTable.push(decoder.decode(buffer.slice(start, offset)));
      offset++; // Skip null terminator
    }
    return true;
  },

  decodeDelta: function(buffer) {
    var view = new DataView(buffer);
    var magic = view.getUint32(0, true);
    if (magic !== this.MAGIC_DELTA) return null;

    var result = {
      timestamp_us: view.getUint32(4, true),
      interval_us: view.getUint16(8, true),
      delta_count: view.getUint8(10),
      flags: view.getUint8(11),
      deltas: []
    };

    var offset = 12;
    for (var i = 0; i < result.delta_count; i++) {
      var delta = {};
      var type = view.getUint8(offset++);
      delta.t = ['c', 'g', 'h'][type];
      delta.n = this.stringTable[view.getUint8(offset++)];

      var labelCount = view.getUint8(offset++);
      if (labelCount > 0) {
        delta.l = {};
        for (var j = 0; j < labelCount; j++) {
          var key = this.stringTable[view.getUint8(offset++)];
          var val = this.stringTable[view.getUint8(offset++)];
          delta.l[key] = val;
        }
      }

      if (type === 0) { // Counter
        var v = this.decodeVarint(view, offset);
        delta.d = v.value;
        offset += v.bytesRead;
      } else if (type === 1) { // Gauge
        var v = this.decodeVarsint(view, offset);
        delta.v = v.value;
        offset += v.bytesRead;
      } else if (type === 2) { // Histogram
        var c = this.decodeVarint(view, offset);
        delta.c = c.value;
        offset += c.bytesRead;
        var s = this.decodeVarint(view, offset);
        delta.s = s.value;
        offset += s.bytesRead;
      }

      result.deltas.push(delta);
    }

    return result;
  }
};
```

#### Task 3.2: Modify SSE event handler
**File:** `src/modules/aio/debug/script.js`
**Lines:** Modify EventSource handler (~line 2755)

```javascript
// Add binary event handlers
eventSource.addEventListener('strings', function(e) {
  var binary = base64ToArrayBuffer(e.data);
  BinaryDecoder.decodeStringTable(binary);
});

eventSource.addEventListener('delta', function(e) {
  var binary = base64ToArrayBuffer(e.data);
  var delta = BinaryDecoder.decodeDelta(binary);
  if (delta) {
    // Convert to same format as JSON deltas for existing code
    handleModularDelta({
      ts: delta.timestamp_us,
      interval_us: delta.interval_us,
      deltas: delta.deltas
    });
  }
});

// Base64 decoder helper
function base64ToArrayBuffer(base64) {
  var binary = atob(base64);
  var len = binary.length;
  var bytes = new Uint8Array(len);
  for (var i = 0; i < len; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes.buffer;
}
```

#### Task 3.3: Add format negotiation
**File:** `src/modules/aio/debug/script.js`
**Lines:** Modify SSE connection setup (~line 2750)

```javascript
// Request binary format if supported
var useBinary = true; // Could be a user preference

if (useBinary) {
  // Use fetch to establish connection with Accept header
  // Then switch to EventSource-like handling
  fetch('/debug/diagnostics/memory', {
    headers: {'Accept': 'application/octet-stream'}
  }).then(function(response) {
    // Handle binary streaming...
  });
} else {
  // Existing EventSource path
  eventSource = new EventSource('/debug/diagnostics/memory');
}
```

---

### Phase 4: Testing

#### Task 4.1: Create binary protocol test file
**File:** `test/test_binary_metrics.c`

```c
#include "testing.h"
#include "metrics_delta.h"

TEST(binary_varint_small_values) {
  uint8_t buf[16];
  ASSERT_EQ(encode_varint(0, buf), 1);
  ASSERT_EQ(buf[0], 0x00);
  ASSERT_EQ(encode_varint(127, buf), 1);
  ASSERT_EQ(buf[0], 0x7F);
}

TEST(binary_varint_multibyte) {
  uint8_t buf[16];
  ASSERT_EQ(encode_varint(128, buf), 2);
  ASSERT_EQ(encode_varint(16383, buf), 2);
  ASSERT_EQ(encode_varint(16384, buf), 3);
}

TEST(binary_varint_roundtrip) {
  uint8_t buf[16];
  uint64_t values[] = {0, 1, 127, 128, 255, 256, 16383, 16384,
                       9394464, 100000000, UINT64_MAX};
  for (size_t i = 0; i < sizeof(values)/sizeof(values[0]); i++) {
    size_t written = encode_varint(values[i], buf);
    size_t read;
    uint64_t decoded = decode_varint(buf, &read);
    ASSERT_EQ(written, read);
    ASSERT_EQ(decoded, values[i]);
  }
}

TEST(binary_varsint_negative) {
  uint8_t buf[16];
  // Zigzag encoding: -1 -> 1, -2 -> 3, etc.
  ASSERT_EQ(encode_varsint(-1, buf), 1);
  ASSERT_EQ(buf[0], 0x01);
  ASSERT_EQ(encode_varsint(-64, buf), 1);
}

TEST(binary_delta_size_reduction) {
  // Setup typical delta
  valk_delta_snapshot_t snap = {0};
  snap.timestamp_us = 40551668053;
  snap.interval_us = 100223;
  snap.delta_count = 2;
  snap.counters_changed = 1;
  snap.gauges_changed = 1;

  valk_metric_delta_t deltas[2];
  valk_label_set_v2_t labels = {
    .labels = {{.key = "loop", .value = "main"}},
    .count = 1
  };
  deltas[0] = (valk_metric_delta_t){
    .name = "event_loop_iterations",
    .type = VALK_DELTA_INCREMENT,
    .labels = &labels,
    .data.increment = 1
  };
  deltas[1] = (valk_metric_delta_t){
    .name = "event_loop_idle_us",
    .type = VALK_DELTA_SET,
    .labels = &labels,
    .data.value = 9394464
  };
  snap.deltas = deltas;

  // Encode as JSON
  char json_buf[1024];
  size_t json_len = valk_delta_to_json(&snap, json_buf, sizeof(json_buf));

  // Encode as binary
  uint8_t binary_buf[256];
  const char *string_ptrs[256];
  valk_string_table_t strings = {.strings = string_ptrs, .count = 0};
  bool strings_changed;
  size_t binary_len = valk_delta_to_binary(&snap, binary_buf, sizeof(binary_buf),
                                           &strings, &strings_changed);

  // Binary should be significantly smaller
  ASSERT_LT(binary_len, json_len / 2);
  printf("JSON: %zu bytes, Binary: %zu bytes (%.0f%% reduction)\n",
         json_len, binary_len, 100.0 * (1.0 - (double)binary_len / json_len));
}

TEST(binary_string_table) {
  const char *string_ptrs[256];
  valk_string_table_t strings = {.strings = string_ptrs, .count = 0};

  uint8_t id1 = get_or_add_string(&strings, "hello");
  uint8_t id2 = get_or_add_string(&strings, "world");
  uint8_t id3 = get_or_add_string(&strings, "hello");  // Duplicate

  ASSERT_EQ(id1, 0);
  ASSERT_EQ(id2, 1);
  ASSERT_EQ(id3, 0);  // Same as first "hello"
  ASSERT_EQ(strings.count, 2);
}

SUITE(binary_metrics) {
  RUN_TEST(binary_varint_small_values);
  RUN_TEST(binary_varint_multibyte);
  RUN_TEST(binary_varint_roundtrip);
  RUN_TEST(binary_varsint_negative);
  RUN_TEST(binary_delta_size_reduction);
  RUN_TEST(binary_string_table);
}
```

#### Task 4.2: Add to CMakeLists.txt
**File:** `CMakeLists.txt`
**Lines:** Add near other test definitions (~line 200)

```cmake
add_executable(test_binary_metrics test/test_binary_metrics.c)
target_link_libraries(test_binary_metrics valkyria)
add_test(NAME test_binary_metrics COMMAND test_binary_metrics)
```

#### Task 4.3: Integration test
**File:** `test/test_binary_sse.valk`

```lisp
; Test binary SSE metrics streaming
(def {test-binary-sse} (lambda {}
  ; Start server with binary metrics enabled
  ; Connect with Accept: application/octet-stream
  ; Verify string table received
  ; Verify binary deltas decodable
  ; Compare bandwidth with JSON baseline
  (print "Binary SSE test placeholder")
))
```

---

## Migration Strategy

### Phase 1: Opt-in Binary (Week 1)
- Implement binary encoder in C
- Add `Accept` header check
- Keep JSON as default
- Test with manual curl requests

### Phase 2: JavaScript Decoder (Week 2)
- Implement decoder in dashboard JS
- Add toggle in dashboard UI
- A/B test bandwidth savings

### Phase 3: Default Binary (Week 3)
- Switch default to binary
- Keep JSON fallback for debugging
- Document wire format

---

## Rollback Plan

If issues arise:
1. Remove `Accept` header check to force JSON
2. Or add `?format=json` query parameter override
3. Binary encoder code remains but unused

---

## Success Metrics

| Metric | Target | Measurement |
|--------|--------|-------------|
| Bandwidth reduction | >50% | Compare SSE bytes/second |
| Encoding latency | <10µs | Benchmark `valk_delta_to_binary` |
| Decoding latency (JS) | <1ms | Browser performance.now() |
| Memory overhead | <1KB/connection | String table size |

---

## Files Modified Summary

| File | Changes |
|------|---------|
| `src/metrics_delta.h` | Add binary types and function declarations |
| `src/metrics_delta.c` | Add varint encoding, binary encoder |
| `src/aio_sse_diagnostics.c` | Add format negotiation, binary emission |
| `src/aio_sse_stream_registry.c` | Add string table to stream state |
| `src/modules/aio/debug/script.js` | Add binary decoder, format negotiation |
| `test/test_binary_metrics.c` | New test file |
| `CMakeLists.txt` | Add test binary |
