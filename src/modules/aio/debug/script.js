// Valkyria Dashboard - Real-time Metrics Visualization
(function() {
  'use strict';

  // ==================== Configuration ====================
  var POLL_INTERVAL = 1000;
  var HISTORY_SIZE = 60;  // 60 seconds of history
  var MAX_BACKOFF = 30000;
  var GAUGE_CIRCUMFERENCE = 251.2;  // 2 * PI * 40

  // Adaptive interval system
  var adaptiveInterval = {
    min: 500,
    normal: 1000,
    slow: 5000,
    current: 1000,
    lastValues: {}
  };

  function calculateChangeRate(metrics) {
    var changes = 0;
    var total = 0;
    var keys = ['requestRate', 'errorRate', 'heapPct'];

    keys.forEach(function(key) {
      var current = metrics[key] || 0;
      var last = adaptiveInterval.lastValues[key] || current;
      var change = Math.abs(current - last) / Math.max(last, 1);
      changes += change;
      total++;
      adaptiveInterval.lastValues[key] = current;
    });

    return total > 0 ? changes / total : 0;
  }

  function getAdaptiveInterval(changeRate) {
    if (changeRate > 0.10) return adaptiveInterval.min;
    if (changeRate > 0.02) return adaptiveInterval.normal;
    return adaptiveInterval.slow;
  }

  // ==================== RLE Decoder ====================
  // Decodes RLE-encoded state string: "F16A3I2" -> "FFFFFFFFFFFFFFFFAAAII"
  function decodeRLE(rleStr) {
    if (!rleStr || rleStr.length === 0) return '';

    var result = [];
    var i = 0;
    while (i < rleStr.length) {
      var char = rleStr[i];
      i++;
      // Read the count (one or more digits following the char)
      var countStr = '';
      while (i < rleStr.length && rleStr[i] >= '0' && rleStr[i] <= '9') {
        countStr += rleStr[i];
        i++;
      }
      var count = parseInt(countStr, 10) || 1;
      // Expand: add 'count' copies of 'char'
      for (var j = 0; j < count; j++) {
        result.push(char);
      }
    }
    return result.join('');
  }

  // ==================== State ====================
  var currentBackoff = POLL_INTERVAL;
  var history = {
    requestRate: [],
    errorRate: [],
    latency: [],
    heapUsage: [],
    gcPauses: [],
    loopIterations: []
  };
  var prevMetrics = null;
  var prevTimestamp = null;
  var serverCards = {};  // Track dynamically created server cards

  // ==================== DOM Helpers ====================
  var $ = function(id) { return document.getElementById(id); };

  // ==================== Formatters ====================
  function fmt(n, d) {
    if (n === null || n === undefined) return '--';
    return d === undefined ? Math.round(n).toString() : n.toFixed(d);
  }

  function fmtCompact(n) {
    if (n === null || n === undefined) return '--';
    if (n >= 1000000000) return (n / 1000000000).toFixed(1) + 'B';
    if (n >= 1000000) return (n / 1000000).toFixed(1) + 'M';
    if (n >= 1000) return (n / 1000).toFixed(1) + 'K';
    return Math.round(n).toString();
  }

  function fmtUptime(seconds) {
    if (!seconds) return '--';
    var d = Math.floor(seconds / 86400);
    var h = Math.floor((seconds % 86400) / 3600);
    var m = Math.floor((seconds % 3600) / 60);
    var s = Math.floor(seconds % 60);
    if (d > 0) return d + 'd ' + h + 'h ' + m + 'm';
    if (h > 0) return h + 'h ' + m + 'm ' + s + 's';
    if (m > 0) return m + 'm ' + s + 's';
    return s + 's';
  }

  function fmtBytes(b) {
    if (b === null || b === undefined) return '--';
    if (b < 1024) return b + ' B';
    if (b < 1048576) return (b / 1024).toFixed(1) + ' KB';
    if (b < 1073741824) return (b / 1048576).toFixed(1) + ' MB';
    return (b / 1073741824).toFixed(2) + ' GB';
  }

  function fmtRate(bytesPerSec) {
    if (!bytesPerSec) return '0 B/s';
    if (bytesPerSec < 1024) return Math.round(bytesPerSec) + ' B/s';
    if (bytesPerSec < 1048576) return (bytesPerSec / 1024).toFixed(1) + ' KB/s';
    return (bytesPerSec / 1048576).toFixed(1) + ' MB/s';
  }

  function fmtMs(us) {
    if (!us || us === 0) return '0';
    if (us < 1000) return us + 'µs';
    if (us < 1000000) return (us / 1000).toFixed(1) + 'ms';
    return (us / 1000000).toFixed(2) + 's';
  }

  // Format latency in seconds to human-readable string
  function fmtLatency(seconds) {
    if (!seconds || seconds === 0) return '0';
    var us = seconds * 1000000;
    if (us < 1000) return Math.round(us) + 'µs';
    if (us < 10000) return (us / 1000).toFixed(1) + 'ms';
    if (us < 1000000) return Math.round(us / 1000) + 'ms';
    return (us / 1000000).toFixed(2) + 's';
  }

  // ==================== Metric Helpers ====================
  function findMetric(arr, name, labels) {
    if (!arr) return null;
    for (var i = 0; i < arr.length; i++) {
      if (arr[i].name !== name) continue;
      if (!labels) return arr[i];
      var match = true;
      for (var k in labels) {
        if (arr[i].labels && arr[i].labels[k] !== labels[k]) {
          match = false;
          break;
        }
      }
      if (match) return arr[i];
    }
    return null;
  }

  function getMetricValue(arr, name, labels) {
    var m = findMetric(arr, name, labels);
    return m ? (m.value || 0) : 0;
  }

  function groupByServer(mod) {
    var servers = {};
    var counters = mod.counters || [];
    var gauges = mod.gauges || [];
    var histograms = mod.histograms || [];

    function addServer(labels) {
      if (!labels || !labels.server || !labels.port) return null;
      var key = labels.server + ':' + labels.port;
      if (!servers[key]) {
        servers[key] = {
          key: key,
          server: labels.server,
          port: labels.port,
          counters: [],
          gauges: [],
          histograms: []
        };
      }
      return servers[key];
    }

    counters.forEach(function(c) {
      var s = addServer(c.labels);
      if (s) s.counters.push(c);
    });
    gauges.forEach(function(g) {
      var s = addServer(g.labels);
      if (s) s.gauges.push(g);
    });
    histograms.forEach(function(h) {
      var s = addServer(h.labels);
      if (s) s.histograms.push(h);
    });

    return servers;
  }

  // ==================== History Management ====================
  function pushHistory(arr, value) {
    arr.push(value);
    while (arr.length > HISTORY_SIZE) arr.shift();
  }

  function calculateRate(current, previous, deltaSeconds) {
    if (!previous || deltaSeconds <= 0) return 0;
    return (current - previous) / deltaSeconds;
  }

  // ==================== Rendering: Gauges ====================
  function updateGauge(fillId, valueId, percent, thresholds) {
    var fill = $(fillId);
    var valueEl = $(valueId);
    if (!fill || !valueEl) return;

    percent = Math.max(0, Math.min(100, percent || 0));
    var offset = GAUGE_CIRCUMFERENCE - (percent / 100) * GAUGE_CIRCUMFERENCE;
    fill.style.strokeDashoffset = offset;

    // Update color based on thresholds
    fill.classList.remove('warning', 'critical');
    if (thresholds) {
      if (percent >= thresholds.critical) {
        fill.classList.add('critical');
      } else if (percent >= thresholds.warning) {
        fill.classList.add('warning');
      }
    }

    valueEl.textContent = fmt(percent, 0);
  }

  // ==================== Rendering: GC Timeline ====================
  function renderGcTimeline(gcPauses) {
    var container = $('gc-timeline');
    if (!container) return;

    // Remove old bars (keep threshold and axis)
    var oldBars = container.querySelectorAll('.gc-timeline-bar');
    oldBars.forEach(function(bar) { bar.remove(); });

    if (!gcPauses || gcPauses.length === 0) return;

    var maxPause = Math.max.apply(null, gcPauses.map(function(p) { return p.pause; }));
    var scaleMax = Math.max(maxPause, 10); // At least 10ms scale
    var barWidth = 100 / HISTORY_SIZE;

    gcPauses.forEach(function(p, i) {
      var bar = document.createElement('div');
      bar.className = 'gc-timeline-bar';
      if (p.pause > 10) bar.classList.add('warning');
      if (p.pause > 50) bar.classList.add('critical');

      var height = (p.pause / scaleMax) * 100;
      bar.style.height = Math.max(2, height) + '%';
      bar.style.left = (i * barWidth) + '%';
      bar.style.width = Math.max(2, barWidth - 1) + 'px';

      container.appendChild(bar);
    });
  }

  // ==================== Rendering: Sparklines ====================
  function renderSparkline(containerId, data, options) {
    var container = $(containerId);
    if (!container || !data || data.length === 0) return;

    options = options || {};
    var width = container.offsetWidth || 100;
    var height = container.offsetHeight || 30;
    var max = Math.max.apply(null, data);
    if (max === 0) max = 1;

    var points = data.map(function(v, i) {
      var x = (i / (data.length - 1)) * width;
      var y = height - (v / max) * height;
      return x + ',' + y;
    }).join(' ');

    container.innerHTML = '<svg viewBox="0 0 ' + width + ' ' + height + '" preserveAspectRatio="none">' +
      '<polyline class="sparkline-line" points="' + points + '" fill="none" stroke="' + (options.color || 'var(--color-accent)') + '" stroke-width="1.5"/>' +
      '</svg>';
  }

  // ==================== Rendering: Histograms ====================
  function renderHistogram(containerId, histogram) {
    var container = $(containerId);
    if (!container) return;

    if (!histogram || !histogram.buckets || histogram.buckets.length === 0) {
      container.innerHTML = '<div style="color: var(--text-muted); text-align: center;">No data</div>';
      return;
    }

    var buckets = histogram.buckets;
    var maxCount = Math.max.apply(null, buckets.map(function(b) { return b.count; }));
    if (maxCount === 0) maxCount = 1;

    var html = '<div class="histogram-bars">';
    buckets.forEach(function(bucket) {
      var pct = (bucket.count / maxCount) * 100;
      html += '<div class="histogram-bar-wrapper">';
      html += '<div class="histogram-bar" style="height: ' + pct + '%"></div>';
      html += '<div class="histogram-label">' + bucket.le + '</div>';
      html += '</div>';
    });
    html += '</div>';

    container.innerHTML = html;
  }

  // ==================== Rendering: Progress Bars ====================
  function updateProgressBar(barId, usageId, used, total) {
    var bar = $(barId);
    var usage = $(usageId);
    if (!bar || !usage) return;

    var pct = total > 0 ? (used / total) * 100 : 0;
    bar.style.width = pct + '%';

    // Color based on usage
    bar.classList.remove('warning', 'critical');
    if (pct >= 90) bar.classList.add('critical');
    else if (pct >= 70) bar.classList.add('warning');

    usage.textContent = used + ' / ' + total;
  }

  // ==================== Rendering: AIO System Panels ====================
  var aioSystemPanels = {};  // Cache of AIO system panels by name

  function createAioSystemPanel(sys, index) {
    var name = sys.name || 'System ' + (index + 1);
    var id = 'aio-sys-' + index;

    var html =
      '<article class="panel aio-system-panel aio-expanded" id="' + id + '" aria-labelledby="' + id + '-title">' +
        '<div class="panel-header">' +
          '<div class="panel-icon aio" aria-hidden="true">' + (index + 1) + '</div>' +
          '<h3 class="panel-title" id="' + id + '-title">' + name.charAt(0).toUpperCase() + name.slice(1) + ' AIO</h3>' +
          '<div class="panel-badges">' +
            '<div class="panel-badge aio-sys-servers" title="Number of HTTP servers bound to this AIO system">-- servers</div>' +
            '<span class="section-badge"><span class="sse-dot"></span> Live</span>' +
          '</div>' +
        '</div>' +
        '<div class="panel-body">' +

          // Event Loop Stats Row
          '<div class="aio-section-block">' +
            '<div class="block-header">' +
              '<span class="block-title">Event Loop</span>' +
            '</div>' +
            '<div class="mini-stats" role="list">' +
              '<div class="mini-stat" role="listitem" title="Event loop iterations. Each iteration polls for I/O events.">' +
                '<div class="mini-stat-value aio-sys-iterations">--</div>' +
                '<div class="mini-stat-label">Loop Iters</div>' +
              '</div>' +
              '<div class="mini-stat" role="listitem" title="Total I/O events processed (reads, writes, connections, timers).">' +
                '<div class="mini-stat-value aio-sys-events">--</div>' +
                '<div class="mini-stat-label">Events</div>' +
              '</div>' +
              '<div class="mini-stat" role="listitem" title="Active libuv handles (sockets, timers, signals).">' +
                '<div class="mini-stat-value aio-sys-handles">--</div>' +
                '<div class="mini-stat-label">Handles</div>' +
              '</div>' +
              '<div class="mini-stat" role="listitem" title="Pending items in request/response queue.">' +
                '<div class="mini-stat-value aio-sys-queue">0</div>' +
                '<div class="mini-stat-label">Queue</div>' +
              '</div>' +
            '</div>' +
          '</div>' +

          // Shared Resource Pools Section
          '<div class="aio-section-block">' +
            '<div class="block-header">' +
              '<span class="block-title">Shared Resource Pools</span>' +
              '<span class="section-badge"><span class="sse-dot"></span> Live</span>' +
            '</div>' +

            // Handle Slab (AIO Handles - mixed types)
            '<div class="resource-pool-panel" id="' + id + '-handles-pool">' +
              '<div class="pool-header">' +
                '<span class="pool-name">AIO Handles</span>' +
                '<span class="pool-usage"><span class="aio-sys-handles-used">0</span> / <span class="aio-sys-handles-total">--</span> (<span class="aio-sys-handles-pct">0</span>%)</span>' +
              '</div>' +
              '<div class="pool-grid-container">' +
                '<div class="pool-grid connection-grid aio-sys-handles-grid"></div>' +
              '</div>' +
              // Handle type breakdown (inline)
              '<div class="handle-type-breakdown">' +
                '<span class="type-item type-http"><span class="type-label">HTTP</span> <span class="type-count-http">--</span></span>' +
                '<span class="type-item type-tcp"><span class="type-label">TCP</span> <span class="type-count-tcp">--</span></span>' +
                '<span class="type-item type-task"><span class="type-label">Task</span> <span class="type-count-task">--</span></span>' +
                '<span class="type-item type-timer"><span class="type-label">Timer</span> <span class="type-count-timer">--</span></span>' +
              '</div>' +
              // HTTP connection state breakdown (only for HTTP connections)
              '<div class="pool-breakdown">' +
                '<div class="breakdown-header">HTTP Connection States</div>' +
                '<div class="breakdown-by-state">' +
                  '<div class="legend-item"><span class="legend-dot active"></span> Active: <span class="state-count-active">--</span></div>' +
                  '<div class="legend-item"><span class="legend-dot idle"></span> Idle: <span class="state-count-idle">--</span></div>' +
                  '<div class="legend-item"><span class="legend-dot closing"></span> Closing: <span class="state-count-closing">--</span></div>' +
                '</div>' +
                '<div class="owner-breakdown" id="' + id + '-handles-by-owner">' +
                  '<!-- Owner table rendered dynamically by renderOwnerBreakdown() -->' +
                '</div>' +
              '</div>' +
              '<div class="pool-warnings">' +
                '<span class="capacity-warning" style="display:none">⚠ Approaching capacity</span>' +
                '<span class="overflow-warning" style="display:none">⚠ -- overflows</span>' +
              '</div>' +
            '</div>' +

            // Compact resource grids row
            '<div class="aio-slab-grid">' +
              // TCP Buffers Slab
              '<div class="memory-slab-panel compact" id="' + id + '-tcp-buffers-panel">' +
                '<div class="slab-header">' +
                  '<span class="slab-name">TCP Buffers</span>' +
                  '<span class="slab-badge aio-sys-tcp-pct">0%</span>' +
                '</div>' +
                '<div class="slab-canvas">' +
                  '<div class="slab-grid aio-sys-tcp-grid"></div>' +
                '</div>' +
                '<div class="slab-stats">' +
                  '<span><span class="aio-sys-tcp-used">0</span> / <span class="aio-sys-tcp-total">200</span></span>' +
                '</div>' +
              '</div>' +
              // Stream Arenas Slab
              '<div class="memory-slab-panel compact" id="' + id + '-stream-arenas-panel">' +
                '<div class="slab-header">' +
                  '<span class="slab-name">Stream Arenas</span>' +
                  '<span class="slab-badge aio-sys-arenas-pct">0%</span>' +
                '</div>' +
                '<div class="slab-canvas">' +
                  '<div class="slab-grid aio-sys-arenas-grid"></div>' +
                '</div>' +
                '<div class="slab-stats">' +
                  '<span><span class="aio-sys-arenas-used">0</span> / <span class="aio-sys-arenas-total">64</span></span>' +
                '</div>' +
              '</div>' +
              // Queue Slab (placeholder for pending requests)
              '<div class="memory-slab-panel compact" id="' + id + '-queue-panel">' +
                '<div class="slab-header">' +
                  '<span class="slab-name">Request Queue</span>' +
                  '<span class="slab-badge aio-sys-queue-pct">0</span>' +
                '</div>' +
                '<div class="slab-canvas">' +
                  '<div class="slab-grid aio-sys-queue-grid"></div>' +
                '</div>' +
                '<div class="slab-stats">' +
                  '<span>pending/completed</span>' +
                '</div>' +
              '</div>' +
            '</div>' +

            '<div class="memory-legend-inline">' +
              '<div class="legend-item"><div class="legend-dot free"></div><span>Free</span></div>' +
              '<div class="legend-item"><div class="legend-dot used"></div><span>Used</span></div>' +
              '<div class="legend-item"><div class="legend-dot flash"></div><span>Changed</span></div>' +
            '</div>' +
          '</div>' +

          // HTTP Servers Section (nested under AIO)
          '<div class="aio-section-block">' +
            '<div class="block-header">' +
              '<span class="block-title">HTTP Servers</span>' +
              '<span class="block-badge aio-sys-servers-count">-- servers</span>' +
              '<span class="block-badge aio-sys-servers-rate">-- req/s</span>' +
            '</div>' +
            '<div class="nested-cards-grid aio-sys-servers-container" id="' + id + '-servers-container">' +
              '<!-- Server cards will be injected here -->' +
              '<div class="aio-no-entities" style="color: var(--text-muted); font-size: 12px; padding: var(--space-md);">No HTTP servers</div>' +
            '</div>' +
          '</div>' +

          // HTTP Clients Section (nested under AIO)
          '<div class="aio-section-block">' +
            '<div class="block-header">' +
              '<span class="block-title">HTTP Clients</span>' +
              '<span class="block-badge aio-sys-clients-count">-- clients</span>' +
            '</div>' +
            '<div class="nested-cards-grid aio-sys-clients-container" id="' + id + '-clients-container">' +
              '<!-- Client cards will be injected here -->' +
              '<div class="aio-no-entities" style="color: var(--text-muted); font-size: 12px; padding: var(--space-md);">No HTTP clients</div>' +
            '</div>' +
          '</div>' +

        '</div>' +
      '</article>';

    var temp = document.createElement('div');
    temp.innerHTML = html;
    return temp.firstChild;
  }

  function updateAioSystemPanel(panel, sys) {
    var conns = sys.connections || {};
    var sysStats = sys.system || {};
    var loop = sys.loop || {};

    // Update mini-stats
    panel.querySelector('.aio-sys-iterations').textContent = fmtCompact(loop.iterations || 0);
    panel.querySelector('.aio-sys-events').textContent = fmtCompact(loop.events_processed || 0);
    panel.querySelector('.aio-sys-handles').textContent = sysStats.handles || 0;
    panel.querySelector('.aio-sys-servers').textContent = (sysStats.servers || 0) + ' servers';

    // Connection pool is now updated via SSE memory diagnostics (handles slab)
    // See MemoryDiagnostics.updateConnectionPoolFromHandles()
  }

  function updateProgressBarInPanel(panel, barSel, usageSel, used, total) {
    var bar = panel.querySelector(barSel);
    var usage = panel.querySelector(usageSel);
    if (!bar || !usage) return;

    var pct = total > 0 ? (used / total) * 100 : 0;
    bar.style.width = pct + '%';
    bar.classList.remove('warning', 'critical');
    if (pct >= 90) bar.classList.add('critical');
    else if (pct >= 70) bar.classList.add('warning');
    usage.textContent = used + ' / ' + total;
  }

  function renderAioSystems(systems) {
    var container = $('aio-systems-container');
    if (!container) return;

    // Update section badge
    $('aio-systems-badge').textContent = systems.length + ' system' + (systems.length !== 1 ? 's' : '');

    // Calculate total connections across all systems
    var totalConns = 0;
    for (var i = 0; i < systems.length; i++) {
      totalConns += (systems[i].connections || {}).active || 0;
    }
    $('aio-conns-badge').textContent = totalConns + ' conns';

    // Hide "no systems" message if we have systems
    var noSystems = $('aio-no-systems');
    if (noSystems) {
      noSystems.style.display = systems.length > 0 ? 'none' : 'block';
    }

    // Track which systems we've seen this update
    var seenPanels = {};

    for (var i = 0; i < systems.length; i++) {
      var sys = systems[i];
      var name = sys.name || 'system-' + i;
      seenPanels[name] = true;

      var panel = aioSystemPanels[name];
      if (!panel) {
        // Create new panel
        panel = createAioSystemPanel(sys, i);
        container.appendChild(panel);
        aioSystemPanels[name] = panel;
      }

      updateAioSystemPanel(panel, sys);
    }

    // Remove panels for systems that no longer exist
    for (var name in aioSystemPanels) {
      if (!seenPanels[name]) {
        aioSystemPanels[name].remove();
        delete aioSystemPanels[name];
      }
    }
  }

  // ==================== Rendering: Connection Pool Mini-Grid ====================
  var MINI_GRID_SLOTS = 50;  // Single row of 50 slots

  function renderConnPoolMiniInContainer(container, active, idle, closing, total) {
    if (!container) return;

    // Scale actual connections to 50 slots for visualization
    var scale = total > 0 ? MINI_GRID_SLOTS / total : 1;
    var scaledActive = Math.round(active * scale);
    var scaledIdle = Math.round(idle * scale);
    var scaledClosing = Math.round(closing * scale);

    // Ensure we don't exceed 50 slots
    var totalScaled = scaledActive + scaledIdle + scaledClosing;
    if (totalScaled > MINI_GRID_SLOTS) {
      var ratio = MINI_GRID_SLOTS / totalScaled;
      scaledActive = Math.floor(scaledActive * ratio);
      scaledIdle = Math.floor(scaledIdle * ratio);
      scaledClosing = MINI_GRID_SLOTS - scaledActive - scaledIdle;
    }

    // Build slots array with states
    var slots = [];
    for (var i = 0; i < scaledActive; i++) slots.push('active');
    for (var i = 0; i < scaledIdle; i++) slots.push('idle');
    for (var i = 0; i < scaledClosing; i++) slots.push('closing');
    while (slots.length < MINI_GRID_SLOTS) slots.push('');

    // Shuffle to distribute states visually (seeded for stability)
    var seed = Math.floor(Date.now() / 5000);
    for (var i = slots.length - 1; i > 0; i--) {
      var j = Math.floor(((seed * (i + 1)) % 97) / 97 * (i + 1));
      var temp = slots[i];
      slots[i] = slots[j];
      slots[j] = temp;
    }

    // Render slots
    var html = '';
    for (var i = 0; i < MINI_GRID_SLOTS; i++) {
      var cls = 'conn-pool-slot';
      if (slots[i]) cls += ' ' + slots[i];
      html += '<div class="' + cls + '"></div>';
    }
    container.innerHTML = html;
  }

  function renderConnPoolMini(active, idle, closing, total) {
    var container = $('conn-pool-mini');
    renderConnPoolMiniInContainer(container, active, idle, closing, total);
  }

  // ==================== Rendering: HTTP Server Cards ====================
  // Per-server history for sparklines
  var serverHistory = {};

  function getServerHistory(key) {
    if (!serverHistory[key]) {
      serverHistory[key] = {
        bytesIn: [],
        bytesOut: [],
        prevBytesIn: 0,
        prevBytesOut: 0
      };
    }
    return serverHistory[key];
  }

  function createServerCard(serverInfo) {
    var card = document.createElement('article');
    card.className = 'entity-card';
    card.id = 'server-' + serverInfo.key.replace(/[:.]/g, '-');

    card.innerHTML = `
      <div class="entity-header">
        <div class="entity-status ok" role="img" aria-label="Status: Healthy" title="Server health based on error rate. Green (<1% errors), Yellow (1-5% errors), Red (>5% errors)."></div>
        <h3 class="entity-name">${serverInfo.server}:${serverInfo.port}</h3>
        <div class="entity-label">HTTP</div>
        <div class="entity-stats">
          <div class="entity-stat" title="Current number of active TCP connections to this server. High connection count may indicate slow responses or connection pool exhaustion on clients.">
            <div class="entity-stat-value active-conns">--</div>
            <div class="entity-stat-label">Conns</div>
          </div>
          <div class="entity-stat" title="Requests per second on this server. Compare with historical baseline to detect anomalies. Sudden drops may indicate upstream issues.">
            <div class="entity-stat-value req-rate">--/s</div>
            <div class="entity-stat-label">Req</div>
          </div>
        </div>
        <button class="expand-toggle" onclick="this.closest('.entity-card').classList.toggle('collapsed')" aria-label="Toggle details" title="Expand/collapse card details">▼</button>
      </div>
      <div class="entity-body">
        <!-- Status Codes Section -->
        <div class="entity-section">
          <div class="entity-section-title" title="HTTP response status codes grouped by class. Monitor 4xx for client issues (bad requests, auth failures) and 5xx for server errors (bugs, timeouts, dependencies).">Response Codes</div>
          <div class="status-row" role="list">
            <div class="status-chip s2xx" role="listitem" title="Successful responses (200-299). Includes OK, Created, Accepted, No Content. This should be the vast majority of responses.">
              <div class="status-chip-value count-2xx">0</div>
              <div class="status-chip-label"><span class="icon" aria-hidden="true">✓</span> 2xx</div>
            </div>
            <div class="status-chip s4xx" role="listitem" title="Client errors (400-499). Bad Request, Unauthorized, Forbidden, Not Found. High 4xx may indicate API misuse, auth issues, or invalid client requests.">
              <div class="status-chip-value count-4xx">0</div>
              <div class="status-chip-label"><span class="icon" aria-hidden="true">!</span> 4xx</div>
            </div>
            <div class="status-chip s5xx" role="listitem" title="Server errors (500-599). Internal errors, Bad Gateway, Service Unavailable. Any 5xx requires investigation - check logs, dependencies, and resource exhaustion.">
              <div class="status-chip-value count-5xx">0</div>
              <div class="status-chip-label"><span class="icon" aria-hidden="true">✕</span> 5xx</div>
            </div>
          </div>
          <div class="status-bar" role="img" aria-label="Response code breakdown" title="Visual proportion of response codes. A healthy service shows mostly green (2xx).">
            <div class="status-segment s2xx" style="width: 100%"></div>
            <div class="status-segment s4xx" style="width: 0%"></div>
            <div class="status-segment s5xx" style="width: 0%"></div>
          </div>
        </div>

        <!-- Latency Section -->
        <div class="entity-section">
          <div class="entity-section-title" title="Request latency distribution showing how long requests take to complete. Bars show count of requests in each latency bucket. Color indicates severity: green (fast), yellow (moderate), red (slow).">Latency Distribution</div>
          <div class="histogram" role="img" aria-label="Latency histogram" title="Histogram of request durations. Hover over bars to see exact counts. Bimodal distributions may indicate cache hits vs misses or different code paths."></div>
          <div class="histogram-meta">
            <span>0ms</span>
            <span>500ms+</span>
          </div>
          <div class="percentiles" role="list" aria-label="Latency percentiles">
            <div class="percentile" role="listitem" title="Median latency - 50% of requests complete faster than this. Represents typical user experience. Should match your latency SLO target.">
              <div class="percentile-dot p50" aria-hidden="true"></div>
              <span class="percentile-label">P50</span>
              <span class="percentile-value p50-value">--</span>
            </div>
            <div class="percentile" role="listitem" title="95th percentile - only 5% of requests are slower. Key SLO metric. If P95 >> P50, investigate outliers: GC pauses, cold caches, or slow queries.">
              <div class="percentile-dot p95" aria-hidden="true"></div>
              <span class="percentile-label">P95</span>
              <span class="percentile-value p95-value">--</span>
            </div>
            <div class="percentile" role="listitem" title="99th percentile - worst 1% of requests. High P99 affects user experience and may indicate resource contention, timeouts, or retry storms.">
              <div class="percentile-dot p99" aria-hidden="true"></div>
              <span class="percentile-label">P99</span>
              <span class="percentile-value p99-value">--</span>
            </div>
          </div>
        </div>

        <!-- Throughput Section -->
        <div class="entity-section">
          <div class="entity-section-title" title="Network I/O throughput over the last 60 seconds. Useful for detecting traffic patterns, large response bodies, or potential bandwidth saturation.">Throughput</div>
          <div class="sparkline-container" title="Sparkline showing bytes in (requests received) and bytes out (responses sent) over time.">
            <div class="sparkline" role="img" aria-label="Throughput chart"></div>
            <span class="sparkline-time-label start">-60s</span>
            <span class="sparkline-time-label end">now</span>
          </div>
          <div class="sparkline-meta">
            <div class="sparkline-stat" title="Incoming bytes per second (request bodies, headers). High inbound traffic may indicate file uploads or large POST payloads.">
              <div class="sparkline-dot in" aria-hidden="true"></div>
              <span class="sparkline-label">In</span>
              <span class="sparkline-value bytes-in-rate">0 B/s</span>
            </div>
            <div class="sparkline-stat" title="Outgoing bytes per second (response bodies, headers). High outbound traffic indicates large responses. Monitor for bandwidth limits.">
              <div class="sparkline-dot out" aria-hidden="true"></div>
              <span class="sparkline-label">Out</span>
              <span class="sparkline-value bytes-out-rate">0 B/s</span>
            </div>
          </div>
        </div>
      </div>
    `;

    return card;
  }

  // Format latency bucket label (compact version for axis)
  function fmtBucketLabel(le) {
    if (le === Infinity) return '+∞';
    if (le < 0.001) return (le * 1000000).toFixed(0) + 'µ';
    if (le < 0.01) return (le * 1000).toFixed(1) + 'm';
    if (le < 1) return Math.round(le * 1000) + 'm';
    return le.toFixed(0) + 's';
  }

  function renderServerHistogram(container, histogram) {
    if (!container) return;

    // Find or create the meta element for axis labels
    var metaEl = container.nextElementSibling;
    if (metaEl && metaEl.classList.contains('histogram-meta')) {
      // We'll update this with dynamic labels
    }

    if (!histogram || !histogram.buckets || histogram.buckets.length === 0) {
      // Show empty histogram bars
      var html = '';
      for (var i = 0; i < 8; i++) {
        html += '<div class="histogram-bar-wrap"><div class="histogram-bar" style="height: 2px;" tabindex="0"></div><div class="histogram-bar-label">--</div></div>';
      }
      container.innerHTML = html;
      if (metaEl) metaEl.style.display = 'none';
      return;
    }

    var buckets = histogram.buckets;

    // Convert cumulative buckets to per-bucket counts
    var perBucket = [];
    var prevCount = 0;
    var totalCount = 0;
    for (var i = 0; i < buckets.length; i++) {
      var bucket = buckets[i];
      var le = bucket.le === '+Inf' ? Infinity : parseFloat(bucket.le);
      var count = bucket.count - prevCount;
      count = Math.max(0, count);
      perBucket.push({ le: le, count: count, cumulative: bucket.count });
      prevCount = bucket.count;
      totalCount += count;
    }

    // Smart range selection: find P1 to P99.9 range
    var p001Count = totalCount * 0.001;  // 0.1% threshold
    var p999Count = totalCount * 0.999;  // 99.9% threshold

    var startIdx = 0;
    var endIdx = perBucket.length - 1;
    var cumulativeCount = 0;

    // Find first bucket with meaningful data (above P0.1)
    for (var i = 0; i < perBucket.length; i++) {
      cumulativeCount += perBucket[i].count;
      if (cumulativeCount >= p001Count && perBucket[i].count > 0) {
        startIdx = Math.max(0, i - 1);  // Include one bucket before for context
        break;
      }
    }

    // Find last bucket with meaningful data (below P99.9)
    cumulativeCount = 0;
    for (var i = 0; i < perBucket.length; i++) {
      cumulativeCount += perBucket[i].count;
      if (cumulativeCount >= p999Count) {
        endIdx = Math.min(perBucket.length - 1, i + 1);  // Include one bucket after for context
        break;
      }
    }

    // Ensure we have at least 4 buckets and at most 8 (to fit labels nicely)
    var range = endIdx - startIdx + 1;
    if (range < 4) {
      var expand = Math.floor((4 - range) / 2);
      startIdx = Math.max(0, startIdx - expand);
      endIdx = Math.min(perBucket.length - 1, endIdx + expand);
    }
    if (range > 8) {
      // Aggregate buckets if too many
      var step = Math.ceil(range / 8);
      var aggregated = [];
      for (var i = startIdx; i <= endIdx; i += step) {
        var aggCount = 0;
        var lastLe = perBucket[Math.min(i + step - 1, endIdx)].le;
        for (var j = i; j < Math.min(i + step, endIdx + 1); j++) {
          aggCount += perBucket[j].count;
        }
        aggregated.push({ le: lastLe, count: aggCount });
      }
      perBucket = aggregated;
    } else {
      perBucket = perBucket.slice(startIdx, endIdx + 1);
    }

    // Find max for scaling (with minimum to avoid flat bars)
    var maxCount = 1;
    for (var i = 0; i < perBucket.length; i++) {
      if (perBucket[i].count > maxCount) maxCount = perBucket[i].count;
    }

    // Bar area height = container height (60px) - label height (12px) = 48px
    var barAreaHeight = 48;

    // Build the histogram HTML with bars and labels
    var html = '';
    for (var i = 0; i < perBucket.length; i++) {
      var bucket = perBucket[i];
      var pct = bucket.count / maxCount;
      var barClass = 'histogram-bar';

      // Color code based on latency threshold (realistic webserver SLOs)
      var le = bucket.le;
      if (le <= 0.1) barClass += ' p50';         // Green for fast (≤100ms)
      else if (le <= 1.0) barClass += ' p95';    // Yellow for acceptable (≤1s)
      else barClass += ' p99';                   // Red for slow (>1s)

      // Format label for the bucket
      var leLabel = fmtBucketLabel(le);
      var fullLabel = fmtLatency(le);

      // Calculate bar height in pixels (min 2px for visibility)
      var barHeight = bucket.count > 0 ? Math.max(2, Math.round(pct * barAreaHeight)) : 2;

      html += '<div class="histogram-bar-wrap">';
      html += '<div class="' + barClass + '" style="height: ' + barHeight + 'px;" tabindex="0" title="≤' + fullLabel + ': ' + bucket.count + '"></div>';
      html += '<div class="histogram-bar-label">' + leLabel + '</div>';
      html += '</div>';
    }
    container.innerHTML = html;

    // Hide the old meta element since we have per-bar labels now
    if (metaEl) metaEl.style.display = 'none';
  }

  function renderServerSparkline(container, histIn, histOut) {
    if (!container) return;

    var width = container.offsetWidth || 200;
    var height = container.offsetHeight || 40;

    // Find max value for scaling
    var maxVal = 1;
    for (var i = 0; i < histIn.length; i++) {
      if (histIn[i] > maxVal) maxVal = histIn[i];
    }
    for (var i = 0; i < histOut.length; i++) {
      if (histOut[i] > maxVal) maxVal = histOut[i];
    }

    function makePoints(data, color) {
      if (data.length < 2) return '';
      var points = [];
      for (var i = 0; i < data.length; i++) {
        var x = (i / (data.length - 1)) * width;
        var y = height - (data[i] / maxVal) * (height - 4);
        points.push(x.toFixed(1) + ',' + y.toFixed(1));
      }
      return '<polyline class="sparkline-path" points="' + points.join(' ') + '" stroke="' + color + '" />';
    }

    var svg = '<svg viewBox="0 0 ' + width + ' ' + height + '" preserveAspectRatio="none">';
    svg += makePoints(histIn, 'var(--color-ok)');
    svg += makePoints(histOut, 'var(--color-info)');
    svg += '</svg>';

    container.innerHTML = svg;
  }

  function updateServerCard(card, serverInfo, deltaSeconds) {
    var counters = serverInfo.counters;
    var histograms = serverInfo.histograms;
    var gauges = serverInfo.gauges;

    var req2xx = getMetricValue(counters, 'http_requests_total', {status: '2xx'});
    var req4xx = getMetricValue(counters, 'http_requests_total', {status: '4xx'});
    var req5xx = getMetricValue(counters, 'http_requests_total', {status: '5xx'});
    var reqTotal = req2xx + req4xx + req5xx;

    var bytesSent = getMetricValue(counters, 'http_bytes_sent_total', {});
    var bytesRecv = getMetricValue(counters, 'http_bytes_recv_total', {});
    var activeConns = getMetricValue(gauges, 'http_connections_active', {});

    // Calculate request rate
    var prevTotal = card.dataset.prevReqTotal ? parseInt(card.dataset.prevReqTotal) : 0;
    var reqRate = deltaSeconds > 0 ? (reqTotal - prevTotal) / deltaSeconds : 0;
    card.dataset.prevReqTotal = reqTotal;

    // Find latency histogram
    var latencyHist = findMetric(histograms, 'http_request_duration_seconds', {});

    // Update header stats
    card.querySelector('.active-conns').textContent = activeConns;
    card.querySelector('.req-rate').textContent = fmt(reqRate, 1) + '/s';

    // Update entity status based on error rate
    var errorRate = reqTotal > 0 ? ((req4xx + req5xx) / reqTotal) * 100 : 0;
    var statusEl = card.querySelector('.entity-status');
    statusEl.className = 'entity-status';
    if (errorRate > 5) {
      statusEl.classList.add('error');
    } else if (errorRate > 1) {
      statusEl.classList.add('warning');
    } else {
      statusEl.classList.add('ok');
    }

    // Update status code chips
    card.querySelector('.count-2xx').textContent = fmtCompact(req2xx);
    card.querySelector('.count-4xx').textContent = fmtCompact(req4xx);
    card.querySelector('.count-5xx').textContent = fmtCompact(req5xx);

    // Update status bar segments
    var total = Math.max(reqTotal, 1);
    var seg2xx = card.querySelector('.status-segment.s2xx');
    var seg4xx = card.querySelector('.status-segment.s4xx');
    var seg5xx = card.querySelector('.status-segment.s5xx');
    if (seg2xx) seg2xx.style.width = ((req2xx / total) * 100) + '%';
    if (seg4xx) seg4xx.style.width = ((req4xx / total) * 100) + '%';
    if (seg5xx) seg5xx.style.width = ((req5xx / total) * 100) + '%';

    // Render latency histogram
    var histContainer = card.querySelector('.histogram');
    renderServerHistogram(histContainer, latencyHist);

    // Update percentile values (estimated from histogram if available)
    if (latencyHist && latencyHist.buckets && latencyHist.count > 0) {
      var buckets = latencyHist.buckets;
      var p50 = estimatePercentile(buckets, latencyHist.count, 0.50);
      var p95 = estimatePercentile(buckets, latencyHist.count, 0.95);
      var p99 = estimatePercentile(buckets, latencyHist.count, 0.99);

      var p50El = card.querySelector('.p50-value');
      var p95El = card.querySelector('.p95-value');
      var p99El = card.querySelector('.p99-value');
      if (p50El) p50El.textContent = fmtLatency(p50);
      if (p95El) p95El.textContent = fmtLatency(p95);
      if (p99El) p99El.textContent = fmtLatency(p99);
    }

    // Update throughput sparkline
    var hist = getServerHistory(serverInfo.key);
    var bytesInRate = deltaSeconds > 0 ? (bytesRecv - hist.prevBytesIn) / deltaSeconds : 0;
    var bytesOutRate = deltaSeconds > 0 ? (bytesSent - hist.prevBytesOut) / deltaSeconds : 0;

    // Only record positive rates
    if (bytesInRate >= 0) pushHistory(hist.bytesIn, bytesInRate);
    if (bytesOutRate >= 0) pushHistory(hist.bytesOut, bytesOutRate);

    hist.prevBytesIn = bytesRecv;
    hist.prevBytesOut = bytesSent;

    var sparkContainer = card.querySelector('.sparkline');
    renderServerSparkline(sparkContainer, hist.bytesIn, hist.bytesOut);

    // Update throughput labels
    var inRateEl = card.querySelector('.bytes-in-rate');
    var outRateEl = card.querySelector('.bytes-out-rate');
    if (inRateEl) inRateEl.textContent = fmtRate(Math.max(0, bytesInRate));
    if (outRateEl) outRateEl.textContent = fmtRate(Math.max(0, bytesOutRate));
  }

  // Estimate percentile from histogram buckets (cumulative format)
  function estimatePercentile(buckets, totalCount, percentile) {
    if (!buckets || buckets.length === 0 || totalCount === 0) return 0;

    var target = totalCount * percentile;

    for (var i = 0; i < buckets.length; i++) {
      var bucket = buckets[i];
      // bucket.count is cumulative
      if (bucket.count >= target) {
        var le = bucket.le === '+Inf' ? Infinity : parseFloat(bucket.le);
        if (le === Infinity && i > 0) {
          // Use previous bucket's bound
          return parseFloat(buckets[i - 1].le);
        }
        return le;
      }
    }

    // Return last non-Inf bucket if not found
    for (var i = buckets.length - 1; i >= 0; i--) {
      if (buckets[i].le !== '+Inf') {
        return parseFloat(buckets[i].le);
      }
    }
    return 0;
  }

  function renderHttpServers(servers, deltaSeconds) {
    // Phase 2: Render server cards into AIO panel's nested container
    // Find all AIO panels and their server containers
    var aioServerContainers = document.querySelectorAll('.aio-sys-servers-container');
    var serverKeys = Object.keys(servers);

    // For now, render all servers into the first AIO panel (single-system case)
    // Future: match servers to their owning AIO system
    var container = aioServerContainers.length > 0 ? aioServerContainers[0] : null;

    if (!container) {
      // No AIO panels yet, skip rendering
      return;
    }

    // Hide "no servers" placeholder if we have servers
    var noServersEl = container.querySelector('.aio-no-entities');
    if (serverKeys.length === 0) {
      if (noServersEl) noServersEl.style.display = 'block';
      // Remove old server cards
      for (var key in serverCards) {
        if (serverCards[key].parentNode) {
          serverCards[key].parentNode.removeChild(serverCards[key]);
        }
      }
      serverCards = {};
      return;
    }

    if (noServersEl) noServersEl.style.display = 'none';

    // Update or create server cards
    serverKeys.forEach(function(key) {
      var serverInfo = servers[key];
      var cardId = 'server-' + key.replace(/[:.]/g, '-');

      if (!serverCards[key]) {
        serverCards[key] = createServerCard(serverInfo);
        container.appendChild(serverCards[key]);
      }

      updateServerCard(serverCards[key], serverInfo, deltaSeconds);
    });

    // Remove cards for servers that no longer exist
    for (var key in serverCards) {
      if (!servers[key]) {
        if (serverCards[key].parentNode) {
          serverCards[key].parentNode.removeChild(serverCards[key]);
        }
        delete serverCards[key];
      }
    }

    // Update AIO panel badges for server count and rate
    var aioPanel = container.closest('.aio-system-panel');
    if (aioPanel) {
      var serverCountBadge = aioPanel.querySelector('.aio-sys-servers-count');
      var serverRateBadge = aioPanel.querySelector('.aio-sys-servers-rate');
      var panelServersBadge = aioPanel.querySelector('.aio-sys-servers');

      if (serverCountBadge) {
        serverCountBadge.textContent = serverKeys.length + ' server' + (serverKeys.length !== 1 ? 's' : '');
      }
      if (panelServersBadge) {
        panelServersBadge.textContent = serverKeys.length + ' servers';
      }

      // Calculate total request rate from all server cards
      var totalRate = 0;
      serverKeys.forEach(function(key) {
        var card = serverCards[key];
        if (card) {
          var rateEl = card.querySelector('.req-rate');
          if (rateEl) {
            var rateText = rateEl.textContent;
            var rateVal = parseFloat(rateText) || 0;
            totalRate += rateVal;
          }
        }
      });

      if (serverRateBadge) {
        serverRateBadge.textContent = fmt(totalRate, 1) + ' req/s';
      }
    }

    // Update global section badges
    var globalCountBadge = $('http-servers-count');
    var globalRateBadge = $('http-total-rate');
    if (globalCountBadge) {
      globalCountBadge.textContent = serverKeys.length + ' server' + (serverKeys.length !== 1 ? 's' : '');
    }
  }

  // ==================== Main Update Function ====================
  function updateDashboard(data) {
    hideLoadingState();

    var now = Date.now();
    var deltaSeconds = prevTimestamp ? (now - prevTimestamp) / 1000 : 1;
    prevTimestamp = now;

    var aio = data.aio_metrics || {};
    var mod = data.modular_metrics || {};
    var vm = data.vm_metrics || {};

    var gc = vm.gc || {};
    var interp = vm.interpreter || {};
    var loop = vm.event_loop || {};
    var sys = aio.system || {};
    var conns = aio.connections || {};

    // ========== Header ==========
    $('uptime-value').textContent = fmtUptime(aio.uptime_seconds || mod.uptime_seconds || 0);
    $('timestamp').textContent = new Date().toLocaleTimeString();

    // ========== Health Overview ==========
    // Calculate derived metrics
    var servers = groupByServer(mod);
    var serverKeys = Object.keys(servers);

    // Total request rate across all servers
    var totalReqNow = 0;
    var totalReq2xx = 0;
    var totalReq4xx = 0;
    var totalReq5xx = 0;

    serverKeys.forEach(function(key) {
      var srv = servers[key];
      totalReq2xx += getMetricValue(srv.counters, 'http_requests_total', {status: '2xx'});
      totalReq4xx += getMetricValue(srv.counters, 'http_requests_total', {status: '4xx'});
      totalReq5xx += getMetricValue(srv.counters, 'http_requests_total', {status: '5xx'});
    });
    totalReqNow = totalReq2xx + totalReq4xx + totalReq5xx;

    var prevTotalReq = prevMetrics ? prevMetrics.totalReq : 0;
    var requestRate = calculateRate(totalReqNow, prevTotalReq, deltaSeconds);
    pushHistory(history.requestRate, requestRate);

    var errorRate = totalReqNow > 0 ? ((totalReq4xx + totalReq5xx) / totalReqNow) * 100 : 0;
    pushHistory(history.errorRate, errorRate);

    // Average latency across all servers
    var totalLatencySum = 0;
    var totalLatencyCount = 0;
    serverKeys.forEach(function(key) {
      var srv = servers[key];
      var hist = findMetric(srv.histograms, 'http_request_duration_seconds', {});
      if (hist) {
        totalLatencySum += hist.sum;
        totalLatencyCount += hist.count;
      }
    });
    var avgLatency = totalLatencyCount > 0 ? (totalLatencySum / totalLatencyCount) * 1000 : 0;
    pushHistory(history.latency, avgLatency);

    // Heap usage
    var heapUsed = gc.heap_used_bytes || 0;
    var heapTotal = gc.heap_total_bytes || 1;
    var heapPct = (heapUsed / heapTotal) * 100;
    pushHistory(history.heapUsage, heapPct);

    // Update health cards
    $('health-request-rate').innerHTML = fmt(requestRate, 1) + '<span style="font-size: 14px; font-weight: 400;">/s</span>';
    $('health-error-rate').innerHTML = fmt(errorRate, 1) + '<span style="font-size: 14px; font-weight: 400;">%</span>';
    $('health-avg-latency').innerHTML = fmt(avgLatency, 1) + '<span style="font-size: 14px; font-weight: 400;">ms</span>';
    $('health-heap-pct').innerHTML = fmt(heapPct, 0) + '<span style="font-size: 14px; font-weight: 400;">%</span>';
    $('health-heap-usage').textContent = fmtBytes(heapUsed) + ' / ' + fmtBytes(heapTotal);

    // Update health card statuses
    function updateHealthCardStatus(cardEl, value, warningThreshold, criticalThreshold, inverse) {
      if (!cardEl) return;
      var card = cardEl.closest('.health-card');
      if (!card) return;

      card.classList.remove('status-ok', 'status-warning', 'status-critical');

      var isWarning = inverse ? value < warningThreshold : value > warningThreshold;
      var isCritical = inverse ? value < criticalThreshold : value > criticalThreshold;

      if (isCritical) card.classList.add('status-critical');
      else if (isWarning) card.classList.add('status-warning');
      else card.classList.add('status-ok');
    }

    updateHealthCardStatus($('health-error-rate'), errorRate, 1, 5, false);
    updateHealthCardStatus($('health-heap-pct'), heapPct, 70, 90, false);
    updateHealthCardStatus($('health-avg-latency'), avgLatency, 100, 500, false);

    // ========== VM Section Badges ==========
    $('vm-gc-badge').textContent = fmtCompact(gc.cycles_total || 0) + ' cycles';
    $('vm-heap-badge').textContent = fmtBytes(heapUsed) + ' heap';

    // ========== GC Panel ==========
    $('gc-cycles-badge').textContent = fmtCompact(gc.cycles_total || 0) + ' cycles';
    $('gc-cycles').textContent = fmtCompact(gc.cycles_total || 0);
    $('gc-max-pause').innerHTML = fmt((gc.pause_us_max || 0) / 1000, 1) + '<span class="unit">ms</span>';
    $('gc-avg-pause').innerHTML = fmt(gc.pause_ms_avg || 0, 2) + '<span class="unit">ms</span>';
    $('gc-reclaimed').innerHTML = fmtBytes(gc.reclaimed_bytes_total || 0).replace(' ', '<span class="unit">') + '</span>';

    // Track GC pauses for timeline
    if (prevMetrics && gc.cycles_total > prevMetrics.gcCycles) {
      var pauseMs = (gc.pause_us_max || 0) / 1000;
      history.gcPauses.push({ pause: pauseMs, timestamp: now });
      while (history.gcPauses.length > HISTORY_SIZE) history.gcPauses.shift();
    }
    renderGcTimeline(history.gcPauses);

    // ========== Heap Memory Panel ==========
    updateGauge('heap-gauge-fill', 'heap-gauge-value', heapPct, { warning: 70, critical: 90 });
    $('heap-used').textContent = fmtBytes(heapUsed);
    $('heap-total').textContent = fmtBytes(heapTotal);
    $('heap-reclaimed').textContent = fmtBytes(gc.reclaimed_bytes_total || 0);

    // ========== Interpreter Panel ==========
    $('interp-evals').textContent = fmtCompact(interp.evals_total || 0);
    $('interp-fn-calls').textContent = fmtCompact(interp.function_calls || 0);
    $('interp-builtins').textContent = fmtCompact(interp.builtin_calls || 0);
    $('interp-stack-depth').textContent = interp.stack_depth_max || 0;
    $('interp-closures').textContent = fmtCompact(interp.closures_created || 0);
    $('interp-env-lookups').textContent = fmtCompact(interp.env_lookups || 0);

    // ========== AIO Systems Section ==========
    // Use the new aio_systems array for multi-system support
    var aioSystems = data.aio_systems || [];
    // Fallback: if aio_systems is empty but we have aio_metrics, create a system from it
    if (aioSystems.length === 0 && aio.system) {
      aioSystems = [{
        name: 'main',
        uptime_seconds: aio.uptime_seconds || 0,
        loop: loop,
        system: sys,
        connections: conns
      }];
    }
    renderAioSystems(aioSystems);

    // ========== HTTP Servers Section ==========
    renderHttpServers(servers, deltaSeconds);

    // Calculate total rate for badge
    var totalRateForBadge = 0;
    for (var key in serverCards) {
      var card = serverCards[key];
      var rateText = card.querySelector('.req-rate').textContent;
      var rateVal = parseFloat(rateText) || 0;
      totalRateForBadge += rateVal;
    }
    $('http-total-rate').textContent = fmt(totalRateForBadge, 1) + ' req/s';

    // Store metrics for next iteration
    prevMetrics = {
      totalReq: totalReqNow,
      gcCycles: gc.cycles_total || 0,
      timestamp: now
    };

    // Update adaptive interval
    var changeRate = calculateChangeRate({
      requestRate: requestRate,
      errorRate: errorRate,
      heapPct: heapPct
    });
    adaptiveInterval.current = getAdaptiveInterval(changeRate);

    // Update global status
    updateConnectionStatus(true);
  }

  // ==================== Connection Status ====================
  function updateConnectionStatus(connected) {
    var statusBadge = $('global-status');
    var statusText = $('global-status-text');
    var statusIcon = statusBadge.querySelector('.status-icon');
    var pulse = statusBadge.querySelector('.pulse');

    if (connected) {
      statusBadge.classList.remove('error');
      statusBadge.classList.add('connected');
      statusText.textContent = 'Connected';
      statusIcon.textContent = '✓';
      pulse.style.display = 'block';
      currentBackoff = POLL_INTERVAL;
    } else {
      statusBadge.classList.remove('connected');
      statusBadge.classList.add('error');
      statusText.textContent = 'Disconnected';
      statusIcon.textContent = '!';
      pulse.style.display = 'none';
    }
  }

  function showError(message) {
    var banner = $('error-banner');
    var text = $('error-text');
    if (banner && text) {
      text.textContent = message || 'Connection lost. Metrics may be stale.';
      banner.style.display = 'flex';
    }
    updateConnectionStatus(false);
  }

  window.dismissError = function() {
    var banner = $('error-banner');
    if (banner) banner.style.display = 'none';
  };

  // ==================== Loading State Management ====================
  function showLoadingState() {
    document.querySelectorAll('.health-card-value').forEach(function(el) {
      el.classList.add('loading');
    });
  }

  function hideLoadingState() {
    document.querySelectorAll('.health-card-value').forEach(function(el) {
      el.classList.remove('loading');
    });
  }

  // ==================== Initialization ====================
  // Note: Polling has been removed - all data now comes through the unified SSE diagnostics stream
  // This eliminates dashboard requests competing with the server during stress tests

  function init() {
    // No polling needed - MemoryDiagnostics SSE handles everything
    showLoadingState();
  }

  // Start when DOM is ready
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

  // ==================== Memory Diagnostics SSE Connection ====================
  class MemoryDiagnostics {
    constructor() {
      this.eventSource = null;
      this.reconnectAttempts = 0;
      this.maxReconnectAttempts = 10;
      this.lastEventId = null;

      // DOM references
      this.grids = {};
      this.arenaGauges = {};

      // State for delta detection
      this.previousState = {};
    }

    connect() {
      var url = '/debug/diagnostics/memory';
      this.eventSource = new EventSource(url);

      var self = this;

      // Listen for unified diagnostics event (memory + metrics)
      this.eventSource.addEventListener('diagnostics', function(e) {
        self.lastEventId = e.lastEventId;
        var data = JSON.parse(e.data);

        // Handle memory section
        if (data.memory) {
          self.handleMemoryUpdate(data.memory);
        }

        // Handle metrics section - update the main dashboard
        if (data.metrics) {
          self.handleMetricsUpdate(data.metrics);
        }
      });

      // Also listen for legacy 'memory' event for backwards compatibility
      this.eventSource.addEventListener('memory', function(e) {
        self.lastEventId = e.lastEventId;
        self.handleMemoryUpdate(JSON.parse(e.data));
      });

      this.eventSource.onopen = function() {
        self.reconnectAttempts = 0;
        self.updateConnectionStatus(true);
        console.log('[MemDiag] SSE connected (unified diagnostics mode)');
      };

      this.eventSource.onerror = function(e) {
        if (self.eventSource.readyState === EventSource.CLOSED) {
          self.updateConnectionStatus(false);
          self.scheduleReconnect();
        }
      };
    }

    scheduleReconnect() {
      if (this.reconnectAttempts >= this.maxReconnectAttempts) {
        console.error('[MemDiag] Max reconnection attempts reached');
        return;
      }

      this.reconnectAttempts++;
      var delay = Math.min(1000 * Math.pow(2, this.reconnectAttempts), 30000);
      console.log('[MemDiag] Reconnecting in ' + delay + 'ms...');

      var self = this;
      setTimeout(function() {
        if (self.eventSource) {
          self.eventSource.close();
        }
        self.connect();
      }, delay);
    }

    updateConnectionStatus(connected) {
      var dot = document.querySelector('.sse-dot');
      if (dot) {
        dot.style.background = connected ? 'var(--color-ok)' : 'var(--color-error)';
      }

      var sseWarning = document.getElementById('sse-warning');
      var sseLastUpdate = document.getElementById('sse-last-update');
      if (connected) {
        if (sseWarning) sseWarning.classList.remove('visible');
        if (sseLastUpdate) sseLastUpdate.textContent = new Date().toLocaleTimeString();
        document.querySelectorAll('.memory-slab-panel, .memory-arena-section').forEach(function(el) {
          el.classList.remove('stale');
        });
      } else {
        if (sseWarning) sseWarning.classList.add('visible');
        document.querySelectorAll('.memory-slab-panel, .memory-arena-section').forEach(function(el) {
          el.classList.add('stale');
        });
      }
    }

    handleMemoryUpdate(data) {
      var self = this;

      // Store owner_map for use in rendering
      if (data.owner_map) {
        this.ownerMap = data.owner_map;
      }

      // Track capacity warnings
      var warnings = [];
      var critical = [];

      // Update slab grids
      if (data.slabs) {
        data.slabs.forEach(function(slab) {
          self.updateSlabGrid(slab, self.ownerMap);

          // Check capacity thresholds
          if (slab.total > 0) {
            var pct = (slab.used / slab.total) * 100;
            if (pct >= 95) {
              critical.push({ name: slab.name, pct: Math.round(pct), used: slab.used, total: slab.total });
            } else if (pct >= 80) {
              warnings.push({ name: slab.name, pct: Math.round(pct), used: slab.used, total: slab.total });
            }
          }

          // Check for overflow
          if (slab.overflow > 0) {
            critical.push({ name: slab.name + ' overflow', pct: null, overflow: slab.overflow });
          }
        });
      }

      // Update arena gauges
      if (data.arenas) {
        data.arenas.forEach(function(arena) {
          self.updateArenaGauge(arena);

          // Check capacity thresholds
          if (arena.capacity > 0) {
            var pct = (arena.used / arena.capacity) * 100;
            if (pct >= 95) {
              critical.push({ name: arena.name, pct: Math.round(pct) });
            } else if (pct >= 80) {
              warnings.push({ name: arena.name, pct: Math.round(pct) });
            }
          }

          // Check for overflow fallbacks
          if (arena.overflow > 0) {
            critical.push({ name: arena.name + ' fallback', pct: null, overflow: arena.overflow });
          }
        });
      }

      // Update GC stats
      if (data.gc) {
        self.updateGCStats(data.gc);
      }

      // Update capacity warning banner
      this.updateCapacityWarnings(warnings, critical);
    }

    updateCapacityWarnings(warnings, critical) {
      var banner = document.getElementById('capacity-warning-banner');
      if (!banner) return;

      // Combine warnings and criticals
      var allWarnings = critical.concat(warnings);

      if (allWarnings.length === 0) {
        banner.classList.remove('visible', 'critical');
        return;
      }

      // Build message
      var messages = allWarnings.map(function(w) {
        if (w.overflow) {
          return w.name + ': ' + w.overflow + ' overflow(s)';
        }
        return w.name + ': ' + w.pct + '%';
      });

      var text = banner.querySelector('.capacity-warning-text');
      if (text) {
        text.textContent = messages.slice(0, 3).join(', ');
        if (allWarnings.length > 3) {
          text.textContent += ' (+' + (allWarnings.length - 3) + ' more)';
        }
      }

      banner.classList.add('visible');
      if (critical.length > 0) {
        banner.classList.add('critical');
      } else {
        banner.classList.remove('critical');
      }
    }

    // Handle metrics data from the unified SSE event
    // This transforms the SSE format to match what updateDashboard expects
    handleMetricsUpdate(metrics) {
      if (!metrics) return;

      // Transform SSE metrics format to updateDashboard format
      var dashboardData = {
        aio_metrics: {},
        aio_systems: [],
        modular_metrics: metrics.modular || {},
        vm_metrics: {}
      };

      // Transform VM metrics
      if (metrics.vm) {
        var vm = metrics.vm;
        dashboardData.vm_metrics = {
          gc: {
            cycles_total: vm.gc ? vm.gc.cycles_total : 0,
            pause_us_total: vm.gc ? vm.gc.pause_us_total : 0,
            pause_us_max: vm.gc ? vm.gc.pause_us_max : 0,
            reclaimed_bytes_total: vm.gc ? vm.gc.reclaimed_bytes : 0,
            heap_used_bytes: vm.gc ? vm.gc.heap_used_bytes : 0,
            heap_total_bytes: vm.gc ? vm.gc.heap_total_bytes : 0,
            pause_ms_avg: vm.gc && vm.gc.cycles_total > 0
              ? (vm.gc.pause_us_total / vm.gc.cycles_total) / 1000
              : 0
          },
          interpreter: {
            evals_total: vm.interpreter ? vm.interpreter.evals_total : 0,
            function_calls: vm.interpreter ? vm.interpreter.function_calls : 0,
            builtin_calls: vm.interpreter ? vm.interpreter.builtin_calls : 0,
            stack_depth_max: vm.interpreter ? vm.interpreter.stack_depth_max : 0,
            closures_created: vm.interpreter ? vm.interpreter.closures_created : 0,
            env_lookups: vm.interpreter ? vm.interpreter.env_lookups : 0
          },
          event_loop: {
            iterations: vm.event_loop ? vm.event_loop.iterations : 0,
            events_processed: vm.event_loop ? vm.event_loop.events_processed : 0,
            idle_time_us: vm.event_loop ? vm.event_loop.idle_time_us : 0
          }
        };
      }

      // Transform AIO metrics
      if (metrics.aio) {
        var aio = metrics.aio;
        dashboardData.aio_metrics = {
          uptime_seconds: aio.uptime_seconds || 0,
          system: {
            servers: 0,  // Will be populated from modular metrics
            handles: 0
          },
          connections: {
            total: aio.connections ? aio.connections.total : 0,
            active: aio.connections ? aio.connections.active : 0,
            failed: aio.connections ? aio.connections.failed : 0,
            idle: aio.connections ? aio.connections.idle : 0,
            closing: aio.connections ? aio.connections.closing : 0,
            connecting: aio.connections ? aio.connections.connecting : 0
          }
        };

        // Create an AIO system entry for the systems array
        dashboardData.aio_systems = [{
          name: 'main',
          uptime_seconds: aio.uptime_seconds || 0,
          loop: dashboardData.vm_metrics.event_loop || {},
          system: dashboardData.aio_metrics.system,
          connections: dashboardData.aio_metrics.connections
        }];
      }

      // Call the main dashboard update function
      updateDashboard(dashboardData);
    }

    updateSlabGrid(slab, ownerMap) {
      // Map slab names to CSS class selectors used in AIO panels
      var slabClassMap = {
        'tcp_buffers': '.aio-sys-tcp-grid',
        'handles': '.aio-sys-handles-grid',
        'stream_arenas': '.aio-sys-arenas-grid',
        'http_servers': '.aio-sys-servers-grid',
        'http_clients': '.aio-sys-clients-grid',
        'lval': '#lval-grid'
      };

      // Find all matching grids (there may be multiple AIO panels)
      var selector = slabClassMap[slab.name];
      var grids = selector ? document.querySelectorAll(selector) : [];

      // Also try the legacy global ID for backwards compatibility
      var gridId = slab.name.replace(/_/g, '-') + '-grid';
      var legacyGrid = document.getElementById(gridId);
      if (legacyGrid) {
        grids = Array.from(grids);
        grids.push(legacyGrid);
      }

      if (grids.length === 0) return;

      // Update each grid (typically just one per slab type)
      var self = this;
      grids.forEach(function(grid) {
        self.updateSingleSlabGrid(grid, slab, ownerMap);
      });
    }

    updateSingleSlabGrid(grid, slab, ownerMap) {
      if (!grid) return;

      // Track previous state for flash animation using grid's unique ID/selector
      var gridKey = grid.id || grid.className;
      var prevKey = 'slab_' + slab.name + '_' + gridKey;
      var prevStates = this.previousState[prevKey] || [];

      var self = this;

      // Check if this slab has per-slot state tracking (connection-aware slabs)
      if (slab.states) {
        var states = decodeRLE(slab.states);  // Decode RLE: "F16A3" -> "FFFFFFFFFFFFFFFFAAA"
        var summary = slab.summary;  // Capture before async callback
        requestAnimationFrame(function() {
          if (states.length > 5000) {
            // For large slabs, use aggregated view
            self.renderAggregatedStateGrid(grid, states, prevStates, summary);
          } else {
            self.renderStateGrid(grid, states, prevStates, summary);
          }
        });
        this.previousState[prevKey] = states;
      } else {
        // Binary bitmap for simple slabs
        var bitmap = this.hexToBitArray(slab.bitmap, slab.total);
        requestAnimationFrame(function() {
          if (slab.total > 5000) {
            self.renderAggregatedGrid(grid, bitmap, slab.total, prevStates);
          } else {
            self.renderDirectGrid(grid, bitmap, prevStates);
          }
        });
        this.previousState[prevKey] = bitmap;
      }

      // Find the parent panel
      var panel = grid.closest('.memory-slab-panel') || grid.closest('.resource-pool-panel');
      if (!panel) return;

      // Update owner breakdown for handles slab (only if we have by_owner data)
      if (slab.name === 'handles' && slab.summary && slab.summary.by_owner && ownerMap) {
        this.renderOwnerBreakdown(panel, slab.summary.by_owner, slab.used, ownerMap);
      }

      // Update handle type breakdown table (only for handles slab)
      if (slab.name === 'handles' && slab.by_type) {
        var httpCount = panel.querySelector('.type-count-http');
        var tcpCount = panel.querySelector('.type-count-tcp');
        var taskCount = panel.querySelector('.type-count-task');
        var timerCount = panel.querySelector('.type-count-timer');
        if (httpCount) httpCount.textContent = slab.by_type.http || 0;
        if (tcpCount) tcpCount.textContent = slab.by_type.tcp || 0;
        if (taskCount) taskCount.textContent = slab.by_type.task || 0;
        if (timerCount) timerCount.textContent = slab.by_type.timer || 0;
      }

      var pct = slab.total > 0 ? Math.round((slab.used / slab.total) * 100) : 0;

      // Update slab badge (percentage or count)
      var badge = panel.querySelector('.slab-badge');
      if (badge) {
        if (slab.total <= 10) {
          // For small slabs like HTTP servers/clients, show count
          badge.textContent = slab.used + '/' + slab.total;
        } else {
          badge.textContent = pct + '%';
        }
        // Add warning/critical class
        badge.classList.remove('warning', 'critical');
        if (pct >= 90) badge.classList.add('critical');
        else if (pct >= 70) badge.classList.add('warning');
      }

      // Update stats row (used-count, totals)
      var statsEl = panel.querySelector('.slab-stats');
      if (statsEl) {
        var usedCount = statsEl.querySelector('.used-count') ||
                        statsEl.querySelector('[class*="-used"]');
        if (usedCount) usedCount.textContent = slab.used.toLocaleString();

        var totalCount = statsEl.querySelector('[class*="-total"]');
        if (totalCount) totalCount.textContent = slab.total.toLocaleString();

        var overflowEl = statsEl.querySelector('.overflow-warning');
        if (overflowEl) {
          if (slab.overflow > 0) {
            overflowEl.textContent = '⚠ ' + slab.overflow + ' overflows';
            overflowEl.style.display = '';
          } else {
            overflowEl.style.display = 'none';
          }
        }
      }

      // Update AIO panel specific elements (for grids inside AIO panels)
      var slabClassToAio = {
        'aio-sys-handles-grid': { pct: '.aio-sys-handles-pct', used: '.aio-sys-handles-used', total: '.aio-sys-handles-total' },
        'aio-sys-tcp-grid': { pct: '.aio-sys-tcp-pct', used: '.aio-sys-tcp-used', total: '.aio-sys-tcp-total' },
        'aio-sys-arenas-grid': { pct: '.aio-sys-arenas-pct', used: '.aio-sys-arenas-used', total: '.aio-sys-arenas-total' },
        'aio-sys-servers-grid': { pct: '.aio-sys-servers-pct' },
        'aio-sys-clients-grid': { pct: '.aio-sys-clients-pct' }
      };

      for (var cls in slabClassToAio) {
        if (grid.classList.contains(cls)) {
          var selectors = slabClassToAio[cls];
          if (selectors.pct) {
            var pctEl = panel.querySelector(selectors.pct);
            if (pctEl) {
              if (slab.total <= 10) {
                pctEl.textContent = slab.used + '/' + slab.total;
              } else {
                pctEl.textContent = pct + '%';
              }
            }
          }
          if (selectors.used) {
            var usedEl = panel.querySelector(selectors.used);
            if (usedEl) usedEl.textContent = slab.used;
          }
          if (selectors.total) {
            var totalEl = panel.querySelector(selectors.total);
            if (totalEl) totalEl.textContent = slab.total;
          }
          break;
        }
      }

      // Update ARIA label
      var ariaLabel = slab.name.replace(/_/g, ' ') + ': ' + slab.used + ' of ' + slab.total + ' slots used (' + pct + '%)';
      if (slab.overflow > 0) {
        ariaLabel += ', ' + slab.overflow + ' overflows detected';
      }
      grid.setAttribute('aria-label', ariaLabel);
    }

    renderDirectGrid(grid, bitmap, prevBitmap) {
      // Ensure grid has correct number of cells
      while (grid.children.length < bitmap.length) {
        var cell = document.createElement('div');
        cell.className = 'slab-cell free';
        grid.appendChild(cell);
      }
      while (grid.children.length > bitmap.length) {
        grid.removeChild(grid.lastChild);
      }

      // Update cells with flash on change
      for (var i = 0; i < bitmap.length; i++) {
        var cell = grid.children[i];
        var newState = bitmap[i] ? 'used' : 'free';
        var oldState = prevBitmap[i] ? 'used' : 'free';

        if (newState !== oldState) {
          // State changed - flash animation
          cell.className = 'slab-cell flash';
          setTimeout(function(c, s) {
            return function() {
              c.className = 'slab-cell ' + s;
            };
          }(cell, newState), 300);
        } else if (!cell.classList.contains(newState)) {
          cell.className = 'slab-cell ' + newState;
        }
      }
    }

    renderAggregatedGrid(grid, bitmap, totalSlots, prevBitmap) {
      // For large slabs, aggregate to displayable size
      // CSS auto-fill handles columns, we just control total cell count
      var targetCells = 3000;
      var cellsPerSlot = Math.ceil(totalSlots / targetCells);

      var aggregated = new Array(targetCells).fill(0);
      var prevAggregated = new Array(targetCells).fill(0);

      for (var i = 0; i < bitmap.length; i++) {
        var aggIdx = Math.floor(i / cellsPerSlot);
        if (aggIdx < aggregated.length) {
          aggregated[aggIdx] += bitmap[i] ? 1 : 0;
          prevAggregated[aggIdx] += (prevBitmap[i] || 0) ? 1 : 0;
        }
      }

      // Normalize to 0-1
      var threshold = cellsPerSlot / 2;
      for (var i = 0; i < aggregated.length; i++) {
        aggregated[i] = aggregated[i] > threshold ? 1 : 0;
        prevAggregated[i] = prevAggregated[i] > threshold ? 1 : 0;
      }

      this.renderDirectGrid(grid, aggregated, prevAggregated);
    }

    // Render grid with per-slot handle states
    // HTTP connections: A=active, I=idle, C=closing, N=connecting
    // Other handles: T=tcp listener, K=task, M=timer
    // F=free
    renderStateGrid(grid, states, prevStates, summary) {
      // Map state chars to CSS classes
      var stateClasses = {
        'A': 'active',
        'N': 'connecting',
        'I': 'idle',
        'C': 'closing',
        'T': 'tcp-listener',
        'K': 'task',
        'M': 'timer',
        'F': 'free'
      };

      // Ensure grid has correct number of cells
      while (grid.children.length < states.length) {
        var cell = document.createElement('div');
        cell.className = 'slab-cell free';
        grid.appendChild(cell);
      }
      while (grid.children.length > states.length) {
        grid.removeChild(grid.lastChild);
      }

      // Update cells with flash on change
      for (var i = 0; i < states.length; i++) {
        var cell = grid.children[i];
        var newState = stateClasses[states[i]] || 'free';
        var oldState = prevStates[i] ? (stateClasses[prevStates[i]] || 'free') : 'free';

        if (newState !== oldState) {
          // State changed - flash animation
          cell.className = 'slab-cell flash';
          setTimeout(function(c, s) {
            return function() {
              c.className = 'slab-cell ' + s;
            };
          }(cell, newState), 300);
        } else if (!cell.classList.contains(newState)) {
          cell.className = 'slab-cell ' + newState;
        }
      }

      // Update state summary legend if present
      var panel = grid.closest('.memory-slab-panel') || grid.closest('.resource-pool-panel');
      if (panel && summary) {
        var legendActive = panel.querySelector('.state-count-active');
        var legendIdle = panel.querySelector('.state-count-idle');
        var legendClosing = panel.querySelector('.state-count-closing');
        if (legendActive) legendActive.textContent = summary.A || 0;
        if (legendIdle) legendIdle.textContent = summary.I || 0;
        if (legendClosing) legendClosing.textContent = summary.C || 0;
      }
    }

    // Render aggregated state grid for large slabs (>5000 slots)
    // Aggregates states into displayable grid cells
    renderAggregatedStateGrid(grid, states, prevStates, summary) {
      // CSS auto-fill handles columns, we just control total cell count
      var targetCells = 3000;
      var slotsPerCell = Math.ceil(states.length / targetCells);

      // Aggregate states: for each cell, find dominant non-free state
      var aggregated = [];
      var prevAggregated = [];

      for (var i = 0; i < targetCells; i++) {
        var startIdx = i * slotsPerCell;
        var endIdx = Math.min(startIdx + slotsPerCell, states.length);

        // Count states in this chunk (including new handle types)
        var counts = { 'A': 0, 'I': 0, 'C': 0, 'N': 0, 'T': 0, 'K': 0, 'M': 0, 'F': 0 };
        var prevCounts = { 'A': 0, 'I': 0, 'C': 0, 'N': 0, 'T': 0, 'K': 0, 'M': 0, 'F': 0 };

        for (var j = startIdx; j < endIdx; j++) {
          var s = states[j] || 'F';
          counts[s] = (counts[s] || 0) + 1;
          var ps = (prevStates && prevStates[j]) || 'F';
          prevCounts[ps] = (prevCounts[ps] || 0) + 1;
        }

        // Determine dominant state (priority: A > C > I > N > T > K > M > F)
        var dominant = 'F';
        if (counts['A'] > 0) dominant = 'A';
        else if (counts['C'] > 0) dominant = 'C';
        else if (counts['I'] > 0) dominant = 'I';
        else if (counts['N'] > 0) dominant = 'N';
        else if (counts['T'] > 0) dominant = 'T';
        else if (counts['K'] > 0) dominant = 'K';
        else if (counts['M'] > 0) dominant = 'M';

        var prevDominant = 'F';
        if (prevCounts['A'] > 0) prevDominant = 'A';
        else if (prevCounts['C'] > 0) prevDominant = 'C';
        else if (prevCounts['I'] > 0) prevDominant = 'I';
        else if (prevCounts['N'] > 0) prevDominant = 'N';
        else if (prevCounts['T'] > 0) prevDominant = 'T';
        else if (prevCounts['K'] > 0) prevDominant = 'K';
        else if (prevCounts['M'] > 0) prevDominant = 'M';

        aggregated.push(dominant);
        prevAggregated.push(prevDominant);
      }

      // Now render as a state grid with aggregated states
      this.renderStateGrid(grid, aggregated.join(''), prevAggregated.join(''), summary);
    }

    // Render owner breakdown as a table with rows=servers/clients, cols=active/idle/closing
    // byOwner format: {"0": {"A": x, "I": y, "C": z}, "1": {...}, ...}
    renderOwnerBreakdown(panel, byOwner, totalUsed, ownerMap) {
      var breakdownEl = panel.querySelector('.owner-breakdown');
      if (!breakdownEl) return;

      // Convert byOwner object to array with per-state counts
      var owners = [];
      for (var key in byOwner) {
        var idx = parseInt(key);
        var name = ownerMap[idx] || 'unknown';
        var states = byOwner[key];
        var active = states.A || 0;
        var idle = states.I || 0;
        var closing = states.C || 0;
        var total = active + idle + closing;
        owners.push({ idx: idx, name: name, active: active, idle: idle, closing: closing, total: total });
      }
      owners.sort(function(a, b) { return b.total - a.total; });

      // Don't show if no owners
      if (owners.length === 0) {
        breakdownEl.style.display = 'none';
        return;
      }
      breakdownEl.style.display = '';

      // Render table with rows=servers/clients, cols=active/idle/closing
      // This table shows HTTP connections only (not TCP listeners, tasks, timers)
      var tableHtml = '<table class="owner-table">';
      tableHtml += '<thead><tr>';
      tableHtml += '<th class="owner-name-col">Owner</th>';
      tableHtml += '<th class="state-col active-col">Active</th>';
      tableHtml += '<th class="state-col idle-col">Idle</th>';
      tableHtml += '<th class="state-col closing-col">Closing</th>';
      tableHtml += '<th class="state-col total-col">Conns</th>';
      tableHtml += '</tr></thead>';
      tableHtml += '<tbody>';

      owners.forEach(function(owner) {
        var pct = totalUsed > 0 ? Math.round((owner.total / totalUsed) * 100) : 0;
        tableHtml += '<tr>';
        tableHtml += '<td class="owner-name-cell">' + owner.name + '</td>';
        tableHtml += '<td class="state-cell active-cell">' + owner.active + '</td>';
        tableHtml += '<td class="state-cell idle-cell">' + owner.idle + '</td>';
        tableHtml += '<td class="state-cell closing-cell">' + owner.closing + '</td>';
        tableHtml += '<td class="state-cell total-cell">' + owner.total + ' <span class="owner-pct">(' + pct + '%)</span></td>';
        tableHtml += '</tr>';
      });

      tableHtml += '</tbody></table>';
      breakdownEl.innerHTML = tableHtml;
    }

    updateArenaGauge(arena) {
      var gauge = document.querySelector('[data-arena="' + arena.name + '"]');
      if (!gauge) return;

      var percentage = (arena.used / arena.capacity) * 100;
      var hwmPercentage = (arena.hwm / arena.capacity) * 100;

      // Update bar
      var bar = gauge.querySelector('.arena-bar');
      if (bar) {
        bar.style.width = percentage + '%';

        // Color based on usage
        bar.className = 'arena-bar';
        if (percentage >= 90) {
          bar.classList.add('critical');
        } else if (percentage >= 70) {
          bar.classList.add('warning');
        } else {
          bar.classList.add('healthy');
        }
      }

      // Update high water mark
      var hwm = gauge.querySelector('.arena-hwm');
      if (hwm) {
        hwm.style.left = hwmPercentage + '%';
      }

      // Update label
      var label = gauge.querySelector('.arena-label');
      if (label) {
        var usedStr = this.formatBytes(arena.used);
        var capacityStr = this.formatBytes(arena.capacity);
        label.innerHTML = '<span class="pct">' + percentage.toFixed(0) + '%</span> &mdash; ' + usedStr + ' / ' + capacityStr;
      }

      // After updating the label, add ARIA updates
      gauge.setAttribute('aria-valuenow', Math.round(percentage));
      gauge.setAttribute('aria-label', arena.name + ': ' + percentage.toFixed(0) + '% used, ' + usedStr + ' of ' + capacityStr);

      // Update overflow indicator
      if (arena.overflow > 0) {
        gauge.classList.add('has-overflow');
      } else {
        gauge.classList.remove('has-overflow');
      }
    }

    updateGCStats(gc) {
      // Update GC panel if it exists
      var gcPanel = document.querySelector('.gc-stats-panel');
      if (!gcPanel) return;

      var allocated = gcPanel.querySelector('[data-gc="allocated"]');
      var peak = gcPanel.querySelector('[data-gc="peak"]');
      var cycles = gcPanel.querySelector('[data-gc="cycles"]');

      if (allocated) allocated.textContent = this.formatBytes(gc.allocated);
      if (peak) peak.textContent = this.formatBytes(gc.peak);
      if (cycles) cycles.textContent = gc.cycles.toLocaleString();
    }

    // Utility functions
    // Decode RLE hex string: "ff*32,00*8" -> array of bytes [0xff, 0xff, ..., 0x00, ...]
    decodeRleHex(rleHex) {
      if (!rleHex || rleHex.length === 0) return [];

      var bytes = [];
      // Check if it's RLE format (contains comma or asterisk)
      if (rleHex.indexOf(',') === -1 && rleHex.indexOf('*') === -1) {
        // Plain hex format (legacy) - decode directly
        for (var i = 0; i < rleHex.length; i += 2) {
          bytes.push(parseInt(rleHex.substr(i, 2), 16));
        }
        return bytes;
      }

      // RLE format: "XX*N,YY*M,..."
      var runs = rleHex.split(',');
      for (var i = 0; i < runs.length; i++) {
        var run = runs[i];
        if (!run) continue;

        var asteriskIdx = run.indexOf('*');
        var hexPart, count;
        if (asteriskIdx === -1) {
          // No asterisk means count of 1
          hexPart = run;
          count = 1;
        } else {
          hexPart = run.substring(0, asteriskIdx);
          count = parseInt(run.substring(asteriskIdx + 1), 10) || 1;
        }

        var byte = parseInt(hexPart, 16);
        for (var j = 0; j < count; j++) {
          bytes.push(byte);
        }
      }
      return bytes;
    }

    // Convert hex string (plain or RLE) to bit array (LSB-first order to match C bitmap)
    hexToBitArray(hex, totalSlots) {
      var bytes = this.decodeRleHex(hex);
      var bits = [];
      for (var i = 0; i < bytes.length; i++) {
        var byte = bytes[i];
        // LSB-first: bit 0 is first slot in each byte
        for (var b = 0; b < 8; b++) {
          bits.push((byte >> b) & 1);
        }
      }
      // Truncate to actual slot count (bitmap may have padding bits)
      if (totalSlots !== undefined && bits.length > totalSlots) {
        bits = bits.slice(0, totalSlots);
      }
      return bits;
    }

    formatBytes(bytes) {
      if (bytes < 1024) return bytes + 'B';
      if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + 'KB';
      if (bytes < 1024 * 1024 * 1024) return (bytes / (1024 * 1024)).toFixed(1) + 'MB';
      return (bytes / (1024 * 1024 * 1024)).toFixed(1) + 'GB';
    }

    disconnect() {
      if (this.eventSource) {
        this.eventSource.close();
        this.eventSource = null;
      }
    }
  }

  // Initialize on page load
  var memoryDiagnostics = null;
  document.addEventListener('DOMContentLoaded', function() {
    memoryDiagnostics = new MemoryDiagnostics();
    memoryDiagnostics.connect();
  });

  // ==================== Keyboard Shortcuts ====================
  document.addEventListener('keydown', function(e) {
    if (!e.altKey) return;

    var shortcuts = {
      'h': '#health-title',
      'v': '#vm-section-title',
      'r': '#resources-section-title',
      'a': '#aio-section-title',
      's': '#http-section-title'
    };

    var target = shortcuts[e.key.toLowerCase()];
    if (target) {
      e.preventDefault();
      var el = document.querySelector(target);
      if (el) {
        el.scrollIntoView({ behavior: 'smooth', block: 'start' });
        el.focus();
      }
    }
  });

  // ==================== Custom Tooltips ====================
  function initializeTooltips() {
    document.querySelectorAll('[data-tooltip]').forEach(function(el) {
      var tooltipText = el.getAttribute('data-tooltip');
      var tooltipTitle = el.getAttribute('data-tooltip-title') || '';

      el.classList.add('has-tooltip');
      el.removeAttribute('title');

      var tooltip = document.createElement('div');
      tooltip.className = 'tooltip';
      tooltip.setAttribute('role', 'tooltip');
      tooltip.innerHTML = (tooltipTitle ? '<div class="tooltip-title">' + tooltipTitle + '</div>' : '') +
                          '<div class="tooltip-body">' + tooltipText + '</div>';

      var tooltipId = 'tooltip-' + Math.random().toString(36).substr(2, 9);
      tooltip.id = tooltipId;
      el.setAttribute('aria-describedby', tooltipId);
      el.appendChild(tooltip);
    });
  }

  document.addEventListener('DOMContentLoaded', initializeTooltips);
})();
