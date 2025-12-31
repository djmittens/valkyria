// Valkyria Dashboard - Real-time Metrics Visualization
(function() {
  'use strict';

  // ==================== Configuration ====================
  // Sparkline window size in samples (server sends updates every 100ms)
  // 1800 samples = 3 minutes, 600 = 1 minute, 3000 = 5 minutes
  var HISTORY_SAMPLES = 1800;
  // Display window for sparklines (60 samples = 6 seconds at 100ms intervals)
  // This is how many samples are rendered - keeps sparklines from "zooming out"
  var SPARKLINE_DISPLAY_SAMPLES = 60;
  var GAUGE_CIRCUMFERENCE = 251.2;  // 2 * PI * 40

  // Adaptive interval system (for rate-based UI updates)
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

  // ==================== Phase 1: Core Infrastructure ====================

  // Pad array to fixed size with zeros at the beginning (for stable sparkline width)
  function padSparklineData(data, targetSize, defaultValue) {
    var size = targetSize || SPARKLINE_DISPLAY_SAMPLES;
    var padValue = defaultValue !== undefined ? defaultValue : 0;
    var arr = data.slice(-size);
    while (arr.length < size) {
      arr.unshift(padValue);
    }
    return arr;
  }

  // Pad status code array (objects with s2xx, s4xx, s5xx) to fixed size
  function padStatusCodeData(data, targetSize) {
    var size = targetSize || SPARKLINE_DISPLAY_SAMPLES;
    var emptyEntry = { s2xx: 0, s4xx: 0, s5xx: 0 };
    var arr = data.slice(-size);
    while (arr.length < size) {
      arr.unshift(emptyEntry);
    }
    return arr;
  }

  // Generic circular buffer for sparkline history
  function createHistoryBuffer(maxSize) {
    return {
      data: [],
      maxSize: maxSize || HISTORY_SAMPLES,
      push: function(value) {
        this.data.push(value);
        if (this.data.length > this.maxSize) {
          this.data.shift();
        }
      },
      toArray: function() {
        return this.data.slice();
      },
      last: function() {
        return this.data[this.data.length - 1];
      }
    };
  }

  // Per-entity history storage
  var entityHistory = {
    // 'http-server:api:8443': { requestRate: buffer, errorRate: buffer, p50: buffer, ... }
  };

  function getEntityHistory(type, key) {
    var id = type + ':' + key;
    if (!entityHistory[id]) {
      entityHistory[id] = {
        requestRate: createHistoryBuffer(HISTORY_SAMPLES),
        errorRate: createHistoryBuffer(HISTORY_SAMPLES),
        p50: createHistoryBuffer(HISTORY_SAMPLES),
        p95: createHistoryBuffer(HISTORY_SAMPLES),
        p99: createHistoryBuffer(HISTORY_SAMPLES),
        bytesIn: createHistoryBuffer(HISTORY_SAMPLES),
        bytesOut: createHistoryBuffer(HISTORY_SAMPLES),
        statusCodes: createHistoryBuffer(HISTORY_SAMPLES)
      };
    }
    return entityHistory[id];
  }

  // ==================== Canvas Sparkline Infrastructure ====================
  var sparklineColors = null;
  var sparklineRegistry = new Map();  // container -> { data, opts, type, lastUpdate }
  var sparklineRafId = null;
  var sparklineStaleThreshold = 500;  // Stop scrolling if no update for this long

  // Sample interval tracking for smooth animation
  var sampleIntervalHistory = [];  // Recent sample intervals in ms
  var sampleIntervalMax = 10;      // Number of samples to average
  var lastSampleTime = 0;          // Time of last data update
  var avgSampleInterval = 100;     // Running average (starts at expected 100ms)

  function getSparklineColors() {
    if (sparklineColors) return sparklineColors;
    var style = getComputedStyle(document.documentElement);
    sparklineColors = {
      ok: style.getPropertyValue('--color-ok').trim() || '#3fb950',
      warning: style.getPropertyValue('--color-warning').trim() || '#d29922',
      error: style.getPropertyValue('--color-error').trim() || '#f85149',
      info: style.getPropertyValue('--color-info').trim() || '#58a6ff',
      purple: style.getPropertyValue('--color-purple').trim() || '#a371f7',
      cyan: style.getPropertyValue('--color-cyan').trim() || '#39d4d4'
    };
    return sparklineColors;
  }

  function updateSampleInterval(now) {
    if (lastSampleTime > 0) {
      var interval = now - lastSampleTime;
      if (interval > 0 && interval < 2000) {
        sampleIntervalHistory.push(interval);
        if (sampleIntervalHistory.length > sampleIntervalMax) {
          sampleIntervalHistory.shift();
        }
        var sum = 0;
        for (var i = 0; i < sampleIntervalHistory.length; i++) {
          sum += sampleIntervalHistory[i];
        }
        avgSampleInterval = sum / sampleIntervalHistory.length;
      }
    }
    lastSampleTime = now;
  }

  function sparklineAnimationLoop(now) {
    sparklineRafId = null;
    var hasActive = false;

    sparklineRegistry.forEach(function(state, container) {
      if (!container.isConnected) {
        sparklineRegistry.delete(container);
        return;
      }

      var elapsed = now - state.lastUpdate;
      var isStale = elapsed > sparklineStaleThreshold;

      // Calculate scroll offset as fraction of one sample step
      // scrollT goes from 0 (just received data) to 1 (one sample interval elapsed)
      // Beyond 1.0 we clamp (data stays at final position until next update)
      var scrollT = isStale ? 0 : Math.min(1, elapsed / avgSampleInterval);

      if (state.type === 'line') {
        drawLineSparklineWithOffset(container, state.series, state.opts, scrollT);
      } else if (state.type === 'bar') {
        drawBarSparklineWithOffset(container, state.data, state.opts, scrollT);
      }

      // Keep animating if scroll not complete and not stale
      if (scrollT < 1 && !isStale) hasActive = true;
    });

    // Always keep the animation loop running if we have any registered sparklines
    // This ensures smooth 60fps even between data updates
    if (sparklineRegistry.size > 0 && !sparklineRafId) {
      sparklineRafId = requestAnimationFrame(sparklineAnimationLoop);
    }
  }

  function registerSparkline(container, type, dataOrSeries, opts) {
    var now = performance.now();

    // Update sample interval tracking
    updateSampleInterval(now);

    sparklineRegistry.set(container, {
      type: type,
      series: type === 'line' ? dataOrSeries : null,
      data: type === 'bar' ? dataOrSeries : null,
      opts: opts,
      lastUpdate: now
    });

    if (!sparklineRafId) {
      sparklineRafId = requestAnimationFrame(sparklineAnimationLoop);
    }
  }

  function ensureCanvas(container, height) {
    var canvas = container._sparkCanvas;
    var dpr = window.devicePixelRatio || 1;
    var width = container.clientWidth || 160;
    var sw = Math.round(width * dpr), sh = Math.round(height * dpr);

    if (!canvas) {
      canvas = document.createElement('canvas');
      canvas.style.cssText = 'width:100%;height:' + height + 'px;display:block';
      canvas.width = sw;
      canvas.height = sh;
      container.innerHTML = '';
      container.appendChild(canvas);
      container._sparkCanvas = canvas;
    } else if (canvas.width !== sw || canvas.height !== sh) {
      canvas.width = sw;
      canvas.height = sh;
    }
    var ctx = canvas.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, width, height);
    return { ctx: ctx, width: width, height: height };
  }

  // Unified line sparkline renderer with scroll offset
  // scrollT: 0-1 representing progress through current sample interval (for smooth scrolling)
  // Right edge is pinned, left side scrolls off
  function drawLineSparklineWithOffset(container, series, options, scrollT) {
    var opts = options || {};
    var h = opts.height || 32;
    var pad = opts.padding || 2;
    var c = ensureCanvas(container, h);
    var ctx = c.ctx, w = c.width;
    var colors = getSparklineColors();

    // Find global max across all series
    var max = 0;
    for (var s = 0; s < series.length; s++) {
      var d = series[s].data;
      for (var i = 0; i < d.length; i++) if (d[i] > max) max = d[i];
    }
    if (max === 0) max = 1;

    var plotH = h - pad * 2;
    var baseline = h - pad;
    var len = series[0].data.length;

    // Smooth scrolling: data extends beyond both edges
    // First point (i=0) is off-screen left, last point (i=len-1) is off-screen right
    // Visible area shows len-2 points worth of data
    // As scrollT goes 0->1, everything shifts left by one step
    var step = w / (len - 2);
    var shiftX = scrollT * step;

    function toY(v) { return baseline - (v / max) * plotH; }
    function toX(i) { return i * step - shiftX; }

    // Clip to canvas bounds for smooth edge scrolling
    ctx.save();
    ctx.beginPath();
    ctx.rect(0, 0, w, h);
    ctx.clip();

    // Draw each series (back to front)
    for (var si = 0; si < series.length; si++) {
      var sr = series[si];
      var data = sr.data;
      var strokeColor = colors[sr.color] || sr.color || colors.info;
      var fillColor = sr.fillColor ? (colors[sr.fillColor] || sr.fillColor) : strokeColor;

      // Area fill
      if (sr.fill) {
        ctx.beginPath();
        ctx.moveTo(toX(0), toY(data[0]));
        for (var i = 1; i < data.length; i++) {
          ctx.lineTo(toX(i), toY(data[i]));
        }
        ctx.lineTo(toX(data.length - 1), baseline);
        ctx.lineTo(toX(0), baseline);
        ctx.closePath();

        if (sr.fillGradient) {
          var grad = ctx.createLinearGradient(0, pad, 0, baseline);
          grad.addColorStop(0, fillColor);
          grad.addColorStop(1, 'transparent');
          ctx.fillStyle = grad;
          ctx.globalAlpha = sr.fill;
        } else {
          ctx.fillStyle = fillColor;
          ctx.globalAlpha = sr.fill;
        }
        ctx.fill();
        ctx.globalAlpha = 1;
      }

      // Line stroke
      if (sr.stroke !== false) {
        ctx.beginPath();
        ctx.moveTo(toX(0), toY(data[0]));
        for (var i = 1; i < data.length; i++) {
          ctx.lineTo(toX(i), toY(data[i]));
        }
        ctx.strokeStyle = strokeColor;
        ctx.lineWidth = sr.width || 1.5;
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';
        ctx.globalAlpha = typeof sr.stroke === 'number' ? sr.stroke : 0.9;
        if (sr.dash) ctx.setLineDash(sr.dash);
        else ctx.setLineDash([]);
        ctx.stroke();
        ctx.globalAlpha = 1;
      }
    }
    ctx.setLineDash([]);
    ctx.restore();
  }

  function renderLineSparkline(container, series, options) {
    if (!container || !series || !series.length) return;
    var first = series[0];
    if (!first.data || first.data.length < 2) {
      if (container._sparkCanvas) container._sparkCanvas.getContext('2d').clearRect(0, 0, 9999, 9999);
      return;
    }
    registerSparkline(container, 'line', series, options);
  }

  // Stacked bar sparkline for status codes
  // data: [{ s2xx, s4xx, s5xx }, ...]
  // options: {
  //   height,
  //   minBarHeight: number,     // minimum height for non-zero segments (default: 4)
  //   gap: number,              // gap ratio between bars 0-1 (default: 0.1)
  //   radius: number,           // corner radius (default: 0)
  //   segments: [{              // segment definitions (default: status code segments)
  //     key: string,            // property name in data
  //     color: string,          // color key or CSS color
  //   }]
  // }
  var defaultBarSegments = [
    { key: 's2xx', color: 'ok' },
    { key: 's4xx', color: 'warning' },
    { key: 's5xx', color: 'error' }
  ];

  function drawBarSparklineWithOffset(container, data, options, scrollT) {
    var opts = options || {};
    var h = opts.height || 32;
    var minH = opts.minBarHeight || 4;
    var gapRatio = opts.gap !== undefined ? opts.gap : 0.1;
    var radius = opts.radius || 0;
    var segments = opts.segments || defaultBarSegments;
    var c = ensureCanvas(container, h);
    var ctx = c.ctx, w = c.width;
    var colors = getSparklineColors();

    var len = data.length;
    // Smooth scrolling: data extends beyond both edges
    // First bar (i=0) is off-screen left, last bar (i=len-1) is off-screen right
    // Visible area shows len-2 bars worth of data
    // As scrollT goes 0->1, everything shifts left by one bar width
    var barW = w / (len - 2);
    var gap = Math.max(0.5, barW * gapRatio);
    var bw = barW - gap;
    var shiftX = scrollT * barW;

    // Clip to canvas bounds for smooth edge scrolling
    ctx.save();
    ctx.beginPath();
    ctx.rect(0, 0, w, h);
    ctx.clip();

    for (var i = 0; i < len; i++) {
      var d = data[i];
      if (!d) continue;

      // Calculate total from all segments
      var total = 0;
      for (var si = 0; si < segments.length; si++) {
        total += d[segments[si].key] || 0;
      }
      if (total === 0) continue;

      // Position: bar i at x = i * barW - shiftX (first bar starts off-screen left)
      var x = i * barW - shiftX + gap / 2;

      // Calculate heights with minimum visibility for non-zero values
      var heights = [];
      var usedH = 0;
      for (var si = segments.length - 1; si >= 0; si--) {
        var val = d[segments[si].key] || 0;
        var segH = val > 0 ? Math.max(minH, (val / total) * h) : 0;
        heights[si] = segH;
        usedH += segH;
      }
      // Adjust first segment to fill remaining space
      if (heights[0] > 0) heights[0] = Math.max(0, h - (usedH - heights[0]));

      // Draw segments from bottom to top
      var y = h;
      for (var si = 0; si < segments.length; si++) {
        var segH = heights[si];
        if (segH > 0) {
          var segColor = colors[segments[si].color] || segments[si].color;
          ctx.fillStyle = segColor;
          if (radius > 0) {
            ctx.beginPath();
            ctx.roundRect(x, y - segH, bw, segH, radius);
            ctx.fill();
          } else {
            ctx.fillRect(x, y - segH, bw, segH);
          }
          y -= segH;
        }
      }
    }
    ctx.restore();
  }

  function renderBarSparkline(container, data, options) {
    if (!container || !data || data.length < 2) return;
    registerSparkline(container, 'bar', data, options);
  }

  // SVG-based mini sparkline renderer (48x16 px default)
  function renderMiniSparkline(container, data, options) {
    if (!container || !data || data.length < 2) {
      if (container) container.innerHTML = '';
      return;
    }

    var opts = options || {};
    var width = opts.width || 48;
    var height = opts.height || 16;
    var color = opts.color || 'var(--color-info)';
    var fillOpacity = opts.fillOpacity !== undefined ? opts.fillOpacity : 0.2;
    var strokeWidth = opts.strokeWidth || 1.5;

    var max = Math.max.apply(null, data);
    // Default min to 0 for rate-style sparklines (shows absolute scale)
    var min = opts.minValue !== undefined ? opts.minValue : 0;
    var range = max - min || 1;

    var points = data.map(function(v, i) {
      var x = (i / (data.length - 1)) * width;
      var y = height - 2 - ((v - min) / range) * (height - 4);
      return x.toFixed(1) + ',' + y.toFixed(1);
    }).join(' ');

    var areaPoints = points + ' ' + width + ',' + height + ' 0,' + height;

    container.innerHTML =
      '<svg width="100%" height="100%" viewBox="0 0 ' + width + ' ' + height + '" preserveAspectRatio="none" style="display:block;">' +
      '<polygon points="' + areaPoints + '" fill="' + color + '" opacity="' + fillOpacity + '"/>' +
      '<polyline points="' + points + '" fill="none" stroke="' + color + '" stroke-width="' + strokeWidth + '" stroke-linecap="round" stroke-linejoin="round"/>' +
      '</svg>';
  }

  // NOTE: renderPercentileSparkline and renderStatusCodeSparkline are defined
  // later in this file (around line ~1500) with the full implementation.
  // The definitions there support history buffer objects with .data property.

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

  // ==================== Delta State Decoder ====================
  // Decodes sparse delta format: "3:A2I1,10:F3" -> applies changes at offsets
  // Takes existing state string and applies delta patches
  function applyDeltaStates(existingStates, deltaStr) {
    if (!deltaStr || deltaStr.length === 0) return existingStates;
    if (!existingStates) existingStates = '';

    // Convert to array for easier manipulation
    var states = existingStates.split('');

    // Parse delta: "offset:RLE,offset:RLE,..."
    var regions = deltaStr.split(',');
    for (var r = 0; r < regions.length; r++) {
      var region = regions[r];
      var colonIdx = region.indexOf(':');
      if (colonIdx === -1) continue;

      var offset = parseInt(region.substring(0, colonIdx), 10);
      var rle = region.substring(colonIdx + 1);

      if (isNaN(offset) || offset < 0) continue;

      // Decode RLE and apply at offset
      var expanded = decodeRLE(rle);
      for (var i = 0; i < expanded.length; i++) {
        var idx = offset + i;
        // Extend array if needed
        while (states.length <= idx) {
          states.push('F');
        }
        states[idx] = expanded[i];
      }
    }

    return states.join('');
  }

  // ==================== PoolWidget ====================
  // Unified pool/slab visualization component combining gauge bar, canvas grid, and legend.
  //
  // Usage:
  //   var widget = new PoolWidget({
  //     id: 'slab-tier',
  //     name: 'Slab Tier',
  //     slabKey: 'lval',               // For registry lookup
  //     icon: 'S',                     // Optional icon letter
  //     preset: 'slab',                // 'slab' | 'malloc' | 'arena' | 'buffer' | 'queue'
  //     variant: 'full',               // 'full' | 'compact' | 'mini' | 'gauge-only'
  //     showGauge: true,               // Show gauge bar (default: true)
  //     showGrid: true,                // Show canvas grid (default: true)
  //     showLegend: true,              // Show legend (default: false for compact/mini)
  //     markers: [                     // Gauge markers
  //       { type: 'hwm', id: 'hwm' },
  //       { type: 'threshold', id: 'threshold', label: 'GC', position: 75 }
  //     ],
  //     legend: [                      // Legend items
  //       { type: 'bar', label: 'current' },
  //       { type: 'marker', label: 'hwm', color: 'var(--color-info)' }
  //     ],
  //     states: [                      // State legend for grid (optional)
  //       { char: 'A', class: 'active', label: 'Active', color: '#3fb950' },
  //       { char: 'I', class: 'idle', label: 'Idle', color: '#1f6feb' }
  //     ],
  //     stats: [                       // Stats to show
  //       { id: 'objects', label: 'objects:' },
  //       { id: 'hwm', label: 'hwm:', suffix: '%' }
  //     ]
  //   });
  //   container.innerHTML = widget.render();
  //   widget.bind();
  //   widget.update({ used: 100, total: 1000, states: 'F900A100', ... });
  //
  function PoolWidget(config) {
    this.id = config.id;
    this.name = config.name;
    this.tooltip = config.tooltip || null;
    this.slabKey = config.slabKey || null;
    this.icon = config.icon || null;
    this.preset = config.preset || null;
    this.variant = config.variant || 'compact';

    // Feature flags
    this.showGauge = config.showGauge !== false;
    this.showGrid = config.showGrid !== false;
    this.showLegend = config.showLegend === true || this.variant === 'full';
    this.showOwnerBreakdown = config.showOwnerBreakdown === true;

    // Collapsible grid feature - shows compact view with expandable detail
    this.collapsibleGrid = config.collapsibleGrid === true;
    this.gridCollapsed = this._loadGridState();

    // Trend indicator (for non-slab allocators like malloc)
    this.showTrend = config.showTrend === true;
    this.prevUsed = null;
    this.trend = 0;  // -1 = down, 0 = stable, 1 = up

    // Custom colors (override preset)
    this.color = config.color || null;
    this.colorMuted = config.colorMuted || null;

    // Gauge markers (store configs for label formatting)
    this.markers = config.markers || [];
    this.markerConfigs = {};
    for (var i = 0; i < this.markers.length; i++) {
      var m = this.markers[i];
      if (m.id) {
        this.markerConfigs[m.id] = m;
      }
    }

    // Legend configuration
    this.legend = config.legend || [];

    // State configuration for grid
    this.states = config.states || null;
    this.stateClasses = {};
    this.stateColors = {};
    if (this.states) {
      for (var i = 0; i < this.states.length; i++) {
        var s = this.states[i];
        this.stateClasses[s.char] = s.class;
        this.stateColors[s.class] = s.color;
      }
    }

    // Stats configuration
    this.stats = config.stats || [];

    // Thresholds for warning/critical
    this.warningThreshold = config.warningThreshold !== undefined ? config.warningThreshold : 75;
    this.criticalThreshold = config.criticalThreshold !== undefined ? config.criticalThreshold : 90;

    // DOM references (set by bind())
    this.el = null;
    this.canvasEl = null;
    this.ctx = null;
    this.fillEl = null;
    this.badgeEl = null;
    this.usageEl = null;
    this.trendEl = null;
    this.markerEls = {};
    this.statEls = {};

    // Canvas state
    this.canvasConfigured = false;
    this.cellSize = 5;
    this.cellGap = 1;
    this.cols = 0;
    this.rows = 0;
    this.lastSlabData = null;

    // Zoom state for large slabs
    this.zoomEnabled = config.zoomEnabled !== false;
    this.zoomStart = 0;
    this.zoomEnd = 0;  // 0 = full range
    this.zoomBuckets = null;
    this.zoomPending = false;
  }

  // Default state mappings
  PoolWidget.DEFAULT_STATES = [
    { char: 'F', class: 'free', label: 'Free', color: 'rgba(255, 255, 255, 0.25)' },
    { char: 'U', class: 'used', label: 'Used', color: '#3fb950' },
    { char: 'A', class: 'active', label: 'Active', color: '#3fb950' },
    { char: 'N', class: 'connecting', label: 'Connecting', color: '#58a6ff' },
    { char: 'I', class: 'idle', label: 'Idle', color: '#1f6feb' },
    { char: 'C', class: 'closing', label: 'Closing', color: '#d29922' },
    { char: 'T', class: 'tcp-listener', label: 'TCP Listener', color: '#a371f7' },
    { char: 'K', class: 'task', label: 'Task', color: '#39d4d4' },
    { char: 'M', class: 'timer', label: 'Timer', color: '#9e6a03' }
  ];

  // Color presets
  PoolWidget.PRESETS = {
    slab: { color: 'var(--color-cyan)', colorMuted: 'var(--color-cyan-muted)' },
    malloc: { color: 'var(--color-warning)', colorMuted: 'var(--color-warning-muted)' },
    arena: { color: 'var(--color-ok)', colorMuted: 'var(--color-ok-muted)' },
    buffer: { color: 'var(--color-purple)', colorMuted: 'var(--color-purple-muted)' },
    queue: { color: 'var(--color-info)', colorMuted: 'var(--color-info-muted)' }
  };

  // Canvas colors (matching CSS variables)
  PoolWidget.COLORS = {
    free: 'rgba(255, 255, 255, 0.25)',
    used: '#3fb950',
    active: '#3fb950',
    connecting: '#58a6ff',
    idle: '#1f6feb',
    closing: '#d29922',
    'tcp-listener': '#a371f7',
    task: '#39d4d4',
    timer: '#9e6a03'
  };

  // Format a value based on format type
  // Supported formats: 'bytes', 'count', 'percent', or a custom function
  PoolWidget.formatValue = function(value, format) {
    if (typeof format === 'function') {
      return format(value);
    }
    switch (format) {
      case 'bytes':
        if (value >= 1024 * 1024 * 1024) return (value / (1024 * 1024 * 1024)).toFixed(1) + ' GB';
        if (value >= 1024 * 1024) return (value / (1024 * 1024)).toFixed(1) + ' MB';
        if (value >= 1024) return (value / 1024).toFixed(1) + ' KB';
        return value + ' B';
      case 'count':
        return value.toLocaleString();
      case 'percent':
        return Math.round(value) + '%';
      default:
        return String(value);
    }
  };

  // Render the widget HTML
  PoolWidget.prototype.render = function() {
    var classes = ['pool-widget'];
    if (this.preset) classes.push(this.preset);
    if (this.variant) classes.push(this.variant);

    // Build inline style for custom colors
    var style = '';
    if (this.color) style += '--pool-color: ' + this.color + ';';
    if (this.colorMuted) style += '--pool-color-muted: ' + this.colorMuted + ';';
    var styleAttr = style ? ' style="' + style + '"' : '';

    var html = '<div class="' + classes.join(' ') + '" id="' + this.id + '"' + styleAttr + '>';

    // Header
    html += '<div class="pool-widget-header">';
    // Toggle button for collapsible grid (left side for accessibility)
    if (this.collapsibleGrid && this.showGrid) {
      var expanded = !this.gridCollapsed;
      html += '<button class="pool-widget-toggle" aria-expanded="' + expanded + '" title="' + (this.gridCollapsed ? 'Show detailed grid' : 'Hide detailed grid') + '">';
      html += '<svg class="toggle-chevron" viewBox="0 0 12 12" width="12" height="12"><path d="M3 4.5L6 7.5L9 4.5" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/></svg>';
      html += '</button>';
    } else if (this.showTrend) {
      // Trend indicator for non-slab allocators (occupies chevron space)
      html += '<span class="pool-widget-trend" id="' + this.id + '-trend" title="Memory trend">→</span>';
    }
    if (this.icon) {
      html += '<span class="pool-widget-icon">' + this.icon + '</span>';
    }
    html += '<span class="pool-widget-name"' + (this.tooltip ? ' title="' + this.tooltip + '"' : '') + '>' + this.name + '</span>';
    html += '<span class="pool-widget-usage" id="' + this.id + '-usage">-- / --</span>';
    html += '<span class="pool-widget-badge" id="' + this.id + '-badge">--%</span>';
    html += '</div>';

    // Gauge bar (if enabled)
    if (this.showGauge) {
      var gaugeClasses = 'pool-widget-gauge';
      if (this.collapsibleGrid && this.showGrid) gaugeClasses += ' has-minimap';
      html += '<div class="' + gaugeClasses + '">';
      // Mini-map canvas for collapsible grids (shows compressed memory view in gauge)
      if (this.collapsibleGrid && this.showGrid) {
        html += '<canvas class="pool-widget-minimap" id="' + this.id + '-minimap"></canvas>';
      }
      html += '<div class="pool-widget-fill" id="' + this.id + '-fill"></div>';
      html += '<div class="pool-widget-markers">';
      for (var i = 0; i < this.markers.length; i++) {
        var m = this.markers[i];
        var mClass = 'pool-widget-marker ' + (m.type || 'custom');
        var mStyle = m.position !== undefined ? 'left:' + m.position + '%;' : '';
        if (m.color) mStyle += 'background:' + m.color + ';';
        var mLabel = m.label ? ' data-label="' + m.label + '"' : '';
        html += '<div class="' + mClass + '" id="' + this.id + '-marker-' + (m.id || m.type || i) + '" style="' + mStyle + '"' + mLabel + '></div>';
      }
      html += '</div></div>';
    }

    // Canvas grid (if enabled)
    if (this.showGrid) {
      var wrapperClasses = 'pool-widget-grid-wrapper';
      if (this.collapsibleGrid && this.gridCollapsed) wrapperClasses += ' collapsed';
      html += '<div class="' + wrapperClasses + '">';
      html += '<div class="pool-widget-grid">';
      html += '<canvas class="pool-widget-canvas" id="' + this.id + '-canvas"></canvas>';
      html += '</div>';
      html += '</div>';
    }

    // Stats row
    if (this.stats.length > 0 && this.variant !== 'mini') {
      html += '<div class="pool-widget-stats">';
      for (var i = 0; i < this.stats.length; i++) {
        var st = this.stats[i];
        html += '<span class="pool-widget-stat">';
        html += '<span class="label">' + st.label + '</span>';
        html += '<span class="value" id="' + this.id + '-stat-' + st.id + '">--</span>';
        if (st.suffix) html += '<span class="label">' + st.suffix + '</span>';
        html += '</span>';
      }
      html += '</div>';
    }

    // Legend (if enabled)
    if (this.showLegend && this.legend.length > 0) {
      html += '<div class="pool-widget-legend">';
      for (var i = 0; i < this.legend.length; i++) {
        var lg = this.legend[i];
        html += '<span class="pool-widget-legend-item">';
        if (lg.type === 'bar') {
          html += '<span class="pool-widget-legend-bar" style="background:' + (lg.color || 'var(--pool-color)') + '"></span>';
        } else if (lg.type === 'marker') {
          html += '<span class="pool-widget-legend-marker" style="background:' + (lg.color || 'var(--color-info)') + '"></span>';
        } else if (lg.type === 'dot') {
          html += '<span class="pool-widget-legend-dot" style="background:' + (lg.color || 'var(--color-ok)') + '"></span>';
        }
        html += lg.label + '</span>';
      }
      html += '</div>';
    }

    // Owner breakdown (for handles slab)
    if (this.showOwnerBreakdown) {
      html += '<div class="owner-breakdown"></div>';
    }

    html += '</div>';
    return html;
  };

  // Bind to DOM elements after insertion
  PoolWidget.prototype.bind = function() {
    this.el = document.getElementById(this.id);
    if (!this.el) return false;

    this.badgeEl = document.getElementById(this.id + '-badge');
    this.usageEl = document.getElementById(this.id + '-usage');
    this.fillEl = document.getElementById(this.id + '-fill');
    this.trendEl = document.getElementById(this.id + '-trend');

    // Bind marker elements
    this.markerEls = {};
    for (var i = 0; i < this.markers.length; i++) {
      var m = this.markers[i];
      var mId = m.id || m.type || i;
      this.markerEls[mId] = document.getElementById(this.id + '-marker-' + mId);
    }

    // Bind stat elements
    this.statEls = {};
    for (var i = 0; i < this.stats.length; i++) {
      var st = this.stats[i];
      this.statEls[st.id] = document.getElementById(this.id + '-stat-' + st.id);
    }

    // Bind canvas
    this.canvasEl = document.getElementById(this.id + '-canvas');
    if (this.canvasEl) {
      this.ctx = this.canvasEl.getContext('2d');

      // Watch for resize
      var self = this;
      if (window.ResizeObserver) {
        this.resizeObserver = new ResizeObserver(function() {
          if (self.lastSlabData) {
            self.canvasConfigured = false;
            self._renderGrid(self.lastSlabData);
          }
        });
        var container = this.canvasEl.parentElement;
        if (container) this.resizeObserver.observe(container);
      }

      // Zoom click handler for heatmap cells
      if (this.zoomEnabled && this.slabKey) {
        this.canvasEl.style.cursor = 'pointer';
        this.canvasEl.addEventListener('click', function(e) {
          self._handleZoomClick(e);
        });
      }
    }

    // Bind minimap canvas for collapsible grids
    this.minimapEl = document.getElementById(this.id + '-minimap');
    if (this.minimapEl) {
      this.minimapCtx = this.minimapEl.getContext('2d');
      this.minimapConfigured = false;

      // Watch for gauge resize to reconfigure minimap
      var self = this;
      if (window.ResizeObserver) {
        var gaugeEl = this.minimapEl.parentElement;
        if (gaugeEl) {
          this.minimapResizeObserver = new ResizeObserver(function() {
            self.minimapConfigured = false;
            if (self.lastSlabData) {
              self._renderMinimap(self.lastSlabData);
            }
          });
          this.minimapResizeObserver.observe(gaugeEl);
        }
      }
    }

    // Bind toggle button for collapsible grid
    if (this.collapsibleGrid) {
      var self = this;
      var toggleBtn = this.el.querySelector('.pool-widget-toggle');
      if (toggleBtn) {
        toggleBtn.addEventListener('click', function(e) {
          e.preventDefault();
          e.stopPropagation();
          self.toggleGrid();
        });
      }
    }

    return true;
  };

  // Load grid collapsed state from localStorage
  PoolWidget.prototype._loadGridState = function() {
    if (!this.collapsibleGrid) return false;
    try {
      var prefs = JSON.parse(localStorage.getItem('pool-widget-grids') || '{}');
      return prefs[this.id] !== false; // Default to collapsed (true)
    } catch(e) { return true; }
  };

  // Save grid collapsed state to localStorage
  PoolWidget.prototype._saveGridState = function() {
    try {
      var prefs = JSON.parse(localStorage.getItem('pool-widget-grids') || '{}');
      prefs[this.id] = this.gridCollapsed;
      localStorage.setItem('pool-widget-grids', JSON.stringify(prefs));
    } catch(e) {}
  };

  // Toggle grid collapsed state
  PoolWidget.prototype.toggleGrid = function() {
    if (!this.collapsibleGrid || !this.el) return;
    // Don't toggle if minimap shows all slots (expanded would be redundant)
    if (this.minimapIs1to1) return;
    this.gridCollapsed = !this.gridCollapsed;
    this._saveGridState();
    this._updateGridVisibility();
  };

  // Update grid visibility based on collapsed state
  PoolWidget.prototype._updateGridVisibility = function() {
    if (!this.el) return;
    var gridWrapper = this.el.querySelector('.pool-widget-grid-wrapper');
    var toggleBtn = this.el.querySelector('.pool-widget-toggle');

    if (gridWrapper) {
      if (this.gridCollapsed) {
        gridWrapper.classList.add('collapsed');
      } else {
        gridWrapper.classList.remove('collapsed');
        // Re-render grid when expanded (may have been skipped while collapsed)
        if (this.lastSlabData && this.showGrid && this.canvasEl && this.ctx) {
          this.canvasConfigured = false;
          this._renderGrid(this.lastSlabData);
        }
      }
    }

    if (toggleBtn) {
      toggleBtn.setAttribute('aria-expanded', !this.gridCollapsed);
      toggleBtn.title = this.gridCollapsed ? 'Show detailed grid' : 'Hide detailed grid';
    }
  };

  // Update UI when grid is too large to render 1:1 (>MAX_GRID_SLOTS)
  PoolWidget.prototype._setGridTooLarge = function(tooLarge, slotCount) {
    if (!this.el) return;

    var gridWrapper = this.el.querySelector('.pool-widget-grid-wrapper');

    this.gridTooLarge = tooLarge;

    if (gridWrapper) {
      if (tooLarge) {
        gridWrapper.classList.add('downsampled');
      } else {
        gridWrapper.classList.remove('downsampled');
      }
    }
  };

  // Update widget with new data
  // data: { used, total, usedFormatted?, totalFormatted?, states?, bitmap?, markers:{}, stats:{} }
  PoolWidget.prototype.update = function(data) {
    if (!this.el) return;

    var used = data.used || 0;
    var total = data.total || 1;
    var pct = data.pct !== undefined ? data.pct : (used / total) * 100;

    // Merge with previous data to preserve states/bitmap across updates
    // (gauge updates may not include grid data and vice versa)
    // Note: slab data has slot counts, gauge data has byte counts - keep both
    if (this.lastSlabData) {
      if (data.states === undefined && this.lastSlabData.states !== undefined) {
        data.states = this.lastSlabData.states;
        // Also preserve slot-based total for grid sizing (different from byte total)
        if (data.slotTotal === undefined && this.lastSlabData.slotTotal !== undefined) {
          data.slotTotal = this.lastSlabData.slotTotal;
        } else if (this.lastSlabData.total !== undefined && !this.lastSlabData.usedFormatted) {
          // Previous data was slot-based (no formatted strings), preserve as slotTotal
          data.slotTotal = this.lastSlabData.total;
        }
      }
      if (data.bitmap === undefined && this.lastSlabData.bitmap !== undefined) {
        data.bitmap = this.lastSlabData.bitmap;
        if (data.slotTotal === undefined && this.lastSlabData.slotTotal !== undefined) {
          data.slotTotal = this.lastSlabData.slotTotal;
        }
      }
    }
    // If this is slab data (has states or bitmap but no formatted strings), store total as slotTotal
    if ((data.states !== undefined || data.bitmap !== undefined) && !data.usedFormatted && data.slotTotal === undefined) {
      data.slotTotal = data.total;
    }

    // Store for resize
    this.lastSlabData = data;

    // Update gauge fill
    if (this.fillEl) {
      this.fillEl.style.width = Math.min(pct, 100) + '%';
      this.fillEl.classList.remove('warning', 'critical');
      if (pct >= this.criticalThreshold) {
        this.fillEl.classList.add('critical');
      } else if (pct >= this.warningThreshold) {
        this.fillEl.classList.add('warning');
      }
    }

    // Update badge
    if (this.badgeEl) {
      this.badgeEl.textContent = Math.round(pct) + '%';
      this.badgeEl.classList.remove('warning', 'critical');
      if (pct >= this.criticalThreshold) {
        this.badgeEl.classList.add('critical');
      } else if (pct >= this.warningThreshold) {
        this.badgeEl.classList.add('warning');
      }
    }

    // Update usage
    if (this.usageEl) {
      if (data.usedFormatted && data.totalFormatted) {
        this.usageEl.textContent = data.usedFormatted + ' / ' + data.totalFormatted;
      } else {
        this.usageEl.textContent = used + ' / ' + total;
      }
    }

    // Update trend indicator
    if (this.trendEl && this.showTrend) {
      if (this.prevUsed !== null) {
        var delta = used - this.prevUsed;
        // Use threshold to avoid jitter (0.1% of total)
        var threshold = total * 0.001;
        if (delta > threshold) {
          this.trend = 1;
          this.trendEl.textContent = '▲';
          this.trendEl.className = 'pool-widget-trend up';
        } else if (delta < -threshold) {
          this.trend = -1;
          this.trendEl.textContent = '▼';
          this.trendEl.className = 'pool-widget-trend down';
        } else {
          this.trend = 0;
          this.trendEl.textContent = '→';
          this.trendEl.className = 'pool-widget-trend stable';
        }
      }
      this.prevUsed = used;
    }

    // Update markers
    if (data.markers) {
      for (var mId in data.markers) {
        var mEl = this.markerEls[mId];
        if (mEl) {
          var mv = data.markers[mId];
          var mConfig = this.markerConfigs[mId];
          if (typeof mv === 'object') {
            if (mv.position !== undefined) mEl.style.left = mv.position + '%';
            if (mv.color) mEl.style.background = mv.color;
            // Auto-format label from value if config has valueFormat
            if (mv.label !== undefined) {
              mEl.setAttribute('data-label', mv.label);
            } else if (mv.value !== undefined && mConfig && mConfig.valueFormat) {
              var prefix = mConfig.labelPrefix !== undefined ? mConfig.labelPrefix : (mConfig.label + ': ');
              var suffix = mConfig.labelSuffix || '';
              mEl.setAttribute('data-label', prefix + PoolWidget.formatValue(mv.value, mConfig.valueFormat) + suffix);
            }
          } else {
            // Simple number = position only
            mEl.style.left = mv + '%';
          }
        }
      }
    }

    // Update stats
    if (data.stats) {
      for (var sId in data.stats) {
        var sEl = this.statEls[sId];
        if (sEl) sEl.textContent = data.stats[sId];
      }
    }

    // Render grid (full detail view)
    if (this.showGrid && this.canvasEl && this.ctx) {
      this._renderGrid(data);
    }

    // Render minimap in gauge (compressed preview)
    if (this.minimapEl && this.minimapCtx) {
      this._renderMinimap(data);
    }
  };

  // Configure canvas dimensions
  PoolWidget.prototype._configureCanvas = function(total) {
    if (!this.canvasEl) return;

    var cellSize = this.cellSize;
    var gap = this.cellGap;
    var step = cellSize + gap;

    var container = this.canvasEl.parentElement;
    var containerWidth = container ? container.clientWidth : 200;

    var cols = Math.max(1, Math.floor(containerWidth / step));
    var rows = Math.ceil(total / cols);

    var width = containerWidth;
    var height = rows * step;

    var dpr = window.devicePixelRatio || 1;
    this.canvasEl.width = width * dpr;
    this.canvasEl.height = height * dpr;
    this.canvasEl.style.width = width + 'px';
    this.canvasEl.style.height = height + 'px';

    this.ctx.setTransform(1, 0, 0, 1, 0, 0);
    this.ctx.scale(dpr, dpr);

    this.cols = cols;
    this.rows = rows;
    this.canvasConfigured = true;
  };

  // Maximum slots to render in the detailed grid view
  // Above this limit, the grid shows a placeholder message instead
  // 10K slots = ~60KB of canvas memory, renders in <10ms
  PoolWidget.MAX_GRID_SLOTS = 10000;

  // Render grid from data
  PoolWidget.prototype._renderGrid = function(data) {
    // Only render grid if we have slot-based data (states or bitmap)
    // Don't use byte totals for grid sizing - they're way too large
    if (!data.states && data.bitmap === undefined) return;

    // Use slotTotal for grid sizing (slot count), fall back to total only if reasonable
    var total = data.slotTotal || data.total || 0;
    if (total <= 0 || total > 500000) return;  // Sanity check

    // Check if grid is too large BEFORE checking collapsed state
    // This ensures the UI state is always correct
    var tooLarge = total > PoolWidget.MAX_GRID_SLOTS;
    this._setGridTooLarge(tooLarge, total);

    // Skip rendering if grid is collapsed (save CPU cycles)
    if (this.collapsibleGrid && this.gridCollapsed) return;

    var container = this.canvasEl.parentElement;
    var containerWidth = container ? container.clientWidth : 0;

    // For large slabs, render a downsampled heatmap instead of 1:1 grid
    if (tooLarge) {
      if (!this.heatmapConfigured || this.lastTotal !== total || this.lastContainerWidth !== containerWidth) {
        this._configureHeatmap(total, containerWidth);
        this.lastTotal = total;
        this.lastContainerWidth = containerWidth;
      }
      var self = this;
      if (data.states) {
        requestAnimationFrame(function() { self._renderHeatmapStates(data.states, total); });
      } else if (data.bitmap !== undefined) {
        requestAnimationFrame(function() { self._renderHeatmapBitmap(data.bitmap, total); });
      }
      return;
    }

    if (!this.canvasConfigured || this.lastTotal !== total || this.lastContainerWidth !== containerWidth) {
      this._configureCanvas(total);
      this.lastTotal = total;
      this.lastContainerWidth = containerWidth;
    }

    var self = this;
    if (data.states) {
      requestAnimationFrame(function() { self._renderStateGrid(data.states, total); });
    } else if (data.bitmap !== undefined) {
      requestAnimationFrame(function() { self._renderBitmapGrid(data.bitmap, total); });
    } else {
      requestAnimationFrame(function() { self._renderEmptyGrid(total, data.used || 0); });
    }
  };

  // Configure canvas for downsampled heatmap (for large slabs)
  // Max 8K cells (e.g., 128x64) regardless of actual slot count
  PoolWidget.prototype._configureHeatmap = function(total, containerWidth) {
    if (!this.canvasEl) return;

    var cellSize = 4;  // Smaller cells for heatmap
    var gap = 1;
    var step = cellSize + gap;

    var cols = Math.max(1, Math.floor(containerWidth / step));
    // Limit rows to keep total cells under 8K
    var maxCells = 8192;
    var maxRows = Math.ceil(maxCells / cols);
    var idealRows = Math.ceil(total / cols);
    var rows = Math.min(idealRows, maxRows);

    // Calculate how many slots each cell represents
    this.heatmapSlotsPerCell = Math.ceil(total / (cols * rows));
    this.heatmapCols = cols;
    this.heatmapRows = rows;
    this.heatmapCellSize = cellSize;
    this.heatmapGap = gap;

    var width = containerWidth;
    var height = rows * step;

    var dpr = window.devicePixelRatio || 1;
    this.canvasEl.width = width * dpr;
    this.canvasEl.height = height * dpr;
    this.canvasEl.style.width = width + 'px';
    this.canvasEl.style.height = height + 'px';

    this.ctx.setTransform(1, 0, 0, 1, 0, 0);
    this.ctx.scale(dpr, dpr);

    this.heatmapConfigured = true;
    this.canvasConfigured = false;  // Mark 1:1 config as stale
  };

  // Render downsampled heatmap from RLE state string
  // Each cell shows utilization ratio of the slots it represents
  PoolWidget.prototype._renderHeatmapStates = function(rleStr, total) {
    var ctx = this.ctx;
    var cols = this.heatmapCols;
    var rows = this.heatmapRows;
    var cellSize = this.heatmapCellSize;
    var step = cellSize + this.heatmapGap;
    var slotsPerCell = this.heatmapSlotsPerCell;
    var totalCells = cols * rows;
    var colors = PoolWidget.COLORS;

    ctx.clearRect(0, 0, this.canvasEl.width, this.canvasEl.height);

    // Build bucket counts - one per cell
    var buckets = new Array(totalCells);
    for (var i = 0; i < totalCells; i++) {
      buckets[i] = { free: 0, used: 0 };
    }

    // Parse RLE and fill buckets efficiently (O(runs) not O(slots))
    var slotIdx = 0;
    var i = 0;
    while (i < rleStr.length && slotIdx < total) {
      var stateChar = rleStr[i++];
      var countStr = '';
      while (i < rleStr.length && rleStr[i] >= '0' && rleStr[i] <= '9') countStr += rleStr[i++];
      var count = parseInt(countStr, 10) || 1;
      count = Math.min(count, total - slotIdx);

      var isFree = (stateChar === 'F');
      var runEnd = slotIdx + count;

      while (slotIdx < runEnd) {
        var cellIdx = Math.min(Math.floor(slotIdx / slotsPerCell), totalCells - 1);
        var cellEnd = Math.min((cellIdx + 1) * slotsPerCell, runEnd);
        var slotsInCell = cellEnd - slotIdx;

        if (isFree) {
          buckets[cellIdx].free += slotsInCell;
        } else {
          buckets[cellIdx].used += slotsInCell;
        }
        slotIdx = cellEnd;
      }
    }

    // Fill remaining slots as free
    while (slotIdx < total) {
      var cellIdx = Math.min(Math.floor(slotIdx / slotsPerCell), totalCells - 1);
      var cellEnd = Math.min((cellIdx + 1) * slotsPerCell, total);
      buckets[cellIdx].free += cellEnd - slotIdx;
      slotIdx = cellEnd;
    }

    // Render cells with color based on utilization
    var freeColor = colors.free;
    var usedColor = colors.used;

    for (var c = 0; c < totalCells; c++) {
      var bucket = buckets[c];
      var totalInBucket = bucket.free + bucket.used;
      if (totalInBucket === 0) continue;

      var usedRatio = bucket.used / totalInBucket;
      var x = (c % cols) * step;
      var y = Math.floor(c / cols) * step;

      if (usedRatio === 0) {
        ctx.fillStyle = freeColor;
      } else if (usedRatio === 1) {
        ctx.fillStyle = usedColor;
      } else {
        ctx.fillStyle = this._blendColor(freeColor, usedColor, usedRatio);
      }

      ctx.fillRect(x, y, cellSize, cellSize);
    }
  };

  // Render downsampled heatmap from bitmap
  PoolWidget.prototype._renderHeatmapBitmap = function(rleHex, total) {
    var ctx = this.ctx;
    var cols = this.heatmapCols;
    var rows = this.heatmapRows;
    var cellSize = this.heatmapCellSize;
    var step = cellSize + this.heatmapGap;
    var slotsPerCell = this.heatmapSlotsPerCell;
    var totalCells = cols * rows;
    var colors = PoolWidget.COLORS;

    ctx.clearRect(0, 0, this.canvasEl.width, this.canvasEl.height);

    var buckets = new Array(totalCells);
    for (var i = 0; i < totalCells; i++) {
      buckets[i] = { free: 0, used: 0 };
    }

    // Popcount table
    var popcount8 = new Uint8Array(256);
    for (var i = 0; i < 256; i++) {
      var c = i;
      c = c - ((c >> 1) & 0x55);
      c = (c & 0x33) + ((c >> 2) & 0x33);
      popcount8[i] = (c + (c >> 4)) & 0x0F;
    }

    var segments = rleHex ? rleHex.split(',') : [];
    var slotIdx = 0;

    for (var s = 0; s < segments.length && slotIdx < total; s++) {
      var segment = segments[s];
      var starIdx = segment.indexOf('*');
      var hexByte = starIdx !== -1 ? segment.substring(0, starIdx) : segment;
      var byteCount = starIdx !== -1 ? parseInt(segment.substring(starIdx + 1), 10) || 1 : 1;
      var byteVal = parseInt(hexByte, 16);
      if (isNaN(byteVal)) continue;

      for (var b = 0; b < byteCount && slotIdx < total; b++) {
        var bitsToProcess = Math.min(8, total - slotIdx);
        var cellIdx = Math.min(Math.floor(slotIdx / slotsPerCell), totalCells - 1);
        var cellEnd = (cellIdx + 1) * slotsPerCell;

        // Fast path: all bits in same cell
        if (slotIdx + bitsToProcess <= cellEnd) {
          var usedBits = popcount8[byteVal & ((1 << bitsToProcess) - 1)];
          buckets[cellIdx].used += usedBits;
          buckets[cellIdx].free += bitsToProcess - usedBits;
        } else {
          // Slow path: bits span cells
          for (var bit = 0; bit < bitsToProcess; bit++) {
            var ci = Math.min(Math.floor((slotIdx + bit) / slotsPerCell), totalCells - 1);
            if ((byteVal >> bit) & 1) {
              buckets[ci].used++;
            } else {
              buckets[ci].free++;
            }
          }
        }
        slotIdx += bitsToProcess;
      }
    }

    // Fill remaining as free
    while (slotIdx < total) {
      var cellIdx = Math.min(Math.floor(slotIdx / slotsPerCell), totalCells - 1);
      var cellEnd = Math.min((cellIdx + 1) * slotsPerCell, total);
      buckets[cellIdx].free += cellEnd - slotIdx;
      slotIdx = cellEnd;
    }

    // Render
    var freeColor = colors.free;
    var usedColor = colors.used;

    for (var c = 0; c < totalCells; c++) {
      var bucket = buckets[c];
      var totalInBucket = bucket.free + bucket.used;
      if (totalInBucket === 0) continue;

      var usedRatio = bucket.used / totalInBucket;
      var x = (c % cols) * step;
      var y = Math.floor(c / cols) * step;

      if (usedRatio === 0) {
        ctx.fillStyle = freeColor;
      } else if (usedRatio === 1) {
        ctx.fillStyle = usedColor;
      } else {
        ctx.fillStyle = this._blendColor(freeColor, usedColor, usedRatio);
      }

      ctx.fillRect(x, y, cellSize, cellSize);
    }
  };

  // Render state grid from RLE string
  PoolWidget.prototype._renderStateGrid = function(rleStr, total) {
    var ctx = this.ctx;
    var cellSize = this.cellSize;
    var step = cellSize + this.cellGap;
    var cols = this.cols;
    var colors = PoolWidget.COLORS;

    ctx.clearRect(0, 0, this.canvasEl.width, this.canvasEl.height);

    if (!rleStr || rleStr.length === 0) {
      ctx.fillStyle = colors.free;
      for (var i = 0; i < total; i++) {
        ctx.fillRect((i % cols) * step, Math.floor(i / cols) * step, cellSize, cellSize);
      }
      return;
    }

    var slotIdx = 0, i = 0;
    while (i < rleStr.length && slotIdx < total) {
      var stateChar = rleStr[i++];
      var countStr = '';
      while (i < rleStr.length && rleStr[i] >= '0' && rleStr[i] <= '9') countStr += rleStr[i++];
      var count = parseInt(countStr, 10) || 1;

      var cssClass = this.stateClasses[stateChar] || (PoolWidget.DEFAULT_STATES.find(function(s) { return s.char === stateChar; }) || {}).class || 'free';
      ctx.fillStyle = this.stateColors[cssClass] || colors[cssClass] || colors.free;

      for (var c = 0; c < count && slotIdx < total; c++, slotIdx++) {
        ctx.fillRect((slotIdx % cols) * step, Math.floor(slotIdx / cols) * step, cellSize, cellSize);
      }
    }

    ctx.fillStyle = colors.free;
    while (slotIdx < total) {
      ctx.fillRect((slotIdx % cols) * step, Math.floor(slotIdx / cols) * step, cellSize, cellSize);
      slotIdx++;
    }
  };

  // Render bitmap grid from RLE hex
  PoolWidget.prototype._renderBitmapGrid = function(rleHex, total) {
    var ctx = this.ctx;
    var cellSize = this.cellSize;
    var step = cellSize + this.cellGap;
    var cols = this.cols;
    var colors = PoolWidget.COLORS;

    ctx.clearRect(0, 0, this.canvasEl.width, this.canvasEl.height);

    if (!rleHex) {
      ctx.fillStyle = colors.free;
      for (var i = 0; i < total; i++) {
        ctx.fillRect((i % cols) * step, Math.floor(i / cols) * step, cellSize, cellSize);
      }
      return;
    }

    var segments = rleHex.split(',');
    var slotIdx = 0;

    for (var s = 0; s < segments.length && slotIdx < total; s++) {
      var segment = segments[s];
      var starIdx = segment.indexOf('*');
      var hexByte = starIdx !== -1 ? segment.substring(0, starIdx) : segment;
      var byteCount = starIdx !== -1 ? parseInt(segment.substring(starIdx + 1), 10) || 1 : 1;
      var byteVal = parseInt(hexByte, 16);
      if (isNaN(byteVal)) continue;

      for (var c = 0; c < byteCount && slotIdx < total; c++) {
        for (var bit = 0; bit < 8 && slotIdx < total; bit++, slotIdx++) {
          ctx.fillStyle = ((byteVal >> bit) & 1) ? colors.used : colors.free;
          ctx.fillRect((slotIdx % cols) * step, Math.floor(slotIdx / cols) * step, cellSize, cellSize);
        }
      }
    }

    ctx.fillStyle = colors.free;
    while (slotIdx < total) {
      ctx.fillRect((slotIdx % cols) * step, Math.floor(slotIdx / cols) * step, cellSize, cellSize);
      slotIdx++;
    }
  };

  // Render empty/simple used grid
  PoolWidget.prototype._renderEmptyGrid = function(total, used) {
    var ctx = this.ctx;
    var cellSize = this.cellSize;
    var step = cellSize + this.cellGap;
    var cols = this.cols;
    var colors = PoolWidget.COLORS;

    ctx.clearRect(0, 0, this.canvasEl.width, this.canvasEl.height);

    for (var i = 0; i < total; i++) {
      ctx.fillStyle = i < used ? colors.used : colors.free;
      ctx.fillRect((i % cols) * step, Math.floor(i / cols) * step, cellSize, cellSize);
    }
  };

  // Handle zoom click on heatmap - zoom into clicked region
  PoolWidget.prototype._handleZoomClick = function(e) {
    if (!this.heatmapConfigured || !this.slabKey) return;

    var rect = this.canvasEl.getBoundingClientRect();
    var dpr = window.devicePixelRatio || 1;
    var x = (e.clientX - rect.left) * dpr;
    var y = (e.clientY - rect.top) * dpr;

    // Convert to cell coordinates
    var step = (this.heatmapCellSize + this.heatmapGap) * dpr;
    var col = Math.floor(x / step);
    var row = Math.floor(y / step);
    var cellIdx = row * this.heatmapCols + col;

    var slotsPerCell = this.heatmapSlotsPerCell;
    var total = this.lastTotal || 0;

    // Calculate region to zoom into (expand by 10x the current cell size)
    var zoomFactor = 10;
    var zoomSlots = slotsPerCell * zoomFactor;
    var centerSlot = cellIdx * slotsPerCell + slotsPerCell / 2;

    var start = Math.max(0, Math.floor(centerSlot - zoomSlots / 2));
    var end = Math.min(total, Math.ceil(centerSlot + zoomSlots / 2));

    // If already zoomed in far enough, zoom out
    if (this.zoomEnd > 0 && (end - start) <= PoolWidget.MAX_GRID_SLOTS) {
      this.zoomStart = 0;
      this.zoomEnd = 0;
      this.zoomBuckets = null;
      if (this.lastSlabData) {
        this._renderGrid(this.lastSlabData);
      }
      return;
    }

    // Fetch buckets for the zoomed region
    this._fetchZoomBuckets(this.slabKey, start, end, 256);
  };

  // Fetch bucket data from server for zoom region
  PoolWidget.prototype._fetchZoomBuckets = function(slabName, start, end, numBuckets) {
    if (this.zoomPending) return;

    var self = this;
    this.zoomPending = true;

    var url = '/debug/slab/buckets?slab=' + encodeURIComponent(slabName) +
              '&start=' + start + '&end=' + end + '&buckets=' + numBuckets;

    fetch(url)
      .then(function(resp) { return resp.json(); })
      .then(function(data) {
        self.zoomPending = false;
        if (data && data.buckets) {
          self.zoomStart = start;
          self.zoomEnd = end;
          self.zoomBuckets = data.buckets;
          self._renderZoomHeatmap(data.buckets, start, end);
        }
      })
      .catch(function(err) {
        self.zoomPending = false;
        console.error('Zoom fetch error:', err);
      });
  };

  // Render zoomed heatmap from server bucket data
  PoolWidget.prototype._renderZoomHeatmap = function(buckets, start, end) {
    if (!this.ctx || !buckets || buckets.length === 0) return;

    var ctx = this.ctx;
    var container = this.canvasEl.parentElement;
    var containerWidth = container ? container.clientWidth : 0;

    var cellSize = 4;
    var gap = 1;
    var step = cellSize + gap;

    var cols = Math.max(1, Math.floor(containerWidth / step));
    var rows = Math.ceil(buckets.length / cols);

    // Reconfigure canvas for zoomed view
    var width = containerWidth;
    var height = rows * step;

    var dpr = window.devicePixelRatio || 1;
    this.canvasEl.width = width * dpr;
    this.canvasEl.height = height * dpr;
    this.canvasEl.style.width = width + 'px';
    this.canvasEl.style.height = height + 'px';

    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.scale(dpr, dpr);

    ctx.clearRect(0, 0, width, height);

    var colors = PoolWidget.COLORS;
    var freeColor = colors.free;
    var usedColor = colors.used;

    for (var c = 0; c < buckets.length; c++) {
      var bucket = buckets[c];
      var totalInBucket = (bucket.u || 0) + (bucket.f || 0);
      if (totalInBucket === 0) continue;

      var usedRatio = (bucket.u || 0) / totalInBucket;
      var x = (c % cols) * step;
      var y = Math.floor(c / cols) * step;

      if (usedRatio === 0) {
        ctx.fillStyle = freeColor;
      } else if (usedRatio === 1) {
        ctx.fillStyle = usedColor;
      } else {
        ctx.fillStyle = this._blendColor(freeColor, usedColor, usedRatio);
      }

      ctx.fillRect(x, y, cellSize, cellSize);
    }

    // Draw zoom indicator border
    ctx.strokeStyle = '#58a6ff';
    ctx.lineWidth = 2;
    ctx.strokeRect(1, 1, width - 2, height - 2);

    // Show zoom range info
    var infoText = 'Zoomed: ' + start + '-' + end + ' (click to zoom out)';
    ctx.fillStyle = '#58a6ff';
    ctx.font = '10px monospace';
    ctx.fillText(infoText, 4, height - 4);
  };

  // Configure minimap canvas dimensions
  PoolWidget.prototype._configureMinimap = function(totalSlots) {
    if (!this.minimapEl) return;

    // Get the actual rendered size of the canvas element
    var rect = this.minimapEl.getBoundingClientRect();
    var width = Math.floor(rect.width) || 200;
    var height = Math.floor(rect.height) || 10;

    var dpr = window.devicePixelRatio || 1;
    this.minimapEl.width = width * dpr;
    this.minimapEl.height = height * dpr;

    this.minimapCtx.setTransform(1, 0, 0, 1, 0, 0);
    this.minimapCtx.scale(dpr, dpr);

    this.minimapWidth = width;
    this.minimapHeight = height;

    // Calculate cell layout
    // For small slot counts, show each slot as a cell
    // For large counts, downsample to ~60-80 cells
    var maxCells = 80;
    var gap = 1;
    var cellCount;

    if (totalSlots <= maxCells) {
      // Show each slot as its own cell
      cellCount = totalSlots;
    } else {
      // Downsample to maxCells
      cellCount = maxCells;
    }

    // Calculate cell width to fill the entire gauge width
    // Total width = (cellCount * cellWidth) + ((cellCount - 1) * gap)
    // Solve for cellWidth: cellWidth = (width - (cellCount - 1) * gap) / cellCount
    var cellWidth = (width - (cellCount - 1) * gap) / cellCount;

    // Ensure minimum cell width
    if (cellWidth < 2 && cellCount > 1) {
      // Reduce cell count to fit
      cellCount = Math.floor((width + gap) / (2 + gap));
      cellWidth = (width - (cellCount - 1) * gap) / cellCount;
    }

    this.minimapCellCount = cellCount;
    this.minimapCellWidth = cellWidth;
    this.minimapGap = gap;
    this.minimapTotalSlots = totalSlots;

    // When minimap shows all slots 1:1, disable the toggle (expanded grid would be redundant)
    this.minimapIs1to1 = (cellCount === totalSlots);
    this._updateToggleState();

    this.minimapConfigured = true;
  };

  // Update toggle button based on whether minimap is 1:1
  PoolWidget.prototype._updateToggleState = function() {
    if (!this.el) return;
    var toggleBtn = this.el.querySelector('.pool-widget-toggle');
    if (!toggleBtn) return;

    if (this.minimapIs1to1) {
      // Minimap shows all slots - no need for expanded grid
      toggleBtn.classList.add('disabled');
      toggleBtn.setAttribute('aria-disabled', 'true');
      toggleBtn.setAttribute('title', 'All slots visible in minimap');
    } else {
      toggleBtn.classList.remove('disabled');
      toggleBtn.removeAttribute('aria-disabled');
      toggleBtn.setAttribute('title', this.gridCollapsed ? 'Show detailed grid' : 'Hide detailed grid');
    }
  };

  // Render minimap - compressed 1D view of memory states in the gauge
  PoolWidget.prototype._renderMinimap = function(data) {
    if (!this.minimapEl || !this.minimapCtx) return;
    if (!data.states && data.bitmap === undefined) return;

    var total = data.slotTotal || data.total || 0;
    if (total <= 0 || total > 500000) return;

    // Configure canvas if needed (reconfigure if width or slot count changes)
    var rect = this.minimapEl.getBoundingClientRect();
    var currentWidth = Math.floor(rect.width);
    if (!this.minimapConfigured || this.lastMinimapWidth !== currentWidth || this.minimapTotalSlots !== total) {
      this._configureMinimap(total);
      this.lastMinimapWidth = currentWidth;
    }

    var ctx = this.minimapCtx;
    var width = this.minimapWidth;
    var height = this.minimapHeight;
    var colors = PoolWidget.COLORS;

    ctx.clearRect(0, 0, this.minimapEl.width, this.minimapEl.height);

    if (data.states) {
      this._renderMinimapStates(data.states, total, width, height);
    } else if (data.bitmap !== undefined) {
      this._renderMinimapBitmap(data.bitmap, total, width, height);
    }
  };

  // Render minimap from RLE state string - downsamples to discrete cells
  // Optimized: processes RLE runs directly without iterating each slot
  PoolWidget.prototype._renderMinimapStates = function(rleStr, total, width, height) {
    var ctx = this.minimapCtx;
    var colors = PoolWidget.COLORS;
    var cellCount = this.minimapCellCount;
    var cellWidth = this.minimapCellWidth;
    var gap = this.minimapGap;

    // Each cell represents (total / cellCount) slots
    var slotsPerCell = total / cellCount;
    var buckets = new Array(cellCount);

    // Initialize buckets with state counts
    for (var i = 0; i < buckets.length; i++) {
      buckets[i] = { free: 0, used: 0 };
    }

    // Parse RLE and fill buckets - optimized to process runs, not individual slots
    var slotIdx = 0;
    var i = 0;
    while (i < rleStr.length && slotIdx < total) {
      var stateChar = rleStr[i++];
      var countStr = '';
      while (i < rleStr.length && rleStr[i] >= '0' && rleStr[i] <= '9') countStr += rleStr[i++];
      var count = parseInt(countStr, 10) || 1;
      count = Math.min(count, total - slotIdx);  // Clamp to remaining slots

      var isFree = (stateChar === 'F');

      // Distribute this run across buckets without per-slot iteration
      var runEnd = slotIdx + count;
      while (slotIdx < runEnd) {
        var bucketIdx = Math.min(Math.floor(slotIdx / slotsPerCell), cellCount - 1);
        var bucketEnd = Math.min((bucketIdx + 1) * slotsPerCell, runEnd);
        var slotsInBucket = Math.floor(bucketEnd) - slotIdx;
        if (slotsInBucket <= 0) slotsInBucket = 1;

        if (isFree) {
          buckets[bucketIdx].free += slotsInBucket;
        } else {
          buckets[bucketIdx].used += slotsInBucket;
        }
        slotIdx += slotsInBucket;
      }
    }

    // Fill remaining slots as free (distribute across buckets)
    if (slotIdx < total) {
      var remaining = total - slotIdx;
      while (slotIdx < total) {
        var bucketIdx = Math.min(Math.floor(slotIdx / slotsPerCell), cellCount - 1);
        var bucketEnd = Math.min((bucketIdx + 1) * slotsPerCell, total);
        var slotsInBucket = Math.floor(bucketEnd) - slotIdx;
        if (slotsInBucket <= 0) slotsInBucket = 1;
        buckets[bucketIdx].free += slotsInBucket;
        slotIdx += slotsInBucket;
      }
    }

    // Render discrete cells with gaps
    var freeColor = colors.free;
    var usedColor = colors.used;  // Always use standard green for used slots

    for (var c = 0; c < cellCount; c++) {
      var bucket = buckets[c];
      var totalInBucket = bucket.free + bucket.used;
      if (totalInBucket === 0) continue;

      var usedRatio = bucket.used / totalInBucket;
      var x = c * (cellWidth + gap);

      if (usedRatio === 0) {
        ctx.fillStyle = freeColor;
      } else if (usedRatio === 1) {
        ctx.fillStyle = usedColor;
      } else {
        ctx.fillStyle = this._blendColor(freeColor, usedColor, usedRatio);
      }

      ctx.fillRect(x, 1, cellWidth, height - 2);
    }
  };

  // Render minimap from bitmap - downsamples to discrete cells
  // Optimized: processes bytes directly and counts bits efficiently
  PoolWidget.prototype._renderMinimapBitmap = function(rleHex, total, width, height) {
    var ctx = this.minimapCtx;
    var colors = PoolWidget.COLORS;
    var cellCount = this.minimapCellCount;
    var cellWidth = this.minimapCellWidth;
    var gap = this.minimapGap;

    var slotsPerCell = total / cellCount;
    var buckets = new Array(cellCount);

    for (var i = 0; i < buckets.length; i++) {
      buckets[i] = { free: 0, used: 0 };
    }

    // Precompute popcount table for fast bit counting
    var popcount8 = new Uint8Array(256);
    for (var i = 0; i < 256; i++) {
      var c = i;
      c = c - ((c >> 1) & 0x55);
      c = (c & 0x33) + ((c >> 2) & 0x33);
      popcount8[i] = (c + (c >> 4)) & 0x0F;
    }

    // Decode bitmap RLE - process whole bytes at a time
    var segments = rleHex ? rleHex.split(',') : [];
    var slotIdx = 0;

    for (var s = 0; s < segments.length && slotIdx < total; s++) {
      var segment = segments[s];
      var starIdx = segment.indexOf('*');
      var hexByte = starIdx !== -1 ? segment.substring(0, starIdx) : segment;
      var byteCount = starIdx !== -1 ? parseInt(segment.substring(starIdx + 1), 10) || 1 : 1;
      var byteVal = parseInt(hexByte, 16);
      if (isNaN(byteVal)) continue;

      // For each repeated byte, distribute 8 slots across buckets
      for (var c = 0; c < byteCount && slotIdx < total; c++) {
        var bitsToProcess = Math.min(8, total - slotIdx);
        var usedBits = popcount8[byteVal & ((1 << bitsToProcess) - 1)];
        var freeBits = bitsToProcess - usedBits;

        // Fast path: if all 8 bits fall into same bucket
        var startBucket = Math.floor(slotIdx / slotsPerCell);
        var endBucket = Math.floor((slotIdx + bitsToProcess - 1) / slotsPerCell);

        if (startBucket === endBucket && startBucket < cellCount) {
          buckets[startBucket].used += usedBits;
          buckets[startBucket].free += freeBits;
        } else {
          // Slow path: bits span multiple buckets - process per-bit
          for (var bit = 0; bit < bitsToProcess; bit++) {
            var bucketIdx = Math.min(Math.floor((slotIdx + bit) / slotsPerCell), cellCount - 1);
            if ((byteVal >> bit) & 1) {
              buckets[bucketIdx].used++;
            } else {
              buckets[bucketIdx].free++;
            }
          }
        }
        slotIdx += bitsToProcess;
      }
    }

    // Fill remaining as free - distribute across buckets efficiently
    if (slotIdx < total) {
      while (slotIdx < total) {
        var bucketIdx = Math.min(Math.floor(slotIdx / slotsPerCell), cellCount - 1);
        var bucketEnd = Math.min(Math.ceil((bucketIdx + 1) * slotsPerCell), total);
        var slotsInBucket = bucketEnd - slotIdx;
        if (slotsInBucket <= 0) slotsInBucket = 1;
        buckets[bucketIdx].free += slotsInBucket;
        slotIdx += slotsInBucket;
      }
    }

    // Render discrete cells with gaps
    var freeColor = colors.free;
    var usedColor = colors.used;  // Always use standard green for used slots

    for (var c = 0; c < cellCount; c++) {
      var bucket = buckets[c];
      var totalInBucket = bucket.free + bucket.used;
      if (totalInBucket === 0) continue;

      var usedRatio = bucket.used / totalInBucket;
      var x = c * (cellWidth + gap);

      if (usedRatio === 0) {
        ctx.fillStyle = freeColor;
      } else if (usedRatio === 1) {
        ctx.fillStyle = usedColor;
      } else {
        ctx.fillStyle = this._blendColor(freeColor, usedColor, usedRatio);
      }

      ctx.fillRect(x, 1, cellWidth, height - 2);
    }
  };

  // Get the preset color for this widget
  PoolWidget.prototype._getPresetColor = function() {
    var presetColors = {
      slab: '#39d4d4',      // cyan
      malloc: '#d29922',    // warning/orange
      arena: '#3fb950',     // green
      buffer: '#a371f7',    // purple
      queue: '#58a6ff'      // info/blue
    };
    return this.preset ? presetColors[this.preset] : null;
  };

  // Blend two colors by ratio - returns rgba string
  PoolWidget.prototype._blendColor = function(color1, color2, ratio) {
    // Parse hex color to rgba with varying alpha based on ratio
    var alpha = 0.25 + (ratio * 0.75); // Range from 0.25 to 1.0

    if (color2.charAt(0) === '#') {
      var r = parseInt(color2.slice(1, 3), 16);
      var g = parseInt(color2.slice(3, 5), 16);
      var b = parseInt(color2.slice(5, 7), 16);
      return 'rgba(' + r + ',' + g + ',' + b + ',' + alpha + ')';
    }

    // If already rgba, replace alpha
    if (color2.indexOf('rgba') === 0) {
      return color2.replace(/[\d.]+\)$/, alpha + ')');
    }

    // Fallback
    return color2;
  };

  // Registry for PoolWidget instances
  PoolWidget.registry = {};

  PoolWidget.register = function(key, widget) {
    if (!PoolWidget.registry[key]) PoolWidget.registry[key] = [];
    PoolWidget.registry[key].push(widget);
  };

  PoolWidget.getAll = function(key) {
    return PoolWidget.registry[key] || [];
  };

  PoolWidget.unregister = function(key, widget) {
    var arr = PoolWidget.registry[key];
    if (!arr) return;
    var idx = arr.indexOf(widget);
    if (idx !== -1) arr.splice(idx, 1);
  };

  PoolWidget.updateAll = function(key, data) {
    var widgets = PoolWidget.getAll(key);
    for (var i = 0; i < widgets.length; i++) widgets[i].update(data);
  };

  // Helper builders
  PoolWidget.Markers = {
    heapMarkers: function(opts) {
      opts = opts || {};
      var hwmMarker = {
        type: 'hwm', id: 'hwm', label: opts.hwmLabel || 'hwm',
        color: opts.hwmColor || 'var(--color-info)',
        valueFormat: opts.hwmFormat || 'bytes'
      };
      if (opts.hwmLabelSuffix) hwmMarker.labelSuffix = opts.hwmLabelSuffix;
      return [
        hwmMarker,
        { type: 'threshold', id: 'threshold', label: opts.thresholdLabel || 'gc',
          color: opts.thresholdColor || 'var(--color-error)',
          valueFormat: 'percent', position: opts.thresholdPosition || 75 }
      ];
    },
    hwmOnly: function(opts) {
      opts = opts || {};
      var marker = {
        type: 'hwm', id: 'hwm', label: opts.hwmLabel || 'hwm',
        color: opts.hwmColor || 'var(--color-info)',
        valueFormat: opts.hwmFormat || 'bytes'
      };
      if (opts.hwmLabelSuffix) marker.labelSuffix = opts.hwmLabelSuffix;
      return [marker];
    }
  };

  PoolWidget.Legend = {
    heap: function() {
      return [
        { type: 'bar', label: 'current' },
        { type: 'marker', label: 'hwm', color: 'var(--color-info)' },
        { type: 'marker', label: 'gc threshold', color: 'var(--color-error)' }
      ];
    },
    states: function(states) {
      return states.map(function(s) {
        return { type: 'dot', label: s.label, color: s.color };
      });
    }
  };

  // Make PoolWidget globally available
  window.PoolWidget = PoolWidget;

  // ==================== State ====================
  var history = {
    requestRate: [],
    errorRate: [],
    latency: [],
    heapUsage: [],
    gcPauses: [],
    loopIterations: [],
    allocRate: [],       // Bytes allocated per second
    reclaimRate: [],     // Bytes reclaimed per second
    evalRate: []         // Evaluations per second
  };
  var prevMetrics = null;
  var prevTimestamp = null;
  var serverCards = {};  // Track dynamically created server cards
  var currentModular = null;  // Current modular metrics (for event loop etc)
  var currentSseMetrics = null;  // Current SSE registry metrics (bytes pushed, etc)

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
          loop: labels.loop || 'main',  // AIO system ownership
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
    while (arr.length > HISTORY_SAMPLES) arr.shift();
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
    var barWidth = 100 / HISTORY_SAMPLES;

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
  // Legacy wrapper for backward compatibility (old signature: containerId, data, color)
  // New code should use the Phase 1 renderMiniSparkline(container, data, options) directly
  function renderMiniSparklineLegacy(containerId, data, color) {
    var container = $(containerId);
    if (!container) return;
    // Call the new function with converted parameters
    renderMiniSparkline(container, data, {
      width: 48,
      height: 20,
      color: color || 'var(--color-info)',
      fillOpacity: 0.2,
      strokeWidth: 1.5
    });
  }

  // Render multi-line percentile sparkline showing P50/P95/P99 trends
  function renderPercentileSparkline(container, history, options) {
    if (!container || !history.p50 || !history.p50.data || history.p50.data.length < 1) return;
    var opts = options || {};
    var ds = opts.displaySamples || SPARKLINE_DISPLAY_SAMPLES;
    renderLineSparkline(container, [
      { data: padSparklineData(history.p99.data, ds), color: 'error', width: 1 },
      { data: padSparklineData(history.p95.data, ds), color: 'warning', width: 1.2 },
      { data: padSparklineData(history.p50.data, ds), color: 'ok', width: 1.5 }
    ], { height: opts.height || 32 });
  }

  // Render stacked bar sparkline showing 2xx/4xx/5xx status codes over time
  function renderStatusCodeSparkline(container, history, options) {
    if (!container || !history || history.length < 2) return;
    var opts = options || {};
    renderBarSparkline(container, history, { height: opts.height || 20 });
  }

  // ==================== Rendering: AIO System Panels ====================
  var aioSystemPanels = {};  // Cache of AIO system panels by name

  // Pre-configured slab widget definitions for AIO systems
  // Each definition creates a PoolWidget with appropriate settings
  var AIO_SLAB_CONFIGS = {
    handles: function(id) {
      return new PoolWidget({
        id: id + '-handles',
        name: 'AIO Handles',
        slabKey: 'handles',
        icon: 'H',
        preset: 'buffer',
        variant: 'full',
        showGauge: true,
        showGrid: true,
        showLegend: true,
        showOwnerBreakdown: true,
        collapsibleGrid: true,
        markers: PoolWidget.Markers.hwmOnly({ hwmFormat: 'count' }),
        states: [
          { char: 'A', class: 'active', label: 'Active', color: PoolWidget.COLORS.active },
          { char: 'I', class: 'idle', label: 'Idle', color: PoolWidget.COLORS.idle },
          { char: 'C', class: 'closing', label: 'Closing', color: PoolWidget.COLORS.closing },
          { char: 'T', class: 'tcp-listener', label: 'TCP', color: PoolWidget.COLORS['tcp-listener'] },
          { char: 'K', class: 'task', label: 'Task', color: PoolWidget.COLORS.task },
          { char: 'M', class: 'timer', label: 'Timer', color: PoolWidget.COLORS.timer },
          { char: 'F', class: 'free', label: 'Free', color: PoolWidget.COLORS.free }
        ],
        legend: [
          { type: 'dot', label: 'active', color: PoolWidget.COLORS.active },
          { type: 'dot', label: 'idle', color: PoolWidget.COLORS.idle },
          { type: 'dot', label: 'closing', color: PoolWidget.COLORS.closing },
          { type: 'dot', label: 'free', color: PoolWidget.COLORS.free }
        ]
      });
    },
    tcp_buffers: function(id) {
      return new PoolWidget({
        id: id + '-tcp-buffers',
        name: 'TCP Buffers',
        slabKey: 'tcp_buffers',
        icon: 'T',
        preset: 'slab',
        variant: 'compact',
        showGauge: true,
        showGrid: true,
        collapsibleGrid: true,
        markers: PoolWidget.Markers.hwmOnly({ hwmFormat: 'count' })
      });
    },
    stream_arenas: function(id) {
      return new PoolWidget({
        id: id + '-stream-arenas',
        name: 'Stream Arenas',
        slabKey: 'stream_arenas',
        icon: 'A',
        preset: 'arena',
        variant: 'compact',
        showGauge: true,
        showGrid: true,
        collapsibleGrid: true,
        markers: PoolWidget.Markers.hwmOnly({ hwmFormat: 'count' })
      });
    },
    queue: function(id) {
      return new PoolWidget({
        id: id + '-queue',
        name: 'Request Queue',
        tooltip: 'HTTP requests/responses queued in the event loop. High values indicate CPU/processing bottleneck.',
        preset: 'queue',
        variant: 'compact',
        showGauge: true,
        showGrid: false,
        warningThreshold: 50,
        criticalThreshold: 80,
        stats: [
          { id: 'pending', label: 'pending:' },
          { id: 'capacity', label: '/', suffix: '' }
        ]
      });
    },
    pendingStreams: function(id) {
      return new PoolWidget({
        id: id + '-pending-streams',
        name: 'Pending Streams',
        tooltip: 'HTTP/2 streams waiting for arena memory allocation. High values indicate memory pool exhaustion.',
        preset: 'queue',
        variant: 'compact',
        showGauge: true,
        showGrid: false,
        warningThreshold: 30,
        criticalThreshold: 70,
        color: '#f0883e',  // Orange for pending streams
        colorMuted: 'rgba(240, 136, 62, 0.3)',
        stats: [
          { id: 'total', label: 'total:' },
          { id: 'now', label: 'now:' },
          { id: 'processed', label: '✓', suffix: '' },
          { id: 'dropped', label: '✗', suffix: '' }
        ]
      });
    }
  };

  function createAioSystemPanel(sys, index) {
    var name = sys.name || 'System ' + (index + 1);
    var id = 'aio-sys-' + index;

    // Check localStorage for saved collapse state
    var isCollapsed = false;
    try {
      var prefs = JSON.parse(localStorage.getItem('dashboard-panels') || '{}');
      isCollapsed = prefs[id] === true;
    } catch(e) {}

    // Create slab widgets and pool gauges for this AIO system
    var widgets = {
      handles: AIO_SLAB_CONFIGS.handles(id),
      tcp_buffers: AIO_SLAB_CONFIGS.tcp_buffers(id),
      stream_arenas: AIO_SLAB_CONFIGS.stream_arenas(id),
      queue: AIO_SLAB_CONFIGS.queue(id),
      pendingStreams: AIO_SLAB_CONFIGS.pendingStreams(id)
    };

    var panelClass = 'panel aio-system-panel' + (isCollapsed ? ' collapsed' : ' aio-expanded');
    var ariaExpanded = isCollapsed ? 'false' : 'true';

    var html =
      '<article class="' + panelClass + '" id="' + id + '" aria-labelledby="' + id + '-title">' +
        '<div class="panel-header" aria-expanded="' + ariaExpanded + '">' +
          '<div class="panel-icon aio" aria-hidden="true">' + (index + 1) + '</div>' +
          '<h3 class="panel-title" id="' + id + '-title">' + name.charAt(0).toUpperCase() + name.slice(1) + ' AIO</h3>' +
          '<div class="panel-badges">' +
            '<div class="panel-badge aio-sys-servers" title="Number of HTTP servers bound to this AIO system">-- servers</div>' +
          '</div>' +
        '</div>' +
        '<div class="panel-body">' +

          // Event Loop - Compact inline with activity visualization
          '<div class="aio-section-block event-loop-block">' +
            '<div class="event-loop-compact">' +
              '<div class="event-loop-header">' +
                '<span class="block-title">Event Loop</span>' +
                '<div class="event-loop-pulse" title="Live activity indicator - pulses with event processing">' +
                  '<span class="pulse-dot"></span>' +
                  '<span class="pulse-dot"></span>' +
                  '<span class="pulse-dot"></span>' +
                  '<span class="pulse-dot"></span>' +
                  '<span class="pulse-dot"></span>' +
                '</div>' +
              '</div>' +
              '<div class="event-loop-metrics">' +
                '<div class="event-loop-util" title="Event loop utilization - percentage of time spent processing vs idle">' +
                  '<div class="util-bar">' +
                    '<div class="util-fill aio-sys-util-fill" style="width: 0%"></div>' +
                  '</div>' +
                  '<span class="util-label"><span class="aio-sys-util-pct">--</span>% busy</span>' +
                '</div>' +
                '<span class="metric-sep">│</span>' +
                '<span class="event-loop-metric" title="Loop iterations per second (poll cycles)">' +
                  '<span class="metric-value aio-sys-iter-rate">--</span>' +
                  '<span class="metric-unit">iter/s</span>' +
                '</span>' +
                '<span class="metric-sep">│</span>' +
                '<span class="event-loop-metric" title="Active libuv handles (sockets, timers, signals)">' +
                  '<span class="metric-value aio-sys-handles">--</span>' +
                  '<span class="metric-unit">handles</span>' +
                '</span>' +
                '<span class="metric-sep">│</span>' +
                '<span class="event-loop-metric queue-metric" title="Pending requests in queue - high values indicate backpressure">' +
                  '<span class="metric-value aio-sys-queue">0</span>' +
                  '<span class="metric-unit">queued</span>' +
                '</span>' +
              '</div>' +
            '</div>' +
          '</div>' +

          // Memory Section (Slabs + Libraries)
          '<div class="aio-section-block memory-section-block">' +
            '<div class="block-header">' +
              '<span class="block-title">Memory</span>' +
              '<span class="block-badge aio-sys-mem-total">--</span>' +
            '</div>' +

            // Library memory stats row (SSL + nghttp2 + libuv)
            '<div class="aio-lib-memory-stats">' +
              '<div class="lib-mem-stat" title="OpenSSL memory usage (TLS encryption)">' +
                '<span class="lib-mem-icon ssl">S</span>' +
                '<span class="lib-mem-label">SSL</span>' +
                '<span class="lib-mem-value aio-ssl-bytes">--</span>' +
              '</div>' +
              '<div class="lib-mem-stat" title="nghttp2 memory usage (HTTP/2 sessions)">' +
                '<span class="lib-mem-icon http2">H2</span>' +
                '<span class="lib-mem-label">nghttp2</span>' +
                '<span class="lib-mem-value aio-nghttp2-bytes">--</span>' +
              '</div>' +
              '<div class="lib-mem-stat" title="libuv memory usage (event loop, handles, buffers)">' +
                '<span class="lib-mem-icon libuv">UV</span>' +
                '<span class="lib-mem-label">libuv</span>' +
                '<span class="lib-mem-value aio-libuv-bytes">--</span>' +
              '</div>' +
              '<div class="lib-mem-stat lib-mem-total" title="Total library memory (SSL + nghttp2 + libuv)">' +
                '<span class="lib-mem-label">Total</span>' +
                '<span class="lib-mem-value aio-lib-total-bytes">--</span>' +
              '</div>' +
            '</div>' +

            // Handle Slab (generated by SlabWidget)
            widgets.handles.render() +

            // Compact resource grids row
            '<div class="aio-slab-grid">' +
              widgets.tcp_buffers.render() +
              widgets.stream_arenas.render() +
              // Request queue gauge (using PoolWidget)
              widgets.queue.render() +
              // Pending streams waiting for arenas
              widgets.pendingStreams.render() +
            '</div>' +

            '<div class="memory-legend-inline">' +
              '<div class="legend-item"><div class="legend-dot free"></div><span>Free</span></div>' +
              '<div class="legend-item"><div class="legend-dot used"></div><span>Used</span></div>' +
              '<div class="legend-item"><div class="legend-dot flash"></div><span>Changed</span></div>' +
            '</div>' +
          '</div>' +

          // HTTP Servers Section (nested under AIO)
          '<div class="aio-section-block http-servers-section" style="display:none">' +
            '<div class="block-header">' +
              '<span class="block-title">HTTP Servers</span>' +
              '<span class="block-badge aio-sys-servers-count">0 servers</span>' +
              '<span class="block-badge aio-sys-servers-rate">0 req/s</span>' +
            '</div>' +
            '<div class="nested-cards-grid aio-sys-servers-container" id="' + id + '-servers-container">' +
            '</div>' +
          '</div>' +

          // HTTP Clients Section (nested under AIO)
          '<div class="aio-section-block http-clients-section" style="display:none">' +
            '<div class="block-header">' +
              '<span class="block-title">HTTP Clients</span>' +
              '<span class="block-badge aio-sys-clients-count">0 clients</span>' +
            '</div>' +
            '<div class="nested-cards-grid aio-sys-clients-container" id="' + id + '-clients-container">' +
            '</div>' +
          '</div>' +

          // TCP Servers Section (nested under AIO)
          '<div class="aio-section-block tcp-servers-section" style="display:none">' +
            '<div class="block-header">' +
              '<span class="block-title">TCP Servers</span>' +
              '<span class="block-badge aio-sys-tcp-servers-count">0 servers</span>' +
            '</div>' +
            '<div class="nested-cards-grid aio-sys-tcp-servers-container" id="' + id + '-tcp-servers-container">' +
            '</div>' +
          '</div>' +

          // TCP Clients Section (nested under AIO)
          '<div class="aio-section-block tcp-clients-section" style="display:none">' +
            '<div class="block-header">' +
              '<span class="block-title">TCP Clients</span>' +
              '<span class="block-badge aio-sys-tcp-clients-count">0 clients</span>' +
            '</div>' +
            '<div class="nested-cards-grid aio-sys-tcp-clients-container" id="' + id + '-tcp-clients-container">' +
            '</div>' +
          '</div>' +

          // UDP Sockets Section (nested under AIO)
          '<div class="aio-section-block udp-section" style="display:none">' +
            '<div class="block-header">' +
              '<span class="block-title">UDP Sockets</span>' +
              '<span class="block-badge aio-sys-udp-count">0 sockets</span>' +
            '</div>' +
            '<div class="nested-cards-grid aio-sys-udp-container" id="' + id + '-udp-container">' +
            '</div>' +
          '</div>' +

          // File Operations Section (nested under AIO)
          '<div class="aio-section-block file-ops-section" style="display:none">' +
            '<div class="block-header">' +
              '<span class="block-title">File Operations</span>' +
              '<span class="block-badge aio-sys-file-ops-count">0 ops</span>' +
            '</div>' +
            '<div class="nested-cards-grid aio-sys-file-ops-container" id="' + id + '-file-ops-container">' +
            '</div>' +
          '</div>' +

        '</div>' +
      '</article>';

    var temp = document.createElement('div');
    temp.innerHTML = html;
    var panel = temp.firstChild;

    // Store widgets on the panel (will be bound after DOM insertion)
    panel._slabWidgets = widgets;
    panel._widgetsBound = false;

    return panel;
  }

  // Bind widgets after panel is in the document DOM
  function bindAioSystemPanelWidgets(panel) {
    if (panel._widgetsBound || !panel._slabWidgets) return;

    for (var key in panel._slabWidgets) {
      var widget = panel._slabWidgets[key];
      widget.bind();
      // Register SlabWidgets by slabKey, PoolWidgets are accessed directly via panel._slabWidgets
      if (widget.slabKey) {
        PoolWidget.register(widget.slabKey, widget);
      }
    }
    panel._widgetsBound = true;
  }

  function updateAioSystemPanel(panel, sys) {
    var conns = sys.connections || {};
    var sysStats = sys.system || {};
    var queue = sys.queue || {};
    var loopName = sys.name || 'main';

    // Get event loop metrics from modular metrics (registered with loop={name} label)
    var loopLabels = {loop: loopName};
    var counters = currentModular ? currentModular.counters || [] : [];
    var gauges = currentModular ? currentModular.gauges || [] : [];

    // Read current values from modular gauges/counters
    var iterNow = getMetricValue(counters, 'event_loop_iterations', loopLabels);
    var idleNow = getMetricValue(gauges, 'event_loop_idle_us', loopLabels);
    var handlesNow = getMetricValue(gauges, 'event_loop_handles', loopLabels);

    // Track previous values for rate calculation
    var now = Date.now();
    var prev = panel._prevLoop || {};

    // Store current values
    panel._prevLoop = {
      time: now,
      iter: iterNow,
      idle: idleNow
    };

    // Skip calculations on first update or when values are still 0 (not yet populated)
    if (!prev.time || idleNow === 0) {
      var utilFill = panel.querySelector('.aio-sys-util-fill');
      var utilPctEl = panel.querySelector('.aio-sys-util-pct');
      if (utilFill && utilPctEl) {
        utilFill.style.width = '0%';
        utilPctEl.textContent = '--';
      }
      var rateEl = panel.querySelector('.aio-sys-iter-rate');
      if (rateEl) rateEl.textContent = '--';
      var handlesEl = panel.querySelector('.aio-sys-handles');
      if (handlesEl) handlesEl.textContent = handlesNow || '--';
      return;
    }

    // Calculate rates - gauges now sent every 100ms (Prometheus-style)
    var dt = (now - prev.time) / 1000;
    if (dt <= 0) dt = 0.1;

    // Iteration rate
    var iterDelta = iterNow - (prev.iter || 0);
    var iterRate = iterDelta >= 0 ? iterDelta / dt : 0;

    // Utilization from idle time delta
    var idleDelta = idleNow - (prev.idle || 0);
    var dtUs = dt * 1e6;
    var utilPct = 0;
    if (idleDelta >= 0 && idleDelta <= dtUs * 2) {
      // Normal: idle_delta should be close to dt (if ~100% idle, idle_delta ≈ dt)
      utilPct = Math.max(0, Math.min(100, 100 - (idleDelta / dtUs) * 100));
    }
    // If idle_delta is negative (wrap) or huge (first real data), show 0%

    // Update utilization bar and label
    var utilFill = panel.querySelector('.aio-sys-util-fill');
    var utilPctEl = panel.querySelector('.aio-sys-util-pct');
    if (utilFill && utilPctEl) {
      utilFill.style.width = utilPct.toFixed(0) + '%';
      utilPctEl.textContent = utilPct.toFixed(0);
      utilFill.classList.toggle('high', utilPct > 70);
      utilFill.classList.toggle('critical', utilPct > 90);
    }

    // Update iteration rate
    var rateEl = panel.querySelector('.aio-sys-iter-rate');
    if (rateEl) {
      rateEl.textContent = fmtCompact(Math.round(iterRate));
    }

    // Update handles from modular metrics
    var handlesEl = panel.querySelector('.aio-sys-handles');
    if (handlesEl) {
      handlesEl.textContent = handlesNow || sysStats.handles || 0;
    }
    panel.querySelector('.aio-sys-servers').textContent = (sysStats.servers || 0) + ' servers';

    // Animate pulse dots based on activity (iter rate)
    var pulseDots = panel.querySelectorAll('.pulse-dot');
    var activityLevel = Math.min(5, Math.ceil(iterRate / 5)); // 0-5 dots lit based on rate (idle ~10/s)
    for (var i = 0; i < pulseDots.length; i++) {
      pulseDots[i].classList.toggle('active', i < activityLevel);
      // Add staggered animation for visual interest
      if (i < activityLevel && iterRate > 0) {
        pulseDots[i].style.animationDelay = (i * 0.1) + 's';
      }
    }

    // Update queue stats (pending requests + pending responses)
    var pending = (queue.pending_requests || 0) + (queue.pending_responses || 0);
    var capacity = queue.capacity || 1;
    var queuePct = capacity > 0 ? (pending / capacity) * 100 : 0;

    // Update queue in Event Loop section
    var queueEl = panel.querySelector('.aio-sys-queue');
    if (queueEl) {
      queueEl.textContent = pending;
    }
    var queueMetric = panel.querySelector('.queue-metric');
    if (queueMetric) {
      queueMetric.classList.toggle('warning', queuePct > 50);
      queueMetric.classList.toggle('critical', queuePct > 80);
    }

    // Update queue PoolWidget in Resource Pools section
    if (panel._slabWidgets && panel._slabWidgets.queue) {
      panel._slabWidgets.queue.update({
        used: pending,
        total: capacity,
        stats: {
          pending: pending,
          capacity: capacity
        }
      });
    }

    // Update pending streams PoolWidget (streams waiting for arenas)
    var ps = sys.pending_streams || {};
    if (panel._slabWidgets && panel._slabWidgets.pendingStreams) {
      var psCurrent = ps.current || 0;
      var psPoolSize = ps.pool_size || 64;
      var psTotal = ps.total || 0;
      var psProcessed = ps.processed || 0;
      var psDropped = ps.dropped || 0;

      panel._slabWidgets.pendingStreams.update({
        used: psCurrent,
        total: psPoolSize,
        stats: {
          total: fmtCompact(psTotal),
          now: psCurrent,
          processed: fmtCompact(psProcessed),
          dropped: fmtCompact(psDropped)
        }
      });
    }

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
        // Bind widgets now that panel is in the DOM
        bindAioSystemPanelWidgets(panel);
        aioSystemPanels[name] = panel;
      }

      updateAioSystemPanel(panel, sys);
    }

    // Remove panels for systems that no longer exist
    for (var name in aioSystemPanels) {
      if (!seenPanels[name]) {
        var panel = aioSystemPanels[name];
        // Unregister widgets from the global registry
        if (panel._slabWidgets) {
          for (var key in panel._slabWidgets) {
            var widget = panel._slabWidgets[key];
            PoolWidget.unregister(widget.slabKey, widget);
          }
        }
        panel.remove();
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

  // Helper to create circular buffer with last() method
  function createHistoryBuffer(maxSize) {
    return {
      data: [],
      maxSize: maxSize || HISTORY_SAMPLES,
      push: function(value) {
        this.data.push(value);
        if (this.data.length > this.maxSize) {
          this.data.shift();
        }
      },
      toArray: function() {
        return this.data.slice();
      },
      last: function() {
        return this.data[this.data.length - 1];
      },
      slice: function(start, end) {
        return this.data.slice(start, end);
      }
    };
  }

  function getServerHistory(key) {
    if (!serverHistory[key]) {
      serverHistory[key] = {
        bytesIn: createHistoryBuffer(HISTORY_SAMPLES),
        bytesOut: createHistoryBuffer(HISTORY_SAMPLES),
        prevBytesIn: 0,
        prevBytesOut: 0,
        prevSseBytes: 0,  // Track SSE bytes separately for throughput
        statusCodes: createHistoryBuffer(HISTORY_SAMPLES),
        p50: createHistoryBuffer(HISTORY_SAMPLES),
        p95: createHistoryBuffer(HISTORY_SAMPLES),
        p99: createHistoryBuffer(HISTORY_SAMPLES),
        reqRate: createHistoryBuffer(HISTORY_SAMPLES),
        conns: createHistoryBuffer(HISTORY_SAMPLES),
        sse: createHistoryBuffer(HISTORY_SAMPLES)
      };
    }
    return serverHistory[key];
  }

  function createServerCard(serverInfo) {
    var card = document.createElement('article');
    var cardId = 'server-' + serverInfo.key.replace(/[:.]/g, '-');

    // Check localStorage for saved collapse state (default to collapsed)
    var isCollapsed = window.getEntityCardCollapsed ? window.getEntityCardCollapsed(cardId) : true;

    card.className = 'entity-card' + (isCollapsed ? ' collapsed' : '');
    card.id = cardId;
    card.setAttribute('tabindex', '0');
    card.setAttribute('role', 'article');
    card.setAttribute('aria-expanded', isCollapsed ? 'false' : 'true');

    card.innerHTML = `
      <div class="entity-header">
        <div class="entity-status ok"></div>
        <h3 class="entity-name">${serverInfo.server}:${serverInfo.port}</h3>
        <div class="entity-label">HTTP</div>
        <div class="entity-header-metrics">
          <div class="header-metric-item" title="Request rate">
            <div class="header-metric-spark req-rate-spark"></div>
            <span class="header-metric-value req-rate">--</span>
            <span class="header-metric-unit">/s</span>
          </div>
          <div class="header-metric-item" title="P99 latency">
            <div class="header-metric-spark latency-spark"></div>
            <span class="header-metric-value p99-header">--</span>
            <span class="header-metric-unit">ms</span>
          </div>
          <div class="header-metric-item success-metric" title="Success rate">
            <span class="header-metric-value success-rate">100</span>
            <span class="header-metric-unit">%</span>
          </div>
        </div>
        <button class="expand-toggle" onclick="toggleEntityCard(this.closest('.entity-card'))" aria-label="Toggle details"><span class="expand-icon">${isCollapsed ? '▼' : '▲'}</span></button>
      </div>
      <div class="entity-body">
        <!-- Metrics Grid -->
        <div class="server-metrics-grid">
          <!-- Response Codes Section -->
          <div class="metric-panel response-codes-panel">
            <div class="metric-panel-header">
              <span class="metric-panel-title">Response Codes</span>
              <div class="code-chips">
                <span class="code-chip s2xx"><span class="count-2xx">0</span></span>
                <span class="code-chip s4xx"><span class="count-4xx">0</span></span>
                <span class="code-chip s5xx"><span class="count-5xx">0</span></span>
              </div>
            </div>
            <div class="metric-panel-body">
              <div class="status-code-spark-large"></div>
              <div class="status-bar-large">
                <div class="status-segment s2xx" style="width: 100%"></div>
                <div class="status-segment s4xx" style="width: 0%"></div>
                <div class="status-segment s5xx" style="width: 0%"></div>
              </div>
            </div>
          </div>
          <!-- Latency Section -->
          <div class="metric-panel latency-panel">
            <div class="metric-panel-header">
              <span class="metric-panel-title">Latency</span>
              <div class="latency-chips">
                <span class="latency-chip p50"><span class="label">p50</span><span class="value p50-value">--</span></span>
                <span class="latency-chip p95"><span class="label">p95</span><span class="value p95-value">--</span></span>
                <span class="latency-chip p99"><span class="label">p99</span><span class="value p99-value">--</span></span>
              </div>
            </div>
            <div class="metric-panel-body">
              <div class="latency-trend-spark-large"></div>
            </div>
          </div>
          <!-- Throughput Section -->
          <div class="metric-panel throughput-panel">
            <div class="metric-panel-header">
              <span class="metric-panel-title">Throughput</span>
              <div class="throughput-stats">
                <span class="throughput-stat in"><span class="arrow">↓</span><span class="value bytes-in-rate">0 B/s</span></span>
                <span class="throughput-stat out"><span class="arrow">↑</span><span class="value bytes-out-rate">0 B/s</span></span>
              </div>
            </div>
            <div class="metric-panel-body">
              <div class="throughput-spark-large"></div>
            </div>
          </div>
          <!-- Concurrency Section -->
          <div class="metric-panel concurrency-panel">
            <div class="metric-panel-header">
              <span class="metric-panel-title">Concurrency</span>
              <div class="concurrency-stats">
                <span class="concurrency-stat conns"><span class="value active-conns">0</span><span class="label">conns</span></span>
                <span class="concurrency-stat sse"><span class="value sse-streams">0</span><span class="label">sse</span></span>
              </div>
            </div>
            <div class="metric-panel-body">
              <div class="concurrency-spark-large"></div>
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

  function renderServerHistogramMini(container, histogram) {
    if (!container) return;
    if (!histogram || histogram.length === 0) {
      container.innerHTML = '';
      return;
    }

    var max = Math.max.apply(null, histogram.map(function(b) { return b.count; }));
    if (max === 0) max = 1;

    // Render 8 condensed bars
    var numBars = 8;
    var step = Math.ceil(histogram.length / numBars);
    var bars = [];

    for (var i = 0; i < numBars; i++) {
      var startIdx = i * step;
      var endIdx = Math.min(startIdx + step, histogram.length);
      var sum = 0;
      for (var j = startIdx; j < endIdx; j++) {
        sum += histogram[j].count;
      }
      var pct = (sum / max) * 100;
      var pClass = '';
      // Mark bars based on position (approximating p50/p95/p99)
      if (i === 2) pClass = 'p50';
      else if (i === 5) pClass = 'p95';
      else if (i === 7) pClass = 'p99';
      bars.push('<div class="bar ' + pClass + '" style="height: ' + Math.max(pct, 10) + '%"></div>');
    }

    container.innerHTML = bars.join('');
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
    var sseStreams = getMetricValue(gauges, 'http_sse_streams_active', {});

    // Calculate request rate
    var prevTotal = card.dataset.prevReqTotal ? parseInt(card.dataset.prevReqTotal) : 0;
    var reqRate = deltaSeconds > 0 ? (reqTotal - prevTotal) / deltaSeconds : 0;
    card.dataset.prevReqTotal = reqTotal;

    // Get history buffers
    var hist = getServerHistory(serverInfo.key);

    // Track request rate history
    hist.reqRate.push(reqRate);

    // Track concurrency history
    hist.conns.push(activeConns);
    hist.sse.push(sseStreams);

    // Find latency histogram
    var latencyHist = findMetric(histograms, 'http_request_duration_seconds', {});

    // Update percentile values (estimated from histogram if available)
    var p50 = 0, p95 = 0, p99 = 0;
    if (latencyHist && latencyHist.buckets && latencyHist.count > 0) {
      var buckets = latencyHist.buckets;
      p50 = estimatePercentile(buckets, latencyHist.count, 0.50);
      p95 = estimatePercentile(buckets, latencyHist.count, 0.95);
      p99 = estimatePercentile(buckets, latencyHist.count, 0.99);
    }

    // Track latency history for trend sparkline (convert to ms)
    hist.p50.push((p50 || 0) * 1000);
    hist.p95.push((p95 || 0) * 1000);
    hist.p99.push((p99 || 0) * 1000);

    // Calculate rates
    var successRate = reqTotal > 0 ? ((req2xx / reqTotal) * 100) : 100;
    var errorRate = reqTotal > 0 ? ((req4xx + req5xx) / reqTotal) * 100 : 0;

    // ========== Header Updates ==========
    // Update request rate in header
    var reqRateEl = card.querySelector('.entity-header-metrics .req-rate');
    if (reqRateEl) reqRateEl.textContent = fmt(reqRate, 1);

    // Update P99 in header (convert to ms)
    var p99HeaderEl = card.querySelector('.p99-header');
    if (p99HeaderEl) p99HeaderEl.textContent = fmt(p99 * 1000, 1);

    // Update success rate in header
    var successEl = card.querySelector('.entity-header-metrics .success-rate');
    if (successEl) {
      successEl.textContent = successRate.toFixed(0);
      var successMetric = successEl.closest('.success-metric');
      if (successMetric) {
        successMetric.classList.remove('ok', 'warning', 'error');
        if (successRate >= 99) successMetric.classList.add('ok');
        else if (successRate >= 95) successMetric.classList.add('warning');
        else successMetric.classList.add('error');
      }
    }

    // Render header sparklines (padded to fixed size for stable display)
    var reqRateSpark = card.querySelector('.req-rate-spark');
    if (reqRateSpark && hist.reqRate.data.length >= 1) {
      renderMiniSparkline(reqRateSpark, padSparklineData(hist.reqRate.toArray(), 20), {
        color: 'var(--color-info)',
        width: 40,
        height: 14
      });
    }

    var latencySpark = card.querySelector('.latency-spark');
    if (latencySpark && hist.p99.data.length >= 1) {
      renderMiniSparkline(latencySpark, padSparklineData(hist.p99.toArray(), 20), {
        color: 'var(--color-warning)',
        width: 40,
        height: 14
      });
    }

    // Update entity status based on error rate
    var statusEl = card.querySelector('.entity-status');
    statusEl.className = 'entity-status';
    if (errorRate > 5) {
      statusEl.classList.add('error');
    } else if (errorRate > 1) {
      statusEl.classList.add('warning');
    } else {
      statusEl.classList.add('ok');
    }

    // ========== Body Updates ==========
    // Update status code chips
    var count2xxEl = card.querySelector('.count-2xx');
    var count4xxEl = card.querySelector('.count-4xx');
    var count5xxEl = card.querySelector('.count-5xx');
    if (count2xxEl) count2xxEl.textContent = fmtCompact(req2xx);
    if (count4xxEl) count4xxEl.textContent = fmtCompact(req4xx);
    if (count5xxEl) count5xxEl.textContent = fmtCompact(req5xx);

    // Update status bar segments
    var total = Math.max(reqTotal, 1);
    var seg2xx = card.querySelector('.status-bar-large .status-segment.s2xx');
    var seg4xx = card.querySelector('.status-bar-large .status-segment.s4xx');
    var seg5xx = card.querySelector('.status-bar-large .status-segment.s5xx');
    if (seg2xx) seg2xx.style.width = ((req2xx / total) * 100) + '%';
    if (seg4xx) seg4xx.style.width = ((req4xx / total) * 100) + '%';
    if (seg5xx) seg5xx.style.width = ((req5xx / total) * 100) + '%';

    // Track status code history for sparkline
    var prev = hist.statusCodes.last() || { s2xx: 0, s4xx: 0, s5xx: 0, total2xx: 0, total4xx: 0, total5xx: 0 };
    var delta2xx = req2xx - (prev.total2xx || 0);
    var delta4xx = req4xx - (prev.total4xx || 0);
    var delta5xx = req5xx - (prev.total5xx || 0);

    hist.statusCodes.push({
      s2xx: Math.max(0, delta2xx),
      s4xx: Math.max(0, delta4xx),
      s5xx: Math.max(0, delta5xx),
      total2xx: req2xx,
      total4xx: req4xx,
      total5xx: req5xx
    });

    // Render large status code sparkline (pad to fixed size to match throughput alignment)
    var statusSparkLarge = card.querySelector('.status-code-spark-large');
    if (statusSparkLarge && hist.statusCodes.data.length >= 1) {
      renderStatusCodeSparkline(statusSparkLarge, padStatusCodeData(hist.statusCodes.toArray()), {
        width: 160,
        height: 32
      });
    }

    // Update latency percentile chips
    var p50El = card.querySelector('.p50-value');
    var p95El = card.querySelector('.p95-value');
    var p99El = card.querySelector('.p99-value');
    if (p50El) p50El.textContent = fmtLatency(p50);
    if (p95El) p95El.textContent = fmtLatency(p95);
    if (p99El) p99El.textContent = fmtLatency(p99);

    // Render large latency trend sparkline (padded to fixed size to avoid zoom-out effect)
    var latencyTrendLarge = card.querySelector('.latency-trend-spark-large');
    if (latencyTrendLarge && hist.p50.data.length >= 1) {
      renderPercentileSparkline(latencyTrendLarge, hist, { width: 160, height: 40 });
    }

    // Update throughput (including SSE bytes in outbound for servers with active SSE)
    var bytesInRate = deltaSeconds > 0 ? (bytesRecv - hist.prevBytesIn) / deltaSeconds : 0;
    var bytesOutRate = deltaSeconds > 0 ? (bytesSent - hist.prevBytesOut) / deltaSeconds : 0;

    // Add SSE bytes only to servers with active SSE streams (avoids double-counting)
    if (sseStreams > 0 && currentSseMetrics) {
      var sseBytes = currentSseMetrics.bytes_pushed_total || 0;
      var sseBytesRate = deltaSeconds > 0 ? (sseBytes - hist.prevSseBytes) / deltaSeconds : 0;
      if (sseBytesRate > 0) {
        bytesOutRate += sseBytesRate;
      }
      hist.prevSseBytes = sseBytes;
    }

    // Only record positive rates
    if (bytesInRate >= 0) hist.bytesIn.push(bytesInRate);
    if (bytesOutRate >= 0) hist.bytesOut.push(bytesOutRate);

    hist.prevBytesIn = bytesRecv;
    hist.prevBytesOut = bytesSent;

    // Update throughput labels
    var inRateEl = card.querySelector('.bytes-in-rate');
    var outRateEl = card.querySelector('.bytes-out-rate');
    if (inRateEl) inRateEl.textContent = fmtRate(Math.max(0, bytesInRate));
    if (outRateEl) outRateEl.textContent = fmtRate(Math.max(0, bytesOutRate));

    // Render throughput sparkline (pad to fixed size to avoid zoom-out effect)
    var throughputSparkLarge = card.querySelector('.throughput-spark-large');
    if (throughputSparkLarge && hist.bytesIn.data.length >= 1) {
      renderThroughputSparkline(throughputSparkLarge,
        padSparklineData(hist.bytesIn.toArray()),
        padSparklineData(hist.bytesOut.toArray()), {
        width: 160,
        height: 32
      });
    }

    // Update concurrency stats
    var connsEl = card.querySelector('.concurrency-stats .active-conns');
    var sseEl = card.querySelector('.concurrency-stats .sse-streams');
    if (connsEl) connsEl.textContent = activeConns;
    if (sseEl) sseEl.textContent = sseStreams;

    // Show/hide SSE stat based on whether there are active streams
    var sseStat = card.querySelector('.concurrency-stat.sse');
    if (sseStat) {
      sseStat.style.display = sseStreams > 0 ? '' : 'none';
    }

    // Render concurrency sparkline (pad to fixed size to avoid zoom-out effect)
    var concurrencySparkLarge = card.querySelector('.concurrency-spark-large');
    if (concurrencySparkLarge && hist.conns.data.length >= 1) {
      renderConcurrencySparkline(concurrencySparkLarge,
        padSparklineData(hist.conns.toArray()),
        padSparklineData(hist.sse.toArray()), {
        width: 160,
        height: 32
      });
    }
  }

  // Render throughput sparkline (dual line: in/out)
  function renderThroughputSparkline(container, bytesIn, bytesOut, options) {
    if (!container || !bytesIn || bytesIn.length < 2) return;
    var opts = options || {};
    var series = [
      { data: bytesIn, color: 'ok', fill: 0.15 }
    ];
    if (bytesOut && bytesOut.length >= 2) {
      series.push({ data: bytesOut, color: 'info', dash: [3, 2] });
    }
    renderLineSparkline(container, series, { height: opts.height || 32 });
  }

  // Render concurrency sparkline (connections + SSE)
  function renderConcurrencySparkline(container, conns, sse, options) {
    if (!container || !conns || conns.length < 2) return;
    var opts = options || {};
    var series = [
      { data: conns, color: 'purple', fill: 0.3 }
    ];
    var hasSSE = sse && sse.some(function(v) { return v > 0; });
    if (hasSSE) {
      series.push({ data: sse, color: 'cyan', fill: 0.3 });
    }
    renderLineSparkline(container, series, { height: opts.height || 32 });
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

    // Return last non-Inf bucket if not found (this means all data is in +Inf)
    for (var i = buckets.length - 1; i >= 0; i--) {
      if (buckets[i].le !== '+Inf') {
        return parseFloat(buckets[i].le);
      }
    }
    return 0;
  }

  function updateAggregateHealth(servers) {
    var okCount = 0;
    var warnCount = 0;
    var errorCount = 0;
    var totalOps = 0;
    var totalReq2xx = 0;
    var totalReq4xx = 0;
    var totalReq5xx = 0;
    var maxP99 = 0;

    var serverKeys = Object.keys(servers);

    serverKeys.forEach(function(key) {
      var srv = servers[key];

      var req2xx = getMetricValue(srv.counters, 'http_requests_total', {status: '2xx'});
      var req4xx = getMetricValue(srv.counters, 'http_requests_total', {status: '4xx'});
      var req5xx = getMetricValue(srv.counters, 'http_requests_total', {status: '5xx'});
      var reqTotal = req2xx + req4xx + req5xx;

      var errorRate = reqTotal > 0 ? ((req4xx + req5xx) / reqTotal) * 100 : 0;

      if (errorRate > 5) {
        errorCount++;
      } else if (errorRate > 1) {
        warnCount++;
      } else {
        okCount++;
      }

      totalReq2xx += req2xx;
      totalReq4xx += req4xx;
      totalReq5xx += req5xx;

      var hist = findMetric(srv.histograms, 'http_request_duration_seconds', {});
      if (hist && hist.p99_us) {
        var p99Ms = hist.p99_us / 1000;
        maxP99 = Math.max(maxP99, p99Ms);
      }
    });

    totalOps = totalReq2xx + totalReq4xx + totalReq5xx;
    var aggregateErrorRate = totalOps > 0 ? ((totalReq4xx + totalReq5xx) / totalOps) * 100 : 0;

    $('aio-ok-count').textContent = okCount;
    $('aio-warn-count').textContent = warnCount;
    $('aio-error-count').textContent = errorCount;
    $('aio-total-ops').textContent = fmtCompact(totalOps);
    $('aio-error-rate').textContent = aggregateErrorRate.toFixed(2);
    $('aio-p99').textContent = maxP99 > 0 ? fmt(maxP99, 1) : '0';
  }

  function renderHttpServers(servers, deltaSeconds) {
    var serverKeys = Object.keys(servers);

    // Group servers by their owning AIO system (loop label)
    var serversByLoop = {};
    serverKeys.forEach(function(key) {
      var srv = servers[key];
      var loop = srv.loop || 'main';
      if (!serversByLoop[loop]) {
        serversByLoop[loop] = {};
      }
      serversByLoop[loop][key] = srv;
    });

    // Track which loops have servers for "no servers" placeholder visibility
    var loopsWithServers = Object.keys(serversByLoop);

    // Iterate through each AIO system panel and render its servers
    for (var loopName in aioSystemPanels) {
      var panel = aioSystemPanels[loopName];
      var container = panel.querySelector('.aio-sys-servers-container');
      if (!container) continue;

      var loopServers = serversByLoop[loopName] || {};
      var loopServerKeys = Object.keys(loopServers);

      // Show/hide entire section based on server count
      var serversSection = panel.querySelector('.http-servers-section');
      if (serversSection) {
        serversSection.style.display = loopServerKeys.length > 0 ? '' : 'none';
      }

      // Update or create server cards for this loop
      loopServerKeys.forEach(function(key) {
        var serverInfo = loopServers[key];

        if (!serverCards[key]) {
          serverCards[key] = createServerCard(serverInfo);
          container.appendChild(serverCards[key]);
        } else if (serverCards[key].parentNode !== container) {
          // Card exists but in wrong container, move it
          container.appendChild(serverCards[key]);
        }

        updateServerCard(serverCards[key], serverInfo, deltaSeconds);
      });

      // Update AIO panel badges for server count and rate
      var serverCountBadge = panel.querySelector('.aio-sys-servers-count');
      var serverRateBadge = panel.querySelector('.aio-sys-servers-rate');
      var panelServersBadge = panel.querySelector('.aio-sys-servers');

      if (serverCountBadge) {
        serverCountBadge.textContent = loopServerKeys.length + ' server' + (loopServerKeys.length !== 1 ? 's' : '');
      }
      if (panelServersBadge) {
        panelServersBadge.textContent = loopServerKeys.length + ' servers';
      }

      // Calculate total request rate for this loop's servers
      var totalRate = 0;
      loopServerKeys.forEach(function(key) {
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

    // Remove cards for servers that no longer exist
    for (var key in serverCards) {
      if (!servers[key]) {
        if (serverCards[key].parentNode) {
          serverCards[key].parentNode.removeChild(serverCards[key]);
        }
        delete serverCards[key];
      }
    }

    // Update global section badges
    var globalCountBadge = $('http-servers-count');
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

    // Store modular for access by other update functions
    currentModular = mod;
    currentSseMetrics = data.sse_metrics || null;

    var gc = vm.gc || {};
    var interp = vm.interpreter || {};
    var sys = aio.system || {};
    var conns = aio.connections || {};

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
        totalLatencySum += hist.sum_us || 0;
        totalLatencyCount += hist.count || 0;
      }
    });
    // sum_us is in microseconds, convert to milliseconds
    var avgLatency = totalLatencyCount > 0 ? (totalLatencySum / totalLatencyCount) / 1000 : 0;
    pushHistory(history.latency, avgLatency);

    // Heap usage
    var heapUsed = gc.heap_used_bytes || 0;
    var heapTotal = gc.heap_total_bytes || 1;
    var heapPct = (heapUsed / heapTotal) * 100;
    pushHistory(history.heapUsage, heapPct);

    // Update compact health bar
    $('health-request-rate').textContent = fmt(requestRate, 1);
    $('health-error-rate').textContent = fmt(errorRate, 1);
    $('health-avg-latency').textContent = fmt(avgLatency, 1);
    $('health-heap-pct').textContent = fmt(heapPct, 0);

    // Render mini sparklines (padded to fixed size for stable display)
    renderMiniSparklineLegacy('spark-request-rate', padSparklineData(history.requestRate, 20), 'var(--color-info)');
    renderMiniSparklineLegacy('spark-error-rate', padSparklineData(history.errorRate, 20), 'var(--color-warning)');
    renderMiniSparklineLegacy('spark-latency', padSparklineData(history.latency, 20), 'var(--color-cyan)');
    renderMiniSparklineLegacy('spark-heap', padSparklineData(history.heapUsage, 20), 'var(--color-ok)');

    // Update health metric value colors based on thresholds
    function updateHealthMetricColor(el, value, warningThreshold, criticalThreshold) {
      if (!el) return;
      el.classList.remove('ok', 'warning', 'critical');
      if (value > criticalThreshold) el.classList.add('critical');
      else if (value > warningThreshold) el.classList.add('warning');
      else el.classList.add('ok');
    }

    updateHealthMetricColor($('health-error-rate'), errorRate, 1, 5);
    updateHealthMetricColor($('health-heap-pct'), heapPct, 70, 90);
    updateHealthMetricColor($('health-avg-latency'), avgLatency, 100, 500);

    // ========== VM Section Badges ==========
    $('vm-gc-badge').textContent = fmtCompact(gc.cycles_total || 0) + ' cycles';
    $('vm-heap-badge').textContent = fmtBytes(heapUsed) + ' heap';

    // ========== GC Panel ==========
    $('gc-cycles-badge').textContent = fmtCompact(gc.cycles_total || 0) + ' cycles';
    $('gc-cycles').textContent = fmtCompact(gc.cycles_total || 0);
    $('gc-max-pause').innerHTML = fmt((gc.pause_us_max || 0) / 1000, 1) + '<span class="unit">ms</span>';
    $('gc-avg-pause').innerHTML = fmt(gc.pause_ms_avg || 0, 2) + '<span class="unit">ms</span>';
    $('gc-reclaimed').innerHTML = fmtBytes(gc.reclaimed_bytes_total || 0).replace(' ', '<span class="unit">') + '</span>';

    // Update GC+Interpreter panel summary (for collapsed state)
    var gcSummary = $('gc-summary');
    if (gcSummary) {
      gcSummary.textContent = fmtCompact(gc.cycles_total || 0) + ' cycles, ' +
        fmtCompact(interp.evals_total || 0) + ' evals';
    }

    // Track GC pauses for timeline
    if (prevMetrics && gc.cycles_total > prevMetrics.gcCycles) {
      var pauseMs = (gc.pause_us_max || 0) / 1000;
      history.gcPauses.push({ pause: pauseMs, timestamp: now });
      while (history.gcPauses.length > HISTORY_SAMPLES) history.gcPauses.shift();
    }
    renderGcTimeline(history.gcPauses);

    // Track allocation and reclaim rates
    var allocBytesTotal = gc.allocated_bytes_total || 0;
    var reclaimBytesTotal = gc.reclaimed_bytes_total || 0;
    if (prevMetrics) {
      var prevAlloc = prevMetrics.allocBytesTotal || 0;
      var prevReclaim = prevMetrics.reclaimBytesTotal || 0;
      var allocRate = calculateRate(allocBytesTotal, prevAlloc, deltaSeconds);
      var reclaimRate = calculateRate(reclaimBytesTotal, prevReclaim, deltaSeconds);
      pushHistory(history.allocRate, allocRate);
      pushHistory(history.reclaimRate, reclaimRate);
    }

    // ========== Interpreter Stats (integrated into GC panel) ==========
    var evalsTotal = interp.evals_total || 0;
    var fnCalls = interp.function_calls || 0;
    var builtinCalls = interp.builtin_calls || 0;

    $('interp-evals').textContent = fmtCompact(evalsTotal);
    $('interp-fn-calls').textContent = fmtCompact(fnCalls);
    $('interp-builtins').textContent = fmtCompact(builtinCalls);
    $('interp-stack-depth').textContent = interp.stack_depth_max || 0;

    // Calculate interpreter rates
    var evalRate = 0;
    if (prevMetrics && deltaSeconds > 0) {
      var prevEvals = prevMetrics.evalsTotal || 0;
      evalRate = calculateRate(evalsTotal, prevEvals, deltaSeconds);
      pushHistory(history.evalRate, evalRate);
    }

    // Update eval rate display
    var evalRateEl = $('interp-eval-rate');
    if (evalRateEl) {
      evalRateEl.textContent = fmtCompact(Math.round(evalRate));
    }

    // Render eval rate sparkline
    var evalSparkContainer = $('interp-eval-spark');
    if (evalSparkContainer && history.evalRate.length >= 2) {
      renderMiniSparkline(evalSparkContainer, padSparklineData(history.evalRate, 20), {
        color: 'var(--color-warning)',
        height: 24,
        width: 48
      });
    }

    // ========== AIO Systems Section ==========
    // Use the new aio_systems array for multi-system support
    var aioSystems = data.aio_systems || [];
    // Fallback: if aio_systems is empty but we have aio_metrics, create a system from it
    // Note: event_loop metrics come from modular metrics (loop={name} label)
    if (aioSystems.length === 0 && aio.system) {
      aioSystems = [{
        name: 'main',
        uptime_seconds: aio.uptime_seconds || 0,
        system: sys,
        connections: conns,
        queue: aio.queue || {}
      }];
    }
    renderAioSystems(aioSystems);

    // ========== Aggregate Health Bar ==========
    updateAggregateHealth(servers);

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
      allocBytesTotal: gc.allocated_bytes_total || 0,
      reclaimBytesTotal: gc.reclaimed_bytes_total || 0,
      evalsTotal: evalsTotal,
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
    var statusIndicator = $('global-status');
    if (!statusIndicator) return;

    if (connected) {
      statusIndicator.classList.remove('error');
      statusIndicator.title = 'Connected';
    } else {
      statusIndicator.classList.add('error');
      statusIndicator.title = 'Disconnected';
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

  // Global PoolWidget references for memory visualizations
  var arenaGauges = {};  // Map of arena name -> PoolWidget
  var heapTierGauge = null;  // Single heap tier for parallel GC

  function init() {
    showLoadingState();

    // Initialize PoolWidgets for memory visualization (includes LVAL grid in slab tier)
    initPoolWidgets();
  }

  // Initialize PoolWidgets for GC heap tiers (arenas are created dynamically)
  function initPoolWidgets() {
    // Heap tier gauge removed - now only using the GC panel heap pressure display
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
      this.isClosing = false;  // Flag to suppress errors during page unload

      // DOM references
      this.grids = {};
      this.arenaGauges = {};

      // State for delta detection (UI animation)
      this.previousState = {};

      // Full state storage for delta merging
      // Server sends full state on connect, then deltas only
      this.fullState = {
        memory: null,
        metrics: null,
        platform: null  // 'darwin', 'linux', 'windows', or 'unknown'
      };

      // RSS history for trend sparkline (cross-platform memory signal)
      this.rssHistory = createHistoryBuffer(HISTORY_SAMPLES);

      // Expanded slab states (decoded RLE) for delta application
      this.slabStates = {};  // keyed by slab name

      // Owner map for server/client names (indexed by owner_idx)
      this.ownerMap = [];

      // Fresh state endpoint for initial HTTP fetch
      this.freshStateUrl = '/debug/metrics/state';
    }

    fetchFreshState() {
      var self = this;
      return fetch(this.freshStateUrl)
        .then(function(response) {
          if (!response.ok) throw new Error('HTTP ' + response.status);
          return response.json();
        })
        .then(function(data) {
          // Store as full state
          self.fullState = {
            memory: data.memory,
            metrics: data.metrics,
            platform: data.platform || null
          };

          // Expand and store slab states
          if (data.memory && data.memory.slabs) {
            data.memory.slabs.forEach(function(slab) {
              if (slab.states) {
                self.slabStates[slab.name] = decodeRLE(slab.states);
              }
            });
          }

          // Render initial state - metrics first, then memory
          if (data.metrics) {
            self.handleMetricsUpdate(data.metrics);
          }
          if (data.memory) {
            self.handleMemoryUpdate(data.memory);
          }

          return true;
        })
        .catch(function() {
          return false;
        });
    }

    connect() {
      var self = this;

      // Fetch fresh state FIRST, then connect SSE
      this.fetchFreshState().then(function() {
        // Connect SSE for updates (whether fresh state succeeded or not)
        var url = '/debug/diagnostics/memory';
        self.eventSource = new EventSource(url);

        // Listen for full diagnostics event (sent on initial connect)
        // Still needed for backwards compatibility or if fresh state fetch failed
        self.eventSource.addEventListener('diagnostics', function(e) {
          self.lastEventId = e.lastEventId;
          var data = JSON.parse(e.data);

          // Store platform for cross-platform UI adaptation
          if (data.platform) {
            self.fullState.platform = data.platform;
          }

          // Store full state
          if (data.memory) {
            self.fullState.memory = data.memory;
            // Expand and store slab states for delta tracking
            if (data.memory.slabs) {
              data.memory.slabs.forEach(function(slab) {
                if (slab.states) {
                  self.slabStates[slab.name] = decodeRLE(slab.states);
                }
              });
            }
          }

          // Handle metrics FIRST to create AIO panels before memory update
          // tries to find slab grid elements
          if (data.metrics) {
            self.fullState.metrics = data.metrics;
            self.handleMetricsUpdate(data.metrics);
          }

          // Now update memory/slabs - panels should exist from metrics update
          if (data.memory) {
            self.handleMemoryUpdate(data.memory);
          }
        });

        // Listen for delta diagnostics events (sent after first full event)
        self.eventSource.addEventListener('diagnostics-delta', function(e) {
          self.lastEventId = e.lastEventId;
          var delta = JSON.parse(e.data);
          self.applyDelta(delta);
        });

        // Also listen for legacy 'memory' event for backwards compatibility
        self.eventSource.addEventListener('memory', function(e) {
          self.lastEventId = e.lastEventId;
          self.handleMemoryUpdate(JSON.parse(e.data));
        });

        self.eventSource.onopen = function() {
          var wasReconnect = self.reconnectAttempts > 0;
          self.reconnectAttempts = 0;
          self.updateConnectionStatus(true);

          // On reconnect, always fetch fresh state from server
          // Server may have restarted with new state, and our cached state would be stale
          if (wasReconnect) {
            // Clear old state before fetching fresh
            self.fullState = {};
            self.slabStates = {};
            self.fetchFreshState();
          } else if (!self.fullState.memory || !self.fullState.metrics) {
            // Initial connect but fetchFreshState failed - try again
            self.fetchFreshState();
          }
        };

        self.eventSource.onerror = function(e) {
          if (self.isClosing) return;

          self.updateConnectionStatus(false);
          if (self.eventSource.readyState === EventSource.CLOSED) {
            self.scheduleReconnect();
          }
        };
      });
    }

    // Apply delta update to stored full state
    applyDelta(delta) {
      // Handle heartbeat events - these have no changes but should still advance graphs
      if (delta.heartbeat) {
        // Trigger UI updates with existing state to advance time series
        if (this.fullState.metrics) {
          this.handleMetricsUpdate(this.fullState.metrics);
        }
        if (this.fullState.memory) {
          this.handleMemoryUpdate(this.fullState.memory);
        }
        return;
      }

      if (!this.fullState.memory && delta.memory) {
        // No full state yet, can't apply delta - request reconnect
        this.scheduleReconnect();
        return;
      }

      var memoryUpdated = false;
      var metricsUpdated = false;

      // Apply memory deltas
      if (delta.memory && this.fullState.memory) {
        var mem = this.fullState.memory;

        // Apply slab deltas
        if (delta.memory.slabs) {
          delta.memory.slabs.forEach(function(deltaSlab) {
            // Find matching slab in full state
            var fullSlab = null;
            for (var i = 0; i < mem.slabs.length; i++) {
              if (mem.slabs[i].name === deltaSlab.name) {
                fullSlab = mem.slabs[i];
                break;
              }
            }
            if (!fullSlab) return;

            // Update used count
            if (deltaSlab.used !== undefined) {
              fullSlab.used = deltaSlab.used;
            }

            // Update HWM (high water mark)
            if (deltaSlab.hwm !== undefined) {
              fullSlab.hwm = deltaSlab.hwm;
            }

            // Apply delta_states to stored expanded state
            if (deltaSlab.delta_states && this.slabStates[deltaSlab.name]) {
              this.slabStates[deltaSlab.name] = applyDeltaStates(
                this.slabStates[deltaSlab.name],
                deltaSlab.delta_states
              );
              // Re-encode to RLE for the UI (or pass expanded directly)
              // For simplicity, store as expanded and let render use it
              fullSlab.states = this.slabStates[deltaSlab.name];
              fullSlab._statesExpanded = true;  // Flag to skip decoding
            }

            // Update bitmap if provided (full bitmap, already RLE)
            if (deltaSlab.bitmap !== undefined) {
              fullSlab.bitmap = deltaSlab.bitmap;
            }

            // Update summary stats
            if (deltaSlab.summary) {
              fullSlab.summary = deltaSlab.summary;
            }

            // Update by_type (handle type breakdown)
            if (deltaSlab.by_type) {
              fullSlab.by_type = deltaSlab.by_type;
            }
          }, this);
        }

        // Apply arena deltas
        if (delta.memory.arenas) {
          delta.memory.arenas.forEach(function(deltaArena) {
            var fullArena = null;
            for (var i = 0; i < mem.arenas.length; i++) {
              if (mem.arenas[i].name === deltaArena.name) {
                fullArena = mem.arenas[i];
                break;
              }
            }
            if (fullArena && deltaArena.used !== undefined) {
              fullArena.used = deltaArena.used;
            }
          });
        }

        // Apply GC deltas
        if (delta.memory.gc) {
          if (!mem.gc) mem.gc = {};
          Object.assign(mem.gc, delta.memory.gc);
        }

        memoryUpdated = true;
      }

      // Apply metrics deltas
      if (delta.metrics && this.fullState.metrics) {
        var metrics = this.fullState.metrics;

        // Apply VM metrics (GC stats) - these are absolute values
        if (delta.metrics.vm) {
          if (!metrics.vm) metrics.vm = {};
          if (delta.metrics.vm.gc) {
            if (!metrics.vm.gc) metrics.vm.gc = {};
            Object.assign(metrics.vm.gc, delta.metrics.vm.gc);
          }
        }

        if (delta.metrics.aio) {
          if (!metrics.aio) metrics.aio = {};

          // Apply byte deltas (accumulate)
          if (delta.metrics.aio.bytes) {
            if (!metrics.aio.bytes) metrics.aio.bytes = { sent: 0, recv: 0 };
            if (delta.metrics.aio.bytes.d_sent) {
              metrics.aio.bytes.sent = (metrics.aio.bytes.sent || 0) + delta.metrics.aio.bytes.d_sent;
            }
            if (delta.metrics.aio.bytes.d_recv) {
              metrics.aio.bytes.recv = (metrics.aio.bytes.recv || 0) + delta.metrics.aio.bytes.d_recv;
            }
          }

          // Apply request deltas
          if (delta.metrics.aio.requests) {
            if (!metrics.aio.requests) metrics.aio.requests = { total: 0 };
            if (delta.metrics.aio.requests.d_total) {
              metrics.aio.requests.total = (metrics.aio.requests.total || 0) + delta.metrics.aio.requests.d_total;
            }
          }

          // Connection counts are absolute (gauges)
          if (delta.metrics.aio.connections) {
            if (!metrics.aio.connections) metrics.aio.connections = {};
            Object.assign(metrics.aio.connections, delta.metrics.aio.connections);
          }

          // Pending streams metrics (current is absolute, others are deltas)
          if (delta.metrics.aio.pending_streams) {
            if (!metrics.aio.pending_streams) {
              metrics.aio.pending_streams = { current: 0, total: 0, processed: 0, dropped: 0, pool_size: 64 };
            }
            var ps = delta.metrics.aio.pending_streams;
            // Current is absolute (gauge)
            if (typeof ps.current !== 'undefined') {
              metrics.aio.pending_streams.current = ps.current;
            }
            // Deltas for counters
            if (ps.d_total) {
              metrics.aio.pending_streams.total = (metrics.aio.pending_streams.total || 0) + ps.d_total;
            }
            if (ps.d_processed) {
              metrics.aio.pending_streams.processed = (metrics.aio.pending_streams.processed || 0) + ps.d_processed;
            }
            if (ps.d_dropped) {
              metrics.aio.pending_streams.dropped = (metrics.aio.pending_streams.dropped || 0) + ps.d_dropped;
            }
          }
        }

        // Apply SSE registry stats (long-lived diagnostic streams)
        if (delta.metrics.sse) {
          if (!metrics.sse) metrics.sse = {};
          Object.assign(metrics.sse, delta.metrics.sse);
        }

        // Apply registry stats (meta-metrics) - these are absolute values
        if (delta.metrics.registry) {
          metrics.registry = delta.metrics.registry;
        }

        // Apply modular metrics deltas (counters, gauges, histograms)
        if (delta.metrics.modular && delta.metrics.modular.deltas) {
          if (!metrics.modular) metrics.modular = { counters: [], gauges: [], histograms: [] };
          var mod = metrics.modular;

          // Helper: check if labels match (delta labels in d.l, metric labels in m.labels)
          function labelsMatch(deltaLabels, metricLabels) {
            if (!deltaLabels && !metricLabels) return true;
            if (!deltaLabels || !metricLabels) return false;
            var dKeys = Object.keys(deltaLabels);
            var mKeys = Object.keys(metricLabels);
            if (dKeys.length !== mKeys.length) return false;
            for (var i = 0; i < dKeys.length; i++) {
              var k = dKeys[i];
              if (deltaLabels[k] !== metricLabels[k]) return false;
            }
            return true;
          }

          delta.metrics.modular.deltas.forEach(function(d) {
            if (d.t === 'c') {
              // Counter increment - find by name AND labels, then add delta
              var counter = null;
              for (var i = 0; i < (mod.counters || []).length; i++) {
                if (mod.counters[i].name === d.n && labelsMatch(d.l, mod.counters[i].labels)) {
                  counter = mod.counters[i];
                  break;
                }
              }
              if (counter) {
                counter.value = (counter.value || 0) + (d.d || 0);
              } else {
                // New counter, add it with labels
                if (!mod.counters) mod.counters = [];
                mod.counters.push({ name: d.n, value: d.d || 0, labels: d.l || {} });
              }
            } else if (d.t === 'g') {
              // Gauge set - find by name AND labels, then replace value
              var gauge = null;
              for (var i = 0; i < (mod.gauges || []).length; i++) {
                if (mod.gauges[i].name === d.n && labelsMatch(d.l, mod.gauges[i].labels)) {
                  gauge = mod.gauges[i];
                  break;
                }
              }
              if (gauge) {
                gauge.value = d.v;
              } else {
                // New gauge, add it with labels
                if (!mod.gauges) mod.gauges = [];
                mod.gauges.push({ name: d.n, value: d.v, labels: d.l || {} });
              }
            } else if (d.t === 'h') {
              // Histogram observe - find by name AND labels, then add deltas
              var hist = null;
              for (var i = 0; i < (mod.histograms || []).length; i++) {
                if (mod.histograms[i].name === d.n && labelsMatch(d.l, mod.histograms[i].labels)) {
                  hist = mod.histograms[i];
                  break;
                }
              }
              if (hist) {
                hist.count = (hist.count || 0) + (d.c || 0);
                hist.sum_us = (hist.sum_us || 0) + (d.s || 0);
                // Apply bucket deltas (d.b contains cumulative delta per bucket)
                if (d.b && hist.buckets) {
                  for (var bi = 0; bi < d.b.length && bi < hist.buckets.length; bi++) {
                    hist.buckets[bi].count = (hist.buckets[bi].count || 0) + (d.b[bi].d || 0);
                  }
                }
              } else {
                // New histogram, add it with labels and buckets
                if (!mod.histograms) mod.histograms = [];
                var newHist = { name: d.n, count: d.c || 0, sum_us: d.s || 0, labels: d.l || {} };
                if (d.b) {
                  newHist.buckets = d.b.map(function(b) { return { le: b.le, count: b.d || 0 }; });
                }
                mod.histograms.push(newHist);
              }
            }
          });
        }

        metricsUpdated = true;
      }

      // Trigger UI updates with merged state
      // Handle metrics first to ensure panels exist before memory update
      if (metricsUpdated) {
        this.handleMetricsUpdate(this.fullState.metrics);
      }
      if (memoryUpdated) {
        this.handleMemoryUpdate(this.fullState.memory);
      }
    }

    scheduleReconnect() {
      if (this.reconnectAttempts >= this.maxReconnectAttempts) {
        return;
      }

      this.reconnectAttempts++;
      // Immediate first reconnect, then exponential backoff
      var delay = this.reconnectAttempts === 1 ? 0 : Math.min(1000 * Math.pow(2, this.reconnectAttempts - 1), 30000);

      var self = this;
      setTimeout(function() {
        if (self.eventSource) {
          self.eventSource.close();
        }
        self.connect();
      }, delay);
    }

    updateConnectionStatus(connected) {
      updateConnectionStatus(connected);

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
        });
      }

      // Update GC stats
      if (data.gc) {
        self.updateGCStats(data.gc);
      }

      // Update process memory overview
      if (data.process && data.breakdown) {
        self.updateProcessMemory(data.process, data.breakdown, data.smaps);
        if (window.updateCapacityObservedUsage) {
          window.updateCapacityObservedUsage(data.breakdown);
        }
      }

      // Update capacity warning banner
      this.updateCapacityWarnings(warnings, critical);

      // Update REPL eval delta (if running as REPL)
      if (data.repl_eval && data.repl_eval.valid) {
        this.updateReplEvalDelta(data.repl_eval, data.arenas);
      }

    }

    // Update REPL eval memory display with SSE data
    updateReplEvalDelta(replEval, arenas) {
      // Show the REPL eval section if we have data
      var evalSection = document.querySelector('.eval-memory-section');
      if (evalSection) {
        evalSection.style.display = '';
      }

      // Update the display elements
      var exprEl = document.getElementById('eval-last-expr');
      var allocatedEl = document.getElementById('eval-allocated');
      var afterGcEl = document.getElementById('eval-after-gc');
      var deltaEl = document.getElementById('eval-delta');
      var durationEl = document.getElementById('eval-duration');
      var gcTimeEl = document.getElementById('eval-gc-time');
      var arenaHwmEl = document.getElementById('eval-arena-hwm');

      if (exprEl) exprEl.textContent = 'Eval #' + replEval.eval_count;
      if (allocatedEl) allocatedEl.textContent = this.formatBytesDelta(replEval.heap_delta + replEval.scratch_delta);
      if (afterGcEl) afterGcEl.textContent = this.formatBytesDelta(replEval.heap_delta);
      if (deltaEl) {
        deltaEl.textContent = this.formatBytesDelta(replEval.heap_delta);
        deltaEl.classList.remove('positive', 'negative', 'zero');
        if (replEval.heap_delta > 0) deltaEl.classList.add('positive');
        else if (replEval.heap_delta < 0) deltaEl.classList.add('negative');
        else deltaEl.classList.add('zero');
      }

      // Object count changes
      var lvalDelta = replEval.lval_delta || 0;
      var lenvDelta = replEval.lenv_delta || 0;
      if (durationEl) durationEl.textContent = '+' + lvalDelta + ' LVALs';
      if (gcTimeEl) gcTimeEl.textContent = '+' + lenvDelta + ' LENVs';

      // Calculate and display max Arena HWM (useful for large evals)
      if (arenaHwmEl && arenas && arenas.length > 0) {
        var maxHwm = 0;
        arenas.forEach(function(arena) {
          var hwm = arena.high_water_mark || arena.hwm || 0;
          if (hwm > maxHwm) maxHwm = hwm;
        });
        arenaHwmEl.textContent = this.formatBytes(maxHwm);
      }

      // Check for potential leak (positive heap delta)
      var warningEl = document.getElementById('eval-leak-warning');
      if (warningEl) {
        warningEl.style.display = replEval.heap_delta > 0 ? '' : 'none';
      }

      // Record in history using existing function
      if (window.recordEvaluation) {
        window.recordEvaluation(
          'Eval #' + replEval.eval_count,
          replEval.heap_delta + replEval.scratch_delta,
          replEval.heap_delta,
          0,
          0
        );
      }
    }

    // Format byte delta with sign
    formatBytesDelta(bytes) {
      var sign = bytes >= 0 ? '+' : '';
      return sign + this.formatBytes(Math.abs(bytes));
    }

    // Update process memory overview widget
    updateProcessMemory(process, breakdown, smaps) {
      var rss = process.rss || 0;
      var vms = process.vms || 0;
      var systemTotal = process.system_total || 0;

      // Track RSS history for trend sparkline
      this.rssHistory.push(rss);

      // Update inline gauge (memory pressure: RSS as % of system RAM)
      var pct = systemTotal > 0 ? (rss / systemTotal) * 100 : 0;
      var fillEl = document.getElementById('process-gauge-fill');
      if (fillEl) fillEl.style.width = Math.min(pct, 100) + '%';

      // Update RSS and VMS text displays
      var rssEl = document.getElementById('process-rss-text');
      if (rssEl) rssEl.textContent = fmtBytes(rss);

      // Render RSS trend sparkline
      var rssSparkContainer = document.getElementById('spark-rss');
      if (rssSparkContainer) {
        var rssData = padSparklineData(this.rssHistory.toArray(), 60);
        renderMiniSparkline(rssSparkContainer, rssData, {
          width: 48,
          height: 16,
          color: 'var(--color-info)',
          fillOpacity: 0.2,
          strokeWidth: 1.5
        });
      }

      var vmsTextEl = document.getElementById('process-vms-text');
      if (vmsTextEl) vmsTextEl.textContent = fmtBytes(vms);

      // Get capacity and used for each subsystem
      // Runtime combines GC + Scratch
      var runtimeUsed = (breakdown.gc_used || 0) + (breakdown.scratch_used || 0);
      var runtimeCap = (breakdown.gc_cap || 0) + (breakdown.scratch_cap || 0);
      var aioUsed = breakdown.aio_used || 0;
      var aioCap = breakdown.aio_cap || 0;
      var metricsUsed = breakdown.metrics_used || 0;
      var metricsCap = breakdown.metrics_cap || 0;
      var unregistered = breakdown.untracked || 0;           // RSS - tracked used
      var unregisteredReserved = breakdown.untracked_reserved || 0;  // VMS - tracked caps

      // Use RSS as the baseline for the stacked bar (not VMS).
      // VMS on macOS is inflated to hundreds of GB due to pre-reserved address space
      // (MALLOC_NANO, GPU regions, etc.) which makes the bar useless.
      // RSS represents actual physical memory and is meaningful cross-platform.
      var totalTrackedCap = runtimeCap + aioCap + metricsCap;
      var barBase = Math.max(rss, totalTrackedCap);
      var runtimeWidthPct = barBase > 0 ? (runtimeCap / barBase) * 100 : 0;
      var aioWidthPct = barBase > 0 ? (aioCap / barBase) * 100 : 0;
      var metricsWidthPct = barBase > 0 ? (metricsCap / barBase) * 100 : 0;
      // "Other" is untracked RSS (difference between RSS and what we track)
      var untrackedRss = rss > totalTrackedCap ? rss - totalTrackedCap : 0;
      var unregisteredWidthPct = barBase > 0 ? (untrackedRss / barBase) * 100 : 0;

      // Calculate fill percentages (used as % of capacity = resident as % of reserved)
      var runtimeFillPct = runtimeCap > 0 ? (runtimeUsed / runtimeCap) * 100 : 0;
      var aioFillPct = aioCap > 0 ? (aioUsed / aioCap) * 100 : 0;
      var metricsFillPct = metricsCap > 0 ? (metricsUsed / metricsCap) * 100 : 0;
      // "Other" segment is always 100% filled (it represents actual untracked RSS)
      var unregisteredFillPct = 100;

      // Update stacked bar segment widths (based on capacity as % of RSS)
      this.setSegmentWidth('segment-runtime', runtimeWidthPct);
      this.setSegmentWidth('segment-aio', aioWidthPct);
      this.setSegmentWidth('segment-metrics', metricsWidthPct);
      this.setSegmentWidth('segment-other', unregisteredWidthPct);

      // Update segment fills (based on utilization = resident/reserved)
      this.setSegmentFill('fill-runtime', runtimeFillPct);
      this.setSegmentFill('fill-aio', aioFillPct);
      this.setSegmentFill('fill-metrics', metricsFillPct);
      this.setSegmentFill('fill-other', unregisteredFillPct);

      // Update legend values (used / capacity and utilization %)
      this.updateLegendItemWithCap('runtime', runtimeUsed, runtimeCap, runtimeFillPct);
      this.updateLegendItemWithCap('aio', aioUsed, aioCap, aioFillPct);
      this.updateLegendItemWithCap('metrics', metricsUsed, metricsCap, metricsFillPct);
      // "Other" shows untracked RSS (no separate capacity - it's just what's left)
      this.updateLegendItemWithCap('other', untrackedRss, untrackedRss, 100);

      // Update SSL/nghttp2/libuv library memory stats (global - updates all matching elements)
      var sslUsed = breakdown.ssl_used || 0;
      var nghttp2Used = breakdown.nghttp2_used || 0;
      var libuvUsed = breakdown.libuv_used || 0;
      var libTotal = sslUsed + nghttp2Used + libuvUsed;

      document.querySelectorAll('.aio-ssl-bytes').forEach(function(el) {
        el.textContent = fmtBytes(sslUsed);
      });
      document.querySelectorAll('.aio-nghttp2-bytes').forEach(function(el) {
        el.textContent = fmtBytes(nghttp2Used);
      });
      document.querySelectorAll('.aio-libuv-bytes').forEach(function(el) {
        el.textContent = fmtBytes(libuvUsed);
      });
      document.querySelectorAll('.aio-lib-total-bytes').forEach(function(el) {
        el.textContent = fmtBytes(libTotal);
      });
      document.querySelectorAll('.aio-sys-mem-total').forEach(function(el) {
        el.textContent = fmtBytes(aioUsed);
      });

      // Update footer stats
      var vmsEl = document.getElementById('process-vms');
      if (vmsEl) vmsEl.textContent = fmtBytes(vms);

      var pfMinorEl = document.getElementById('process-pf-minor');
      if (pfMinorEl) pfMinorEl.textContent = fmtCompact(process.page_faults_minor || 0);

      var pfMajorEl = document.getElementById('process-pf-major');
      if (pfMajorEl) pfMajorEl.textContent = fmtCompact(process.page_faults_major || 0);

      // Update smaps breakdown (OS memory regions)
      // Hide on macOS - the data is unreliable (only has anon/shmem, no real breakdown)
      // Detect macOS by checking if file and stack are both 0 (Linux always has these)
      var smapsEl = document.querySelector('.smaps-breakdown');
      var isRealSmaps = smaps && smaps.total > 0 && (smaps.file > 0 || smaps.stack > 0);
      
      if (smapsEl) {
        smapsEl.style.display = isRealSmaps ? '' : 'none';
      }
      
      if (isRealSmaps) {
        var total = smaps.total;

        // Update bar segment widths as percentage of total
        this.setSegmentWidth('smaps-seg-heap', (smaps.heap / total) * 100);
        this.setSegmentWidth('smaps-seg-anon', (smaps.anon / total) * 100);
        this.setSegmentWidth('smaps-seg-file', (smaps.file / total) * 100);
        this.setSegmentWidth('smaps-seg-stack', (smaps.stack / total) * 100);
        this.setSegmentWidth('smaps-seg-uring', (smaps.uring / total) * 100);
        this.setSegmentWidth('smaps-seg-other', (smaps.other / total) * 100);

        // Update legend values
        var heapEl = document.getElementById('smaps-heap-value');
        if (heapEl) heapEl.textContent = fmtBytes(smaps.heap);

        var anonEl = document.getElementById('smaps-anon-value');
        if (anonEl) anonEl.textContent = fmtBytes(smaps.anon);

        var fileEl = document.getElementById('smaps-file-value');
        if (fileEl) fileEl.textContent = fmtBytes(smaps.file);

        var stackEl = document.getElementById('smaps-stack-value');
        if (stackEl) stackEl.textContent = fmtBytes(smaps.stack);

        var uringEl = document.getElementById('smaps-uring-value');
        if (uringEl) uringEl.textContent = fmtBytes(smaps.uring);

        var otherEl = document.getElementById('smaps-other-value');
        if (otherEl) otherEl.textContent = fmtBytes(smaps.other);

        // Update region counts
        var anonRegionsEl = document.getElementById('smaps-anon-regions');
        if (anonRegionsEl) anonRegionsEl.textContent = smaps.anon_regions || 0;

        var fileRegionsEl = document.getElementById('smaps-file-regions');
        if (fileRegionsEl) fileRegionsEl.textContent = smaps.file_regions || 0;
      }
    }

    setSegmentWidth(id, pct) {
      var el = document.getElementById(id);
      if (el) el.style.width = pct + '%';
    }

    setSegmentFill(id, pct) {
      var el = document.getElementById(id);
      if (el) el.style.width = Math.min(pct, 100) + '%';
    }

    updateLegendItemWithCap(name, used, cap, utilPct) {
      var valueEl = document.getElementById('breakdown-' + name + '-value');
      if (valueEl) valueEl.textContent = fmtBytes(used);

      var capEl = document.getElementById('breakdown-' + name + '-cap');
      if (capEl) capEl.textContent = fmtBytes(cap);

      var pctEl = document.getElementById('breakdown-' + name + '-pct');
      if (pctEl) pctEl.textContent = '(' + Math.round(utilPct) + '%)';
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
        var gcData = {
          cycles_total: vm.gc ? vm.gc.cycles_total : 0,
          pause_us_total: vm.gc ? vm.gc.pause_us_total : 0,
          pause_us_max: vm.gc ? vm.gc.pause_us_max : 0,
          reclaimed_bytes_total: vm.gc ? vm.gc.reclaimed_bytes_total : 0,
          allocated_bytes_total: vm.gc ? vm.gc.allocated_bytes : 0,
          efficiency_pct: vm.gc ? vm.gc.efficiency_pct : 0,
          heap_used_bytes: vm.gc ? vm.gc.heap_used_bytes : 0,
          heap_total_bytes: vm.gc ? vm.gc.heap_total_bytes : 0,
          large_object_bytes: vm.gc ? vm.gc.large_object_bytes : 0,
          pause_ms_avg: vm.gc && vm.gc.cycles_total > 0
            ? (vm.gc.pause_us_total / vm.gc.cycles_total) / 1000
            : 0
        };
        // Pass through size_classes, pause_histogram, survival if present
        if (vm.gc && vm.gc.size_classes) {
          gcData.size_classes = vm.gc.size_classes;
        }
        if (vm.gc && vm.gc.pause_histogram) {
          gcData.pause_histogram = vm.gc.pause_histogram;
        }
        if (vm.gc && vm.gc.survival) {
          gcData.survival = vm.gc.survival;
        }
        dashboardData.vm_metrics = {
          gc: gcData,
          interpreter: {
            evals_total: vm.interpreter ? vm.interpreter.evals_total : 0,
            function_calls: vm.interpreter ? vm.interpreter.function_calls : 0,
            builtin_calls: vm.interpreter ? vm.interpreter.builtin_calls : 0,
            stack_depth_max: vm.interpreter ? vm.interpreter.stack_depth_max : 0,
            closures_created: vm.interpreter ? vm.interpreter.closures_created : 0,
            env_lookups: vm.interpreter ? vm.interpreter.env_lookups : 0
          }
          // Note: event_loop metrics are now in modular metrics with loop={name} label
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
          },
          queue: {
            pending_requests: aio.queue ? aio.queue.pending_requests : 0,
            pending_responses: aio.queue ? aio.queue.pending_responses : 0,
            capacity: aio.queue ? aio.queue.capacity : 0
          },
          pending_streams: {
            current: aio.pending_streams ? aio.pending_streams.current : 0,
            total: aio.pending_streams ? aio.pending_streams.total : 0,
            processed: aio.pending_streams ? aio.pending_streams.processed : 0,
            dropped: aio.pending_streams ? aio.pending_streams.dropped : 0,
            avg_wait_ms: aio.pending_streams ? aio.pending_streams.avg_wait_ms : 0,
            pool_size: aio.pending_streams ? aio.pending_streams.pool_size : 64
          }
        };

        // Create an AIO system entry for the systems array
        // Note: event_loop metrics come from modular metrics (loop={name} label)
        dashboardData.aio_systems = [{
          name: 'main',
          uptime_seconds: aio.uptime_seconds || 0,
          system: dashboardData.aio_metrics.system,
          connections: dashboardData.aio_metrics.connections,
          queue: dashboardData.aio_metrics.queue,
          pending_streams: dashboardData.aio_metrics.pending_streams
        }];
      }

      // Add SSE registry metrics (long-lived diagnostic streams)
      if (metrics.sse) {
        dashboardData.sse_metrics = {
          streams_active: metrics.sse.streams_active || 0,
          events_pushed_total: metrics.sse.events_pushed_total || 0,
          bytes_pushed_total: metrics.sse.bytes_pushed_total || 0
        };
      }

      // Call the main dashboard update function
      updateDashboard(dashboardData);

      // Update GC stats panel with full VM GC data (size_classes, pause_histogram, survival)
      if (dashboardData.vm_metrics && dashboardData.vm_metrics.gc) {
        this.updateGCStats(dashboardData.vm_metrics.gc);
      }

      // Update metrics registry panel if registry data is present
      if (metrics.registry) {
        this.updateRegistryPanel(metrics.registry);
      }
    }

    // Update the metrics registry meta-metrics panel
    updateRegistryPanel(registry) {
      if (!registry) return;

      // Helper to update a stat card
      function updateStatCard(prefix, data) {
        var active = data.active || 0;
        var capacity = data.capacity || 1;
        var free = data.free || 0;
        var pct = (active / capacity) * 100;

        var barEl = $(prefix + '-bar');
        var activeEl = $(prefix + '-active');
        var capacityEl = $(prefix + '-capacity');
        var freeEl = $(prefix + '-free');

        if (barEl) {
          barEl.style.width = Math.min(pct, 100) + '%';
          barEl.classList.remove('warning', 'critical');
          if (pct > 90) barEl.classList.add('critical');
          else if (pct > 70) barEl.classList.add('warning');
        }
        if (activeEl) activeEl.textContent = active;
        if (capacityEl) capacityEl.textContent = capacity;
        if (freeEl) freeEl.textContent = free;
      }

      // Update counters
      if (registry.counters) {
        updateStatCard('registry-counters', registry.counters);
      }

      // Update gauges
      if (registry.gauges) {
        updateStatCard('registry-gauges', registry.gauges);
      }

      // Update histograms
      if (registry.histograms) {
        updateStatCard('registry-histograms', registry.histograms);
      }

      // Update string pool
      if (registry.string_pool) {
        var sp = registry.string_pool;
        var spPct = (sp.used / (sp.capacity || 1)) * 100;
        var barEl = $('registry-strings-bar');
        var usedEl = $('registry-strings-used');
        var capEl = $('registry-strings-capacity');

        if (barEl) {
          barEl.style.width = Math.min(spPct, 100) + '%';
          barEl.classList.remove('warning', 'critical');
          if (spPct > 90) barEl.classList.add('critical');
          else if (spPct > 70) barEl.classList.add('warning');
        }
        if (usedEl) usedEl.textContent = sp.used;
        if (capEl) capEl.textContent = sp.capacity;
      }

      // Update eviction stats
      if (registry.evictions) {
        var ev = registry.evictions;
        var totalEl = $('registry-evictions-total');
        var cntEl = $('registry-evictions-counters');
        var gaugeEl = $('registry-evictions-gauges');
        var histEl = $('registry-evictions-histograms');

        if (totalEl) totalEl.textContent = fmtCompact(ev.total || 0);
        if (cntEl) cntEl.textContent = ev.counters || 0;
        if (gaugeEl) gaugeEl.textContent = ev.gauges || 0;
        if (histEl) histEl.textContent = ev.histograms || 0;
      }

      // Update collection time
      var collectEl = $('registry-collect-time');
      if (collectEl && registry.collect_time_us !== undefined) {
        collectEl.textContent = registry.collect_time_us;
      }

      // Update section badges
      var totalActive = (registry.counters ? registry.counters.active : 0) +
                        (registry.gauges ? registry.gauges.active : 0) +
                        (registry.histograms ? registry.histograms.active : 0);
      var stringsUsed = registry.string_pool ? registry.string_pool.used : 0;

      var totalBadge = $('metrics-total-badge');
      var stringsBadge = $('metrics-strings-badge');
      if (totalBadge) {
        totalBadge.textContent = totalActive + ' metrics';
      }
      if (stringsBadge) {
        stringsBadge.textContent = stringsUsed + ' strings';
      }
    }

    updateSlabGrid(slab, ownerMap) {
      var self = this;

      // Compute HWM percentage for markers if hwm is provided
      var slabData = Object.assign({}, slab);
      if (slab.hwm !== undefined && slab.total > 0) {
        var hwmPct = (slab.hwm / slab.total) * 100;
        slabData.markers = { hwm: { position: hwmPct, value: slab.hwm } };
      }

      var widgets = PoolWidget.getAll(slab.slabKey || slab.name);
      widgets.forEach(function(widget) {
        widget.update(slabData);

        // Handle owner breakdown rendering (special case for handles slab)
        if (slab.name === 'handles' && widget.el) {
          if (slab.summary && slab.summary.by_owner && ownerMap && ownerMap.length > 0) {
            self.renderOwnerBreakdown(widget.el, slab.summary.by_owner, slab.used, ownerMap);
          }
        }
      });
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
      var used = arena.used_bytes || arena.used || 0;
      var capacity = arena.capacity_bytes || arena.capacity || 1;
      var hwm = arena.high_water_mark || arena.hwm || 0;
      var hwmPercentage = (hwm / capacity) * 100;
      var usedStr = this.formatBytes(used);
      var capacityStr = this.formatBytes(capacity);
      var overflow = arena.overflow_fallbacks || arena.overflow || 0;
      var overflowBytes = arena.overflow_bytes || 0;

      // Get or create widget for this arena
      var widget = arenaGauges[arena.name];
      if (!widget) {
        var container = document.getElementById('arenas-container');
        if (!container) return;

        // Create widget dynamically
        var widgetId = 'arena-' + arena.name.replace(/[^a-z0-9]/gi, '-');
        widget = new PoolWidget({
          id: widgetId,
          name: arena.name.charAt(0).toUpperCase() + arena.name.slice(1),
          preset: 'arena',
          variant: 'compact',
          showGauge: true,
          showGrid: false,
          showTrend: true,
          markers: PoolWidget.Markers.hwmOnly({ hwmColor: 'var(--color-warning)' }),
          stats: [
            { id: 'hwm', label: 'hwm:' },
            { id: 'overflow', label: 'overflow:' }
          ]
        });

        // Append to container
        var wrapper = document.createElement('div');
        wrapper.innerHTML = widget.render();
        container.appendChild(wrapper.firstChild);
        widget.bind();
        arenaGauges[arena.name] = widget;
      }

      // Update widget
      widget.update({
        used: used,
        total: capacity,
        usedFormatted: usedStr,
        totalFormatted: capacityStr,
        markers: {
          hwm: { position: hwmPercentage, value: hwm }
        },
        stats: {
          hwm: this.formatBytes(hwm),
          overflow: overflow > 0 ? overflow : '0'
        }
      });
    }

    updateGCStats(gc) {
      // Update heap pressure gauge (works with both tiered and non-tiered GC)
      this.updateHeapPressure(gc);
      
      if (gc.tiers && gc.tiers.length > 0) {
        this.updateTieredHeap(gc);
      }

      // Update GC panel if it exists (legacy)
      var gcPanel = document.querySelector('.gc-stats-panel');
      if (gcPanel) {
        var allocated = gcPanel.querySelector('[data-gc="allocated"]');
        var peak = gcPanel.querySelector('[data-gc="peak"]');
        var cycles = gcPanel.querySelector('[data-gc="cycles"]');

        // For legacy panel, show combined bytes from all tiers or heap_used_bytes
        var totalUsed = 0;
        if (gc.tiers) {
          for (var i = 0; i < gc.tiers.length; i++) {
            totalUsed += gc.tiers[i].bytes_used || 0;
          }
        } else {
          totalUsed = gc.heap_used_bytes || 0;
        }
        if (allocated) allocated.textContent = this.formatBytes(totalUsed);
        if (cycles) cycles.textContent = (gc.cycles_total || gc.cycles || 0).toLocaleString();
      }

      // Update survival histogram (object lifetimes)
      if (gc.survival) {
        this.updateSurvivalHistogram(gc.survival, gc.efficiency_pct);
      }

      // Update frame-time pause histogram for game profile
      if (gc.pause_histogram && document.body.classList.contains('profile-game')) {
        this.updatePauseHistogram(gc.pause_histogram);
      }

      // Update capacity planner peak for embedded profile
      if (gc.tiers && document.body.classList.contains('profile-embedded')) {
        var totalPeak = 0;
        for (var i = 0; i < gc.tiers.length; i++) {
          totalPeak += gc.tiers[i].bytes_peak || 0;
        }
        if (window.updateCapacityCurrentPeak) {
          window.updateCapacityCurrentPeak(totalPeak);
        }
      }

      // Update parallel GC badge
      if (gc.parallel) {
        this.updateParallelBadge(gc.parallel);
      }

      // Update pause histogram (new UI - always show, not just game profile)
      if (gc.pause_histogram) {
        this.updateGCPauseHistogram(gc.pause_histogram);
      }

      // Update size classes
      if (gc.size_classes) {
        this.updateSizeClasses(gc.size_classes, gc.large_object_bytes);
      }
    }

    updateFragmentationStats(frag) {
      var lvalPctEl = document.getElementById('lval-frag-pct');
      var lenvPctEl = document.getElementById('lenv-frag-pct');
      var lvalBarEl = document.getElementById('lval-frag-bar');
      var lenvBarEl = document.getElementById('lenv-frag-bar');
      var freeListCountEl = document.getElementById('free-list-count');
      var freeListBytesEl = document.getElementById('free-list-bytes');

      var lvalPct = frag.lval_pct || 0;
      var lenvPct = frag.lenv_pct || 0;

      if (lvalPctEl) lvalPctEl.textContent = lvalPct.toFixed(1);
      if (lenvPctEl) lenvPctEl.textContent = lenvPct.toFixed(1);

      if (lvalBarEl) lvalBarEl.style.width = Math.min(100, lvalPct) + '%';
      if (lenvBarEl) lenvBarEl.style.width = Math.min(100, lenvPct) + '%';

      // Add warning class for high fragmentation (>25%)
      var lvalStat = lvalPctEl ? lvalPctEl.closest('.frag-stat') : null;
      var lenvStat = lenvPctEl ? lenvPctEl.closest('.frag-stat') : null;
      if (lvalStat) lvalStat.classList.toggle('high-frag', lvalPct > 25);
      if (lenvStat) lenvStat.classList.toggle('high-frag', lenvPct > 25);

      if (freeListCountEl) freeListCountEl.textContent = (frag.free_list_count || 0).toLocaleString();
      if (freeListBytesEl) freeListBytesEl.textContent = this.formatBytes(frag.free_list_bytes || 0);
    }

    updateParallelBadge(parallel) {
      var badge = document.getElementById('gc-parallel-badge');
      if (!badge) return;

      var textEl = badge.querySelector('.parallel-text');
      if (!textEl) textEl = badge;

      if (parallel.enabled) {
        textEl.textContent = parallel.threads + ' threads';
        badge.classList.add('parallel-active');
        this.updateThreadActivity(parallel.threads, parallel.cycles > (this._prevParallelCycles || 0));
        this._prevParallelCycles = parallel.cycles;
      } else {
        textEl.textContent = 'Single';
        badge.classList.remove('parallel-active');
        this.hideThreadActivity();
      }
    }

    updateThreadActivity(threadCount, isActive) {
      var container = document.getElementById('gc-thread-activity');
      var grid = document.getElementById('thread-activity-grid');
      var countEl = document.getElementById('thread-count');
      
      if (!container || !grid) return;

      if (threadCount > 1) {
        container.style.display = '';
        countEl.textContent = threadCount + ' threads';

        var html = '';
        for (var i = 0; i < threadCount; i++) {
          var cls = 'thread-indicator' + (isActive ? ' marking' : ' active');
          html += '<div class="' + cls + '">' + i + '</div>';
        }
        grid.innerHTML = html;
      } else {
        container.style.display = 'none';
      }
    }

    hideThreadActivity() {
      var container = document.getElementById('gc-thread-activity');
      if (container) container.style.display = 'none';
    }

    updateHeapPressure(gc) {
      var heapUsed, heapTotal;
      
      if (gc.tiers && gc.tiers.length > 0) {
        var heapTier = this.findTier(gc.tiers, 'heap2') || {};
        heapUsed = heapTier.bytes_used || 0;
        heapTotal = heapTier.bytes_total || 1;
      } else {
        heapUsed = gc.heap_used_bytes || 0;
        heapTotal = gc.heap_total_bytes || 1;
      }
      var heapPct = heapTotal > 0 ? (heapUsed / heapTotal) * 100 : 0;

      var arc = document.getElementById('heap-pressure-arc');
      var valueEl = document.getElementById('heap-pressure-value');
      var usedEl = document.getElementById('heap-pressure-used');
      var totalEl = document.getElementById('heap-pressure-total');

      if (arc) {
        var circumference = 251.2;
        var offset = circumference * (1 - heapPct / 100);
        arc.style.strokeDashoffset = offset;
      }

      if (valueEl) valueEl.textContent = Math.round(heapPct);
      if (usedEl) usedEl.textContent = this.formatBytes(heapUsed);
      if (totalEl) totalEl.textContent = this.formatBytes(heapTotal);

      this.updateAllocationRate(heapUsed);
    }

    updateAllocationRate(currentUsed) {
      var now = Date.now();
      var prev = this._prevAllocState || { time: now, used: currentUsed };
      
      var dt = (now - prev.time) / 1000;
      if (dt < 0.05) return;

      var bytesAllocated = currentUsed - prev.used;
      var rate = bytesAllocated > 0 ? bytesAllocated / dt : 0;

      this._allocRateHistory = this._allocRateHistory || [];
      this._allocRateHistory.push(rate);
      if (this._allocRateHistory.length > 60) this._allocRateHistory.shift();

      this._prevAllocState = { time: now, used: currentUsed };

      var rateDisplay = document.getElementById('alloc-rate-display');
      var badgeValue = document.querySelector('.gc-alloc-rate-badge .alloc-rate-value');
      
      var rateStr = this.formatBytesRate(rate);
      if (rateDisplay) rateDisplay.textContent = rateStr;
      if (badgeValue) badgeValue.textContent = rateStr.replace('/s', '');

      var sparkContainer = document.getElementById('alloc-rate-spark');
      if (sparkContainer && this._allocRateHistory.length > 2) {
        var data = this._allocRateHistory.slice();
        while (data.length < 60) data.unshift(0);
        renderMiniSparkline(sparkContainer, data, {
          width: sparkContainer.clientWidth || 200,
          height: 48,
          color: 'var(--color-cyan)',
          fillOpacity: 0.3
        });
      }
    }

    formatBytesRate(bytesPerSec) {
      if (bytesPerSec >= 1024 * 1024 * 1024) return (bytesPerSec / (1024 * 1024 * 1024)).toFixed(1) + 'GB/s';
      if (bytesPerSec >= 1024 * 1024) return (bytesPerSec / (1024 * 1024)).toFixed(1) + 'MB/s';
      if (bytesPerSec >= 1024) return (bytesPerSec / 1024).toFixed(1) + 'KB/s';
      return Math.round(bytesPerSec) + 'B/s';
    }

    updateGCPauseHistogram(pauseHist) {
      var buckets = [
        { key: '0_1ms', id: 'gc-pause-0-1', count: pauseHist['0_1ms'] || 0, midpoint: 0.5 },
        { key: '1_5ms', id: 'gc-pause-1-5', count: pauseHist['1_5ms'] || 0, midpoint: 3 },
        { key: '5_10ms', id: 'gc-pause-5-10', count: pauseHist['5_10ms'] || 0, midpoint: 7.5 },
        { key: '10_16ms', id: 'gc-pause-10-16', count: pauseHist['10_16ms'] || 0, midpoint: 13 },
        { key: '16ms_plus', id: 'gc-pause-16-plus', count: pauseHist['16ms_plus'] || 0, midpoint: 25 }
      ];

      var maxCount = Math.max(1, Math.max.apply(null, buckets.map(function(b) { return b.count; })));
      var maxBarHeight = 36;

      var totalPauses = 0;
      var weightedSum = 0;
      buckets.forEach(function(b) {
        totalPauses += b.count;
        weightedSum += b.count * b.midpoint;
      });
      var avgPause = totalPauses > 0 ? weightedSum / totalPauses : 0;

      var avgEl = document.getElementById('gc-avg-pause-inline');
      if (avgEl) {
        avgEl.textContent = 'avg: ' + avgPause.toFixed(1) + 'ms';
        avgEl.classList.remove('warning', 'error');
        if (avgPause > 10) avgEl.classList.add('error');
        else if (avgPause > 5) avgEl.classList.add('warning');
      }

      var self = this;
      buckets.forEach(function(b) {
        var el = document.getElementById(b.id);
        if (!el) return;

        var fill = el.querySelector('.gc-pause-bar-fill');
        var countEl = el.querySelector('.gc-pause-bar-count');

        if (fill) {
          var pct = (b.count / maxCount) * maxBarHeight;
          fill.style.height = Math.max(2, pct) + 'px';
        }
        if (countEl) {
          countEl.textContent = b.count > 0 ? self.fmtCompact(b.count) : '--';
        }
      });
    }

    updateSizeClasses(sizeClasses, largeObjectBytes) {
      var grid = document.getElementById('gc-size-class-grid');
      if (!grid) return;

      var self = this;
      sizeClasses.forEach(function(cls) {
        var usage = cls.total > 0 ? (cls.used / cls.total * 100) : 0;
        var sizeEl = grid.querySelector('[data-size="' + cls.size + '"]');
        if (sizeEl) {
          var bar = sizeEl.querySelector('.gc-size-class-bar');
          var fill = sizeEl.querySelector('.gc-size-class-fill');
          var glow = sizeEl.querySelector('.gc-size-class-glow');
          var tooltip = sizeEl.querySelector('.gc-size-class-tooltip');
          
          if (bar) {
            bar.style.setProperty('--usage', usage + '%');
          }
          if (fill) {
            fill.style.height = usage + '%';
          }
          if (glow) {
            glow.style.height = usage + '%';
          }
          if (tooltip) {
            tooltip.textContent = self.fmtCompact(cls.used) + '/' + self.fmtCompact(cls.total) + ' (' + usage.toFixed(0) + '%)';
          }
        }
      });

      var largeEl = document.getElementById('gc-large-objects');
      if (largeEl && largeObjectBytes !== undefined) {
        largeEl.textContent = 'Large: ' + this.formatBytes(largeObjectBytes);
      }
    }

    fmtCompact(n) {
      if (n >= 1000000) return (n / 1000000).toFixed(1) + 'M';
      if (n >= 1000) return (n / 1000).toFixed(1) + 'K';
      return n.toString();
    }

    updatePauseHistogram(pauseHist) {
      var buckets = {
        '0-1': pauseHist['0_1ms'] || 0,
        '1-5': pauseHist['1_5ms'] || 0,
        '5-10': pauseHist['5_10ms'] || 0,
        '10-16': pauseHist['10_16ms'] || 0,
        '16+': pauseHist['16ms_plus'] || 0
      };

      var maxCount = Math.max(1, Math.max.apply(null, Object.values(buckets)));
      var bucketHeight = 48;

      var bucketIds = [
        { key: '0-1', id: 'frame-pause-0-1' },
        { key: '1-5', id: 'frame-pause-1-5' },
        { key: '5-10', id: 'frame-pause-5-10' },
        { key: '10-16', id: 'frame-pause-10-16' },
        { key: '16+', id: 'frame-pause-16-plus' }
      ];

      bucketIds.forEach(function(b) {
        var el = document.getElementById(b.id);
        var countEl = document.getElementById(b.id + '-count');
        if (el && countEl) {
          var count = buckets[b.key] || 0;
          var fill = el.querySelector('.frame-pause-bar-fill');
          if (fill) {
            fill.style.height = Math.max(2, (count / maxCount) * bucketHeight) + 'px';
          }
          countEl.textContent = count > 0 ? count : '--';
        }
      });

      var warningEl = document.getElementById('frame-pause-warning');
      if (warningEl) {
        var total = buckets['0-1'] + buckets['1-5'] + buckets['5-10'] + buckets['10-16'] + buckets['16+'];
        var exceeds10ms = buckets['10-16'] + buckets['16+'];
        var pctExceeds = total > 0 ? (exceeds10ms / total) * 100 : 0;
        warningEl.style.display = pctExceeds > 10 ? '' : 'none';
      }
    }

    updateSurvivalHistogram(survival, efficiencyPct) {
      // Get counts from survival object
      var gen0 = survival.gen_0 || 0;
      var gen1_5 = survival.gen_1_5 || 0;
      var gen6_20 = survival.gen_6_20 || 0;
      var gen21_plus = survival.gen_21_plus || 0;

      // Calculate total and percentages
      var total = gen0 + gen1_5 + gen6_20 + gen21_plus;

      // Update bar heights (as percentage of max)
      var maxCount = Math.max(gen0, gen1_5, gen6_20, gen21_plus, 1);
      var maxBarHeight = 28; // Max height in pixels

      this.updateSurvivalBar('gc-survival-gen0', gen0, maxCount, maxBarHeight);
      this.updateSurvivalBar('gc-survival-gen1-5', gen1_5, maxCount, maxBarHeight);
      this.updateSurvivalBar('gc-survival-gen6-20', gen6_20, maxCount, maxBarHeight);
      this.updateSurvivalBar('gc-survival-gen21-plus', gen21_plus, maxCount, maxBarHeight);

      // Update count labels
      var gen0CountEl = document.getElementById('gc-survival-gen0-count');
      var gen1_5CountEl = document.getElementById('gc-survival-gen1-5-count');
      var gen6_20CountEl = document.getElementById('gc-survival-gen6-20-count');
      var gen21_plusCountEl = document.getElementById('gc-survival-gen21-plus-count');

      if (gen0CountEl) gen0CountEl.textContent = fmtCompact(gen0);
      if (gen1_5CountEl) gen1_5CountEl.textContent = fmtCompact(gen1_5);
      if (gen6_20CountEl) gen6_20CountEl.textContent = fmtCompact(gen6_20);
      if (gen21_plusCountEl) gen21_plusCountEl.textContent = fmtCompact(gen21_plus);

      // Update efficiency display
      var efficiencyEl = document.getElementById('gc-efficiency-value');
      if (efficiencyEl) {
        var eff = efficiencyPct || 0;
        efficiencyEl.textContent = eff;
        efficiencyEl.classList.remove('warning', 'critical');
        if (eff < 50) {
          efficiencyEl.classList.add('critical');
        } else if (eff < 80) {
          efficiencyEl.classList.add('warning');
        }
      }

      // Show leak warning if long-lived objects are growing
      // Heuristic: warn if >2% of total objects are in gen21+ bucket
      var leakWarningEl = document.getElementById('gc-leak-warning');
      if (leakWarningEl) {
        var longLivedPct = total > 0 ? (gen21_plus / total) * 100 : 0;
        // Also track if gen21+ count is growing (store previous value)
        var prevGen21Plus = this._prevGen21Plus || 0;
        var isGrowing = gen21_plus > prevGen21Plus && prevGen21Plus > 0;
        this._prevGen21Plus = gen21_plus;

        // Show warning if: significant long-lived objects AND they're growing
        if (longLivedPct > 5 || (longLivedPct > 2 && isGrowing && gen21_plus > 100)) {
          leakWarningEl.style.display = '';
        } else {
          leakWarningEl.style.display = 'none';
        }
      }
    }

    updateSurvivalBar(id, count, maxCount, maxHeight) {
      var barEl = document.getElementById(id);
      if (!barEl) return;

      var fillEl = barEl.querySelector('.gc-survival-bar-fill');
      if (fillEl) {
        var height = maxCount > 0 ? (count / maxCount) * maxHeight : 2;
        fillEl.style.height = Math.max(height, 2) + 'px';
      }
    }

    // Helper to find a tier by name from the tiers array
    findTier(tiers, name) {
      if (!tiers) return null;
      for (var i = 0; i < tiers.length; i++) {
        if (tiers[i].name === name) return tiers[i];
      }
      return null;
    }

    updateTieredHeap(gc) {
      // Find heap2 tier (the new parallel GC heap)
      var tiers = gc.tiers || [];
      var heapTier = this.findTier(tiers, 'heap2') || {};

      // Heap metrics
      var heapUsed = heapTier.bytes_used || 0;
      var heapTotal = heapTier.bytes_total || 1;
      var heapPeak = heapTier.bytes_peak || 0;
      var heapHwmPct = heapTotal > 0 ? (heapPeak / heapTotal) * 100 : 0;
      var heapUsagePct = heapTotal > 0 ? (heapUsed / heapTotal) * 100 : 0;

      var thresholdPct = gc.threshold_pct || 75;

      // Update Heap Tier PoolWidget
      if (heapTierGauge) {
        heapTierGauge.warningThreshold = thresholdPct;
        heapTierGauge.update({
          used: heapUsed,
          total: heapTotal,
          usedFormatted: fmtBytes(heapUsed),
          totalFormatted: fmtBytes(heapTotal),
          markers: {
            hwm: { position: heapHwmPct, value: heapPeak },
            threshold: { position: thresholdPct, value: thresholdPct }
          },
          stats: {
            peak: fmtBytes(heapPeak),
            hwm: Math.round(heapHwmPct)
          }
        });
      }

    }

    formatBytes(bytes) {
      if (bytes < 1024) return bytes + 'B';
      if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + 'KB';
      if (bytes < 1024 * 1024 * 1024) return (bytes / (1024 * 1024)).toFixed(1) + 'MB';
      return (bytes / (1024 * 1024 * 1024)).toFixed(1) + 'GB';
    }

    disconnect() {
      if (this.eventSource) {
        this.isClosing = true;
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

  // Clean up EventSource on page unload to prevent connection errors
  window.addEventListener('beforeunload', function() {
    if (memoryDiagnostics && memoryDiagnostics.eventSource) {
      memoryDiagnostics.isClosing = true;
      memoryDiagnostics.eventSource.close();
    }
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

  // ==================== Panel Collapse/Expand ====================
  window.togglePanel = function(panelId) {
    var panel = document.getElementById(panelId);
    if (!panel) return;

    var isCollapsed = panel.classList.contains('collapsed');
    var header = panel.querySelector('.panel-header');

    if (isCollapsed) {
      panel.classList.remove('collapsed');
      if (header) header.setAttribute('aria-expanded', 'true');
    } else {
      panel.classList.add('collapsed');
      if (header) header.setAttribute('aria-expanded', 'false');
    }

    // Save preference to localStorage
    try {
      var prefs = JSON.parse(localStorage.getItem('dashboard-panels') || '{}');
      prefs[panelId] = !isCollapsed;
      localStorage.setItem('dashboard-panels', JSON.stringify(prefs));
    } catch(e) {}
  };

  // Toggle process memory breakdown
  window.toggleBreakdown = function() {
    var breakdown = document.getElementById('process-breakdown');
    var toggle = document.querySelector('.breakdown-toggle');
    if (!breakdown) return;

    var isCollapsed = breakdown.classList.contains('collapsed');

    if (isCollapsed) {
      breakdown.classList.remove('collapsed');
      if (toggle) toggle.setAttribute('aria-expanded', 'true');
    } else {
      breakdown.classList.add('collapsed');
      if (toggle) toggle.setAttribute('aria-expanded', 'false');
    }

    // Save preference
    try {
      localStorage.setItem('dashboard-breakdown-expanded', isCollapsed ? 'true' : 'false');
    } catch(e) {}
  };

  // Restore breakdown state on load
  function restoreBreakdownState() {
    try {
      var expanded = localStorage.getItem('dashboard-breakdown-expanded') === 'true';
      if (expanded) {
        var breakdown = document.getElementById('process-breakdown');
        var toggle = document.querySelector('.breakdown-toggle');
        if (breakdown) breakdown.classList.remove('collapsed');
        if (toggle) toggle.setAttribute('aria-expanded', 'true');
      }
    } catch(e) {}
  }

  // Restore panel states on load
  function restorePanelStates() {
    try {
      var prefs = JSON.parse(localStorage.getItem('dashboard-panels') || '{}');
      for (var panelId in prefs) {
        if (prefs[panelId]) {
          var panel = document.getElementById(panelId);
          if (panel) {
            panel.classList.add('collapsed');
            var header = panel.querySelector('.panel-header');
            if (header) header.setAttribute('aria-expanded', 'false');
          }
        }
      }
    } catch(e) {}
  }

  // Keyboard support for panel toggle
  document.addEventListener('keydown', function(e) {
    if (e.target.classList.contains('panel-header') || e.target.closest('.panel-header')) {
      if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        var header = e.target.classList.contains('panel-header') ? e.target : e.target.closest('.panel-header');
        if (header && header.onclick) {
          header.onclick();
        }
      }
    }
  });

  document.addEventListener('DOMContentLoaded', restorePanelStates);
  document.addEventListener('DOMContentLoaded', restoreBreakdownState);
})();

// ==================== PHASE 7: I/O Entity Cards ====================
// Note: I/O sections (TCP, UDP, Files) are now nested inside each AIO system panel
// These card creation functions are used when real data becomes available
(function() {
  'use strict';

  // TCP Server Card
  function createTcpServerCard(info) {
    var card = document.createElement('article');
    card.className = 'entity-card tcp-server collapsed';
    card.id = 'tcp-server-' + info.port;

    card.innerHTML =
      '<div class="entity-header" onclick="toggleEntityCard(this.parentElement)">' +
      '<div class="entity-status ok"></div>' +
      '<h3 class="entity-name">:' + info.port + '</h3>' +
      '<div class="entity-label">TCP</div>' +
      '<div class="entity-stats">' +
      '<div class="entity-stat"><div class="entity-stat-value active-count">--</div><div class="entity-stat-label">Conns</div></div>' +
      '<div class="entity-stat"><div class="entity-stat-value accept-rate">--/s</div><div class="entity-stat-label">Accept</div></div>' +
      '</div>' +
      '<div class="entity-summary">' +
      '<span class="summary-metric conn-count">-- conn</span>' +
      '<span class="summary-metric accept-rate">--/s</span>' +
      '</div>' +
      '<button class="expand-toggle"><span class="expand-icon">▼</span></button>' +
      '</div>' +
      '<div class="entity-body">' +
      '<div class="entity-section">' +
      '<div class="tcp-conn-stats">' +
      '<span class="tcp-stat">●<span class="active-count">--</span> active</span>' +
      '<span class="tcp-stat">○<span class="idle-count">--</span> idle</span>' +
      '<span class="tcp-stat">◐<span class="closing-count">--</span> closing</span>' +
      '</div>' +
      '</div>' +
      '<div class="entity-section">' +
      '<div class="throughput-row">' +
      '<div class="throughput-item"><span class="arrow in">↓</span><span class="value bytes-in">--</span>/s</div>' +
      '<div class="throughput-item"><span class="arrow out">↑</span><span class="value bytes-out">--</span>/s</div>' +
      '</div>' +
      '</div>' +
      '</div>';

    return card;
  }

  // TCP Client Card
  function createTcpClientCard(info) {
    var card = document.createElement('article');
    card.className = 'entity-card tcp-client collapsed';
    card.id = 'tcp-client-' + info.name.replace(/[^a-z0-9]/gi, '-');

    card.innerHTML =
      '<div class="entity-header" onclick="toggleEntityCard(this.parentElement)">' +
      '<div class="entity-status ok"></div>' +
      '<h3 class="entity-name">' + info.name + '</h3>' +
      '<div class="entity-label">Client</div>' +
      '<div class="entity-stats">' +
      '<div class="entity-stat"><div class="entity-stat-value pool-active">--</div><div class="entity-stat-label">Conns</div></div>' +
      '<div class="entity-stat"><div class="entity-stat-value p99">--</div><div class="entity-stat-label">P99</div></div>' +
      '</div>' +
      '<div class="entity-summary">' +
      '<span class="summary-metric conn-count">-- conn</span>' +
      '<span class="summary-metric latency">P99:--</span>' +
      '</div>' +
      '<button class="expand-toggle"><span class="expand-icon">▼</span></button>' +
      '</div>' +
      '<div class="entity-body">' +
      '<div class="entity-section">' +
      '<div class="tcp-pool-bar">' +
      '<div class="tcp-pool-fill" style="width: 0%"></div>' +
      '</div>' +
      '<div class="tcp-pool-stats">' +
      '<span><span class="pool-active">--</span>/<span class="pool-max">--</span> conns</span>' +
      '</div>' +
      '</div>' +
      '<div class="entity-section">' +
      '<div class="latency-row">' +
      '<div class="latency-values">' +
      '<div class="latency-item p50"><span class="label">p50</span><span class="value p50">--</span></div>' +
      '<div class="latency-item p99"><span class="label">p99</span><span class="value p99">--</span></div>' +
      '</div>' +
      '</div>' +
      '</div>' +
      '</div>';

    return card;
  }

  // UDP Socket Card
  function createUdpSocketCard(info) {
    var card = document.createElement('article');
    card.className = 'entity-card udp-socket collapsed';
    card.id = 'udp-' + info.name.replace(/[^a-z0-9]/gi, '-');

    card.innerHTML =
      '<div class="entity-header" onclick="toggleEntityCard(this.parentElement)">' +
      '<div class="entity-status ok"></div>' +
      '<h3 class="entity-name">' + info.name + '</h3>' +
      '<div class="entity-label">UDP</div>' +
      '<div class="entity-stats">' +
      '<div class="entity-stat"><div class="entity-stat-value recv-rate">--/s</div><div class="entity-stat-label">Recv</div></div>' +
      '<div class="entity-stat"><div class="entity-stat-value send-rate">--/s</div><div class="entity-stat-label">Send</div></div>' +
      '</div>' +
      '<div class="entity-summary">' +
      '<span class="summary-metric recv-rate">--/s ↓</span>' +
      '<span class="summary-metric loss-rate">--% loss</span>' +
      '</div>' +
      '<button class="expand-toggle"><span class="expand-icon">▼</span></button>' +
      '</div>' +
      '<div class="entity-body">' +
      '<div class="entity-section">' +
      '<div class="entity-metrics-row">' +
      '<div class="entity-metric"><span class="entity-metric-label">Recv</span><span class="entity-metric-value recv-total">--</span></div>' +
      '<div class="entity-metric"><span class="entity-metric-label">Send</span><span class="entity-metric-value send-total">--</span></div>' +
      '<div class="entity-metric"><span class="entity-metric-label">Drop</span><span class="entity-metric-value dropped warning">--</span></div>' +
      '<div class="entity-metric"><span class="entity-metric-label">Loss</span><span class="entity-metric-value loss-pct">--%</span></div>' +
      '</div>' +
      '</div>' +
      '</div>';

    return card;
  }

  // File I/O Card
  function createFileIOCard(info) {
    var card = document.createElement('article');
    card.className = 'entity-card file-io';
    card.id = 'file-io-ops';

    card.innerHTML =
      '<div class="entity-header">' +
      '<div class="entity-status ok"><span class="status-shape">●</span></div>' +
      '<h3 class="entity-name">Async File Operations</h3>' +
      '</div>' +
      '<div class="entity-body">' +
      '<div class="file-io-grid">' +
      '<div class="file-io-row">' +
      '<span class="file-io-label">Reads</span>' +
      '<span class="file-io-rate" id="file-read-rate">--/s</span>' +
      '<div class="file-io-spark" id="file-read-spark"></div>' +
      '<span class="file-io-throughput" id="file-read-throughput">-- MB/s</span>' +
      '<span class="file-io-latency">P99: <span id="file-read-p99">--</span></span>' +
      '</div>' +
      '<div class="file-io-row">' +
      '<span class="file-io-label">Writes</span>' +
      '<span class="file-io-rate" id="file-write-rate">--/s</span>' +
      '<div class="file-io-spark" id="file-write-spark"></div>' +
      '<span class="file-io-throughput" id="file-write-throughput">-- MB/s</span>' +
      '<span class="file-io-latency">P99: <span id="file-write-p99">--</span></span>' +
      '</div>' +
      '<div class="file-io-row">' +
      '<span class="file-io-label">Fsync</span>' +
      '<span class="file-io-rate" id="file-fsync-rate">--/s</span>' +
      '<div class="file-io-spark" id="file-fsync-spark"></div>' +
      '<span class="file-io-throughput">--</span>' +
      '<span class="file-io-latency">P99: <span id="file-fsync-p99">--</span></span>' +
      '</div>' +
      '</div>' +
      '<div class="file-io-pending">' +
      'Open FDs: <span id="file-open-fds">--</span>' +
      '&nbsp;│&nbsp;' +
      'Pending: <span id="file-pending-reads">--</span> read, ' +
      '<span id="file-pending-writes">--</span> write' +
      '</div>' +
      '</div>';

    return card;
  }

  // Unix Socket Card
  function createUnixSocketCard(info) {
    var card = document.createElement('article');
    card.className = 'entity-card unix-socket collapsed';
    card.id = 'unix-' + info.path.replace(/[^a-z0-9]/gi, '-');

    var typeLabel = info.isStream ? 'stream' : 'dgram';

    card.innerHTML =
      '<div class="entity-header" onclick="toggleEntityCard(this.parentElement)">' +
      '<div class="entity-status ok"><span class="status-shape">●</span></div>' +
      '<h3 class="entity-name">' + info.path + '</h3>' +
      '<div class="entity-label">' + typeLabel + '</div>' +
      '<div class="entity-summary">' +
      '<span class="summary-metric conn-count">-- conn</span>' +
      '<span class="summary-metric ops-rate">--/s</span>' +
      '<span class="summary-metric latency">P99:--</span>' +
      '<div class="summary-spark"></div>' +
      '</div>' +
      '<button class="expand-toggle"><span class="expand-icon">▼</span></button>' +
      '</div>' +
      '<div class="entity-body">' +
      '<div class="entity-section">' +
      '<div class="entity-section-title">Statistics</div>' +
      '<div class="unix-socket-stats">' +
      '<span>Ops: <span class="ops-total">--</span></span>' +
      '<span>Bytes: <span class="bytes-total">--</span></span>' +
      (info.isStream ? '<span>Connections: <span class="conn-count">--</span></span>' : '') +
      '</div>' +
      '</div>' +
      '<div class="entity-section">' +
      '<div class="entity-section-title">Throughput</div>' +
      '<div class="sparkline-container">' +
      '<div class="sparkline unix-throughput-spark"></div>' +
      '</div>' +
      '</div>' +
      '</div>';

    return card;
  }

  // Named Pipe Card
  function createNamedPipeCard(info) {
    var card = document.createElement('article');
    card.className = 'entity-card named-pipe collapsed';
    card.id = 'pipe-' + info.path.replace(/[^a-z0-9]/gi, '-');

    var dirIcon = info.isWriter ? '→' : '←';
    var dirLabel = info.isWriter ? 'writer' : 'reader';

    card.innerHTML =
      '<div class="entity-header" onclick="toggleEntityCard(this.parentElement)">' +
      '<div class="entity-status ok"><span class="status-shape">●</span></div>' +
      '<h3 class="entity-name">' + info.path + '</h3>' +
      '<div class="entity-label">' + dirIcon + ' ' + dirLabel + '</div>' +
      '<div class="entity-summary">' +
      '<span class="summary-metric throughput">-- KB/s</span>' +
      '<div class="summary-spark"></div>' +
      '</div>' +
      '<button class="expand-toggle"><span class="expand-icon">▼</span></button>' +
      '</div>' +
      '<div class="entity-body">' +
      '<div class="entity-section">' +
      '<div class="entity-section-title">Throughput</div>' +
      '<div class="pipe-throughput">' +
      '<span class="pipe-rate">-- KB/s</span>' +
      '<div class="sparkline-container">' +
      '<div class="sparkline pipe-spark"></div>' +
      '</div>' +
      '</div>' +
      '</div>' +
      '<div class="entity-section">' +
      '<div class="entity-section-title">Buffer</div>' +
      '<div class="pipe-buffer-bar">' +
      '<div class="pipe-buffer-fill" style="width: 0%"></div>' +
      '</div>' +
      '<div class="pipe-buffer-label"><span class="buffer-pct">0</span>% full</div>' +
      '</div>' +
      '</div>';

    return card;
  }

  // Helper function to toggle entity card collapse state
  window.toggleEntityCard = function(card) {
    var isCollapsed = card.classList.contains('collapsed');
    card.classList.toggle('collapsed');
    card.setAttribute('aria-expanded', isCollapsed ? 'true' : 'false');

    var icon = card.querySelector('.expand-icon');
    if (icon) {
      icon.textContent = isCollapsed ? '▲' : '▼';
    }

    // Save entity card collapse state to localStorage
    if (card.id) {
      try {
        var prefs = JSON.parse(localStorage.getItem('dashboard-entity-cards') || '{}');
        prefs[card.id] = !isCollapsed; // Store new collapsed state
        localStorage.setItem('dashboard-entity-cards', JSON.stringify(prefs));
      } catch(e) {}
    }
  };

  // Helper to get saved entity card collapse state
  window.getEntityCardCollapsed = function(cardId) {
    try {
      var prefs = JSON.parse(localStorage.getItem('dashboard-entity-cards') || '{}');
      return prefs[cardId] === true;
    } catch(e) { return true; } // Default collapsed
  };

  // Export card creation functions for use by update code
  window.createTcpServerCard = createTcpServerCard;
  window.createTcpClientCard = createTcpClientCard;
  window.createUdpSocketCard = createUdpSocketCard;
  window.createFileIOCard = createFileIOCard;
  window.createUnixSocketCard = createUnixSocketCard;
  window.createNamedPipeCard = createNamedPipeCard;

  // ==================== Keyboard Navigation ====================
  (function() {
    var focusedIndex = -1;
    
    function getEntityCards() {
      return Array.from(document.querySelectorAll('.entity-card'));
    }
    
    function setFocus(index) {
      var cards = getEntityCards();
      if (index < 0 || index >= cards.length) return;
      cards.forEach(function(c) { c.classList.remove('keyboard-focus'); });
      focusedIndex = index;
      cards[index].classList.add('keyboard-focus');
      cards[index].scrollIntoView({ block: 'nearest', behavior: 'smooth' });
    }
    
    function handleKeyDown(e) {
      if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;
      var cards = getEntityCards();
      if (cards.length === 0) return;
      
      switch (e.key) {
        case 'j':
          e.preventDefault();
          setFocus(Math.min(focusedIndex + 1, cards.length - 1));
          break;
        case 'k':
          e.preventDefault();
          setFocus(Math.max(focusedIndex - 1, 0));
          break;
        case ' ':
          e.preventDefault();
          if (focusedIndex >= 0 && cards[focusedIndex]) {
            toggleEntityCard(cards[focusedIndex]);
          }
          break;
        case 'l':
          e.preventDefault();
          if (focusedIndex >= 0 && cards[focusedIndex]) {
            cards[focusedIndex].classList.remove('collapsed');
            cards[focusedIndex].setAttribute('aria-expanded', 'true');
          }
          break;
        case 'h':
          e.preventDefault();
          if (focusedIndex >= 0 && cards[focusedIndex]) {
            cards[focusedIndex].classList.add('collapsed');
            cards[focusedIndex].setAttribute('aria-expanded', 'false');
          }
          break;
        case 'G':
          e.preventDefault();
          setFocus(cards.length - 1);
          break;
        case '?':
          e.preventDefault();
          toggleKeyboardHelp();
          break;
        case 'Escape':
          cards.forEach(function(c) { c.classList.remove('keyboard-focus'); });
          focusedIndex = -1;
          hideKeyboardHelp();
          break;
      }
    }
    
    document.addEventListener('keydown', handleKeyDown);
  })();

  // Keyboard help overlay functions
  window.toggleKeyboardHelp = function() {
    var overlay = document.getElementById('keyboard-help');
    if (!overlay) return;
    var isHidden = overlay.getAttribute('aria-hidden') === 'true';
    overlay.setAttribute('aria-hidden', isHidden ? 'false' : 'true');
    overlay.style.display = isHidden ? 'flex' : 'none';
  };

  window.hideKeyboardHelp = function() {
    var overlay = document.getElementById('keyboard-help');
    if (!overlay) return;
    overlay.setAttribute('aria-hidden', 'true');
    overlay.style.display = 'none';
  };

})();
