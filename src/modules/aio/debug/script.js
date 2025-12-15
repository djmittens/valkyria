// Valkyria Dashboard - Real-time Metrics Visualization
(function() {
  'use strict';

  // ==================== Configuration ====================
  // Sparkline window size in samples (server sends updates every 100ms)
  // 1800 samples = 3 minutes, 600 = 1 minute, 3000 = 5 minutes
  var HISTORY_SAMPLES = 1800;
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
    html += '<span class="pool-widget-name">' + this.name + '</span>';
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

  // Render grid from data
  PoolWidget.prototype._renderGrid = function(data) {
    // Skip rendering if grid is collapsed (save CPU cycles)
    if (this.collapsibleGrid && this.gridCollapsed) return;

    // Only render grid if we have slot-based data (states or bitmap)
    // Don't use byte totals for grid sizing - they're way too large
    if (!data.states && data.bitmap === undefined) return;

    // Use slotTotal for grid sizing (slot count), fall back to total only if reasonable
    var total = data.slotTotal || data.total || 0;
    if (total <= 0 || total > 500000) return;  // Sanity check (256K slab = 262144 slots)

    var container = this.canvasEl.parentElement;
    var containerWidth = container ? container.clientWidth : 0;
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

    // Parse RLE and fill buckets
    var slotIdx = 0;
    var i = 0;
    while (i < rleStr.length && slotIdx < total) {
      var stateChar = rleStr[i++];
      var countStr = '';
      while (i < rleStr.length && rleStr[i] >= '0' && rleStr[i] <= '9') countStr += rleStr[i++];
      var count = parseInt(countStr, 10) || 1;

      var isFree = (stateChar === 'F');

      for (var c = 0; c < count && slotIdx < total; c++, slotIdx++) {
        var bucketIdx = Math.min(Math.floor(slotIdx / slotsPerCell), buckets.length - 1);
        if (isFree) {
          buckets[bucketIdx].free++;
        } else {
          buckets[bucketIdx].used++;
        }
      }
    }

    // Fill remaining slots as free
    while (slotIdx < total) {
      var bucketIdx = Math.min(Math.floor(slotIdx / slotsPerCell), buckets.length - 1);
      buckets[bucketIdx].free++;
      slotIdx++;
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

    // Decode bitmap RLE
    var segments = rleHex ? rleHex.split(',') : [];
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
          var bucketIdx = Math.min(Math.floor(slotIdx / slotsPerCell), buckets.length - 1);
          if ((byteVal >> bit) & 1) {
            buckets[bucketIdx].used++;
          } else {
            buckets[bucketIdx].free++;
          }
        }
      }
    }

    // Fill remaining as free
    while (slotIdx < total) {
      var bucketIdx = Math.min(Math.floor(slotIdx / slotsPerCell), buckets.length - 1);
      buckets[bucketIdx].free++;
      slotIdx++;
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
    loopIterations: []
  };
  var prevMetrics = null;
  var prevTimestamp = null;
  var serverCards = {};  // Track dynamically created server cards
  var currentModular = null;  // Current modular metrics (for event loop etc)

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
    if (!container || !history.p50 || !history.p50.data || history.p50.data.length < 2) {
      if (container) container.innerHTML = '';
      return;
    }

    var opts = options || {};
    var width = opts.width || 120;
    var height = opts.height || 32;

    var allData = history.p50.data.concat(history.p95.data).concat(history.p99.data);
    var max = Math.max.apply(null, allData) || 1;
    var min = 0;

    function pathFor(data, color, strokeWidth) {
      if (!data || data.length < 2) return '';
      var points = data.map(function(v, i) {
        var x = (i / (data.length - 1)) * width;
        var y = height - ((v - min) / (max - min)) * (height - 4) - 2;
        return (i === 0 ? 'M' : 'L') + x.toFixed(1) + ',' + y.toFixed(1);
      }).join(' ');
      return '<path d="' + points + '" fill="none" stroke="' + color + '" stroke-width="' + strokeWidth + '" stroke-linecap="round" stroke-linejoin="round" opacity="0.9"/>';
    }

    container.innerHTML =
      '<svg width="100%" height="100%" viewBox="0 0 ' + width + ' ' + height + '" preserveAspectRatio="none" style="display:block;">' +
      pathFor(history.p99.data, 'var(--color-error)', 1) +
      pathFor(history.p95.data, 'var(--color-warning)', 1.2) +
      pathFor(history.p50.data, 'var(--color-ok)', 1.5) +
      '</svg>';
  }

  // Render stacked bar sparkline showing 2xx/4xx/5xx status codes over time
  function renderStatusCodeSparkline(container, history, options) {
    if (!container || !history || history.length < 2) {
      if (container) container.innerHTML = '';
      return;
    }

    var opts = options || {};
    var width = opts.width || 60;
    var height = opts.height || 20;
    var barWidth = Math.max(2, width / history.length);

    var bars = history.map(function(d, i) {
      var total = d.s2xx + d.s4xx + d.s5xx;
      if (total === 0) return '';

      var x = i * barWidth;
      var h2xx = (d.s2xx / total) * height;
      var h4xx = (d.s4xx / total) * height;
      var h5xx = (d.s5xx / total) * height;

      var y2xx = 0;
      var y4xx = h2xx;
      var y5xx = h2xx + h4xx;

      return '<g>' +
        '<rect x="' + x + '" y="' + y2xx + '" width="' + Math.max(1, barWidth - 0.5) + '" height="' + h2xx + '" fill="var(--color-ok)"/>' +
        '<rect x="' + x + '" y="' + y4xx + '" width="' + Math.max(1, barWidth - 0.5) + '" height="' + h4xx + '" fill="var(--color-warning)"/>' +
        '<rect x="' + x + '" y="' + y5xx + '" width="' + Math.max(1, barWidth - 0.5) + '" height="' + h5xx + '" fill="var(--color-error)"/>' +
        '</g>';
    }).join('');

    container.innerHTML = '<svg width="100%" height="100%" viewBox="0 0 ' + width + ' ' + height + '" style="display:block;">' + bars + '</svg>';
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
    backpressure: function(id) {
      return new PoolWidget({
        id: id + '-backpressure',
        name: 'Backpressure',
        preset: 'queue',
        variant: 'compact',
        showGauge: true,
        showGrid: false,
        warningThreshold: 30,
        criticalThreshold: 70,
        color: '#f0883e',  // Orange for backpressure
        colorMuted: 'rgba(240, 136, 62, 0.3)',
        stats: [
          { id: 'pending', label: 'queued:' },
          { id: 'processed', label: '✓', suffix: '' },
          { id: 'dropped', label: '✗', suffix: '' },
          { id: 'avgwait', label: 'avg:', suffix: 'ms' }
        ]
      });
    }
  };

  function createAioSystemPanel(sys, index) {
    var name = sys.name || 'System ' + (index + 1);
    var id = 'aio-sys-' + index;

    // Create slab widgets and pool gauges for this AIO system
    var widgets = {
      handles: AIO_SLAB_CONFIGS.handles(id),
      tcp_buffers: AIO_SLAB_CONFIGS.tcp_buffers(id),
      stream_arenas: AIO_SLAB_CONFIGS.stream_arenas(id),
      queue: AIO_SLAB_CONFIGS.queue(id),
      backpressure: AIO_SLAB_CONFIGS.backpressure(id)
    };

    var html =
      '<article class="panel aio-system-panel aio-expanded" id="' + id + '" aria-labelledby="' + id + '-title">' +
        '<div class="panel-header">' +
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
              // Backpressure queue gauge (pending streams waiting for arenas)
              widgets.backpressure.render() +
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

    // Update backpressure PoolWidget (pending streams waiting for arenas)
    var bp = sys.backpressure || {};
    if (panel._slabWidgets && panel._slabWidgets.backpressure) {
      var bpCurrent = bp.pending_current || 0;
      var bpPoolSize = bp.pool_size || 64;
      var bpProcessed = bp.processed || 0;
      var bpDropped = bp.dropped || 0;
      var bpAvgWait = bp.avg_wait_ms || 0;

      panel._slabWidgets.backpressure.update({
        used: bpCurrent,
        total: bpPoolSize,
        stats: {
          pending: bpCurrent,
          processed: fmtCompact(bpProcessed),
          dropped: bpDropped,
          avgwait: bpAvgWait.toFixed(1)
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
    card.className = 'entity-card collapsed';
    card.id = 'server-' + serverInfo.key.replace(/[:.]/g, '-');
    card.setAttribute('tabindex', '0');
    card.setAttribute('role', 'article');
    card.setAttribute('aria-expanded', 'false');

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
        <button class="expand-toggle" onclick="toggleEntityCard(this.closest('.entity-card'))" aria-label="Toggle details"><span class="expand-icon">▼</span></button>
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

    // Render header sparklines
    var reqRateSpark = card.querySelector('.req-rate-spark');
    if (reqRateSpark && hist.reqRate.data.length >= 2) {
      renderMiniSparkline(reqRateSpark, hist.reqRate.toArray().slice(-20), {
        color: 'var(--color-info)',
        width: 40,
        height: 14
      });
    }

    var latencySpark = card.querySelector('.latency-spark');
    if (latencySpark && hist.p99.data.length >= 2) {
      renderMiniSparkline(latencySpark, hist.p99.toArray().slice(-20), {
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

    // Render large status code sparkline
    var statusSparkLarge = card.querySelector('.status-code-spark-large');
    if (statusSparkLarge && hist.statusCodes.data.length >= 2) {
      renderStatusCodeSparkline(statusSparkLarge, hist.statusCodes.toArray(), {
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

    // Render large latency trend sparkline
    var latencyTrendLarge = card.querySelector('.latency-trend-spark-large');
    if (latencyTrendLarge && hist.p50.data.length >= 2) {
      renderPercentileSparkline(latencyTrendLarge, hist, { width: 160, height: 40 });
    }

    // Update throughput
    var bytesInRate = deltaSeconds > 0 ? (bytesRecv - hist.prevBytesIn) / deltaSeconds : 0;
    var bytesOutRate = deltaSeconds > 0 ? (bytesSent - hist.prevBytesOut) / deltaSeconds : 0;

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

    // Render throughput sparkline
    var throughputSparkLarge = card.querySelector('.throughput-spark-large');
    if (throughputSparkLarge && hist.bytesIn.data.length >= 2) {
      renderThroughputSparkline(throughputSparkLarge, hist.bytesIn.toArray(), hist.bytesOut.toArray(), {
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

    // Render concurrency sparkline
    var concurrencySparkLarge = card.querySelector('.concurrency-spark-large');
    if (concurrencySparkLarge && hist.conns.data.length >= 2) {
      renderConcurrencySparkline(concurrencySparkLarge, hist.conns.toArray(), hist.sse.toArray(), {
        width: 160,
        height: 32
      });
    }
  }

  // Render throughput sparkline (dual line: in/out)
  function renderThroughputSparkline(container, bytesIn, bytesOut, options) {
    if (!container || !bytesIn || bytesIn.length < 2) {
      if (container) container.innerHTML = '';
      return;
    }

    var opts = options || {};
    var width = opts.width || 160;
    var height = opts.height || 32;

    var allData = bytesIn.concat(bytesOut || []);
    var max = Math.max.apply(null, allData) || 1;

    function pathFor(data, color, dashArray) {
      if (!data || data.length < 2) return '';
      var points = data.map(function(v, i) {
        var x = (i / (data.length - 1)) * width;
        var y = height - 2 - ((v / max) * (height - 4));
        return (i === 0 ? 'M' : 'L') + x.toFixed(1) + ',' + y.toFixed(1);
      }).join(' ');
      var dash = dashArray ? ' stroke-dasharray="' + dashArray + '"' : '';
      return '<path d="' + points + '" fill="none" stroke="' + color + '" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" opacity="0.9"' + dash + '/>';
    }

    // Area fill for in
    var areaPoints = bytesIn.map(function(v, i) {
      var x = (i / (bytesIn.length - 1)) * width;
      var y = height - 2 - ((v / max) * (height - 4));
      return x.toFixed(1) + ',' + y.toFixed(1);
    }).join(' ');
    areaPoints += ' ' + width + ',' + (height - 2) + ' 0,' + (height - 2);

    container.innerHTML =
      '<svg width="100%" height="100%" viewBox="0 0 ' + width + ' ' + height + '" preserveAspectRatio="none" style="display:block;">' +
      '<polygon points="' + areaPoints + '" fill="var(--color-ok)" opacity="0.15"/>' +
      pathFor(bytesIn, 'var(--color-ok)', null) +
      pathFor(bytesOut, 'var(--color-info)', '3,2') +
      '</svg>';
  }

  // Render concurrency sparkline (connections + SSE)
  function renderConcurrencySparkline(container, conns, sse, options) {
    if (!container || !conns || conns.length < 2) {
      if (container) container.innerHTML = '';
      return;
    }

    var opts = options || {};
    var width = opts.width || 160;
    var height = opts.height || 32;

    var allData = conns.concat(sse || []);
    var max = Math.max.apply(null, allData) || 1;

    function areaFor(data, color) {
      if (!data || data.length < 2) return '';
      var points = data.map(function(v, i) {
        var x = (i / (data.length - 1)) * width;
        var y = height - 2 - ((v / max) * (height - 4));
        return x.toFixed(1) + ',' + y.toFixed(1);
      }).join(' ');
      points += ' ' + width + ',' + (height - 2) + ' 0,' + (height - 2);
      return '<polygon points="' + points + '" fill="' + color + '" opacity="0.3"/>';
    }

    function lineFor(data, color) {
      if (!data || data.length < 2) return '';
      var points = data.map(function(v, i) {
        var x = (i / (data.length - 1)) * width;
        var y = height - 2 - ((v / max) * (height - 4));
        return (i === 0 ? 'M' : 'L') + x.toFixed(1) + ',' + y.toFixed(1);
      }).join(' ');
      return '<path d="' + points + '" fill="none" stroke="' + color + '" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/>';
    }

    var hasSSE = sse && sse.some(function(v) { return v > 0; });

    container.innerHTML =
      '<svg width="100%" height="100%" viewBox="0 0 ' + width + ' ' + height + '" preserveAspectRatio="none" style="display:block;">' +
      areaFor(conns, 'var(--color-purple)') +
      lineFor(conns, 'var(--color-purple)') +
      (hasSSE ? areaFor(sse, 'var(--color-cyan)') + lineFor(sse, 'var(--color-cyan)') : '') +
      '</svg>';
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

    // Render mini sparklines
    renderMiniSparklineLegacy('spark-request-rate', history.requestRate.slice(-20), 'var(--color-info)');
    renderMiniSparklineLegacy('spark-error-rate', history.errorRate.slice(-20), 'var(--color-warning)');
    renderMiniSparklineLegacy('spark-latency', history.latency.slice(-20), 'var(--color-cyan)');
    renderMiniSparklineLegacy('spark-heap', history.heapUsage.slice(-20), 'var(--color-ok)');

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

    // Update GC panel summary (for collapsed state)
    var gcSummary = $('gc-summary');
    if (gcSummary) {
      gcSummary.textContent = fmtCompact(gc.cycles_total || 0) + ' cycles, ' +
        fmt((gc.pause_us_max || 0) / 1000, 1) + 'ms max, ' +
        fmtBytes(gc.reclaimed_bytes_total || 0) + ' reclaimed';
    }

    // Track GC pauses for timeline
    if (prevMetrics && gc.cycles_total > prevMetrics.gcCycles) {
      var pauseMs = (gc.pause_us_max || 0) / 1000;
      history.gcPauses.push({ pause: pauseMs, timestamp: now });
      while (history.gcPauses.length > HISTORY_SAMPLES) history.gcPauses.shift();
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

    // Update Interpreter panel summary (for collapsed state)
    var interpSummary = $('interp-summary');
    if (interpSummary) {
      interpSummary.textContent = fmtCompact(interp.evals_total || 0) + ' evals, ' +
        fmtCompact(interp.function_calls || 0) + ' fn calls';
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
  var lvalSlabTierGauge = null;
  var lenvSlabTierGauge = null;
  var mallocTierGauge = null;

  function init() {
    showLoadingState();

    // Initialize PoolWidgets for memory visualization (includes LVAL grid in slab tier)
    initPoolWidgets();
  }

  // Initialize PoolWidgets for GC heap tiers (arenas are created dynamically)
  function initPoolWidgets() {
    // GC Heap Tiers (LVAL Slab + LENV Slab + Malloc)
    var heapContainer = document.getElementById('heap-tiers-container');
    if (heapContainer) {
      // LVAL Slab Tier PoolWidget (includes LVAL grid)
      lvalSlabTierGauge = new PoolWidget({
        id: 'lval-slab-tier-gauge',
        name: 'LVAL Slab',
        slabKey: 'lval',
        icon: 'V',
        preset: 'slab',
        variant: 'compact',
        showGauge: true,
        showGrid: true,
        collapsibleGrid: true,
        markers: PoolWidget.Markers.heapMarkers({
          hwmFormat: 'count', hwmLabelSuffix: ' obj',
          thresholdLabel: 'gc', thresholdPosition: 75
        }),
        stats: [
          { id: 'objects', label: 'lvals:' },
          { id: 'hwm', label: 'hwm:', suffix: '%' }
        ]
      });

      // LENV Slab Tier PoolWidget (for environments)
      lenvSlabTierGauge = new PoolWidget({
        id: 'lenv-slab-tier-gauge',
        name: 'LENV Slab',
        slabKey: 'lenv',
        icon: 'E',
        preset: 'slab',
        variant: 'compact',
        showGauge: true,
        showGrid: true,
        collapsibleGrid: true,
        markers: PoolWidget.Markers.heapMarkers({
          hwmFormat: 'count', hwmLabelSuffix: ' env',
          thresholdLabel: 'gc', thresholdPosition: 75
        }),
        stats: [
          { id: 'objects', label: 'envs:' },
          { id: 'hwm', label: 'hwm:', suffix: '%' }
        ]
      });

      // Malloc PoolWidget (no grid - uses trend indicator instead)
      mallocTierGauge = new PoolWidget({
        id: 'malloc-tier-gauge',
        name: 'Malloc',
        icon: 'M',
        preset: 'malloc',
        variant: 'compact',
        showGauge: true,
        showGrid: false,
        showTrend: true,
        markers: PoolWidget.Markers.heapMarkers({
          hwmFormat: 'bytes',
          thresholdLabel: 'gc', thresholdPosition: 75
        }),
        stats: [
          { id: 'peak', label: 'peak:' },
          { id: 'hwm', label: 'hwm:', suffix: '%' }
        ]
      });

      heapContainer.innerHTML = lvalSlabTierGauge.render() + lenvSlabTierGauge.render() + mallocTierGauge.render();
      lvalSlabTierGauge.bind();
      lenvSlabTierGauge.bind();
      mallocTierGauge.bind();

      // Register slab tiers for grid updates
      PoolWidget.register('lval', lvalSlabTierGauge);
      PoolWidget.register('lenv', lenvSlabTierGauge);
    }
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
        metrics: null
      };

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
            metrics: data.metrics
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
              } else {
                // New histogram, add it with labels
                if (!mod.histograms) mod.histograms = [];
                mod.histograms.push({ name: d.n, count: d.c || 0, sum_us: d.s || 0, labels: d.l || {} });
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
      }

      // Update capacity warning banner
      this.updateCapacityWarnings(warnings, critical);
    }

    // Update process memory overview widget
    updateProcessMemory(process, breakdown, smaps) {
      var rss = process.rss || 0;
      var vms = process.vms || 0;
      var systemTotal = process.system_total || 0;

      // Update inline gauge (memory pressure: RSS as % of system RAM)
      var pct = systemTotal > 0 ? (rss / systemTotal) * 100 : 0;
      var fillEl = document.getElementById('process-gauge-fill');
      if (fillEl) fillEl.style.width = Math.min(pct, 100) + '%';

      // Update RSS and VMS text displays
      var rssEl = document.getElementById('process-rss-text');
      if (rssEl) rssEl.textContent = fmtBytes(rss);

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

      // VMS determines total bar width - segment widths are capacity as % of VMS
      var runtimeWidthPct = vms > 0 ? (runtimeCap / vms) * 100 : 0;
      var aioWidthPct = vms > 0 ? (aioCap / vms) * 100 : 0;
      var metricsWidthPct = vms > 0 ? (metricsCap / vms) * 100 : 0;
      var unregisteredWidthPct = vms > 0 ? (unregisteredReserved / vms) * 100 : 0;

      // Calculate fill percentages (used as % of capacity = resident as % of reserved)
      var runtimeFillPct = runtimeCap > 0 ? (runtimeUsed / runtimeCap) * 100 : 0;
      var aioFillPct = aioCap > 0 ? (aioUsed / aioCap) * 100 : 0;
      var metricsFillPct = metricsCap > 0 ? (metricsUsed / metricsCap) * 100 : 0;
      var unregisteredFillPct = unregisteredReserved > 0 ? (unregistered / unregisteredReserved) * 100 : 0;

      // Update stacked bar segment widths (based on capacity as % of VMS)
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
      this.updateLegendItemWithCap('other', unregistered, unregisteredReserved, unregisteredFillPct);

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
      if (smaps && smaps.total > 0) {
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
          }
        };

        // Create an AIO system entry for the systems array
        // Note: event_loop metrics come from modular metrics (loop={name} label)
        dashboardData.aio_systems = [{
          name: 'main',
          uptime_seconds: aio.uptime_seconds || 0,
          system: dashboardData.aio_metrics.system,
          connections: dashboardData.aio_metrics.connections,
          queue: dashboardData.aio_metrics.queue
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
      // Update tiered heap display (supports generic tiers array format)
      if (gc.tiers && gc.tiers.length > 0) {
        this.updateTieredHeap(gc);
      }

      // Update GC panel if it exists (legacy)
      var gcPanel = document.querySelector('.gc-stats-panel');
      if (gcPanel) {
        var allocated = gcPanel.querySelector('[data-gc="allocated"]');
        var peak = gcPanel.querySelector('[data-gc="peak"]');
        var cycles = gcPanel.querySelector('[data-gc="cycles"]');

        // For legacy panel, show combined bytes from all tiers
        var totalUsed = 0;
        if (gc.tiers) {
          for (var i = 0; i < gc.tiers.length; i++) {
            totalUsed += gc.tiers[i].bytes_used || 0;
          }
        }
        if (allocated) allocated.textContent = this.formatBytes(totalUsed);
        if (cycles) cycles.textContent = gc.cycles.toLocaleString();
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
      // Generic tier-based update - find tiers by name
      var tiers = gc.tiers || [];
      var lvalTier = this.findTier(tiers, 'lval') || {};
      var lenvTier = this.findTier(tiers, 'lenv') || {};
      var mallocTier = this.findTier(tiers, 'malloc') || {};

      // LVAL slab metrics
      var lvalSlabUsed = lvalTier.bytes_used || 0;
      var lvalSlabTotal = lvalTier.bytes_total || 1;
      var lvalObjUsed = lvalTier.objects_used || 0;
      var lvalObjTotal = lvalTier.objects_total || 1;
      var lvalSlabPeakObjects = lvalTier.objects_peak || 0;
      var lvalSlabHwmPct = lvalObjTotal > 0 ? (lvalSlabPeakObjects / lvalObjTotal) * 100 : 0;

      // LENV slab metrics
      var lenvSlabUsed = lenvTier.bytes_used || 0;
      var lenvSlabTotal = lenvTier.bytes_total || 1;
      var lenvObjUsed = lenvTier.objects_used || 0;
      var lenvObjTotal = lenvTier.objects_total || 1;
      var lenvSlabPeakObjects = lenvTier.objects_peak || 0;
      var lenvSlabHwmPct = lenvObjTotal > 0 ? (lenvSlabPeakObjects / lenvObjTotal) * 100 : 0;

      // Malloc metrics
      var mallocUsed = mallocTier.bytes_used || 0;
      var mallocLimit = mallocTier.bytes_total || 1;
      var mallocPeakBytes = mallocTier.bytes_peak || 0;
      var mallocHwmPct = mallocLimit > 0 ? (mallocPeakBytes / mallocLimit) * 100 : 0;

      // Combined totals for header
      var totalUsed = lvalSlabUsed + lenvSlabUsed + mallocUsed;
      var totalCapacity = lvalSlabTotal + lenvSlabTotal + mallocLimit;
      var totalPct = totalCapacity > 0 ? (totalUsed / totalCapacity) * 100 : 0;

      var thresholdPct = gc.threshold_pct || 75;

      // Update LVAL Slab Tier PoolWidget
      if (lvalSlabTierGauge) {
        lvalSlabTierGauge.warningThreshold = thresholdPct;
        lvalSlabTierGauge.update({
          used: lvalSlabUsed,
          total: lvalSlabTotal,
          usedFormatted: fmtBytes(lvalSlabUsed),
          totalFormatted: fmtBytes(lvalSlabTotal),
          markers: {
            hwm: { position: lvalSlabHwmPct, value: lvalSlabPeakObjects },
            threshold: { position: thresholdPct, value: thresholdPct }
          },
          stats: {
            objects: lvalObjUsed.toLocaleString() + '/' + lvalObjTotal.toLocaleString(),
            hwm: Math.round(lvalSlabHwmPct)
          }
        });
      }

      // Update LENV Slab Tier PoolWidget
      if (lenvSlabTierGauge) {
        lenvSlabTierGauge.warningThreshold = thresholdPct;
        lenvSlabTierGauge.update({
          used: lenvSlabUsed,
          total: lenvSlabTotal,
          usedFormatted: fmtBytes(lenvSlabUsed),
          totalFormatted: fmtBytes(lenvSlabTotal),
          markers: {
            hwm: { position: lenvSlabHwmPct, value: lenvSlabPeakObjects },
            threshold: { position: thresholdPct, value: thresholdPct }
          },
          stats: {
            objects: lenvObjUsed.toLocaleString() + '/' + lenvObjTotal.toLocaleString(),
            hwm: Math.round(lenvSlabHwmPct)
          }
        });
      }

      // Update Malloc Tier PoolWidget
      if (mallocTierGauge) {
        mallocTierGauge.warningThreshold = thresholdPct;
        mallocTierGauge.update({
          used: mallocUsed,
          total: mallocLimit,
          usedFormatted: fmtBytes(mallocUsed),
          totalFormatted: fmtBytes(mallocLimit),
          markers: {
            hwm: { position: mallocHwmPct, value: mallocPeakBytes },
            threshold: { position: thresholdPct, value: thresholdPct }
          },
          stats: {
            peak: fmtBytes(mallocPeakBytes),
            hwm: Math.round(mallocHwmPct)
          }
        });
      }

      // Update combined heap stats in header
      var heapUsedEl = $('heap-used');
      var heapTotalEl = $('heap-total');
      var heapGaugeValue = $('heap-gauge-value');

      if (heapUsedEl) heapUsedEl.textContent = fmtBytes(totalUsed);
      if (heapTotalEl) heapTotalEl.textContent = fmtBytes(totalCapacity);
      if (heapGaugeValue) heapGaugeValue.textContent = Math.round(totalPct);

      // Update aggregate stats
      var gcThresholdPctEl = $('gc-threshold-pct');
      if (gcThresholdPctEl) gcThresholdPctEl.textContent = thresholdPct;
      // heap-reclaimed is updated elsewhere from vm_metrics.gc_reclaimed_bytes
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
