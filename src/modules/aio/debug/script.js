// Valkyria Debug Dashboard - Hierarchical View
(function() {
  var POLL = 1000;
  var $ = function(id) { return document.getElementById(id); };

  // Formatters
  function fmt(n, d) { return (n || 0).toFixed(d === undefined ? 0 : d); }
  function fmtUp(s) {
    var d = Math.floor(s / 86400), h = Math.floor((s % 86400) / 3600);
    var m = Math.floor((s % 3600) / 60), sec = Math.floor(s % 60);
    if (d) return d + 'd ' + h + 'h ' + m + 'm';
    if (h) return h + 'h ' + m + 'm ' + sec + 's';
    if (m) return m + 'm ' + sec + 's';
    return sec + 's';
  }
  function fmtB(b) {
    if (b < 1024) return b + ' B';
    if (b < 1048576) return (b / 1024).toFixed(1) + ' KB';
    if (b < 1073741824) return (b / 1048576).toFixed(1) + ' MB';
    return (b / 1073741824).toFixed(2) + ' GB';
  }
  function fmtR(kbps) {
    if (kbps < 1) return (kbps * 1024).toFixed(0) + ' B/s';
    if (kbps < 1024) return kbps.toFixed(1) + ' KB/s';
    return (kbps / 1024).toFixed(1) + ' MB/s';
  }
  function fmtUs(us) {
    if (!us || us === 0) return '0';
    if (us < 1000) return us + 'µs';
    if (us < 1000000) return (us / 1000).toFixed(1) + 'ms';
    return (us / 1000000).toFixed(2) + 's';
  }

  // Build a row element
  function row(l, v, c) {
    return '<div class="row"><span class="lbl">' + l + '</span><span class="val' + (c ? ' ' + c : '') + '">' + v + '</span></div>';
  }

  // Build a node header
  function nodeHdr(lvl, icon, name, tags, value, valClass) {
    var html = '<div class="node-hdr lvl' + lvl + '">';
    html += '<span class="node-icon">' + icon + '</span>';
    html += '<span class="node-name">' + name + '</span>';
    if (tags) {
      for (var i = 0; i < tags.length; i++) {
        html += '<span class="node-tag ' + (tags[i].cls || '') + '">' + tags[i].text + '</span>';
      }
    }
    if (value !== undefined) {
      html += '<span class="node-val' + (valClass ? ' ' + valClass : '') + '">' + value + '</span>';
    }
    html += '</div>';
    return html;
  }

  // Find metrics by name and optional label filter
  function findMetric(arr, name, labels) {
    for (var i = 0; i < arr.length; i++) {
      if (arr[i].name !== name) continue;
      if (!labels) return arr[i];
      var match = true;
      for (var k in labels) {
        if (arr[i].labels[k] !== labels[k]) { match = false; break; }
      }
      if (match) return arr[i];
    }
    return null;
  }

  function findCounter(arr, name, labels) {
    var m = findMetric(arr, name, labels);
    return m ? m.value : 0;
  }

  // Group metrics by server:port
  function groupByServer(mod) {
    var servers = {};
    var counters = mod.counters || [];
    var gauges = mod.gauges || [];
    var histograms = mod.histograms || [];

    // Collect unique server:port combinations
    function addServer(labels) {
      if (!labels || !labels.server || !labels.port) return;
      var key = labels.server + ':' + labels.port;
      if (!servers[key]) {
        servers[key] = { server: labels.server, port: labels.port, counters: [], gauges: [], histograms: [] };
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

  // Render VM metrics section (GC and Interpreter only - Event Loop is part of AIO)
  function renderVmMetrics(vm) {
    if (!vm) return '';

    var gc = vm.gc || {};
    var interp = vm.interpreter || {};

    var html = '';

    // Garbage Collector section
    html += '<div class="node">';
    html += nodeHdr(1, 'G', 'Garbage Collector', null,
      (gc.cycles_total || 0) + ' cycles, ' + fmtUs(gc.pause_us_max));

    html += '<div class="sub-grid">';

    html += '<div class="sub-card">';
    html += '<h3>GC Cycles</h3>';
    html += row('Total Cycles', gc.cycles_total || 0);
    html += row('Total Pause', fmtUs(gc.pause_us_total));
    html += row('Max Pause', fmtUs(gc.pause_us_max));
    html += row('Avg Pause', gc.pause_ms_avg ? gc.pause_ms_avg.toFixed(2) + 'ms' : '0');
    html += '</div>';

    html += '<div class="sub-card">';
    html += '<h3>Heap Memory</h3>';
    html += row('Used', fmtB(gc.heap_used_bytes));
    html += row('Total', fmtB(gc.heap_total_bytes));
    html += row('Utilization', (gc.heap_utilization_pct || 0).toFixed(1) + '%');
    html += row('Reclaimed', fmtB(gc.reclaimed_bytes_total));
    html += '</div>';

    html += '</div>'; // sub-grid
    html += '</div>'; // node

    // Interpreter section
    html += '<div class="node">';
    html += nodeHdr(1, 'I', 'Interpreter', null,
      (interp.evals_total || 0) + ' evals, depth ' + (interp.stack_depth_max || 0));

    html += '<div class="sub-grid">';

    html += '<div class="sub-card">';
    html += '<h3>Evaluations</h3>';
    html += row('Total Evals', interp.evals_total || 0);
    html += row('Function Calls', interp.function_calls || 0);
    html += row('Builtin Calls', interp.builtin_calls || 0);
    html += '</div>';

    html += '<div class="sub-card">';
    html += '<h3>Stack & Closures</h3>';
    html += row('Max Stack Depth', interp.stack_depth_max || 0);
    html += row('Closures Created', interp.closures_created || 0);
    html += row('Env Lookups', interp.env_lookups || 0);
    html += '</div>';

    html += '</div>'; // sub-grid
    html += '</div>'; // node

    return html;
  }

  function render(d) {
    var aio = d.aio_metrics || {};
    var mod = d.modular_metrics || {};
    var vm = d.vm_metrics || {};
    var uptime = aio.uptime_seconds || mod.uptime_seconds || 0;
    var c = aio.connections || {};
    var s = aio.streams || {};
    var b = aio.bytes || {};

    var html = '';

    // Level 0: VM
    html += '<div class="node">';
    html += nodeHdr(0, 'V', 'Valkyria VM', null, fmtUp(uptime), 'grn');
    html += '</div>';

    // Level 1: AIO System (servers, clients, handles, pools, event loop)
    var sys = aio.system || {};
    var loop = vm.event_loop || {};
    html += '<div class="node">';
    html += nodeHdr(1, 'A', 'Async I/O', null, (sys.servers || 0) + ' srv, ' + (loop.iterations || 0) + ' iters');

    // AIO system-wide stats sub-grid
    html += '<div class="sub-grid" style="margin-left: 32px;">';

    // Resources card
    html += '<div class="sub-card">';
    html += '<h3>Resources</h3>';
    html += row('Servers', sys.servers || 0, sys.servers > 0 ? 'grn' : '');
    html += row('Clients', sys.clients || 0);
    html += row('Handles', sys.handles || 0);
    html += '</div>';

    // Memory Pools card
    html += '<div class="sub-card">';
    html += '<h3>Memory Pools</h3>';
    html += row('Stream Arenas', (sys.arenas_used || 0) + '/' + (sys.arenas_total || 0));
    html += row('TCP Buffers', (sys.tcp_buffers_used || 0) + '/' + (sys.tcp_buffers_total || 0));
    html += '</div>';

    // Event Loop card (libuv metrics)
    html += '<div class="sub-card">';
    html += '<h3>Event Loop</h3>';
    html += row('Iterations', loop.iterations || 0);
    html += row('Events', loop.events_processed || 0);
    html += row('Idle Time', fmtUs(loop.idle_time_us));
    html += '</div>';

    // Queue Status card
    html += '<div class="sub-card">';
    html += '<h3>Queue Status</h3>';
    html += row('Queue Depth', sys.queue_depth || 0);
    html += row('Pending Reqs', sys.pending_requests || 0);
    html += row('Pending Resp', sys.pending_responses || 0);
    html += '</div>';

    html += '</div>'; // sub-grid
    html += '</div>'; // node

    // Level 1: VM Metrics (GC and Interpreter - Event Loop is inside AIO)
    html += renderVmMetrics(vm);

    // Level 1: Servers (grouped by server:port from modular metrics)
    var servers = groupByServer(mod);
    for (var key in servers) {
      var srv = servers[key];

      html += '<div class="node">';
      html += nodeHdr(1, 'S', 'HTTP Server', [
        { text: srv.server, cls: 'server' },
        { text: ':' + srv.port, cls: 'port' }
      ], (c.active || 0) + ' conn', c.active > 0 ? 'grn' : '');

      // Sub-sections for this server
      html += '<div class="sub-grid">';

      // Connections card
      html += '<div class="sub-card">';
      html += '<h3>Connections</h3>';
      html += row('Active', c.active || 0, c.active > 0 ? 'grn' : '');
      html += row('Total', c.total || 0);
      html += row('Failed', c.failed || 0, c.failed > 0 ? 'red' : '');
      html += '</div>';

      // Streams card
      html += '<div class="sub-card">';
      html += '<h3>Streams</h3>';
      html += row('Active', s.active || 0, s.active > 0 ? 'grn' : '');
      html += row('Total', s.total || 0);
      html += '</div>';

      // HTTP Requests card
      var req2xx = findCounter(srv.counters, 'http_requests_total', {status: '2xx'});
      var req4xx = findCounter(srv.counters, 'http_requests_total', {status: '4xx'});
      var req5xx = findCounter(srv.counters, 'http_requests_total', {status: '5xx'});
      var reqTotal = findCounter(srv.counters, 'http_requests_total', {});
      if (reqTotal === 0) reqTotal = req2xx + req4xx + req5xx;

      html += '<div class="sub-card">';
      html += '<h3>HTTP Requests</h3>';
      html += row('Total', reqTotal);
      html += row('2xx Success', req2xx, req2xx > 0 ? 'grn' : '');
      html += row('4xx Client Err', req4xx, req4xx > 0 ? 'ylw' : '');
      html += row('5xx Server Err', req5xx, req5xx > 0 ? 'red' : '');
      html += '</div>';

      // Traffic card
      var bytesSent = findCounter(srv.counters, 'http_bytes_sent_total', {});
      var bytesRecv = findCounter(srv.counters, 'http_bytes_recv_total', {});

      html += '<div class="sub-card">';
      html += '<h3>Traffic</h3>';
      html += row('Sent', fmtB(bytesSent));
      html += row('Received', fmtB(bytesRecv));
      html += row('Send Rate', fmtR(b.sent_rate_kbps || 0), 'blu');
      html += row('Recv Rate', fmtR(b.recv_rate_kbps || 0), 'blu');
      html += '</div>';

      // Latency card
      var hist = srv.histograms.length > 0 ? srv.histograms[0] : null;
      var avgMs = hist && hist.count > 0 ? (hist.sum * 1000 / hist.count) : 0;

      html += '<div class="sub-card">';
      html += '<h3>Latency</h3>';
      html += row('Avg Response', fmt(avgMs, 2) + ' ms');
      html += row('Request Count', hist ? hist.count : 0);
      html += row('Total Time', fmt(hist ? hist.sum * 1000 : 0, 1) + ' ms');
      html += '</div>';

      html += '</div>'; // sub-grid
      html += '</div>'; // node
    }

    // If no servers found, show placeholder
    if (Object.keys(servers).length === 0) {
      html += '<div class="node">';
      html += nodeHdr(1, 'S', 'HTTP Server', [{ text: 'none', cls: '' }]);
      html += '<div class="metrics lvl1">';
      html += row('Status', 'No servers registered');
      html += '</div>';
      html += '</div>';
    }

    $('tree').innerHTML = html;
    $('ts').textContent = new Date().toLocaleTimeString();
    $('st').className = 'dot';
    $('err').style.display = 'none';
  }

  function showErr(msg) {
    $('err').textContent = msg;
    $('err').style.display = 'block';
    $('st').className = 'dot err';
  }

  function poll() {
    fetch('/debug/metrics')
      .then(function(r) { return r.json(); })
      .then(render)
      .catch(function(e) { showErr(e.message); });
  }

  poll();
  setInterval(poll, POLL);
})();
