// Valkyria AIO Debug Dashboard

(function() {
  var POLL_INTERVAL_MS = 1000;
  var METRICS_ENDPOINT = '/debug/metrics';

  function metric(label, value) {
    return '<div class="metric"><div class="metric-label">' + label + '</div><div class="metric-value">' + value + '</div></div>';
  }

  function formatUptime(seconds) {
    var d = Math.floor(seconds / 86400);
    var h = Math.floor((seconds % 86400) / 3600);
    var m = Math.floor((seconds % 3600) / 60);
    var s = Math.floor(seconds % 60);
    return (d ? d + 'd ' : '') + (h ? h + 'h ' : '') + (m ? m + 'm ' : '') + s + 's';
  }

  function formatBytes(bytes) {
    if (bytes < 1024) return bytes + ' B';
    if (bytes < 1048576) return (bytes / 1024).toFixed(1) + ' KB';
    return (bytes / 1048576).toFixed(1) + ' MB';
  }

  function formatRate(kbps) {
    if (kbps < 1) return (kbps * 1024).toFixed(0) + ' B/s';
    if (kbps < 1024) return kbps.toFixed(1) + ' KB/s';
    return (kbps / 1024).toFixed(1) + ' MB/s';
  }

  function renderMetrics(data) {
    var c = data.connections || {};
    var s = data.streams || {};
    var r = data.requests || {};
    var b = data.bytes || {};

    document.getElementById('sys').innerHTML = metric('Uptime', formatUptime(data.uptime_seconds));
    document.getElementById('conn').innerHTML = metric('Total', c.total || 0) + metric('Active', c.active || 0) + metric('Failed', c.failed || 0);
    document.getElementById('strm').innerHTML = metric('Total', s.total || 0) + metric('Active', s.active || 0);
    document.getElementById('req').innerHTML = metric('Total', r.total || 0) + metric('Errors', r.errors || 0) + metric('Rate', (r.rate_per_sec || 0).toFixed(1) + '/s');
    document.getElementById('byt').innerHTML = metric('Sent', formatBytes(b.sent_total || 0)) + metric('Recv', formatBytes(b.recv_total || 0)) + metric('Send Rate', formatRate(b.sent_rate_kbps || 0)) + metric('Recv Rate', formatRate(b.recv_rate_kbps || 0));
    document.getElementById('ts').textContent = new Date().toLocaleTimeString();
    document.getElementById('st').className = 'status';
  }

  function showError(message) {
    document.getElementById('err').textContent = message;
    document.getElementById('err').style.display = 'block';
    document.getElementById('st').className = 'status err';
  }

  function pollMetrics() {
    fetch(METRICS_ENDPOINT)
      .then(function(response) {
        return response.json();
      })
      .then(function(data) {
        renderMetrics(data);
        document.getElementById('err').style.display = 'none';
      })
      .catch(function(error) {
        showError(error.message);
      });
  }

  // Initial poll and start interval
  pollMetrics();
  setInterval(pollMetrics, POLL_INTERVAL_MS);
})();
