// Valkyria AIO Debug Dashboard
// Polls /debug/metrics and renders JSON

const POLL_INTERVAL_MS = 1500;
const METRICS_ENDPOINT = '/debug/metrics';

function renderMetric(label, value) {
  return `
    <div class="metric">
      <div class="metric-label">${label}</div>
      <div class="metric-value">${value}</div>
    </div>
  `;
}

function formatUptime(seconds) {
  const days = Math.floor(seconds / 86400);
  const hours = Math.floor((seconds % 86400) / 3600);
  const mins = Math.floor((seconds % 3600) / 60);
  const secs = Math.floor(seconds % 60);

  if (days > 0) return `${days}d ${hours}h ${mins}m ${secs}s`;
  if (hours > 0) return `${hours}h ${mins}m ${secs}s`;
  if (mins > 0) return `${mins}m ${secs}s`;
  return `${secs}s`;
}

function formatBytes(bytes) {
  if (bytes < 1024) return `${bytes} B`;
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(2)} KB`;
  if (bytes < 1024 * 1024 * 1024) return `${(bytes / 1024 / 1024).toFixed(2)} MB`;
  return `${(bytes / 1024 / 1024 / 1024).toFixed(2)} GB`;
}

function formatNumber(num) {
  return num.toLocaleString();
}

function renderMetrics(data) {
  // System
  document.getElementById('system-metrics').innerHTML =
    renderMetric('Uptime', formatUptime(data.uptime_seconds));

  // Connections
  const conn = data.connections || {};
  document.getElementById('connection-metrics').innerHTML =
    renderMetric('Total', formatNumber(conn.total || 0)) +
    renderMetric('Active', formatNumber(conn.active || 0)) +
    renderMetric('Failed', formatNumber(conn.failed || 0));

  // Streams
  const streams = data.streams || {};
  document.getElementById('stream-metrics').innerHTML =
    renderMetric('Total', formatNumber(streams.total || 0)) +
    renderMetric('Active', formatNumber(streams.active || 0));

  // Requests
  const req = data.requests || {};
  document.getElementById('request-metrics').innerHTML =
    renderMetric('Total', formatNumber(req.total || 0)) +
    renderMetric('Active', formatNumber(req.active || 0)) +
    renderMetric('Errors', formatNumber(req.errors || 0)) +
    renderMetric('Rate', `${(req.rate_per_sec || 0).toFixed(2)} req/s`) +
    renderMetric('Avg Latency', `${(req.avg_latency_ms || 0).toFixed(2)} ms`);

  // Bytes
  const bytes = data.bytes || {};
  document.getElementById('bytes-metrics').innerHTML =
    renderMetric('Sent Total', formatBytes(bytes.sent_total || 0)) +
    renderMetric('Received Total', formatBytes(bytes.recv_total || 0)) +
    renderMetric('Send Rate', `${(bytes.sent_rate_kbps || 0).toFixed(2)} KB/s`) +
    renderMetric('Recv Rate', `${(bytes.recv_rate_kbps || 0).toFixed(2)} KB/s`);

  // Timestamp
  document.getElementById('timestamp').textContent = new Date().toLocaleTimeString();

  // Update status indicator
  document.getElementById('status').className = 'status-indicator';
}

function showError(message) {
  const errorEl = document.getElementById('error');
  errorEl.textContent = `Error: ${message}`;
  errorEl.style.display = 'block';
  document.getElementById('status').className = 'status-indicator error';
}

function hideError() {
  document.getElementById('error').style.display = 'none';
}

async function pollMetrics() {
  try {
    const params = new URLSearchParams(window.location.search);
    let endpoint = METRICS_ENDPOINT;

    if (params.toString()) {
      endpoint += '?' + params.toString();
    }

    const response = await fetch(endpoint);
    if (!response.ok) {
      throw new Error(`HTTP ${response.status}: ${response.statusText}`);
    }

    const data = await response.json();
    renderMetrics(data);
    hideError();
  } catch (err) {
    showError(err.message);
    console.error('Failed to fetch metrics:', err);
  }
}

// Initial load
document.getElementById('system-metrics').innerHTML = renderMetric('Uptime', 'Loading...');
document.getElementById('connection-metrics').innerHTML = renderMetric('Status', 'Loading...');
document.getElementById('stream-metrics').innerHTML = renderMetric('Status', 'Loading...');
document.getElementById('request-metrics').innerHTML = renderMetric('Status', 'Loading...');
document.getElementById('bytes-metrics').innerHTML = renderMetric('Status', 'Loading...');

// Start polling
pollMetrics();
setInterval(pollMetrics, POLL_INTERVAL_MS);
