"use strict";

const clientId = Math.random().toString(36).slice(2, 10);
const root = document.getElementById("root");
const chromeEl = document.getElementById("chrome");
const connEl = document.getElementById("conn");
const latEl = document.getElementById("latency");

const kw = (v) => (typeof v === "string" && v.startsWith(":")) ? v.slice(1) : v;
const has = (v) => v != null && !(Array.isArray(v) && v.length === 0);

// Layout slots: perspectives assign panes to main/side/bottom; unlisted
// panes park hidden (their state keeps flowing, they just don't render).
const SLOT_NAMES = ["main", "side", "bottom"];
const slotEls = {};
SLOT_NAMES.forEach((s) => {
  const d = document.createElement("div");
  d.id = "slot-" + s;
  d.className = "slot";
  root.appendChild(d);
  slotEls[s] = d;
});
const hiddenEl = document.createElement("div");
hiddenEl.id = "slot-hidden";
root.appendChild(hiddenEl);

let layout = null;

function applyLayout() {
  if (!layout) return;
  const used = { main: false, side: false, bottom: false };
  const listed = new Set();
  (layout.slots || []).forEach((s) => {
    const name = kw(s.slot);
    const el = slotEls[name];
    if (!el) return;
    (s.panes || []).forEach((pid) => {
      listed.add(pid);
      const p = document.getElementById("pane-" + pid);
      if (p) {
        el.appendChild(p);
        used[name] = true;
      }
    });
  });
  root.querySelectorAll(".w-panel[id^='pane-']").forEach((p) => {
    if (!listed.has(p.id.slice(5))) hiddenEl.appendChild(p);
  });
  SLOT_NAMES.forEach((s) => {
    slotEls[s].style.display = used[s] ? "flex" : "none";
  });
  root.style.gridTemplateColumns = used.side ? "1fr minmax(340px, 28%)" : "1fr";
  root.style.gridTemplateRows = used.bottom ? "1fr minmax(160px, 30%)" : "1fr";
  root.style.gridTemplateAreas = used.bottom
    ? (used.side ? '"main side" "bottom side"' : '"main" "bottom"')
    : (used.side ? '"main side"' : '"main"');
}

function renderText(node, el) {
  (node.runs || []).forEach((r) => {
    const s = document.createElement("span");
    s.className = "s-" + kw(r.style || "plain");
    if (r.effect) s.classList.add("fx-" + kw(r.effect));
    s.textContent = r.t || "";
    el.appendChild(s);
  });
}

function renderTable(node, el) {
  const tbl = document.createElement("table");
  if (has(node.cols)) {
    const tr = document.createElement("tr");
    node.cols.forEach((c) => {
      const th = document.createElement("th");
      th.textContent = c;
      tr.appendChild(th);
    });
    tbl.appendChild(tr);
  }
  (node.rows || []).forEach((row) => {
    const tr = document.createElement("tr");
    row.forEach((cell) => {
      const td = document.createElement("td");
      td.textContent = cell;
      tr.appendChild(td);
    });
    tbl.appendChild(tr);
  });
  el.appendChild(tbl);
}

function runsWithCursor(runs, col, lineEl) {
  let off = 0;
  let placed = false;
  (runs || []).forEach((r) => {
    const t = r.t || "";
    const cls = "s-" + kw(r.style || "plain");
    if (!placed && col >= off && col < off + t.length) {
      const k = col - off;
      if (k > 0) lineEl.appendChild(span(cls, t.slice(0, k)));
      lineEl.appendChild(span("input-cursor", t.slice(k, k + 1)));
      if (k + 1 < t.length) lineEl.appendChild(span(cls, t.slice(k + 1)));
      placed = true;
    } else {
      lineEl.appendChild(span(cls, t));
    }
    off += t.length;
  });
  if (!placed) lineEl.appendChild(span("input-cursor", "\u00a0"));
}

function renderInput(node, el) {
  const hl = has(node.hl) ? node.hl : null;
  (node.lines || []).forEach((ln, r) => {
    const lineEl = document.createElement("div");
    lineEl.className = "input-line";
    const runs = hl && hl[r] && has(hl[r]) ? hl[r] : [{ t: ln, style: ":plain" }];
    if (r === node.row) {
      runsWithCursor(runs, node.col || 0, lineEl);
    } else if (ln === "") {
      lineEl.textContent = "\u00a0";
    } else {
      runs.forEach((x) => lineEl.appendChild(span("s-" + kw(x.style || "plain"), x.t || "")));
    }
    el.appendChild(lineEl);
  });
}

function renderTreeNode(n, depth) {
  const wrap = document.createElement("div");
  const row = document.createElement("div");
  row.className = "tree-node";
  row.style.paddingLeft = depth * 14 + "px";
  if (n.key) row.appendChild(span("tree-key", n.key + " "));
  row.appendChild(span("s-" + kw(n.style || "plain"), n.label || ""));
  wrap.appendChild(row);
  if (has(n.children)) {
    n.children.forEach((c) => wrap.appendChild(renderTreeNode(c, depth + 1)));
  }
  return wrap;
}

function render(node) {
  const w = kw(node.w);
  const el = document.createElement("div");
  el.className = "w-" + w;
  if (node.effect) el.classList.add("fx-" + kw(node.effect));
  if (w === "root") {
    (node.panes || []).forEach((p) => el.appendChild(render(p)));
  } else if (w === "panel") {
    const t = document.createElement("div");
    t.className = "panel-title";
    t.textContent = node.title || "";
    el.appendChild(t);
    const b = document.createElement("div");
    b.className = "panel-body";
    (node.children || []).forEach((c) => b.appendChild(render(c)));
    el.appendChild(b);
  } else if (w === "scroll") {
    if (node.id) el.dataset.wid = node.id;
    (node.children || []).forEach((c) => el.appendChild(render(c)));
  } else if (w === "text") {
    renderText(node, el);
  } else if (w === "table") {
    renderTable(node, el);
  } else if (w === "input") {
    renderInput(node, el);
  } else if (w === "tree") {
    el.appendChild(renderTreeNode(node.root || {}, 0));
  }
  return el;
}

function span(cls, text) {
  const s = document.createElement("span");
  s.className = cls;
  s.textContent = text;
  return s;
}

// Procedural art (gen v1): seeded LCG drives a bar-field fingerprint.
// Deterministic per symbol — the same API always shows the same art.
function drawArt(canvas, seed) {
  const ctx = canvas.getContext("2d");
  let s = seed >>> 0;
  const next = () => {
    s = (Math.imul(s, 1103515245) + 12345) >>> 0;
    return s / 4294967296;
  };
  const w = canvas.width;
  const h = canvas.height;
  const hue = Math.floor(next() * 360);
  ctx.fillStyle = "hsl(" + hue + " 35% 8%)";
  ctx.fillRect(0, 0, w, h);
  const bars = 24;
  const bw = w / bars;
  for (let i = 0; i < bars; i++) {
    const bh = 4 + next() * (h - 8);
    const lit = 30 + next() * 35;
    const dh = (hue + next() * 60 - 30 + 360) % 360;
    ctx.fillStyle = "hsl(" + dh + " 70% " + lit + "%)";
    ctx.fillRect(i * bw + 1, h - bh, bw - 2, bh);
  }
  ctx.fillStyle = "hsl(" + hue + " 80% 65%)";
  const gx = next() * (w - 12) + 6;
  const gy = next() * (h - 12) + 6;
  ctx.beginPath();
  ctx.arc(gx, gy, 3 + next() * 4, 0, Math.PI * 2);
  ctx.fill();
}

function renderCard(c) {
  const tier = c.tier || "common";
  const card = document.createElement("div");
  card.className = "card card-tier-" + tier + (tier === "legendary" ? " fx-shimmer" : "");

  const art = document.createElement("canvas");
  art.className = "card-art";
  art.width = 320;
  art.height = 44;
  card.appendChild(art);
  if (c.art && c.art.seed != null) drawArt(art, c.art.seed);

  const head = document.createElement("div");
  head.className = "card-head";
  head.appendChild(span("card-name", c.symbol || ""));
  head.appendChild(span("card-chip chip-" + tier, tier.toUpperCase()));
  card.appendChild(head);

  if (c.sig) card.appendChild(span("s-type card-sig", c.sig));

  if (has(c.stats)) {
    const row = document.createElement("div");
    row.className = "card-stats";
    c.stats.forEach((st) => {
      const cell = document.createElement("span");
      cell.className = "card-stat";
      cell.appendChild(span("st-label", st.label + " "));
      cell.appendChild(span("st-value", String(st.v)));
      row.appendChild(cell);
    });
    const sc = document.createElement("span");
    sc.className = "card-stat";
    sc.appendChild(span("st-label", "SCORE "));
    sc.appendChild(span("st-value", String(c.score != null ? c.score : 0)));
    row.appendChild(sc);
    card.appendChild(row);
  }

  if (c.doc) {
    const body = document.createElement("div");
    body.className = "card-doc";
    body.textContent = c.doc;
    card.appendChild(body);
  }
  if (c.loc) card.appendChild(span("s-dim card-loc", c.loc));
  return card;
}

let focusedPane = null;

function markFocus(paneId) {
  focusedPane = paneId;
  root.querySelectorAll(".w-panel.focused").forEach((p) => p.classList.remove("focused"));
  const el = document.getElementById("pane-" + paneId);
  if (el) el.classList.add("focused");
}

function renderChrome(tree) {
  chromeEl.textContent = "";

  if (has(tree.keyhints)) {
    const kh = document.createElement("div");
    kh.className = "keyhints";
    tree.keyhints.forEach((h) => {
      const row = document.createElement("div");
      row.className = "keyhint";
      row.appendChild(span("kh-key", h.key));
      row.appendChild(span(h.label.startsWith("+") ? "kh-group" : "kh-label", h.label));
      kh.appendChild(row);
    });
    chromeEl.appendChild(kh);
  }

  if (has(tree.card)) {
    chromeEl.appendChild(renderCard(tree.card));
  }

  if (has(tree.completions)) {
    const comp = document.createElement("div");
    comp.className = "completions";
    tree.completions.forEach((c) => {
      const row = document.createElement("div");
      row.className = "completion-item";
      row.appendChild(span("comp-name", c.name || ""));
      if (c.detail) row.appendChild(span("s-dim comp-detail", " " + c.detail));
      comp.appendChild(row);
    });
    chromeEl.appendChild(comp);
  }

  if (has(tree.palette)) {
    const p = tree.palette;
    const pal = document.createElement("div");
    pal.className = "palette";
    const q = document.createElement("div");
    q.className = "palette-query";
    q.appendChild(span("s-dim", "> "));
    q.appendChild(span("s-plain", p.query));
    q.appendChild(span("cursor", "\u2588"));
    pal.appendChild(q);
    (p.items || []).forEach((item, i) => {
      const row = document.createElement("div");
      row.className = "palette-item" + (i === p.sel ? " selected" : "");
      row.appendChild(span("pi-title", item.title));
      row.appendChild(span("pi-id s-dim", item.id));
      row.appendChild(span("pi-keys", item.keys));
      pal.appendChild(row);
    });
    chromeEl.appendChild(pal);
  }

  const sl = document.createElement("div");
  sl.className = "w-statusline";
  const st = tree.statusline || {};
  sl.appendChild(span("mode mode-" + (st.mode || "normal"), st.mode || "normal"));
  if (st.perspective) sl.appendChild(span("perspective", "[" + st.perspective + "]"));
  if (st.pending) sl.appendChild(span("pending", st.pending));
  sl.appendChild(span("slot", "focus " + (st.focus || "")));
  chromeEl.appendChild(sl);
  if (st.focus) markFocus(st.focus);
}

function applyPatch(msg) {
  if (msg.pane === "chrome" && has(msg.tree)) {
    renderChrome(msg.tree);
  } else if (msg.pane === "layout" && has(msg.tree)) {
    layout = msg.tree;
    applyLayout();
  } else if (msg.pane && has(msg.tree)) {
    const el = render(msg.tree);
    el.id = "pane-" + msg.pane;
    const old = document.getElementById("pane-" + msg.pane);
    const scrollPos = {};
    if (old) {
      old.querySelectorAll(".w-scroll[data-wid]").forEach((s) => {
        const atBottom = s.scrollTop + s.clientHeight >= s.scrollHeight - 4;
        scrollPos[s.dataset.wid] = { top: s.scrollTop, atBottom: atBottom };
      });
      old.replaceWith(el);
    } else {
      (layout ? hiddenEl : slotEls.main).appendChild(el);
      applyLayout();
    }
    el.querySelectorAll(".w-scroll[data-wid]").forEach((s) => {
      const prev = scrollPos[s.dataset.wid];
      if (!prev || prev.atBottom) s.scrollTop = s.scrollHeight;
      else s.scrollTop = prev.top;
    });
    if (focusedPane) markFocus(focusedPane);
  }
  if (msg.ts && msg.ts > 0) {
    const now = Math.round(performance.now() * 1000);
    latEl.textContent = "echo " + ((now - msg.ts) / 1000).toFixed(1) + " ms";
    latEl.className = "s-num";
  }
}

const es = new EventSource("/events?client=" + clientId);
es.addEventListener("ui-patch", (e) => applyPatch(JSON.parse(e.data)));
es.onopen = () => {
  connEl.textContent = "live";
  connEl.className = "s-ok fx-pulse";
};
es.onerror = () => {
  connEl.textContent = "offline";
  connEl.className = "s-error";
};

function keyName(e) {
  if (e.key === " ") return "SPC";
  if (e.key === "Enter") return "CR";
  if (e.key === "Escape") return "ESC";
  if (e.key === "Backspace") return "BS";
  if (e.key === "Tab") return "TAB";
  if (e.key === "ArrowUp") return "UP";
  if (e.key === "ArrowDown") return "DOWN";
  if (e.key.length === 1 && !e.ctrlKey && !e.metaKey && !e.altKey) return e.key;
  return null;
}

// Events are serialized through a promise chain: concurrent fetches give no
// ordering guarantee, and key events are only meaningful in order.
let sendChain = Promise.resolve();
function sendEvent(ev) {
  ev.ts = Math.round(performance.now() * 1000);
  const body = JSON.stringify({ client: clientId, event: ev });
  sendChain = sendChain
    .then(() => fetch("/event", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: body,
    }))
    .catch(() => {});
}

window.addEventListener("keydown", (e) => {
  const key = keyName(e);
  if (key === null) return;
  e.preventDefault();
  sendEvent({ type: "key", key: key });
});

// Focus follows the mouse. The server ignores hovers over panes hidden by
// the current perspective and any hover while in insert mode.
let hoverPane = null;
root.addEventListener("pointerover", (e) => {
  const panel = e.target.closest(".w-panel[id^='pane-']");
  const pane = panel ? panel.id.slice(5) : null;
  if (pane === null || pane === hoverPane) return;
  hoverPane = pane;
  sendEvent({ type: "focus", pane: pane });
});
