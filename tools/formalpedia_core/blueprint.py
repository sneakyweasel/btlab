"""Self-contained HTML view of the formalization frontier and the written claim graph.

The page is a generated view of the canonical claims, never a second source. It
embeds the same data that ``formalpedia.py frontier --format json`` returns, so a
reader and an agent see one computation. It makes no network requests.
"""
from __future__ import annotations

import html
import json
from pathlib import Path

from research.claim_dependencies import digest

NODE_W, NODE_H, GAP_X, GAP_Y, PAD = 256, 46, 22, 74, 24
MAX_ROW = 7


def layout(claims: dict, ledger: list[dict]) -> dict:
    """Layered drawing of every claim that has or is named by a written route.

    Arrows point from a claim to its inputs, as in ``claim-graph``. Each claim
    sits below every claim that uses it; barycentre sweeps reduce crossings and
    layers wider than ``MAX_ROW`` wrap onto further rows.
    """
    edges, members = [], set()
    for row in ledger:
        for route in row.get('proof_routes', []):
            members.add(row['id'])
            for edge in route['uses']:
                members.add(edge['claim'])
                edges.append({'from': row['id'], 'to': edge['claim'], 'kind': edge['kind'], 'route': route['id']})
    children = {n: sorted({e['to'] for e in edges if e['from'] == n}) for n in members}
    parents = {n: sorted({e['from'] for e in edges if e['to'] == n}) for n in members}
    level: dict[str, int] = {}

    def depth(name: str) -> int:
        # Each claim sits one row below its lowest user, so leaves stay near what uses them.
        if name not in level:
            level[name] = 1 + max((depth(p) for p in parents[name]), default=-1)
        return level[name]

    for name in sorted(members):
        depth(name)
    layers = [sorted((n for n in members if level[n] == k),
                     key=lambda n: (-claims[n]['downstream'], n)) for k in range(max(level.values(), default=-1) + 1)]
    for _ in range(6):
        for k in range(1, len(layers)):
            _reorder(layers[k], parents, layers[k - 1])
        for k in range(len(layers) - 2, -1, -1):
            _reorder(layers[k], children, layers[k + 1])
    # Wrap wide layers into consecutive rows; every edge still points downwards.
    layers = [layer[i:i + MAX_ROW] for layer in layers for i in range(0, len(layer), MAX_ROW)]
    widest = max((len(layer) for layer in layers), default=0)
    width = PAD * 2 + widest * NODE_W + max(widest - 1, 0) * GAP_X
    nodes = {}
    for row, layer in enumerate(layers):
        span = len(layer) * NODE_W + max(len(layer) - 1, 0) * GAP_X
        left = (width - span) / 2
        for i, name in enumerate(layer):
            nodes[name] = {'x': round(left + i * (NODE_W + GAP_X)), 'y': PAD + row * (NODE_H + GAP_Y)}
    height = PAD * 2 + len(layers) * NODE_H + max(len(layers) - 1, 0) * GAP_Y
    return {'nodes': nodes, 'edges': edges, 'width': width, 'height': height,
            'node_w': NODE_W, 'node_h': NODE_H}


def _reorder(layer: list[str], neighbours: dict[str, list[str]], adjacent: list[str]) -> None:
    """Sort one layer by the mean position of its neighbours in the adjacent layer."""
    position = {n: i for i, n in enumerate(adjacent)}
    current = {n: i for i, n in enumerate(layer)}

    def key(name: str) -> tuple[float, int]:
        placed = [position[n] for n in neighbours[name] if n in position]
        return (sum(placed) / len(placed) if placed else float(current[name]), current[name])

    layer.sort(key=key)


def _statement(ledger: list[dict]) -> dict[str, str]:
    return {row['id']: row['statement'] for row in ledger}


def page_data(result: dict, ledger: list[dict], *, generated: str) -> dict:
    """Everything the page renders; list entries are claim IDs into ``claims``."""
    statements = _statement(ledger)
    claims = {}
    for name, item in result['claims'].items():
        record = {k: v for k, v in item.items() if k != 'routes'}
        record['statement'] = statements[name]
        record['routes'] = [{k: r[k] for k in ('route', 'status', 'coverage', 'blockers', 'conditional_on')}
                            | {'freshness': r['freshness']['status']} for r in item['routes']]
        claims[name] = record
    lists = {name: [i['id'] if name != 'unlocks' else i['claim'] for i in result[name]]
             for name in ('ready', 'almost_ready', 'unlocks', 'blocked', 'stale', 'needs_annotation',
                          'unannotated_boundary')}
    unlocks = {u['claim']: u['would_become_ready'] for u in result['unlocks']}
    graph = layout(result['claims'], ledger)
    return {'generated': generated, 'snapshot': result['snapshot'], 'scope': result['scope'],
            'counts': result['counts'], 'limitations': result['limitations'], 'lists': lists,
            'unlocks': unlocks, 'claims': claims, 'graph': graph}


def render(result: dict, ledger: list[dict], *, generated: str) -> str:
    data = page_data(result, ledger, generated=generated)
    payload = json.dumps(data, ensure_ascii=False, sort_keys=True).replace('</', '<\\/')
    return (TEMPLATE.replace('{{TITLE}}', 'Formalization Blueprint')
            .replace('{{SNAPSHOT}}', html.escape(data['snapshot'][:12]))
            .replace('{{DATA}}', payload))


def write(path: Path, text: str) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding='utf-8', newline='\n')
    return digest(text)


TEMPLATE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{{TITLE}}</title>
<style>
:root {
  --bg: #f7f7f4; --surface: #ffffff; --ink: #1d1f22; --muted: #5d6168; --line: #d5d6d2;
  --edge: #8a8f96; --focus: #b3541e;
  --formal-fill: #d7eedb; --formal-line: #2d7a45;
  --ready-fill: #d6e6fa; --ready-line: #245fa6;
  --cond-line: #a8660e; --open-fill: #fbecd2;
  --finite-fill: #ece6f5; --finite-line: #6a5391;
  --stale-line: #b3261e; --unknown-line: #9a9da3;
  --warn: #b3261e;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #15171a; --surface: #1e2125; --ink: #e8e9ea; --muted: #a2a6ad; --line: #363a40;
    --edge: #7b818a; --focus: #f0995b;
    --formal-fill: #1f3d28; --formal-line: #6cc486;
    --ready-fill: #1c3150; --ready-line: #7fb2f0;
    --cond-line: #e2a74c; --open-fill: #43351c;
    --finite-fill: #2f2742; --finite-line: #b39ddb;
    --stale-line: #f2877f; --unknown-line: #767a80; --warn: #f2877f;
  }
}
:root[data-theme="dark"] {
  --bg: #15171a; --surface: #1e2125; --ink: #e8e9ea; --muted: #a2a6ad; --line: #363a40;
  --edge: #7b818a; --focus: #f0995b;
  --formal-fill: #1f3d28; --formal-line: #6cc486;
  --ready-fill: #1c3150; --ready-line: #7fb2f0;
  --cond-line: #e2a74c; --open-fill: #43351c;
  --finite-fill: #2f2742; --finite-line: #b39ddb;
  --stale-line: #f2877f; --unknown-line: #767a80; --warn: #f2877f;
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink);
  font: 14px/1.45 system-ui, -apple-system, "Segoe UI", sans-serif; }
code, .mono { font-family: ui-monospace, "Cascadia Mono", Consolas, monospace; font-size: 12.5px; }
header { padding: 20px 16px 8px; max-width: 1400px; margin: 0 auto; }
h1 { font-size: 22px; margin: 0 0 4px; }
h2 { font-size: 15px; margin: 0 0 8px; }
.sub { color: var(--muted); margin: 0; }
main { max-width: 1400px; margin: 0 auto; padding: 0 16px 40px; display: grid; gap: 16px;
  grid-template-columns: minmax(0, 1fr) 380px; }
@media (max-width: 960px) { main { grid-template-columns: minmax(0, 1fr); } }
.card { background: var(--surface); border: 1px solid var(--line); border-radius: 8px; padding: 14px; min-width: 0; }
.counts { display: flex; flex-wrap: wrap; gap: 6px; margin: 12px 0 0; }
.chip { border: 1px solid var(--line); background: var(--surface); color: var(--ink); border-radius: 999px;
  padding: 3px 10px; font-size: 12.5px; cursor: pointer; }
.counts.filtering .chip[aria-pressed="false"]:not(.clear) { opacity: .45; }
.chip[aria-pressed="true"] { border-color: var(--focus); box-shadow: inset 0 0 0 1px var(--focus); }
.chip.clear { color: var(--focus); }
button.copy { border: 1px solid var(--line); background: var(--bg); color: var(--muted); border-radius: 4px;
  padding: 0 6px; font: 11.5px system-ui, sans-serif; cursor: pointer; vertical-align: 1px; }
button.copy:hover { color: var(--ink); border-color: var(--focus); }
.task-head { display: flex; align-items: center; justify-content: space-between; margin: 14px 0 4px; }
.task-head h3 { font-size: 13.5px; margin: 0; }
pre.task { white-space: pre-wrap; overflow-wrap: anywhere; background: var(--bg); border: 1px solid var(--line);
  border-radius: 6px; padding: 8px; margin: 0; max-height: 340px; overflow: auto;
  font: 11.5px/1.45 ui-monospace, "Cascadia Mono", Consolas, monospace; }
.chip i { display: inline-block; width: 9px; height: 9px; border-radius: 2px; margin-right: 6px; vertical-align: 0; }
.lists { display: grid; gap: 14px; grid-template-columns: repeat(auto-fit, minmax(260px, 1fr)); }
.lists ol { margin: 0; padding-left: 20px; }
.lists li { margin: 2px 0; }
.lists .empty { color: var(--muted); }
a.claim { color: var(--ink); text-decoration: underline; text-decoration-color: var(--line); cursor: pointer; }
a.claim:hover { text-decoration-color: var(--focus); }
.why { color: var(--muted); font-size: 12.5px; }
.toolbar { display: flex; flex-wrap: wrap; gap: 8px; align-items: center; margin-bottom: 8px; }
input[type=search] { flex: 1 1 220px; min-width: 0; padding: 6px 10px; border: 1px solid var(--line); border-radius: 6px;
  background: var(--bg); color: var(--ink); font: inherit; }
button.small { border: 1px solid var(--line); background: var(--bg); color: var(--ink); border-radius: 6px; padding: 5px 10px; cursor: pointer; font: inherit; }
.graph-wrap { overflow: auto; max-height: 72vh; border: 1px solid var(--line); border-radius: 6px; background: var(--bg); }
svg text { fill: var(--ink); font: 11.5px ui-monospace, "Cascadia Mono", Consolas, monospace; pointer-events: none; }
svg text.st { fill: var(--muted); font: 10.5px system-ui, sans-serif; }
.node { cursor: pointer; }
.node .box { stroke-width: 1.6; }
.node.formalized .box { fill: var(--formal-fill); stroke: var(--formal-line); }
.node.ready .box { fill: var(--ready-fill); stroke: var(--ready-line); stroke-width: 2.4; }
.node.ready_conditional .box { fill: var(--ready-fill); stroke: var(--cond-line); stroke-width: 2.4; }
.node.blocked .box { fill: var(--surface); stroke: var(--muted); }
.node.needs_annotation .box, .node.unannotated .box { fill: var(--surface); stroke: var(--unknown-line); stroke-dasharray: 5 4; }
.node.stale .box { fill: var(--surface); stroke: var(--stale-line); stroke-dasharray: 5 4; }
.node.open .box { fill: var(--open-fill); stroke: var(--cond-line); }
.node.finite .box { fill: var(--finite-fill); stroke: var(--finite-line); }
.node.not_a_target .box { fill: var(--surface); stroke: var(--line); }
.node.selected .box { stroke: var(--focus); stroke-width: 3; }
.node.dim { opacity: .18; }
.node .warn { fill: var(--warn); }
.edge { fill: none; stroke: var(--edge); stroke-width: 1.2; }
.edge.statement { stroke-dasharray: 2 3; }
.edge.assumption { stroke: var(--cond-line); stroke-dasharray: 6 4; }
.edge.computation { stroke: var(--finite-line); stroke-dasharray: 8 3 2 3; }
.edge.dim { opacity: .1; }
.edge.hi { stroke: var(--focus); stroke-width: 2; opacity: 1; }
#arrow path { fill: var(--edge); }
.legend { display: flex; flex-wrap: wrap; gap: 4px 14px; color: var(--muted); font-size: 12.5px; margin-top: 8px; }
aside { position: sticky; top: 12px; align-self: start; max-height: calc(100vh - 24px); overflow: auto; }
@media (max-width: 960px) { aside { position: static; max-height: none; } }
dl { margin: 0; display: grid; grid-template-columns: 110px minmax(0, 1fr); gap: 4px 10px; }
dt { color: var(--muted); }
dd { margin: 0; overflow-wrap: anywhere; }
.stmt { white-space: pre-wrap; overflow-wrap: anywhere; margin: 8px 0; }
.status { display: inline-block; border-radius: 4px; padding: 1px 6px; font-size: 12px; border: 1px solid var(--line); }
.warnline { color: var(--warn); }
.cmd { display: block; background: var(--bg); border: 1px solid var(--line); border-radius: 6px; padding: 6px 8px; margin-top: 6px; overflow-wrap: anywhere; }
table { width: 100%; border-collapse: collapse; }
th, td { text-align: left; padding: 5px 6px; border-bottom: 1px solid var(--line); vertical-align: top; }
th { color: var(--muted); font-weight: 600; font-size: 12.5px; position: sticky; top: 0; background: var(--surface); }
td.n { text-align: right; font-variant-numeric: tabular-nums; }
.table-wrap { max-height: 60vh; overflow: auto; }
.full { grid-column: 1 / -1; }
details summary { cursor: pointer; color: var(--muted); }
#frontier > summary { color: var(--ink); list-style-position: outside; margin-left: 16px; }
#frontier > summary h2 { display: inline; margin: 0; }
#frontier[open] > summary { margin-bottom: 10px; }
</style>
</head>
<body>
<header>
  <h1>Formalization Blueprint</h1>
  <p class="sub">Generated from <code>docs/claims</code> (snapshot <code>{{SNAPSHOT}}</code>, <span id="generated"></span>).
  A view, never a source. Agents: the same data is <code>python tools/formalpedia.py frontier --format json</code>,
  MCP <code>formalpedia_frontier</code>, or the <code>#frontier-data</code> JSON block in this file.</p>
  <div class="counts" id="counts" role="group" aria-label="Filter the graph by status"></div>
</header>
<main>
  <details class="card full" id="frontier" open>
    <summary><h2>Frontier</h2> <span class="why" id="frontier-summary"></span></summary>
    <div class="lists" id="lists"></div>
  </details>
  <section class="card" aria-labelledby="graph-h">
    <h2 id="graph-h">Written claim graph</h2>
    <div class="toolbar">
      <input type="search" id="find" placeholder="Find a claim ID or word in its statement" aria-label="Find a claim">
      <button class="small" id="zoom-out" aria-label="Zoom out">−</button>
      <button class="small" id="zoom-in" aria-label="Zoom in">+</button>
      <button class="small" id="zoom-reset">Fit</button>
    </div>
    <div class="graph-wrap" id="graph-wrap"></div>
    <div class="legend" id="legend"></div>
  </section>
  <aside class="card" id="detail" aria-live="polite">
    <h2>Claim</h2>
    <p class="why">Select a node, a frontier entry or a table row.</p>
  </aside>
  <section class="card full" aria-labelledby="all-h">
    <h2 id="all-h">All claims</h2>
    <div class="toolbar"><input type="search" id="table-find" placeholder="Filter by ID, label, status or statement" aria-label="Filter claims"></div>
    <div class="table-wrap"><table>
      <thead><tr><th>Claim</th><th>Status</th><th>Evidence</th><th>Downstream</th></tr></thead>
      <tbody id="rows"></tbody>
    </table></div>
  </section>
  <section class="card full"><details><summary>Limitations</summary><p id="limits"></p></details></section>
</main>
<script type="application/json" id="frontier-data">{{DATA}}</script>
<script>
(() => {
const D = JSON.parse(document.getElementById('frontier-data').textContent);
const C = D.claims, G = D.graph, NS = 'http://www.w3.org/2000/svg';
const LABEL = {formalized: 'Formalized', ready: 'Ready', ready_conditional: 'Ready, conditional',
  blocked: 'Blocked', stale: 'Stale pin', needs_annotation: 'Route incomplete', unannotated: 'Unannotated',
  open: 'Open hypothesis', finite: 'Finite computation', not_a_target: 'Not a target'};
const SWATCH = {formalized: '--formal-fill', ready: '--ready-fill', ready_conditional: '--ready-fill',
  blocked: '--surface', stale: '--surface', needs_annotation: '--surface', unannotated: '--surface',
  open: '--open-fill', finite: '--finite-fill', not_a_target: '--surface'};
const LISTS = [
  ['ready', 'Ready to formalize', 'Complete route; every proof and statement input is LEAN VERIFIED.'],
  ['almost_ready', 'One blocker away', 'Complete route with exactly one input not yet in Lean.'],
  ['unlocks', 'Highest-value blockers', 'Formalizing one of these makes the listed claims ready.'],
  ['needs_annotation', 'Routes to complete', 'Partial routes: enumerate the immediate dependencies.'],
  ['unannotated_boundary', 'Inputs without routes', 'Used by an annotated proof but never annotated themselves.'],
  ['blocked', 'Blocked', 'Several inputs missing from Lean.'],
  ['stale', 'Stale source pins', 'The cited passage changed; review before repinning.']];
const el = (tag, attrs = {}, text) => { const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v); if (text != null) e.textContent = text; return e; };
const svgEl = (tag, attrs = {}) => { const e = document.createElementNS(NS, tag);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v); return e; };
document.getElementById('generated').textContent = D.generated;
document.getElementById('limits').textContent = D.limitations;
const link = (id) => { const a = el('a', {class: 'claim mono', href: '#' + encodeURIComponent(id)}, id);
  a.addEventListener('click', (ev) => { ev.preventDefault(); select(id, true); }); return a; };
async function copyText(text) {
  try { await navigator.clipboard.writeText(text); return true; } catch (e) {}
  const area = el('textarea'); area.value = text; area.style.position = 'fixed'; area.style.opacity = '0';
  document.body.append(area); area.select();
  let ok = false; try { ok = document.execCommand('copy'); } catch (e) {}
  area.remove(); return ok;
}
function copyButton(text, label, aria) {
  const b = el('button', {class: 'copy', type: 'button', 'aria-label': aria || label}, label);
  b.addEventListener('click', async (ev) => { ev.stopPropagation();
    const ok = await copyText(text); b.textContent = ok ? 'Copied' : 'Copy failed';
    setTimeout(() => { b.textContent = label; }, 1400); });
  return b;
}

// Status chips show only the chosen statuses, in the graph and the table.
// Click selects one status (again to clear); Ctrl, Shift or Cmd adds or removes one.
const active = new Set(), chips = {};
const shown = (status) => !active.size || active.has(status);
const counts = document.getElementById('counts');
for (const status of Object.keys(LABEL)) {
  const n = D.counts[status]; if (!n) continue;
  const b = el('button', {class: 'chip', 'aria-pressed': 'false', type: 'button',
    title: 'Show only this status; Ctrl-click to combine'});
  const sw = el('i'); sw.style.background = `var(${SWATCH[status]})`;
  sw.style.border = '1px solid var(--line)'; b.append(sw, `${LABEL[status]} ${n}`);
  b.addEventListener('click', (ev) => {
    if (ev.ctrlKey || ev.shiftKey || ev.metaKey) active.has(status) ? active.delete(status) : active.add(status);
    else if (active.size === 1 && active.has(status)) active.clear();
    else { active.clear(); active.add(status); }
    applyStatus(true); });
  counts.append(b); chips[status] = b;
}
const clear = el('button', {class: 'chip clear', type: 'button', hidden: ''}, 'Show all');
clear.addEventListener('click', () => { active.clear(); applyStatus(false); });
counts.append(clear);
function applyStatus(reveal) {
  for (const [s, b] of Object.entries(chips)) b.setAttribute('aria-pressed', active.has(s) ? 'true' : 'false');
  counts.classList.toggle('filtering', active.size > 0);
  clear.hidden = !active.size;
  paint(); filterTable(); writeHash();
  if (!reveal || !active.size) return;
  const inGraph = Object.keys(nodeEls).some(id => active.has(C[id].status));
  document.getElementById(inGraph ? 'graph-h' : 'all-h').scrollIntoView({behavior: 'smooth', block: 'start'});
}

// Frontier lists.
const lists = document.getElementById('lists');
// The card collapses to one summary line so the graph can take the screen; the choice is remembered.
const frontierCard = document.getElementById('frontier');
document.getElementById('frontier-summary').textContent = ' — ' + [
  [D.lists.ready.length, 'ready'], [D.lists.almost_ready.length, 'one blocker away'],
  [D.lists.needs_annotation.length, 'routes to complete'], [D.lists.stale.length, 'stale']]
  .filter(([n, label]) => n || label === 'ready').map(([n, label]) => `${n} ${label}`).join(' · ');
try { if (localStorage.getItem('blueprint.frontier') === 'closed') frontierCard.open = false; } catch (e) {}
frontierCard.addEventListener('toggle', () => {
  try { localStorage.setItem('blueprint.frontier', frontierCard.open ? 'open' : 'closed'); } catch (e) {} });
for (const [key, title, why] of LISTS) {
  const ids = D.lists[key]; if (!ids.length && (key === 'stale' || key === 'blocked')) continue;
  const box = el('div'); box.append(el('h2', {}, `${title} (${ids.length})`), el('p', {class: 'why'}, why));
  if (!ids.length) box.append(el('p', {class: 'empty'}, 'None.'));
  const ol = el('ol');
  for (const id of ids.slice(0, 12)) {
    const li = el('li'); li.append(link(id));
    const c = C[id];
    if (key === 'unlocks') li.append(el('span', {class: 'why'}, ` → ${D.unlocks[id].join(', ')}`));
    else if (key === 'almost_ready') li.append(el('span', {class: 'why'}, ` needs ${c.blockers[0].claim}`));
    else if (c.downstream) li.append(el('span', {class: 'why'}, ` · ${c.downstream} downstream`));
    if (c.warnings && c.warnings.length) li.append(el('span', {class: 'warnline', title: c.warnings.join('\n')}, ' !'));
    if (c.agent_prompt) li.append(' ', copyButton(c.agent_prompt, 'Copy task', `Copy the agent task for ${id}`));
    ol.append(li);
  }
  if (ids.length > 12) ol.append(el('li', {class: 'why'}, `… ${ids.length - 12} more in the table`));
  box.append(ol); lists.append(box);
}

// Graph.
const wrap = document.getElementById('graph-wrap');
const svg = svgEl('svg', {role: 'img', 'aria-label': 'Written claim dependency graph'});
const defs = svgEl('defs'); const marker = svgEl('marker', {id: 'arrow', viewBox: '0 0 10 10', refX: 9, refY: 5,
  markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse'});
marker.append(svgEl('path', {d: 'M0,0 L10,5 L0,10 z'})); defs.append(marker); svg.append(defs);
const W = G.node_w, H = G.node_h, nodeEls = {}, edgeEls = [];
for (const e of G.edges) {
  const a = G.nodes[e.from], b = G.nodes[e.to];
  const x1 = a.x + W / 2, y1 = a.y + H, x2 = b.x + W / 2, y2 = b.y;
  const my = (y1 + y2) / 2;
  const p = svgEl('path', {class: `edge ${e.kind}`, d: `M${x1},${y1} C${x1},${my} ${x2},${my} ${x2},${y2 - 2}`,
    'marker-end': 'url(#arrow)'});
  p.append(Object.assign(svgEl('title'), {textContent: `${e.from} uses ${e.to} (${e.kind})`}));
  svg.append(p); edgeEls.push([e, p]);
}
for (const [id, pos] of Object.entries(G.nodes)) {
  const c = C[id]; const g = svgEl('g', {class: `node ${c.status}`, tabindex: 0, role: 'button',
    'aria-label': `${id}: ${LABEL[c.status]}`, transform: `translate(${pos.x},${pos.y})`});
  const shape = c.status === 'open'
    ? svgEl('polygon', {class: 'box', points: `12,0 ${W - 12},0 ${W},${H / 2} ${W - 12},${H} 12,${H} 0,${H / 2}`})
    : svgEl('rect', {class: 'box', width: W, height: H, rx: c.status === 'finite' ? H / 2 : 6});
  g.append(shape);
  const label = id.length > 36 ? id.slice(0, 35) + '…' : id;
  const t1 = svgEl('text', {x: 10, y: 19}); t1.textContent = label;
  const extra = c.status === 'blocked' ? ` · ${c.blockers.length} missing` : c.downstream ? ` · ${c.downstream} downstream` : '';
  const t2 = svgEl('text', {x: 10, y: 35, class: 'st'}); t2.textContent = LABEL[c.status] + extra;
  g.append(t1, t2);
  if (c.warnings && c.warnings.length) g.append(svgEl('circle', {class: 'warn', cx: W - 9, cy: 9, r: 4}));
  g.append(Object.assign(svgEl('title'), {textContent: id}));
  g.addEventListener('click', () => select(id, false));
  g.addEventListener('keydown', (ev) => { if (ev.key === 'Enter' || ev.key === ' ') { ev.preventDefault(); select(id, false); } });
  svg.append(g); nodeEls[id] = g;
}
wrap.append(svg);
let zoom = 1;
const fit = () => Math.max(.55, Math.min(1, (wrap.clientWidth - 4) / G.width));
const setZoom = (z) => { zoom = Math.max(.25, Math.min(2, z));
  svg.setAttribute('width', G.width * zoom); svg.setAttribute('height', G.height * zoom);
  svg.setAttribute('viewBox', `0 0 ${G.width} ${G.height}`); };
document.getElementById('zoom-in').onclick = () => setZoom(zoom * 1.25);
document.getElementById('zoom-out').onclick = () => setZoom(zoom / 1.25);
document.getElementById('zoom-reset').onclick = () => setZoom(fit());
setZoom(fit());

const legend = document.getElementById('legend');
for (const s of ['formalized', 'ready', 'ready_conditional', 'blocked', 'needs_annotation', 'open', 'finite'])
  legend.append(el('span', {}, `${LABEL[s]}: ${{formalized: 'green', ready: 'blue', ready_conditional: 'blue, amber border',
    blocked: 'solid grey border', needs_annotation: 'dashed border', open: 'amber hexagon', finite: 'violet pill'}[s]}`));
legend.append(el('span', {}, 'Arrows point to inputs. Dotted: statement; dashed amber: assumption; dash-dot: computation. Red dot: English-coverage warning.'));

// Search and filters.
let query = '', selected = null;
const find = document.getElementById('find');
find.addEventListener('input', () => { query = find.value.trim().toLowerCase(); paint(); });
function matches(id) { if (!query) return true; const c = C[id];
  return id.toLowerCase().includes(query) || c.statement.toLowerCase().includes(query); }
function paint() {
  const near = new Set();
  if (selected && nodeEls[selected]) { near.add(selected);
    for (const [e] of edgeEls) { if (e.from === selected) near.add(e.to); if (e.to === selected) near.add(e.from); } }
  // A status filter overrides the neighbourhood focus; a selected node always stays visible.
  const focus = selected && nodeEls[selected] && !query && !active.size;
  for (const [id, g] of Object.entries(nodeEls)) {
    const off = id !== selected && (!shown(C[id].status) || !matches(id) || (focus && !near.has(id)));
    g.classList.toggle('dim', off); g.classList.toggle('selected', id === selected);
  }
  for (const [e, p] of edgeEls) {
    const on = selected && (e.from === selected || e.to === selected);
    p.classList.toggle('hi', !!on);
    p.classList.toggle('dim', !on && ((focus && !on) || (!shown(C[e.from].status) && !shown(C[e.to].status))));
  }
}

// Detail panel.
const detail = document.getElementById('detail');
function row(dl, k, v) { if (v == null || v === '' || (Array.isArray(v) && !v.length)) return;
  dl.append(el('dt', {}, k)); const dd = el('dd'); if (v instanceof Node) dd.append(v); else dd.textContent = v; dl.append(dd); }
function ids(list) { const span = el('span'); list.forEach((x, i) => { if (i) span.append(', '); span.append(link(x)); }); return span; }
function select(id, scroll) {
  selected = selected === id && !scroll ? null : id; paint();
  if (!selected) { detail.replaceChildren(el('h2', {}, 'Claim'), el('p', {class: 'why'}, 'Select a node, a frontier entry or a table row.')); return; }
  const c = C[id];
  const box = [el('h2', {class: 'mono'}, id)];
  const st = el('p'); st.append(el('span', {class: 'status'}, LABEL[c.status]), ' ', el('span', {class: 'why'}, c.tag));
  box.push(st, el('p', {class: 'stmt'}, c.statement));
  const dl = el('dl');
  row(dl, 'Next action', c.next_action);
  row(dl, 'Downstream', String(c.downstream));
  row(dl, 'Source', c.source);
  if (c.proof_source) row(dl, 'Proof passage', `${c.proof_source.path}:${c.proof_source.line} (${c.proof_source.freshness})`);
  if (c.route) row(dl, 'Route', c.route);
  if (c.blockers && c.blockers.length) row(dl, 'Blocked by', ids(c.blockers.map(b => b.claim)));
  if (c.conditional_on && c.conditional_on.length) row(dl, 'Assumes', ids(c.conditional_on));
  if (c.inputs && c.inputs.length) { const ul = el('ul');
    for (const i of c.inputs) { const li = el('li'); li.append(link(i.claim), ` (${i.kind}) — ${i.decl.join(', ') || 'no decl'}; coverage ${i.coverage.band}`); ul.append(li); }
    row(dl, 'Lean inputs', ul); }
  if (D.unlocks[id]) row(dl, 'Would unlock', ids(D.unlocks[id]));
  const users = G.edges.filter(e => e.to === id).map(e => e.from);
  if (users.length) row(dl, 'Used by', ids([...new Set(users)]));
  if (c.lean) row(dl, 'Lean file', c.lean);
  if (c.decl && c.decl.length) row(dl, 'Declarations', c.decl.join(', '));
  if (c.coverage) row(dl, 'English coverage', `${c.coverage.band}${c.coverage.reading ? ' — ' + c.coverage.reading : ''} (Jev, advisory)`);
  if (c.warnings && c.warnings.length) { const w = el('div', {class: 'warnline'}); c.warnings.forEach(x => w.append(el('div', {}, x))); row(dl, 'Warnings', w); }
  box.push(dl);
  if (c.agent_prompt) {
    const head = el('div', {class: 'task-head'});
    head.append(el('h3', {}, 'Agent task'), copyButton(c.agent_prompt, 'Copy'));
    box.push(head, el('pre', {class: 'task'}, c.agent_prompt),
      el('code', {class: 'cmd'}, `python tools/formalpedia.py frontier --task ${id}`));
  }
  box.push(el('code', {class: 'cmd'}, `python tools/formalpedia.py claim ${id}`));
  if (nodeEls[id]) box.push(el('code', {class: 'cmd'}, `python tools/formalpedia.py claim-graph ${id} --format markdown`));
  detail.replaceChildren(...box);
  if (scroll && nodeEls[id]) { const p = G.nodes[id];
    wrap.scrollTo({left: p.x * zoom - wrap.clientWidth / 2 + W * zoom / 2, top: p.y * zoom - wrap.clientHeight / 2, behavior: 'smooth'}); }
  writeHash();
}
// The hash keeps both the status filter and the selected claim: #status=ready,blocked&claim=ID.
// A bare #ID, the earlier form, still selects that claim.
function writeHash() {
  const parts = [];
  if (active.size) parts.push('status=' + [...active].join(','));
  if (selected) parts.push('claim=' + encodeURIComponent(selected));
  history.replaceState(null, '', parts.length ? '#' + parts.join('&') : location.pathname + location.search);
}

// Table.
const tbody = document.getElementById('rows');
const order = Object.values(C).sort((a, b) => b.downstream - a.downstream || a.id.localeCompare(b.id));
const trs = order.map(c => { const tr = el('tr'); const td = el('td'); td.append(link(c.id));
  tr.append(td, el('td', {}, LABEL[c.status]), el('td', {}, c.tag), el('td', {class: 'n'}, String(c.downstream)));
  tr.dataset.text = `${c.id} ${c.status} ${LABEL[c.status]} ${c.tag} ${c.statement}`.toLowerCase(); tbody.append(tr); return tr; });
const tf = document.getElementById('table-find');
const tableHead = document.getElementById('all-h');
function filterTable() {
  const q = tf.value.trim().toLowerCase(); let n = 0;
  trs.forEach((tr, i) => { tr.hidden = !shown(order[i].status) || (!!q && !tr.dataset.text.includes(q)); n += !tr.hidden; });
  tableHead.textContent = n === trs.length ? `All claims (${n})` : `Claims (${n} of ${trs.length})`;
}
tf.addEventListener('input', filterTable);

function readHash() {
  const hash = decodeURIComponent(location.hash.slice(1));
  const params = new URLSearchParams(hash.includes('=') ? hash : '');
  active.clear();
  for (const s of (params.get('status') || '').split(',')) if (chips[s]) active.add(s);
  const claim = hash.includes('=') ? params.get('claim') : hash;
  selected = null;
  applyStatus(false);
  if (C[claim]) select(claim, true); else select(null, false);
}
window.addEventListener('hashchange', readHash);
readHash();
})();
</script>
</body>
</html>
"""
