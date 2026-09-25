import { useEffect, useMemo, useRef, useState } from "react";
import { STATUS_LABEL, shown, matches, type Blueprint, type Status } from "../juggler/blueprint";

type Props = {
  data: Blueprint;
  active: ReadonlySet<Status>;
  query: string;
  selected: string | null;
  onSelect: (id: string) => void;
};

/** The written claim graph at the exported layout. Arrows point from a claim to its inputs. */
export function BlueprintGraph({ data, active, query, selected, onSelect }: Props) {
  const { graph, claims } = data;
  const W = graph.node_w, H = graph.node_h;
  const wrap = useRef<HTMLDivElement>(null);
  // The fitted zoom follows the container width; a zoom button fixes it until Fit.
  const [width, setWidth] = useState<number | null>(null);
  const [manual, setManual] = useState<number | null>(null);
  useEffect(() => {
    const el = wrap.current;
    if (!el) return;
    const observer = new ResizeObserver(([entry]) => setWidth(entry.contentRect.width));
    observer.observe(el);
    return () => observer.disconnect();
  }, []);
  const zoom = manual ?? Math.max(0.55, Math.min(1, ((width ?? graph.width) - 4) / graph.width));

  const near = useMemo(() => {
    const set = new Set<string>();
    if (!selected || !graph.nodes[selected]) return set;
    set.add(selected);
    for (const e of graph.edges) {
      if (e.from === selected) set.add(e.to);
      if (e.to === selected) set.add(e.from);
    }
    return set;
  }, [graph, selected]);

  // Keep the selected node centred when the selection or the zoom changes.
  useEffect(() => {
    const p = selected ? graph.nodes[selected] : undefined;
    const el = wrap.current;
    if (!p || !el) return;
    el.scrollTo({ left: p.x * zoom - el.clientWidth / 2 + (W * zoom) / 2, top: p.y * zoom - el.clientHeight / 2, behavior: "smooth" });
  }, [selected, graph.nodes, W, zoom]);

  const focus = !!selected && !!graph.nodes[selected] && !query.trim() && active.size === 0;
  return (
    <div>
      <div className="bp-toolbar" role="group" aria-label="Zoom">
        <button type="button" onClick={() => setManual(Math.max(0.25, zoom / 1.25))} aria-label="Zoom out">−</button>
        <button type="button" onClick={() => setManual(Math.min(2, zoom * 1.25))} aria-label="Zoom in">+</button>
        <button type="button" onClick={() => setManual(null)} aria-pressed={manual === null}>Fit</button>
      </div>
      <div className="bp-graph" ref={wrap}>
        <svg width={graph.width * zoom} height={graph.height * zoom} viewBox={`0 0 ${graph.width} ${graph.height}`}
          role="img" aria-label="Written claim dependency graph">
          <defs>
            <marker id="bp-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
              <path d="M0,0 L10,5 L0,10 z" className="bp-arrow" />
            </marker>
          </defs>
          {graph.edges.map((e, i) => {
            const a = graph.nodes[e.from], b = graph.nodes[e.to];
            const x1 = a.x + W / 2, y1 = a.y + H, x2 = b.x + W / 2, y2 = b.y, my = (y1 + y2) / 2;
            const on = !!selected && (e.from === selected || e.to === selected);
            const dim = !on && (focus || (!shown(active, claims[e.from].status) && !shown(active, claims[e.to].status)));
            return (
              <path key={i} className={`bp-edge bp-edge-${e.kind}${on ? " is-on" : ""}${dim ? " is-dim" : ""}`}
                d={`M${x1},${y1} C${x1},${my} ${x2},${my} ${x2},${y2 - 2}`} markerEnd="url(#bp-arrow)">
                <title>{`${e.from} uses ${e.to} (${e.kind})`}</title>
              </path>
            );
          })}
          {Object.entries(graph.nodes).map(([id, p]) => {
            const c = claims[id];
            const off = id !== selected && (!shown(active, c.status) || !matches(c, query) || (focus && !near.has(id)));
            const extra = c.status === "blocked" ? ` · ${c.blockers?.length ?? 0} missing`
              : c.downstream ? ` · ${c.downstream} downstream` : "";
            return (
              <g key={id} transform={`translate(${p.x},${p.y})`} tabIndex={0} role="button"
                aria-label={`${id}: ${STATUS_LABEL[c.status]}`} aria-pressed={id === selected}
                className={`bp-node bp-${c.status}${off ? " is-dim" : ""}${id === selected ? " is-selected" : ""}`}
                onClick={() => onSelect(id)}
                onKeyDown={ev => { if (ev.key === "Enter" || ev.key === " ") { ev.preventDefault(); onSelect(id); } }}>
                {c.status === "open"
                  ? <polygon className="bp-box" points={`12,0 ${W - 12},0 ${W},${H / 2} ${W - 12},${H} 12,${H} 0,${H / 2}`} />
                  : <rect className="bp-box" width={W} height={H} rx={c.status === "finite" ? H / 2 : 6} />}
                <text x={10} y={19} className="bp-id">{id.length > 36 ? `${id.slice(0, 35)}…` : id}</text>
                <text x={10} y={35} className="bp-sub">{STATUS_LABEL[c.status] + extra}</text>
                {c.warnings.length > 0 && <circle className="bp-warn" cx={W - 9} cy={9} r={4} />}
                <title>{id}</title>
              </g>
            );
          })}
        </svg>
      </div>
      <p className="bp-legend">
        Green: formalized. Blue: ready (amber border: conditional). Solid grey border: blocked. Dashed:
        route incomplete or unannotated. Amber hexagon: open hypothesis. Violet pill: finite computation.
        Arrows point to inputs; dotted is a statement input, dashed amber an assumption, dash-dot a
        computation. A red dot marks an English-coverage warning.
      </p>
    </div>
  );
}
