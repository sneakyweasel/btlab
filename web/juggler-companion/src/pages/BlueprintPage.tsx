import { useDeferredValue, useEffect, useMemo, useRef, useState, type ReactNode } from "react";
import { useSearchParams } from "react-router-dom";
import "../components/blueprint.css";
import {
  LIST_INFO, LIST_KEYS, STATUSES, STATUS_LABEL, formatStatuses, isBlueprint, matches, neighbours,
  parseStatuses, shown, tableOrder, toggleStatus, type Blueprint, type Claim, type ListKey, type Status,
} from "../juggler/blueprint";
import { BlueprintGraph } from "../visuals/BlueprintGraph";

const DATA_URL = `${import.meta.env.BASE_URL}data/blueprint.json`;
const LIST_LIMIT = 12;

function useNoIndex() {
  useEffect(() => {
    const meta = document.createElement("meta");
    meta.name = "robots";
    meta.content = "noindex, nofollow";
    document.head.appendChild(meta);
    const title = document.title;
    document.title = "Formalization blueprint";
    return () => { meta.remove(); document.title = title; };
  }, []);
}

async function copyText(text: string): Promise<boolean> {
  try { await navigator.clipboard.writeText(text); return true; } catch { /* fall back below */ }
  const area = document.createElement("textarea");
  area.value = text;
  area.style.position = "fixed";
  area.style.opacity = "0";
  document.body.append(area);
  area.select();
  let ok = false;
  try { ok = document.execCommand("copy"); } catch { ok = false; }
  area.remove();
  return ok;
}

function CopyButton({ text, label = "Copy", aria }: { text: string; label?: string; aria?: string }) {
  const [state, setState] = useState<"idle" | "ok" | "fail">("idle");
  useEffect(() => {
    if (state === "idle") return;
    const t = setTimeout(() => setState("idle"), 1400);
    return () => clearTimeout(t);
  }, [state]);
  return (
    <button type="button" className="bp-copy" aria-label={aria ?? label}
      onClick={async ev => { ev.stopPropagation(); setState((await copyText(text)) ? "ok" : "fail"); }}>
      {state === "ok" ? "Copied" : state === "fail" ? "Copy failed" : label}
    </button>
  );
}

function ClaimLink({ id, onSelect }: { id: string; onSelect: (id: string) => void }) {
  return (
    <a className="bp-claim" href={`?claim=${encodeURIComponent(id)}`}
      onClick={ev => { ev.preventDefault(); onSelect(id); }}>{id}</a>
  );
}

function Ids({ ids, onSelect }: { ids: string[]; onSelect: (id: string) => void }) {
  return <>{ids.map((id, i) => <span key={id}>{i > 0 && ", "}<ClaimLink id={id} onSelect={onSelect} /></span>)}</>;
}

function Row({ label, children }: { label: string; children: ReactNode }) {
  return <><dt>{label}</dt><dd>{children}</dd></>;
}

function FrontierList({ name, data, onSelect }: { name: ListKey; data: Blueprint; onSelect: (id: string) => void }) {
  const ids = data.lists[name];
  if (!ids.length && (name === "stale" || name === "blocked")) return null;
  const { title, why } = LIST_INFO[name];
  return (
    <div>
      <h3 className="bp-list-title">{title} ({ids.length})</h3>
      <p className="bp-why">{why}</p>
      {ids.length === 0 ? <p className="bp-why">None.</p> : (
        <ol className="bp-list">
          {ids.slice(0, LIST_LIMIT).map(id => {
            const c = data.claims[id];
            return (
              <li key={id}>
                <ClaimLink id={id} onSelect={onSelect} />
                {name === "unlocks" ? <span className="bp-why"> → {data.unlocks[id].join(", ")}</span>
                  : name === "almost_ready" ? <span className="bp-why"> needs {c.blockers?.[0]?.claim}</span>
                  : c.downstream > 0 ? <span className="bp-why"> · {c.downstream} downstream</span> : null}
                {c.warnings.length > 0 && <span className="bp-warnmark" title={c.warnings.join("\n")}> !</span>}
                {c.agent_prompt && <> <CopyButton text={c.agent_prompt} label="Copy task" aria={`Copy the agent task for ${id}`} /></>}
              </li>
            );
          })}
          {ids.length > LIST_LIMIT && <li className="bp-why">… {ids.length - LIST_LIMIT} more in the table</li>}
        </ol>
      )}
    </div>
  );
}

function Detail({ data, id, onSelect }: { data: Blueprint; id: string | null; onSelect: (id: string) => void }) {
  if (!id || !data.claims[id]) {
    return <><h2 className="bp-h2">Claim</h2><p className="bp-why">Select a node, a frontier entry or a table row.</p></>;
  }
  const c: Claim = data.claims[id];
  const { usedBy } = neighbours(data.graph, id);
  return (
    <>
      <h2 className="bp-h2 bp-mono">{id}</h2>
      <p><span className={`bp-status bp-status-${c.status}`}>{STATUS_LABEL[c.status]}</span> <span className="bp-why">{c.tag}</span></p>
      <p className="bp-statement">{c.statement}</p>
      <dl className="bp-facts">
        <Row label="Next action">{c.next_action}</Row>
        <Row label="Downstream">{c.downstream}</Row>
        <Row label="Source">{c.source}</Row>
        {c.proof_source && <Row label="Proof passage">{`${c.proof_source.path}:${c.proof_source.line} (${c.proof_source.freshness})`}</Row>}
        {c.blockers && c.blockers.length > 0 && <Row label="Blocked by"><Ids ids={c.blockers.map(b => b.claim)} onSelect={onSelect} /></Row>}
        {c.conditional_on && c.conditional_on.length > 0 && <Row label="Assumes"><Ids ids={c.conditional_on} onSelect={onSelect} /></Row>}
        {c.inputs && c.inputs.length > 0 && (
          <Row label="Lean inputs">
            <ul className="bp-inputs">
              {c.inputs.map(i => (
                <li key={i.claim}><ClaimLink id={i.claim} onSelect={onSelect} /> ({i.kind}) — {i.decl.join(", ") || "no declaration"}; coverage {i.coverage.band}</li>
              ))}
            </ul>
          </Row>
        )}
        {data.unlocks[id] && <Row label="Would unlock"><Ids ids={data.unlocks[id]} onSelect={onSelect} /></Row>}
        {usedBy.length > 0 && <Row label="Used by"><Ids ids={usedBy} onSelect={onSelect} /></Row>}
        {c.lean && <Row label="Lean file">{c.lean}</Row>}
        {c.decl.length > 0 && <Row label="Declarations">{c.decl.join(", ")}</Row>}
        {c.coverage && <Row label="English coverage">{`${c.coverage.band}${c.coverage.reading ? ` — ${c.coverage.reading}` : ""} (Jev, advisory)`}</Row>}
        {c.warnings.length > 0 && <Row label="Warnings"><span className="bp-warntext">{c.warnings.map(w => <span key={w}>{w}<br /></span>)}</span></Row>}
      </dl>
      {c.agent_prompt && (
        <>
          <div className="bp-task-head"><h3>Agent task</h3><CopyButton text={c.agent_prompt} /></div>
          <pre className="bp-task">{c.agent_prompt}</pre>
          <code className="bp-cmd">python tools/formalpedia.py frontier --task {id}</code>
        </>
      )}
      <code className="bp-cmd">python tools/formalpedia.py claim {id}</code>
    </>
  );
}

function Loaded({ data }: { data: Blueprint }) {
  const [params, setParams] = useSearchParams();
  const active = useMemo(() => parseStatuses(params.get("status")), [params]);
  const selected = params.get("claim");
  const [query, setQuery] = useState("");
  const [tableQuery, setTableQuery] = useState("");
  const deferredTable = useDeferredValue(tableQuery);
  const graphHead = useRef<HTMLHeadingElement>(null);
  const tableHead = useRef<HTMLHeadingElement>(null);
  const [frontierOpen, setFrontierOpen] = useState(() => {
    try { return localStorage.getItem("blueprint.frontier") !== "closed"; } catch { return true; }
  });

  const update = (next: { status?: Set<Status>; claim?: string | null }) => {
    const p = new URLSearchParams(params);
    if (next.status) {
      const s = formatStatuses(next.status);
      if (s) p.set("status", s); else p.delete("status");
    }
    if (next.claim !== undefined) {
      if (next.claim) p.set("claim", next.claim); else p.delete("claim");
    }
    setParams(p, { replace: true });
  };
  const select = (id: string) => update({ claim: id === selected ? null : id });
  const chooseStatus = (status: Status, combine: boolean) => {
    const next = toggleStatus(active, status, combine);
    update({ status: next });
    if (next.size === 0) return;
    const inGraph = Object.keys(data.graph.nodes).some(id => next.has(data.claims[id].status));
    (inGraph ? graphHead : tableHead).current?.scrollIntoView({ behavior: "smooth", block: "start" });
  };

  const order = useMemo(() => tableOrder(data.claims), [data]);
  const rows = order.filter(c => shown(active, c.status) && matches(c, deferredTable));
  const summary = [
    [data.lists.ready.length, "ready"], [data.lists.almost_ready.length, "one blocker away"],
    [data.lists.needs_annotation.length, "routes to complete"], [data.lists.stale.length, "stale"],
  ].filter(([n, label]) => n || label === "ready").map(([n, label]) => `${n} ${label}`).join(" · ");
  const generated = new Date(data.generated);

  return (
    <div className="bp space-y-6">
      <header>
        <p className="text-xs uppercase tracking-[0.18em] text-muted">Laboratory working view</p>
        <h1 className="text-4xl">Formalization blueprint</h1>
        <p className="prose-measure mt-3 text-muted">
          Which human-proved claims have every written input in Lean, and what blocks the rest, after
          Tao's <a href="https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/" target="_blank" rel="noreferrer">PFR blueprint</a>.
          A snapshot of the claim ledger exported {Number.isNaN(generated.getTime()) ? data.generated : generated.toLocaleString()};
          the live view is <code>python tools/formalpedia.py blueprint</code>. No evidence label is promoted here.
        </p>
        <div className="bp-chips" role="group" aria-label="Show only these statuses; Ctrl-click combines them">
          {STATUSES.filter(s => data.counts[s]).map(s => (
            <button key={s} type="button" className={`bp-chip${active.size && !active.has(s) ? " is-off" : ""}`}
              aria-pressed={active.has(s)}
              onClick={ev => chooseStatus(s, ev.ctrlKey || ev.metaKey || ev.shiftKey)}>
              <i className={`bp-swatch bp-${s}`} />{STATUS_LABEL[s]} {data.counts[s]}
            </button>
          ))}
          {active.size > 0 && <button type="button" className="bp-chip bp-clear" onClick={() => update({ status: new Set() })}>Show all</button>}
        </div>
      </header>

      <details className="bp-card" open={frontierOpen}
        onToggle={ev => {
          const open = (ev.currentTarget as HTMLDetailsElement).open;
          setFrontierOpen(open);
          try { localStorage.setItem("blueprint.frontier", open ? "open" : "closed"); } catch { /* per-viewer only */ }
        }}>
        <summary><h2 className="bp-h2 inline">Frontier</h2> <span className="bp-why">— {summary}</span></summary>
        <div className="bp-lists">
          {LIST_KEYS.map(k => <FrontierList key={k} name={k} data={data} onSelect={select} />)}
        </div>
      </details>

      <div className="bp-main">
        <section className="bp-card min-w-0">
          <h2 className="bp-h2" ref={graphHead}>Written claim graph</h2>
          <input type="search" className="bp-search" placeholder="Find a claim ID or word in its statement"
            aria-label="Find a claim in the graph" value={query} onChange={ev => setQuery(ev.target.value)} />
          <BlueprintGraph data={data} active={active} query={query} selected={selected} onSelect={select} />
        </section>
        <aside className="bp-card bp-detail" aria-live="polite">
          <Detail data={data} id={selected} onSelect={select} />
        </aside>
      </div>

      <section className="bp-card">
        <h2 className="bp-h2" ref={tableHead}>
          {rows.length === order.length ? `All claims (${rows.length})` : `Claims (${rows.length} of ${order.length})`}
        </h2>
        <input type="search" className="bp-search" placeholder="Filter by ID, label, status or statement"
          aria-label="Filter claims" value={tableQuery} onChange={ev => setTableQuery(ev.target.value)} />
        <div className="bp-table-wrap">
          <table className="bp-table">
            <thead><tr><th>Claim</th><th>Status</th><th>Evidence</th><th className="text-right">Downstream</th></tr></thead>
            <tbody>
              {rows.map(c => (
                <tr key={c.id} className={c.id === selected ? "is-selected" : undefined}>
                  <td><ClaimLink id={c.id} onSelect={select} /></td>
                  <td>{STATUS_LABEL[c.status]}</td>
                  <td>{c.tag}</td>
                  <td className="text-right tabular-nums">{c.downstream}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </section>

      <details className="bp-card"><summary className="bp-why">Limitations</summary><p className="bp-why mt-2">{data.limitations}</p></details>
    </div>
  );
}

export default function BlueprintPage() {
  useNoIndex();
  const [state, setState] = useState<{ data?: Blueprint; error?: string }>({});
  useEffect(() => {
    let live = true;
    fetch(DATA_URL)
      .then(r => { if (!r.ok) throw new Error(`HTTP ${r.status}`); return r.json(); })
      .then(json => {
        if (!isBlueprint(json)) throw new Error("unexpected snapshot format");
        if (live) setState({ data: json });
      })
      .catch(err => { if (live) setState({ error: String(err.message ?? err) }); });
    return () => { live = false; };
  }, []);
  if (state.error) return <p role="alert">The blueprint snapshot could not be loaded ({state.error}).</p>;
  if (!state.data) return <p role="status">Loading the blueprint snapshot…</p>;
  return <Loaded data={state.data} />;
}
