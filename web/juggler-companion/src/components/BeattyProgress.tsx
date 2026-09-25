import { useDeferredValue, useEffect, useId, useMemo, useRef, useState } from "react";
import { Metric } from "./Metric";
import { BEATTY_CLAIMS, BEATTY_PROGRESS, BEATTY_TAGS, BEATTY_THEMES, beattyTimeline, claimTitle, leanModules, tagCounts, type BeattyTheme, type TimelinePoint } from "../juggler/beattyProgress";
import "./beatty.css";

const TIMELINE = beattyTimeline(BEATTY_CLAIMS);
const COUNTS = tagCounts(BEATTY_CLAIMS);
const MODULES = leanModules(BEATTY_CLAIMS);
const WHEN = new Intl.DateTimeFormat("en-GB", { day: "numeric", month: "short", hour: "2-digit", minute: "2-digit", timeZone: "UTC" });
const DAY = new Intl.DateTimeFormat("en-GB", { day: "numeric", month: "short", timeZone: "UTC" });
const TAG_SHORT: Record<string, string> = {
  "EXACT — LEAN VERIFIED": "Lean verified",
  "EXACT — HUMAN PROOF": "Human proof",
  "COMPUTATIONALLY VERIFIED": "Computational",
};

function Timeline() {
  const container = useRef<HTMLDivElement>(null);
  const [width, setWidth] = useState(720);
  const [hover, setHover] = useState<TimelinePoint | null>(null);
  const titleId = useId(), descriptionId = useId();
  useEffect(() => {
    if (!container.current) return;
    const observer = new ResizeObserver(([entry]) => setWidth(Math.max(260, entry.contentRect.width)));
    observer.observe(container.current);
    return () => observer.disconnect();
  }, []);
  const g = useMemo(() => {
    const height = 240, left = 44, right = width - 12, top = 14, bottom = height - 36;
    const start = TIMELINE[0].time, end = TIMELINE[TIMELINE.length - 1].time;
    const dayMs = 86_400_000;
    const min = Math.floor(start / dayMs) * dayMs, max = Math.ceil(end / dayMs) * dayMs;
    const total = TIMELINE[TIMELINE.length - 1].total;
    const yMax = Math.ceil(total / 20) * 20;
    const x = (t: number) => left + (t - min) / (max - min) * (right - left);
    const y = (n: number) => bottom - n / yMax * (bottom - top);
    let path = `M${x(min)},${y(0)}`;
    for (const point of TIMELINE) path += `H${x(point.time)}V${y(point.total)}`;
    path += `H${x(end)}`;
    const days = Array.from({ length: Math.round((max - min) / dayMs) + 1 }, (_, i) => min + i * dayMs);
    const yTicks = Array.from({ length: yMax / 20 + 1 }, (_, i) => i * 20);
    return { height, left, right, top, bottom, x, y, path, area: `${path}V${y(0)}Z`, days, yTicks, min, max };
  }, [width]);

  function onMove(event: React.PointerEvent<SVGRectElement>) {
    const box = event.currentTarget.getBoundingClientRect();
    const t = g.min + (event.clientX - box.left) / box.width * (g.max - g.min);
    let best: TimelinePoint | null = null;
    for (const point of TIMELINE) if (point.time <= t) best = point;
    setHover(best);
  }

  const last = TIMELINE[TIMELINE.length - 1];
  return (
    <figure className="space-y-2">
      <div ref={container} className="beatty-plot">
        <svg viewBox={`0 0 ${width} ${g.height}`} height={g.height} className="beatty-chart" role="img" aria-labelledby={`${titleId} ${descriptionId}`}>
          <title id={titleId}>Beatty claims recorded over time</title>
          <desc id={descriptionId}>A step curve of the cumulative number of Beatty claims in the ledger, dated by the first commit that recorded each ID. It reaches {last.total} claims on {DAY.format(last.time)}.</desc>
          {g.yTicks.map(tick => <g key={tick}>
            <line x1={g.left} x2={g.right} y1={g.y(tick)} y2={g.y(tick)} stroke="var(--color-line)" strokeWidth={.6} />
            <text x={g.left - 8} y={g.y(tick) + 4} textAnchor="end">{tick}</text>
          </g>)}
          {g.days.map((day, index) => <g key={day}>
            <line x1={g.x(day)} x2={g.x(day)} y1={g.bottom} y2={g.bottom + 5} stroke="var(--color-muted)" strokeWidth={.8} />
            <text x={g.x(day)} y={g.bottom + 20} textAnchor={index === 0 ? "start" : index === g.days.length - 1 ? "end" : "middle"}>{DAY.format(day)}</text>
          </g>)}
          <path d={g.area} fill="var(--color-even)" opacity={.1} />
          <path d={g.path} fill="none" stroke="var(--color-even)" strokeWidth={2} strokeLinejoin="round" />
          <circle cx={g.x(last.time)} cy={g.y(last.total)} r={4} fill="var(--color-even)" stroke="var(--color-card)" strokeWidth={2} />
          <text x={g.x(last.time) - 8} y={g.y(last.total) - 8} textAnchor="end" fontWeight={600}>{last.total} claims</text>
          {hover && <g pointerEvents="none">
            <line x1={g.x(hover.time)} x2={g.x(hover.time)} y1={g.top} y2={g.bottom} stroke="var(--color-muted)" strokeWidth={.8} strokeDasharray="3 3" />
            <circle cx={g.x(hover.time)} cy={g.y(hover.total)} r={4} fill="var(--color-even)" stroke="var(--color-card)" strokeWidth={2} />
          </g>}
          <rect x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} fill="transparent"
            onPointerMove={onMove} onPointerLeave={() => setHover(null)} />
        </svg>
        {hover && <div className="beatty-tooltip" style={{ left: Math.min(Math.max(0, g.x(hover.time) - 126), width - 252), top: 8 }}>
          <div className="font-medium">{WHEN.format(hover.time)} UTC</div>
          <div>{hover.total} claims · {hover.lean} Lean verified</div>
          <div className="mt-1 text-muted">Latest: {claimTitle(hover.id)}</div>
        </div>}
      </div>
      <figcaption className="text-xs text-muted">Cumulative claims, dated by the first commit that recorded each ID. Later retags keep their first date.</figcaption>
    </figure>
  );
}

export function BeattyProgress() {
  const [theme, setTheme] = useState<BeattyTheme | "all">("all");
  const [tag, setTag] = useState<string>("all");
  const [query, setQuery] = useState("");
  const deferred = useDeferredValue(query.trim().toLowerCase());
  const byTheme = useMemo(() => BEATTY_THEMES.map(t => {
    const rows = BEATTY_CLAIMS.filter(c => c.theme === t.key);
    return { ...t, total: rows.length, lean: rows.filter(c => c.tag === "EXACT — LEAN VERIFIED").length };
  }), []);
  const maxTheme = Math.max(...byTheme.map(t => t.total));
  const shown = useMemo(() => BEATTY_CLAIMS.filter(c =>
    (theme === "all" || c.theme === theme) && (tag === "all" || c.tag === tag) &&
    (!deferred || c.id.includes(deferred) || c.statement.toLowerCase().includes(deferred) || (c.lean ?? "").toLowerCase().includes(deferred)),
  ).slice().sort((a, b) => (b.firstRecorded ?? "").localeCompare(a.firstRecorded ?? "")), [theme, tag, deferred]);

  return (
    <div className="space-y-6">
      <div className="grid grid-cols-2 gap-3 sm:grid-cols-3 lg:grid-cols-5">
        <Metric label="Claims" value={String(BEATTY_CLAIMS.length)} hint="Beatty rows in the ledger" />
        {BEATTY_TAGS.map(t => <Metric key={t} label={TAG_SHORT[t]} value={String(COUNTS[t] ?? 0)} hint={t} />)}
        <Metric label="Lean modules" value={String(MODULES.length)} hint="Cited by those rows" />
      </div>

      <section className="rounded-2xl border border-line bg-card p-3 sm:p-5">
        <h3 className="text-xl">Claims recorded over time</h3>
        <Timeline />
      </section>

      <section className="rounded-2xl border border-line bg-card p-3 sm:p-5">
        <h3 className="text-xl">By theme</h3>
        <p className="mt-1 text-sm text-muted">Grouped by claim ID. Select a theme to filter the list below.</p>
        <ul className="mt-3 space-y-2">
          {byTheme.map(t => <li key={t.key}>
            <button type="button" aria-pressed={theme === t.key} onClick={() => setTheme(theme === t.key ? "all" : t.key)}
              className={`grid w-full grid-cols-[minmax(9rem,14rem)_1fr_auto] items-center gap-3 rounded-md px-2 py-1.5 text-left text-sm hover:bg-paper ${theme === t.key ? "bg-paper ring-1 ring-line" : ""}`}
              title={t.hint}>
              <span className="font-medium">{t.label}</span>
              <span className="block h-3 rounded-sm bg-line/40" aria-hidden="true">
                <span className="block h-3 rounded-sm bg-even" style={{ width: `${t.total / maxTheme * 100}%` }} />
              </span>
              <span className="font-mono tabular-nums">{t.total}<span className="text-muted"> · {t.lean} Lean</span></span>
            </button>
          </li>)}
        </ul>
      </section>

      <section className="space-y-3">
        <div className="beatty-controls">
          <label>Theme
            <select value={theme} onChange={e => setTheme(e.target.value as BeattyTheme | "all")}>
              <option value="all">All themes</option>
              {BEATTY_THEMES.map(t => <option key={t.key} value={t.key}>{t.label}</option>)}
            </select>
          </label>
          <label>Evidence
            <select value={tag} onChange={e => setTag(e.target.value)}>
              <option value="all">All labels</option>
              {BEATTY_TAGS.map(t => <option key={t} value={t}>{t}</option>)}
            </select>
          </label>
          <label>Search
            <input type="search" value={query} placeholder="hausdorff, gamma, BeattySlope…" onChange={e => setQuery(e.target.value)} />
          </label>
        </div>
        <p className="text-sm text-muted" aria-live="polite">{shown.length} of {BEATTY_CLAIMS.length} claims · newest first</p>
        <ul className="space-y-2">
          {shown.map(c => <li key={c.id}>
            <details className="rounded-xl border border-line bg-card px-4 py-3 text-sm">
              <summary className="flex cursor-pointer flex-wrap items-baseline gap-x-3 gap-y-1">
                <span className="font-medium">{claimTitle(c.id)}</span>
                <span className={`rounded-full border px-2 text-xs ${c.tag === "EXACT — LEAN VERIFIED" ? "border-ok text-ok" : "border-line text-muted"}`}>{TAG_SHORT[c.tag] ?? c.tag}</span>
                {c.firstRecorded && <span className="ml-auto text-xs text-muted tabular-nums">{DAY.format(Date.parse(c.firstRecorded))}</span>}
              </summary>
              <p className="mt-3 leading-relaxed">{c.statement}</p>
              <dl className="mt-3 grid gap-1 text-xs text-muted sm:grid-cols-[6rem_1fr]">
                <dt>ID</dt><dd className="font-mono break-all">{c.id}</dd>
                <dt>Evidence</dt><dd>{c.tag}</dd>
                {c.lean && <><dt>Lean</dt><dd className="font-mono break-all">formal/{c.lean}</dd></>}
                <dt>Source</dt><dd className="font-mono break-all">{c.source}</dd>
              </dl>
            </details>
          </li>)}
        </ul>
      </section>

      <details className="border-t border-line pt-3 text-xs text-muted">
        <summary className="cursor-pointer">Data and scope</summary>
        <p className="mt-2">Evidence labels are copied from the laboratory ledger unchanged. A Lean row cites the module holding its statement; the site does not re-check it. Themes are a reading aid assigned from claim IDs, not part of the ledger.</p>
        <p className="mt-2">{BEATTY_PROGRESS.dating}</p>
        <p className="mt-2 break-all">Source: {BEATTY_PROGRESS.source}<br />SHA-256: <code>{BEATTY_PROGRESS.sourceSha256}</code></p>
      </details>
    </div>
  );
}
