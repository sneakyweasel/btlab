import { useEffect, useId, useMemo, useRef, useState, type PointerEvent } from "react";
import {
  BEATTY, beattyBounds, beattyLevel, beattyPhase, beattyRow, beattySamples, beattySegments,
  type BeattyLayers, type BeattyRow, type BeattySamples, type BeattySelection,
} from "../juggler/beatty";

type Props = {
  selection: BeattySelection;
  focused: boolean;
  range: BeattySamples;
  layers: BeattyLayers;
  onSelect: (selection: BeattySelection) => void;
};
const LINE = "var(--color-line)", MUTED = "var(--color-muted)";
const PROFILE = "var(--color-even)", SAMPLE = "var(--color-odd)", GAP = "var(--color-warn)";

export function BeattyProfile({ selection, focused, range, layers, onSelect }: Props) {
  const container = useRef<HTMLDivElement>(null);
  const [width, setWidth] = useState(720);
  const [hover, setHover] = useState<{ px: number; py: number; phase: number; sample?: BeattyRow } | null>(null);
  const clipId = useId();
  const titleId = useId();
  const descId = useId();
  useEffect(() => {
    const element = container.current;
    if (!element) return;
    const observer = new ResizeObserver(([entry]) => setWidth(Math.max(250, entry.contentRect.width)));
    observer.observe(element);
    return () => observer.disconnect();
  }, []);

  const phase = beattyPhase(selection);
  const geometry = useMemo(() => {
    const height = width < 480 ? 350 : 420;
    const left = 62, right = width - 70, top = 26, bottom = height - 50;
    const min = focused ? Math.max(0, phase - 0.045) : 0;
    const max = focused ? Math.min(1, phase + 0.045) : 1;
    const samples = beattySamples(range).filter(row => row.phase >= min && row.phase <= max);
    const segments = beattySegments(min, max);
    const values = segments.flatMap(([, , level]) => [level, Math.min(BEATTY.envelope, level + BEATTY.tailUpper)]);
    if (layers.samples) values.push(...samples.map(row => row.ratio));
    if (!focused) values.push(1, BEATTY.envelope);
    const low = Math.min(...values), high = Math.max(...values);
    const pad = Math.max(0.012, (high - low) * 0.055);
    const yMin = low - pad, yMax = high + pad;
    const x = (value: number) => left + 5 + (value - min) / (max - min) * (right - left - 10);
    const y = (value: number) => bottom - 5 - (value - yMin) / (yMax - yMin) * (bottom - top - 10);
    const profilePath = segments.map(([a, b, h]) => `M${x(a)},${y(h)}H${x(b)}`).join("");
    const bandPath = segments.map(([a, b, h]) => `M${x(a)},${y(h)}H${x(b)}V${y(Math.min(BEATTY.envelope, h + BEATTY.tailUpper))}H${x(a)}Z`).join("");
    const radius = focused ? 2.5 : 1.8;
    const samplePath = samples.map(row => `M${x(row.phase) - radius},${y(row.ratio)}a${radius},${radius} 0 1,0 ${radius * 2},0a${radius},${radius} 0 1,0 ${-radius * 2},0`).join("");
    const xCount = width < 480 ? 2 : 5;
    const xTicks = Array.from({ length: xCount + 1 }, (_, i) => min + i * (max - min) / xCount);
    const yTicks = Array.from({ length: 5 }, (_, i) => low + i * (high - low) / 4);
    return { height, left, right, top, bottom, min, max, yMin, yMax, x, y, samples, profilePath, bandPath, samplePath, xTicks, yTicks };
  }, [width, phase, focused, range, layers.samples]);
  const g = geometry;
  const selected = selection.kind === "jump" ? beattyRow(selection.order) : null;
  const leftValue = beattyLevel(phase);
  const stripX = width - 43, stripWidth = 18;

  function inspect(event: PointerEvent<SVGRectElement>, pin: boolean) {
    const bounds = event.currentTarget.ownerSVGElement!.getBoundingClientRect();
    const px = (event.clientX - bounds.left) * width / bounds.width;
    const py = (event.clientY - bounds.top) * g.height / bounds.height;
    const t = Math.max(g.min, Math.min(g.max, g.min + (px - g.left - 5) / (g.right - g.left - 10) * (g.max - g.min)));
    let sample: BeattyRow | undefined;
    let distance = Infinity;
    if (layers.samples) for (const row of g.samples) {
      const d = (g.x(row.phase) - px) ** 2 + (g.y(row.ratio) - py) ** 2;
      if (d < distance) { sample = row; distance = d; }
    }
    if (pin) {
      setHover(null);
      onSelect(sample && distance < 625 ? { kind: "jump", order: sample.order } : { kind: "phase", phase: t });
    } else setHover({ px, py, phase: t, sample });
  }

  return (
    <div ref={container} className="beatty-plot" onPointerLeave={() => setHover(null)}>
      <svg viewBox={`0 0 ${width} ${g.height}`} height={g.height} className="beatty-chart" role="img" aria-labelledby={`${titleId} ${descId}`}>
        <title id={titleId}>Beatty profile, normalized count samples and deleted value intervals</title>
        <desc id={descId}>Disconnected horizontal segments show the left-continuous truncated profile. A tail band encloses the infinite profile. Filled lower and hollow upper dots show the selected jump. The value strip colors only certified gap interiors; the remainder is unresolved.</desc>
        <defs><clipPath id={clipId}><rect x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} /></clipPath></defs>
        <rect x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} fill="none" stroke={LINE} />
        {g.yTicks.map(tick => <g key={tick}>
          <line x1={g.left} x2={g.right} y1={g.y(tick)} y2={g.y(tick)} stroke={LINE} strokeWidth={0.6} />
          <text x={g.left - 8} y={g.y(tick) + 4} textAnchor="end">{tick.toFixed(g.yTicks[1] - g.yTicks[0] < .01 ? 3 : 2)}</text>
        </g>)}
        {g.xTicks.map((tick, index) => <text key={tick} x={g.x(tick)} y={g.bottom + 20} textAnchor={index === 0 ? "start" : index === g.xTicks.length - 1 ? "end" : "middle"}>{tick.toFixed(focused ? 3 : 1)}</text>)}
        <text x={(g.left + g.right) / 2} y={g.height - 7} textAnchor="middle">Beatty phase t</text>
        <text transform={`translate(15,${(g.top + g.bottom) / 2}) rotate(-90)`} textAnchor="middle">Profile / normalized R⁺</text>
        <g clipPath={`url(#${clipId})`}>
          {layers.band && <path data-layer="band" d={g.bandPath} fill={PROFILE} opacity={0.13} />}
          {layers.samples && <path data-layer="samples" d={g.samplePath} fill={SAMPLE} opacity={0.7} />}
          {layers.profile && <path data-layer="profile" d={g.profilePath} fill="none" stroke={PROFILE} strokeWidth={1.5} />}
          <line x1={g.left} x2={g.right} y1={g.y(BEATTY.envelope)} y2={g.y(BEATTY.envelope)} stroke={MUTED} strokeDasharray="3 4" strokeWidth={0.8} />
          <line x1={g.x(phase)} x2={g.x(phase)} y1={g.top} y2={g.bottom} stroke={MUTED} strokeWidth={0.8} />
          {layers.profile && <>
            {selected && <circle data-endpoint="right-trace" cx={g.x(phase)} cy={g.y(leftValue + selected.weight)} r={4.5} fill="var(--color-card)" stroke={PROFILE} strokeWidth={1.6} />}
            <circle data-endpoint="left-value" cx={g.x(phase)} cy={g.y(leftValue)} r={4.5} fill={PROFILE} />
          </>}
          {hover && <g aria-hidden="true">
            <line x1={g.x(hover.phase)} x2={g.x(hover.phase)} y1={g.top} y2={g.bottom} stroke={MUTED} strokeWidth={0.8} />
            {layers.profile && <circle cx={g.x(hover.phase)} cy={g.y(beattyLevel(hover.phase))} r={3.5} fill={PROFILE} />}
            {layers.samples && hover.sample && <circle cx={g.x(hover.sample.phase)} cy={g.y(hover.sample.ratio)} r={4.5} fill="none" stroke={SAMPLE} strokeWidth={1.5} />}
          </g>}
        </g>
        <text x={stripX + stripWidth / 2} y={14} textAnchor="middle">Values</text>
        <rect x={stripX} y={g.y(Math.min(BEATTY.envelope, g.yMax))} width={stripWidth} height={Math.max(0, g.y(Math.max(1, g.yMin)) - g.y(Math.min(BEATTY.envelope, g.yMax)))} fill={LINE} />
        {layers.gaps && BEATTY.cores.filter(core => core.upper > g.yMin && core.lower < g.yMax).map(core => <rect
          key={core.order} data-gap-order={core.order} x={stripX} width={stripWidth}
          y={g.y(Math.min(core.upper, g.yMax))}
          height={Math.max(0, g.y(Math.max(core.lower, g.yMin)) - g.y(Math.min(core.upper, g.yMax)))}
          fill={GAP} opacity={selected?.order === core.order ? 1 : 0.5}
        />)}
        <text x={stripX + stripWidth / 2} y={g.bottom + 20} textAnchor="middle">gaps</text>
        <rect data-chart-hit="" x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} fill="transparent"
          onPointerMove={event => { if (event.pointerType !== "touch") inspect(event, false); }}
          onPointerLeave={() => setHover(null)} onPointerUp={event => inspect(event, true)} />
        <rect x={stripX - 13} y={g.top} width={44} height={g.bottom - g.top} fill="transparent" onPointerUp={event => {
          if (!layers.gaps) return;
          const bounds = event.currentTarget.ownerSVGElement!.getBoundingClientRect();
          const py = (event.clientY - bounds.top) * g.height / bounds.height;
          const core = BEATTY.cores.find(c => py > g.y(c.upper) && py < g.y(c.lower));
          if (core) { setHover(null); onSelect({ kind: "jump", order: core.order }); }
        }} />
      </svg>
      {hover && <div className="beatty-tooltip" role="tooltip" style={{ left: Math.max(0, Math.min(width - 252, hover.px + 12)), top: Math.max(0, Math.min(g.height - 125, hover.py + 12)) }}>
        <div>Phase {hover.phase.toFixed(6)}</div>
        {layers.profile && <div>F₅₀₄₇ ≈ {beattyLevel(hover.phase).toFixed(6)}</div>}
        {layers.band && <div>F(t) ≤ {beattyBounds(hover.phase)[1].toFixed(6)}</div>}
        {layers.samples && hover.sample && <><div>Nearest sample r = {hover.sample.order}</div><div>R⁺ ≈ {hover.sample.ratio.toFixed(6)}</div></>}
      </div>}
    </div>
  );
}
