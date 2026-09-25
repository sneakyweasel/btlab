import { useId, useMemo, useState, type MouseEvent } from "react";
import { lawDim, starDim } from "../juggler/beattyAtlas";
import { useWidth } from "./useWidth";

export type MapPoint = { nu: number; s: number; label: string; tone: "model" | "slope" };

const NU_MAX = 10;
const Y_MAX = 0.72;

export function AtlasDimensionMap({ points, onPick }: { points: readonly MapPoint[]; onPick: (nu: number) => void }) {
  const [ref, width] = useWidth<HTMLDivElement>();
  const [hover, setHover] = useState<number | null>(null);
  const titleId = useId(), descId = useId();
  const g = useMemo(() => {
    const height = 340, left = 52, right = width - 18, top = 18, bottom = height - 46;
    const x = (nu: number) => left + (nu - 1) / (NU_MAX - 1) * (right - left);
    const y = (s: number) => bottom - s / Y_MAX * (bottom - top);
    const samples = Array.from({ length: 181 }, (_, i) => 1 + i * (NU_MAX - 1) / 180);
    const line = (f: (nu: number) => number) => samples.map((nu, i) => `${i ? "L" : "M"}${x(nu)},${y(f(nu))}`).join("");
    const band = line(starDim) + samples.slice().reverse().map(nu => `L${x(nu)},${y(lawDim(nu))}`).join("") + "Z";
    return { height, left, right, top, bottom, x, y, star: line(starDim), law: line(lawDim), band };
  }, [width]);
  const nuAt = (event: MouseEvent<SVGRectElement>) => {
    const box = event.currentTarget.getBoundingClientRect();
    const px = (event.clientX - box.left) / box.width * (g.right - g.left);
    return Math.min(NU_MAX, Math.max(1, 1 + px / (g.right - g.left) * (NU_MAX - 1)));
  };
  return (
    <div ref={ref} className="relative">
      <svg viewBox={`0 0 ${width} ${g.height}`} height={g.height} className="beatty-chart" role="img" aria-labelledby={`${titleId} ${descId}`}>
        <title id={titleId}>Hausdorff dimension of the cluster set against the Diophantine class</title>
        <desc id={descId}>For approximation exponent nu the Hausdorff dimension lies between the law dimension 2/(2+nu) and s*(nu); the packing dimension is 2/3 for every slope.</desc>
        <rect x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} fill="none" stroke="var(--color-line)" />
        {[0, 0.2, 0.4, 0.6].map(s => <g key={s}>
          <line x1={g.left} x2={g.right} y1={g.y(s)} y2={g.y(s)} stroke="var(--color-line)" strokeWidth={0.6} />
          <text x={g.left - 8} y={g.y(s) + 4} textAnchor="end">{s.toFixed(1)}</text>
        </g>)}
        {[1, 2, 3, 4, 5, 6, 7, 8, 9, 10].filter(nu => width > 480 || nu % 3 === 1).map(nu =>
          <text key={nu} x={g.x(nu)} y={g.bottom + 18} textAnchor="middle">{nu}</text>)}
        <text x={(g.left + g.right) / 2} y={g.height - 6} textAnchor="middle">Diophantine class ν (|qα − p| ≤ q^−ν infinitely often)</text>
        <text transform={`translate(13,${(g.top + g.bottom) / 2}) rotate(-90)`} textAnchor="middle">Dimension</text>
        <path d={g.band} fill="var(--color-odd)" opacity={0.1} />
        <line x1={g.left} x2={g.right} y1={g.y(2 / 3)} y2={g.y(2 / 3)} stroke="var(--color-deep)" strokeWidth={1.4} strokeDasharray="6 4" />
        <path d={g.star} fill="none" stroke="var(--color-odd)" strokeWidth={2} />
        <path d={g.law} fill="none" stroke="var(--color-even)" strokeWidth={2} />
        <text x={g.right - 6} y={g.y(2 / 3) - 7} textAnchor="end" className="atlas-curve-label">packing dim of K and of μ = 2/3</text>
        <text x={g.x(6.2)} y={g.y(starDim(6.2)) - 8} className="atlas-curve-label" fill="var(--color-odd)">s*(ν): isolated levels</text>
        <text x={g.x(4.2)} y={g.y(lawDim(4.2)) + 22} className="atlas-curve-label">2/(2+ν): law, regular growth</text>
        {hover !== null && <g pointerEvents="none">
          <line x1={g.x(hover)} x2={g.x(hover)} y1={g.top} y2={g.bottom} stroke="var(--color-muted)" strokeWidth={0.8} />
          <circle cx={g.x(hover)} cy={g.y(starDim(hover))} r={3.5} fill="var(--color-odd)" />
          <circle cx={g.x(hover)} cy={g.y(lawDim(hover))} r={3.5} fill="var(--color-even)" />
        </g>}
        {points.filter(p => Number.isFinite(p.nu) && p.nu <= NU_MAX).map(p => <g key={p.label} pointerEvents="none">
          {p.tone === "model"
            ? <rect x={g.x(p.nu) - 5} y={g.y(p.s) - 5} width={10} height={10} fill="var(--color-card)" stroke="var(--color-ink)" strokeWidth={1.8} transform={`rotate(45 ${g.x(p.nu)} ${g.y(p.s)})`} />
            : <circle cx={g.x(p.nu)} cy={g.y(p.s)} r={6} fill="var(--color-deep)" stroke="var(--color-card)" strokeWidth={2} />}
          <text x={g.x(p.nu) + 10} y={g.y(p.s) + (p.tone === "model" ? 18 : -10)} className="atlas-point-label">{p.label}</text>
        </g>)}
        <rect x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} fill="transparent" style={{ cursor: "crosshair" }}
          onPointerMove={event => setHover(nuAt(event))} onPointerLeave={() => setHover(null)}
          onClick={event => onPick(Math.round(nuAt(event) * 20) / 20)} />
      </svg>
      <p className="mt-2 min-h-[1.5rem] text-sm tabular-nums text-muted" aria-live="polite">
        {hover === null
          ? "Hover to read both bounds; click to load the regular slope of that class into the game."
          : `ν = ${hover.toFixed(2)} · law dimension 2/(2+ν) = ${lawDim(hover).toFixed(5)} · s*(ν) = ${starDim(hover).toFixed(5)} · window ${(starDim(hover) - lawDim(hover)).toFixed(5)}`}
      </p>
    </div>
  );
}
