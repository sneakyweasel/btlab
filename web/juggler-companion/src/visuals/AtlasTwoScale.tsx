import { useId, useMemo, useState, type MouseEvent } from "react";
import { lawDim, starDim, twoScaleDim } from "../juggler/beattyAtlas";
import { useWidth } from "./useWidth";

const NU = [1.05, 8] as const;
const LOG_RHO = [0, 3] as const;
const COLUMNS = 70, ROWS = 42;

/** Share of the window [2/(2+nu), s*(nu)] that the two-scale dimension has climbed. */
function climb(nu: number, rho: number): number {
  const low = lawDim(nu), high = starDim(nu);
  return Math.min(1, Math.max(0, (twoScaleDim(nu, rho).s - low) / (high - low)));
}

export function AtlasTwoScale({ selected, onPick }: { selected: { nu: number; rho: number } | null; onPick: (nu: number, rho: number) => void }) {
  const [ref, width] = useWidth<HTMLDivElement>();
  const [hover, setHover] = useState<{ nu: number; rho: number } | null>(null);
  const titleId = useId(), descId = useId();
  const g = useMemo(() => {
    const height = 320, left = 52, right = width - 18, top = 14, bottom = height - 46;
    const x = (nu: number) => left + (nu - NU[0]) / (NU[1] - NU[0]) * (right - left);
    const y = (rho: number) => bottom - (Math.log10(rho) - LOG_RHO[0]) / (LOG_RHO[1] - LOG_RHO[0]) * (bottom - top);
    const cw = (right - left) / COLUMNS, ch = (bottom - top) / ROWS;
    const cells: { x: number; y: number; f: number; below: boolean }[] = [];
    for (let i = 0; i < COLUMNS; i++) for (let j = 0; j < ROWS; j++) {
      const nu = NU[0] + (i + 0.5) / COLUMNS * (NU[1] - NU[0]);
      const rho = 10 ** (LOG_RHO[0] + (j + 0.5) / ROWS * (LOG_RHO[1] - LOG_RHO[0]));
      cells.push({ x: left + i * cw, y: bottom - (j + 1) * ch, f: climb(nu, rho), below: rho <= 1 + 3 / nu });
    }
    const switchPath = Array.from({ length: 120 }, (_, i) => NU[0] + i / 119 * (NU[1] - NU[0]))
      .map((nu, i) => `${i ? "L" : "M"}${x(nu)},${y(1 + 3 / nu)}`).join("");
    return { height, left, right, top, bottom, x, y, cw, ch, cells, switchPath };
  }, [width]);
  const at = (event: MouseEvent<SVGRectElement>) => {
    const box = event.currentTarget.getBoundingClientRect();
    const fx = (event.clientX - box.left) / box.width, fy = 1 - (event.clientY - box.top) / box.height;
    return { nu: NU[0] + fx * (NU[1] - NU[0]), rho: 10 ** (LOG_RHO[0] + fy * (LOG_RHO[1] - LOG_RHO[0])) };
  };
  const readout = hover ?? selected;
  const value = readout ? twoScaleDim(readout.nu, readout.rho) : null;
  return (
    <div ref={ref}>
      <svg viewBox={`0 0 ${width} ${g.height}`} height={g.height} className="beatty-chart" role="img" aria-labelledby={`${titleId} ${descId}`}>
        <title id={titleId}>Two-scale dimension over jump size and dense-stretch length</title>
        <desc id={descId}>Shading shows how far the two-scale dimension climbs from 2/(2+nu) towards s*(nu). Below the curve rho = 1 + 3/nu windows do not help and the dimension equals 2/(2+nu).</desc>
        {g.cells.map((c, i) => <rect key={i} x={c.x} y={c.y} width={g.cw + 0.6} height={g.ch + 0.6}
          fill={c.below ? "var(--color-even)" : "var(--color-odd)"} opacity={c.below ? 0.12 : 0.08 + 0.8 * c.f} />)}
        <path d={g.switchPath} fill="none" stroke="var(--color-ink)" strokeWidth={1.6} strokeDasharray="5 3" />
        <text x={g.x(1.35)} y={g.y(1 + 3 / 1.35) - 8} className="atlas-curve-label">ρ = 1 + 3/ν</text>
        <rect x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} fill="none" stroke="var(--color-line)" />
        {[1, 2, 3, 4, 5, 6, 7, 8].map(nu => <text key={nu} x={g.x(nu)} y={g.bottom + 18} textAnchor="middle">{nu}</text>)}
        {[1, 10, 100, 1000].map(rho => <text key={rho} x={g.left - 8} y={g.y(rho) + 4} textAnchor="end">{rho}</text>)}
        <text x={(g.left + g.right) / 2} y={g.height - 6} textAnchor="middle">Jump ν</text>
        <text transform={`translate(13,${(g.top + g.bottom) / 2}) rotate(-90)`} textAnchor="middle">Dense stretch ρ</text>
        {selected && <circle cx={g.x(selected.nu)} cy={g.y(selected.rho)} r={6} fill="none" stroke="var(--color-ink)" strokeWidth={2} pointerEvents="none" />}
        <rect x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} fill="transparent" style={{ cursor: "crosshair" }}
          onPointerMove={event => setHover(at(event))} onPointerLeave={() => setHover(null)}
          onClick={event => { const p = at(event); onPick(Math.round(p.nu * 100) / 100, Math.round(p.rho * 100) / 100); }} />
      </svg>
      <p className="mt-2 min-h-[1.5rem] text-sm tabular-nums text-muted" aria-live="polite">
        {readout && value
          ? `ν = ${readout.nu.toFixed(2)}, ρ = ${readout.rho.toFixed(2)} · dim = ${value.s.toFixed(6)} · window exponent γ = ${value.gamma.toFixed(4)} · ${readout.rho <= 1 + 3 / readout.nu ? "windows do not help: dim = 2/(2+ν)" : `${(100 * climb(readout.nu, readout.rho)).toFixed(1)}% of the way to s*(ν)`}`
          : "Hover for the closed form; click to load that two-scale pattern into the game."}
      </p>
    </div>
  );
}
