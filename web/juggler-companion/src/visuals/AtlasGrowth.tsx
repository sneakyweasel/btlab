import { useId } from "react";
import { growthRatios } from "../juggler/beattyAtlas";
import { useWidth } from "./useWidth";

/** Bars of log Q_(k+1) / log Q_k over a certified prefix of partial quotients. */
export function AtlasGrowth({ quotients }: { quotients: readonly number[] }) {
  const [ref, width] = useWidth<HTMLDivElement>();
  const titleId = useId();
  const rows = growthRatios(quotients);
  if (!rows.length) return null;
  const height = 170, left = 40, right = width - 10, top = 10, bottom = height - 30;
  const yMax = Math.max(2, Math.ceil(Math.max(...rows.map(r => r.ratio)) * 2) / 2);
  const y = (v: number) => bottom - (v - 0.8) / (yMax - 0.8) * (bottom - top);
  const bw = (right - left) / rows.length;
  return (
    <div ref={ref}>
      <svg viewBox={`0 0 ${width} ${height}`} height={height} className="beatty-chart" role="img" aria-labelledby={titleId}>
        <title id={titleId}>Growth ratios of convergent denominators</title>
        {[1, yMax].map(v => <g key={v}>
          <line x1={left} x2={right} y1={y(v)} y2={y(v)} stroke="var(--color-line)" strokeWidth={v === 1 ? 1.2 : 0.6} />
          <text x={left - 6} y={y(v) + 4} textAnchor="end" fontSize={11}>{v}</text>
        </g>)}
        {rows.map((r, i) => <g key={r.k}>
          <rect x={left + i * bw + 1} y={y(r.ratio)} width={Math.max(1, bw - 2)} height={y(1) - y(r.ratio)}
            fill={r.a >= 10 ? "var(--color-odd)" : "var(--color-even)"} opacity={0.8}>
            <title>{`k = ${r.k}: log Q_${r.k + 1} / log Q_${r.k} = ${r.ratio.toFixed(4)} (next quotient ${r.a})`}</title>
          </rect>
          {r.a >= 10 && <text x={left + (i + 0.5) * bw} y={y(r.ratio) - 4} textAnchor="middle" fontSize={10}>{r.a}</text>}
        </g>)}
        <text x={(left + right) / 2} y={height - 6} textAnchor="middle" fontSize={11}>Convergent index k (orange: next partial quotient ≥ 10)</text>
      </svg>
    </div>
  );
}
