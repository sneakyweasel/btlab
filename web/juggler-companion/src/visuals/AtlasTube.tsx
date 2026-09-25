import { useId, useMemo } from "react";
import { BEATTY, BEATTY_ROWS } from "../juggler/beatty";
import { tubeVolumeHead } from "../juggler/beattyAtlas";
import { useWidth } from "./useWidth";

const LOG_EPS = [-9, -0.5] as const;

/** Tube volume at log_2 3 from the first 5,047 gaps, on log-log axes, against slope 1/3. */
export function AtlasTube() {
  const [ref, width] = useWidth<HTMLDivElement>();
  const titleId = useId(), descId = useId();
  const weights = useMemo(() => BEATTY_ROWS.map(r => r.weight), []);
  const curve = useMemo(() => Array.from({ length: 90 }, (_, i) => {
    const le = LOG_EPS[0] + i / 89 * (LOG_EPS[1] - LOG_EPS[0]);
    const head = tubeVolumeHead(weights, 10 ** le);
    return { le, head: Math.log10(head), upper: Math.log10(head + Math.min(BEATTY.tailUpper, 1e9)) };
  }), [weights]);
  const height = 280, left = 52, right = width - 16, top = 14, bottom = height - 44;
  const yMin = Math.min(...curve.map(c => c.head)) - 0.2, yMax = 0.6;
  const x = (le: number) => left + (le - LOG_EPS[0]) / (LOG_EPS[1] - LOG_EPS[0]) * (right - left);
  const y = (lv: number) => bottom - (lv - yMin) / (yMax - yMin) * (bottom - top);
  const path = (key: "head" | "upper") => curve.map((c, i) => `${i ? "L" : "M"}${x(c.le)},${y(c[key])}`).join("");
  const anchor = curve[Math.floor(curve.length * 0.55)];
  const ref13 = `M${x(LOG_EPS[0])},${y(anchor.head + (LOG_EPS[0] - anchor.le) / 3)}L${x(LOG_EPS[1])},${y(anchor.head + (LOG_EPS[1] - anchor.le) / 3)}`;
  return (
    <div ref={ref}>
      <div className="beatty-legend" aria-label="Tube legend">
        <span><span className="beatty-swatch beatty-swatch-empirical" aria-hidden="true" />Head: 2ε + Σ min(w_r, 2ε), r ≤ 5,047</span>
        <span><span className="beatty-swatch" style={{ background: "var(--color-muted)" }} aria-hidden="true" />Head + omitted mass bound</span>
        <span><span className="beatty-swatch" style={{ background: "var(--color-deep)" }} aria-hidden="true" />Slope 1/3 reference</span>
      </div>
      <svg viewBox={`0 0 ${width} ${height}`} height={height} className="beatty-chart" role="img" aria-labelledby={`${titleId} ${descId}`}>
        <title id={titleId}>Neighbourhood volume of the cluster set at log₂3</title>
        <desc id={descId}>Log-log plot of the tube volume computed from the first 5,047 gaps. Below about epsilon = 1e-6 the omitted gaps dominate and the head curve underestimates the true volume.</desc>
        <rect x={left} y={top} width={right - left} height={bottom - top} fill="none" stroke="var(--color-line)" />
        {[-9, -7, -5, -3, -1].map(le => <text key={le} x={x(le)} y={bottom + 18} textAnchor="middle">10^{le}</text>)}
        {Array.from({ length: 10 }, (_, i) => -i).filter(v => v > yMin && v < yMax).map(v => <g key={v}>
          <line x1={left} x2={right} y1={y(v)} y2={y(v)} stroke="var(--color-line)" strokeWidth={0.6} />
          <text x={left - 8} y={y(v) + 4} textAnchor="end">10^{v}</text>
        </g>)}
        <text x={(left + right) / 2} y={height - 6} textAnchor="middle">ε</text>
        <text transform={`translate(13,${(top + bottom) / 2}) rotate(-90)`} textAnchor="middle">vol(K_ε)</text>
        <path d={ref13} fill="none" stroke="var(--color-deep)" strokeWidth={1.2} strokeDasharray="6 4" />
        <path d={path("upper")} fill="none" stroke="var(--color-muted)" strokeWidth={1.2} strokeDasharray="3 3" />
        <path d={path("head")} fill="none" stroke="var(--color-odd)" strokeWidth={2} />
      </svg>
    </div>
  );
}
