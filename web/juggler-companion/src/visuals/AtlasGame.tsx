import { useId } from "react";
import { lawDim, starDim, type Pattern } from "../juggler/beattyAtlas";
import { useWidth } from "./useWidth";

type Props = { pattern: Pattern; upper: number; lower: number; gammas: readonly number[]; nu: number };

/** Verdict strip over s in [0, 2/3] and one period of the growth pattern with its window exponents. */
export function AtlasGame({ pattern, upper, lower, gammas, nu }: Props) {
  const [ref, width] = useWidth<HTMLDivElement>();
  const titleId = useId(), descId = useId();
  const left = 16, right = width - 16, sMax = 2 / 3;
  const sx = (s: number) => left + s / sMax * (right - left);
  const weights = pattern.map(e => Math.log(Math.max(e.t, 1.02)));
  const total = weights.reduce((a, b) => a + b, 0);
  const segments = pattern.map((e, i) => {
    const before = weights.slice(0, i).reduce((a, b) => a + b, 0);
    const jumpIndex = pattern.slice(0, i).filter(x => x.kind === "g").length;
    return { ...e, x: left + before / total * (right - left), w: weights[i] / total * (right - left), gamma: e.kind === "g" ? gammas[jumpIndex] : undefined };
  });
  const ticks = [0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 2 / 3];
  return (
    <div ref={ref}>
      <svg viewBox={`0 0 ${width} 214`} height={214} className="beatty-chart" role="img" aria-labelledby={`${titleId} ${descId}`}>
        <title id={titleId}>Where the cover recursion and the window measure meet</title>
        <desc id={descId}>Teal: exponents s the window measure supports. Orange: exponents where the cover recursion forces zero s-measure. Any gap between them is unresolved by the model.</desc>
        <text x={left} y={14} className="atlas-point-label">Exponent s</text>
        <rect x={sx(0)} y={24} width={sx(lower) - sx(0)} height={26} fill="var(--color-even)" opacity={0.75} />
        <rect x={sx(lower)} y={24} width={Math.max(0, sx(upper) - sx(lower))} height={26} fill="var(--color-line)" />
        <rect x={sx(upper)} y={24} width={sx(sMax) - sx(upper)} height={26} fill="var(--color-odd)" opacity={0.75} />
        {[{ s: lawDim(nu), label: "2/(2+ν)" }, { s: starDim(nu), label: "s*(ν)" }].map(m => <g key={m.label}>
          <line x1={sx(m.s)} x2={sx(m.s)} y1={20} y2={56} stroke="var(--color-ink)" strokeWidth={1} strokeDasharray="2 2" />
          <text x={sx(m.s)} y={70} textAnchor="middle" className="atlas-point-label">{m.label}</text>
        </g>)}
        {ticks.map(s => <text key={s} x={sx(s)} y={88} textAnchor="middle" fontSize={11}>{s === sMax ? "2/3" : s.toFixed(1)}</text>)}
        <text x={left} y={120} className="atlas-point-label">One period of log Q growth (width ∝ log t)</text>
        {segments.map((s, i) => <g key={i}>
          <rect x={s.x + 1} y={130} width={Math.max(2, s.w - 2)} height={30} rx={3}
            fill={s.kind === "g" ? "var(--color-odd)" : "var(--color-even)"} opacity={s.kind === "g" ? 0.25 : 0.18} stroke={s.kind === "g" ? "var(--color-odd)" : "var(--color-even)"} />
          {s.gamma !== undefined && s.t > 1 && <>
            <rect x={s.x + 1} y={130} width={Math.max(0, (s.gamma - 1) / (s.t - 1) * (s.w - 2))} height={30} rx={3} fill="var(--color-odd)" opacity={0.55} />
          </>}
          {s.w > 44 && <text x={s.x + s.w / 2} y={178} textAnchor="middle" fontSize={11}>
            {s.kind === "g" ? `jump ${s.t}` : `dense ${s.t >= 1e4 ? s.t.toExponential(0) : s.t}`}
          </text>}
          {s.w > 44 && s.gamma !== undefined && <text x={s.x + s.w / 2} y={194} textAnchor="middle" fontSize={11} fill="var(--color-muted)">γ = {s.gamma.toFixed(3)}</text>}
        </g>)}
      </svg>
    </div>
  );
}
