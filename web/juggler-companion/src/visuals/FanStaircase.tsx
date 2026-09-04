import fanData from "../data/fan.json";

type FanRow = { k: number; L: number; o: number; lam: number; nmax: number };
const FAN = fanData as FanRow[];

const FLOORS = [
  { n: 1_000_000, label: "10⁶" },
  { n: 26_254_995, label: "2.6·10⁷" },
  { n: 162_849_448, label: "1.6·10⁸" },
  { n: 350_000_000, label: "3.5·10⁸" },
];

/** Which fan member the bound reaches at a given floor: the least k with n_max(L_k) > N0. */
export function reachedAt(n0: number): number {
  const hit = FAN.find((r) => r.nmax > n0);
  return hit ? hit.k : FAN.length;
}

/**
 * The price list of Section 5.8. Height is the descent floor each step costs,
 * on a log scale; the shaded band is what the certified floors have paid for.
 */
export function FanStaircase({ height = 220 }: { height?: number }) {
  const w = 720;
  const padL = 52;
  const padB = 34;
  const padT = 12;
  const lo = Math.log10(FAN[0].nmax);
  const hi = Math.log10(FAN[FAN.length - 1].nmax);
  const x = (k: number) => padL + (k / (FAN.length - 1)) * (w - padL - 12);
  const y = (nmax: number) =>
    padT + (1 - (Math.log10(nmax) - lo) / (hi - lo)) * (height - padT - padB);

  const best = FLOORS[FLOORS.length - 1];
  const reached = reachedAt(best.n);

  return (
    <figure className="space-y-2">
      <svg viewBox={`0 0 ${w} ${height}`} className="w-full" role="img"
           aria-label="Descent floor required for each member of the semiconvergent fan">
        {/* the region the certified floors already cover */}
        <rect x={padL} y={padT} width={x(reached) - padL} height={height - padT - padB}
              className="fill-emerald-500/10" />
        <line x1={x(reached)} x2={x(reached)} y1={padT} y2={height - padB}
              className="stroke-emerald-500" strokeDasharray="3 3" strokeWidth={1.5} />

        {FLOORS.map((f) => (
          <g key={f.n}>
            <line x1={padL} x2={w - 12} y1={y(f.n)} y2={y(f.n)}
                  className="stroke-line" strokeDasharray="2 4" />
            <text x={padL - 6} y={y(f.n) + 3} textAnchor="end"
                  className="fill-muted font-mono text-[9px]">{f.label}</text>
          </g>
        ))}

        <path d={FAN.map((r, i) => `${i ? "L" : "M"}${x(r.k)},${y(r.nmax)}`).join(" ")}
              className="stroke-sky-500" fill="none" strokeWidth={1.5} />
        {FAN.filter((r) => r.k % 5 === 0 || r.k === 55).map((r) => (
          <circle key={r.k} cx={x(r.k)} cy={y(r.nmax)} r={2.5}
                  className={r.k < reached ? "fill-emerald-500" : "fill-sky-500"} />
        ))}

        <text x={x(0)} y={height - 20} textAnchor="middle"
              className="fill-muted font-mono text-[9px]">k=0</text>
        <text x={x(55)} y={height - 20} textAnchor="middle"
              className="fill-muted font-mono text-[9px]">k=55</text>
        <text x={x(reached)} y={height - 8} textAnchor="middle"
              className="fill-emerald-600 font-mono text-[9px]">
          reached: L₍{reached}₎
        </text>
      </svg>
      <figcaption className="text-xs text-muted">
        Each point is a fan member <Code>L_k = 176251 + 301994k</Code>; its height is
        <Code>n_max(L_k)</Code>, the descent floor at which finance alone passes it.
        Dashed lines are the four certified floors. The shaded region is what has been
        paid for: the bound today stands at <Code>L₂ = 780239</Code>, and the walk charge
        buys about a factor 8 on top, so the next step costs roughly{" "}
        <Code>5.5·10⁸</Code> rather than <Code>4.5·10⁹</Code>.
      </figcaption>
    </figure>
  );
}

/** Λ_k is affine and hits zero just past k = 55 — which is why the fan is 56 long. */
export function FanLambda({ height = 150 }: { height?: number }) {
  const w = 720;
  const padL = 52;
  const padB = 28;
  const padT = 10;
  const max = FAN[0].lam;
  const x = (k: number) => padL + (k / 56) * (w - padL - 12);
  const y = (lam: number) => padT + (1 - lam / max) * (height - padT - padB);
  const zero = 56 - FAN[55].lam / (FAN[0].lam - FAN[1].lam);

  return (
    <figure className="space-y-2">
      <svg viewBox={`0 0 ${w} ${height}`} className="w-full" role="img"
           aria-label="The linear form Lambda is affine in k and changes sign just past k = 55">
        <line x1={padL} x2={w - 12} y1={y(0)} y2={y(0)} className="stroke-line" />
        <path d={FAN.map((r, i) => `${i ? "L" : "M"}${x(r.k)},${y(r.lam)}`).join(" ")}
              className="stroke-sky-500" fill="none" strokeWidth={1.5} />
        <circle cx={x(55)} cy={y(FAN[55].lam)} r={3} className="fill-emerald-500" />
        <line x1={x(zero)} x2={x(zero)} y1={padT} y2={height - padB}
              className="stroke-rose-500" strokeDasharray="3 3" />
        <text x={x(zero) + 4} y={padT + 10} className="fill-rose-500 font-mono text-[9px]">
          Λ = 0 at k = {zero.toFixed(2)}
        </text>
        <text x={padL - 6} y={y(0) + 3} textAnchor="end"
              className="fill-muted font-mono text-[9px]">0</text>
      </svg>
      <figcaption className="text-xs text-muted">
        <Code>Λ_k = o_k log 3 − L_k log 2</Code> is exactly affine in <Code>k</Code>, so the
        fan ends where it crosses zero: <Code>Λ₀/|Λ′| = 55.81</Code>, giving 56 members.
        The last one is <Code>L₅₅ = 16785921 = q₁₄</Code>, the next convergent — the fan
        stops precisely where the continued fraction of <Code>log 2 / log 3</Code> turns over.
      </figcaption>
    </figure>
  );
}

function Code({ children }: { children: React.ReactNode }) {
  return <code className="font-mono text-[0.95em]">{children}</code>;
}
