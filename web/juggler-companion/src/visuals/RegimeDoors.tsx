import { formatInt } from "../juggler/format";
import { idealExponentApprox, type Regime } from "../juggler/itinerary";
import { EMBER, SEA } from "../juggler/palette";

type RegimeDoorsProps = {
  prefix: string;
  odds: number;
  length: number;
  regime: Regime;
};

function powerLine(base: number, exp: number, value: bigint): string {
  if (exp === 0) return `${base}^0 = 1`;
  const shown = formatInt(value);
  if (shown.startsWith("~") || shown.includes("…")) return `${base}^${exp}`;
  return `${base}^${exp} = ${shown}`;
}

function formatRatio(value: number): string {
  if (!Number.isFinite(value)) return "—";
  if (value !== 0 && (value < 0.01 || value >= 100)) {
    const exp = Math.floor(Math.log10(Math.abs(value)));
    return `${(value / 10 ** exp).toFixed(2)}×10^${exp}`;
  }
  return value.toFixed(3);
}

function RegimeBlock({
  kind,
  active,
}: {
  kind: "expanding" | "contracting";
  active: boolean;
}) {
  const expanding = kind === "expanding";
  const color = expanding ? EMBER : SEA;
  return (
    <div
      className={`flex flex-1 flex-col items-center justify-center gap-1 px-2 py-3 text-center ${
        active ? "" : "opacity-45"
      }`}
    >
      <p className="font-serif text-base leading-tight" style={{ color }}>
        {expanding ? "Expanding" : "Contracting"}
      </p>
      <p className="text-xs text-muted">
        {expanding ? (
          <>
            3<sup>o</sup> &gt; 2<sup>L</sup>
          </>
        ) : (
          <>
            3<sup>o</sup> &lt; 2<sup>L</sup>
          </>
        )}
      </p>
      <p className="text-3xl leading-none" style={{ color }} aria-hidden>
        {expanding ? "⬆" : "⬇"}
      </p>
      <p className="text-xs" style={{ color }}>
        {expanding ? "grows" : "shrinks"}
      </p>
    </div>
  );
}

function RatioBar({ odds, length }: { odds: number; length: number }) {
  const leftLog = Math.max(odds, 0) * Math.log(3);
  const rightLog = Math.max(length, 0) * Math.log(2);
  const total = leftLog + rightLog;
  const leftPct = total === 0 ? 50 : (100 * leftLog) / total;
  const numer = 3n ** BigInt(Math.max(odds, 0));
  const denom = 2n ** BigInt(Math.max(length, 0));
  const approx = length === 0 ? 1 : idealExponentApprox(odds, length);
  return (
    <div className="border-y border-line bg-paper px-2.5 py-2">
      <div className="flex items-baseline justify-between gap-2 font-mono text-[11px] leading-tight">
        <span style={{ color: EMBER }}>{powerLine(3, odds, numer)}</span>
        <span style={{ color: SEA }}>{powerLine(2, length, denom)}</span>
      </div>
      <div
        className="relative mt-1.5 h-3 overflow-hidden rounded-full"
        role="img"
        aria-label={`Ideal ratio 3^${odds} / 2^${length} is ${formatRatio(approx)}`}
      >
        <div className="absolute inset-0 flex">
          <div style={{ width: `${leftPct}%`, background: EMBER }} />
          <div style={{ width: `${100 - leftPct}%`, background: SEA }} />
        </div>
        <div
          className="absolute top-0 bottom-0 w-px bg-ink/70"
          style={{ left: "50%" }}
          aria-hidden
        />
      </div>
      <p className="mt-1.5 text-center font-mono text-[11px] text-muted">
        3<sup>o</sup>/2<sup>L</sup> ≈ {formatRatio(approx)}
      </p>
    </div>
  );
}

export function RegimeDoors({ prefix, odds, length, regime }: RegimeDoorsProps) {
  return (
    <div className="flex h-full min-h-0 flex-col overflow-hidden rounded-2xl border border-line bg-card">
      <RegimeBlock kind="expanding" active={regime === "expanding"} />
      <RatioBar odds={odds} length={length} />
      <RegimeBlock kind="contracting" active={regime === "contracting"} />
      <p className="px-2 pb-2 text-center text-xs text-muted">
        {length === 0
          ? "No letters yet. Play to grow the prefix."
          : regime === "critical"
            ? `${prefix} is critical: 3^${odds} = 2^${length}.`
            : `${prefix || "—"} is ${regime}. A loop must expand.`}
      </p>
    </div>
  );
}
