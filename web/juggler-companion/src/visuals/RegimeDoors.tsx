import type { ReactNode } from "react";
import { idealExponentApprox, type Regime } from "../juggler/itinerary";
import { EMBER, SEA } from "../juggler/palette";

type RegimeDoorsProps = {
  odds: number;
  length: number;
  regime: Regime;
};

function formatRatio(value: number): string {
  if (!Number.isFinite(value)) return "—";
  if (value !== 0 && (value < 0.01 || value >= 100)) {
    const exp = Math.floor(Math.log10(Math.abs(value)));
    return `${(value / 10 ** exp).toFixed(2)}×10^${exp}`;
  }
  return value.toFixed(3);
}

function Pole({
  color,
  title,
  formula,
  dimmed,
  reverse = false,
}: {
  color: string;
  title: string;
  formula: ReactNode;
  dimmed: boolean;
  reverse?: boolean;
}) {
  return (
    <div
      className={`flex w-full shrink-0 flex-col items-center justify-center gap-0.5 text-center ${
        reverse ? "flex-col-reverse" : ""
      } ${dimmed ? "opacity-40" : ""}`}
    >
      <p className="font-serif text-xl leading-none" style={{ color }}>
        {title}
      </p>
      <p className="font-serif text-base leading-none" style={{ color }}>
        {formula}
      </p>
    </div>
  );
}

export function RegimeDoors({ odds, length, regime }: RegimeDoorsProps) {
  const upLog = Math.max(odds, 0) * Math.log(3);
  const downLog = Math.max(length, 0) * Math.log(2);
  const total = upLog + downLog;
  const upPct = total === 0 ? 50 : (100 * upLog) / total;
  const approx = length === 0 ? 1 : idealExponentApprox(odds, length);
  const expanding = regime === "expanding";
  const contracting = regime === "contracting";

  return (
    <div className="flex h-full min-h-[28rem] w-full flex-col items-center rounded-2xl border border-line bg-card px-3 py-3">
      <Pole
        color={EMBER}
        title="Expanding"
        formula={
          <>
            3<sup>x</sup>
          </>
        }
        dimmed={!expanding}
      />

      <div
        className="relative min-h-0 w-full flex-1"
        role="img"
        aria-label={`${odds} odd, length ${length}; ideal ratio 3^${odds} / 2^${length} is ${formatRatio(approx)}`}
      >
        <div
          className="absolute inset-y-0 left-1/2 w-24 -translate-x-1/2 overflow-hidden rounded-full"
          style={{
            background: `linear-gradient(to bottom, ${EMBER} ${upPct}%, ${SEA} ${upPct}%)`,
          }}
        >
          <div
            className="absolute inset-x-0 top-0 flex items-center justify-center text-white"
            style={{ height: `${upPct}%` }}
          >
            <span className="font-serif text-3xl leading-none tabular-nums">
              3<sup className="text-xl">{odds}</sup>
            </span>
          </div>
          <div
            className="absolute inset-x-0 bottom-0 flex items-center justify-center text-white"
            style={{ height: `${100 - upPct}%` }}
          >
            <span className="font-serif text-3xl leading-none tabular-nums">
              2<sup className="text-xl">{length}</sup>
            </span>
          </div>
        </div>

        <div className="absolute inset-x-0 top-1/2 z-10 flex -translate-y-1/2 items-center gap-2">
          <div className="h-0.5 flex-1 bg-ink" />
          <p className="shrink-0 bg-card px-1.5 text-center font-serif text-sm leading-tight text-ink">
            3<sup>o</sup>/2<sup>L</sup> ≈ {formatRatio(approx)}
          </p>
          <div className="h-0.5 flex-1 bg-ink" />
        </div>
      </div>

      <Pole
        color={SEA}
        title="Contracting"
        formula={
          <>
            2<sup>L</sup>
          </>
        }
        dimmed={!contracting}
        reverse
      />
    </div>
  );
}
