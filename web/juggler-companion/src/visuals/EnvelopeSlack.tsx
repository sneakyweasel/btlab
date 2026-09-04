import type { ReactNode } from "react";
import { Metric } from "../components/Metric";
import { Tex } from "../components/Tex";
import { formatInt } from "../juggler/format";
import {
  compareImage,
  envelopeCeilingApprox,
  envelopeRelativeRoom,
  envelopeSlack,
  plotMagnitude,
} from "../juggler/itinerary";
import { EMBER, SEA } from "../juggler/palette";

type EnvelopeFrame = {
  seed: bigint;
  image: bigint;
  odds: number;
  length: number;
};

function formatApprox(value: number): string {
  if (!Number.isFinite(value)) return "too large";
  const abs = Math.abs(value);
  if (abs !== 0 && (abs < 0.01 || abs >= 1e6)) {
    const exp = Math.floor(Math.log10(abs));
    return `${(value / 10 ** exp).toFixed(2)}×10^${exp}`;
  }
  if (abs >= 1000) return value.toFixed(0);
  if (abs >= 100) return value.toFixed(1);
  if (Number.isInteger(value)) return String(value);
  return value.toFixed(3);
}

function formatRoom(value: number): string {
  if (!Number.isFinite(value)) return "too large";
  if (value >= 1000) return value.toFixed(0);
  if (value >= 10) return value.toFixed(1);
  if (value >= 1) return value.toFixed(2);
  return value.toFixed(3);
}

function formatShare(value: number): string {
  if (!Number.isFinite(value)) return "—";
  const pct = value * 100;
  if (pct >= 1) return `${pct.toFixed(2)}%`;
  if (pct >= 0.01) return `${pct.toFixed(2)}%`;
  return `${pct.toExponential(1)}%`;
}

function valueRoom(ceiling: number, image: bigint): number | null {
  const pictured = plotMagnitude(image);
  if (!Number.isFinite(ceiling) || !Number.isFinite(pictured)) return null;
  return Math.max(0, ceiling - pictured);
}

function Pole({
  color,
  title,
  formula,
  reverse = false,
}: {
  color: string;
  title: string;
  formula: ReactNode;
  reverse?: boolean;
}) {
  return (
    <div
      className={`flex w-full shrink-0 flex-col items-center justify-center gap-0.5 text-center ${
        reverse ? "flex-col-reverse" : ""
      }`}
    >
      <p className="font-serif text-xl leading-none" style={{ color }}>
        {title}
      </p>
      <div className="font-serif text-base leading-tight" style={{ color }}>
        {formula}
      </div>
    </div>
  );
}

export function EnvelopeSlack({ seed, image, odds, length }: EnvelopeFrame) {
  const ceiling = envelopeCeilingApprox(seed, odds, length);
  const pictured = plotMagnitude(image);
  const room = valueRoom(ceiling, image);
  const exact = length === 0 ? 0n : envelopeSlack(seed, image, length, odds);
  const relative = length === 0 ? 0 : envelopeRelativeRoom(seed, image, length, odds);
  const fill =
    ceiling > 0 && Number.isFinite(ceiling) && Number.isFinite(pictured)
      ? Math.min(1, pictured / Math.max(ceiling, pictured))
      : 1;
  const slackPct = room !== null && room > 0 ? (1 - fill) * 100 : 0;
  const imagePct = 100 - slackPct;
  const mid =
    length === 0
      ? "slack 0"
      : exact !== null
        ? `Δ = ${formatInt(exact)}`
        : room !== null
          ? `room ≈ ${formatRoom(room)}`
          : "Δ too large";

  return (
    <div className="flex h-full min-h-[28rem] w-full flex-col items-center rounded-2xl border border-line bg-card px-3 py-3">
      <Pole
        color={EMBER}
        title="Ceiling"
        formula={
          <>
            n<sup>
              3<sup>{odds}</sup>/2<sup>{length}</sup>
            </sup>{" "}
            ≈ {formatApprox(ceiling)}
          </>
        }
      />

      <div
        className="relative min-h-0 w-full flex-1"
        role="img"
        aria-label={`Ceiling ${formatApprox(ceiling)}, image ${formatInt(image)}, ${mid}`}
      >
        <div className="absolute inset-y-0 left-1/2 w-24 -translate-x-1/2 overflow-hidden rounded-full bg-odd">
          <div
            className="absolute inset-x-0 bottom-0 flex items-center justify-center text-white"
            style={{ height: `${imagePct}%`, background: SEA }}
          >
            <span className="font-serif text-2xl leading-none tabular-nums">
              {formatInt(image)}
            </span>
          </div>
        </div>

        <div className="absolute inset-x-0 top-1/2 z-10 flex -translate-y-1/2 items-center gap-2">
          <div className="h-0.5 flex-1 bg-ink" />
          <div className="shrink-0 bg-card px-1.5 text-center font-serif text-sm leading-tight text-ink">
            <p>{mid}</p>
            {exact === null && Number.isFinite(relative) && relative > 0 ? (
              <p className="text-xs text-muted">
                {formatShare(relative)} of n<sup>3<sup>o</sup></sup>
              </p>
            ) : null}
          </div>
          <div className="h-0.5 flex-1 bg-ink" />
        </div>
      </div>

      <Pole
        color={SEA}
        title="Image"
        formula={
          <>
            T<sup>{length}</sup>(n) = {formatInt(image)}
          </>
        }
        reverse
      />
    </div>
  );
}

export function EnvelopePanel({ seed, image, odds, length }: EnvelopeFrame) {
  const exact = length === 0 ? 0n : envelopeSlack(seed, image, length, odds);
  const ceiling = envelopeCeilingApprox(seed, odds, length);
  const room = valueRoom(ceiling, image);
  const relative = length === 0 ? 0 : envelopeRelativeRoom(seed, image, length, odds);
  const slackValue =
    length === 0
      ? "0"
      : exact !== null
        ? formatInt(exact)
        : room !== null
          ? `≈ ${formatRoom(room)}`
          : "too large to show";
  const slackHint =
    exact !== null
      ? "n^{3^o} − image^{2^L}"
      : Number.isFinite(relative) && relative > 0
        ? `${formatShare(relative)} of n^{3^o}; exact Δ exceeds 80 bits`
        : "n^{3^o} − image^{2^L}, when the powers fit in 80 bits";

  return (
    <div className="space-y-3">
      <div className="grid gap-3 sm:grid-cols-2">
        <Metric
          label="Image vs n"
          value={`${formatInt(image)} ${compareImage(image, seed)} ${formatInt(seed)}`}
        />
        <Metric label="Slack Δ" value={slackValue} hint={slackHint} />
      </div>
      <Tex display>
        {length === 0
          ? String.raw`T^{0}(n)=n`
          : String.raw`T^{${length}}(n)^{2^{${length}}}\le n^{3^{${odds}}}`}
      </Tex>
    </div>
  );
}
