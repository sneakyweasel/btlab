import { Metric } from "../components/Metric";
import { Tex } from "../components/Tex";
import type { SweepLemmaView } from "../juggler/productions";

type SweepLemmaProps = {
  lemma: SweepLemmaView;
};

const VERDICT: Record<
  SweepLemmaView["verdict"],
  { label: string; hint: string; tone: "ok" | "warn" | "muted" }
> = {
  empty: {
    label: "Empty fiber",
    hint: "No odd n on this Φ(m).",
    tone: "muted",
  },
  good: {
    label: "Good — Lemma 4.2",
    hint: "Both windows pass at m ≥ 10⁶. Scarcer half ≥ H/3 − 2.",
    tone: "ok",
  },
  "thin-zero": {
    label: "Thin — near 0",
    hint: "The step is closer to 0 than 22 m^{-1/3}. The lemma does not apply; the walk can crawl.",
    tone: "warn",
  },
  "thin-half": {
    label: "Thin — near 1/2",
    hint: "The step is closer to 1/2 than 2 m^{-1/3}. The two-step can lock a half.",
    tone: "warn",
  },
  "below-scale": {
    label: "Windows ok, below 10⁶",
    hint: "The same windows would pass, but Lemma 4.2 is stated for m ≥ 10⁶.",
    tone: "muted",
  },
};

function formatPhase(value: number | null): string {
  if (value === null || !Number.isFinite(value)) return "—";
  return value.toFixed(4);
}

function formatFloor(value: number): string {
  return value.toFixed(1);
}

function ShareBar({ lemma }: { lemma: SweepLemmaView }) {
  if (lemma.H === 0) return null;
  const share = lemma.scarcer / lemma.H;
  const marks = [
    { x: 100 / 7, label: "1/7" },
    { x: 100 / 3, label: "1/3" },
    { x: 50, label: "1/2" },
  ];
  return (
    <svg viewBox="0 0 640 56" role="img" className="h-auto w-full">
      <title>Scarcer half of the fiber against the sweep and pairing floors</title>
      <rect x="36" y="18" width="568" height="10" fill="#e8e2d4" rx="5" />
      <rect
        x="36"
        y="18"
        width={Math.max(0, Math.min(568, 568 * share))}
        height="10"
        fill={share + 1e-12 >= 1 / 7 ? "#1f6f6a" : "#8b3a2a"}
        rx="5"
      />
      {marks.map((mark) => (
        <g key={mark.label}>
          <line
            x1={36 + (568 * mark.x) / 100}
            y1="14"
            x2={36 + (568 * mark.x) / 100}
            y2="32"
            stroke="#1d1914"
            strokeWidth="1"
          />
          <text
            x={36 + (568 * mark.x) / 100}
            y="48"
            textAnchor="middle"
            fill="#5e574c"
            fontSize="11"
            fontFamily="IBM Plex Mono, monospace"
          >
            {mark.label}
          </text>
        </g>
      ))}
      <circle
        cx={36 + 568 * share}
        cy="23"
        r="5"
        fill="#1d1914"
      />
    </svg>
  );
}

export function SweepLemma({ lemma }: SweepLemmaProps) {
  const verdict = VERDICT[lemma.verdict];
  const tone =
    verdict.tone === "ok"
      ? "border-ok/40 text-ok"
      : verdict.tone === "warn"
        ? "border-warn/40 text-warn"
        : "border-line text-muted";
  return (
    <div className="space-y-3">
      <div className="flex flex-wrap items-center gap-2">
        <span className={`rounded-full border px-3 py-1 text-sm ${tone}`}>
          {verdict.label}
        </span>
        <span className="text-sm text-muted">
          {lemma.atLemmaScale
            ? "m is at lemma scale"
            : "m is below 10⁶ — windows are drawn, not a proof"}
        </span>
      </div>
      <p className="text-sm text-muted">{verdict.hint}</p>
      <div className="grid gap-3 sm:grid-cols-4">
        <Metric
          label="α"
          value={formatPhase(lemma.alpha)}
          hint="first odd step on the fiber"
        />
        <Metric
          label="||α||"
          value={`${formatPhase(lemma.distZero)} / ${formatPhase(lemma.needZero)}`}
          hint="need ≥ 22 m^{-1/3}"
        />
        <Metric
          label="||α − 1/2||"
          value={`${formatPhase(lemma.distHalf)} / ${formatPhase(lemma.needHalf)}`}
          hint="need ≥ 2 m^{-1/3}"
        />
        <Metric
          label="scarcer"
          value={`${lemma.scarcer} vs ${formatFloor(lemma.sweepFloor)} and ${formatFloor(lemma.pairingFloor)}`}
          hint="H/7 and H/3 − 2"
        />
      </div>
      <ShareBar lemma={lemma} />
      <p className="text-center text-sm text-muted">
        Scarcer half <Tex>{String.raw`\min(G_m,H_m-G_m)`}</Tex>
        {lemma.meetsSweep === null
          ? "."
          : lemma.meetsSweep
            ? " meets 1/7"
            : " misses 1/7"}
        {lemma.meetsPairing === null
          ? ""
          : lemma.meetsPairing
            ? " and H/3 − 2."
            : " and misses H/3 − 2."}{" "}
        One fiber is an observation, not the sweep proof.
      </p>
    </div>
  );
}
