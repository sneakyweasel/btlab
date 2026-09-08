import { Metric } from "../components/Metric";
import { Tex } from "../components/Tex";
import { EVEN } from "../juggler/palette";
import type { BlockAverageView } from "../juggler/productions";

type BlockAverageProps = {
  view: BlockAverageView;
};

function formatShare(value: number | null): string {
  if (value === null || !Number.isFinite(value)) return "—";
  return value.toFixed(3);
}

function formatCount(value: number): string {
  if (Math.abs(value) >= 1000) return value.toFixed(0);
  return value.toFixed(1);
}

function ShareBar({
  share,
  marks,
  title,
}: {
  share: number;
  marks: { x: number; label: string }[];
  title: string;
}) {
  const clamped = Math.max(0, Math.min(1, share));
  return (
    <svg viewBox="0 0 640 56" role="img" className="h-auto w-full">
      <title>{title}</title>
      <rect x="36" y="18" width="568" height="10" fill="#e8e2d4" rx="5" />
      <rect
        x="36"
        y="18"
        width={568 * clamped}
        height="10"
        fill={EVEN}
        rx="5"
      />
      {marks.map((mark) => (
        <g key={mark.label}>
          <line
            x1={36 + 568 * mark.x}
            y1="14"
            x2={36 + 568 * mark.x}
            y2="32"
            stroke="#1d1914"
            strokeWidth="1"
          />
          <text
            x={36 + 568 * mark.x}
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
      <circle cx={36 + 568 * clamped} cy="23" r="5" fill="#1d1914" />
    </svg>
  );
}

export function BlockAverage({ view }: BlockAverageProps) {
  return (
    <div className="space-y-3">
      <div className="flex flex-wrap items-center gap-2">
        <span
          className={`rounded-full border px-3 py-1 text-sm ${
            view.boundPositive
              ? "border-ok/40 text-ok"
              : "border-line text-muted"
          }`}
        >
          {view.boundPositive
            ? "Proved error below 1/4"
            : "Error still larger than 1/4"}
        </span>
        <span className="text-sm text-muted">
          {view.boundPositive
            ? "This m' is large enough that C₀=250 is smaller than #odds/4."
            : "Playground m' — the bar is an observation, not Proposition 4.4."}
        </span>
      </div>
      <div className="grid gap-3 sm:grid-cols-4">
        <Metric
          label="U"
          value={String(view.U)}
          hint="even images on even-m fibers"
        />
        <Metric
          label="#odds"
          value={String(view.H)}
          hint="odd n on every fiber of the block"
        />
        <Metric
          label="U / odds"
          value={`${formatShare(view.share)} / 0.250`}
          hint="need 1/4 after the error"
        />
        <Metric
          label="error"
          value={`${formatCount(view.errorTerm)} vs ${formatCount(view.quarter)}`}
          hint="250 m'^{11/9} log(m'+1)"
        />
      </div>
      {view.share !== null ? (
        <ShareBar
          share={view.share}
          marks={[
            { x: 1 / 4, label: "1/4" },
            { x: 1 / 2, label: "1/2" },
          ]}
          title="Even images over all odd n on the block, against 1/4"
        />
      ) : null}
      <p className="text-center text-sm text-muted">
        <Tex>{String.raw`|U|/\#\{\text{odd }n\}`}</Tex>
        {view.share === null
          ? "."
          : view.share + 1e-12 >= 1 / 4
            ? " meets 1/4 on this block."
            : " misses 1/4 on this block."}{" "}
        Weighted even-fiber share{" "}
        <Tex>{String.raw`U/H_{\mathrm{even}}`}</Tex> is{" "}
        {formatShare(view.meanEven)}. One block is an observation, not the
        exponential-sum proof.
      </p>
    </div>
  );
}
