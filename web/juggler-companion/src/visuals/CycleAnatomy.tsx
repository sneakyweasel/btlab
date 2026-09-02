import type { CycleSeamKind } from "../juggler/itinerary";

type CycleAnatomyProps = {
  word: string;
  aligned: boolean;
  shaped: boolean;
  seam: CycleSeamKind;
};

function Tile({ letter, dim }: { letter?: string; dim?: boolean }) {
  if (!letter || letter === "?") {
    return (
      <span className="inline-flex h-9 w-9 items-center justify-center rounded-lg border border-dashed border-line font-mono text-muted">
        {letter === "?" ? "?" : "·"}
      </span>
    );
  }
  const odd = letter === "O";
  return (
    <span
      className={`inline-flex h-9 w-9 items-center justify-center rounded-lg font-mono text-card ${
        dim ? "opacity-45" : ""
      }`}
      style={{ background: odd ? "#c45c26" : "#1f6f6a" }}
    >
      {letter}
    </span>
  );
}

function Arrow({ letter, dim }: { letter?: string; dim?: boolean }) {
  return (
    <span className={`grid justify-items-center text-xs text-muted ${dim ? "opacity-45" : ""}`}>
      <span className="font-mono">{letter ?? "·"}</span>
      <span>→</span>
    </span>
  );
}

export function CycleSeamStrip({
  word,
  seam,
  shaped,
}: {
  word: string;
  seam: CycleSeamKind;
  shaped: boolean;
}) {
  const lastPeak = word.at(-1);
  const atN = word[0];
  const firstOdd = word[1];
  const firstHigh = word[2];
  const dim = !shaped;
  return (
    <div className={`rounded-xl border border-line bg-paper/70 px-3 py-3 ${dim ? "opacity-70" : ""}`}>
      <p className="text-xs uppercase tracking-wide text-muted">
        Seam at CycleMin — join is drawn here
      </p>
      <div className="mt-3 flex flex-wrap items-end justify-center gap-1.5">
        <Tile letter="O" />
        <Tile letter="O" />
        <Tile letter="?" />
        <Tile letter="?" />
        <Tile letter="?" />
        <div className="grid justify-items-center gap-1">
          <Tile letter="E" />
          <span className="text-xs text-muted">t</span>
        </div>
        <Arrow letter="E" />
        <div className="grid justify-items-center gap-1">
          <span className="inline-flex h-9 min-w-9 items-center justify-center rounded-lg border-2 border-ink bg-card px-2 font-serif text-sm">
            n
          </span>
          <span className="text-xs text-muted">join</span>
        </div>
        <span className="mb-3 text-muted">←</span>
        <div className="grid justify-items-center gap-1">
          <Tile letter={lastPeak} dim={dim} />
          <span className="text-xs text-muted">last peak</span>
        </div>
      </div>
      <div className="mt-3 flex flex-wrap items-end justify-center gap-2">
        <div className="grid justify-items-center gap-1">
          <span className="inline-flex h-9 min-w-9 items-center justify-center rounded-lg border-2 border-ink bg-card px-2 font-serif text-sm">
            n
          </span>
          <span className="text-xs text-muted">knot</span>
        </div>
        <Arrow letter={atN} dim={dim} />
        <div className="grid justify-items-center gap-1">
          <Tile letter={firstOdd} dim={dim || firstOdd !== "O"} />
          <span className="text-xs text-muted">first odd</span>
        </div>
        <Arrow letter={firstOdd} dim={dim} />
        <div className="grid justify-items-center gap-1">
          <Tile letter={firstHigh} dim={dim} />
          <span className="text-xs text-muted">first high</span>
        </div>
      </div>
      <p className="mt-3 text-center text-sm text-muted">
        {seam === "OE|OO"
          ? "Balloon: return cannot be O. Launch is OO. Incoming OE — isolated last E. The stem OO???E is a cartoon of one first visit."
          : seam === "EE|OO"
            ? "Balloon: return cannot be O. Launch is OO. Incoming EE — trailing even run. The stem OO???E is a cartoon of one first visit."
            : "Not a CycleMin seam. Legal cuts are last-peak E, then n, then OO. The stem is still a cartoon."}
      </p>
    </div>
  );
}

export function CycleExtremaSketch({
  aligned,
  shaped,
}: {
  aligned: boolean;
  shaped: boolean;
}) {
  return (
    <div className={`rounded-xl border border-line bg-paper/70 px-3 py-3 ${shaped ? "" : "opacity-70"}`}>
      <p className="text-xs uppercase tracking-wide text-muted">
        Extrema at the CycleMin cut
      </p>
      <svg viewBox="0 0 680 210" role="img" className="mt-1 h-auto w-full">
        <title>
          Launch OO climbs past (n+1)²; last peak lands in the last-even cell
        </title>
        <line
          x1="48"
          y1="40"
          x2="640"
          y2="40"
          stroke="#c45c26"
          strokeWidth="1.2"
          strokeDasharray="5 4"
        />
        <line
          x1="48"
          y1="118"
          x2="640"
          y2="118"
          stroke="#1f6f6a"
          strokeWidth="1.2"
          strokeDasharray="5 4"
        />
        <rect
          x="430"
          y="40"
          width="140"
          height="78"
          fill="#1f6f6a"
          opacity="0.08"
        />
        <path
          d="M70,168 L104,128 L138,78 C150,48 158,28 176,26 C214,22 236,108 270,124 C310,144 348,108 392,98 C430,90 458,72 500,76 C538,80 572,148 618,168"
          fill="none"
          stroke="#1d1914"
          strokeWidth="2.4"
        />
        <circle cx="70" cy="168" r="7" fill="#c45c26" stroke="#1d1914" strokeWidth="2" />
        <circle cx="104" cy="128" r="6" fill="#c45c26" />
        <circle cx="138" cy="78" r="6" fill="#c45c26" />
        <circle cx="176" cy="26" r="7" fill="#1f6f6a" />
        <circle cx="500" cy="76" r="7" fill="#1f6f6a" />
        <path
          d="M618 168 C640 176, 40 186, 70 168"
          fill="none"
          stroke="#5e574c"
          strokeWidth="1.4"
          strokeDasharray="4 3"
          markerEnd="url(#cycle-back)"
        />
        <text x="56" y="34" fontSize="11" fill="#c45c26" fontFamily="Source Sans 3, sans-serif">
          (n+1)²
        </text>
        <text x="56" y="112" fontSize="11" fill="#1f6f6a" fontFamily="Source Sans 3, sans-serif">
          n²
        </text>
        <text x="70" y="196" textAnchor="middle" fontSize="12" fill="#5e574c" fontFamily="Source Sans 3, sans-serif">
          min n
        </text>
        <text x="118" y="158" textAnchor="middle" fontSize="11" fill="#c45c26" fontFamily="Source Sans 3, sans-serif">
          launch OO
        </text>
        <text x="176" y="16" textAnchor="middle" fontSize="12" fill="#5e574c" fontFamily="Source Sans 3, sans-serif">
          first peak overshoots
        </text>
        <text x="500" y="64" textAnchor="middle" fontSize="12" fill="#5e574c" fontFamily="Source Sans 3, sans-serif">
          last peak lands
        </text>
        <text x="500" y="148" textAnchor="middle" fontSize="11" fill="#1f6f6a" fontFamily="Source Sans 3, sans-serif">
          last-even cell
        </text>
        <defs>
          <marker id="cycle-back" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
            <path d="M0,0 L8,4 L0,8 Z" fill="#5e574c" />
          </marker>
        </defs>
      </svg>
      <p className="text-sm text-muted">
        {shaped
          ? "Launch OO: T(n) is odd and T²(n) sits at or above (n+1)². Last even lands in [n²+1, (n+1)²)."
          : aligned
            ? "The marked bead is at the knot, but this spelling is not CycleMin."
            : "A schematic of the CycleMin cut. Rotate until the min bead sits at the knot."}
      </p>
    </div>
  );
}

export function CycleAnatomy({ word, aligned, shaped, seam }: CycleAnatomyProps) {
  return (
    <div className="grid gap-3 lg:grid-cols-2">
      <CycleSeamStrip word={word} seam={seam} shaped={shaped} />
      <CycleExtremaSketch aligned={aligned} shaped={shaped} />
    </div>
  );
}
