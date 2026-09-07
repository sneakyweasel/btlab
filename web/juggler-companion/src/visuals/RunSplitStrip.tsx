const ODD = "#c45c26";
const EVEN = "#1f6f6a";

function Tile({ letter, dim }: { letter: "O" | "E"; dim?: boolean }) {
  return (
    <span
      className="inline-flex h-8 min-w-8 items-center justify-center rounded-md font-mono text-sm text-card"
      style={{
        background: letter === "O" ? ODD : EVEN,
        opacity: dim ? 0.35 : 1,
      }}
    >
      {letter}
    </span>
  );
}

type RunSplitStripProps = {
  a: number;
  suffix: string;
};

/** Canonical split w = v O^a u. The prefix v is a shadow; the cut is the law. */
export function RunSplitStrip({ a, suffix }: RunSplitStripProps) {
  const odds = Math.max(0, Math.min(a, 16));
  return (
    <div className="space-y-2">
      <p className="text-xs uppercase tracking-wide text-muted">
        w = v O<sup>a</sup> u — the cut the law reads
      </p>
      <div className="flex flex-wrap items-center gap-2">
        <span className="text-xs uppercase tracking-wide text-muted">v</span>
        <Tile letter="O" dim />
        <Tile letter="E" dim />
        <span className="font-mono text-muted">…</span>
        <div className="flex flex-wrap items-center gap-1 rounded-xl border border-line bg-paper/70 px-2 py-1.5">
          {Array.from({ length: odds }, (_, index) => (
            <Tile key={`o-${index}`} letter="O" />
          ))}
          <span className="px-1 font-mono text-[10px] uppercase tracking-wide text-muted">
            a = {odds}
          </span>
        </div>
        <span className="h-10 w-px bg-ink" aria-hidden />
        <div className="flex flex-wrap items-center gap-1 rounded-xl border border-line bg-paper/70 px-2 py-1.5">
          {suffix ? (
            [...suffix].map((letter, index) => (
              <Tile key={`u-${index}`} letter={letter === "O" ? "O" : "E"} />
            ))
          ) : (
            <span className="px-1 font-mono text-xs text-muted">ε</span>
          )}
          <span className="px-1 font-mono text-[10px] uppercase tracking-wide text-muted">
            u{suffix ? ` = ${suffix}` : " empty"}
          </span>
        </div>
      </div>
    </div>
  );
}
