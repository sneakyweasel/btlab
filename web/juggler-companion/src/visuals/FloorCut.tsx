import { bitLength, floorPower, letterOf } from "../juggler/map";

type FloorCutProps = {
  n: bigint;
};

function threeDecimals(raw: number, integer: number): string {
  const frac = raw - integer;
  if (frac < 1e-12) return "000";
  return Math.floor(frac * 1000 + 1e-9)
    .toString()
    .padStart(3, "0");
}

export function FloorCut({ n }: FloorCutProps) {
  if (n < 1n || bitLength(n) > 50) {
    return (
      <p className="text-sm text-muted">
        Floor still means: throw away the decimals and keep the integer part.
      </p>
    );
  }
  const x = Number(n);
  const raw = n % 2n === 1n ? x * Math.sqrt(x) : Math.sqrt(x);
  const next = floorPower(n);
  const integer = Number(next);
  const decimals = threeDecimals(raw, integer);
  const exact = raw - integer < 1e-12;
  const letter = letterOf(n);
  const formula = letter === "O" ? `${n}√${n}` : `√${n}`;
  return (
    <div className="rounded-xl border border-line bg-paper/70 px-4 py-3">
      <p className="text-xs uppercase tracking-wide text-muted">
        Floor this step — throw away the decimals
      </p>
      <p className="mt-1 font-mono text-sm text-muted">
        {formula} = {integer}.{decimals}…
      </p>
      <div className="mt-3 flex flex-wrap items-center gap-3 font-mono text-4xl leading-none">
        <span>{integer}</span>
        <span className="relative text-odd">
          .{decimals}
          <span
            aria-hidden="true"
            className="absolute inset-x-0 top-1/2 h-[3px] -translate-y-1/2 rotate-[-8deg] bg-warn"
          />
        </span>
        <span className="text-2xl text-muted">→</span>
        <span className="text-ink">{next.toString()}</span>
      </div>
      <p className="mt-3 text-sm text-muted">
        {exact
          ? `${formula} is already an integer, so floor leaves it unchanged.`
          : `Cross out .${decimals} and keep ${integer}. That is ⌊${formula}⌋.`}
      </p>
    </div>
  );
}
