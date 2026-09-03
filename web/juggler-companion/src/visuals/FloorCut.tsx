import type { ReactNode } from "react";
import { formatInt } from "../juggler/format";
import { bitLength, floorPower, letterOf } from "../juggler/map";

type FloorCutProps = {
  n: bigint;
  result?: bigint | null;
};

function threeDecimals(raw: number, integer: number): string {
  const frac = raw - integer;
  if (frac < 1e-12) return "000";
  return Math.floor(frac * 1000 + 1e-9)
    .toString()
    .padStart(3, "0");
}

function Card({ children }: { children: ReactNode }) {
  return (
    <div className="flex h-full flex-col rounded-2xl border border-line bg-paper/70 px-4 py-3">
      <p className="text-xs uppercase tracking-wide text-muted">
        Step computation
      </p>
      {children}
    </div>
  );
}

export function FloorCut({ n, result }: FloorCutProps) {
  if (n < 1n) {
    return (
      <Card>
        <p className="mt-2 text-sm text-muted">
          Floor still means: throw away the decimals and keep the integer part.
        </p>
      </Card>
    );
  }

  const letter = n % 2n === 1n ? "O" : "E";
  const odd = letter === "O";

  if (bitLength(n) > 50) {
    return (
      <Card>
        <p className="mt-2 font-mono text-sm" style={{ color: odd ? "#c45c26" : "#1f6f6a" }}>
          {odd ? "Odd branch O" : "Even branch E"}
        </p>
        <p className="mt-3 font-mono text-lg leading-snug break-all">
          {odd ? (
            <>
              ⌊{formatInt(n)}
              <sup>3/2</sup>⌋
            </>
          ) : (
            <>⌊√{formatInt(n)}⌋</>
          )}
          {result != null ? (
            <>
              <span className="mx-2 text-muted">→</span>
              {formatInt(result)}
            </>
          ) : null}
        </p>
        <p className="mt-auto pt-3 text-sm text-muted">
          This value is too large to print the decimals here. Floor still
          means: throw away the decimals and keep the integer part.
        </p>
      </Card>
    );
  }

  const x = Number(n);
  const raw = odd ? x * Math.sqrt(x) : Math.sqrt(x);
  const next = result ?? floorPower(n);
  const integer = Number(next);
  const decimals = threeDecimals(raw, integer);
  const exact = raw - integer < 1e-12;
  const formula = odd ? `${n}√${n}` : `√${n}`;
  return (
    <Card>
      <p className="mt-1 font-mono text-sm" style={{ color: odd ? "#c45c26" : "#1f6f6a" }}>
        {odd ? "n odd → ⌊n√n⌋" : "n even → ⌊√n⌋"}
        <span className="ml-2">{letterOf(n)}</span>
      </p>
      <p className="mt-2 font-mono text-sm text-muted">
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
      <p className="mt-auto pt-3 text-sm text-muted">
        {exact
          ? `${formula} is already an integer, so floor leaves it unchanged.`
          : `Cross out .${decimals} and keep ${integer}. That is ⌊${formula}⌋.`}
      </p>
    </Card>
  );
}
