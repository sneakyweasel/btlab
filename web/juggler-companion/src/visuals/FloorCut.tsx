import type { ReactNode } from "react";
import { Tex } from "../components/Tex";
import { bitLength, floorPower, letterOf } from "../juggler/map";

type FloorCutProps = {
  n: bigint;
  result?: bigint | null;
  compact?: boolean;
};

function shortDigits(
  value: bigint | number | string,
  head = 3,
  tail = 3,
  maxFull = head + tail + 1,
): string {
  const text = value.toString();
  if (text.length <= maxFull) return text;
  return `${text.slice(0, head)}…${text.slice(-tail)}`;
}

function threeDecimals(raw: number, integer: number): string {
  const frac = raw - integer;
  if (frac < 1e-12) return "000";
  return Math.floor(frac * 1000 + 1e-9)
    .toString()
    .padStart(3, "0");
}

function Card({
  children,
  compact,
}: {
  children: ReactNode;
  compact?: boolean;
}) {
  if (compact) return <div className="grid gap-1 text-center">{children}</div>;
  return (
    <div className="flex h-full flex-col rounded-2xl border border-line bg-paper/70 px-4 py-3">
      <p className="text-xs uppercase tracking-wide text-muted">
        Step computation
      </p>
      {children}
    </div>
  );
}

export function FloorCut({ n, result, compact = false }: FloorCutProps) {
  if (n < 1n) {
    return (
      <Card compact={compact}>
        <p className="text-sm text-muted">
          Floor still means: throw away the decimals and keep the integer part.
        </p>
      </Card>
    );
  }

  const letter = n % 2n === 1n ? "O" : "E";
  const odd = letter === "O";

  if (bitLength(n) > 50) {
    return (
      <Card compact={compact}>
        {compact ? null : (
          <p className="mt-2 font-mono text-sm" style={{ color: odd ? "#c45c26" : "#1f6f6a" }}>
            {odd ? "Odd branch O" : "Even branch E"}
          </p>
        )}
        <p className={compact ? "text-xs" : "mt-3 text-lg"}>
          <Tex>
            {odd
              ? String.raw`\lfloor\sqrt{${shortDigits(n, compact ? 2 : 3, compact ? 2 : 3, compact ? 6 : 9)}^{3}}\rfloor`
              : String.raw`\lfloor\sqrt{${shortDigits(n, compact ? 2 : 3, compact ? 2 : 3, compact ? 6 : 9)}}\rfloor`}
          </Tex>
        </p>
      </Card>
    );
  }

  const x = Number(n);
  const raw = odd ? x * Math.sqrt(x) : Math.sqrt(x);
  const next = result ?? floorPower(n);
  const integer = Number(next);
  const decimals = threeDecimals(raw, integer);
  const head = compact ? 2 : 3;
  const tail = compact ? 2 : 3;
  const maxFull = compact ? 6 : 9;
  const shownN = shortDigits(n, head, tail, maxFull);
  const shownInt = shortDigits(next, head, tail, maxFull);
  const work = odd ? String.raw`\sqrt{${shownN}^{3}}` : String.raw`\sqrt{${shownN}}`;
  return (
    <Card compact={compact}>
      {compact ? null : (
        <p className="mt-1 font-mono text-sm" style={{ color: odd ? "#c45c26" : "#1f6f6a" }}>
          {odd ? "n odd → ⌊n√n⌋" : "n even → ⌊√n⌋"}
          <span className="ml-2">{letterOf(n)}</span>
        </p>
      )}
      <p className={compact ? "text-xs" : "text-sm"}>
        <Tex>{work}</Tex>
      </p>
      <div
        title={`${next.toString()}.${decimals}…`}
        className={`flex max-w-full items-center justify-center overflow-hidden font-mono leading-none ${
          compact ? "gap-0.5 text-lg" : "mt-3 gap-1 text-4xl"
        }`}
      >
        <span className="min-w-0 truncate">{shownInt}</span>
        <span className="relative shrink-0 text-odd">
          .{decimals}
          <span
            aria-hidden="true"
            className="absolute inset-x-0 top-1/2 h-[3px] -translate-y-1/2 rotate-[-8deg] bg-warn"
          />
        </span>
      </div>
    </Card>
  );
}
