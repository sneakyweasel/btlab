import { Tex } from "../components/Tex";
import { idealExponentApprox, regimeOf } from "../juggler/itinerary";
import { SurplusScale } from "./SurplusScale";

type IdealExponentProps = {
  odds: number;
  length: number;
  start?: bigint | null;
};

function formatApprox(value: number): string {
  if (!Number.isFinite(value)) return "\\infty";
  if (value !== 0 && (value < 0.001 || value >= 1000)) {
    const exp = Math.floor(Math.log10(Math.abs(value)));
    const mant = value / 10 ** exp;
    return `${mant.toFixed(2)}\\times 10^{${exp}}`;
  }
  return value.toFixed(3);
}

export function IdealExponent({ odds, length, start }: IdealExponentProps) {
  if (length <= 0) return null;

  const evens = length - odds;
  const regime = regimeOf(length, odds);
  const approx = idealExponentApprox(odds, length);
  const numer = 3n ** BigInt(odds);
  const denom = 2n ** BigInt(length);
  const showExact = numer.toString().length <= 12 && denom.toString().length <= 12;
  const startShown =
    start !== undefined && start !== null && start.toString().length <= 8
      ? start.toString()
      : null;
  const tex = showExact
    ? String.raw`\dfrac{3^{${odds}}}{2^{${length}}}=\dfrac{${numer}}{${denom}}\approx ${formatApprox(approx)}`
    : String.raw`\dfrac{3^{${odds}}}{2^{${length}}}\approx ${formatApprox(approx)}`;
  const startTex =
    startShown === null
      ? ""
      : showExact
        ? String.raw`${startShown}\cdot\dfrac{3^{${odds}}}{2^{${length}}}=${startShown}\cdot\dfrac{${numer}}{${denom}}`
        : String.raw`${startShown}\cdot\dfrac{3^{${odds}}}{2^{${length}}}`;

  return (
    <div className="grid gap-3 sm:grid-cols-[minmax(0,1fr)_14rem] sm:items-center">
      <div>
        <p className="text-xs uppercase tracking-wide text-muted">
          Ideal exponent of this prefix
        </p>
        <Tex display>{tex}</Tex>
        {startTex ? (
          <>
            <p className="text-sm text-muted">
              Ignoring floors, that would send the start to
            </p>
            <Tex display>{startTex}</Tex>
          </>
        ) : null}
        <p className="text-sm text-ink">
          <span
            className={
              regime === "expanding"
                ? "font-medium text-odd"
                : regime === "contracting"
                  ? "font-medium text-even"
                  : "font-medium text-muted"
            }
          >
            {regime}
          </span>
          {regime === "contracting"
            ? ": the ratio is less than 1, so even without floors this prefix shrinks."
            : regime === "expanding"
              ? ": the ratio is greater than 1, so without floors this prefix grows."
              : regime === "critical"
                ? ": the ratio is exactly 1."
                : ""}
        </p>
        <p className="mt-2 text-sm text-muted">
          {odds} O and {evens} E in {length} {length === 1 ? "step" : "steps"}.
          Floors are not in this ratio.
        </p>
      </div>
      <SurplusScale compact odds={odds} length={length} />
    </div>
  );
}
