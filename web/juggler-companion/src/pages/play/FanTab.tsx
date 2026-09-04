import fanData from "../../data/fan.json";
import { Metric } from "../../components/Metric";
import { formatGrouped } from "../../juggler/format";
import { FanLambda, FanStaircase, reachedAt } from "../../visuals/FanStaircase";

type FanRow = { k: number; L: number; o: number; lam: number; nmax: number };
const FAN = fanData as FanRow[];

function sci(x: number) {
  const e = Math.floor(Math.log10(x));
  return `${(x / 10 ** e).toFixed(2)}·10^${e}`;
}

/**
 * Section 5.8. The tab the reviewer needs between "finance" and "walk charge": what
 * actually survives, why it is one arithmetic progression, and what each further step
 * costs. Everything here is the same object the kill tables run on.
 */
export function FanTab() {
  const reached = reachedAt(350_000_000);
  const rows = FAN.filter((r) => [0, 1, 2, 3, 6, 31, 52, 54, 55].includes(r.k));

  return (
    <div className="space-y-6">
      <p className="prose-measure text-sm text-muted">
        Every length that survives the finance table at every certified floor lies in one
        arithmetic progression, <code className="font-mono">L_k = 176251 + 301994k</code> for{" "}
        <code className="font-mono">k = 0…55</code>. The period bound is not stuck against a
        wall; it is on a staircase whose steps are priced. This tab is that staircase.
      </p>

      <section className="grid gap-3 sm:grid-cols-3">
        <Metric label="fan members" value="56" hint="k = 0 … 55" />
        <Metric label="bound today" value={formatGrouped(780239)} hint="L₂, at floor 3.5·10⁸" />
        <Metric label="ends at" value={formatGrouped(16785921)} hint="L₅₅ = q₁₄, the next convergent" />
      </section>

      <section className="space-y-4 rounded-2xl border border-line bg-card p-4 sm:p-5">
        <header className="space-y-1">
          <h2 className="font-serif text-2xl">Why exactly 56</h2>
          <p className="text-sm text-muted">
            The linear form is affine in k, so the fan ends where it changes sign.
          </p>
        </header>
        <FanLambda />
      </section>

      <section className="space-y-4 rounded-2xl border border-line bg-card p-4 sm:p-5">
        <header className="space-y-1">
          <h2 className="font-serif text-2xl">The price of each step</h2>
          <p className="text-sm text-muted">
            The descent floor required to pass each member, and how far the certified floors reach.
          </p>
        </header>
        <FanStaircase />
        <div className="overflow-x-auto">
          <table className="w-full text-sm">
            <thead>
              <tr className="border-b border-line text-left font-mono text-xs uppercase tracking-wide text-muted">
                <th className="py-2 pr-3">k</th>
                <th className="py-2 pr-3">L_k</th>
                <th className="py-2 pr-3">Λ_k</th>
                <th className="py-2 pr-3">floor to pass</th>
                <th className="py-2">status</th>
              </tr>
            </thead>
            <tbody className="font-mono text-xs">
              {rows.map((r) => (
                <tr key={r.k} className="border-b border-line/50">
                  <td className="py-1.5 pr-3">{r.k}</td>
                  <td className="py-1.5 pr-3">{formatGrouped(r.L)}</td>
                  <td className="py-1.5 pr-3">{r.lam.toExponential(3)}</td>
                  <td className="py-1.5 pr-3">{sci(r.nmax)}</td>
                  <td className="py-1.5">
                    {r.k < reached ? (
                      <span className="text-emerald-600">excluded</span>
                    ) : r.k === reached ? (
                      <span className="text-amber-600">current frontier</span>
                    ) : (
                      <span className="text-muted">open</span>
                    )}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </section>

      <section className="space-y-3 rounded-2xl border border-line bg-card p-4 sm:p-5">
        <h2 className="font-serif text-2xl">What the staircase does not buy</h2>
        <p className="prose-measure text-sm text-muted">
          Exhausting the fan needs a floor of <code className="font-mono">2.2·10¹²</code>;
          passing <code className="font-mono">q₁₄</code> itself needs{" "}
          <code className="font-mono">4.9·10¹²</code>, after which the same structure repeats
          one scale up. The fans recur at every convergent and the required floor grows
          quadratically in the length, so a period bound obtained this way can never become a
          proof that no cycle exists. That gap is not computational.
        </p>
      </section>
    </div>
  );
}
