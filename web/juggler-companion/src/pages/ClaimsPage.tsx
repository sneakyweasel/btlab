import { CLAIM_ROWS, DEFINITIONS, NOT_CLAIMED } from "../content/claims";
import { financeSnapshot } from "../juggler/finance";

export function ClaimsPage() {
  return (
    <div className="space-y-8">
      <header>
        <h1 className="text-4xl">What the paper claims</h1>
        <p className="prose-measure mt-3 text-muted">
          A scoreboard for a reviewer, in plain English. Lean names live in
          the manuscript. Arrival at 1 is not claimed.
        </p>
      </header>
      <section>
        <h2 className="text-2xl">Definitions</h2>
        <p className="prose-measure mt-2 text-sm text-muted">
          The same sentences as Paper A §1. These are not theorems.
        </p>
        <div className="mt-3 overflow-x-auto rounded-xl border border-line bg-card">
          <table className="w-full min-w-[28rem] text-left text-sm">
            <thead className="border-b border-line text-muted">
              <tr>
                <th className="px-3 py-2 font-medium">Term</th>
                <th className="px-3 py-2 font-medium">Meaning</th>
              </tr>
            </thead>
            <tbody>
              {DEFINITIONS.map((row) => (
                <tr key={row.term} className="border-b border-line/70">
                  <td className="px-3 py-2 font-medium">{row.term}</td>
                  <td className="px-3 py-2 text-muted">{row.meaning}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </section>
      <section className="grid gap-3 sm:grid-cols-2">
        <Score
          label="Even letters on a real loop"
          value="≥ 4"
          hint="Theorem 3.22, no descent floor"
        />
        <Score label="Arrival at 1" value="not claimed" hint="one orbit is not a theorem" />
        {financeSnapshot.instances.map((row) => (
          <Score
            key={row.theorem}
            label={row.theorem}
            value={`L ≥ ${row.period.toLocaleString("en-US")}`}
            hint={`N₀ = ${row.floor.toLocaleString("en-US")} · ${row.mechanism}`}
          />
        ))}
      </section>
      <section className="overflow-x-auto rounded-xl border border-line bg-card">
        <table className="w-full min-w-[36rem] text-left text-sm">
          <thead className="border-b border-line text-muted">
            <tr>
              <th className="px-3 py-2 font-medium">In plain English</th>
              <th className="px-3 py-2 font-medium">In the paper</th>
              <th className="px-3 py-2 font-medium">Tag</th>
            </tr>
          </thead>
          <tbody>
            {CLAIM_ROWS.map((row) => (
              <tr key={row.theorem} className="border-b border-line/70">
                <td className="px-3 py-2">{row.plain}</td>
                <td className="px-3 py-2">{row.theorem}</td>
                <td className="px-3 py-2 font-mono text-xs">{row.tag}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </section>
      <section className="rounded-xl border border-warn/30 bg-card p-5">
        <h2 className="text-2xl">What this does not claim</h2>
        <ul className="prose-measure mt-3 list-disc space-y-2 pl-5 text-muted">
          {NOT_CLAIMED.map((item) => (
            <li key={item}>{item}</li>
          ))}
        </ul>
      </section>
    </div>
  );
}

function Score({
  label,
  value,
  hint,
}: {
  label: string;
  value: string;
  hint: string;
}) {
  return (
    <div className="rounded-xl border border-line bg-card p-4">
      <div className="text-xs uppercase tracking-wide text-muted">{label}</div>
      <div className="mt-2 font-serif text-3xl">{value}</div>
      <div className="mt-1 text-sm text-muted">{hint}</div>
    </div>
  );
}
