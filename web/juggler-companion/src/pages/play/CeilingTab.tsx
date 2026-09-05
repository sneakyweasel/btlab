import { Metric } from "../../components/Metric";

type Row = {
  candidate: string;
  where: string;
  verdict: string;
  detail: string;
  status: "eliminated" | "remains";
};

/**
 * Section 5.6 and Section 6. The walk charge buys a factor ~0.44 ln n' over the
 * length-only parity charge, and no more. Five distinct explanations for that ceiling
 * were proposed and measured; all five are gone. What is left is not a slack.
 */
const ROWS: Row[] = [
  {
    candidate: "The envelope is lossy",
    where: "Thm 5.8 vs the lattice program",
    verdict: "eliminated",
    detail:
      "Substituting the census-free envelope for the exact program moves the margin at L = 50508 from 1.1204 to 1.1196 — a difference of 0.07%.",
    status: "eliminated",
  },
  {
    candidate: "The certification is too shallow",
    where: "Thm 5.8's window",
    verdict: "eliminated",
    detail:
      "The window ran to q₁₃ = 301994 only because the printed quotient list did. The sandwich already reaches q₁₄, and the digit criterion gets easier further out, so the window extends 55× to cover the whole fan.",
    status: "eliminated",
  },
  {
    candidate: "The exponent-walk relaxation",
    where: "Prop 5.8b, 5.8c",
    verdict: "eliminated",
    detail:
      "The program maximises over words that need not be realizable. But the charge ordering is flat at the top — the deficit 1 − r₁₆/r₁ is 5.4·10⁻⁸ at L = 50508 — and realizability is spread uniformly through that ordering, so the realizable optimum tracks the relaxed one to a part in 10⁸.",
    status: "eliminated",
  },
  {
    candidate: "The odd-run count",
    where: "Section 6's nominated direction",
    verdict: "eliminated",
    detail:
      "The extremal walk already sits at the ceiling p = min(e, o−1), with longest odd run 2. A lower bound on p cannot bite, and neither can a peak-height tradeoff: the adversary is the flattest word available, in both senses at once.",
    status: "eliminated",
  },
  {
    candidate: "The adversary cannot occur",
    where: "Section 6, realizability of the hug word",
    verdict: "eliminated",
    detail:
      "Hug prefixes are realized at 1.00–1.38 times the generic rate, against a control band over all depth-18 itineraries with median 1.05 and range 0.066–4.4·10³. The hug word is ordinary.",
    status: "eliminated",
  },
  {
    candidate: "The shape of the charge",
    where: "Remark 5.8a",
    verdict: "remains",
    detail:
      "f(u) = 1/(x ln x) at x = n′^(2^u) decays doubly exponentially in u, so the charge lives in a boundary layer of scale 1/(ln3 · ln n′). That is not a slack to recover — it is what the method is worth.",
    status: "remains",
  },
];

export function CeilingTab() {
  return (
    <div className="space-y-6">
      <p className="prose-measure text-sm text-muted">
        The walk charge of Section 5 is worth about{" "}
        <code className="font-mono">0.44 ln n′</code> over the length-only parity charge —
        measured across ten orders of magnitude in the floor, constant to 8%. Doubling it
        would require squaring the descent floor. Five explanations for that ceiling were
        proposed and tested; this tab is the scoreboard.
      </p>

      <section className="grid gap-3 sm:grid-cols-3">
        <Metric label="advantage over parity" value="0.44 ln n′" hint="constant to 8% over 10 orders" />
        <Metric label="candidates eliminated" value="5" hint="envelope, depth, relaxation, runs, realizability" />
        <Metric label="what remains" value="the charge" hint="a boundary layer, not a slack" />
      </section>

      <div className="space-y-3">
        {ROWS.map((r) => (
          <article
            key={r.candidate}
            className={`rounded-2xl border p-4 sm:p-5 ${
              r.status === "eliminated"
                ? "border-line bg-card"
                : "border-amber-500/40 bg-amber-500/5"
            }`}
          >
            <header className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
              <h3 className="font-serif text-lg">{r.candidate}</h3>
              <span className="font-mono text-xs uppercase tracking-[0.18em] text-muted">
                {r.where}
              </span>
              <span
                className={`ml-auto font-mono text-xs uppercase tracking-[0.18em] ${
                  r.status === "eliminated" ? "text-emerald-600" : "text-amber-600"
                }`}
              >
                {r.verdict}
              </span>
            </header>
            <p className="prose-measure mt-2 text-sm text-muted">{r.detail}</p>
          </article>
        ))}
      </div>

      <section className="space-y-3 rounded-2xl border border-line bg-card p-4 sm:p-5">
        <h2 className="font-serif text-2xl">What this does and does not say</h2>
        <p className="prose-measure text-sm text-muted">
          It says the walk charge is finished as a lever: no refinement of the envelope,
          the certification, the admissible class, or the run structure will improve it,
          because none of those is where the factor lives. It does not say the period bound
          cannot rise — a larger certified floor still moves it up the fan, at{" "}
          <code className="font-mono">0.44 ln n′</code> per step. And it says nothing about
          the long regime, where the problem actually lives: excluding a cycle of length{" "}
          <code className="font-mono">L</code> is a statement about one orbit&rsquo;s parity
          word at depth <code className="font-mono">L</code>, and no estimate here reaches it.
        </p>
      </section>
    </div>
  );
}
