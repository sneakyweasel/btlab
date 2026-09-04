import type { ReactNode } from "react";
import { Metric } from "../../components/Metric";
import { NecklaceExplorer } from "../../components/NecklaceExplorer";
import { Tex } from "../../components/Tex";
import { usePlayState } from "../../context/PlayState";
import { LIVE_FINANCE_L_MAX, PAPER_FLOOR, PAPER_L_CAP, PAPER_PERIOD, RECORD_LENGTHS } from "../../juggler/constants";
import { financeSnapshot, financeView, survivorOf } from "../../juggler/finance";
import { formatGrouped } from "../../juggler/format";
import { FinanceBalance, FinanceHierarchy } from "../../visuals/FinanceBalance";
import { NmaxStaircase } from "../../visuals/NmaxStaircase";

function Movement({
  number,
  title,
  question,
  children,
}: {
  number: number;
  title: string;
  question: string;
  children: ReactNode;
}) {
  return (
    <section className="space-y-4 rounded-2xl border border-line bg-card p-4 sm:p-5">
      <header className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
        <span className="font-mono text-xs uppercase tracking-[0.18em] text-muted">Movement {number}</span>
        <h2 className="font-serif text-2xl">{title}</h2>
        <span className="text-sm text-muted">{question}</span>
      </header>
      {children}
    </section>
  );
}

export function FinanceTab() {
  const { financeL, setFinanceL } = usePlayState();
  const view = financeView(financeL);
  const survivor = survivorOf(financeL);
  return (
    <div className="space-y-6">
      <p className="prose-measure text-sm text-muted">
        Section 4 of the paper in three pictures. Necklace presets are shipped
        walks; a custom start walks only under the live bit cap. Type any L through {formatGrouped(LIVE_FINANCE_L_MAX)}
        and θ and the crossing are exact in the browser. From the first survivor{" "}
        {formatGrouped(PAPER_PERIOD)} on, those values and every n_max come from the
        shipped Theorem 4.6 table at N₀ = {formatGrouped(PAPER_FLOOR)}.
      </p>

      <Movement number={1} title="The necklace" question="a realized walk read as excursions">
        <NecklaceExplorer />
        <p className="text-sm text-muted">
          Cycle entry is a choice of cut (the minimum first). Dynamical entry is the last
          even step into n — a genuine boundary condition: the last peak must be an even
          integer in [n²+1, (n+1)²). The first peak, by Lemma 3.4(i), sits at or above
          (n+1)². Those are different even states.
        </p>
      </Movement>

      <Movement number={2} title="The ledger" question="Theorem 4.4 as a balance">
        <Tex display>{String.raw`n\log n\cdot(3^o-2^L)\le L\cdot 3^o`}</Tex>
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            Period L
            <input
              className="ml-2 w-32 rounded border border-line bg-card px-2 py-1 font-mono"
              type="number"
              min={1}
              max={PAPER_L_CAP}
              value={financeL}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (Number.isInteger(value) && value >= 1 && value <= PAPER_L_CAP) setFinanceL(value);
              }}
            />
          </label>
          <select
            className="rounded border border-line bg-card px-2 py-1 text-sm"
            value=""
            onChange={(event) => {
              if (event.target.value) setFinanceL(Number(event.target.value));
            }}
          >
            <option value="">Record lengths</option>
            {RECORD_LENGTHS.map((length) => (
              <option key={length} value={length}>
                {formatGrouped(length)}
              </option>
            ))}
          </select>
          <select
            className="rounded border border-line bg-card px-2 py-1 text-sm"
            value=""
            onChange={(event) => {
              if (event.target.value) setFinanceL(Number(event.target.value));
            }}
          >
            <option value="">Survivors</option>
            {financeSnapshot.previewLengths.map((length) => (
              <option key={length} value={length}>
                {formatGrouped(length)}
              </option>
            ))}
          </select>
        </div>
        <FinanceBalance length={financeL} />
        <div className="grid gap-3 sm:grid-cols-3">
          <Metric
            label="at the floor 10⁶"
            value={view.status}
            hint={
              view.status === "excluded"
                ? "n_max(L) ≤ N₀: no cycle of this length"
                : view.status === "admissible"
                  ? "finance survivor — not evidence for a cycle"
                  : "outside the shipped table"
            }
          />
          <Metric label="in ℰ(10⁶)?" value={view.inExceptionSet ? "yes" : "no"} hint="the 141 survivors of Theorem 4.6(B)" />
          <Metric
            label="lattice coordinates"
            value={survivor ? `(a, b) = (${survivor.a}, ${survivor.b})` : "—"}
            hint={
              survivor
                ? survivor.packingDeath
                  ? "run-type packing kills this one (Theorem 4.8)"
                  : "Proposition 4.9: a·v* + b·v₁₀₅₄"
                : "only survivors sit on the lattice"
            }
          />
        </div>
        <FinanceHierarchy />
        <p className="text-sm text-muted">
          The constant-1 crossing and the shipped parity n_max differ on purpose: rung 1
          charges every defect at the cycle minimum, rung 4 charges valleys at n, deeper
          odds at ⌊n√n⌋ and evens at n², with the 6/5 majorant. The headline
          cutoff 25,781 is not an artifact of that majorant.
        </p>
      </Movement>

      <Movement number={3} title="The staircase" question="where the floor cuts the lengths">
        <NmaxStaircase selected={financeL} onSelect={setFinanceL} />
        <details>
          <summary className="cursor-pointer text-sm text-muted">All lengths in ℰ(10⁶)</summary>
          <p className="mt-2 font-mono text-xs leading-relaxed">
            {financeSnapshot.exceptionLengths.map((length) => formatGrouped(length)).join(", ")}
          </p>
          <p className="mt-2 text-sm text-muted">
            {financeSnapshot.exceptionCount} lengths through {formatGrouped(PAPER_L_CAP)}. Membership is
            not a candidate-cycle list.
          </p>
        </details>
      </Movement>
    </div>
  );
}
