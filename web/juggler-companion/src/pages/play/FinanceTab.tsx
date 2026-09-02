import { Metric } from "../../components/Metric";
import { Tex } from "../../components/Tex";
import { usePlayState } from "../../context/PlayState";
import { RECORD_LENGTHS } from "../../juggler/constants";
import { financeSnapshot, financeView } from "../../juggler/finance";

export function FinanceTab() {
  const { financeL, setFinanceL } = usePlayState();
  const view = financeView(financeL);
  return (
    <div className="space-y-5">
      <Tex display>{String.raw`n\log n\cdot(3^o-2^L)\le L\cdot 3^o`}</Tex>
      <p className="prose-measure text-sm text-muted">
        Theorem 4.4 in the paper. This tab looks up the conservative 6/5 table
        of Theorem 4.6 at N₀ = 1,000,000. n_max is never recomputed here.
      </p>
      <div className="flex flex-wrap items-end gap-3">
        <label className="text-sm text-muted">
          Period L
          <input
            className="ml-2 w-32 rounded border border-line bg-card px-2 py-1 font-mono"
            type="number"
            min={1}
            max={200000}
            value={financeL}
            onChange={(event) => {
              const value = Number(event.target.value);
              if (Number.isInteger(value) && value >= 1) setFinanceL(value);
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
              {length}
            </option>
          ))}
        </select>
      </div>
      <div className="grid gap-3 sm:grid-cols-4">
        <Metric label="This L" value={view.status} />
        <Metric label="o_min" value={view.oMin === null ? "—" : String(view.oMin)} />
        <Metric
          label="n_max"
          value={view.nMax === null ? "—" : view.nMax.toLocaleString("en-US")}
          hint={view.nMax === null ? "not in the shipped record table" : "shipped 6/5 value"}
        />
        <Metric label="In ℰ?" value={view.inExceptionSet ? "yes" : "no"} />
      </div>
      {view.status === "admissible" ? (
        <p className="text-sm text-muted">
          L = {financeL.toLocaleString("en-US")} is admissible to the Theorem
          4.6 table at the descent floor 1,000,000. That is not evidence for a
          cycle.
        </p>
      ) : null}
      {view.status === "excluded" ? (
        <p className="text-sm text-ok">
          L = {financeL.toLocaleString("en-US")} is excluded at the verified
          descent floor 1,000,000.
        </p>
      ) : null}
      {view.status === "beyond table" ? (
        <p className="text-sm text-muted">
          The shipped exception list stops at 100,000. This is not a later-floor
          lookup.
        </p>
      ) : null}
      <details>
        <summary className="cursor-pointer text-sm text-muted">
          First lengths in ℰ
        </summary>
        <p className="mt-2 font-mono text-sm">
          {financeSnapshot.previewLengths.join(", ")}
        </p>
        <p className="mt-2 text-sm text-muted">
          {financeSnapshot.exceptionCount} lengths through 100,000. Membership
          is not a candidate-cycle list.
        </p>
      </details>
    </div>
  );
}
