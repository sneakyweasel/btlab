import { useState } from "react";
import { Metric } from "../../components/Metric";
import { PreimageNumberLine } from "../../visuals/PreimageNumberLine";
import { evenPredecessors, oddPreimageIntegers } from "../../juggler/preimages";

export function PreimagesTab() {
  const [q, setQ] = useState(6);
  const [m, setM] = useState(11);
  const even = evenPredecessors(q);
  const odds = oddPreimageIntegers(m);
  return (
    <div className="grid gap-6 md:grid-cols-2">
      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">Even one-step preimage</h2>
        <p className="text-sm text-muted">
          J is not invertible. The one-step preimage of q is a set: the even
          integers in one square interval that map to q.
        </p>
        <label className="text-sm text-muted">
          Image q
          <input
            className="ml-2 w-24 rounded border border-line bg-paper px-2 py-1 font-mono"
            type="number"
            min={0}
            value={q}
            onChange={(event) => {
              const value = Number(event.target.value);
              if (Number.isInteger(value) && value >= 0 && value <= 200) {
                setQ(value);
              }
            }}
          />
        </label>
        <Metric label="Interval" value={`[${even.lo}, ${even.hi})`} />
        <Metric label="Even predecessors" value={String(even.evenCount)} />
        <PreimageNumberLine
          lo={even.lo}
          hi={even.hi}
          marks={even.evens.slice(0, 8)}
          label={`Even one-step preimage of ${q}`}
        />
        <p className="font-mono text-sm">
          {even.evens.join(", ") || "—"}
          {even.truncated ? "…" : ""}
        </p>
      </section>
      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">Odd one-step preimage</h2>
        <p className="text-sm text-muted">
          The odd one-step preimage of m has at most one integer. That set may
          be empty.
        </p>
        <label className="text-sm text-muted">
          Image m
          <input
            className="ml-2 w-24 rounded border border-line bg-paper px-2 py-1 font-mono"
            type="number"
            min={0}
            value={m}
            onChange={(event) => {
              const value = Number(event.target.value);
              if (Number.isInteger(value) && value >= 0 && value <= 500) {
                setM(value);
              }
            }}
          />
        </label>
        <Metric label="Odd parents" value={String(odds.length)} />
        <PreimageNumberLine
          lo={Math.max(0, (odds[0] ?? m) - 2)}
          hi={(odds[0] ?? m) + 3}
          marks={odds}
          label={`Odd one-step preimage of ${m}`}
        />
        <p className="font-mono text-sm">
          {odds.length ? odds.join(", ") : "Empty odd one-step preimage."}
        </p>
      </section>
    </div>
  );
}
