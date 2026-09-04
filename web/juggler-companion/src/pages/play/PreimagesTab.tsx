import { useMemo, useState } from "react";
import { Disclaimer } from "../../components/Disclaimer";
import { Metric } from "../../components/Metric";
import { Tex } from "../../components/Tex";
import {
  PRODUCTION_M_MAX,
  PRODUCTION_SEEDS,
} from "../../juggler/constants";
import { formatInt } from "../../juggler/format";
import { oddPreimageIntegers } from "../../juggler/preimages";
import { evenBlockView, randomEvenInBlock } from "../../juggler/productions";
import { EvenBlockStrip } from "../../visuals/EvenBlockStrip";
import { PreimageNumberLine } from "../../visuals/PreimageNumberLine";

export function PreimagesTab() {
  const [m, setM] = useState(11);
  const [selected, setSelected] = useState<number | null>(() =>
    randomEvenInBlock(evenBlockView(11)),
  );
  const block = useMemo(() => evenBlockView(m), [m]);
  const odds = useMemo(() => oddPreimageIntegers(m), [m]);

  return (
    <div className="space-y-6">
      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">Seed m</h2>
        <p className="text-sm text-muted">
          Pick a member of a backward-closed set A. The even block is the
          one-step even production. The OE fiber of 100,000 is a separate tab.
        </p>
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            m
            <input
              className="ml-2 w-28 rounded border border-line bg-paper px-2 py-1 font-mono"
              type="number"
              min={1}
              max={PRODUCTION_M_MAX}
              value={m}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (
                  Number.isInteger(value) &&
                  value >= 1 &&
                  value <= PRODUCTION_M_MAX
                ) {
                  setM(value);
                  setSelected(randomEvenInBlock(evenBlockView(value)));
                }
              }}
            />
          </label>
          <div className="flex flex-wrap gap-2">
            {PRODUCTION_SEEDS.map((preset) => (
              <button
                key={preset.value}
                type="button"
                title={preset.note}
                className={`rounded-full px-3 py-1 text-sm ${
                  m === preset.value
                    ? "bg-deep text-card"
                    : "border border-line text-muted"
                }`}
                onClick={() => {
                  setM(preset.value);
                  setSelected(randomEvenInBlock(evenBlockView(preset.value)));
                }}
              >
                {preset.value.toLocaleString("en-US")}
              </button>
            ))}
          </div>
        </div>
      </section>

      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">One-step parents of m</h2>
        <p className="text-sm text-muted">
          Same floor cut on both lines. Above, n in [{formatInt(m)}²,{" "}
          {formatInt(m + 1)}²) = [{formatInt(block.lo)}, {formatInt(block.hi)})
          has <Tex>{String.raw`\lfloor\sqrt{n}\rfloor=m`}</Tex>. Below, n in [∛(
          {formatInt(m)}²), ∛({formatInt(m + 1)}²)) has{" "}
          <Tex>{String.raw`\lfloor n\sqrt{n}\rfloor=m`}</Tex>. The odd slot is
          shorter than 1, so it holds at most one integer. If m is in A, every
          bead with an arrow joins A.
        </p>
        <div className="grid gap-3 sm:grid-cols-3">
          <Metric
            label="Interval"
            value={`[${formatInt(block.lo)}, ${formatInt(block.hi)})`}
          />
          <Metric label="|E(m)|" value={block.count.toLocaleString("en-US")} />
          <Metric
            label="Harmonic range"
            value={`${block.harmonicLo.toExponential(2)} … ${block.harmonicHi.toExponential(2)}`}
            hint="Lemma 3.1 bounds on the sum of 1/n"
          />
        </div>
        <EvenBlockStrip
          view={block}
          selected={selected}
          onSelect={setSelected}
        />
        {block.listed && block.evens.length <= 16 ? (
          <p className="font-mono text-sm">{block.evens.join(", ")}</p>
        ) : null}
      </section>

      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">Odd one-step parent</h2>
        <p className="text-sm text-muted">
          An odd image still has at most one odd parent. That uniqueness is
          Paper A; it is also the seed geometry of odd generation.
        </p>
        <Metric label="Odd parents of m" value={String(odds.length)} />
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

      <Disclaimer>
        If m lies in a backward-closed set A, every even parent joins A. That is
        one contagion production. It excludes no fate and is not a halt theorem.
      </Disclaimer>
    </div>
  );
}
