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
import { evenBlockView, fiberView, randomEvenInBlock } from "../../juggler/productions";
import { EvenBlockStrip } from "../../visuals/EvenBlockStrip";
import { OeFiberStrip } from "../../visuals/OeFiberStrip";
import { PreimageNumberLine } from "../../visuals/PreimageNumberLine";
import { ProductionWork } from "../../visuals/ProductionWork";
import { SweepLane } from "../../visuals/SweepLane";

function formatShare(value: number | null): string {
  if (value === null) return "—";
  return value.toFixed(3);
}

export function PreimagesTab() {
  const [m, setM] = useState(11);
  const [selected, setSelected] = useState<number | null>(() =>
    randomEvenInBlock(evenBlockView(11)),
  );
  const [hovered, setHovered] = useState<number | null>(null);
  const block = useMemo(() => evenBlockView(m), [m]);
  const fiber = useMemo(() => fiberView(m), [m]);
  const odds = useMemo(() => oddPreimageIntegers(m), [m]);
  const inspect =
    hovered ??
    selected ??
    (block.listed ? block.evens[0] : null) ??
    fiber.points[0]?.n ??
    null;

  return (
    <div className="space-y-6">
      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">Seed m</h2>
        <p className="text-sm text-muted">
          Pick a member of a backward-closed set A. The even block and the OE
          fiber are the two exact productions that join A.
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
                  setHovered(null);
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
                  setHovered(null);
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
          onHover={setHovered}
        />
        {block.listed && block.evens.length <= 16 ? (
          <p className="font-mono text-sm">{block.evens.join(", ")}</p>
        ) : null}
      </section>

      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">OE fiber Φ(m)</h2>
        <p className="text-sm text-muted">
          Odd n with <Tex>{String.raw`\lfloor n^{3/4}\rfloor=m`}</Tex>. Sea beads
          have even <Tex>{String.raw`\lfloor n^{3/2}\rfloor`}</Tex>, so{" "}
          <Tex>{String.raw`J(J(n))=m`}</Tex> and they join A. Ember beads do
          not use this production. Shares on this m are an observation, not the
          sweep proof.
        </p>
        <div className="grid gap-3 sm:grid-cols-4">
          <Metric label="H_m" value={String(fiber.H)} hint="odd n on the fiber" />
          <Metric label="G_m" value={String(fiber.G)} hint="even image" />
          <Metric
            label="G_m / H_m"
            value={formatShare(fiber.proportion)}
            hint="this fiber only"
          />
          <Metric
            label="Floors"
            value="1/7 and 1/3"
            hint="elementary and monotone"
          />
        </div>
        <OeFiberStrip
          view={fiber}
          selected={selected}
          onSelect={setSelected}
          onHover={setHovered}
        />
      </section>

      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">Parity sweep</h2>
        <p className="text-sm text-muted">
          On the fiber the quantity <Tex>{String.raw`n^{3/2}/2`}</Tex> advances
          by a nearly constant step. A walk with that step cannot hide in one
          half of the unit interval.
        </p>
        <SweepLane
          points={fiber.points}
          selected={selected}
          onSelect={setSelected}
          onHover={setHovered}
        />
        {inspect !== null ? (
          <ProductionWork n={inspect} />
        ) : (
          <p className="text-sm text-muted">Hover a bead to see the square root and the floor cut.</p>
        )}
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
        If m lies in a backward-closed set A, every sea bead joins A. That is
        the contagion mechanism. It excludes no fate and is not a halt theorem.
      </Disclaimer>
    </div>
  );
}
