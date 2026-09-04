import { useMemo, useState } from "react";
import { Disclaimer } from "../../components/Disclaimer";
import { Metric } from "../../components/Metric";
import { Tex } from "../../components/Tex";
import {
  PRODUCTION_M_MAX,
  PRODUCTION_SEEDS,
} from "../../juggler/constants";
import { formatInt } from "../../juggler/format";
import { floorPower } from "../../juggler/map";
import { oddPreimageIntegers } from "../../juggler/preimages";
import { evenBlockView, fiberView } from "../../juggler/productions";
import { EvenBlockStrip } from "../../visuals/EvenBlockStrip";
import { OeFiberStrip } from "../../visuals/OeFiberStrip";
import { PreimageNumberLine } from "../../visuals/PreimageNumberLine";
import { SweepLane } from "../../visuals/SweepLane";

function formatShare(value: number | null): string {
  if (value === null) return "—";
  return value.toFixed(3);
}

export function PreimagesTab() {
  const [m, setM] = useState(12);
  const [selected, setSelected] = useState<number | null>(null);
  const block = useMemo(() => evenBlockView(m), [m]);
  const fiber = useMemo(() => fiberView(m), [m]);
  const odds = useMemo(() => oddPreimageIntegers(m), [m]);
  const selectedPoint = fiber.points.find((point) => point.n === selected) ?? null;
  const selectedIsEven = selected !== null && selected % 2 === 0;
  const selectedImage =
    selected === null ? null : selectedIsEven
      ? floorPower(BigInt(selected))
      : selectedPoint
        ? floorPower(floorPower(BigInt(selected)))
        : null;

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
                  setSelected(null);
                }
              }}
            />
          </label>
          <div className="flex flex-wrap gap-2">
            {PRODUCTION_SEEDS.map((seed) => (
              <button
                key={seed}
                type="button"
                className={`rounded-full px-3 py-1 text-sm ${
                  m === seed
                    ? "bg-deep text-card"
                    : "border border-line text-muted"
                }`}
                onClick={() => {
                  setM(seed);
                  setSelected(null);
                }}
              >
                {seed.toLocaleString("en-US")}
              </button>
            ))}
          </div>
        </div>
      </section>

      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">Even block E(m)</h2>
        <p className="text-sm text-muted">
          Every even n in [{formatInt(block.lo)}, {formatInt(block.hi)}) has{" "}
          <Tex>{String.raw`J(n)=m`}</Tex>. If m is in A, those evens are in A.
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
        <EvenBlockStrip view={block} selected={selected} onSelect={setSelected} />
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
        <OeFiberStrip view={fiber} selected={selected} onSelect={setSelected} />
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
        />
        {selected !== null ? (
          <p className="font-mono text-sm">
            {selectedIsEven
              ? `${selected} even → J = ${selectedImage?.toString() ?? "—"}`
              : selectedPoint
                ? `${selected} odd, image ${selectedPoint.imageEven ? "even" : "odd"} → J² = ${selectedImage?.toString() ?? "—"}`
                : `${selected} is not on this fiber`}
          </p>
        ) : (
          <p className="text-sm text-muted">Click a bead to inspect it.</p>
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
