import { useMemo, useState } from "react";
import { Link } from "react-router-dom";
import { Disclaimer } from "../../components/Disclaimer";
import { Metric } from "../../components/Metric";
import { Tex } from "../../components/Tex";
import {
  BLOCK_M_PRIME_MAX,
  BLOCK_SEEDS,
  TOUR_BLOCK_M_PRIME,
} from "../../juggler/constants";
import { formatInt } from "../../juggler/format";
import { blockAverageView } from "../../juggler/productions";
import { BlockAverage } from "../../visuals/BlockAverage";
import { BlockAverageStrip } from "../../visuals/BlockAverageStrip";

function formatShare(value: number | null): string {
  if (value === null) return "—";
  return value.toFixed(3);
}

export function BlockAverageTab() {
  const [mPrime, setMPrime] = useState(TOUR_BLOCK_M_PRIME);
  const view = useMemo(() => blockAverageView(mPrime), [mPrime]);
  const [selected, setSelected] = useState<number | null>(
    () => blockAverageView(TOUR_BLOCK_M_PRIME).fibers[0]?.m ?? null,
  );
  const [hovered, setHovered] = useState<number | null>(null);
  const inspect =
    view.fibers.find((fiber) => fiber.m === (hovered ?? selected)) ?? null;

  function loadM(value: number) {
    setMPrime(value);
    setHovered(null);
    const next = blockAverageView(value);
    setSelected(next.fibers[0]?.m ?? null);
  }

  return (
    <div className="space-y-6">
      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">
          Even-block average of {formatInt(mPrime)}
        </h2>
        <p className="text-sm text-muted">
          Proposition 4.4 averages the fibers of the even m in{" "}
          <Tex>{String.raw`E(m')`}</Tex>. Those fibers sit in{" "}
          <Tex>{String.raw`I(m')=[m'^{8/3},(m'+1)^{8/3})`}</Tex>.{" "}
          <Tex>{String.raw`U(m')`}</Tex> is the odd n with even{" "}
          <Tex>{String.raw`\lfloor n^{3/4}\rfloor`}</Tex> and even{" "}
          <Tex>{String.raw`\lfloor n^{3/2}\rfloor`}</Tex> — the teal part of
          the even-m columns. One fiber can be empty; the block is the{" "}
          <Tex>{String.raw`1/3`}</Tex> in item 2 of §5.1. Playground shares
          are an observation, not the van der Corput proof. Those three
          families are the{" "}
          <Link to="/play/three-sources">three sources</Link> tab.
        </p>
        <div className="flex flex-wrap items-end gap-3">
          <label className="text-sm text-muted">
            m'
            <input
              className="ml-2 w-28 rounded border border-line bg-paper px-2 py-1 font-mono"
              type="number"
              min={1}
              max={BLOCK_M_PRIME_MAX}
              value={mPrime}
              onChange={(event) => {
                const value = Number(event.target.value);
                if (
                  Number.isInteger(value) &&
                  value >= 1 &&
                  value <= BLOCK_M_PRIME_MAX
                ) {
                  loadM(value);
                }
              }}
            />
          </label>
          <div className="flex flex-wrap gap-2">
            {BLOCK_SEEDS.map((preset) => (
              <button
                key={preset.value}
                type="button"
                title={preset.note}
                className={`rounded-full px-3 py-1 text-sm ${
                  mPrime === preset.value
                    ? "bg-deep text-card"
                    : "border border-line text-muted"
                }`}
                onClick={() => loadM(preset.value)}
              >
                {preset.value.toLocaleString("en-US")}
              </button>
            ))}
          </div>
        </div>
        <div className="grid gap-3 sm:grid-cols-4">
          <Metric
            label="even m"
            value={String(view.evenM)}
            hint={`E(${formatInt(mPrime)})`}
          />
          <Metric
            label="I(m')"
            value={`${formatInt(view.lo)}–${formatInt(view.hi)}`}
            hint="odd n on the fibers"
          />
          <Metric
            label="mean G/H"
            value={formatShare(view.meanEven)}
            hint="weighted on even m"
          />
          <Metric
            label="this fiber"
            value={
              inspect
                ? `${inspect.G}/${inspect.H}`
                : "—"
            }
            hint={inspect ? `m = ${formatInt(inspect.m)}` : "click a column"}
          />
        </div>
        <BlockAverageStrip
          view={view}
          selected={selected}
          onSelect={setSelected}
          onHover={setHovered}
        />
      </section>

      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">Share against 1/4</h2>
        <p className="text-sm text-muted">
          The proved bound is{" "}
          <Tex>{String.raw`|U|\ge\#\{\text{odd }n\}/4-250\,m'^{11/9}\log(m'+1)`}</Tex>.
          At playground m' the error still dominates the main term. The bar
          is the raw share.
        </p>
        <BlockAverage view={view} />
      </section>

      <Disclaimer>
        {`If ${formatInt(mPrime)} lies in a backward-closed set A, the even images on E(${formatInt(mPrime)}) join A. That is item 2 of the contagion recursion. It excludes no fate and is not a halt theorem.`}
      </Disclaimer>
    </div>
  );
}
