import { useMemo, useState } from "react";
import { Disclaimer } from "../../components/Disclaimer";
import { Metric } from "../../components/Metric";
import { Tex } from "../../components/Tex";
import {
  FIBER_SEEDS,
  PRODUCTION_M_MAX,
  TOUR_OE_FIBER_M,
} from "../../juggler/constants";
import { formatInt } from "../../juggler/format";
import { fiberView, randomOePath } from "../../juggler/productions";
import { OeFiberStrip } from "../../visuals/OeFiberStrip";
import { ProductionWork } from "../../visuals/ProductionWork";
import { SweepLane } from "../../visuals/SweepLane";

function formatShare(value: number | null): string {
  if (value === null) return "—";
  return value.toFixed(3);
}

export function OeFiberTab() {
  const [m, setM] = useState(TOUR_OE_FIBER_M);
  const fiber = useMemo(() => fiberView(m), [m]);
  const [selected, setSelected] = useState<number | null>(() =>
    randomOePath(fiberView(TOUR_OE_FIBER_M)),
  );
  const [hovered, setHovered] = useState<number | null>(null);
  const inspect = hovered ?? selected;

  function loadM(value: number) {
    setM(value);
    setHovered(null);
    setSelected(randomOePath(fiberView(value)));
  }

  return (
    <div className="space-y-6">
      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">OE fiber of {formatInt(m)}</h2>
        <p className="text-sm text-muted">
          Odd n with <Tex>{String.raw`\lfloor n^{3/4}\rfloor=m`}</Tex>. The strip
          is three rails: O every integer around the fiber, E the even images,
          then m. Orange is odd, blue is even, grey sits outside{" "}
          <Tex>{String.raw`\Phi(m)`}</Tex>. An even image means{" "}
          <Tex>{String.raw`J(J(n))=m`}</Tex> and that path joins A. An odd
          image stays on O and never reaches E. Paper C prints{" "}
          {formatInt(TOUR_OE_FIBER_M)}; shares on one m are an observation, not
          the sweep proof.
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
                  loadM(value);
                }
              }}
            />
          </label>
          <div className="flex flex-wrap gap-2">
            {FIBER_SEEDS.map((preset) => (
              <button
                key={preset.value}
                type="button"
                title={preset.note}
                className={`rounded-full px-3 py-1 text-sm ${
                  m === preset.value
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
          On the fiber the quantity <Tex>{String.raw`\{n^{3/2}/2\}`}</Tex> lives
          on the circle <Tex>{String.raw`\mathbb{R}/\mathbb{Z}`}</Tex>: 0 and 1
          are the same point. A walk with a nearly constant step cannot hide in
          one semicircle.
        </p>
        {fiber.points.length ? (
          <SweepLane
            points={fiber.points}
            selected={selected}
            onSelect={setSelected}
            onHover={setHovered}
          />
        ) : (
          <p className="text-sm text-muted">
            This m has no odd n with <Tex>{String.raw`\lfloor n^{3/4}\rfloor=m`}</Tex>.
          </p>
        )}
        {inspect !== null ? (
          <ProductionWork n={inspect} />
        ) : (
          <p className="text-sm text-muted">
            Hover a bead to see the square root and the floor cut.
          </p>
        )}
      </section>

      <Disclaimer>
        {`If ${formatInt(m)} lies in a backward-closed set A, every even image joins A. That is the contagion mechanism. It excludes no fate and is not a halt theorem.`}
      </Disclaimer>
    </div>
  );
}
