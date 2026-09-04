import { useMemo, useState } from "react";
import { Disclaimer } from "../../components/Disclaimer";
import { Metric } from "../../components/Metric";
import { Tex } from "../../components/Tex";
import { TOUR_OE_FIBER_M } from "../../juggler/constants";
import { fiberView } from "../../juggler/productions";
import { OeFiberStrip } from "../../visuals/OeFiberStrip";
import { ProductionWork } from "../../visuals/ProductionWork";
import { SweepLane } from "../../visuals/SweepLane";

function formatShare(value: number | null): string {
  if (value === null) return "—";
  return value.toFixed(3);
}

export function OeFiberTab() {
  const fiber = useMemo(() => fiberView(TOUR_OE_FIBER_M), []);
  const firstSea = fiber.points.find((point) => point.imageEven)?.n ?? fiber.points[0]?.n ?? 0;
  const [selected, setSelected] = useState(firstSea);
  const [hovered, setHovered] = useState<number | null>(null);
  const inspect = hovered ?? selected;

  return (
    <div className="space-y-6">
      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">OE fiber of 100,000</h2>
        <p className="text-sm text-muted">
          The printed Paper C figure. Odd n with{" "}
          <Tex>{String.raw`\lfloor n^{3/4}\rfloor=100000`}</Tex>. Sea beads have
          even <Tex>{String.raw`\lfloor n^{3/2}\rfloor`}</Tex>, so{" "}
          <Tex>{String.raw`J(J(n))=100000`}</Tex> and they join A. Ember beads
          sit on the fiber but do not use this production. Shares on this m are
          an observation, not the sweep proof.
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
          On the fiber the quantity <Tex>{String.raw`\{n^{3/2}/2\}`}</Tex> advances
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

      <Disclaimer>
        If 100,000 lies in a backward-closed set A, every sea bead joins A. That
        is the contagion mechanism. It excludes no fate and is not a halt
        theorem.
      </Disclaimer>
    </div>
  );
}
