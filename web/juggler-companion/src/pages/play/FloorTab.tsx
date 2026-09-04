import { FloorWidget } from "../../components/TourWidgets";
import {
  LAB_FLOOR,
  LAB_WALK_PERIOD,
  PAPER_FLOOR,
  PAPER_PERIOD,
  PRINTED_FLOOR,
  PRINTED_PERIOD,
} from "../../juggler/constants";

const FLOORS = [
  { title: "Theorem 4.6", bound: PAPER_PERIOD, floor: PAPER_FLOOR, name: "known floor" },
  { title: "Theorem 5.9", bound: LAB_WALK_PERIOD, floor: LAB_FLOOR, name: "laboratory floor" },
  { title: "Corollary 5.10", bound: PRINTED_PERIOD, floor: PRINTED_FLOOR, name: "printed floor" },
] as const;

export function FloorTab() {
  return (
    <div className="space-y-5">
      <p className="text-sm text-muted">
        N₀ is a certified computation you feed the inequality, not the theorem.
        Combined with finance those floors become period lower bounds. This page
        does not search for a new floor and is not a halt theorem.
      </p>
      <FloorWidget />
      <div className="grid gap-3 sm:grid-cols-3">
        {FLOORS.map((row) => (
          <div key={row.title} className="rounded-xl border border-line bg-card p-4">
            <div className="text-xs uppercase tracking-wide text-muted">{row.name}</div>
            <div className="mt-1 text-xs text-muted">{row.title}</div>
            <div className="mt-2 font-serif text-3xl">
              L ≥ {row.bound.toLocaleString("en-US")}
            </div>
            <div className="mt-1 text-sm text-muted">
              at N₀ = {row.floor.toLocaleString("en-US")}
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}
