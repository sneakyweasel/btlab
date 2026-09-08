import { NavLink, Navigate, Outlet } from "react-router-dom";
import { Disclaimer } from "../components/Disclaimer";

const TABS = [
  { to: "/play/trajectory", label: "Trajectory" },
  { to: "/play/cycle", label: "Cycle" },
  { to: "/play/survivors", label: "Survivors" },
  { to: "/play/run-suffix", label: "Run-suffix" },
  { to: "/play/itinerary", label: "Itinerary" },
  { to: "/play/preimages", label: "Preimages" },
  { to: "/play/oe-fiber", label: "OE fiber" },
  { to: "/play/block-average", label: "Block average" },
  { to: "/play/three-sources", label: "Three sources" },
  { to: "/play/v-ladder", label: "V-ladder" },
  { to: "/play/floor", label: "Floor" },
  { to: "/play/finance", label: "Finance" },
  { to: "/play/gap-transfer", label: "Gap transfer" },
  { to: "/play/walk", label: "Walk charge" },
  { to: "/play/fan", label: "Fan" },
  { to: "/play/ceiling", label: "Ceiling" },
];

export function PlaygroundIndexPage() {
  return <Navigate to="/play/trajectory" replace />;
}

export function PlaygroundPage() {
  return (
    <div className="space-y-6">
      <header>
        <h1 className="text-4xl">Playground</h1>
        <p className="prose-measure mt-3 text-muted">
          Walk a start — including the shipped peaks — follow a short itinerary,
          rotate a cycle word, inspect a CycleMin survivor, cross a run-suffix
          pair, grow the two Paper C productions, average an even block, split the three sources, climb the V-ladder, look up a certified floor,
          look up a length in the shipped Theorem 4.6 table, read the
          gap-transfer / Rhin plane, the walk-charge explorer, or the
          semiconvergent fan. Caps:
          80 steps, 256 bits live, itineraries of length at most 8 (cycles 16,
          tour words 24), production seeds at most 1,000,000. Shipped monsters
          are pictures, not a live walk. Hitting 1 is not a theorem.
          The Paper C contagion walk is Preimages → OE fiber → Block
          average → Three sources → V-ladder; those tabs are
          observations, not proofs.
        </p>
      </header>
      <nav className="flex flex-wrap gap-2">
        {TABS.map((tab) => (
          <NavLink
            key={tab.to}
            to={tab.to}
            className={({ isActive }) =>
              `rounded-full px-3 py-1 text-sm no-underline ${
                isActive ? "bg-deep text-card" : "border border-line text-muted"
              }`
            }
          >
            {tab.label}
          </NavLink>
        ))}
      </nav>
      <Disclaimer>
        A playground hit of 1, or a length the table does not kill, is not
        evidence for a cycle and not a halt theorem.
      </Disclaimer>
      <Outlet />
    </div>
  );
}
