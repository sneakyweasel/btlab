import { NavLink, Navigate, Outlet } from "react-router-dom";
import { Disclaimer } from "../components/Disclaimer";

const TABS = [
  { to: "/play/trajectory", label: "Trajectory" },
  { to: "/play/itinerary", label: "Itinerary" },
  { to: "/play/preimages", label: "Preimages" },
  { to: "/play/cycle", label: "Cycle" },
  { to: "/play/finance", label: "Finance" },
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
          Basic tests only: walk a start, follow a short itinerary, grow the two
          Paper C productions of a seed, rotate a necklace, or look up a length
          in the shipped Theorem 4.6 table. Caps: 80 steps, 256 bits, itineraries
          of length at most 8 (cycles 16), production seeds at most 100,000. The
          trajectory is the values; the itinerary is the O/E parities of a
          prefix. The even block and the OE fiber are the two productions of
          J⁻¹(m).
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
