import { MapWidget } from "../../components/TourWidgets";

export function TrajectoryTab() {
  return (
    <div className="space-y-5">
      <p className="text-sm text-muted">
        Trajectory = the list of values. Itinerary = the O/E parities of the
        prefix so far. Live starts walk in the browser under 256 bits. Shipped
        peaks (173, 193, 761, 2183, 3889) load from JSON and are not recomputed.
        Hitting 1 is one trajectory, not a theorem.
      </p>
      <MapWidget initial={173n} />
    </div>
  );
}
