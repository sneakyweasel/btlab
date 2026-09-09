import { LeftoverWidget } from "../../components/CycleTourWidget";

export function SurvivorsTab() {
  return (
    <div className="space-y-5">
      <p className="text-sm text-muted">
        A CycleMin-shaped word, or a leftover-shaped walk from a start such
        as 365, is a survivor of an easy kill. That is still not a cycle.
      </p>
      <LeftoverWidget />
    </div>
  );
}
