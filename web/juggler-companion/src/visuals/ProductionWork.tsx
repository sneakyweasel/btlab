import { floorPower } from "../juggler/map";
import { FloorCut } from "./FloorCut";

type ProductionWorkProps = {
  n: number;
};

export function ProductionWork({ n }: ProductionWorkProps) {
  const start = BigInt(n);
  if (n % 2 === 0) {
    return <FloorCut n={start} result={floorPower(start)} />;
  }
  const mid = floorPower(start);
  return (
    <div className="grid gap-3 sm:grid-cols-2">
      <FloorCut n={start} result={mid} />
      <FloorCut n={mid} result={floorPower(mid)} />
    </div>
  );
}
