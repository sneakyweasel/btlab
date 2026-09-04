import { EMBER, SEA } from "../juggler/palette";

type EnvelopeCeilingProps = {
  points: number[];
  ceiling?: number[];
  active?: number;
};

function finitePositive(value: number): number {
  return value > 0 && Number.isFinite(value) ? value : 1;
}

function plotY(value: number, max: number): number {
  return 150 - (Math.log(finitePositive(value)) / Math.log(max + 1)) * 110;
}

function plotX(index: number, count: number): number {
  return 40 + (index * 240) / Math.max(count - 1, 1);
}

export function EnvelopeCeiling({ points, ceiling, active }: EnvelopeCeilingProps) {
  const values = points.length ? points : [1];
  const caps = ceiling && ceiling.length === values.length ? ceiling : null;
  const max = Math.max(
    ...values.map(finitePositive),
    ...(caps ?? []).map(finitePositive),
    1,
  );
  const walk = values.map((value, index) => ({
    x: plotX(index, values.length),
    y: plotY(value, max),
  }));
  const bound = caps?.map((value, index) => ({
    x: plotX(index, values.length),
    y: plotY(value, max),
  }));
  const lastBound = bound?.at(-1);
  const mark = active !== undefined && active >= 0 && active < walk.length ? active : walk.length - 1;

  return (
    <svg viewBox="0 0 320 190" role="img" className="mx-auto h-auto w-full max-w-md">
      <title>The walk stays under the computed power ceiling</title>
      {bound ? (
        <>
          <polyline
            points={bound.map((point) => `${point.x},${point.y}`).join(" ")}
            fill="none"
            stroke={EMBER}
            strokeDasharray="6 5"
            strokeWidth="2"
          />
          {lastBound ? (
            <text x={lastBound.x} y={Math.max(lastBound.y - 10, 14)} textAnchor="end" fill={EMBER} fontSize="12">
              envelope
            </text>
          ) : null}
        </>
      ) : null}
      <polyline
        points={walk.map((point) => `${point.x},${point.y}`).join(" ")}
        fill="none"
        stroke={SEA}
        strokeWidth="3"
      />
      {walk.map((point, index) => (
        <circle
          key={`${point.x}-${index}`}
          cx={point.x}
          cy={point.y}
          r={index === mark ? 6 : 5}
          fill={EMBER}
        />
      ))}
      <text x="160" y="178" textAnchor="middle" fill="#5e574c" fontSize="13">
        slack is the room under the ceiling
      </text>
    </svg>
  );
}
