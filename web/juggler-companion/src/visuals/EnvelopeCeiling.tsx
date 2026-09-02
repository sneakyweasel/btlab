type EnvelopeCeilingProps = {
  points: number[];
};

export function EnvelopeCeiling({ points }: EnvelopeCeilingProps) {
  const values = points.length ? points : [3, 5, 11, 6];
  const max = Math.max(...values, 1);
  const coords = values.map((value, index) => {
    const x = 40 + (index * 240) / Math.max(values.length - 1, 1);
    const y = 150 - (Math.log(value) / Math.log(max + 1)) * 110;
    return `${x},${y}`;
  });
  return (
    <svg viewBox="0 0 320 190" role="img" className="mx-auto h-auto w-full max-w-md">
      <title>The walk stays under a power ceiling</title>
      <line x1="36" y1="28" x2="300" y2="28" stroke="#8b3a2a" strokeDasharray="6 5" strokeWidth="2" />
      <text x="300" y="20" textAnchor="end" fill="#8b3a2a" fontSize="12">
        envelope
      </text>
      <polyline
        points={coords.join(" ")}
        fill="none"
        stroke="#1f6f6a"
        strokeWidth="3"
      />
      {coords.map((pair) => {
        const [x, y] = pair.split(",").map(Number);
        return <circle key={pair} cx={x} cy={y} r="5" fill="#c45c26" />;
      })}
      <text x="160" y="178" textAnchor="middle" fill="#5e574c" fontSize="13">
        slack Δ is the room under the ceiling
      </text>
    </svg>
  );
}
