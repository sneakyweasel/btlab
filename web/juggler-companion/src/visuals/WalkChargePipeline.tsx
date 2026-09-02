const STAGES = [
  "Transport",
  "Hug adversary",
  "Word identity",
  "Denjoy–Koksma",
  "Window",
  "L ≥ 478245",
];

export function WalkChargePipeline() {
  return (
    <svg viewBox="0 0 720 160" role="img" className="h-auto w-full">
      <title>Walk-charge pipeline from transport to the printed period bound</title>
      {STAGES.map((label, index) => {
        const x = 12 + index * 118;
        return (
          <g key={label}>
            <rect x={x} y="48" width="108" height="56" rx="10" fill="#fffdf7" stroke="#1f3d34" />
            <text
              x={x + 54}
              y="80"
              textAnchor="middle"
              fill="#1d1914"
              fontSize="11"
              fontFamily="Source Sans 3, sans-serif"
            >
              {label}
            </text>
            {index < STAGES.length - 1 && (
              <path
                d={`M${x + 108} 76 L${x + 118} 76`}
                stroke="#1f3d34"
                strokeWidth="2"
                markerEnd="url(#arrow)"
              />
            )}
          </g>
        );
      })}
      <defs>
        <marker id="arrow" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
          <path d="M0,0 L8,4 L0,8 Z" fill="#1f3d34" />
        </marker>
      </defs>
    </svg>
  );
}
