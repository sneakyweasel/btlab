type CycleNecklaceProps = {
  word: string;
  shift?: number;
  minIndex?: number;
};

export function CycleNecklace({ itinerary, shift = 0, minIndex }: CycleNecklaceProps) {
  const n = Math.max(word.length, 1);
  const cx = 160;
  const cy = 140;
  const r = 88;
  return (
    <svg viewBox="0 0 320 280" role="img" className="mx-auto h-auto w-full max-w-sm">
      <title>Cycle itinerary as a rotatable necklace</title>
      <circle cx={cx} cy={cy} r={r} fill="none" stroke="#d4cbb8" strokeWidth="2" />
      {Array.from(word).map((letter, index) => {
        const angle = ((index - shift) / n) * 2 * Math.PI - Math.PI / 2;
        const x = cx + r * Math.cos(angle);
        const y = cy + r * Math.sin(angle);
        const isMin = minIndex === index;
        const odd = letter === "O";
        return (
          <g key={`${letter}-${index}`}>
            <circle
              cx={x}
              cy={y}
              r={isMin ? 20 : 16}
              fill={odd ? "#c45c26" : "#1f6f6a"}
              stroke={isMin ? "#1d1914" : "none"}
              strokeWidth={isMin ? 3 : 0}
            />
            <text
              x={x}
              y={y + 5}
              textAnchor="middle"
              fill="#fffdf7"
              fontFamily="IBM Plex Mono, monospace"
              fontSize="14"
            >
              {letter}
            </text>
          </g>
        );
      })}
      <text
        x={cx}
        y={cy + 6}
        textAnchor="middle"
        fill="#5e574c"
        fontFamily="Source Sans 3, sans-serif"
        fontSize="13"
      >
        rotate to CycleMin
      </text>
    </svg>
  );
}
