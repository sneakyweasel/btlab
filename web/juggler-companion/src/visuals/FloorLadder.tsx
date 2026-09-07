const RUNGS = [
  { floor: "1,000,000", period: "25,781", name: "known floor" },
  { floor: "26,254,995", period: "176,251", name: "laboratory floor" },
  { floor: "162,849,448", period: "478,245", name: "second floor" },
  { floor: "350,000,000", period: "780,239", name: "main printed bound" },
];

export function FloorLadder() {
  return (
    <svg viewBox="0 0 640 300" role="img" className="h-auto w-full">
      <title>Four verified descent floors and the period bounds they buy</title>
      {RUNGS.map((rung, index) => {
        const y = 36 + index * 64;
        return (
          <g key={rung.floor}>
            <rect x="16" y={y} width="608" height="52" rx="10" fill="#fffdf7" stroke="#d4cbb8" />
            <text x="36" y={y + 22} fill="#5e574c" fontSize="13">
              {rung.name}
            </text>
            <text x="36" y={y + 42} fill="#1d1914" fontFamily="IBM Plex Mono, monospace" fontSize="15">
              N₀ = {rung.floor}
            </text>
            <text
              x="604"
              y={y + 34}
              textAnchor="end"
              fill="#1f3d34"
              fontFamily="Fraunces, serif"
              fontSize="20"
            >
              L ≥ {rung.period}
            </text>
          </g>
        );
      })}
    </svg>
  );
}
