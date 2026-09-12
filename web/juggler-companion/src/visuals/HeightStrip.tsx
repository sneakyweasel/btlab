const STRIPS = [
  { label: "M < m³", name: "cubic band" },
  { label: "M < m³ − m^{15/8}", name: "Theorem 3.39, m ≥ 7" },
  { label: "later strips at large m", name: "Theorem 3.40" },
];

export function HeightStrip() {
  return (
    <svg viewBox="0 0 640 260" role="img" className="h-auto w-full">
      <title>Nested height ceilings under the cubic band, none of them a period kill</title>
      {STRIPS.map((strip, index) => {
        const y = 28 + index * 64;
        return (
          <g key={strip.label}>
            <rect x="16" y={y} width="608" height="52" rx="10" fill="#fffdf7" stroke="#d4cbb8" />
            <text x="36" y={y + 22} fill="#5e574c" fontSize="13">
              {strip.name}
            </text>
            <text
              x="36"
              y={y + 42}
              fill="#1d1914"
              fontFamily="Fraunces, serif"
              fontSize="20"
            >
              {strip.label}
            </text>
          </g>
        );
      })}
      <text x="36" y="246" fill="#5e574c" fontSize="13">
        necessary ceilings, not an exclusion of period 780,239
      </text>
    </svg>
  );
}
