export function CubicBandOrder() {
  const odds = ["m", "c₁", "c₂", "…", "cₒ₋₁"];
  const evens = ["cₒ", "…", "M"];
  return (
    <svg viewBox="0 0 640 220" role="img" className="h-auto w-full">
      <title>Cubic-band rank rotation: odds then evens, plus the even count</title>
      <text x="36" y="28" fill="#5e574c" fontSize="13">
        sorted states, M &lt; m³
      </text>
      {odds.map((label, index) => {
        const x = 36 + index * 56;
        return (
          <g key={`odd-${label}`}>
            <circle cx={x + 18} cy="78" r="18" fill="#1f3d34" />
            <text
              x={x + 18}
              y="83"
              textAnchor="middle"
              fill="#fffdf7"
              fontFamily="IBM Plex Mono, monospace"
              fontSize="11"
            >
              {label}
            </text>
          </g>
        );
      })}
      {evens.map((label, index) => {
        const x = 36 + (odds.length + index) * 56;
        return (
          <g key={`even-${label}`}>
            <circle cx={x + 18} cy="78" r="18" fill="#fffdf7" stroke="#1f3d34" strokeWidth="2" />
            <text
              x={x + 18}
              y="83"
              textAnchor="middle"
              fill="#1d1914"
              fontFamily="IBM Plex Mono, monospace"
              fontSize="11"
            >
              {label}
            </text>
          </g>
        );
      })}
      <text x="36" y="128" fill="#5e574c" fontSize="13">
        odds below m²
      </text>
      <text x="604" y="128" textAnchor="end" fill="#5e574c" fontSize="13">
        evens at or above m²
      </text>
      <path d="M54 158 H586" stroke="#1f3d34" strokeWidth="2" markerEnd="url(#cubic-arrow)" />
      <text
        x="320"
        y="188"
        textAnchor="middle"
        fill="#1d1914"
        fontFamily="Fraunces, serif"
        fontSize="18"
      >
        J sends each rank ahead by e letters
      </text>
      <text x="320" y="210" textAnchor="middle" fill="#5e574c" fontSize="12">
        leftover counts force the mechanical word if M &lt; m³
      </text>
      <defs>
        <marker id="cubic-arrow" markerWidth="8" markerHeight="8" refX="6" refY="4" orient="auto">
          <path d="M0,0 L8,4 L0,8 Z" fill="#1f3d34" />
        </marker>
      </defs>
    </svg>
  );
}
