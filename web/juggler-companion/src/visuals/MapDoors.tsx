type MapDoorsProps = {
  highlight?: "even" | "odd" | null;
};

export function MapDoors({ highlight = null }: MapDoorsProps) {
  const evenActive = highlight !== "odd";
  const oddActive = highlight !== "even";
  return (
    <svg viewBox="0 0 640 220" role="img" className="h-auto w-full">
      <title>Even steps shrink; odd steps grow</title>
      <rect x="8" y="18" width="300" height="184" rx="16" fill="#fffdf7" stroke="#d4cbb8" />
      <rect x="332" y="18" width="300" height="184" rx="16" fill="#fffdf7" stroke="#d4cbb8" />
      <text x="158" y="48" textAnchor="middle" fill="#1f6f6a" fontFamily="Fraunces, serif" fontSize="20">
        Even door
      </text>
      <text x="482" y="48" textAnchor="middle" fill="#c45c26" fontFamily="Fraunces, serif" fontSize="20">
        Odd door
      </text>
      <text x="158" y="78" textAnchor="middle" fill="#5e574c" fontSize="14" fontFamily="Source Sans 3, sans-serif">
        n even → floor(n
        <tspan baselineShift="super" fontSize="10">1/2</tspan>
        )
      </text>
      <text x="482" y="78" textAnchor="middle" fill="#5e574c" fontSize="14" fontFamily="Source Sans 3, sans-serif">
        n odd → floor(n
        <tspan baselineShift="super" fontSize="10">3/2</tspan>
        )
      </text>
      <path
        d="M80 150 H220"
        stroke="#1f6f6a"
        strokeWidth={evenActive ? 6 : 3}
        opacity={evenActive ? 1 : 0.35}
      />
      <path
        d="M80 138 L80 162 M220 142 L236 150 L220 158"
        fill="none"
        stroke="#1f6f6a"
        strokeWidth="3"
        opacity={evenActive ? 1 : 0.35}
      />
      <text x="158" y="178" textAnchor="middle" fill="#1f6f6a" fontSize="13">
        shrinks
      </text>
      <path
        d="M404 150 H544"
        stroke="#c45c26"
        strokeWidth={oddActive ? 6 : 3}
        opacity={oddActive ? 1 : 0.35}
      />
      <path
        d="M544 138 L544 162 M404 142 L388 150 L404 158"
        fill="none"
        stroke="#c45c26"
        strokeWidth="3"
        opacity={oddActive ? 1 : 0.35}
      />
      <text x="482" y="178" textAnchor="middle" fill="#c45c26" fontSize="13">
        grows
      </text>
    </svg>
  );
}
