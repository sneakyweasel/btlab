import { formatInt } from "../juggler/format";

type BeadMarkProps = {
  x: number;
  y?: number;
  n: number;
  color: string;
  active?: boolean;
  radius?: number;
  width?: number;
  onSelect?: (n: number) => void;
  onHover?: (n: number | null) => void;
};

export function BeadMark({
  x,
  y = 50,
  n,
  color,
  active = false,
  radius = 6,
  width = 640,
  onSelect,
  onHover,
}: BeadMarkProps) {
  const labelX = Math.min(Math.max(x, 40), width - 40);
  return (
    <g
      className="bead-mark"
      tabIndex={0}
      onMouseEnter={() => onHover?.(n)}
      onMouseLeave={() => onHover?.(null)}
      onFocus={() => onHover?.(n)}
      onBlur={() => onHover?.(null)}
      onClick={() => onSelect?.(n)}
    >
      <circle cx={x} cy={y} r="12" fill="transparent" />
      <circle
        className="bead-dot"
        cx={x}
        cy={y}
        r={active ? Math.max(radius + 2, 8) : radius}
        fill={color}
        stroke={active ? "#1d1914" : "none"}
        strokeWidth={active ? 2 : 0}
      />
      <text
        className={active ? undefined : "bead-label"}
        x={labelX}
        y={y - 16}
        textAnchor="middle"
        fill={color}
        fontSize="12"
        fontFamily="IBM Plex Mono, monospace"
        paintOrder="stroke"
        stroke="#fffdf7"
        strokeWidth="4"
      >
        {formatInt(n)}
      </text>
    </g>
  );
}
