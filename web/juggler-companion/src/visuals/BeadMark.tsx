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
  labelBelow?: boolean;
  hideLabel?: boolean;
  persistLabel?: boolean;
  labelSize?: number;
  labelRotate?: number;
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
  labelBelow = false,
  hideLabel = false,
  persistLabel = false,
  labelSize = 12,
  labelRotate,
}: BeadMarkProps) {
  const labelX = Math.min(Math.max(x, 40), width - 40);
  const labelGap = labelRotate == null ? 16 : 10;
  const labelY = labelBelow ? y + labelGap : y - labelGap;
  const sticky = active || persistLabel;
  return (
    <g
      className={onSelect || onHover ? "bead-mark" : "bead-mark bead-mark-static"}
      tabIndex={onSelect || onHover ? 0 : undefined}
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
      {hideLabel ? null : (
      <text
        className={sticky ? undefined : "bead-label"}
        x={labelX}
        y={labelY}
        dominantBaseline={
          labelRotate == null
            ? labelBelow
              ? "hanging"
              : "auto"
            : "middle"
        }
        textAnchor={labelRotate == null ? "middle" : "start"}
        fill={color}
        fontSize={labelSize}
        fontFamily="IBM Plex Mono, monospace"
        paintOrder="stroke"
        stroke="#fffdf7"
        strokeWidth="4"
        transform={
          labelRotate == null
            ? undefined
            : `rotate(${labelRotate} ${labelX} ${labelY})`
        }
      >
        {formatInt(n)}
      </text>
      )}
    </g>
  );
}
