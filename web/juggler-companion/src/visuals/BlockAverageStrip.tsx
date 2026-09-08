import { EVEN, ODD } from "../juggler/palette";
import { formatInt } from "../juggler/format";
import type { BlockAverageView, BlockFiberShare } from "../juggler/productions";

type BlockAverageStripProps = {
  view: BlockAverageView;
  selected?: number | null;
  onSelect?: (m: number) => void;
  onHover?: (m: number | null) => void;
};

const WIDTH = 640;
const HEIGHT = 168;
const LEFT = 28;
const RIGHT = 612;
const BASE = 118;
const BAR_H = 86;
const GREY = "#cfc6b4";

function columnX(index: number, count: number): number {
  const span = RIGHT - LEFT;
  return LEFT + ((index + 0.5) / Math.max(count, 1)) * span;
}

function columnWidth(count: number): number {
  const gap = count <= 12 ? 6 : 3;
  return Math.max(6, Math.min(28, (RIGHT - LEFT) / Math.max(count, 1) - gap));
}

export function BlockAverageStrip({
  view,
  selected = null,
  onSelect,
  onHover,
}: BlockAverageStripProps) {
  const count = view.fibers.length;
  const maxH = Math.max(1, ...view.fibers.map((fiber) => fiber.H));
  const width = columnWidth(count);
  const labelEvery = count <= 12;
  return (
    <div>
      <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} role="img" className="h-auto w-full">
        <title>
          Even-image share G/H on each even-m fiber of the block E({view.mPrime})
        </title>
        <line
          x1={LEFT}
          y1={BASE - BAR_H / 2}
          x2={RIGHT}
          y2={BASE - BAR_H / 2}
          stroke="#1d1914"
          strokeWidth="1"
          strokeDasharray="3 3"
          opacity="0.35"
        />
        <text
          x={LEFT - 4}
          y={BASE - BAR_H / 2 + 4}
          textAnchor="end"
          fill="#5e574c"
          fontSize="10"
          fontFamily="IBM Plex Mono, monospace"
        >
          1/2
        </text>
        {view.fibers.map((fiber, index) => (
          <FiberColumn
            key={fiber.m}
            fiber={fiber}
            x={columnX(index, count)}
            width={width}
            maxH={maxH}
            active={selected === fiber.m}
            showLabel={labelEvery || selected === fiber.m || index === 0 || index === count - 1}
            onSelect={onSelect}
            onHover={onHover}
          />
        ))}
        <line
          x1={LEFT}
          y1={BASE}
          x2={RIGHT}
          y2={BASE}
          stroke="#1d1914"
          strokeWidth="1.4"
        />
      </svg>
      <p className="text-center text-sm text-muted">
        Each column is one even m in E({formatInt(view.mPrime)}). Teal is an even
        image, orange is an odd image. The dashed line is 1/2.
      </p>
    </div>
  );
}

function FiberColumn({
  fiber,
  x,
  width,
  maxH,
  active,
  showLabel,
  onSelect,
  onHover,
}: {
  fiber: BlockFiberShare;
  x: number;
  width: number;
  maxH: number;
  active: boolean;
  showLabel: boolean;
  onSelect?: (m: number) => void;
  onHover?: (m: number | null) => void;
}) {
  const total = (fiber.H / maxH) * BAR_H;
  const evenH = fiber.H === 0 ? 0 : (fiber.G / fiber.H) * total;
  const oddH = total - evenH;
  const left = x - width / 2;
  return (
    <g
      className={onSelect || onHover ? "bead-mark" : "bead-mark bead-mark-static"}
      tabIndex={onSelect || onHover ? 0 : undefined}
      onMouseEnter={() => onHover?.(fiber.m)}
      onMouseLeave={() => onHover?.(null)}
      onFocus={() => onHover?.(fiber.m)}
      onBlur={() => onHover?.(null)}
      onClick={() => onSelect?.(fiber.m)}
    >
      <rect
        x={left - 3}
        y={BASE - BAR_H - 6}
        width={width + 6}
        height={BAR_H + 12}
        fill="transparent"
      />
      {oddH > 0 ? (
        <rect
          x={left}
          y={BASE - total}
          width={width}
          height={oddH}
          fill={ODD}
          opacity="0.85"
        />
      ) : null}
      {evenH > 0 ? (
        <rect
          x={left}
          y={BASE - evenH}
          width={width}
          height={evenH}
          fill={EVEN}
          opacity="0.9"
        />
      ) : null}
      {fiber.H === 0 ? (
        <rect
          x={left}
          y={BASE - 8}
          width={width}
          height={8}
          fill={GREY}
          opacity="0.7"
        />
      ) : null}
      {active ? (
        <rect
          x={left - 1.5}
          y={BASE - Math.max(total, 8) - 1.5}
          width={width + 3}
          height={Math.max(total, 8) + 3}
          fill="none"
          stroke="#1d1914"
          strokeWidth="1.6"
        />
      ) : null}
      {showLabel ? (
        <text
          x={x}
          y={BASE + 16}
          textAnchor="middle"
          fill={active ? "#1d1914" : "#5e574c"}
          fontSize="10"
          fontFamily="IBM Plex Mono, monospace"
        >
          {formatInt(fiber.m)}
        </text>
      ) : null}
    </g>
  );
}
