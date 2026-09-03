import { regimeOf } from "../juggler/itinerary";

type SurplusScaleProps = {
  odds: number;
  length: number;
  compact?: boolean;
};

function powerLabel(base: number, exp: number, value: number): string {
  if (!Number.isFinite(value) || value > 1e12) return `${base}^${exp}`;
  return `${base}^${exp} = ${value}`;
}

export function SurplusScale({ odds, length, compact = false }: SurplusScaleProps) {
  const left = 3 ** odds;
  const right = 2 ** length;
  const finite = Number.isFinite(left) && Number.isFinite(right);
  const max = finite ? Math.max(left, right, 1) : 1;
  const leftLog = odds * Math.log(3);
  const rightLog = length * Math.log(2);
  const maxLog = Math.max(leftLog, rightLog, 1e-9);
  const bar = compact ? 72 : 120;
  const leftH = 16 + (bar * (finite ? left / max : leftLog / maxLog));
  const rightH = 16 + (bar * (finite ? right / max : rightLog / maxLog));
  const regime = regimeOf(length, odds);
  const height = compact ? 168 : 220;
  const base = height - 40;
  return (
    <svg
      viewBox={`0 0 360 ${height}`}
      role="img"
      className={`mx-auto h-auto w-full ${compact ? "" : "max-w-md"}`}
    >
      <title>Balance 3 to the odds against 2 to the length</title>
      <line x1="40" y1={base} x2="320" y2={base} stroke="#d4cbb8" strokeWidth="3" />
      <rect x="70" y={base - leftH} width="70" height={leftH} fill="var(--color-odd)" rx="6" />
      <rect x="220" y={base - rightH} width="70" height={rightH} fill="var(--color-even)" rx="6" />
      <text x="105" y={base + 20} textAnchor="middle" fontSize="13" fill="#5e574c">
        {powerLabel(3, odds, left)}
      </text>
      <text x="255" y={base + 20} textAnchor="middle" fontSize="13" fill="#5e574c">
        {powerLabel(2, length, right)}
      </text>
      <text
        x="180"
        y="28"
        textAnchor="middle"
        fontFamily="Fraunces, serif"
        fontSize="18"
        fill={regime === "expanding" ? "#8b3a2a" : regime === "critical" ? "#5e574c" : "#1f3d34"}
      >
        {regime}
      </text>
    </svg>
  );
}
