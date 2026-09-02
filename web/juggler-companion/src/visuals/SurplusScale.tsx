type SurplusScaleProps = {
  odds: number;
  length: number;
};

export function SurplusScale({ odds, length }: SurplusScaleProps) {
  const left = 3 ** odds;
  const right = 2 ** length;
  const max = Math.max(left, right, 1);
  const leftH = 16 + (120 * left) / max;
  const rightH = 16 + (120 * right) / max;
  const expanding = left > right;
  return (
    <svg viewBox="0 0 360 220" role="img" className="mx-auto h-auto w-full max-w-md">
      <title>Balance 3 to the odds against 2 to the length</title>
      <line x1="40" y1="180" x2="320" y2="180" stroke="#d4cbb8" strokeWidth="3" />
      <rect x="70" y={180 - leftH} width="70" height={leftH} fill="#c45c26" rx="6" />
      <rect x="220" y={180 - rightH} width="70" height={rightH} fill="#1f6f6a" rx="6" />
      <text x="105" y="200" textAnchor="middle" fontSize="13" fill="#5e574c">
        {`3^${odds} = ${left}`}
      </text>
      <text x="255" y="200" textAnchor="middle" fontSize="13" fill="#5e574c">
        {`2^${length} = ${right}`}
      </text>
      <text
        x="180"
        y="28"
        textAnchor="middle"
        fontFamily="Fraunces, serif"
        fontSize="18"
        fill={expanding ? "#8b3a2a" : left === right ? "#5e574c" : "#1f3d34"}
      >
        {expanding ? "expanding" : left === right ? "critical" : "contracting"}
      </text>
    </svg>
  );
}
