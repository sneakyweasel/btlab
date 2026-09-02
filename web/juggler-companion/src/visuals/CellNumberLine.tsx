type CellNumberLineProps = {
  lo: number;
  hi: number;
  marks?: number[];
  label: string;
};

export function CellNumberLine({ lo, hi, marks = [], label }: CellNumberLineProps) {
  const span = Math.max(hi - lo, 1);
  const xOf = (n: number) => 36 + ((n - lo) / span) * 248;
  return (
    <svg viewBox="0 0 320 110" role="img" className="h-auto w-full">
      <title>{label}</title>
      <line x1="28" y1="48" x2="300" y2="48" stroke="#1d1914" strokeWidth="2" />
      <rect
        x={xOf(lo)}
        y="36"
        width={Math.max(xOf(hi) - xOf(lo), 4)}
        height="24"
        fill="#1f6f6a"
        opacity="0.18"
      />
      <text x="28" y="88" fill="#5e574c" fontSize="12" fontFamily="IBM Plex Mono, monospace">
        {lo}
      </text>
      <text x="300" y="88" textAnchor="end" fill="#5e574c" fontSize="12" fontFamily="IBM Plex Mono, monospace">
        {hi}
      </text>
      {marks.map((mark) => (
        <g key={mark}>
          <circle cx={xOf(mark)} cy="48" r="6" fill="#c45c26" />
          <text
            x={xOf(mark)}
            y="22"
            textAnchor="middle"
            fill="#c45c26"
            fontSize="12"
            fontFamily="IBM Plex Mono, monospace"
          >
            {mark}
          </text>
        </g>
      ))}
    </svg>
  );
}
