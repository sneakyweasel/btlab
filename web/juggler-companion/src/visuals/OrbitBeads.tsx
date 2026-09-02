import { letterOf } from "../juggler/map";

type OrbitBeadsProps = {
  states: readonly bigint[];
  active?: number;
};

export function OrbitBeads({ states, active }: OrbitBeadsProps) {
  const width = Math.max(640, states.length * 88);
  return (
    <svg viewBox={`0 0 ${width} 120`} role="img" className="h-auto w-full">
      <title>Orbit beads, odd and even letters</title>
      {states.map((state, index) => {
        const x = 44 + index * 88;
        const letter = index < states.length - 1 ? letterOf(state) : "";
        const odd = state % 2n === 1n;
        const isActive = active === index;
        return (
          <g key={`${index}-${state.toString()}`}>
            {index < states.length - 1 && (
              <line
                x1={x + 28}
                y1="48"
                x2={x + 60}
                y2="48"
                stroke="#d4cbb8"
                strokeWidth="2"
              />
            )}
            <circle
              cx={x}
              cy="48"
              r={isActive ? 26 : 22}
              fill={odd ? "#c45c26" : "#1f6f6a"}
              opacity={isActive || active === undefined ? 1 : 0.45}
            />
            <text
              x={x}
              y="53"
              textAnchor="middle"
              fill="#fffdf7"
              fontFamily="IBM Plex Mono, monospace"
              fontSize="14"
            >
              {state.toString()}
            </text>
            {letter && (
              <text
                x={x}
                y="96"
                textAnchor="middle"
                fill={letter === "O" ? "#c45c26" : "#1f6f6a"}
                fontFamily="IBM Plex Mono, monospace"
                fontSize="16"
              >
                {letter}
              </text>
            )}
          </g>
        );
      })}
    </svg>
  );
}
