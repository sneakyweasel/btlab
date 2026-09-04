import type { NecklaceFigure } from "../juggler/necklace";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const INK = "#1d1914";
const MUTED = "#5e574c";
const WARN = "#8b3a2a";
const OK = "#2d6a4f";

const WIDTH = 640;
const HEIGHT = 420;
const CX = 320;
const CY = 200;
/** Radius of the lowest value on the log scale. */
const R_MIN = 34;
/** Radius of the highest value on the log scale. */
const R_MAX = 158;
/** Ring where the itinerary letters sit. */
const R_LETTERS = R_MAX + 22;

function TenPow({ exp }: { exp: number }) {
  return (
    <>
      10
      <tspan dy="-4" fontSize="7">
        {Math.round(exp)}
      </tspan>
    </>
  );
}

type ExcursionWaveProps = {
  figure: NecklaceFigure;
  /** Hide the step labels and verdicts for a tour-sized figure. */
  compact?: boolean;
};

/**
 * The wave v_0 → p_0 → v_1 → … of a realized walk, drawn in polar
 * coordinates: one full turn is the word, the angle is the step, the
 * radius is log value. A cycle would close on itself at the top. The
 * three rings a cycle minimum must respect are n itself (the inner
 * ring), n² (every even state is at least here) and (n+1)² (the first
 * peak must clear it; the last peak must land in the thin band just
 * under it, so that one square root returns to n).
 */
export function ExcursionWave({ figure, compact = false }: ExcursionWaveProps) {
  const { word, logs, logN, logSq, logSq1 } = figure;
  const turn = Math.max(word.length, 1);
  const dataLo = Math.min(...logs, logN);
  const dataHi = Math.max(...logs, logSq1);
  const pad = Math.max(0.35, (dataHi - dataLo) * 0.08);
  const lo = Math.max(0, dataLo - pad);
  const hi = dataHi + pad;

  const radius = (log10v: number) =>
    hi === lo ? (R_MIN + R_MAX) / 2 : R_MIN + ((log10v - lo) / (hi - lo)) * (R_MAX - R_MIN);
  const angle = (step: number) => -Math.PI / 2 + (2 * Math.PI * step) / turn;
  const polar = (r: number, a: number) => ({ x: CX + r * Math.cos(a), y: CY + r * Math.sin(a) });

  const points = logs.map((log, index) => {
    const { x, y } = polar(radius(log), angle(index));
    return {
      x,
      y,
      letter: figure.realized[index] ?? null,
      below: figure.below[index],
      odd: figure.odd[index],
      label: figure.labels[index],
      r: radius(log),
      a: angle(index),
    };
  });

  const rN = radius(logN);
  const rSq = radius(logSq);
  const rSq1 = radius(logSq1);

  const firstPeakStep = figure.firstPeakStep;
  const lastPeakStep = figure.lastPeakStep;

  const decades: number[] = [];
  const span = hi - lo;
  /* keep decade labels at least ~22px apart along the radius */
  const stride = Math.max(1, Math.ceil((22 * span) / (R_MAX - R_MIN)));
  if (Number.isFinite(lo) && Number.isFinite(hi) && Number.isFinite(stride)) {
    for (let exp = Math.ceil(lo); exp <= Math.floor(hi) && decades.length < 24; exp += stride) {
      decades.push(exp);
    }
  }

  const height = compact ? HEIGHT - 14 : HEIGHT;
  const closed = figure.closed;
  const end = closed ? points[points.length - 1] : null;
  const start = points[0];

  return (
    <svg viewBox={`0 0 ${WIDTH} ${height}`} role="img" className="h-auto w-full">
      <title>Excursion necklace in polar coordinates: one turn is the word, radius is log value</title>

      {/* decade rings, labelled on the left */}
      {decades.map((exp) => {
        const r = radius(exp);
        const at = polar(r + 2, (-3 * Math.PI) / 4);
        return (
          <g key={exp}>
            <circle cx={CX} cy={CY} r={r} fill="none" stroke="#e8e2d4" strokeWidth="0.75" />
            <text
              x={at.x}
              y={at.y}
              textAnchor="end"
              fill={MUTED}
              fontFamily="IBM Plex Mono, monospace"
              fontSize="9"
              paintOrder="stroke"
              stroke="#fffdf7"
              strokeWidth="3"
            >
              <TenPow exp={exp} />
            </text>
          </g>
        );
      })}

      {/* below the minimum: not a cycle minimum any more */}
      <circle cx={CX} cy={CY} r={rN} fill={WARN} opacity="0.05" />

      {/* landing band [n², (n+1)²) as an annulus */}
      <path
        d={`M${CX + rSq1},${CY} A${rSq1},${rSq1} 0 1 0 ${CX - rSq1},${CY} A${rSq1},${rSq1} 0 1 0 ${CX + rSq1},${CY} Z M${CX + rSq},${CY} A${rSq},${rSq} 0 1 0 ${CX - rSq},${CY} A${rSq},${rSq} 0 1 0 ${CX + rSq},${CY} Z`}
        fill={EVEN}
        fillRule="evenodd"
        opacity="0.14"
      />
      <circle cx={CX} cy={CY} r={rSq1} fill="none" stroke={ODD} strokeWidth="1.2" strokeDasharray="5 4" />
      <circle cx={CX} cy={CY} r={rSq} fill="none" stroke={EVEN} strokeWidth="1.2" strokeDasharray="5 4" />
      <circle cx={CX} cy={CY} r={rN} fill="none" stroke={INK} strokeWidth="1.4" />

      {/* ring labels on the lower-right diagonal, haloed so the wave never hides them.
          At small n the band [n²,(n+1)²) is a sliver on the log scale; split the ray. */}
      {(() => {
        const tightBand = Math.abs(rSq1 - rSq) < 22;
        return [
          {
            r: rSq1,
            text: "(n+1)²",
            color: ODD,
            dy: tightBand ? -8 : -3,
            a: tightBand ? Math.PI / 4 - 0.38 : Math.PI / 4,
          },
          {
            r: rSq,
            text: "n² · landing band",
            color: EVEN,
            dy: tightBand ? 10 : 9,
            a: Math.PI / 4,
          },
          { r: rN, text: "n", color: INK, dy: 3, a: Math.PI / 4 },
        ].map((ring) => {
          const at = polar(ring.r + 3, ring.a);
          return (
            <text
              key={ring.text}
              x={at.x}
              y={at.y + ring.dy}
              fill={ring.color}
              fontSize="10"
              fontFamily="Source Sans 3, sans-serif"
              paintOrder="stroke"
              stroke="#fffdf7"
              strokeWidth="3"
            >
              {ring.text}
            </text>
          );
        });
      })()}

      {/* Word colors stay. A strike through O reads as θ; recoloring hides O⁷EEEE. */}
      {[...word].map((letter, index) => {
        const a = angle(index + 0.5);
        const { x, y } = polar(R_LETTERS, a);
        const tick = polar(R_LETTERS + 11, a);
        const realized = figure.realized[index];
        const mismatch = realized !== undefined && realized !== letter;
        const missing = realized === undefined;
        return (
          <g key={`letter-${index}`}>
            <text
              x={x}
              y={y}
              textAnchor="middle"
              dominantBaseline="central"
              fill={letter === "O" ? ODD : EVEN}
              opacity={missing ? 0.35 : 1}
              fontFamily="IBM Plex Mono, monospace"
              fontSize={word.length > 48 ? "8" : word.length > 24 ? "9" : "12"}
            >
              {letter}
            </text>
            {mismatch ? (
              <circle cx={tick.x} cy={tick.y} r="2.2" fill={WARN} />
            ) : null}
          </g>
        );
      })}
      {/* closure seam at the top */}
      <line
        x1={CX}
        y1={CY - R_LETTERS - 10}
        x2={CX}
        y2={CY - R_MIN + 6}
        stroke={MUTED}
        strokeWidth="0.8"
        strokeDasharray="2 3"
      />
      <text x={CX} y={CY - R_LETTERS - 14} textAnchor="middle" fill={MUTED} fontSize="9">
        cut · minimum first
      </text>

      {/* the wave */}
      {points.slice(0, -1).map((point, index) => {
        const next = points[index + 1];
        const odd = point.letter === "O";
        return (
          <line
            key={`seg-${index}`}
            x1={point.x}
            y1={point.y}
            x2={next.x}
            y2={next.y}
            stroke={next.below ? WARN : odd ? ODD : EVEN}
            strokeWidth="1.7"
            opacity={next.below ? 0.7 : 1}
          />
        );
      })}

      {/* the closure gap: J^L(n) against n at the same angle */}
      {end && !figure.returns ? (
        <line
          x1={start.x}
          y1={start.y}
          x2={end.x}
          y2={end.y}
          stroke={WARN}
          strokeWidth="1.4"
          strokeDasharray="3 3"
        />
      ) : null}

      {points.map((point, index) => {
        const odd = point.odd;
        const isFirstPeak = index === firstPeakStep;
        const isLastPeak = index === lastPeakStep;
        const isPeak = point.letter === "E";
        const isFail = figure.failIndex === index;
        const isEnd = closed && index === points.length - 1;
        const fill = point.below ? WARN : odd ? ODD : EVEN;
        const ring = isFirstPeak || isLastPeak || index === 0 || isEnd;
        const showLabel =
          !compact && (logs.length <= 14 || index === 0 || isFirstPeak || isLastPeak || isFail || isEnd);
        const out = polar(point.r + 13, point.a);
        return (
          <g key={index}>
            <circle
              cx={point.x}
              cy={point.y}
              r={ring ? 4.6 : isPeak ? 3.4 : 2.6}
              fill={isEnd && !figure.returns ? "#fffdf7" : fill}
              stroke={ring ? (isEnd && !figure.returns ? WARN : INK) : "none"}
              strokeWidth={ring ? 1.3 : 0}
            />
            {showLabel ? (
              <text
                x={out.x}
                y={out.y + 3}
                textAnchor={Math.cos(point.a) > 0.2 ? "start" : Math.cos(point.a) < -0.2 ? "end" : "middle"}
                fill={isFail ? WARN : INK}
                fontFamily="IBM Plex Mono, monospace"
                fontSize="10"
                paintOrder="stroke"
                stroke="#fffdf7"
                strokeWidth="3"
              >
                {point.label}
              </text>
            ) : null}
          </g>
        );
      })}

      {/* verdicts */}
      {!compact && firstPeakStep !== null ? (
        <text x={12} y={height - 44} fill={figure.firstPeakOvershoots ? OK : WARN} fontSize="11">
          first peak {figure.firstPeakOvershoots ? "clears (n+1)²" : "does not clear (n+1)²"}
        </text>
      ) : null}
      {!compact && lastPeakStep !== null && lastPeakStep !== firstPeakStep ? (
        <text x={12} y={height - 28} fill={figure.lastPeakLands ? OK : WARN} fontSize="11">
          last peak {figure.lastPeakLands ? "lands in the band" : "misses the band"}
        </text>
      ) : null}
      {!compact && figure.failIndex !== null ? (
        <text x={WIDTH - 12} y={height - 44} textAnchor="end" fill={WARN} fontSize="11">
          letter {figure.failIndex + 1}: word says {word[figure.failIndex]}, walk is {figure.realized[figure.failIndex] ?? "—"}
        </text>
      ) : null}
      <text x={12} y={height - 10} fill={MUTED} fontSize="11">
        {figure.belowMinimumIndex === null
          ? "the walk stays at or above n"
          : `step ${figure.belowMinimumIndex}: below n — this start is not a cycle minimum`}
      </text>
      <text x={WIDTH - 12} y={height - 10} textAnchor="end" fill={figure.returns ? OK : MUTED} fontSize="11">
        {figure.returns
          ? "closes: returns to n"
          : figure.imageLabel === null
            ? "walk stopped before the turn"
            : `does not close: J^${word.length}(n) = ${figure.imageLabel} ≠ n`}
      </text>
    </svg>
  );
}

const SLOT_SUB = "₁₂₃₄₅₆₇₈₉";

function slotName(block: NecklaceFigure["tiles"][number]): string {
  if (block.index === 0) return "a₁";
  if (block.last && block.complete) return "aₑ";
  const n = block.index + 1;
  return n <= 9 ? `a${SLOT_SUB[n - 1]}` : `a${n}`;
}

function BlockWord({ block }: { block: NecklaceFigure["tiles"][number] }) {
  const close = block.complete ? (
    <span style={{ color: EVEN }}>E</span>
  ) : (
    <span className="text-muted">…</span>
  );
  if (block.odds === 0) return close;
  return (
    <>
      <span style={{ color: ODD }}>
        O
        {block.odds > 1 ? <sup>{block.odds}</sup> : null}
      </span>
      {close}
    </>
  );
}

function regimeWord(regime: NecklaceFigure["tiles"][number]["regime"]): string {
  if (regime === "expanding") return "expands";
  if (regime === "contracting") return "contracts";
  return "critical";
}

/** One row per block O^{a_i}E: slot, μ(a_i), and valley → peak. */
export function ExcursionTiles({ figure }: { figure: NecklaceFigure }) {
  if (figure.tiles.length === 0) {
    return <p className="text-sm text-muted">No step yet: a necklace needs at least one E.</p>;
  }
  return (
    <div className="max-h-80 overflow-auto rounded-xl border border-line bg-card">
      <table className="w-full min-w-[28rem] text-left text-sm">
        <thead className="sticky top-0 border-b border-line bg-card text-muted">
          <tr>
            <th className="px-3 py-2 font-medium">slot</th>
            <th className="px-3 py-2 font-medium">block</th>
            <th className="px-3 py-2 font-medium">μ(a)</th>
            <th className="px-3 py-2 font-medium">valley</th>
            <th className="px-3 py-2 font-medium">peak</th>
          </tr>
        </thead>
        <tbody>
          {figure.tiles.map((block) => {
            const color = block.regime === "expanding" ? ODD : block.regime === "contracting" ? EVEN : MUTED;
            return (
              <tr
                key={block.index}
                className={`border-b border-line/70 last:border-0 ${block.complete ? "" : "opacity-70"}`}
              >
                <td className="px-3 py-1.5 font-mono">
                  {slotName(block)}
                  {block.index === 0 ? <span className="text-muted"> · launch</span> : null}
                </td>
                <td className="px-3 py-1.5 font-mono">
                  <BlockWord block={block} />
                </td>
                <td className="px-3 py-1.5 font-mono" style={{ color }}>
                  {block.mu} {regimeWord(block.regime)}
                </td>
                <td className="px-3 py-1.5 font-mono">{block.valley}</td>
                <td className="px-3 py-1.5 font-mono">{block.peak ?? "…"}</td>
              </tr>
            );
          })}
        </tbody>
      </table>
    </div>
  );
}
