import type { Excursion, NecklaceView } from "../juggler/necklace";
import { formatInt, log10Of } from "../juggler/format";

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
  view: NecklaceView;
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
export function ExcursionWave({ view, compact = false }: ExcursionWaveProps) {
  const { states, n, nSquared, nPlusOneSquared, word } = view;
  const turn = Math.max(word.length, 1);
  const logs = states.map(log10Of);
  const logN = log10Of(n);
  const logSq = log10Of(nSquared);
  const logSq1 = log10Of(nPlusOneSquared);
  const dataLo = Math.min(...logs, logN);
  const dataHi = Math.max(...logs, logSq1);
  const pad = Math.max(0.35, (dataHi - dataLo) * 0.08);
  const lo = Math.max(0, dataLo - pad);
  const hi = dataHi + pad;

  const radius = (log10v: number) =>
    hi === lo ? (R_MIN + R_MAX) / 2 : R_MIN + ((log10v - lo) / (hi - lo)) * (R_MAX - R_MIN);
  const angle = (step: number) => -Math.PI / 2 + (2 * Math.PI * step) / turn;
  const polar = (r: number, a: number) => ({ x: CX + r * Math.cos(a), y: CY + r * Math.sin(a) });

  const points = states.map((state, index) => {
    const { x, y } = polar(radius(logs[index]), angle(index));
    return { x, y, state, letter: view.realized[index] ?? null, below: state < n, r: radius(logs[index]), a: angle(index) };
  });

  const rN = radius(logN);
  const rSq = radius(logSq);
  const rSq1 = radius(logSq1);

  const complete = view.excursions.filter((block) => block.complete);
  const firstPeakStep = complete[0] ? complete[0].states.length - 1 : null;
  const lastPeakStep =
    complete.length > 0
      ? view.excursions.slice(0, complete.length).reduce((sum, block) => sum + block.states.length, 0) - 1
      : null;

  const decades: number[] = [];
  const span = hi - lo;
  /* keep decade labels at least ~22px apart along the radius */
  const stride = Math.max(1, Math.ceil((22 * span) / (R_MAX - R_MIN)));
  for (let exp = Math.ceil(lo); exp <= Math.floor(hi); exp += stride) decades.push(exp);

  const height = compact ? HEIGHT - 14 : HEIGHT;
  const closed = states.length === word.length + 1;
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

      {/* ring labels on the lower-right diagonal, haloed so the wave never hides them */}
      {[
        { r: rSq1, text: "(n+1)²", color: ODD, dy: -3 },
        { r: rSq, text: "n² · landing band", color: EVEN, dy: 9 },
        { r: rN, text: "n", color: INK, dy: 3 },
      ].map((ring) => {
        const at = polar(ring.r + 3, Math.PI / 4);
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
      })}

      {/* the itinerary as a ring of letters */}
      {[...word].map((letter, index) => {
        const { x, y } = polar(R_LETTERS, angle(index + 0.5));
        const realized = view.realized[index];
        const mismatch = realized !== undefined && realized !== letter;
        const missing = realized === undefined;
        return (
          <text
            key={`letter-${index}`}
            x={x}
            y={y + 3.5}
            textAnchor="middle"
            fill={mismatch ? WARN : letter === "O" ? ODD : EVEN}
            opacity={missing ? 0.35 : 1}
            fontFamily="IBM Plex Mono, monospace"
            fontSize={word.length > 24 ? "9" : "11"}
            fontWeight={mismatch ? 700 : 400}
            textDecoration={mismatch ? "line-through" : "none"}
          >
            {letter}
          </text>
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
            strokeWidth="2.4"
            opacity={next.below ? 0.7 : 1}
          />
        );
      })}

      {/* the closure gap: J^L(n) against n at the same angle */}
      {end && !view.returns ? (
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
        const odd = point.state % 2n === 1n;
        const isFirstPeak = index === firstPeakStep;
        const isLastPeak = index === lastPeakStep;
        const isPeak = point.letter === "E";
        const isFail = view.failIndex === index;
        const isEnd = closed && index === points.length - 1;
        const fill = point.below ? WARN : odd ? ODD : EVEN;
        const ring = isFirstPeak || isLastPeak || index === 0 || isEnd;
        const showLabel =
          !compact && (states.length <= 14 || index === 0 || isFirstPeak || isLastPeak || isFail || isEnd);
        const out = polar(point.r + 13, point.a);
        return (
          <g key={index}>
            <circle
              cx={point.x}
              cy={point.y}
              r={ring ? 7 : isPeak ? 5.5 : 4.5}
              fill={isEnd && !view.returns ? "#fffdf7" : fill}
              stroke={ring ? (isEnd && !view.returns ? WARN : INK) : "none"}
              strokeWidth={ring ? 1.8 : 0}
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
                {formatInt(point.state)}
              </text>
            ) : null}
          </g>
        );
      })}

      {/* verdicts */}
      {!compact && firstPeakStep !== null ? (
        <text x={12} y={height - 44} fill={view.firstPeakOvershoots ? OK : WARN} fontSize="11">
          first peak {view.firstPeakOvershoots ? "clears (n+1)²" : "does not clear (n+1)²"}
        </text>
      ) : null}
      {!compact && lastPeakStep !== null && lastPeakStep !== firstPeakStep ? (
        <text x={12} y={height - 28} fill={view.lastPeakLands ? OK : WARN} fontSize="11">
          last peak {view.lastPeakLands ? "lands in the band" : "misses the band"}
        </text>
      ) : null}
      {!compact && view.failIndex !== null ? (
        <text x={WIDTH - 12} y={height - 44} textAnchor="end" fill={WARN} fontSize="11">
          letter {view.failIndex + 1}: word says {word[view.failIndex]}, walk is {view.realized[view.failIndex] ?? "—"}
        </text>
      ) : null}
      <text x={12} y={height - 10} fill={MUTED} fontSize="11">
        {view.belowMinimumIndex === null
          ? "the walk stays at or above n"
          : `step ${view.belowMinimumIndex}: below n — this start is not a cycle minimum`}
      </text>
      <text x={WIDTH - 12} y={height - 10} textAnchor="end" fill={view.returns ? OK : MUTED} fontSize="11">
        {view.returns
          ? "closes: returns to n"
          : view.image === null
            ? "walk stopped before the turn"
            : `does not close: J^${word.length}(n) = ${formatInt(view.image)} ≠ n`}
      </text>
    </svg>
  );
}

function Tile({ letter }: { letter: "O" | "E" }) {
  return (
    <span
      className="inline-flex h-6 min-w-6 items-center justify-center rounded-md font-mono text-xs text-card"
      style={{ background: letter === "O" ? ODD : EVEN }}
    >
      {letter}
    </span>
  );
}

function regimeWord(block: Excursion): string {
  if (block.mu.regime === "expanding") return "expands";
  if (block.mu.regime === "contracting") return "contracts";
  return "critical";
}

/** One tile per block O^{a_i}E: its ideal exponent μ(a_i) and its valley → peak. */
export function ExcursionTiles({ view }: { view: NecklaceView }) {
  if (view.excursions.length === 0) {
    return <p className="text-sm text-muted">No step yet: a necklace needs at least one E.</p>;
  }
  return (
    <div className="flex flex-wrap items-stretch gap-2">
      {view.excursions.map((block) => {
        const last = block.index === view.excursions.length - 1;
        const oddsShown = Math.min(block.odds, 5);
        const color = block.mu.regime === "expanding" ? ODD : block.mu.regime === "contracting" ? EVEN : MUTED;
        return (
          <div
            key={block.index}
            className={`grid min-w-[7.5rem] content-start gap-1 rounded-lg border border-line bg-card px-2 py-1.5 ${
              block.complete ? "" : "border-dashed opacity-70"
            }`}
          >
            <span className="flex items-center gap-0.5">
              {block.odds === 0 ? (
                <span className="inline-flex h-6 w-3 items-center justify-center font-mono text-xs text-muted">
                  ·
                </span>
              ) : (
                Array.from({ length: oddsShown }, (_, index) => <Tile key={index} letter="O" />)
              )}
              {block.odds > oddsShown ? (
                <span className="font-mono text-xs text-muted">×{block.odds}</span>
              ) : null}
              {block.complete ? <Tile letter="E" /> : <span className="font-mono text-xs text-muted">…</span>}
            </span>
            <span className="font-mono text-xs" style={{ color }}>
              μ({block.odds}) = {block.mu.num.toString()}/{block.mu.den.toString()} · {regimeWord(block)}
            </span>
            <span className="font-mono text-[11px] text-muted">
              {formatInt(block.valley)} → {block.peak === null ? "…" : formatInt(block.peak)}
            </span>
            <span className="text-[10px] uppercase tracking-wide text-muted">
              {block.index === 0 ? "launch a₁" : last && block.complete ? "last aₑ" : `a${block.index + 1}`}
            </span>
          </div>
        );
      })}
    </div>
  );
}
