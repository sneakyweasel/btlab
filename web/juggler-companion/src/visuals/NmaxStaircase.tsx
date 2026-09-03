import { useState } from "react";
import { PAPER_FLOOR, PAPER_L_CAP, PAPER_PERIOD } from "../juggler/constants";
import { financeLattice, financeSnapshot, financeSurvivors, type FinanceSurvivor } from "../juggler/finance";
import { formatGrouped } from "../juggler/format";

const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const DEEP = "#1f3d34";
const INK = "#1d1914";
const MUTED = "#5e574c";
const LINE = "#d4cbb8";
const GRID = "#e8e2d4";
const DEAD = "#a89f8e";

const WIDTH = 720;
const HEIGHT = 300;
const TOP = 30;
const BOTTOM = 240;

/* left panel: log–log staircase */
const L_LEFT = 54;
const L_RIGHT = 290;
/* right panel: linear comb over the survivor window */
const R_LEFT = 350;
const R_RIGHT = 700;

const COMB_LO = 24_000;
const COMB_HI = 101_000;
const COMB_Y_LO = 5.85;
const COMB_Y_HI = 8.35;

function sliceColor(row: FinanceSurvivor): string {
  if (row.packingDeath) return DEAD;
  if (row.a === 1) return ODD;
  if (row.a === 2) return EVEN;
  return DEEP;
}

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

type NmaxStaircaseProps = {
  /** Length highlighted in both panels (the balance's L). */
  selected?: number;
  onSelect?: (length: number) => void;
  compact?: boolean;
};

/**
 * Left: the record values of the parity n_max(L) as a staircase on
 * log–log axes, with the floor 10^6 as the line it must clear. Right: the
 * 141 finance survivors on [25781, 100000] with their n_max, coloured by
 * the Proposition 4.9 lattice slice; the 42 run-packing deaths are grey.
 * Every number is shipped from finance.json.
 */
export function NmaxStaircase({ selected, onSelect, compact = false }: NmaxStaircaseProps) {
  const [hover, setHover] = useState<FinanceSurvivor | null>(null);
  const records = financeSnapshot.records;

  const xLog = (length: number) =>
    L_LEFT + (Math.log10(Math.max(length, 1)) / Math.log10(PAPER_L_CAP)) * (L_RIGHT - L_LEFT);
  const yLog = (value: number) => {
    const lo = 0;
    const hi = 8.6;
    return BOTTOM - ((Math.log10(Math.max(value, 1)) - lo) / (hi - lo)) * (BOTTOM - TOP);
  };
  const xLin = (length: number) => R_LEFT + ((length - COMB_LO) / (COMB_HI - COMB_LO)) * (R_RIGHT - R_LEFT);
  const yComb = (value: number) =>
    BOTTOM - ((Math.log10(value) - COMB_Y_LO) / (COMB_Y_HI - COMB_Y_LO)) * (BOTTOM - TOP);

  const stairs: string[] = [];
  records.forEach((row, index) => {
    const x = xLog(row.L);
    const y = yLog(row.nMax);
    if (index === 0) stairs.push(`M${x.toFixed(1)},${BOTTOM} L${x.toFixed(1)},${y.toFixed(1)}`);
    else {
      const prevY = yLog(records[index - 1].nMax);
      stairs.push(`L${x.toFixed(1)},${prevY.toFixed(1)} L${x.toFixed(1)},${y.toFixed(1)}`);
    }
  });
  const last = records[records.length - 1];
  stairs.push(`L${xLog(PAPER_L_CAP).toFixed(1)},${yLog(last.nMax).toFixed(1)}`);

  const floorYLog = yLog(PAPER_FLOOR);
  const floorYComb = yComb(PAPER_FLOOR);
  const shown = hover ?? (selected === undefined ? null : financeSurvivors.find((row) => row.L === selected) ?? null);

  return (
    <div className="space-y-2">
      <svg viewBox={`0 0 ${WIDTH} ${HEIGHT}`} role="img" className="h-auto w-full" onMouseLeave={() => setHover(null)}>
        <title>Record parity n_max(L) staircase against the floor, and the 141 survivors with their lattice slice</title>

        {/* ----- left panel ----- */}
        {[0, 2, 4, 6, 8].map((exp) => (
          <g key={`ly${exp}`}>
            <line x1={L_LEFT} y1={yLog(10 ** exp)} x2={L_RIGHT} y2={yLog(10 ** exp)} stroke={GRID} strokeWidth="0.75" />
            <text x={L_LEFT - 6} y={yLog(10 ** exp) + 3} textAnchor="end" fill={MUTED} fontFamily="IBM Plex Mono, monospace" fontSize="10">
              <TenPow exp={exp} />
            </text>
          </g>
        ))}
        {[1, 2, 3, 4, 5].map((exp) => (
          <text key={`lx${exp}`} x={xLog(10 ** exp)} y={BOTTOM + 15} textAnchor="middle" fill={MUTED} fontFamily="IBM Plex Mono, monospace" fontSize="10">
            <TenPow exp={exp} />
          </text>
        ))}
        <line x1={L_LEFT} y1={TOP} x2={L_LEFT} y2={BOTTOM} stroke={LINE} />
        <line x1={L_LEFT} y1={BOTTOM} x2={L_RIGHT} y2={BOTTOM} stroke={LINE} />
        <text x={L_LEFT} y={TOP - 12} fill={INK} fontFamily="Fraunces, serif" fontSize="13">
          record n_max(L)
        </text>
        <text x={L_RIGHT} y={BOTTOM + 30} textAnchor="end" fill={MUTED} fontSize="11">
          period L
        </text>

        <rect x={L_LEFT} y={TOP} width={L_RIGHT - L_LEFT} height={Math.max(0, floorYLog - TOP)} fill={EVEN} opacity="0.05" />
        <line x1={L_LEFT} y1={floorYLog} x2={L_RIGHT} y2={floorYLog} stroke={INK} strokeWidth="1.2" strokeDasharray="4 3" />
        <text x={L_LEFT + 4} y={floorYLog - 4} fill={INK} fontSize="10">
          N₀ = 10⁶ — below this line the length is dead
        </text>

        <path d={stairs.join(" ")} fill="none" stroke={DEEP} strokeWidth="2.2" />
        {records.map((row) => {
          const isCut = row.L === PAPER_PERIOD;
          const isSel = row.L === selected;
          return (
            <g key={row.L}>
              <circle
                cx={xLog(row.L)}
                cy={yLog(row.nMax)}
                r={isCut || isSel ? 6 : 4}
                fill={row.nMax > PAPER_FLOOR ? ODD : DEEP}
                stroke={isSel ? INK : "#fffdf7"}
                strokeWidth={isSel ? 2 : 1.2}
                style={{ cursor: onSelect ? "pointer" : "default" }}
                onClick={() => onSelect?.(row.L)}
              >
                <title>{`L = ${formatGrouped(row.L)}, o_min = ${formatGrouped(row.o)}, n_max = ${formatGrouped(row.nMax)}`}</title>
              </circle>
              {isCut ? (
                <text x={xLog(row.L) - 8} y={yLog(row.nMax) - 10} textAnchor="end" fill={ODD} fontSize="10" fontFamily="IBM Plex Mono, monospace">
                  25781 clears the floor
                </text>
              ) : null}
            </g>
          );
        })}

        {/* ----- right panel ----- */}
        {[6, 7, 8].map((exp) => (
          <g key={`ry${exp}`}>
            <line x1={R_LEFT} y1={yComb(10 ** exp)} x2={R_RIGHT} y2={yComb(10 ** exp)} stroke={GRID} strokeWidth="0.75" />
            <text x={R_LEFT - 6} y={yComb(10 ** exp) + 3} textAnchor="end" fill={MUTED} fontFamily="IBM Plex Mono, monospace" fontSize="10">
              <TenPow exp={exp} />
            </text>
          </g>
        ))}
        {[25_781, 50_508, 76_289, 100_000].map((length) => (
          <text key={`rx${length}`} x={xLin(length)} y={BOTTOM + 15} textAnchor="middle" fill={MUTED} fontFamily="IBM Plex Mono, monospace" fontSize="10">
            {formatGrouped(length)}
          </text>
        ))}
        <line x1={R_LEFT} y1={TOP} x2={R_LEFT} y2={BOTTOM} stroke={LINE} />
        <line x1={R_LEFT} y1={BOTTOM} x2={R_RIGHT} y2={BOTTOM} stroke={LINE} />
        <text x={R_LEFT} y={TOP - 12} fill={INK} fontFamily="Fraunces, serif" fontSize="13">
          the {financeSurvivors.length} survivors at 10⁶
        </text>
        <line x1={R_LEFT} y1={floorYComb} x2={R_RIGHT} y2={floorYComb} stroke={INK} strokeWidth="1.2" strokeDasharray="4 3" />

        {financeSurvivors.map((row) => {
          const isSel = row.L === selected;
          const isHover = hover?.L === row.L;
          return (
            <circle
              key={row.L}
              cx={xLin(row.L)}
              cy={yComb(row.nMax)}
              r={isSel || isHover ? 5.5 : 3.2}
              fill={row.packingDeath ? "#fffdf7" : sliceColor(row)}
              stroke={isSel ? INK : row.packingDeath ? DEAD : "none"}
              strokeWidth={isSel ? 2 : 1.2}
              style={{ cursor: onSelect ? "pointer" : "default" }}
              onMouseEnter={() => setHover(row)}
              onClick={() => onSelect?.(row.L)}
            >
              <title>{`L = ${formatGrouped(row.L)}, o_min = ${formatGrouped(row.o)}, n_max = ${formatGrouped(row.nMax)}, (a, b) = (${row.a}, ${row.b})${row.packingDeath ? ", run-packing death" : ""}`}</title>
            </circle>
          );
        })}

        {/* legend */}
        <g fontSize="10" fill={MUTED} fontFamily="Source Sans 3, sans-serif">
          <circle cx={R_LEFT + 6} cy={HEIGHT - 12} r="3.2" fill={ODD} />
          <text x={R_LEFT + 13} y={HEIGHT - 9}>a = 1</text>
          <circle cx={R_LEFT + 56} cy={HEIGHT - 12} r="3.2" fill={EVEN} />
          <text x={R_LEFT + 63} y={HEIGHT - 9}>a = 2</text>
          <circle cx={R_LEFT + 106} cy={HEIGHT - 12} r="3.2" fill={DEEP} />
          <text x={R_LEFT + 113} y={HEIGHT - 9}>a = 3</text>
          <circle cx={R_LEFT + 158} cy={HEIGHT - 12} r="3.2" fill="#fffdf7" stroke={DEAD} strokeWidth="1.2" />
          <text x={R_LEFT + 165} y={HEIGHT - 9}>run-packing death (Thm 4.8)</text>
        </g>
        <text x={L_LEFT} y={HEIGHT - 9} fill={MUTED} fontSize="10">
          (L, o) = a·(25781, 16266) + b·(1054, 665)
        </text>
      </svg>

      {compact ? null : (
        <p className="min-h-[1.5rem] font-mono text-xs text-muted">
          {shown
            ? `L = ${formatGrouped(shown.L)} · o_min = ${formatGrouped(shown.o)} · n_max = ${formatGrouped(shown.nMax)} · (a, b) = (${shown.a}, ${shown.b})${
                shown.packingDeath ? " · killed by run-type packing (Theorem 4.8)" : " · finance survivor — not a cycle"
              }`
            : `hover or click a survivor · slices ${financeLattice.sliceCounts.join(" / ")} · ${financeLattice.packingDeaths} packing deaths leave ${financeLattice.runSurvivors}`}
        </p>
      )}
    </div>
  );
}
