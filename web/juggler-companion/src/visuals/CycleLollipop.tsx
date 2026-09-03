import { memo, useCallback, type KeyboardEvent, type MouseEvent, type ReactNode } from "react";
import type { DecisionFocus } from "../content/idealDecisions";
import {
  IDEAL_BALLOON_BEADS,
  IDEAL_BALLOON_INTERVALS,
  idealJoinSpots,
  intervalCountBead,
  intervalIsMass,
  intervalSlotName,
  stepIdealJoin,
  type BalloonInterval,
  type IdealBead,
} from "../juggler/constants";
import {
  JOIN_INTERVALS_NOT_STOPS,
  JOIN_VS_WORD_ROTATION,
  idealJoinConfig,
} from "../juggler/joinConfig";
import {
  joinFigure,
  paintStem,
  siteAtIndex,
  type FigureMark,
  type PaintedBead,
  type StemDisplayMode,
} from "../juggler/lollipop";

const STATIONS = 10;
const BEAD_R = 13;
const STEP = 42;
const R = STEP / (2 * Math.sin(Math.PI / STATIONS));
const STEM_STEP = STEP;
const JOIN_ANGLE = Math.PI / 2;
const PAD_TOP = 28;
const CX = 180;
const CY = PAD_TOP + BEAD_R + R;
const JOIN_Y = CY + R;
const VIEW_W = 360;
const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const GREY = "#8a8378";
const INK = "#4a453e";
const BAND_HALF = 6.5;
const BALLOON = IDEAL_BALLOON_BEADS;
const N = BALLOON.length;
const JOIN_SPOTS = idealJoinSpots(BALLOON);

function letterColor(letter: IdealBead["letter"]): string {
  if (letter === "O") return ODD;
  if (letter === "E") return EVEN;
  return GREY;
}

function sureSlot(sureIndex: number): number {
  return sureIndex <= 1 ? sureIndex : 2 * sureIndex - 1;
}

function stationAngle(slot: number, joinAt = 0): number {
  return ((slot - sureSlot(joinAt)) / STATIONS) * 2 * Math.PI + JOIN_ANGLE;
}

function beadAngle(index: number, joinAt = 0): number {
  return stationAngle(sureSlot(index), joinAt);
}

function atAngle(angle: number, radius: number, dy = 0): { x: number; y: number } {
  return { x: CX + radius * Math.cos(angle), y: CY + radius * Math.sin(angle) + dy };
}

function arcSweep(a0: number, a1: number): number {
  return (a1 - a0 + 2 * Math.PI) % (2 * Math.PI);
}

function pointedArcPath(a0: number, a1: number, rim0 = BEAD_R + 0.4, rim1 = BEAD_R + 0.4): string {
  const sweep = arcSweep(a0, a1);
  const startPad = Math.asin(Math.min(1, rim0 / R));
  const endPad = Math.asin(Math.min(1, rim1 / R));
  const start = a0 + startPad;
  const span = sweep - startPad - endPad;
  const steps = 10;
  const halfW = 2.7;
  const outer: string[] = [];
  const inner: string[] = [];
  for (let i = 0; i <= steps; i += 1) {
    const t = i / steps;
    const ang = start + span * t;
    const w = halfW * (1 - t);
    const o = atAngle(ang, R + w);
    const n = atAngle(ang, R - w);
    outer.push(`${o.x} ${o.y}`);
    inner.push(`${n.x} ${n.y}`);
  }
  return `M ${outer.join(" L ")} L ${inner.reverse().join(" L ")} Z`;
}

function annularSector(a0: number, a1: number, inner: number, outer: number): string {
  const sweep = arcSweep(a0, a1);
  const rim = Math.asin(Math.min(1, (BEAD_R + 1.5) / R));
  const start = a0 + rim;
  const span = sweep - 2 * rim;
  if (span < 0.06) return "";
  const end = start + span;
  const large = span > Math.PI ? 1 : 0;
  const o0 = atAngle(start, outer);
  const o1 = atAngle(end, outer);
  const i1 = atAngle(end, inner);
  const i0 = atAngle(start, inner);
  return `M ${o0.x} ${o0.y} A ${outer} ${outer} 0 ${large} 1 ${o1.x} ${o1.y} L ${i1.x} ${i1.y} A ${inner} ${inner} 0 ${large} 0 ${i0.x} ${i0.y} Z`;
}

function pointedSegPath(x0: number, y0: number, x1: number, y1: number): string {
  const dx = x1 - x0;
  const dy = y1 - y0;
  const len = Math.hypot(dx, dy);
  if (len < 2) return "";
  const ux = dx / len;
  const uy = dy / len;
  const px = -uy;
  const py = ux;
  const rim = BEAD_R + 0.4;
  const start = Math.min(rim, len / 2);
  const end = Math.max(len - rim, start + 1);
  const span = end - start;
  const halfW = 2.7;
  const steps = 8;
  const left: string[] = [];
  const right: string[] = [];
  for (let i = 0; i <= steps; i += 1) {
    const t = i / steps;
    const s = start + span * t;
    const w = halfW * (1 - t);
    const mx = x0 + ux * s;
    const my = y0 + uy * s;
    left.push(`${mx + px * w} ${my + py * w}`);
    right.push(`${mx - px * w} ${my - py * w}`);
  }
  return `M ${left.join(" L ")} L ${right.reverse().join(" L ")} Z`;
}

function intervalAngle(afterBead: number, joinAt = 0): number {
  return stationAngle(sureSlot(afterBead) + 1, joinAt);
}

function beadMark(bead: IdealBead | PaintedBead): FigureMark | undefined {
  return "mark" in bead ? bead.mark : undefined;
}

function beadPaint(bead: IdealBead | PaintedBead): {
  fill: string;
  stroke: string;
  dash?: string;
  text: string;
} {
  const mark = beadMark(bead);
  if (mark === "optional" || mark === "offFigure") {
    const fill = letterColor(bead.letter);
    return { fill: "#fffdf7", stroke: fill, dash: "4 3", text: fill };
  }
  if (bead.tone === "unknown" || mark === "unknown") {
    return { fill: "#fffdf7", stroke: GREY, dash: "3 2", text: GREY };
  }
  const fill = bead.letter === "O" ? ODD : EVEN;
  if (bead.tone === "count" || mark === "leftover") {
    return { fill: "#fffdf7", stroke: fill, dash: "3 2", text: fill };
  }
  return { fill, stroke: "none", text: "#fffdf7" };
}

function intervalBoundCaption(interval: BalloonInterval): string {
  if (interval.max === null) return "≥0";
  if (interval.kind === "lastZeroOrOne") return "≤1";
  return `{${interval.min},${interval.max}}`;
}

function regionLit(focus: DecisionFocus | undefined, region: DecisionFocus): boolean {
  if (!focus || focus === "figure") return true;
  if (focus === "none") return false;
  if (focus === region) return true;
  if (focus === "string" && region.startsWith("string")) return true;
  if (focus === "balloon" && region.startsWith("balloon")) return true;
  if (focus === "join" && (region === "join" || region === "string-e")) return true;
  if (focus === "balloon-e" && region === "balloon-first-e") return true;
  return false;
}

function fadeClass(lit: boolean): string | undefined {
  return lit ? undefined : "stem-cycle-dim";
}

function stemRegion(index: number, last: number): DecisionFocus {
  if (index <= 1) return "string-oo";
  if (index === last) return "string-e";
  return "string-grey";
}

function balloonRegion(index: number, bead: IdealBead): DecisionFocus {
  const firstSureEven = BALLOON.findIndex(
    (item) => item.letter === "E" && item.tone === "sure",
  );
  if (index <= 1) return "balloon-oo";
  if (index === N - 1) return "balloon-seam";
  if (index === firstSureEven) return "balloon-first-e";
  if (bead.letter === "E" && bead.tone === "sure") return "balloon-e";
  return "balloon";
}

function intervalRegion(interval: BalloonInterval): DecisionFocus {
  if (interval.kind === "lastZeroOrOne") return "balloon-seam";
  if (interval.kind === "extraEven") return "balloon-e";
  return "balloon-fade";
}

function intervalDecision(interval: BalloonInterval): string {
  if (interval.kind === "lastZeroOrOne") return "balloon-seam";
  if (interval.kind === "extraEven") return "balloon-evens";
  return "balloon-fade";
}

function balloonDecision(region: DecisionFocus): string {
  if (region === "balloon-oo") return "balloon-oo";
  if (region === "balloon-first-e") return "balloon-overshoot";
  if (region === "balloon-e") return "balloon-evens";
  if (region === "balloon-seam") return "balloon-seam";
  if (region === "balloon-fade") return "balloon-fade";
  return "balloon-cut";
}

function stemDecision(region: DecisionFocus): string {
  if (region === "string-oo") return "string-oo";
  if (region === "string-e") return "string-e";
  return "string-grey";
}

type StemItem = {
  x: number;
  y: number;
  bead: IdealBead | PaintedBead;
  region: DecisionFocus;
  caption?: string;
};

function stemBoundCaption(bead: PaintedBead): string | undefined {
  return bead.caption === "≥0" ? "≥0" : undefined;
}

function stemItemsFromPainted(beads: readonly PaintedBead[]): StemItem[] {
  const last = beads.length - 1;
  return beads.map((bead, index) => ({
    x: CX,
    y: JOIN_Y + (beads.length - index) * STEM_STEP,
    bead,
    region:
      bead.mark === "optional"
        ? "string-oo"
        : index === last
          ? "string-e"
          : stemRegion(index, last),
    caption: stemBoundCaption(bead),
  }));
}

function stemForJoin(joinAt: number, mode: StemDisplayMode): StemItem[] {
  return stemItemsFromPainted(paintStem(mode, joinFigure(siteAtIndex(joinAt), joinAt)));
}

type ArcSeg = {
  key: string;
  color: string;
  hollow: boolean;
  region: DecisionFocus;
  pointed: string;
};

function stationLetter(slot: number): IdealBead["letter"] {
  if (slot === 0 || slot === 1) return "O";
  const interval = intervalAtSlot(slot);
  if (interval) return intervalCountBead(interval).letter;
  return "E";
}

function slotRim(_slot: number): number {
  return BEAD_R + 0.4;
}

function hopTouchesMass(slot: number, next: number): boolean {
  const here = intervalAtSlot(slot);
  const nxt = intervalAtSlot(next);
  return Boolean((here && intervalIsMass(here)) || (nxt && intervalIsMass(nxt)));
}

function arcColor(slot: number): string {
  return letterColor(stationLetter(slot));
}

function intervalAtSlot(slot: number): BalloonInterval | undefined {
  return IDEAL_BALLOON_INTERVALS.find(
    (item) => sureSlot(item.afterBead) + 1 === slot,
  );
}

function arcRegion(slot: number): DecisionFocus {
  const here = intervalAtSlot(slot);
  if (here) return intervalRegion(here);
  const next = intervalAtSlot((slot + 1) % STATIONS);
  if (next) return intervalRegion(next);
  if (slot === 0) return "balloon-oo";
  return "balloon-seam";
}

function balloonArcs(joinAt: number): ArcSeg[] {
  return Array.from({ length: STATIONS }, (_, slot) => {
    const next = (slot + 1) % STATIONS;
    if (hopTouchesMass(slot, next)) return null;
    const a0 = stationAngle(slot, joinAt);
    const a1 = stationAngle(next, joinAt);
    const hollow = Boolean(intervalAtSlot(slot) || intervalAtSlot(next));
    return {
      key: `arc-${slot}`,
      color: arcColor(slot),
      hollow,
      region: arcRegion(slot),
      pointed: pointedArcPath(a0, a1, slotRim(slot), slotRim(next)),
    };
  }).filter((arc): arc is ArcSeg => arc !== null);
}

type FigureNode = {
  key: string;
  x: number;
  y: number;
  bead: IdealBead;
  radius: number;
  glyph?: string;
  caption?: string;
  name?: string;
  captionX?: number;
  captionY?: number;
  region: DecisionFocus;
  decision: string;
  marked?: boolean;
  index?: number;
};

function balloonNodes(joinAt: number): FigureNode[] {
  return BALLOON.map((bead, index) => {
    const angle = beadAngle(index, joinAt);
    const { x, y } = atAngle(angle, R);
    const region = balloonRegion(index, bead);
    return {
      key: `balloon-${index}`,
      x,
      y,
      bead,
      radius: BEAD_R,
      region,
      decision: index === 0 ? "balloon-cut" : balloonDecision(region),
      marked: index === 0,
      index,
    };
  });
}

function letterIntervalNodes(joinAt: number): FigureNode[] {
  return IDEAL_BALLOON_INTERVALS.filter((interval) => !intervalIsMass(interval)).map(
    (interval) => {
      const angle = intervalAngle(interval.afterBead, joinAt);
      const { x, y } = atAngle(angle, R);
      const label = atAngle(angle, R + BEAD_R + 22);
      const region = intervalRegion(interval);
      return {
        key: `interval-${interval.kind}`,
        x,
        y,
        bead: intervalCountBead(interval),
        radius: BEAD_R,
        name: intervalSlotName(interval),
        caption: intervalBoundCaption(interval),
        captionX: label.x,
        captionY: label.y + 3,
        region,
        decision: intervalDecision(interval),
      };
    },
  );
}

type MassBand = {
  key: string;
  path: string;
  rim: string;
  continuesOO: boolean;
  name: string;
  bound: string;
  captionX: number;
  captionY: number;
  region: DecisionFocus;
  decision: string;
};

function massBands(joinAt: number): MassBand[] {
  return IDEAL_BALLOON_INTERVALS.filter(intervalIsMass).map((interval) => {
    const a0 = beadAngle(interval.afterBead, joinAt);
    const a1 = beadAngle(interval.afterBead + 1, joinAt);
    const mid = a0 + arcSweep(a0, a1) / 2;
    const label = atAngle(mid, R + BAND_HALF + 22);
    const continuesOO = interval.kind === "a1Extras";
    return {
      key: `mass-${interval.kind}`,
      path: annularSector(a0, a1, R - BAND_HALF, R + BAND_HALF),
      rim: continuesOO ? ODD : INK,
      continuesOO,
      name: intervalSlotName(interval),
      bound: intervalBoundCaption(interval),
      captionX: label.x,
      captionY: label.y + 3,
      region: intervalRegion(interval),
      decision: intervalDecision(interval),
    };
  });
}

type CycleFigure = {
  arcs: ArcSeg[];
  nodes: FigureNode[];
  intervals: FigureNode[];
  bands: MassBand[];
};

function cycleFigure(joinAt: number): CycleFigure {
  return {
    arcs: balloonArcs(joinAt),
    nodes: balloonNodes(joinAt),
    intervals: letterIntervalNodes(joinAt),
    bands: massBands(joinAt),
  };
}

const CYCLE_FIGURES = new Map(JOIN_SPOTS.map((spot) => [spot, cycleFigure(spot)]));

function figureAt(joinAt: number): CycleFigure {
  return CYCLE_FIGURES.get(joinAt) ?? CYCLE_FIGURES.get(0) ?? cycleFigure(0);
}

type JoinGeom = {
  path: string;
  color: string;
  hollow: boolean;
};

function joinGeom(stem: StemItem[]): JoinGeom {
  const last = stem.at(-1);
  const stemLastY = last?.y ?? JOIN_Y + STEP;
  return {
    path: pointedSegPath(CX, stemLastY, CX, JOIN_Y),
    color: letterColor(last?.bead.letter ?? "?"),
    hollow: last?.bead.tone !== "sure",
  };
}

function RotateCcwIcon() {
  return (
    <svg viewBox="0 0 24 24" className="h-3.5 w-3.5" aria-hidden="true">
      <path
        d="M3 12a9 9 0 1 0 3-6.7M3 4v5h5"
        fill="none"
        stroke="currentColor"
        strokeWidth="2"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
}

function RotateCwIcon() {
  return (
    <svg viewBox="0 0 24 24" className="h-3.5 w-3.5" aria-hidden="true">
      <path
        d="M21 12a9 9 0 1 1-3-6.7M21 4v5h-5"
        fill="none"
        stroke="currentColor"
        strokeWidth="2"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </svg>
  );
}

function SnapIcon() {
  return (
    <svg viewBox="0 0 24 24" className="h-3.5 w-3.5" aria-hidden="true">
      <circle
        cx="12"
        cy="12"
        r="3"
        fill="currentColor"
      />
      <path
        d="M12 3v3M12 18v3M3 12h3M18 12h3"
        fill="none"
        stroke="currentColor"
        strokeWidth="2"
        strokeLinecap="round"
      />
    </svg>
  );
}

function LegendBead({
  letter,
  kind,
  label,
}: {
  letter: "O" | "E" | "?";
  kind: "sure" | "count" | "unknown" | "min";
  label?: string;
}) {
  const color = letterColor(letter);
  const filled = kind === "sure" || kind === "min";
  const shown = label ?? (kind === "unknown" ? "?" : letter === "?" ? "?" : letter);
  return (
    <svg viewBox="0 0 22 22" width="22" height="22" className="stem-cycle-legend-swatch" aria-hidden>
      <circle
        cx="11"
        cy="11"
        r="8"
        fill={filled ? color : "#fffdf7"}
        stroke={kind === "min" ? "#1d1914" : filled ? "none" : color}
        strokeWidth={kind === "min" || !filled ? 1.6 : 0}
        strokeDasharray={kind === "count" || kind === "unknown" ? "3 2" : undefined}
      />
      {shown ? (
        <text
          x="11"
          y="15"
          textAnchor="middle"
          fill={filled ? "#fffdf7" : color}
          className="stem-cycle-mono"
          fontSize={shown.length >= 3 ? "7" : "9"}
        >
          {shown}
        </text>
      ) : null}
    </svg>
  );
}

function LegendMass({ rim = INK }: { rim?: string }) {
  return (
    <svg viewBox="0 0 28 16" width="28" height="16" className="stem-cycle-legend-swatch" aria-hidden>
      <path
        d="M 3 13 A 20 20 0 0 1 25 13 L 22.6 8.2 A 14 14 0 0 0 5.4 8.2 Z"
        fill="#fffdf7"
        stroke={rim}
        strokeWidth="1.2"
        strokeDasharray="2.6 1.8"
      />
    </svg>
  );
}

function LegendLink({ hollow }: { hollow?: boolean }) {
  return (
    <svg viewBox="0 0 28 10" width="28" height="10" className="stem-cycle-legend-swatch" aria-hidden>
      <path
        d="M 2 1.4 L 25 5 L 2 8.6 Z"
        fill={hollow ? "#fffdf7" : "#1d1914"}
        stroke="#1d1914"
        strokeWidth="1.2"
        strokeLinejoin="round"
      />
    </svg>
  );
}

function LegendItem({
  label,
  decision,
  onPick,
  children,
}: {
  label: string;
  decision: string;
  onPick: (id: string) => void;
  children: ReactNode;
}) {
  return (
    <button
      type="button"
      className="stem-cycle-legend-item"
      onClick={() => onPick(decision)}
    >
      {children}
      <span>{label}</span>
    </button>
  );
}

const FigureLegend = memo(function FigureLegend({
  onPick,
}: {
  onPick: (id: string) => void;
}) {
  return (
    <div className="stem-cycle-legend" data-keep-focus>
      <span className="stem-cycle-legend-k">Parity</span>
      <div className="stem-cycle-legend-row">
        <LegendItem label="odd" decision="balloon-parity" onPick={onPick}>
          <LegendBead letter="O" kind="sure" />
        </LegendItem>
        <LegendItem label="even" decision="balloon-parity" onPick={onPick}>
          <LegendBead letter="E" kind="sure" />
        </LegendItem>
      </div>
      <span className="stem-cycle-legend-k">Certainty</span>
      <div className="stem-cycle-legend-row">
        <LegendItem label="plain — sure link (OO, wrap EO)" decision="balloon-links" onPick={onPick}>
          <LegendLink />
        </LegendItem>
        <LegendItem label="hollow — interval, may be empty" decision="balloon-links" onPick={onPick}>
          <LegendLink hollow />
        </LegendItem>
      </div>
      <span className="stem-cycle-legend-k">CycleMin</span>
      <div className="stem-cycle-legend-row">
        <LegendItem label="black ring — CycleMin only" decision="balloon-cut" onPick={onPick}>
          <LegendBead letter="O" kind="min" />
        </LegendItem>
      </div>
      <span className="stem-cycle-legend-k">Letters</span>
      <div className="stem-cycle-legend-row">
        <LegendItem label="filled — sure letter" decision="balloon-fade" onPick={onPick}>
          <LegendBead letter="E" kind="sure" />
        </LegendItem>
        <LegendItem label="hollow — aₑ" decision="balloon-seam" onPick={onPick}>
          <LegendBead letter="O" kind="count" />
        </LegendItem>
        <LegendItem label="grey ? — unknown stem" decision="string-grey" onPick={onPick}>
          <LegendBead letter="?" kind="unknown" />
        </LegendItem>
      </div>
      <span className="stem-cycle-legend-k">Mass</span>
      <div className="stem-cycle-legend-row">
        <LegendItem label="ink band — leftover count, may split" decision="balloon-fade" onPick={onPick}>
          <LegendMass />
        </LegendItem>
        <LegendItem label="orange dots — a₁ continues OO" decision="balloon-oo" onPick={onPick}>
          <LegendMass rim={ODD} />
        </LegendItem>
      </div>
    </div>
  );
});

function JoinIconButton({
  label,
  disabled,
  active,
  onClick,
  children,
}: {
  label: string;
  disabled?: boolean;
  active?: boolean;
  onClick: () => void;
  children: ReactNode;
}) {
  return (
    <button
      type="button"
      title={label}
      aria-label={label}
      disabled={disabled}
      className={`grid h-6 w-6 place-items-center rounded-full border ${
        active
          ? "border-deep bg-deep text-card"
          : "border-line bg-card text-ink"
      } disabled:opacity-40`}
      onClick={onClick}
    >
      {children}
    </button>
  );
}

export function JoinRotateControls({
  joinAt,
  onJoinIndex,
}: {
  joinAt: number;
  onJoinIndex: (index: number) => void;
}) {
  const at = JOIN_SPOTS.includes(joinAt) ? joinAt : 0;
  return (
    <div className="flex items-center gap-1.5">
      <JoinIconButton
        label="Join left"
        onClick={() => onJoinIndex(stepIdealJoin(at, -1, JOIN_SPOTS))}
      >
        <RotateCcwIcon />
      </JoinIconButton>
      <JoinIconButton
        label="Snap join to CycleMin"
        disabled={at === 0}
        active={at === 0}
        onClick={() => onJoinIndex(0)}
      >
        <SnapIcon />
      </JoinIconButton>
      <JoinIconButton
        label="Join right"
        onClick={() => onJoinIndex(stepIdealJoin(at, 1, JOIN_SPOTS))}
      >
        <RotateCwIcon />
      </JoinIconButton>
    </div>
  );
}

function activate(
  onPick: (() => void) | undefined,
  event: MouseEvent | KeyboardEvent,
) {
  if ("key" in event && event.key !== "Enter" && event.key !== " ") return;
  if ("key" in event) event.preventDefault();
  event.stopPropagation();
  onPick?.();
}

const Bead = memo(function Bead({
  x,
  y,
  bead,
  radius,
  marked,
  caption,
  captionX,
  captionY,
  glyph,
  name,
  lit,
  onPick,
}: {
  x: number;
  y: number;
  bead: IdealBead | PaintedBead;
  radius: number;
  marked?: boolean;
  caption?: string;
  name?: string;
  captionX?: number;
  captionY?: number;
  glyph?: string;
  lit: boolean;
  onPick?: () => void;
}) {
  const paint = beadPaint(bead);
  const bound =
    caption === "≥0" || caption === "≤1" || caption?.startsWith("{")
      ? caption
      : undefined;
  const shown =
    glyph ??
    (bead.letter === "O" || bead.letter === "E"
      ? bead.letter
      : (bound ?? bead.letter));
  const note = name ?? (bound ? undefined : caption);
  const sub = name ? bound : undefined;
  const glyphSize = shown.length >= 5 ? "8" : shown.length >= 3 ? "9" : "11";
  const aria = [
    bead.letter === "O"
      ? shown
        ? `odd ${shown}`
        : "odd"
      : bead.letter === "E"
        ? shown
          ? `even ${shown}`
          : "even"
        : shown === "?" || !shown
          ? "unknown"
          : `unknown ${shown}`,
    name,
    sub,
  ]
    .filter(Boolean)
    .join(" ");
  return (
    <g
      className={fadeClass(lit)}
      role={onPick ? "button" : undefined}
      tabIndex={onPick ? 0 : undefined}
      aria-label={onPick ? aria : undefined}
      onClick={onPick ? (event) => activate(onPick, event) : undefined}
      onKeyDown={onPick ? (event) => activate(onPick, event) : undefined}
    >
        <circle
        cx={x}
        cy={y}
        r={radius}
        fill={paint.fill}
        stroke={marked ? "#1d1914" : paint.stroke}
        strokeWidth={paint.dash || marked ? 1.6 : 0}
        strokeDasharray={paint.dash}
      />
      {shown ? (
        <text
          x={x}
          y={y + 4}
          textAnchor="middle"
          fill={paint.text}
          className="stem-cycle-mono"
          fontSize={glyphSize}
        >
          {shown}
        </text>
      ) : null}
      {note ? (
        <text
          x={captionX ?? x}
          y={(captionY ?? y + radius + 16) - (sub ? 6 : 0)}
          textAnchor="middle"
          className="stem-cycle-note"
        >
          {note}
        </text>
      ) : null}
      {sub ? (
        <text
          x={captionX ?? x}
          y={(captionY ?? y + radius + 16) + 7}
          fill={INK}
          className="stem-cycle-mono"
          fontSize="8"
          textAnchor="middle"
        >
          {sub}
        </text>
      ) : null}
    </g>
  );
});

const MassBandMark = memo(function MassBandMark({
  band,
  lit,
  onPick,
}: {
  band: MassBand;
  lit: boolean;
  onPick: () => void;
}) {
  const aria = band.continuesOO
    ? `mass ${band.name} ${band.bound}, continues launch OO`
    : `mass ${band.name} ${band.bound}, may split`;
  return (
    <g
      className={fadeClass(lit)}
      role="button"
      tabIndex={0}
      aria-label={aria}
      onClick={(event) => activate(onPick, event)}
      onKeyDown={(event) => activate(onPick, event)}
    >
      <path
        d={band.path}
        fill="#fffdf7"
        stroke={band.rim}
        strokeWidth="1.35"
        strokeDasharray="3.2 2.2"
        strokeLinejoin="round"
      />
      <text x={band.captionX} y={band.captionY - 6} className="stem-cycle-note">
        {band.name}
      </text>
      <text
        x={band.captionX}
        y={band.captionY + 7}
        fill={INK}
        className="stem-cycle-mono"
        fontSize="8"
        textAnchor="middle"
      >
        {band.bound}
      </text>
    </g>
  );
});

const JoinCard = memo(function JoinCard({
  joinAt,
  lit,
  onPick,
}: {
  joinAt: number;
  lit: boolean;
  onPick: (id: string) => void;
}) {
  const join = idealJoinConfig(joinAt);
  const atCycleMin = join.isValley;
  return (
    <button
      type="button"
      data-keep-focus
      className={`stem-cycle-card ${fadeClass(lit) ?? ""}`}
      onClick={() => onPick("join-seam")}
    >
      <p className="text-xs uppercase tracking-wide text-muted">
        Join at {join.name}
        {atCycleMin ? " — CycleMin cut" : " — same loop, not the CycleMin cut"}
        {join.fillDependent ? " — fill-dependent arrival" : ""}
      </p>
      <p className="mt-1 font-mono text-sm text-ink">
        vertex {join.vertex} · arrives {join.arrival}
        {join.fillDependent ? " (fill-dependent)" : ""} · stem t is{" "}
        {join.stemTerminal === "E" ? "even (forced)" : "unknown"}
      </p>
      <p className="mt-1 text-sm text-ink">
        Cyclic parent: {join.cycleParent}. Stem: {join.stem}.
      </p>
      <ul className="mt-1 list-disc pl-4 text-xs text-muted">
        {join.forbidden.map((item) => (
          <li key={item}>{item}</li>
        ))}
      </ul>
      <p className="mt-1 text-xs text-muted">
        {join.arrivalWhy} {join.lean}. {JOIN_INTERVALS_NOT_STOPS} {JOIN_VS_WORD_ROTATION}
      </p>
    </button>
  );
});

const FigureSvg = memo(function FigureSvg({
  focus,
  joinAt,
  stemMode,
  onPick,
  onClear,
}: {
  focus?: DecisionFocus;
  joinAt: number;
  stemMode: StemDisplayMode;
  onPick: (id: string) => void;
  onClear?: () => void;
}) {
  const stem = stemForJoin(joinAt, stemMode);
  const emptyStem = stem.length === 0;
  const join = joinGeom(stem);
  const cycle = figureAt(joinAt);
  const joinLit = regionLit(focus, "join");
  const joinFocus = focus === "join";
  const stemTitleY = (stem[0]?.y ?? JOIN_Y) + BEAD_R + 20;
  const viewH = emptyStem
    ? Math.ceil(JOIN_Y + BEAD_R + 16)
    : Math.ceil(stemTitleY + 16);

  return (
    <svg
      viewBox={`0 0 ${VIEW_W} ${viewH}`}
      role="img"
      className="stem-cycle-svg mt-1 h-auto w-full"
      onClick={(event) => {
        if ((event.target as Element).closest("[role='button']")) return;
        onClear?.();
      }}
    >
      <title>
        Schematic CycleMin geometry with an optional stem. No nontrivial cycle
        is known. Circles are letters. Ink bands in the gaps are leftover mass,
        not a letter color. Pointed links: filled is sure (OO, wrap EO), hollow
        may be empty.
      </title>
      {emptyStem ? null : (
        <text x={CX} y={stemTitleY} className="stem-cycle-title">
          Stem
        </text>
      )}
      {stem.slice(0, -1).map((item, index) => {
        const next = stem[index + 1];
        const hollow = item.bead.tone !== "sure" || next.bead.tone !== "sure";
        const color = letterColor(item.bead.letter);
        return (
          <path
            key={`stem-link-${index}`}
            className={`stem-cycle-flow ${fadeClass(regionLit(focus, item.region)) ?? ""}`}
            d={pointedSegPath(item.x, item.y, next.x, next.y)}
            fill={hollow ? "#fffdf7" : color}
            stroke={color}
            strokeWidth="1.3"
            strokeLinejoin="round"
          />
        );
      })}
      {stem.map((item, index) => (
        <Bead
          key={`stem-${item.region}-${index}`}
          x={item.x}
          y={item.y}
          bead={item.bead}
          radius={BEAD_R}
          caption={item.caption}
          captionX={item.x + BEAD_R + 20}
          captionY={item.y + 4}
          lit={regionLit(focus, item.region)}
          onPick={() => onPick(stemDecision(item.region))}
        />
      ))}
      {cycle.bands.map((band) => (
        <MassBandMark
          key={band.key}
          band={band}
          lit={regionLit(focus, band.region)}
          onPick={() => onPick(band.decision)}
        />
      ))}
      {cycle.arcs.map((arc) => (
        <g key={arc.key} className={fadeClass(regionLit(focus, arc.region))}>
        <path
            className="stem-cycle-flow"
            d={arc.pointed}
            fill={arc.hollow ? "#fffdf7" : arc.color}
            stroke={arc.color}
            strokeWidth="1.3"
            strokeLinejoin="round"
          />
        </g>
      ))}
      {cycle.intervals.map((node) => (
        <Bead
          key={node.key}
          x={node.x}
          y={node.y}
          bead={node.bead}
          radius={node.radius}
          glyph={node.glyph}
          caption={node.caption}
          name={node.name}
          captionX={node.captionX}
          captionY={node.captionY}
          lit={regionLit(focus, node.region)}
          onPick={() => onPick(node.decision)}
        />
      ))}
      {emptyStem ? null : (
        <path
          d={join.path}
          className={fadeClass(joinLit)}
          fill={join.hollow ? "#fffdf7" : join.color}
          stroke={join.color}
          strokeWidth="1.3"
          strokeLinejoin="round"
          role="button"
          onClick={(event) => activate(() => onPick("join-seam"), event)}
        />
      )}
      {cycle.nodes.map((node) => {
        const isJoin = node.index === joinAt;
        return (
          <Bead
            key={node.key}
            x={node.x}
            y={node.y}
            bead={node.bead}
            radius={node.radius}
            marked={node.marked}
            glyph={node.glyph}
            caption={node.caption}
            captionX={node.captionX}
            captionY={node.captionY}
            lit={joinFocus ? isJoin : regionLit(focus, node.region)}
            onPick={() => onPick(node.decision)}
          />
        );
      })}
      <text
        x={CX}
        y={CY - 3}
        className="stem-cycle-title"
        role="button"
        aria-label="Ideal cycle"
        onClick={(event) => activate(() => onPick("balloon-run"), event)}
      >
        <tspan x={CX} dy="0">
          Ideal
        </tspan>
        <tspan x={CX} dy="20">
          cycle
        </tspan>
      </text>
    </svg>
  );
});

export const CycleLollipop = memo(function CycleLollipop({
  focus,
  joinIndex = 0,
  stemMode = "empty",
  onSelectDecision,
  onClearFocus,
}: {
  focus?: DecisionFocus;
  joinIndex?: number;
  stemMode?: StemDisplayMode;
  onSelectDecision?: (id: string) => void;
  onClearFocus?: () => void;
}) {
  const joinAt = JOIN_SPOTS.includes(joinIndex) ? joinIndex : 0;
  const pick = useCallback(
    (id: string) => {
      onSelectDecision?.(id);
    },
    [onSelectDecision],
  );

  return (
    <div
      className="stem-cycle rounded-xl border border-line bg-paper/70 px-3 py-3"
      onClick={(event) => {
        if (event.target === event.currentTarget) onClearFocus?.();
      }}
    >
      <div>
        <FigureSvg
          focus={focus}
          joinAt={joinAt}
          stemMode={stemMode}
          onPick={pick}
          onClear={onClearFocus}
        />
        <FigureLegend onPick={pick} />
      </div>
      {stemMode === "empty" ? null : (
        <JoinCard
          joinAt={joinAt}
          lit={regionLit(focus, "join") || !focus}
          onPick={pick}
        />
      )}
    </div>
  );
});
