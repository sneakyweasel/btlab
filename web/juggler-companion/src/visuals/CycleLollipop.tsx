import { memo, useCallback, type KeyboardEvent, type MouseEvent } from "react";
import type { DecisionFocus } from "../content/idealDecisions";
import {
  IDEAL_BALLOON_BEADS,
  IDEAL_BALLOON_INTERVALS,
  idealJoinSpots,
  intervalCountBead,
  stepIdealJoin,
  type BalloonInterval,
  type IdealBead,
} from "../juggler/constants";
import {
  formatNecklaceFill,
  formatOddEvenRuns,
  formatRunWord,
  necklaceFillToRuns,
  oddEvenRuns,
  runsEqual,
  type NecklaceFill,
} from "../juggler/itinerary";
import {
  JOIN_INTERVALS_NOT_STOPS,
  JOIN_VS_WORD_ROTATION,
  idealJoinConfig,
} from "../juggler/joinConfig";
import {
  FIGURE_BANNER,
  joinFigure,
  paintCaptureStem,
  paintStem,
  siteAtIndex,
  type FigureMark,
  type PaintedBead,
  type RealizedWitness,
  type StemDisplayMode,
} from "../juggler/lollipop";

const CX = 548;
const CY = 160;
const R = 104;
const ODD = "#c45c26";
const EVEN = "#1f6f6a";
const GREY = "#8a8378";
const STEM_X0 = 36;
const STEM_STEP = 54;
const BALLOON = IDEAL_BALLOON_BEADS;
const N = BALLOON.length;
const JOIN_SPOTS = idealJoinSpots(BALLOON);
const BEAD_R = Math.min(14, Math.max(9, (Math.PI * R) / N - 1.2));

function letterColor(letter: IdealBead["letter"]): string {
  if (letter === "O") return ODD;
  if (letter === "E") return EVEN;
  return GREY;
}

function beadAngle(index: number): number {
  return (index / N) * 2 * Math.PI + Math.PI;
}

function atAngle(angle: number, radius: number, dy = 0): { x: number; y: number } {
  return { x: CX + radius * Math.cos(angle), y: CY + radius * Math.sin(angle) + dy };
}

function arcPath(a0: number, a1: number): string {
  const x0 = CX + R * Math.cos(a0);
  const y0 = CY + R * Math.sin(a0);
  const x1 = CX + R * Math.cos(a1);
  const y1 = CY + R * Math.sin(a1);
  const sweep = (a1 - a0 + 2 * Math.PI) % (2 * Math.PI);
  return `M ${x0} ${y0} A ${R} ${R} 0 ${sweep > Math.PI ? 1 : 0} 1 ${x1} ${y1}`;
}

function minorArcDelta(from: number, to: number): number {
  const tau = 2 * Math.PI;
  const a0 = ((from % tau) + tau) % tau;
  const a1 = ((to % tau) + tau) % tau;
  let delta = a1 - a0;
  if (delta > Math.PI) delta -= tau;
  if (delta < -Math.PI) delta += tau;
  return delta;
}

function intervalAngle(afterBead: number): number {
  const a0 = beadAngle(afterBead);
  let a1 = beadAngle(afterBead + 1);
  if (a1 <= a0) a1 += 2 * Math.PI;
  return (a0 + a1) / 2;
}

function intervalAfter(index: number): BalloonInterval | undefined {
  return IDEAL_BALLOON_INTERVALS.find((item) => item.afterBead === index);
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

function balloonNote(index: number): string {
  const sureEvens = BALLOON.flatMap((item, itemIndex) =>
    item.letter === "E" && item.tone === "sure" ? [itemIndex] : [],
  );
  if (index === 0) return "CycleMin";
  if (index === 1) return "launch";
  if (index === sureEvens[0]) return "overshoots";
  if (index === sureEvens[sureEvens.length - 1]) return "lands";
  const evenRank = sureEvens.indexOf(index);
  return evenRank > 0 ? `E ${evenRank + 1}` : "";
}

function intervalNote(interval: BalloonInterval): string {
  if (interval.kind === "a1Extras") return "a₁ extras";
  if (interval.kind === "middle") return "middle odds";
  if (interval.kind === "extraEven") return "extra E";
  return "last odd";
}

function intervalCountGlyph(interval: BalloonInterval): string {
  return interval.max === null ? `${interval.min}+` : `{${interval.min},${interval.max}}`;
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

function stemCaption(index: number, bead: IdealBead | PaintedBead, last: number): string {
  if ("caption" in bead && bead.caption) return bead.caption;
  if (index === last && bead.letter === "E") return "t even";
  if (index === last) return "t = E|O";
  if (beadMark(bead) === "optional") return "optional";
  if (bead.tone === "unknown") return "unknown";
  return "";
}

type StemItem = {
  x: number;
  bead: IdealBead | PaintedBead;
  region: DecisionFocus;
  label: string;
  glyph?: string;
};

function stemItemsFromPainted(beads: readonly PaintedBead[]): StemItem[] {
  const last = beads.length - 1;
  return beads.map((bead, index) => ({
    x: STEM_X0 + index * STEM_STEP,
    bead,
    region:
      bead.mark === "optional"
        ? "string-oo"
        : index === last
          ? "string-e"
          : stemRegion(index, last),
    label: stemCaption(index, bead, last),
    glyph: bead.glyph,
  }));
}

function stemForJoin(
  joinAt: number,
  mode: StemDisplayMode,
  witness: RealizedWitness | null,
): StemItem[] {
  if (witness?.fate === "capture") return stemItemsFromPainted(paintCaptureStem(witness));
  return stemItemsFromPainted(paintStem(mode, joinFigure(siteAtIndex(joinAt), joinAt)));
}

type CycleTile = {
  note: string;
  glyph: string;
  decision: string;
  focus: DecisionFocus;
  bead: IdealBead;
};

const CYCLE_TILES: CycleTile[] = BALLOON.flatMap((bead, index) => {
  const region = balloonRegion(index, bead);
  const count = index === 1 ? "a₁≥2" : "";
  const tile: CycleTile = {
    note: balloonNote(index),
    glyph: index === 0 ? "n" : count || bead.letter,
    decision: index === 0 ? "balloon-cut" : balloonDecision(region),
    focus: index === 0 ? "balloon" : region,
    bead,
  };
  const interval = intervalAfter(index);
  if (!interval) return [tile];
  return [
    tile,
    {
      note: intervalNote(interval),
      glyph: intervalCountGlyph(interval),
      decision: intervalDecision(interval),
      focus: intervalRegion(interval),
      bead: intervalCountBead(interval),
    },
  ];
});

type ArcSeg = {
  key: string;
  d: string;
  color: string;
  dashed: boolean;
  launch: boolean;
  region: DecisionFocus;
};

const BALLOON_ARCS: ArcSeg[] = BALLOON.flatMap((bead, index): ArcSeg[] => {
  const a0 = beadAngle(index);
  const a1 = beadAngle(index + 1);
  const interval = intervalAfter(index);
  const region = interval ? intervalRegion(interval) : balloonRegion(index, bead);
  const launch = index === 0;
  if (!interval) {
    return [
      {
        key: `arc-${index}`,
        d: arcPath(a0, a1),
        color: letterColor(bead.letter),
        dashed: false,
        launch,
        region,
      },
    ];
  }
  const mid = intervalAngle(interval.afterBead);
  return [
    {
      key: `arc-${index}-a`,
      d: arcPath(a0, mid),
      color: letterColor(bead.letter),
      dashed: true,
      launch,
      region,
    },
    {
      key: `arc-${index}-b`,
      d: arcPath(mid, a1),
      color: letterColor(intervalCountBead(interval).letter),
      dashed: true,
      launch,
      region,
    },
  ];
});

type FigureNode = {
  key: string;
  x: number;
  y: number;
  bead: IdealBead;
  radius: number;
  glyph?: string;
  caption: string;
  captionX: number;
  captionY: number;
  region: DecisionFocus;
  decision: string;
  marked?: boolean;
  index?: number;
};

const BALLOON_NODES: FigureNode[] = BALLOON.map((bead, index) => {
  const angle = beadAngle(index);
  const { x, y } = atAngle(angle, R);
  const count = index === 1 ? "a₁≥2" : "";
  const radius = index === 0 || count ? BEAD_R + 4 : BEAD_R;
  const outer = index === 0 ? { x, y: y - radius - 14 } : atAngle(angle, R + radius + 16, 4);
  const region = balloonRegion(index, bead);
  return {
    key: `balloon-${index}`,
    x,
    y,
    bead,
    radius,
    glyph: count || undefined,
    caption: balloonNote(index),
    captionX: outer.x,
    captionY: outer.y,
    region,
    decision: balloonDecision(region),
    marked: index === 0,
    index,
  };
});

const INTERVAL_NODES: FigureNode[] = IDEAL_BALLOON_INTERVALS.map((interval) => {
  const angle = intervalAngle(interval.afterBead);
  const { x, y } = atAngle(angle, R);
  const outer = atAngle(angle, R + BEAD_R + 17, 4);
  const region = intervalRegion(interval);
  return {
    key: `interval-${interval.kind}`,
    x,
    y,
    bead: intervalCountBead(interval),
    radius: BEAD_R + 1,
    glyph: intervalCountGlyph(interval),
    caption: intervalNote(interval),
    captionX: outer.x,
    captionY: outer.y,
    region,
    decision: intervalDecision(interval),
  };
});

const SURE_OO = atAngle((beadAngle(0) + beadAngle(1)) / 2, R - 34);
const SURE_EO = atAngle(intervalAngle(N - 1), R + 28);

type JoinGeom = {
  path: string;
  labelX: number;
  labelY: number;
  color: string;
};

function joinGeom(joinAt: number, stem: StemItem[]): JoinGeom {
  const stemLastX = stem.at(-1)?.x ?? STEM_X0;
  const dest = atAngle(beadAngle(joinAt), R);
  const color = letterColor(stem.at(-1)?.bead.letter ?? "?");
  if (joinAt === 0) {
    return {
      path: `M ${stemLastX} ${CY} L ${dest.x} ${dest.y}`,
      labelX: (stemLastX + dest.x) / 2,
      labelY: CY - 22,
      color,
    };
  }
  const entry = atAngle(beadAngle(0), R);
  const delta = minorArcDelta(beadAngle(0), beadAngle(joinAt));
  const mid = beadAngle(0) + delta / 2;
  const label = atAngle(mid, R + 38, 4);
  return {
    path: `M ${stemLastX} ${CY} L ${entry.x} ${entry.y} A ${R} ${R} 0 0 ${delta >= 0 ? 1 : 0} ${dest.x} ${dest.y}`,
    labelX: label.x,
    labelY: label.y,
    color,
  };
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
  joined,
  caption,
  captionX,
  captionY,
  glyph,
  lit,
  onPick,
}: {
  x: number;
  y: number;
  bead: IdealBead | PaintedBead;
  radius: number;
  marked?: boolean;
  joined?: boolean;
  caption?: string;
  captionX?: number;
  captionY?: number;
  glyph?: string;
  lit: boolean;
  onPick?: () => void;
}) {
  const paint = beadPaint(bead);
  const shown = glyph ?? (bead.letter === "O" && marked ? "n" : bead.letter);
  const glyphSize =
    shown.length >= 5 ? "8" : shown.length >= 3 ? "10" : radius >= 15 ? "13" : "11";
  return (
    <g
      className={fadeClass(lit)}
      role={onPick ? "button" : undefined}
      tabIndex={onPick ? 0 : undefined}
      onClick={onPick ? (event) => activate(onPick, event) : undefined}
      onKeyDown={onPick ? (event) => activate(onPick, event) : undefined}
    >
      <circle
        cx={x}
        cy={y}
        r={radius}
        fill={paint.fill}
        stroke={joined || marked ? "#1d1914" : paint.stroke}
        strokeWidth={joined ? 3.4 : marked ? 3 : paint.dash ? 1.6 : 0}
        strokeDasharray={paint.dash}
      />
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
      {caption ? (
        <text
          x={captionX ?? x}
          y={captionY ?? y + radius + 16}
          textAnchor="middle"
          className="stem-cycle-note"
        >
          {caption}
        </text>
      ) : null}
    </g>
  );
});

const RunTile = memo(function RunTile({
  bead,
  glyph,
  ring,
}: {
  bead: IdealBead;
  glyph?: string;
  ring?: boolean;
}) {
  const paint = beadPaint(bead);
  const shown = glyph ?? bead.letter;
  const wide = shown.length > 1;
  return (
    <span
      className="inline-flex h-7 items-center justify-center rounded-full font-mono text-xs"
      style={{
        minWidth: wide ? 38 : 28,
        paddingInline: wide ? 5 : 0,
        background: paint.fill,
        color: paint.text,
        border: ring
          ? "2px solid #1d1914"
          : paint.dash
            ? `1px dashed ${paint.stroke}`
            : "none",
      }}
    >
      {shown}
    </span>
  );
});

const CycleLeanPanel = memo(function CycleLeanPanel({
  word,
  fill,
  lit,
  onPick,
}: {
  word?: string;
  fill?: NecklaceFill | null;
  lit: boolean;
  onPick: (id: string) => void;
}) {
  const runs = word ? oddEvenRuns(word) : null;
  const projected = fill ? necklaceFillToRuns(fill) : null;
  const matchesFill = Boolean(runs && projected && runsEqual(runs, projected));
  return (
    <button
      type="button"
      data-keep-focus
      className={`stem-cycle-card ${fadeClass(lit) ?? ""}`}
      onClick={() => onPick("balloon-run")}
    >
      <p className="text-xs uppercase tracking-wide text-muted">
        On the cycle — cycleMin_has_full_odd_even_run_form
      </p>
      <p className="mt-1 font-mono text-sm text-ink">
        {runs
          ? `w = ${formatRunWord(runs)}   ${formatOddEvenRuns(runs)}`
          : "w = O^a1 E ... O^ae E   with a1 >= 2, ae <= 1"}
      </p>
      <p className="mt-1 text-xs text-muted">
        {runs && projected && matchesFill
          ? `Equals toRuns of assembleFill ${formatNecklaceFill(fill!)}. The ring is that bunched projection.`
          : runs
            ? "Interior runs the four-slot ring forgets. The beads are a projection, not assembleFill."
            : "The ring is a projection of this Lean list onto six sure letters. Sure links are launch OO and wrap EO."}
      </p>
    </button>
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
  const atCycleMin = joinAt === 0;
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
      </p>
      <p className="mt-1 font-mono text-sm text-ink">
        vertex {join.vertex} · arrives {join.arrival} · stem t is{" "}
        {join.stemTerminal === "E" ? "even" : "E or O"}
      </p>
      <p className="mt-1 text-sm text-ink">
        Cyclic parent: {join.cycleParent}. Stem: {join.stem}.
      </p>
      <p className="mt-1 text-xs text-muted">
        {join.arrivalWhy} {join.lean}. {JOIN_INTERVALS_NOT_STOPS} {JOIN_VS_WORD_ROTATION}
      </p>
    </button>
  );
});

const FigureSvg = memo(function FigureSvg({
  focus,
  joinAt,
  onPick,
  onClear,
}: {
  focus?: DecisionFocus;
  joinAt: number;
  onPick: (id: string) => void;
  onClear?: () => void;
}) {
  const stem = stemForJoin(joinAt);
  const join = JOIN_GEOM[joinAt] ?? JOIN_GEOM[0]!;
  const joinLit = regionLit(focus, "join");
  const joinFocus = focus === "join";
  const atCycleMin = joinAt === 0;
  const joinCfg = idealJoinConfig(joinAt);

  return (
    <svg
      viewBox="0 0 720 340"
      role="img"
      className="stem-cycle-svg mt-1 h-auto w-full"
      onClick={(event) => {
        if ((event.target as Element).closest("[role='button']")) return;
        onClear?.();
      }}
    >
      <title>
        Optional stem joining a CycleMin cycle at a sure letter. The cycle is a
        projection of the Lean run list onto six sure letters.
      </title>
      <text x={(stem[0].x + stem[Math.max(stem.length - 2, 0)].x) / 2} y={CY - 44} className="stem-cycle-title">
        Stem
      </text>
      {stem.slice(0, -1).map((item, index) => {
        const next = stem[index + 1];
        const unsure = item.bead.tone !== "sure" || next.bead.tone !== "sure";
        return (
          <line
            key={`stem-link-${index}`}
            x1={item.x}
            y1={CY}
            x2={next.x}
            y2={CY}
            stroke={letterColor(item.bead.letter)}
            strokeWidth="2.2"
            strokeLinecap="round"
            strokeDasharray={unsure ? "3 3" : undefined}
            className={fadeClass(regionLit(focus, item.region))}
          />
        );
      })}
      {stem.map((item) => (
        <Bead
          key={`stem-${item.region}-${item.x}`}
          x={item.x}
          y={CY}
          bead={item.bead}
          radius={16}
          glyph={item.glyph}
          caption={item.label}
          lit={regionLit(focus, item.region)}
          onPick={() => onPick(stemDecision(item.region))}
        />
      ))}
      {BALLOON_ARCS.map((arc) => (
        <path
          key={arc.key}
          d={arc.d}
          fill="none"
          stroke={arc.color}
          strokeWidth={arc.launch ? 5 : 3}
          strokeLinecap="round"
          strokeDasharray={arc.dashed ? "3 3" : undefined}
          className={fadeClass(regionLit(focus, arc.region))}
        />
      ))}
      {INTERVAL_NODES.map((node) => (
        <Bead
          key={node.key}
          x={node.x}
          y={node.y}
          bead={node.bead}
          radius={node.radius}
          glyph={node.glyph}
          caption={node.caption}
          captionX={node.captionX}
          captionY={node.captionY}
          lit={regionLit(focus, node.region)}
          onPick={() => onPick(node.decision)}
        />
      ))}
      <path
        d={join.path}
        fill="none"
        stroke={join.color}
        strokeWidth="2.2"
        strokeLinecap="round"
        className={fadeClass(joinLit)}
        role="button"
        onClick={(event) => activate(() => onPick("join-seam"), event)}
      />
      <text
        x={join.labelX}
        y={join.labelY}
        textAnchor="middle"
        className={`stem-cycle-note stem-cycle-ink ${fadeClass(joinLit) ?? ""}`}
        role="button"
        onClick={(event) => activate(() => onPick("join-seam"), event)}
      >
        {atCycleMin ? "join · CycleMin" : `join · ${joinCfg.name}`}
      </text>
      {BALLOON_NODES.map((node) => {
        const isJoin = node.index === joinAt;
        return (
          <Bead
            key={node.key}
            x={node.x}
            y={node.y}
            bead={node.bead}
            radius={node.radius}
            marked={node.marked}
            joined={isJoin}
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
        y={CY - 8}
        className="stem-cycle-title stem-cycle-title-sm"
        role="button"
        onClick={(event) => activate(() => onPick("balloon-run"), event)}
      >
        Idealized cycle
      </text>
      <text
        x={CX}
        y={CY + 14}
        className="stem-cycle-note"
        role="button"
        onClick={(event) => activate(() => onPick("balloon-run"), event)}
      >
        O^a₁ E … O^aₑ E
      </text>
      <text
        x={SURE_OO.x}
        y={SURE_OO.y}
        fill={ODD}
        className={`stem-cycle-link ${fadeClass(regionLit(focus, "balloon-oo") || regionLit(focus, "balloon-seam") || regionLit(focus, "balloon")) ?? ""}`}
        role="button"
        onClick={(event) => activate(() => onPick("balloon-links"), event)}
      >
        sure OO
      </text>
      <text
        x={SURE_EO.x}
        y={SURE_EO.y}
        fill={EVEN}
        className={`stem-cycle-link ${fadeClass(regionLit(focus, "balloon-oo") || regionLit(focus, "balloon-seam") || regionLit(focus, "balloon")) ?? ""}`}
        role="button"
        onClick={(event) => activate(() => onPick("balloon-links"), event)}
      >
        sure EO
      </text>
    </svg>
  );
});

const TileRow = memo(function TileRow({
  focus,
  joinAt,
  onPick,
}: {
  focus?: DecisionFocus;
  joinAt: number;
  onPick: (id: string) => void;
}) {
  const stem = stemForJoin(joinAt);
  return (
    <div className="mt-2 grid gap-3">
      <div>
        <p className="text-[10px] uppercase tracking-wide text-muted">Stem</p>
        <div className="mt-1.5 flex flex-wrap items-end justify-center gap-2">
          {stem.map((item, index) => (
            <button
              key={`stem-tile-${index}`}
              type="button"
              className={`grid justify-items-center gap-0.5 ${fadeClass(regionLit(focus, item.region)) ?? ""}`}
              onClick={() => onPick(stemDecision(item.region))}
            >
              <RunTile bead={item.bead} glyph={item.glyph ?? item.bead.letter} />
              <span className="text-[10px] text-muted">{item.label}</span>
            </button>
          ))}
        </div>
      </div>
      <div>
        <p className="text-[10px] uppercase tracking-wide text-muted">
          Idealized cycle
        </p>
        <div className="mt-1.5 flex flex-wrap items-end justify-center gap-1.5">
          {CYCLE_TILES.map((tile, index) => (
            <button
              key={`${tile.note}-${index}`}
              type="button"
              className={`grid justify-items-center gap-0.5 ${fadeClass(regionLit(focus, tile.focus)) ?? ""}`}
              onClick={() => onPick(tile.decision)}
            >
              <RunTile bead={tile.bead} glyph={tile.glyph} />
              <span className="text-[10px] text-muted">{tile.note}</span>
            </button>
          ))}
        </div>
      </div>
    </div>
  );
});

export const CycleLollipop = memo(function CycleLollipop({
  focus,
  joinIndex = 0,
  word,
  fill = null,
  onJoinIndex,
  onSelectDecision,
  onClearFocus,
}: {
  focus?: DecisionFocus;
  joinIndex?: number;
  word?: string;
  fill?: NecklaceFill | null;
  onJoinIndex?: (index: number) => void;
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
      <FigureSvg focus={focus} joinAt={joinAt} onPick={pick} onClear={onClearFocus} />
      <TileRow focus={focus} joinAt={joinAt} onPick={pick} />
      <CycleLeanPanel
        word={word}
        fill={fill}
        lit={!focus || focus === "figure" || focus.startsWith("balloon")}
        onPick={pick}
      />
      <div className="mt-2 flex flex-wrap items-center justify-center gap-2">
        <button
          type="button"
          className="rounded-full border border-line px-3 py-1 text-sm"
          onClick={() => onJoinIndex?.(stepIdealJoin(joinAt, -1, JOIN_SPOTS))}
        >
          Join left
        </button>
        <button
          type="button"
          className="rounded-full bg-deep px-3 py-1 text-sm text-card disabled:opacity-40"
          disabled={joinAt === 0}
          onClick={() => onJoinIndex?.(0)}
        >
          Snap join to CycleMin
        </button>
        <button
          type="button"
          className="rounded-full border border-line px-3 py-1 text-sm"
          onClick={() => onJoinIndex?.(stepIdealJoin(joinAt, 1, JOIN_SPOTS))}
        >
          Join right
        </button>
      </div>
      <JoinCard
        joinAt={joinAt}
        lit={regionLit(focus, "join") || !focus}
        onPick={pick}
      />
      <p className="mt-2 text-sm text-muted">
        Counts sit in the beads, notes outside. Join left/right walks the
        stem around the six sure letters. Necklace rotate is a different
        motion: a cut that starts E or OE is not CycleMin.
      </p>
    </div>
  );
});
