import { useCallback, useEffect, useRef, useState, type ReactNode } from "react";
import {
  ENVELOPE_MONSTERS,
  ENVELOPE_STARTS,
  EXPANDING_MONSTERS,
  EXPANDING_STARTS,
  LIVE_STARTS,
  MONSTER_ROW_LIVE,
  RECORD_LENGTHS,
  TRAJECTORY_STEPS_MAX,
} from "../juggler/constants";
import { usePlayState } from "../context/PlayState";
import { financeView } from "../juggler/finance";
import { formatInt, parsePositiveInt } from "../juggler/format";
import { floorPower, letterOf } from "../juggler/map";
import { monsterCatalog, resolveTrajectory } from "../juggler/monsters";
import { envelopeLog10Series, oddCount, regimeOf } from "../juggler/itinerary";
import { CycleTourWidget, LeftoverWidget } from "./CycleTourWidget";
import { GapTransferExplorer } from "./GapTransferExplorer";
import { RunSuffixExplorer } from "./RunSuffixExplorer";
import { FanExplorer } from "./FanExplorer";
import { WalkChargeExplorer } from "./WalkChargeExplorer";
import { EnvelopePanel, EnvelopeSlack } from "../visuals/EnvelopeSlack";
import { RegimeDoors } from "../visuals/RegimeDoors";
import { FinanceBalance, FinanceHierarchy } from "../visuals/FinanceBalance";
import { FloorLadder } from "../visuals/FloorLadder";
import { CubicBandOrder } from "../visuals/CubicBandOrder";
import { HeightStrip } from "../visuals/HeightStrip";
import { UpperCellRange } from "../visuals/UpperCellRange";
import { NmaxStaircase } from "../visuals/NmaxStaircase";
import { NecklaceExplorer } from "./NecklaceExplorer";
import { FloorCut } from "../visuals/FloorCut";
import { IdealExponent } from "../visuals/IdealExponent";
import { ItineraryBeads } from "../visuals/ItineraryBeads";
import { LinkedWalk } from "../visuals/LinkedWalk";
import { MapDoors } from "../visuals/MapDoors";
import { MediaPlayer, MediaScrubber } from "./MediaControls";
import { Tex } from "./Tex";

const MAP_DEFAULT = 37n;
const AUTOPLAY_MS = 550;

function fieldHasFocus(target: EventTarget | null): boolean {
  if (!(target instanceof HTMLElement)) return false;
  if (target.isContentEditable) return true;
  const tag = target.tagName;
  if (tag === "TEXTAREA" || tag === "SELECT") return true;
  if (tag !== "INPUT") return false;
  return (target as HTMLInputElement).type !== "range";
}

function useLatest<T>(value: T) {
  const ref = useRef(value);
  useEffect(() => {
    ref.current = value;
  });
  return ref;
}

function chipHover(
  label: string | undefined,
  value: bigint,
  note: string,
  numbered: boolean,
): string {
  if (!numbered) return note;
  const extra = label && label !== value.toString() ? label : "";
  return extra ? `${extra} — ${note}` : note;
}

function Chip({
  selected,
  tone = "live",
  title,
  onClick,
  children,
}: {
  selected: boolean;
  tone?: "live" | "monster";
  title?: string;
  onClick: () => void;
  children: string;
}) {
  const active =
    tone === "monster" ? "bg-odd text-card" : "bg-deep text-card";
  return (
    <button
      type="button"
      title={title}
      className={`rounded-full px-2.5 py-0.5 font-mono text-sm ${
        selected ? active : "border border-line bg-card text-ink"
      }`}
      onClick={onClick}
    >
      {children}
    </button>
  );
}

export type MapFrame = {
  prefix: string;
  odds: number;
  length: number;
  regime: ReturnType<typeof regimeOf>;
  stepIndex: number;
  seed: bigint;
  image: bigint;
  states: bigint[];
};

type StartChip = {
  value: bigint;
  note: string;
  label?: string;
};

export function MapWidget({
  initial = MAP_DEFAULT,
  initialStep = 0,
  side,
  below,
  showEnvelope = false,
  liveStarts = LIVE_STARTS,
  monsterStarts,
  useChipLabels = false,
  presetHint = "Ideas the browser can walk, and shipped monsters that outgrow that walker. Pictures only: hitting 1 is not a theorem.",
}: {
  initial?: bigint;
  initialStep?: number;
  side?: (frame: MapFrame) => ReactNode;
  below?: (frame: MapFrame) => ReactNode;
  showEnvelope?: boolean;
  liveStarts?: readonly StartChip[];
  monsterStarts?: readonly StartChip[];
  useChipLabels?: boolean;
  presetHint?: string;
} = {}) {
  const opening = resolveTrajectory(initial, TRAJECTORY_STEPS_MAX);
  const openingCursor =
    opening.states[Math.min(Math.max(initialStep, 0), Math.max(opening.states.length - 1, 0))] ??
    initial;
  const [startText, setStartText] = useState(initial.toString());
  const [cursor, setCursor] = useState(openingCursor);
  const [playing, setPlaying] = useState(false);
  const start = parsePositiveInt(startText);
  const seed = start ?? MAP_DEFAULT;
  const trajectory = resolveTrajectory(seed, TRAJECTORY_STEPS_MAX);
  const letter = letterOf(cursor);
  const active = trajectory.states.findIndex((state) => state === cursor);
  const stepIndex = active >= 0 ? active : 0;
  const stepLast = Math.max(trajectory.states.length - 1, 0);
  const prev = stepIndex > 0 ? trajectory.states[stepIndex - 1] : null;
  const nextFromPath =
    active >= 0 && active + 1 < trajectory.states.length ? trajectory.states[active + 1] : null;
  const next =
    nextFromPath ??
    (active < 0 && trajectory.source === "live" && cursor >= 1n ? floorPower(cursor) : null);
  useEffect(() => {
    if (!playing) return;
    const path = resolveTrajectory(seed, TRAJECTORY_STEPS_MAX).states;
    const id = window.setInterval(() => {
      setCursor((current) => {
        const index = path.findIndex((state) => state === current);
        const following = index >= 0 ? path[index + 1] : undefined;
        if (following === undefined) {
          setPlaying(false);
          return current;
        }
        return following;
      });
    }, AUTOPLAY_MS);
    return () => window.clearInterval(id);
  }, [playing, seed]);

  function chooseStart(value: bigint) {
    setStartText(value.toString());
    setCursor(value);
    setPlaying(true);
  }

  const playCurrent = useCallback(() => {
    if (playing) {
      setPlaying(false);
      return;
    }
    const path = resolveTrajectory(seed, TRAJECTORY_STEPS_MAX).states;
    const atEnd = next === null || cursor === path[path.length - 1];
    if (atEnd) setCursor(seed);
    setPlaying(true);
  }, [cursor, next, playing, seed]);

  const seekTo = useCallback(
    (index: number) => {
      const clamped = Math.max(0, Math.min(stepLast, index));
      const state = trajectory.states[clamped];
      if (state !== undefined) setCursor(state);
    },
    [stepLast, trajectory.states],
  );

  const keysRef = useLatest({ playCurrent, seekTo, stepIndex, next });

  useEffect(() => {
    function onKey(event: KeyboardEvent) {
      if (event.altKey || event.ctrlKey || event.metaKey) return;
      if (fieldHasFocus(event.target)) return;
      const frame = keysRef.current;
      if (event.key === "ArrowLeft") {
        event.preventDefault();
        setPlaying(false);
        if (frame.stepIndex === 0) return;
        frame.seekTo(frame.stepIndex - 1);
        return;
      }
      if (event.key === "ArrowRight") {
        event.preventDefault();
        setPlaying(false);
        if (frame.next === null) return;
        setCursor(frame.next);
        return;
      }
      if (event.key === " " || event.code === "Space") {
        event.preventDefault();
        frame.playCurrent();
      }
    }

    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [keysRef]);

  const prefix = trajectory.itinerary.slice(0, Math.max(stepIndex, 0));
  const prefixOdds = oddCount(prefix);
  const frame: MapFrame = {
    prefix,
    odds: prefixOdds,
    length: prefix.length,
    regime: regimeOf(prefix.length, prefixOdds),
    stepIndex,
    seed,
    image: cursor,
    states: trajectory.states.slice(0, Math.max(stepIndex, 0) + 1),
  };

  return (
    <div className="min-w-0 space-y-4">
      <MapDoors
        states={trajectory.states}
        highlight={side ? null : letter === "O" ? "odd" : "even"}
        active={active >= 0 ? active : undefined}
        sparseScale={trajectory.source === "monster"}
        stepComputation={side ? undefined : <FloorCut compact n={cursor} result={next} />}
        side={side?.(frame)}
        fillPlot={Boolean(side)}
        envelopeLogs={showEnvelope ? envelopeLog10Series(seed, trajectory.states) : undefined}
        onSelect={(index) => {
          setPlaying(false);
          seekTo(index);
        }}
        controls={
          <div className="flex flex-wrap items-start gap-x-12 gap-y-4">
            <label className="grid gap-1">
              <span className="text-xs uppercase tracking-wide text-muted">
                Starting number
              </span>
              <input
                className="start-input min-w-64 max-w-full rounded-xl border-2 border-ink bg-card px-3 py-2 font-mono text-3xl leading-none text-ink"
                style={{ width: `calc(${Math.max(10, startText.length)}ch + 1.5rem)` }}
                type="number"
                min={1}
                value={startText}
                onChange={(event) => {
                  const text = event.target.value;
                  setPlaying(false);
                  setStartText(text);
                  const value = parsePositiveInt(text);
                  if (value !== null) setCursor(value);
                }}
              />
            </label>
            <div className="grid min-w-0 flex-1 gap-1.5">
              <p
                className="text-xs uppercase tracking-wide text-muted"
                title={presetHint}
              >
                Interesting presets
              </p>
              <div className="flex flex-wrap items-center gap-1.5">
                <span
                  className="w-6 text-center text-base leading-none"
                  title="Live starts the browser can walk under 256 bits."
                  aria-label="Ideas"
                >
                  ⚡
                </span>
                {liveStarts.map((preset) => (
                  <Chip
                    key={preset.value.toString()}
                    selected={seed === preset.value}
                    title={chipHover(preset.label, preset.value, preset.note, useChipLabels)}
                    onClick={() => chooseStart(preset.value)}
                  >
                    {useChipLabels ? preset.value.toString() : (preset.label ?? preset.value.toString())}
                  </Chip>
                ))}
              </div>
              {monsterStarts !== undefined && monsterStarts.length === 0 ? null : (
              <div className="flex flex-wrap items-center gap-1.5">
                <span
                  className="w-6 text-center text-base leading-none"
                  title="Shipped trajectories whose peak exceeds the live 256-bit walker, plus the even tower 2^32."
                  aria-label="Monsters"
                >
                  👹
                </span>
                {(monsterStarts ?? [
                  ...MONSTER_ROW_LIVE.map((preset) => ({
                    value: preset.value,
                    note: preset.note,
                    label: preset.label,
                  })),
                  ...monsterCatalog().map((preset) => ({
                    value: preset.n,
                    note: preset.blurb,
                    label: preset.n.toString(),
                  })),
                ]).map((preset) => (
                  <Chip
                    key={preset.value.toString()}
                    selected={seed === preset.value}
                    tone="monster"
                    title={chipHover(preset.label, preset.value, preset.note, useChipLabels)}
                    onClick={() => chooseStart(preset.value)}
                  >
                    {useChipLabels ? preset.value.toString() : (preset.label ?? preset.value.toString())}
                  </Chip>
                ))}
              </div>
              )}
            </div>
          </div>
        }
        axis={
          <MediaScrubber
            value={stepIndex}
            min={0}
            max={stepLast}
            onSeek={(index) => {
              setPlaying(false);
              seekTo(index);
            }}
          />
        }
        player={
          <MediaPlayer
            playing={playing}
            prevLabel={prev === null ? "" : formatInt(prev)}
            nextLabel={next === null ? "" : formatInt(next)}
            firstDisabled={stepIndex === 0}
            prevDisabled={stepIndex === 0}
            nextDisabled={next === null}
            lastDisabled={stepIndex === stepLast}
            onFirst={() => {
              setPlaying(false);
              setCursor(seed);
            }}
            onPrev={() => {
              setPlaying(false);
              seekTo(stepIndex - 1);
            }}
            onPlay={playCurrent}
            onNext={() => {
              setPlaying(false);
              if (next !== null) setCursor(next);
            }}
            onLast={() => {
              setPlaying(false);
              seekTo(stepLast);
            }}
          />
        }
      />
      {side ? (
        <div className="space-y-3">
          <div className="rounded-2xl border border-line bg-card px-4 py-3">
            <ItineraryBeads
              word={prefix}
              onSelect={(index) => {
                setPlaying(false);
                seekTo(index + 1);
              }}
            />
          </div>
          <div className="rounded-2xl border border-line bg-paper/70 px-4 py-3">
            {below ? (
              below(frame)
            ) : prefix.length === 0 ? (
              <>
                <p className="text-xs uppercase tracking-wide text-muted">
                  Ideal exponent
                </p>
                <p className="mt-2 text-sm text-ink">
                  Ignoring floors, o odd letters and length L multiply n by{" "}
                  3<sup>o</sup>/2<sup>L</sup>. Floors only discard decimals, so a
                  contracting prefix still cannot close. Play to write the word.
                </p>
              </>
            ) : (
              <IdealExponent
                odds={prefixOdds}
                length={prefix.length}
                start={seed}
                showScale={false}
              />
            )}
          </div>
        </div>
      ) : (
        <LinkedWalk
          states={trajectory.states}
          itinerary={trajectory.itinerary}
          active={stepIndex}
          onSeek={(index) => {
            setPlaying(false);
            seekTo(index);
          }}
          note={
            trajectory.source === "monster"
              ? `Shipped trajectory${trajectory.peakBits ? ` (peak ${trajectory.peakBits} bits)` : ""}. The browser did not walk this start. ${trajectory.blurb ?? ""} Hitting 1 is not a theorem.`
              : trajectory.bitCapped
                ? "A value exceeded the live 256-bit cap. Famous larger starts are under Monsters if we shipped them."
                : trajectory.reachedOne && stepIndex >= trajectory.itinerary.length
                  ? "This walk hit 1, which is not a theorem."
                  : null
          }
        />
      )}
    </div>
  );
}

export function CycleWidget() {
  return <CycleTourWidget />;
}

export function LeftoversWidget() {
  return <LeftoverWidget />;
}

export function ExpandingWidget() {
  return (
    <MapWidget
      initial={37n}
      initialStep={5}
      liveStarts={EXPANDING_STARTS}
      monsterStarts={EXPANDING_MONSTERS}
      useChipLabels
      presetHint="Starts chosen to show 3^o against 2^L. Hitting 1 is not a theorem."
      side={(frame) => (
        <RegimeDoors
          odds={frame.odds}
          length={frame.length}
          regime={frame.regime}
        />
      )}
    />
  );
}

export function EnvelopeWidget() {
  return (
    <MapWidget
      initial={3n}
      liveStarts={ENVELOPE_STARTS}
      monsterStarts={ENVELOPE_MONSTERS}
      showEnvelope
      presetHint="Starts chosen to show the realized ceiling and slack. Hitting 1 is not a theorem."
      side={(frame) => (
        <EnvelopeSlack
          seed={frame.seed}
          image={frame.image}
          odds={frame.odds}
          length={frame.length}
        />
      )}
      below={(frame) => (
        <EnvelopePanel
          seed={frame.seed}
          image={frame.image}
          odds={frame.odds}
          length={frame.length}
        />
      )}
    />
  );
}

export function FloorWidget() {
  return (
    <div className="space-y-3">
      <FloorLadder />
      <p className="text-sm text-muted">
        These four numbers are certified computations already finished. The
        next useful floor 5.54·10⁸ is parked; this page does not raise N₀.
      </p>
    </div>
  );
}

function Movement({
  number,
  title,
  question,
  children,
}: {
  number: number;
  title: string;
  question: string;
  children: ReactNode;
}) {
  return (
    <section className="space-y-3">
      <header className="flex flex-wrap items-baseline gap-x-3 gap-y-1">
        <span className="font-mono text-xs uppercase tracking-[0.18em] text-muted">
          Movement {number}
        </span>
        <h3 className="font-serif text-xl">{title}</h3>
        <span className="text-sm text-muted">{question}</span>
      </header>
      {children}
    </section>
  );
}

export function FinanceWidget() {
  const { financeL, setFinanceL } = usePlayState();
  const view = financeView(financeL);
  return (
    <div className="space-y-8">
      <Movement number={1} title="The necklace" question="what does a cycle look like at its minimum?">
        <NecklaceExplorer compact />
        <p className="text-sm text-muted">
          Rotate a hypothetical cycle to its smallest value n and read it round the
          circle: one turn is the word, the angle is the step, the radius is the value.
          Each block OᵃE leaves a valley, climbs to an even peak, and drops. The first
          peak must clear the outer ring (n+1)²; the last peak must land in the thin
          band [n²+1, (n+1)²) so that one square root returns exactly to n and the curve
          closes at the top. Real walks show the miss: the curve either spirals outward
          or falls inside the ring n.
        </p>
      </Movement>
      <Movement number={2} title="The ledger" question="why must the surplus be paid?">
        <Tex display>{String.raw`n\log n\cdot(3^o-2^L)\le L\cdot 3^o\qquad\Longleftrightarrow\qquad \theta(L)=1-\frac{2^L}{3^o}\le\frac{L}{n\log n}`}</Tex>
        <FinanceBalance length={financeL} compact />
        <div className="flex flex-wrap items-center gap-2 text-sm text-muted">
          <span>Length</span>
          <select
            className="rounded border border-line bg-card px-2 py-1 font-mono"
            value={RECORD_LENGTHS.includes(financeL as (typeof RECORD_LENGTHS)[number]) ? financeL : ""}
            onChange={(event) => {
              if (event.target.value) setFinanceL(Number(event.target.value));
            }}
          >
            {RECORD_LENGTHS.includes(financeL as (typeof RECORD_LENGTHS)[number]) ? null : (
              <option value="">{financeL.toLocaleString("en-US")}</option>
            )}
            {RECORD_LENGTHS.map((item) => (
              <option key={item} value={item}>
                {item.toLocaleString("en-US")}
              </option>
            ))}
          </select>
          <span>
            — o_min {view.oMin === null ? "—" : view.oMin.toLocaleString("en-US")}, shipped n_max{" "}
            {view.nMax === null ? "not tabulated" : view.nMax.toLocaleString("en-US")}
          </span>
        </div>
        <FinanceHierarchy />
      </Movement>
      <Movement number={3} title="The staircase" question="where does the floor cut the lengths?">
        <NmaxStaircase selected={financeL} onSelect={setFinanceL} compact />
        <p className="text-sm text-muted">
          Each record raises the bar n_max(L) a cycle minimum would have to sit under.
          The floor 10⁶ is the line already searched: every length whose bar is below
          it is dead. The first length to clear the line is 25,781; the 141 that clear
          it before 100,000 are the finance survivors, and they sit on a two-vector
          lattice around the convergents of log 2 / log 3. A survivor is a length the
          inequality did not kill, not a candidate cycle.
        </p>
      </Movement>
    </div>
  );
}

export function RunSuffixWidget() {
  return <RunSuffixExplorer compact />;
}

export function GapTransferWidget() {
  return <GapTransferExplorer compact />;
}

export function WalkChargeWidget() {
  return <WalkChargeExplorer compact />;
}

export function FanWidget() {
  return <FanExplorer compact />;
}

export function CubicBandWidget() {
  return (
    <div className="space-y-3">
      <CubicBandOrder />
      <p className="text-sm text-muted">
        Sorted odds then evens, rotated by the even count. The leftover
        counts force that mechanical word only if M stays below m³.
      </p>
    </div>
  );
}

export function HeightGapWidget() {
  return (
    <div className="space-y-3">
      <HeightStrip />
      <p className="text-sm text-muted">
        Each strip is a necessary ceiling on the maximum. None of them
        raises the period 780,239.
      </p>
    </div>
  );
}

export function UpperCellsWidget() {
  return (
    <div className="space-y-3">
      <UpperCellRange />
      <p className="text-sm text-muted">
        The leftover length still survives. The signed first-triple test
        remains open.
      </p>
    </div>
  );
}
