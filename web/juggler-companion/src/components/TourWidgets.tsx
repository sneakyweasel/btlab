import { useEffect, useMemo, useState, type ReactNode } from "react";
import { evenPreimage, oddPreimageIntegers } from "../juggler/preimages";
import { LIVE_STARTS, NOTE_TRAJECTORY_3, TRAJECTORY_STEPS_MAX } from "../juggler/constants";
import { financeView } from "../juggler/finance";
import { formatInt, parsePositiveInt } from "../juggler/format";
import { floorPower, letterOf } from "../juggler/map";
import { monsterCatalog, resolveTrajectory } from "../juggler/monsters";
import {
  envelopeSlack,
  expanding,
  followsItinerary,
  imageAfter,
  oddCount,
  parseItinerary,
  regimeOf,
} from "../juggler/itinerary";
import { PreimageNumberLine } from "../visuals/PreimageNumberLine";
import { CycleTourWidget } from "./CycleTourWidget";
import { EnvelopeCeiling } from "../visuals/EnvelopeCeiling";
import { FloorLadder } from "../visuals/FloorLadder";
import { AppearingItinerary } from "../visuals/AppearingItinerary";
import { FloorCut } from "../visuals/FloorCut";
import { MapDoors } from "../visuals/MapDoors";
import { TrajectoryBeads } from "../visuals/TrajectoryBeads";
import { SurplusScale } from "../visuals/SurplusScale";
import { WalkChargePipeline } from "../visuals/WalkChargePipeline";
import { Metric } from "./Metric";
import { Tex } from "./Tex";

const MAP_DEFAULT = 37n;
const AUTOPLAY_MS = 550;

function FrameIcon({
  children,
  large,
}: {
  children: ReactNode;
  large?: boolean;
}) {
  return (
    <svg
      viewBox="0 0 16 16"
      className={large ? "h-4 w-4" : "h-3.5 w-3.5"}
      fill="currentColor"
      aria-hidden
    >
      {children}
    </svg>
  );
}

function IconFirst() {
  return (
    <FrameIcon>
      <rect x="2" y="3" width="2" height="10" rx="0.4" />
      <path d="M14 3.2v9.6L6.2 8z" />
    </FrameIcon>
  );
}

function IconPrevFrame() {
  return (
    <FrameIcon>
      <path d="M12.4 3.2v9.6L4.2 8z" />
    </FrameIcon>
  );
}

function IconPlay() {
  return (
    <FrameIcon large>
      <path d="M4 2.8v10.4L13.6 8z" />
    </FrameIcon>
  );
}

function IconPause() {
  return (
    <FrameIcon large>
      <rect x="3.4" y="3" width="3" height="10" rx="0.5" />
      <rect x="9.6" y="3" width="3" height="10" rx="0.5" />
    </FrameIcon>
  );
}

function IconNextFrame() {
  return (
    <FrameIcon>
      <path d="M3.6 3.2v9.6L11.8 8z" />
    </FrameIcon>
  );
}

function IconLast() {
  return (
    <FrameIcon>
      <path d="M2 3.2v9.6L9.8 8z" />
      <rect x="12" y="3" width="2" height="10" rx="0.4" />
    </FrameIcon>
  );
}

function Transport({
  label,
  disabled,
  primary,
  onClick,
  children,
}: {
  label: string;
  disabled?: boolean;
  primary?: boolean;
  onClick: () => void;
  children: ReactNode;
}) {
  return (
    <button
      type="button"
      aria-label={label}
      title={label}
      disabled={disabled}
      onClick={onClick}
      className={
        primary
          ? "flex h-9 w-9 items-center justify-center rounded-full bg-deep text-card disabled:opacity-40"
          : "flex h-8 w-8 items-center justify-center rounded-full text-ink disabled:opacity-35 hover:bg-line/50"
      }
    >
      {children}
    </button>
  );
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

export function MapWidget() {
  const [startText, setStartText] = useState(MAP_DEFAULT.toString());
  const [cursor, setCursor] = useState(MAP_DEFAULT);
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
  const progressPct = stepLast === 0 ? 0 : (100 * stepIndex) / stepLast;
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
    setPlaying(false);
    setStartText(value.toString());
    setCursor(value);
  }

  function playCurrent() {
    if (playing) {
      setPlaying(false);
      return;
    }
    const path = resolveTrajectory(seed, TRAJECTORY_STEPS_MAX).states;
    const atEnd = next === null || cursor === path[path.length - 1];
    if (atEnd) setCursor(seed);
    setPlaying(true);
  }

  function seekTo(index: number) {
    const clamped = Math.max(0, Math.min(stepLast, index));
    const state = trajectory.states[clamped];
    if (state !== undefined) setCursor(state);
  }

  return (
    <div className="space-y-4">
      <MapDoors
        states={trajectory.states}
        highlight={letter === "O" ? "odd" : "even"}
        active={active >= 0 ? active : undefined}
        sparseScale={trajectory.source === "monster"}
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
                title="Ideas the browser can walk — including even towers of nested square roots — and shipped monsters that outgrow that walker. Pictures only: hitting 1 is not a theorem."
              >
                Interesting presets
              </p>
              <div className="flex flex-wrap items-center gap-1.5">
                <span
                  className="w-6 text-center text-base leading-none"
                  title="Live starts the browser can walk, including even towers, under 256 bits."
                  aria-label="Ideas"
                >
                  ⚡
                </span>
                {LIVE_STARTS.map((preset) => (
                  <Chip
                    key={preset.value.toString()}
                    selected={seed === preset.value}
                    title={preset.note}
                    onClick={() => chooseStart(preset.value)}
                  >
                    {preset.value.toString()}
                  </Chip>
                ))}
              </div>
              <div className="flex flex-wrap items-center gap-1.5">
                <span
                  className="w-6 text-center text-base leading-none"
                  title="Shipped trajectories whose peak exceeds the live 256-bit walker."
                  aria-label="Monsters"
                >
                  👹
                </span>
                {monsterCatalog().map((preset) => (
                  <Chip
                    key={preset.n.toString()}
                    selected={seed === preset.n}
                    tone="monster"
                    title={preset.blurb}
                    onClick={() => chooseStart(preset.n)}
                  >
                    {preset.n.toString()}
                  </Chip>
                ))}
              </div>
            </div>
          </div>
        }
        axis={
          <div className="relative flex h-4 items-center">
            <div className="pointer-events-none absolute inset-x-0 h-1 rounded-full bg-line" />
            <div
              className="pointer-events-none absolute left-0 h-1 rounded-full bg-deep"
              style={{ width: `${progressPct}%` }}
            />
            <input
              className="trajectory-scrubber relative z-10"
              type="range"
              min={0}
              max={stepLast}
              step={1}
              value={stepIndex}
              aria-label="Frame"
              aria-valuemin={0}
              aria-valuemax={stepLast}
              aria-valuenow={stepIndex}
              onChange={(event) => seekTo(Number(event.target.value))}
            />
          </div>
        }
        player={
          <div className="flex w-full items-center justify-center gap-3">
            <p className="min-w-0 flex-1 text-right font-mono text-sm leading-tight break-all text-muted">
              {prev === null ? "" : formatInt(prev)}
            </p>
            <div className="flex shrink-0 items-center gap-0.5">
              <Transport
                label="First frame"
                disabled={stepIndex === 0}
                onClick={() => {
                  setPlaying(false);
                  setCursor(seed);
                }}
              >
                <IconFirst />
              </Transport>
              <Transport
                label="Previous frame"
                disabled={stepIndex === 0}
                onClick={() => {
                  setPlaying(false);
                  seekTo(stepIndex - 1);
                }}
              >
                <IconPrevFrame />
              </Transport>
              <Transport label={playing ? "Pause" : "Play"} primary onClick={playCurrent}>
                {playing ? <IconPause /> : <IconPlay />}
              </Transport>
              <Transport
                label="Next frame"
                disabled={next === null}
                onClick={() => {
                  setPlaying(false);
                  if (next !== null) setCursor(next);
                }}
              >
                <IconNextFrame />
              </Transport>
              <Transport
                label="Last frame"
                disabled={stepIndex === stepLast}
                onClick={() => {
                  setPlaying(false);
                  seekTo(stepLast);
                }}
              >
                <IconLast />
              </Transport>
            </div>
            <p className="min-w-0 flex-1 font-mono text-sm leading-tight break-all text-muted">
              {next === null ? "" : formatInt(next)}
            </p>
          </div>
        }
      />
      <div className="grid gap-3 sm:grid-cols-2 sm:items-stretch">
        <FloorCut n={cursor} result={next} />
        <AppearingItinerary
          itinerary={trajectory.itinerary}
          revealed={stepIndex}
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
      </div>
    </div>
  );
}

export function TrajectoryWidget() {
  const [shown, setShown] = useState<number>(NOTE_TRAJECTORY_3.length);
  const states = NOTE_TRAJECTORY_3.slice(0, shown);
  return (
    <div className="space-y-3">
      <TrajectoryBeads states={states} active={shown - 1} />
      <div className="flex gap-2">
        <button
          type="button"
          className="rounded-full bg-deep px-3 py-1 text-sm text-card"
          onClick={() => setShown((value) => Math.min(NOTE_TRAJECTORY_3.length, value + 1))}
        >
          Replay next
        </button>
        <button
          type="button"
          className="rounded-full border border-line px-3 py-1 text-sm"
          onClick={() => setShown(1)}
        >
          Restart
        </button>
      </div>
      <p className="text-sm text-muted">
        Itinerary so far:{" "}
        <span className="font-mono">
          {states.slice(0, -1).map((state) => letterOf(state)).join("") || "—"}
        </span>
        . Reaching 1 here is the trajectory of 3, not a halt theorem.
      </p>
    </div>
  );
}

export function CycleWidget() {
  return <CycleTourWidget />;
}

export function ExpandingWidget() {
  const [text, setText] = useState("OOE");
  const word = parseItinerary(text, 16) ?? "";
  const odds = oddCount(word);
  return (
    <div className="space-y-3">
      <SurplusScale odds={odds} length={word.length} />
      <label className="block text-sm text-muted">
        Short O/E itinerary
        <input
          className="mt-1 block w-full max-w-xs rounded border border-line bg-card px-2 py-1 font-mono"
          value={text}
          onChange={(event) => setText(event.target.value)}
        />
      </label>
      <p className="text-sm text-muted">
        {word
          ? `${word} is ${regimeOf(word.length, odds)}. Surplus 3^${odds} − 2^${word.length} = ${3 ** odds - 2 ** word.length}.`
          : "Type only O and E."}
      </p>
    </div>
  );
}

export function EnvelopeWidget() {
  const n = 5n;
  const word = "OOE";
  const follows = followsItinerary(n, word);
  const image = follows ? imageAfter(n, word) : null;
  const slack =
    image === null ? null : envelopeSlack(n, image, word.length, oddCount(word));
  const points = useMemo(() => {
    const path = [n];
    let current = n;
    for (let index = 0; index < word.length; index += 1) {
      current = floorPower(current);
      path.push(current);
    }
    return path.map((value) => Number(value));
  }, []);
  return (
    <div className="space-y-3">
      <EnvelopeCeiling points={points} />
      <div className="grid gap-3 sm:grid-cols-3">
        <Metric label="Start" value="5" hint="follows OOE" />
        <Metric label="Image" value={image === null ? "—" : image.toString()} />
        <Metric
          label="Slack Δ"
          value={slack === null ? "too large" : formatInt(slack)}
          hint="n^{9} − image^{8}"
        />
      </div>
      <p className="text-sm text-muted">
        {expanding(word) ? "OOE is expanding, so the ceiling sits above n." : ""}
        The walk is 5 → 11 → 36 → 6.
      </p>
    </div>
  );
}

export function PreimagesWidget() {
  const even = evenPreimage(6);
  const odds = oddPreimageIntegers(11);
  return (
    <div className="grid gap-6 md:grid-cols-2">
      <div>
        <h3 className="mb-2 font-serif text-lg">Even one-step preimage of 6</h3>
        <PreimageNumberLine lo={even.lo} hi={even.hi} marks={[36, 38, 40]} label="Even parents of 6" />
        <p className="text-sm text-muted">
          Even n in [{even.lo}, {even.hi}) all map to 6.
        </p>
      </div>
      <div>
        <h3 className="mb-2 font-serif text-lg">Odd one-step preimage of 11</h3>
        <PreimageNumberLine lo={4} hi={7} marks={odds} label="Odd parent of 11" />
        <p className="text-sm text-muted">
          At most one integer: here {odds[0] ?? "none"}.
        </p>
      </div>
    </div>
  );
}

export function FloorWidget() {
  return (
    <div className="space-y-3">
      <FloorLadder />
      <p className="text-sm text-muted">
        These three numbers are certified computations already finished. This
        page does not search for new floors.
      </p>
    </div>
  );
}

export function FinanceWidget() {
  const records = [11, 19, 84, 569, 1054, 25781];
  const [length, setLength] = useState(11);
  const view = financeView(length);
  return (
    <div className="space-y-3">
      <Tex display>{String.raw`n\log n\cdot(3^o-2^L)\le L\cdot 3^o`}</Tex>
      <label className="block text-sm text-muted">
        Record length
        <select
          className="ml-2 rounded border border-line bg-card px-2 py-1 font-mono"
          value={length}
          onChange={(event) => setLength(Number(event.target.value))}
        >
          {records.map((item) => (
            <option key={item} value={item}>
              {item}
            </option>
          ))}
        </select>
      </label>
      <div className="grid gap-3 sm:grid-cols-3">
        <Metric label="Status" value={view.status} />
        <Metric label="o_min" value={view.oMin === null ? "—" : String(view.oMin)} />
        <Metric
          label="n_max"
          value={view.nMax === null ? "—" : view.nMax.toLocaleString("en-US")}
          hint="from the shipped 6/5 table"
        />
      </div>
    </div>
  );
}

export function WalkChargeWidget() {
  return (
    <div className="space-y-3">
      <WalkChargePipeline />
      <p className="text-sm text-muted">
        A picture of §5, not a calculator. The site does not recompute hug
        charge, Ostrowski digits, or Denjoy–Koksma blocks.
      </p>
    </div>
  );
}
