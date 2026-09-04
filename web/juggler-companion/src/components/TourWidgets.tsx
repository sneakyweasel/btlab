import { useCallback, useEffect, useMemo, useRef, useState, type ReactNode } from "react";
import {
  LIVE_STARTS,
  MONSTER_ROW_LIVE,
  PRODUCTION_M_MAX,
  PRODUCTION_SEEDS,
  RECORD_LENGTHS,
  TOUR_EVEN_BLOCK_M,
  TOUR_OE_FIBER_M,
  TRAJECTORY_STEPS_MAX,
} from "../juggler/constants";
import { oddPreimages } from "../juggler/preimages";
import { evenBlockView, fiberView, randomEvenInBlock } from "../juggler/productions";
import { usePlayState } from "../context/PlayState";
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
import { EvenBlockStrip } from "../visuals/EvenBlockStrip";
import { OeFiberStrip } from "../visuals/OeFiberStrip";
import { ProductionWork } from "../visuals/ProductionWork";
import { SweepLane } from "../visuals/SweepLane";
import { CycleTourWidget, LeftoverWidget } from "./CycleTourWidget";
import { EnvelopeCeiling } from "../visuals/EnvelopeCeiling";
import { FinanceBalance, FinanceHierarchy } from "../visuals/FinanceBalance";
import { FloorLadder } from "../visuals/FloorLadder";
import { NmaxStaircase } from "../visuals/NmaxStaircase";
import { NecklaceExplorer } from "./NecklaceExplorer";
import { FloorCut } from "../visuals/FloorCut";
import { LinkedWalk } from "../visuals/LinkedWalk";
import { MapDoors } from "../visuals/MapDoors";
import { SurplusScale } from "../visuals/SurplusScale";
import { WalkChargePipeline } from "../visuals/WalkChargePipeline";
import { MediaControls, MediaPlayer, MediaScrubber } from "./MediaControls";
import { Metric } from "./Metric";
import { Tex } from "./Tex";

const MAP_DEFAULT = 37n;
const AUTOPLAY_MS = 550;
const EVEN_BLOCK_PLAY_LO = 1;
const EVEN_BLOCK_PLAY_HI = 20;

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

  const keysRef = useRef({ playCurrent, seekTo, stepIndex, next });
  keysRef.current = { playCurrent, seekTo, stepIndex, next };

  useEffect(() => {
    function fieldHasFocus(target: EventTarget | null): boolean {
      if (!(target instanceof HTMLElement)) return false;
      if (target.isContentEditable) return true;
      const tag = target.tagName;
      if (tag === "TEXTAREA" || tag === "SELECT") return true;
      if (tag !== "INPUT") return false;
      return (target as HTMLInputElement).type !== "range";
    }

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
  }, []);

  return (
    <div className="min-w-0 space-y-4">
      <MapDoors
        states={trajectory.states}
        highlight={letter === "O" ? "odd" : "even"}
        active={active >= 0 ? active : undefined}
        sparseScale={trajectory.source === "monster"}
        stepComputation={<FloorCut compact n={cursor} result={next} />}
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
                title="Ideas the browser can walk, and shipped monsters that outgrow that walker. Pictures only: hitting 1 is not a theorem."
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
                  title="Shipped trajectories whose peak exceeds the live 256-bit walker, plus the even tower 2^32."
                  aria-label="Monsters"
                >
                  👹
                </span>
                {MONSTER_ROW_LIVE.map((preset) => (
                  <Chip
                    key={preset.value.toString()}
                    selected={seed === preset.value}
                    tone="monster"
                    title={preset.note}
                    onClick={() => chooseStart(preset.value)}
                  >
                    {preset.label}
                  </Chip>
                ))}
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
  const [startText, setStartText] = useState(String(TOUR_EVEN_BLOCK_M));
  const [m, setM] = useState(TOUR_EVEN_BLOCK_M);
  const [playing, setPlaying] = useState(false);
  const block = useMemo(() => evenBlockView(m), [m]);
  const oddParent = useMemo(() => oddPreimages(m)[0] ?? null, [m]);
  const fiber = fiberView(TOUR_OE_FIBER_M);
  const firstSea = fiber.points.find((point) => point.imageEven)?.n ?? fiber.points[0]?.n ?? 0;
  const [blockN, setBlockN] = useState<number | null>(() =>
    randomEvenInBlock(evenBlockView(TOUR_EVEN_BLOCK_M)),
  );
  const [fiberN, setFiberN] = useState(firstSea);
  const [fiberHover, setFiberHover] = useState<number | null>(null);
  const fiberInspect = fiberHover ?? fiberN;
  const parsed = parsePositiveInt(startText);
  const startError =
    startText.trim() === ""
      ? null
      : parsed === null
        ? "Enter a positive integer."
        : parsed > BigInt(PRODUCTION_M_MAX)
          ? `At most ${PRODUCTION_M_MAX.toLocaleString("en-US")} on this page.`
          : null;
  const inPlayRange = m >= EVEN_BLOCK_PLAY_LO && m <= EVEN_BLOCK_PLAY_HI;
  const playValue = inPlayRange ? m : EVEN_BLOCK_PLAY_LO;
  const chooseM = useCallback((value: number) => {
    setPlaying(false);
    setStartText(String(value));
    setM(value);
    const next = evenBlockView(value);
    setBlockN(randomEvenInBlock(next));
  }, []);
  const seekPlay = useCallback((value: number) => {
    setPlaying(false);
    const span = EVEN_BLOCK_PLAY_HI - EVEN_BLOCK_PLAY_LO + 1;
    const wrapped =
      EVEN_BLOCK_PLAY_LO +
      ((((value - EVEN_BLOCK_PLAY_LO) % span) + span) % span);
    setStartText(String(wrapped));
    setM(wrapped);
    const next = evenBlockView(wrapped);
    setBlockN(randomEvenInBlock(next));
  }, []);
  const playCurrent = useCallback(() => {
    if (playing) {
      setPlaying(false);
      return;
    }
    if (!inPlayRange) {
      setStartText(String(EVEN_BLOCK_PLAY_LO));
      setM(EVEN_BLOCK_PLAY_LO);
      const next = evenBlockView(EVEN_BLOCK_PLAY_LO);
      setBlockN(randomEvenInBlock(next));
    }
    setPlaying(true);
  }, [inPlayRange, playing]);
  useEffect(() => {
    if (!playing) return;
    const id = window.setInterval(() => {
      setM((current) => {
        const next =
          current >= EVEN_BLOCK_PLAY_HI || current < EVEN_BLOCK_PLAY_LO
            ? EVEN_BLOCK_PLAY_LO
            : current + 1;
        setStartText(String(next));
        const view = evenBlockView(next);
        setBlockN(randomEvenInBlock(view));
        return next;
      });
    }, AUTOPLAY_MS);
    return () => window.clearInterval(id);
  }, [playing]);
  const keysRef = useRef({ playCurrent, seekPlay, playValue });
  keysRef.current = { playCurrent, seekPlay, playValue };
  useEffect(() => {
    function fieldHasFocus(target: EventTarget | null): boolean {
      if (!(target instanceof HTMLElement)) return false;
      if (target.isContentEditable) return true;
      const tag = target.tagName;
      if (tag === "TEXTAREA" || tag === "SELECT") return true;
      if (tag !== "INPUT") return false;
      return (target as HTMLInputElement).type !== "range";
    }
    function onKey(event: KeyboardEvent) {
      if (event.altKey || event.ctrlKey || event.metaKey) return;
      if (fieldHasFocus(event.target)) return;
      const frame = keysRef.current;
      if (event.key === "ArrowLeft") {
        event.preventDefault();
        frame.seekPlay(frame.playValue - 1);
        return;
      }
      if (event.key === "ArrowRight") {
        event.preventDefault();
        frame.seekPlay(frame.playValue + 1);
        return;
      }
      if (event.key === " " || event.code === "Space") {
        event.preventDefault();
        frame.playCurrent();
      }
    }
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, []);
  return (
    <div className="space-y-6">
      <div>
        <h3 className="mb-2 font-serif text-lg">Even block of {formatInt(m)}</h3>
        <p className="text-sm text-muted">
          The even block of {formatInt(m)} is the set of even one-step
          preimages of {formatInt(m)}: every even n in [{formatInt(m)}²,{" "}
          {formatInt(m + 1)}²) = [{formatInt(block.lo)}, {formatInt(block.hi)}
          ). If {formatInt(m)} is in a backward-closed set A, so is this block.
        </p>
        <p className="mb-4 text-sm text-muted">
          {oddParent === null
            ? `${formatInt(m)} has no odd one-step precursor.`
            : `The unique odd precursor of ${formatInt(m)} is ${formatInt(oddParent)}.`}
        </p>
        <div className="mb-4 rounded-2xl border border-line bg-paper px-4 py-2.5">
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
                max={PRODUCTION_M_MAX}
                value={startText}
                onChange={(event) => {
                  const text = event.target.value;
                  setStartText(text);
                  const value = parsePositiveInt(text);
                  if (value !== null && value <= BigInt(PRODUCTION_M_MAX)) {
                    chooseM(Number(value));
                  }
                }}
              />
              {startError ? (
                <span className="text-sm text-warn">{startError}</span>
              ) : null}
            </label>
            <div className="grid min-w-0 flex-1 gap-1.5">
              <p className="text-xs uppercase tracking-wide text-muted">
                Interesting presets
              </p>
              <div className="flex flex-wrap items-center gap-1.5">
                {PRODUCTION_SEEDS.map((preset) => (
                  <Chip
                    key={preset.value}
                    selected={m === preset.value}
                    title={preset.note}
                    onClick={() => chooseM(preset.value)}
                  >
                    {preset.value.toString()}
                  </Chip>
                ))}
              </div>
            </div>
          </div>
        </div>
        <EvenBlockStrip
          view={block}
          selected={blockN}
          onSelect={setBlockN}
        />
        <div className="mt-3">
          <MediaControls
            value={playValue}
            min={EVEN_BLOCK_PLAY_LO}
            max={EVEN_BLOCK_PLAY_HI}
            playing={playing}
            loop
            prevLabel={formatInt(
              playValue <= EVEN_BLOCK_PLAY_LO
                ? EVEN_BLOCK_PLAY_HI
                : playValue - 1,
            )}
            nextLabel={formatInt(
              playValue >= EVEN_BLOCK_PLAY_HI
                ? EVEN_BLOCK_PLAY_LO
                : playValue + 1,
            )}
            onSeek={seekPlay}
            onPlay={playCurrent}
          />
        </div>
      </div>
      <div>
        <h3 className="mb-2 font-serif text-lg">OE fiber of 100,000</h3>
        <OeFiberStrip
          view={fiber}
          selected={fiberN}
          onSelect={setFiberN}
          onHover={setFiberHover}
        />
        <SweepLane
          points={fiber.points}
          selected={fiberN}
          onSelect={setFiberN}
          onHover={setFiberHover}
        />
        <ProductionWork n={fiberInspect} />
        <p className="mt-3 text-sm text-muted">
          H = {fiber.H} odd n, G = {fiber.G} with even image. The odd step
          grows, the even step drops to 100000. Ember beads are on the fiber
          but not this production. An odd image still has at most one odd
          parent.
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
