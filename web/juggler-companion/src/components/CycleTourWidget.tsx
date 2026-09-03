import { memo, useCallback, useMemo, useState, type ReactNode } from "react";
import { Link } from "react-router-dom";
import { Tex } from "./Tex";
import {
  CYCLE_TOUR_PRESETS,
  TOUR_WORD_MAX,
} from "../juggler/constants";
import { type StemDisplayMode } from "../juggler/lollipop";
import {
  assembleFillCounts,
  cycleMinShape,
  formatNecklaceFill,
  formatOddEvenRuns,
  oddEvenRuns,
  parseItinerary,
  rotateItinerary,
  tryAssembleFill,
  type AssembleFillCounts,
  type CycleMinShape,
  type NecklaceFill,
} from "../juggler/itinerary";
import { CycleLollipop } from "../visuals/CycleLollipop";
import { CycleNecklace } from "../visuals/CycleNecklace";
import { OddEvenRunStrip } from "../visuals/OddEvenRunStrip";
import {
  IdealDecisionCard,
  IdealDecisionList,
  findDecision,
} from "./IdealDecisionList";
import { Metric } from "./Metric";

const DEFAULT_SHAPE = CYCLE_TOUR_PRESETS[0];

type TourWord = {
  parsed: string | null;
  stored: string;
  current: string;
  balloonWord: string;
  shift: number;
  minIndex: number;
  text: string;
  shape: CycleMinShape;
  balloonShape: CycleMinShape;
  currentFill: NecklaceFill | null;
  balloonFill: NecklaceFill | null;
  balloonFillCounts: AssembleFillCounts | null;
  currentRuns: number[] | null;
  balloonRuns: number[] | null;
  aligned: boolean;
};

const CycleTourLeftovers = memo(function CycleTourLeftovers({
  word,
  onChooseShape,
  onRotate,
  onSnap,
  onSelectIndex,
  onLeftover,
  onRun,
}: {
  word: TourWord;
  onChooseShape: (next: string, min: number) => void;
  onRotate: (delta: number) => void;
  onSnap: () => void;
  onSelectIndex: (index: number) => void;
  onLeftover: () => void;
  onRun: () => void;
}) {
  const {
    stored,
    current,
    shift,
    minIndex,
    text,
    shape,
    balloonShape,
    currentFill,
    balloonFill,
    balloonFillCounts,
    currentRuns,
    balloonRuns,
    aligned,
  } = word;
  return (
    <div className="space-y-5">
      <div>
        <p className="mb-1.5 text-xs uppercase tracking-wide text-muted">
          Cycle leftovers — not realized loops
        </p>
        <div className="flex flex-wrap items-center gap-1.5">
          {CYCLE_TOUR_PRESETS.map((preset) => (
            <button
              key={preset.id}
              type="button"
              title={preset.hint}
              className={`rounded-full px-2.5 py-0.5 font-mono text-sm ${
                text === preset.word && shift === 0
                  ? "bg-deep text-card"
                  : "border border-line bg-card text-ink"
              }`}
              onClick={() => {
                onChooseShape(preset.word, preset.minIndex);
                onLeftover();
              }}
            >
              {preset.label}
            </button>
          ))}
        </div>
      </div>
      <div
        className={`rounded-xl border px-3 py-2 text-sm ${
          balloonShape.cycleMinShaped
            ? "border-ok/40 bg-ok/10 text-ink"
            : aligned
              ? "border-warn/40 bg-warn/10 text-ink"
              : "border-line bg-paper/70 text-muted"
        }`}
      >
        {balloonShape.cycleMinShaped && balloonFill && balloonRuns
          ? `CycleMin-shaped leftover. Runs ${formatOddEvenRuns(balloonRuns)} equal toRuns of assembleFill ${formatNecklaceFill(balloonFill)}. Still not a realized cycle.`
          : balloonShape.cycleMinShaped && balloonRuns
            ? `CycleMin-shaped leftover. Runs ${formatOddEvenRuns(balloonRuns)} are not a four-slot fill. Still not a realized cycle (CycleMinShape_not_of_CycleMin).`
            : aligned
              ? "This cut is not CycleMin. A minimum spelling starts OO, ends E, has four evens and seven odds."
              : "Rotate until the min bead sits at the leftover knot."}
      </div>
      <div className="grid gap-6 md:grid-cols-[minmax(16rem,22rem)_1fr] md:items-start">
        <div>
          <CycleNecklace
            word={stored}
            shift={shift}
            minIndex={minIndex}
            showCut
            onSelectIndex={onSelectIndex}
          />
          <div className="mt-1 flex justify-center gap-2">
            <button
              type="button"
              className="rounded-full border border-line px-3 py-1 text-sm"
              disabled={!stored}
              onClick={() => onRotate(-1)}
            >
              Rotate left
            </button>
            <button
              type="button"
              className="rounded-full bg-deep px-3 py-1 text-sm text-card disabled:opacity-40"
              disabled={!stored || aligned}
              onClick={onSnap}
            >
              Snap to CycleMin
            </button>
            <button
              type="button"
              className="rounded-full border border-line px-3 py-1 text-sm"
              disabled={!stored}
              onClick={() => onRotate(1)}
            >
              Rotate right
            </button>
          </div>
          <p className="mt-1 text-center text-xs text-muted">
            This rotate moves the CycleMin cut. It does not walk the
            stem. A cut that starts E or OE is not CycleMin
            (rotate_even_not_cycleMin, rotate_OE_not_cycleMin).
          </p>
        </div>
        <div className="space-y-3">
          {currentRuns ? (
            <OddEvenRunStrip
              word={current}
              fill={currentFill}
              onSelect={onRun}
            />
          ) : (
            <LetterRow word={current} aligned={aligned} />
          )}
          <p className="text-xs uppercase tracking-wide text-muted">
            Cycle checklist
          </p>
          <ul className="grid gap-1.5">
            <Check ok={shape.startsOO}>
              Launch OO — cycleMin_launch_is_OO
            </Check>
            <Check ok={Boolean(currentRuns) && shape.startsOO && shape.lastOddRunAtMost1}>
              {currentRuns
                ? `Full run ${formatOddEvenRuns(currentRuns)} — cycleMin_has_full_odd_even_run_form`
                : (
                  <>
                    Full run <Tex>{String.raw`O^{a_1}E\cdots O^{a_e}E`}</Tex>
                    {" — needs terminal E"}
                  </>
                )}
            </Check>
            <Check ok={shape.endsE}>
              Wrap EO — cycleMin_wrap_is_EO, last-even cell
            </Check>
            <Check ok={shape.evenCountGe4 && shape.oddCountGe7 && shape.lengthGe11}>
              At least four evens and seven odds — period at least 11
            </Check>
            <Check ok={shape.expanding}>
              {`Expanding — 3^${shape.oddCount} beats 2^${current.length}`}
            </Check>
            <Check ok={shape.lastOddRunAtMost1}>
              Last odd-run a ≤ 1 — ends OE or EE, not OOE…
            </Check>
            <Check ok={Boolean(currentFill)}>
              {currentFill
                ? `assembleFill ${formatNecklaceFill(currentFill)} — counts exact on this fill`
                : "Not an assembleFill — four-slot candidate does not reconstruct this word"}
            </Check>
          </ul>
          <div className="grid gap-3 sm:grid-cols-2">
            <Metric
              label="This spelling"
              value={current || "—"}
              hint={
                shape.seam === "other"
                  ? "not a legal 2+2 seam"
                  : `${shape.seam.replace("|", " | n | ")} seam`
              }
            />
            <Metric
              label="Odds / evens"
              value={current ? `${shape.oddCount} / ${shape.evenCount}` : "—"}
              hint={
                current
                  ? `unplaced odds ${shape.unplacedOdds}, extra evens ${shape.extraEvens}`
                  : "four evens first hold at length 11"
              }
            />
            <Metric
              label="odd-even runs"
              value={balloonRuns ? formatOddEvenRuns(balloonRuns) : "needs terminal E"}
              hint="unique split of a word ending E; CycleMin adds a1 >= 2 and ae <= 1"
            />
            <Metric
              label="Lean fill"
              value={balloonFill ? formatNecklaceFill(balloonFill) : "none"}
              hint={
                balloonFillCounts
                  ? `#O=${balloonFillCounts.oddCount}, #E=${balloonFillCounts.evenCount}, L=${balloonFillCounts.length}`
                  : "shaped leftover need not be a NecklaceFill"
              }
            />
            <Metric
              label="Shape vs cycle"
              value={shape.cycleMinShaped ? "shape only" : "not shaped"}
              hint="CycleMinShape_not_of_CycleMin: leftovers inhabit the shape"
            />
          </div>
        </div>
      </div>
    </div>
  );
});

function Check({ ok, children }: { ok: boolean; children: ReactNode }) {
  return (
    <li className={`flex gap-2 text-sm ${ok ? "text-ink" : "text-muted"}`}>
      <span
        className={`mt-0.5 inline-flex h-4 w-4 shrink-0 items-center justify-center rounded-full text-[10px] text-card ${
          ok ? "bg-ok" : "bg-line"
        }`}
        aria-hidden
      >
        {ok ? "✓" : "·"}
      </span>
      <span>{children}</span>
    </li>
  );
}

function LetterRow({
  word,
  aligned,
}: {
  word: string;
  aligned: boolean;
}) {
  return (
    <div className="flex flex-wrap items-end gap-1" aria-label={`Current spelling ${word}`}>
      {Array.from(word).map((letter, index) => {
        const odd = letter === "O";
        const start = index === 0;
        const launch = aligned && index < 2;
        const last = index === word.length - 1;
        return (
          <span key={`${index}-${letter}`} className="grid justify-items-center gap-0.5">
            <span
              className={`inline-flex h-8 min-w-8 items-center justify-center rounded-md font-mono text-sm text-card ${
                start ? "ring-2 ring-ink ring-offset-2 ring-offset-card" : ""
              }`}
              style={{ background: odd ? "#c45c26" : "#1f6f6a" }}
            >
              {letter}
            </span>
            <span className="h-3 text-[10px] uppercase tracking-wide text-muted">
              {start && aligned ? "min" : launch ? "OO" : last && aligned ? "E" : ""}
            </span>
          </span>
        );
      })}
    </div>
  );
}

export function CycleTourWidget() {
  const [text, setText] = useState<string>(DEFAULT_SHAPE.word);
  const [shift, setShift] = useState<number>(0);
  const [minIndex, setMinIndex] = useState<number>(DEFAULT_SHAPE.minIndex);
  const [decisionId, setDecisionId] = useState<string | null>(null);
  const [joinIndex, setJoinIndex] = useState<number>(0);
  const [stemMode, setStemMode] = useState<StemDisplayMode>("optionalLaunch");
  const decision = findDecision(decisionId);

  const chooseDecision = useCallback((id: string | null) => {
    setDecisionId(id);
  }, []);

  const toggleDecision = useCallback((id: string) => {
    setDecisionId((current) => (current === id ? null : id));
  }, []);

  const clearDecision = useCallback(() => {
    setDecisionId(null);
  }, []);

  const setJoin = useCallback((index: number) => {
    setJoinIndex(index);
    setDecisionId("join-seam");
  }, []);

  const word = useMemo(() => {
    const parsed = parseItinerary(text, TOUR_WORD_MAX);
    const stored = parsed ?? "";
    const current = stored ? rotateItinerary(stored, shift) : "";
    const balloonWord = stored ? rotateItinerary(stored, minIndex) : "";
    const balloonFill = balloonWord ? tryAssembleFill(balloonWord) : null;
    return {
      parsed,
      stored,
      current,
      balloonWord,
      shift,
      minIndex,
      text,
      shape: cycleMinShape(current),
      balloonShape: cycleMinShape(balloonWord),
      currentFill: current ? tryAssembleFill(current) : null,
      balloonFill,
      balloonFillCounts: balloonFill ? assembleFillCounts(balloonFill) : null,
      currentRuns: current ? oddEvenRuns(current) : null,
      balloonRuns: balloonWord ? oddEvenRuns(balloonWord) : null,
      aligned:
        stored.length > 0 &&
        ((shift % stored.length) + stored.length) % stored.length === minIndex,
    };
  }, [text, shift, minIndex]);

  const chooseShape = useCallback((next: string, min: number) => {
    setText(next);
    setMinIndex(min);
    setShift(0);
  }, []);

  const rotateBy = useCallback(
    (delta: number) => {
      if (!word.stored) return;
      setShift((value) => (value + delta + word.stored.length) % word.stored.length);
    },
    [word.stored],
  );

  const snapCut = useCallback(() => {
    setShift(word.minIndex);
  }, [word.minIndex]);

  return (
    <div
      className="space-y-5"
      onClick={(event) => {
        const target = event.target;
        if (!(target instanceof Element)) return;
        if (target.closest("button, a, input, [role='button'], [data-keep-focus]")) return;
        clearDecision();
      }}
    >
      <p className="text-sm text-muted">
        No nontrivial cycle is known. The balloon is CycleMin geometry,
        not a realized loop.         Join left/right walks the stem around the
        six sure letters. Necklace rotate changes the CycleMin cut.
      </p>
      <div className="flex flex-wrap items-center gap-1.5">
        <span className="text-xs uppercase tracking-wide text-muted">Stem</span>
        {(
          [
            ["empty", "Empty"],
            ["unknownSlot", "Unknown ≥0"],
            ["optionalLaunch", "Optional OO"],
          ] as const
        ).map(([mode, label]) => (
          <button
            key={mode}
            type="button"
            className={`rounded-full px-2.5 py-0.5 text-sm ${
              stemMode === mode
                ? "bg-deep text-card"
                : "border border-line bg-card text-ink"
            }`}
            onClick={() => {
              setStemMode(mode);
              chooseDecision(mode === "empty" ? "empty-string" : "string-oo");
            }}
          >
            {label}
          </button>
        ))}
      </div>
      <div className="grid gap-3 lg:grid-cols-[minmax(0,1fr)_minmax(16rem,20rem)] lg:items-start">
        <CycleLollipop
          focus={decision?.focus}
          joinIndex={joinIndex}
          word={word.balloonWord}
          fill={word.balloonFill}
          stemMode={stemMode}
          onJoinIndex={setJoin}
          onSelectDecision={toggleDecision}
          onClearFocus={clearDecision}
        />
        <IdealDecisionCard decision={decision} />
      </div>
      <IdealDecisionList selectedId={decision?.id ?? null} onSelect={chooseDecision} />
      {word.parsed === null ? (
        <p className="text-sm text-warn">Use only O and E, length at most 24.</p>
      ) : (
        <CycleTourLeftovers
          word={word}
          onChooseShape={chooseShape}
          onRotate={rotateBy}
          onSnap={snapCut}
          onSelectIndex={setShift}
          onLeftover={() => chooseDecision("leftovers")}
          onRun={() => chooseDecision("balloon-run")}
        />
      )}
      <label className="block text-sm text-muted">
        Or type a short necklace
        <input
          className="mt-1 block w-full max-w-md rounded border border-line bg-card px-2 py-1 font-mono uppercase"
          value={text}
          onChange={(event) => chooseShape(event.target.value.toUpperCase(), 0)}
        />
      </label>
      <p className="text-sm text-muted">
        O⁷EEEE and O⁶EEEOE are assembleFill leftovers. The three-valley
        word has runs [3, 2, 2, 0]: CycleMin-shaped and not a fill.
        Pin misses OOEEEOOOOOE and OOOEEEOOOOE are outside CycleMinShape.
        None of them close.{" "}
        <Link to="/play/cycle">Try the same necklace in the playground</Link>.
      </p>
    </div>
  );
}
