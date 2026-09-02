import { useState } from "react";
import { Link } from "react-router-dom";
import { CYCLE_TOUR_PRESETS, TOUR_WORD_MAX } from "../juggler/constants";
import {
  assembleFillCounts,
  cycleMinShape,
  formatNecklaceFill,
  formatOddEvenRuns,
  oddEvenRuns,
  parseItinerary,
  rotateItinerary,
  tryAssembleFill,
} from "../juggler/itinerary";
import { CycleAnatomy } from "../visuals/CycleAnatomy";
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

function Check({ ok, children }: { ok: boolean; children: string }) {
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
  const [shift, setShift] = useState(0);
  const [minIndex, setMinIndex] = useState(DEFAULT_SHAPE.minIndex);
  const [decisionId, setDecisionId] = useState<string | null>(null);
  const [joinIndex, setJoinIndex] = useState(0);
  const decision = findDecision(decisionId);

  function chooseDecision(id: string | null) {
    setDecisionId(id);
  }

  function toggleDecision(id: string) {
    setDecisionId((current) => (current === id ? null : id));
  }

  function clearDecision() {
    setDecisionId(null);
  }
  const parsed = parseItinerary(text, TOUR_WORD_MAX);
  const stored = parsed ?? "";
  const current = stored ? rotateItinerary(stored, shift) : "";
  const balloonWord = stored ? rotateItinerary(stored, minIndex) : "";
  const shape = cycleMinShape(current);
  const balloonShape = cycleMinShape(balloonWord);
  const currentFill = current ? tryAssembleFill(current) : null;
  const balloonFill = balloonWord ? tryAssembleFill(balloonWord) : null;
  const balloonFillCounts = balloonFill ? assembleFillCounts(balloonFill) : null;
  const currentRuns = current ? oddEvenRuns(current) : null;
  const balloonRuns = balloonWord ? oddEvenRuns(balloonWord) : null;
  const aligned =
    stored.length > 0 &&
    ((shift % stored.length) + stored.length) % stored.length === minIndex;

  function chooseShape(word: string, min: number) {
    setText(word);
    setMinIndex(min);
    setShift(0);
  }

  function rotateBy(delta: number) {
    if (!stored) return;
    setShift((value) => (value + delta + stored.length) % stored.length);
  }

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
        If a cycle existed it would need a CycleMin rotation. Join
        left/right walks the stem around the six sure letters — that
        card under the join buttons is the Lean fork at that bead.
        Necklace rotate below is a different motion: it changes the
        CycleMin cut, not the stem. Cuts that start E or OE are not
        CycleMin. Pictures of necessity, not a realized loop beyond 1.
        The unique known cycle is 1.
      </p>
      <div className="grid gap-3 lg:grid-cols-[minmax(0,1fr)_minmax(16rem,20rem)] lg:items-start">
        <CycleLollipop
          focus={decision?.focus}
          joinIndex={joinIndex}
          word={balloonWord}
          fill={balloonFill}
          onJoinIndex={(index) => {
            setJoinIndex(index);
            setDecisionId("join-seam");
          }}
          onSelectDecision={toggleDecision}
          onClearFocus={clearDecision}
        />
        <IdealDecisionCard decision={decision} />
      </div>
      <IdealDecisionList selectedId={decision?.id ?? null} onSelect={chooseDecision} />
      {parsed === null ? (
        <p className="text-sm text-warn">Use only O and E, length at most 24.</p>
      ) : (
        <>
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
                    chooseShape(preset.word, preset.minIndex);
                    setDecisionId("leftovers");
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
                onSelectIndex={setShift}
              />
              <div className="mt-1 flex justify-center gap-2">
                <button
                  type="button"
                  className="rounded-full border border-line px-3 py-1 text-sm"
                  disabled={!stored}
                  onClick={() => rotateBy(-1)}
                >
                  Rotate left
                </button>
                <button
                  type="button"
                  className="rounded-full bg-deep px-3 py-1 text-sm text-card disabled:opacity-40"
                  disabled={!stored || aligned}
                  onClick={() => setShift(minIndex)}
                >
                  Snap to CycleMin
                </button>
                <button
                  type="button"
                  className="rounded-full border border-line px-3 py-1 text-sm"
                  disabled={!stored}
                  onClick={() => rotateBy(1)}
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
                  onSelect={() => setDecisionId("balloon-run")}
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
                    : "Full run O^a1 E ... O^ae E — needs terminal E"}
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
          <CycleAnatomy
            word={current}
            aligned={aligned}
            shaped={shape.cycleMinShaped}
            seam={shape.seam}
          />
        </>
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
        None of them close.{" "}
        <Link to="/play/cycle">Try the same necklace in the playground</Link>.
      </p>
    </div>
  );
}
