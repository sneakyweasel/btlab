import { useState } from "react";
import { Link } from "react-router-dom";
import { CYCLE_TOUR_PRESETS, TOUR_WORD_MAX } from "../juggler/constants";
import {
  cycleMinShape,
  parseItinerary,
  rotateItinerary,
} from "../juggler/itinerary";
import { CycleAnatomy } from "../visuals/CycleAnatomy";
import { CycleLollipop } from "../visuals/CycleLollipop";
import { CycleNecklace } from "../visuals/CycleNecklace";
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
  const parsed = parseItinerary(text, TOUR_WORD_MAX);
  const stored = parsed ?? "";
  const current = stored ? rotateItinerary(stored, shift) : "";
  const balloonWord = stored ? rotateItinerary(stored, minIndex) : "";
  const shape = cycleMinShape(current);
  const balloonShape = cycleMinShape(balloonWord);
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
    <div className="space-y-5">
      <p className="text-sm text-muted">
        If a cycle existed it would need this string and the CycleMin run
        form: odd-run, even, odd-run, even, through four evens. Forced
        letters are solid; faded O and E have known parity and unknown
        count; grey ??? are unknown color. Period at least 11.
        Pictures of necessity, not a cycle. The unique known balloon is 1.
      </p>
      <div>
        <p className="mb-1.5 text-xs uppercase tracking-wide text-muted">
          Balloon leftovers — not cycles
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
              onClick={() => chooseShape(preset.word, preset.minIndex)}
            >
              {preset.label}
            </button>
          ))}
        </div>
      </div>
      {parsed !== null ? (
        <div
          className={`rounded-xl border px-3 py-2 text-sm ${
            balloonShape.cycleMinShaped
              ? "border-ok/40 bg-ok/10 text-ink"
              : aligned
                ? "border-warn/40 bg-warn/10 text-ink"
                : "border-line bg-paper/70 text-muted"
          }`}
        >
          {balloonShape.cycleMinShaped
            ? "The circle above is the necessary balloon. This leftover is one filling of the grey letters. Still not a cycle."
            : aligned
              ? "This cut is not CycleMin. A minimum spelling starts OO, ends E, and has four evens."
              : "Rotate until the min bead sits at the knot. The string joins there."}
        </div>
      ) : null}
      {parsed === null ? (
        <p className="text-sm text-warn">Use only O and E, length at most 24.</p>
      ) : (
        <>
          <div className="grid gap-3 lg:grid-cols-[minmax(0,1fr)_minmax(16rem,20rem)] lg:items-start">
            <CycleLollipop />
            <div className="rounded-xl border border-line bg-paper/70 px-3 py-3">
              <p className="text-xs uppercase tracking-wide text-muted">
                Necessary letters
              </p>
              <ul className="mt-2 grid gap-1.5">
                <Check ok>String starts OO — a launch, then the walk</Check>
                <Check ok>String greys — no nontrivial cycle to fill them</Check>
                <Check ok>String ends E — off-cycle parent t of the minimum</Check>
                <Check ok>Join at the seam — first meeting at CycleMin n</Check>
                <Check ok>Balloon is run form — odd-run, E, odd-run, E, …</Check>
                <Check ok>First odd-run at least 2 — launch OO, not E or OE</Check>
                <Check ok>At least four E — period at least 11</Check>
                <Check ok>Last odd-run at most 1 — ends EE or OE</Check>
              </ul>
              <p className="mt-3 text-sm text-muted">
                A start already on the balloon has an empty string. A
                contracting prefix is descent, not a balloon. An unbounded walk
                has neither. This figure places the first meeting at CycleMin;
                a join can sit elsewhere on the loop.
              </p>
            </div>
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
            </div>
            <div className="space-y-3">
              <LetterRow word={current} aligned={aligned} />
              <p className="text-xs uppercase tracking-wide text-muted">
                Balloon checklist
              </p>
              <ul className="grid gap-1.5">
                <Check ok={shape.startsOO}>
                  Starts OO — not E, not OE
                </Check>
                <Check ok={shape.startsOO}>
                  Launch is OO — T(n) odd, T²(n) overshoots (n+1)²
                </Check>
                <Check ok={shape.endsE}>
                  Ends E — last peak lands in the last-even cell
                </Check>
                <Check ok={shape.evenCountGe4}>
                  At least four evens — period at least 11
                </Check>
                <Check ok={shape.expanding}>
                  {`Expanding — 3^${shape.oddCount} beats 2^${current.length}`}
                </Check>
                <Check ok={shape.lastOddRunAtMost1}>
                  Last odd-run a ≤ 1 — ends OE or EE, not OOE…
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
                  hint="four evens first hold at length 11"
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
        O⁷EEEE, O⁶EEEOE, and the three-valley word fill the balloon greys and
        still do not close. The grey letters are not a realized walk.{" "}
        <Link to="/play/cycle">Try the same necklace in the playground</Link>.
      </p>
    </div>
  );
}
