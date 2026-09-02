import { useState } from "react";
import { Link } from "react-router-dom";
import { CYCLE_TOUR_PRESETS, STRING_TOUR_PRESETS } from "../juggler/constants";
import {
  cycleMinShape,
  parseItinerary,
  rotateItinerary,
} from "../juggler/itinerary";
import { CycleAnatomy } from "../visuals/CycleAnatomy";
import { CycleLollipop } from "../visuals/CycleLollipop";
import { CycleNecklace } from "../visuals/CycleNecklace";
import { Metric } from "./Metric";

const DEFAULT = CYCLE_TOUR_PRESETS[0];

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
  const [text, setText] = useState<string>(DEFAULT.word);
  const [shift, setShift] = useState(0);
  const [minIndex, setMinIndex] = useState<number>(DEFAULT.minIndex);
  const [stringId, setStringId] = useState<string>("69");
  const stringExample =
    STRING_TOUR_PRESETS.find((item) => item.id === stringId) ?? STRING_TOUR_PRESETS[0];
  const stringWord = stringExample.states
    .slice(0, -1)
    .map((state) => (state % 2n === 1n ? "O" : "E"))
    .join("");
  const parsed = parseItinerary(text, 16);
  const stored = parsed ?? "";
  const current = stored ? rotateItinerary(stored, shift) : "";
  const shape = cycleMinShape(current);
  const aligned = stored.length > 0 && ((shift % stored.length) + stored.length) % stored.length === minIndex;

  function choose(word: string, min: number) {
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
        The balloon is the cycle. CycleMin cuts that balloon at its smallest
        value: last peak, n, and launch OO meet there. The string is the
        itinerary before the first visit to the balloon. Pictures of forced
        shape, not cycles. The unique known balloon is 1.
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
            onClick={() => choose(preset.word, preset.minIndex)}
          >
            {preset.label}
          </button>
        ))}
      </div>
      {parsed !== null ? (
        <div
          className={`rounded-xl border px-3 py-2 text-sm ${
            shape.cycleMinShaped
              ? "border-ok/40 bg-ok/10 text-ink"
              : aligned
                ? "border-warn/40 bg-warn/10 text-ink"
                : "border-line bg-paper/70 text-muted"
          }`}
        >
          {shape.cycleMinShaped
            ? "CycleMin shape. Necessary, not a cycle."
            : aligned
              ? "This cut is not CycleMin. A minimum spelling starts OO, ends E, and has four evens."
              : "Rotate until the min bead sits at the knot."}
        </div>
      ) : null}
      {parsed === null ? (
        <p className="text-sm text-warn">Use only O and E, length at most 16.</p>
      ) : (
        <>
          <div className="grid gap-6 md:grid-cols-[minmax(16rem,22rem)_1fr] md:items-start">
            <div>
              <CycleNecklace
                word={stored}
                shift={shift}
                minIndex={minIndex}
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
          <div className="flex flex-wrap items-center gap-1.5">
            {STRING_TOUR_PRESETS.map((preset) => (
              <button
                key={preset.id}
                type="button"
                title={preset.hint}
                className={`rounded-full px-2.5 py-0.5 text-sm ${
                  stringId === preset.id
                    ? "bg-odd text-card"
                    : "border border-line bg-card text-ink"
                }`}
                onClick={() => setStringId(preset.id)}
              >
                {preset.label}
              </button>
            ))}
          </div>
          <div className="grid gap-3 lg:grid-cols-[1fr_minmax(16rem,20rem)] lg:items-start">
            <CycleLollipop example={stringExample} />
            <div className="rounded-xl border border-line bg-paper/70 px-3 py-3">
              <p className="text-xs uppercase tracking-wide text-muted">
                String restrictions
              </p>
              <ul className="mt-2 grid gap-1.5">
                <Check ok>{`Realized — this walk follows ${stringWord}`}</Check>
                <Check ok>Envelope still applies — floors only shrink</Check>
                <Check ok>No prefix return — a return before the join is a shorter cycle</Check>
                <Check ok>Contracting prefixes are descent, not a balloon</Check>
                <Check ok>Capture — this balloon is 1, not a nontrivial cycle</Check>
                <Check ok>Join is first meeting — last even maps to 1; 1 maps to 1</Check>
              </ul>
              <p className="mt-3 text-sm text-muted">
                An unbounded walk has no balloon, hence no string. The join is
                not the CycleMin cut unless they happen to coincide.
              </p>
            </div>
          </div>
        </>
      )}
      <label className="block text-sm text-muted">
        Or type a short necklace
        <input
          className="mt-1 block w-full max-w-md rounded border border-line bg-card px-2 py-1 font-mono uppercase"
          value={text}
          onChange={(event) => choose(event.target.value.toUpperCase(), 0)}
        />
      </label>
      <p className="text-sm text-muted">
        O⁷EEEE and O⁶EEEOE are named leftovers: they have the shape and still
        do not close.{" "}
        <Link to="/play/cycle">Try the same necklace in the playground</Link>.
      </p>
    </div>
  );
}
