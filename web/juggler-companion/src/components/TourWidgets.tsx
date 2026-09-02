import { useMemo, useState } from "react";
import { evenCell, oddCellIntegers } from "../juggler/cells";
import { NOTE_ORBIT_3 } from "../juggler/constants";
import { financeView } from "../juggler/finance";
import { formatInt } from "../juggler/format";
import { floorPower, letterOf } from "../juggler/map";
import {
  envelopeSlack,
  expanding,
  followsWord,
  imageAfter,
  oddCount,
  parseWord,
  regimeOf,
  rotateWord,
} from "../juggler/word";
import { CellNumberLine } from "../visuals/CellNumberLine";
import { CycleNecklace } from "../visuals/CycleNecklace";
import { EnvelopeCeiling } from "../visuals/EnvelopeCeiling";
import { FloorLadder } from "../visuals/FloorLadder";
import { MapDoors } from "../visuals/MapDoors";
import { OrbitBeads } from "../visuals/OrbitBeads";
import { SurplusScale } from "../visuals/SurplusScale";
import { WalkChargePipeline } from "../visuals/WalkChargePipeline";
import { Metric } from "./Metric";
import { Tex } from "./Tex";

export function MapWidget() {
  const [n, setN] = useState(3n);
  const letter = letterOf(n);
  const next = n < 1n ? null : floorPower(n);
  return (
    <div className="space-y-4">
      <MapDoors highlight={letter === "O" ? "odd" : "even"} />
      <p className="text-sm text-muted">
        Floor means: throw away the decimals and keep the integer part. It is
        applied after every even or odd step, not once at the end.
      </p>
      <div className="flex flex-wrap items-end gap-3">
        <label className="text-sm text-muted">
          Start
          <input
            className="ml-2 rounded border border-line bg-card px-2 py-1 font-mono"
            type="number"
            min={1}
            value={n.toString()}
            onChange={(event) => {
              const value = Number(event.target.value);
              if (Number.isInteger(value) && value >= 1) setN(BigInt(value));
            }}
          />
        </label>
        <button
          type="button"
          className="rounded-full bg-deep px-3 py-1 text-sm text-card"
          onClick={() => {
            if (next !== null) setN(next);
          }}
        >
          Step once
        </button>
        <button
          type="button"
          className="rounded-full border border-line px-3 py-1 text-sm"
          onClick={() => setN(3n)}
        >
          Reset to 3
        </button>
      </div>
      <div className="grid gap-3 sm:grid-cols-3">
        <Metric label="Now" value={n.toString()} hint={letter === "O" ? "odd, will grow" : "even, will shrink"} />
        <Metric label="Letter" value={letter} />
        <Metric label="J(n)" value={next === null ? "—" : next.toString()} />
      </div>
    </div>
  );
}

export function OrbitWidget() {
  const [shown, setShown] = useState<number>(NOTE_ORBIT_3.length);
  const states = NOTE_ORBIT_3.slice(0, shown);
  return (
    <div className="space-y-3">
      <OrbitBeads states={states} active={shown - 1} />
      <div className="flex gap-2">
        <button
          type="button"
          className="rounded-full bg-deep px-3 py-1 text-sm text-card"
          onClick={() => setShown((value) => Math.min(NOTE_ORBIT_3.length, value + 1))}
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
        Word so far:{" "}
        <span className="font-mono">
          {states.slice(0, -1).map((state) => letterOf(state)).join("") || "—"}
        </span>
        . Reaching 1 here is the orbit of 3, not a halt theorem.
      </p>
    </div>
  );
}

export function CycleWidget() {
  const [word, setWord] = useState("OEO");
  const [shift, setShift] = useState(0);
  const parsed = parseWord(word, 16) ?? "";
  const current = parsed ? rotateWord(parsed, shift) : "";
  return (
    <div className="space-y-3">
      <CycleNecklace word={parsed} shift={shift} minIndex={0} />
      <div className="flex flex-wrap gap-2">
        {(["OEO", "OOE"] as const).map((preset) => (
          <button
            key={preset}
            type="button"
            className="rounded-full border border-line px-3 py-1 font-mono text-sm"
            onClick={() => {
              setWord(preset);
              setShift(0);
            }}
          >
            {preset}
          </button>
        ))}
        <button
          type="button"
          className="rounded-full bg-deep px-3 py-1 text-sm text-card"
          onClick={() => parsed && setShift((value) => (value + 1) % parsed.length)}
        >
          Rotate
        </button>
      </div>
      <Metric
        label="This spelling"
        value={current || "—"}
        hint={current.startsWith("O") ? "legal CycleMin spelling starts odd" : "rotate toward the minimum"}
      />
    </div>
  );
}

export function ExpandingWidget() {
  const [text, setText] = useState("OOE");
  const word = parseWord(text, 16) ?? "";
  const odds = oddCount(word);
  return (
    <div className="space-y-3">
      <SurplusScale odds={odds} length={word.length} />
      <label className="block text-sm text-muted">
        Short O/E word
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
  const follows = followsWord(n, word);
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

export function CellsWidget() {
  const even = evenCell(6);
  const odds = oddCellIntegers(11);
  return (
    <div className="grid gap-6 md:grid-cols-2">
      <div>
        <h3 className="mb-2 font-serif text-lg">Even cell of 6</h3>
        <CellNumberLine lo={even.lo} hi={even.hi} marks={[36, 38, 40]} label="Even parents of 6" />
        <p className="text-sm text-muted">
          Even n in [{even.lo}, {even.hi}) all map to 6.
        </p>
      </div>
      <div>
        <h3 className="mb-2 font-serif text-lg">Odd cell of 11</h3>
        <CellNumberLine lo={4} hi={7} marks={odds} label="Odd parent of 11" />
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
