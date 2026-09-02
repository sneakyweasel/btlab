import { describe, expect, it } from "vitest";
import {
  HARVESTED_LEMMA_NEEDLES,
  IDEAL_DECISIONS,
} from "../content/idealDecisions";
import { evenPreimage, oddPreimageIntegers } from "./preimages";
import {
  NOTE_TRAJECTORY_3,
  NOTE_PEAK_37,
  PAPER_EXCEPTION_COUNT,
  PAPER_PERIOD,
  BALLOON_SCHEMA,
  IDEAL_BALLOON_BEADS,
  IDEAL_BALLOON_INTERVALS,
  IDEAL_BALLOON_LETTERS,
  idealJoinLabel,
  idealJoinSpots,
  intervalBoundLabel,
  packCountRuns,
  stepIdealJoin,
  IDEAL_STRING_BEADS,
  IDEAL_STRING_LETTERS,
  STRING_TOUR_PRESETS,
  TOUR_WORD_MAX,
} from "./constants";
import { financeSnapshot, financeView } from "./finance";
import { floorPower } from "./map";
import { monsterTrajectory, resolveTrajectory } from "./monsters";
import { walkTrajectory } from "./trajectory";
import {
  cycleMinShape,
  envelopeSlack,
  expanding,
  followsItinerary,
  imageAfter,
  regimeOf,
} from "./itinerary";

describe("floorPower", () => {
  it("matches the note trajectory of 3", () => {
    expect(floorPower(3n)).toBe(5n);
    expect(floorPower(5n)).toBe(11n);
    expect(floorPower(11n)).toBe(36n);
    expect(floorPower(36n)).toBe(6n);
    expect(floorPower(6n)).toBe(2n);
    expect(floorPower(2n)).toBe(1n);
  });
});

describe("walkTrajectory", () => {
  it("replays the note trajectory of 3", () => {
    const view = walkTrajectory(3n, 20);
    expect(view.states).toEqual([...NOTE_TRAJECTORY_3]);
    expect(view.itinerary).toBe("OOOEEE");
    expect(view.reachedOne).toBe(true);
    expect(view.tooLarge).toBe(false);
  });

  it("collapses the even tower 256", () => {
    const view = walkTrajectory(256n, 20);
    expect(view.states).toEqual([256n, 16n, 4n, 2n, 1n]);
    expect(view.itinerary).toBe("EEEE");
    expect(view.reachedOne).toBe(true);
  });

  it("records the note peak of 37", () => {
    const view = walkTrajectory(37n, 80);
    expect(view.states).toContain(NOTE_PEAK_37);
    expect(view.reachedOne).toBe(true);
    expect(view.bitCapped).toBe(false);
  });

  it("stops a start larger than the 256-bit display cap", () => {
    const view = walkTrajectory(1n << 256n, 10);
    expect(view.bitCapped).toBe(true);
    expect(view.tooLarge).toBe(true);
    expect(view.states).toHaveLength(1);
  });
});

describe("monster trajectories", () => {
  it("loads the shipped 193 delay record", () => {
    const view = monsterTrajectory(193n);
    expect(view).not.toBeNull();
    expect(view?.source).toBe("monster");
    expect(view?.reachedOne).toBe(true);
    expect(view?.peakBits).toBe(900);
    expect(view?.states[0]).toBe(193n);
    expect(view?.states.at(-1)).toBe(1n);
  });

  it("resolves 37 live and 173 from JSON", () => {
    const live = resolveTrajectory(37n, 80);
    expect(live.source).toBe("live");
    expect(live.states).toContain(NOTE_PEAK_37);
    const shipped = resolveTrajectory(173n, 80);
    expect(shipped.source).toBe("monster");
    expect(shipped.reachedOne).toBe(true);
    expect((shipped.peakBits ?? 0) > 256).toBe(true);
  });
});

describe("itineraries", () => {
  it("follows OOE at 5 and lands at 6", () => {
    expect(followsItinerary(5n, "OOE")).toBe(true);
    expect(imageAfter(5n, "OOE")).toBe(6n);
    expect(regimeOf(3, 2)).toBe("expanding");
    expect(expanding("OOE")).toBe(true);
  });

  it("rejects a parity mismatch", () => {
    expect(followsItinerary(3n, "E")).toBe(false);
    expect(followsItinerary(2n, "O")).toBe(false);
  });

  it("computes one-letter envelope slack at n=3", () => {
    expect(envelopeSlack(3n, 5n, 1, 1)).toBe(2n);
  });
});

describe("cycleMinShape", () => {
  it("accepts O^7 EEEE as a CycleMin-shaped leftover", () => {
    const shape = cycleMinShape("OOOOOOOEEEE");
    expect(shape.cycleMinShaped).toBe(true);
    expect(shape.seam).toBe("EE|OO");
    expect(shape.lastOddRun).toBe(0);
    expect(shape.evenCount).toBe(4);
  });

  it("accepts O^6 EEEOE as an OE-seam leftover", () => {
    const shape = cycleMinShape("OOOOOOEEEOE");
    expect(shape.cycleMinShaped).toBe(true);
    expect(shape.seam).toBe("OE|OO");
    expect(shape.lastOddRun).toBe(1);
  });

  it("rejects OOE and OEO", () => {
    expect(cycleMinShape("OOE").cycleMinShaped).toBe(false);
    expect(cycleMinShape("OOE").evenCountGe4).toBe(false);
    expect(cycleMinShape("OOE").lastOddRunAtMost1).toBe(false);
    expect(cycleMinShape("OOE").seam).toBe("other");
    expect(cycleMinShape("OEO").startsOO).toBe(false);
    expect(cycleMinShape("OEO").endsE).toBe(false);
  });

  it("rejects a wrong cut of the leftover", () => {
    expect(cycleMinShape("EEOOOOOOOEE").cycleMinShaped).toBe(false);
    expect(cycleMinShape("EEOOOOOOOEE").startsOO).toBe(false);
  });

  it("accepts a three-valley CycleMin-shaped leftover", () => {
    const shape = cycleMinShape("OOOEOOEOOEE");
    expect(shape.cycleMinShaped).toBe(true);
    expect(shape.seam).toBe("EE|OO");
    expect(shape.evenCount).toBe(4);
    expect(shape.oddCount).toBe(7);
  });
});

describe("idealized string stem", () => {
  it("starts OO, leaves the middle undefined, and ends E", () => {
    expect(IDEAL_STRING_LETTERS.join("")).toBe("OO???E");
    expect(IDEAL_STRING_BEADS.filter((bead) => bead.tone === "sure").map((bead) => bead.letter).join("")).toBe("OOE");
    expect(IDEAL_STRING_BEADS.filter((bead) => bead.tone === "unknown")).toHaveLength(3);
  });
});

describe("idealized cycle", () => {
  it("draws the Lean schema: two sure O, four sure E, no invented ? letters", () => {
    expect(BALLOON_SCHEMA.map((station) => station.kind)).toEqual([
      "sureLaunchO",
      "intervalOdd",
      "sureEven",
      "intervalOdd",
      "sureEven",
      "sureEven",
      "intervalOdd",
      "sureEven",
      "intervalExtraEven",
    ]);
    expect(IDEAL_BALLOON_LETTERS.join("")).toBe("OOEEEE");
    expect(IDEAL_BALLOON_BEADS).toHaveLength(6);
    expect(IDEAL_BALLOON_BEADS.filter((bead) => bead.letter === "O" && bead.tone === "sure")).toHaveLength(2);
    expect(IDEAL_BALLOON_BEADS.filter((bead) => bead.letter === "E" && bead.tone === "sure")).toHaveLength(4);
    expect(IDEAL_BALLOON_BEADS.filter((bead) => bead.letter === "?")).toHaveLength(0);
    expect(IDEAL_BALLOON_BEADS.filter((bead) => bead.tone === "unknown")).toHaveLength(0);
    expect(IDEAL_BALLOON_BEADS.at(-1)).toEqual({ letter: "E", tone: "sure" });
    expect(packCountRuns(IDEAL_BALLOON_BEADS)).toHaveLength(6);
  });

  it("describes leftover mass as interval bounds, not letter beads", () => {
    expect(IDEAL_BALLOON_INTERVALS.map((interval) => interval.kind)).toEqual([
      "a1Extras",
      "middle",
      "extraEven",
      "lastZeroOrOne",
    ]);
    expect(IDEAL_BALLOON_INTERVALS.every((interval) => interval.min === 0)).toBe(true);
    expect(intervalBoundLabel(IDEAL_BALLOON_INTERVALS[0])).toBe("0+");
    expect(intervalBoundLabel(IDEAL_BALLOON_INTERVALS[3])).toBe("0 or 1");
    expect(IDEAL_BALLOON_INTERVALS[3]?.max).toBe(1);
    expect(IDEAL_BALLOON_INTERVALS[2]?.max).toBeNull();
  });

  it("rotates the join only among the six sure letters", () => {
    const spots = idealJoinSpots();
    expect(spots).toEqual([0, 1, 2, 3, 4, 5]);
    expect(spots.every((index) => IDEAL_BALLOON_BEADS[index]?.tone === "sure")).toBe(true);
    expect(spots.filter((index) => IDEAL_BALLOON_BEADS[index]?.letter === "O")).toHaveLength(2);
    expect(spots.filter((index) => IDEAL_BALLOON_BEADS[index]?.letter === "E")).toHaveLength(4);
    expect(idealJoinLabel(0)).toBe("CycleMin n");
    expect(idealJoinLabel(1)).toBe("launch O");
    expect(idealJoinLabel(2)).toBe("first E");
    expect(idealJoinLabel(3)).toBe("E 2");
    expect(idealJoinLabel(5)).toBe("last E");
    expect(stepIdealJoin(0, 1)).toBe(1);
    expect(stepIdealJoin(1, 1)).toBe(2);
    expect(stepIdealJoin(5, 1)).toBe(0);
    expect(stepIdealJoin(0, -1)).toBe(5);
    expect(stepIdealJoin(2, 1)).toBe(3);
  });
});

describe("string tour presets", () => {
  it("ends every shipped string on the cycle 1", () => {
    for (const preset of STRING_TOUR_PRESETS) {
      expect(preset.states.at(-1)).toBe(1n);
      expect(preset.states.at(-2)).toBe(2n);
    }
  });

  it("replays each string as a realized walk that fits the tour cap", () => {
    for (const preset of STRING_TOUR_PRESETS) {
      for (let index = 0; index < preset.states.length - 1; index += 1) {
        expect(floorPower(preset.states[index])).toBe(preset.states[index + 1]);
      }
      const word = preset.states
        .slice(0, -1)
        .map((state) => (state % 2n === 1n ? "O" : "E"))
        .join("");
      expect(word.length).toBeLessThanOrEqual(TOUR_WORD_MAX);
    }
  });

  it("replays the repeated-block walk of 69", () => {
    const preset = STRING_TOUR_PRESETS.find((item) => item.id === "69");
    expect(preset?.states).toEqual([
      69n, 573n, 13716n, 117n, 1265n, 44992n, 212n, 14n, 3n, 5n, 11n, 36n, 6n,
      2n, 1n,
    ]);
  });

  it("ships 365 as a 21-letter leftover that still captures", () => {
    const preset = STRING_TOUR_PRESETS.find((item) => item.id === "365");
    const word = preset?.states
      .slice(0, -1)
      .map((state) => (state % 2n === 1n ? "O" : "E"))
      .join("");
    expect(word).toBe("OOEOOEOOEOOEOEEEOOEEE");
    expect(word?.length).toBe(21);
  });
});

describe("preimages", () => {
  it("gives the even one-step preimage of 6 as [36, 49)", () => {
    expect(evenPreimage(6)).toEqual({ lo: 36, hi: 49 });
  });

  it("gives the unique parent 5 of odd image 11", () => {
    expect(oddPreimageIntegers(11)).toEqual([5]);
  });
});

describe("idealized figure decisions", () => {
  it("covers every harvested lemma from the itinerary extract", () => {
    const catalog = IDEAL_DECISIONS.map((decision) => decision.lemma).join("\n");
    for (const needle of HARVESTED_LEMMA_NEEDLES) {
      expect(catalog).toContain(needle);
    }
  });

  it("keeps the optional stem off the cycle theorems", () => {
    const optional = IDEAL_DECISIONS.filter((decision) => decision.kind === "optional");
    expect(optional.map((decision) => decision.id)).toEqual([
      "string-oo",
      "string-e",
      "join-seam",
    ]);
    expect(IDEAL_DECISIONS.filter((decision) => decision.part === "cycle").every((decision) => decision.kind !== "optional")).toBe(true);
  });

  it("does not paint equidistribution or automatic descent as beads", () => {
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "equidistribution")?.kind).toBe("off-figure");
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "automatic")?.kind).toBe("off-figure");
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "empty-string")?.why).toMatch(/minimum length 0/);
  });
});

describe("finance lookup", () => {
  it("excludes every period at most 25780 at the 10^6 floor", () => {
    expect(financeView(11).status).toBe("excluded");
    expect(financeView(25780).status).toBe("excluded");
  });

  it("marks 25781 as the first admissible length", () => {
    const view = financeView(PAPER_PERIOD);
    expect(view.status).toBe("admissible");
    expect(view.oMin).toBe(16266);
    expect(view.nMax).toBe(26_254_995);
    expect(financeSnapshot.exceptionCount).toBe(PAPER_EXCEPTION_COUNT);
  });
});
