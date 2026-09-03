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
  intervalCountBead,
  intervalIsMass,
  intervalSlotName,
  packCountRuns,
  SURE_LINKS,
  stepIdealJoin,
  IDEAL_STRING_BEADS,
  IDEAL_STRING_LETTERS,
  STRING_TOUR_PRESETS,
  TOUR_WORD_MAX,
} from "./constants";
import { financeSnapshot, financeView } from "./finance";
import { idealJoinConfig, stemBeadsForJoin, stemTerminalLetter } from "./joinConfig";
import {
  DEFAULT_STEM_BEADS,
  PIN_MISS_WORDS,
  SCHEMATIC_LOLLIPOP,
  defaultStemIsNotSureOOE,
  joinFigure,
  paintStem,
  siteRigidity,
} from "./lollipop";
import { floorPower } from "./map";
import { monsterTrajectory, resolveTrajectory } from "./monsters";
import { walkTrajectory } from "./trajectory";
import {
  assembleFill,
  assembleFillCounts,
  assembleOddEvenRuns,
  cycleMinShape,
  formatBalloonSlots,
  formatOddEvenRuns,
  formatRunWord,
  formatRunWordTex,
  necklaceFillAdmits,
  necklaceFillToRuns,
  oddEvenRuns,
  runsEqual,
  envelopeSlack,
  expanding,
  followsItinerary,
  imageAfter,
  regimeOf,
  tryAssembleFill,
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
    expect(shape.oddCountGe7).toBe(true);
    expect(shape.unplacedOdds).toBe(5);
    expect(shape.extraEvens).toBe(0);
    expect(shape.startsOddEvenBlock).toBe(true);
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
    expect(tryAssembleFill("OOOEOOEOOEE")).toBeNull();
  });

  it("rejects the necklace-pin misses as CycleMinShape", () => {
    const miss2005 = cycleMinShape("OOEEEOOOOOE");
    const miss3004 = cycleMinShape("OOOEEEOOOOE");
    expect(miss2005.cycleMinShaped).toBe(false);
    expect(miss3004.cycleMinShaped).toBe(false);
    expect(miss2005.lastOddRun).toBe(5);
    expect(miss3004.lastOddRun).toBe(4);
    expect(miss2005.startsOO).toBe(true);
    expect(miss2005.evenCount).toBe(4);
    expect(miss2005.oddCount).toBe(7);
    expect(miss2005.expanding).toBe(true);
  });
});

describe("assembleFill identities", () => {
  it("matches Lean leftover fills and count identities", () => {
    const o7 = { a1Extras: 5, middleOdds: 0, extraEvens: 0, lastOdds: 0 };
    const o6 = { a1Extras: 4, middleOdds: 0, extraEvens: 0, lastOdds: 1 };
    expect(assembleFill(o7)).toBe("OOOOOOOEEEE");
    expect(assembleFill(o6)).toBe("OOOOOOEEEOE");
    expect(formatBalloonSlots(o7)).toBe("a₁ = 7, a∗ = 0, e₊ = 0, aₑ = 0");
    expect(formatBalloonSlots(o6)).toBe("a₁ = 6, a∗ = 0, e₊ = 0, aₑ = 1");
    expect(tryAssembleFill("OOOOOOOEEEE")).toEqual(o7);
    expect(tryAssembleFill("OOOOOOEEEOE")).toEqual(o6);
    expect(assembleFillCounts(o7)).toEqual({
      oddCount: 7,
      evenCount: 4,
      length: 11,
      unplacedOdds: 5,
      extraEvens: 0,
    });
    expect(assembleFillCounts(o6)).toEqual({
      oddCount: 7,
      evenCount: 4,
      length: 11,
      unplacedOdds: 5,
      extraEvens: 0,
    });
  });

  it("does not treat a three-valley leftover as a fill", () => {
    expect(tryAssembleFill("OOOEOOEOOEE")).toBeNull();
    expect(oddEvenRuns("OOOEOOEOOEE")).toEqual([3, 2, 2, 0]);
    expect(assembleOddEvenRuns([3, 2, 2, 0])).toBe("OOOEOOEOOEE");
    expect(formatOddEvenRuns([3, 2, 2, 0])).toBe("[3, 2, 2, 0]");
    expect(formatRunWord([3, 2, 2, 0])).toBe("O^3 E O^2 E O^2 E E");
    expect(formatRunWord([7, 0, 0, 0])).toBe("O^7 E E E E");
    expect(formatRunWordTex([3, 2, 2, 0])).toBe("O^{3}E\\,O^{2}E\\,O^{2}E\\,E");
    expect(formatRunWordTex([7, 0, 0, 0])).toBe("O^{7}E\\,E\\,E\\,E");
    expect(runsEqual([3, 2, 2, 0], [3, 2, 2, 0])).toBe(true);
    expect(runsEqual([3, 2, 2, 0], [7, 0, 0, 0])).toBe(false);
  });

  it("assembles the necklace-pin misses but does not admit them", () => {
    const miss2005 = { a1Extras: 0, middleOdds: 0, extraEvens: 0, lastOdds: 5 };
    const miss3004 = { a1Extras: 1, middleOdds: 0, extraEvens: 0, lastOdds: 4 };
    expect(assembleFill(miss2005)).toBe("OOEEEOOOOOE");
    expect(assembleFill(miss3004)).toBe("OOOEEEOOOOE");
    expect(tryAssembleFill("OOEEEOOOOOE")).toEqual(miss2005);
    expect(tryAssembleFill("OOOEEEOOOOE")).toEqual(miss3004);
    expect(necklaceFillAdmits(miss2005)).toBe(false);
    expect(necklaceFillAdmits(miss3004)).toBe(false);
  });

  it("projects a fill onto a bunched run list", () => {
    const o7 = { a1Extras: 5, middleOdds: 0, extraEvens: 0, lastOdds: 0 };
    expect(necklaceFillToRuns(o7)).toEqual([7, 0, 0, 0]);
    expect(assembleOddEvenRuns(necklaceFillToRuns(o7))).toBe(assembleFill(o7));
    expect(necklaceFillToRuns(o7)[2]).toBe(0);
    expect(necklaceFillToRuns(o7)).not.toEqual([3, 2, 2, 0]);
  });
});

describe("honest default stem", () => {
  it("is not sure OOE", () => {
    expect(IDEAL_STRING_LETTERS.join("")).not.toBe("OO?E");
    expect(IDEAL_STRING_BEADS.filter((bead) => bead.tone === "sure")).toHaveLength(0);
    expect(defaultStemIsNotSureOOE(DEFAULT_STEM_BEADS)).toBe(true);
    expect(SCHEMATIC_LOLLIPOP.stem).toBe("empty");
    expect(SCHEMATIC_LOLLIPOP.witness).toBeNull();
  });

  it("forces an even terminal only on O-arrival", () => {
    expect(joinFigure("launchO").terminal).toBe("even");
    expect(joinFigure("firstE").terminal).toBe("even");
    expect(joinFigure("valley").terminal).toBe("unknown");
    expect(joinFigure("thirdE").terminal).toBe("unknown");
    expect(paintStem("optionalLaunch", joinFigure("launchO")).at(-1)).toMatchObject({
      letter: "E",
      mark: "forced",
    });
    expect(paintStem("optionalLaunch", joinFigure("valley")).at(-1)).toMatchObject({
      letter: "?",
      mark: "unknown",
    });
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
      "intervalExtraEven",
      "sureEven",
      "intervalOdd",
      "sureEven",
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
    expect(IDEAL_BALLOON_INTERVALS.map(intervalSlotName)).toEqual([
      "a₁",
      "a∗",
      "e₊",
      "aₑ",
    ]);
    expect(IDEAL_BALLOON_INTERVALS.map(intervalIsMass)).toEqual([
      true,
      true,
      true,
      false,
    ]);
    expect(intervalCountBead(IDEAL_BALLOON_INTERVALS[0]!)).toEqual({
      letter: "O",
      tone: "count",
    });
    expect(intervalCountBead(IDEAL_BALLOON_INTERVALS[2]!)).toEqual({
      letter: "E",
      tone: "count",
    });
    expect(intervalCountBead(IDEAL_BALLOON_INTERVALS[3]!)).toEqual({
      letter: "O",
      tone: "count",
    });
  });

  it("classifies the six sure-letter join forks", () => {
    expect(siteRigidity("valley")).toEqual({ kind: "rigid", arr: "eArrival" });
    expect(siteRigidity("launchO")).toEqual({ kind: "rigid", arr: "oArrival" });
    expect(siteRigidity("firstE")).toEqual({ kind: "rigid", arr: "oArrival" });
    expect(siteRigidity("middleE")).toEqual({ kind: "dependsOnFill" });
    expect(siteRigidity("thirdE")).toEqual({ kind: "rigid", arr: "eArrival" });
    expect(siteRigidity("lastE")).toEqual({ kind: "dependsOnFill" });
    expect(idealJoinConfig(0).arrival).toBe("E");
    expect(idealJoinConfig(0).stemTerminal).toBe("E_or_O");
    expect(idealJoinConfig(0).fillDependent).toBe(false);
    expect(idealJoinConfig(1).arrival).toBe("O");
    expect(stemTerminalLetter(1)).toBe("E");
    expect(stemBeadsForJoin(1).at(-1)).toMatchObject({ letter: "E", mark: "forced" });
    expect(idealJoinConfig(2).forbidden.some((item) => /rotate_even_not_cycleMin/.test(item))).toBe(true);
    expect(idealJoinConfig(3).arrival).toBe("O_or_E");
    expect(idealJoinConfig(3).fillDependent).toBe(true);
    expect(idealJoinConfig(4).arrival).toBe("E");
    expect(idealJoinConfig(5).arrival).toBe("O_or_E");
    expect(stemBeadsForJoin(0).at(-1)).toMatchObject({ letter: "?", mark: "unknown" });
    expect(PIN_MISS_WORDS).toEqual(["OOEEEOOOOOE", "OOOEEEOOOOE"]);
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
    expect(SURE_LINKS).toEqual([
      [0, 1],
      [5, 0],
    ]);
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
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "empty-string")?.why).toMatch(/0\+ slot/);
  });

  it("records the Lean honesty split on the cycle figure", () => {
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "balloon-run")?.why).toMatch(
      /cycleMin_has_full_odd_even_run_form/,
    );
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "balloon-run")?.why).toMatch(
      /projection/,
    );
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "balloon-fill")?.why).toMatch(
      /not a fill/,
    );
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "leftovers")?.lemma).toContain(
      "CycleMinShape_not_of_CycleMin",
    );
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "balloon-links")?.lemma).toContain(
      "cycleMin_only_forced_adjacencies",
    );
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "balloon-seam")?.lemma).toContain(
      "cycleMin_has_two_seams",
    );
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "leftovers")?.lemma).toContain(
      "necklace_pin_misses_not_CycleMinShape",
    );
    expect(IDEAL_DECISIONS.find((decision) => decision.id === "leftovers")?.why).toMatch(
      /no_cycleMin_four_even/,
    );
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
