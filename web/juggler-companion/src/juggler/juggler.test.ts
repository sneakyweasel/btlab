import { describe, expect, it } from "vitest";
import {
  HARVESTED_LEMMA_NEEDLES,
  IDEAL_DECISIONS,
} from "../content/idealDecisions";
import { evenPreimage, oddPreimageIntegers } from "./preimages";
import {
  evenBlock,
  evenMembersMapToSeed,
  fiberBounds,
  fiberStats,
  oeFiber,
  oeMembersMapToSeed,
} from "./productions";
import {
  NECKLACE_PRESETS,
  NOTE_TRAJECTORY_3,
  NOTE_PEAK_37,
  PAPER_EXCEPTION_COUNT,
  PAPER_FLOOR,
  PAPER_L_CAP,
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
import {
  financeLattice,
  financeSnapshot,
  financeSurvivors,
  financeView,
  shippedNMax,
  survivorOf,
} from "./finance";
import {
  blockExponent,
  constantOneCrossing,
  financeBudgetConstantOne,
  necklaceView,
  oMinExact,
  thetaExact,
} from "./necklace";
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
import { EMBER, FLARE, PLUNGE, SEA, mixHex, stepPathColor } from "./palette";
import { monsterTrajectory, resolveTrajectory } from "./monsters";
import { walkTrajectory } from "./trajectory";
import {
  assembleFill,
  assembleFillCounts,
  assembleOddEvenRuns,
  cycleMinCuts,
  cycleMinShape,
  firstCycleMinCut,
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
  idealExponentApprox,
  regimeOf,
  tryAssembleFill,
} from "./itinerary";

describe("stepPathColor", () => {
  it("stays ember or sea on a flat step and runs toward flare or plunge when steep", () => {
    expect(stepPathColor(0)).toBe(EMBER);
    expect(stepPathColor(-0)).toBe(EMBER);
    expect(mixHex(EMBER, FLARE, 1)).toBe(FLARE);
    expect(mixHex(SEA, PLUNGE, 1)).toBe(PLUNGE);
    expect(stepPathColor(3)).toBe(FLARE);
    expect(stepPathColor(-3)).toBe(PLUNGE);
  });
});

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
    expect(regimeOf(17, 9)).toBe("contracting");
    expect(idealExponentApprox(9, 17)).toBeCloseTo(19683 / 131072, 6);
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

  it("finds the CycleMin cut from the O/E pattern, not from letter counts", () => {
    expect(cycleMinCuts("OOOOOOOEEEE")).toEqual([0]);
    expect(cycleMinCuts("EEOOOOOOOEE")).toEqual([2]);
    expect(firstCycleMinCut("EEOOOOOOOEE")).toBe(2);
    expect(cycleMinCuts("OOOOOOEEEOE")).toEqual([0]);
    expect(cycleMinCuts("OOOEOOEOOEE")).toEqual([0]);
    expect(cycleMinCuts("OOE")).toEqual([]);
    expect(cycleMinCuts("OEO")).toEqual([]);
    expect(firstCycleMinCut("OOE")).toBeUndefined();
    expect(cycleMinCuts("OOEEEOOOOOE")).toEqual([5]);
    expect(cycleMinCuts("OOOEEEOOOOE")).toEqual([6]);
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

describe("productions", () => {
  it("gives the even block of 6 as the evens of [36, 49)", () => {
    expect(evenBlock(6)).toEqual([36, 38, 40, 42, 44, 46, 48]);
    expect(evenMembersMapToSeed(6)).toBe(true);
  });

  it("sends every OE member of 12 to 12 in two steps", () => {
    const fiber = oeFiber(12);
    expect(fiber.map((point) => point.n)).toEqual([29]);
    expect(fiber[0]?.imageEven).toBe(true);
    expect(oeMembersMapToSeed(12)).toBe(true);
  });

  it("matches the Paper C figure fiber of 100000", () => {
    expect(fiberBounds(100000)).toEqual({ lo: 4_641_589, hi: 4_641_651 });
    expect(fiberStats(100000)).toEqual({
      m: 100000,
      H: 31,
      G: 19,
      proportion: 19 / 31,
    });
    expect(oeMembersMapToSeed(100000)).toBe(true);
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

  it("ships the 141 survivors above the floor with their n_max", () => {
    expect(financeSurvivors).toHaveLength(PAPER_EXCEPTION_COUNT);
    expect(financeSurvivors.map((row) => row.L)).toEqual(financeSnapshot.exceptionLengths);
    for (const row of financeSurvivors) {
      expect(row.nMax).toBeGreaterThan(PAPER_FLOOR);
      expect(row.L).toBeLessThanOrEqual(PAPER_L_CAP);
    }
    expect(survivorOf(26835)?.nMax).toBe(10_630_371);
    expect(financeView(26835).nMax).toBe(10_630_371);
    expect(shippedNMax(1054)).toBe(788_014);
    expect(shippedNMax(1055)).toBeNull();
  });

  it("places every survivor on the Proposition 4.9 lattice", () => {
    const [vStarL, vStarO] = financeLattice.vStar;
    const [v1054L, v1054O] = financeLattice.v1054;
    expect(vStarL * v1054O - v1054L * vStarO).toBe(1);
    for (const row of financeSurvivors) {
      expect(row.a * vStarL + row.b * v1054L).toBe(row.L);
      expect(row.a * vStarO + row.b * v1054O).toBe(row.o);
      expect(row.o).toBe(oMinExact(row.L));
    }
    const deaths = financeSurvivors.filter((row) => row.packingDeath);
    expect(deaths).toHaveLength(42);
    expect(deaths.map((row) => row.L)).toEqual(
      Array.from({ length: 42 }, (_, k) => 56347 + 1054 * k),
    );
    const slices = [1, 2, 3].map(
      (a) => financeSurvivors.filter((row) => !row.packingDeath && row.a === a).length,
    );
    expect(slices).toEqual([29, 47, 23]);
    expect(financeLattice.sliceCounts).toEqual(slices);
  });
});

describe("excursion necklace", () => {
  it("prices blocks by μ(a) = 3^a / 2^(a+1)", () => {
    expect(blockExponent(1)).toMatchObject({ num: 3n, den: 4n, regime: "contracting" });
    expect(blockExponent(2)).toMatchObject({ num: 9n, den: 8n, regime: "expanding" });
    expect(blockExponent(0)).toMatchObject({ num: 1n, den: 2n, regime: "contracting" });
    expect(blockExponent(3).approx).toBeCloseTo(27 / 16);
  });

  it("reads the walk of 365 as six excursions that fall through n", () => {
    const preset = NECKLACE_PRESETS[0];
    const view = necklaceView(preset.n, preset.word);
    expect(view.follows).toBe(true);
    expect(view.realized).toBe(preset.word);
    expect(view.excursions.map((block) => block.odds)).toEqual([2, 2, 2, 2, 1, 0, 0, 2, 0, 0]);
    expect(view.excursions.every((block) => block.complete)).toBe(true);
    expect(view.excursions[0].valley).toBe(365n);
    expect(view.excursions[0].peak).toBe(582276n);
    expect(view.excursions[0].landing).toBe(763n);
    expect(view.firstPeakOvershoots).toBe(true);
    expect(view.lastPeakLands).toBe(false);
    expect(view.returns).toBe(false);
    expect(view.belowMinimumIndex).toBe(15);
    expect(view.states[15]).toBe(34n);
  });

  it("reports where O⁷EEEE leaves the real walk of 5", () => {
    const view = necklaceView(5n, "OOOOOOOEEEE");
    expect(view.follows).toBe(false);
    expect(view.failIndex).toBe(2);
    expect(view.realized.startsWith("OOE")).toBe(true);
    expect(view.firstPeak).toBe(36n);
    expect(view.firstPeakOvershoots).toBe(true);
    expect(view.lastPeakLands).toBe(false);
  });

  it("keeps an unfinished odd-run as an incomplete block", () => {
    const view = necklaceView(3n, "OO");
    expect(view.excursions).toHaveLength(1);
    expect(view.excursions[0]).toMatchObject({ odds: 2, complete: false, peak: null });
    expect(view.firstPeak).toBeNull();
    expect(view.lastPeakLands).toBeNull();
  });

  it("computes θ(L) exactly and agrees with the shipped records", () => {
    expect(oMinExact(1)).toBe(1);
    expect(oMinExact(11)).toBe(7);
    expect(oMinExact(1054)).toBe(665);
    expect(oMinExact(25781)).toBe(16266);
    expect(oMinExact(50508)).toBe(31867);
    for (const row of financeSnapshot.records) {
      expect(oMinExact(row.L)).toBe(row.o);
    }
    const theta = thetaExact(25781);
    expect(theta.o).toBe(16266);
    expect(theta.den).toBe(3n ** 16266n);
    expect(theta.num).toBe(3n ** 16266n - 2n ** 25781n);
    expect(theta.approx).toBeCloseTo(2.5459198127264017e-5, 12);
    expect(theta.decimal.startsWith("0.0000254591")).toBe(true);
    expect(thetaExact(1)).toMatchObject({ o: 1, num: 1n, den: 3n });
    expect(thetaExact(1).decimal).toBe("0.333333333333");
  });

  it("solves the constant-1 crossing of Theorem 4.4", () => {
    const theta = thetaExact(25781);
    const n = constantOneCrossing(25781, theta.approx);
    expect(n * Math.log(n)).toBeCloseTo(25781 / theta.approx, -2);
    expect(financeBudgetConstantOne(25781, n)).toBeCloseTo(theta.approx, 12);
    expect(n).toBeGreaterThan(shippedNMax(25781)!);
  });
});
