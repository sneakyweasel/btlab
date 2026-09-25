import { describe, expect, it } from "vitest";
import {
  ATLAS_CLAIMS, EVIDENCE_LABEL, GAME_FAMILIES, SLOPES, denominators, lowerDim, starDim,
  twoScaleDim, upperDim, type Pattern,
} from "./beattyAtlas";
import gameData from "../../../../data/research/juggler/winkler_phase_collapse/dimension_game.json";
import ledgerData from "../../../../docs/claims/juggler/beatty_first_passage.json";

const game = gameData as unknown as {
  periods: number;
  families: { family: string; pattern: [string, number][]; upper: number; lower: number; closed_form?: number }[];
};

describe("dimension game port", () => {
  it("covers the committed families in the same order", () => {
    expect(GAME_FAMILIES.map(f => f.name)).toEqual(game.families.map(f => f.family));
    for (const [index, family] of game.families.entries()) {
      expect(GAME_FAMILIES[index].pattern.map(e => [e.kind, e.t])).toEqual(family.pattern);
    }
  });

  it("reproduces the committed upper thresholds bit for bit", () => {
    for (const [index, family] of game.families.entries()) {
      expect(upperDim(GAME_FAMILIES[index].pattern, game.periods)).toBe(family.upper);
    }
  });

  it("reaches the committed window-measure values", () => {
    for (const [index, family] of game.families.entries()) {
      expect(Math.abs(lowerDim(GAME_FAMILIES[index].pattern).s - family.lower)).toBeLessThan(1e-9);
    }
  });

  it("matches the two-scale closed form and its limits", () => {
    for (const family of game.families.filter(f => f.closed_form !== undefined)) {
      const [[, nu], [, rho]] = family.pattern;
      expect(twoScaleDim(nu, rho).s).toBeCloseTo(family.closed_form!, 14);
    }
    expect(twoScaleDim(2, 1 + 3 / 2).s).toBeCloseTo(0.5, 14);
    expect(twoScaleDim(3, 1e12).s).toBeCloseTo(starDim(3), 5);
    const pattern: Pattern = [{ kind: "g", t: 2.5 }, { kind: "d", t: 7 }];
    expect(upperDim(pattern)).toBeCloseTo(twoScaleDim(2.5, 7).s, 9);
  });
});

describe("atlas sources", () => {
  const ledger = ledgerData as { id: string; tag: string }[];
  const tags = new Map(ledger.map(row => [row.id, row.tag]));

  it("cites every claim with the ledger's current evidence label", () => {
    const cited = new Set(Object.keys(ATLAS_CLAIMS));
    for (const slope of SLOPES) for (const s of slope.statements) if (s.claim) cited.add(s.claim);
    for (const id of cited) {
      expect(tags.get(id), id).toBe(EVIDENCE_LABEL[ATLAS_CLAIMS[id]]);
    }
    for (const slope of SLOPES) for (const s of slope.statements) {
      if (s.claim) expect(EVIDENCE_LABEL[s.evidence], s.claim).toBe(tags.get(s.claim));
    }
  });

  it("keeps the Arb-certified prefixes (last convergent denominators)", () => {
    const q = (key: string) => denominators(SLOPES.find(s => s.key === key)!.quotients).at(-1);
    expect(q("log23")).toBe(27444133206411171953n);
    expect(q("e")).toBe(1075253811351460636n);
  });
});
