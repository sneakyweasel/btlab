import { describe, expect, it } from "vitest";
import { BEATTY_CLAIMS, BEATTY_THEMES, beattyTheme, beattyTimeline, tagCounts } from "./beattyProgress";

describe("Beatty progress snapshot", () => {
  it("classifies every claim into one theme and keeps IDs unique", () => {
    expect(BEATTY_CLAIMS.length).toBeGreaterThan(0);
    expect(new Set(BEATTY_CLAIMS.map(c => c.id)).size).toBe(BEATTY_CLAIMS.length);
    const keys = BEATTY_THEMES.map(t => t.key) as string[];
    for (const claim of BEATTY_CLAIMS) expect(keys).toContain(claim.theme);
    for (const theme of BEATTY_THEMES) expect(BEATTY_CLAIMS.some(c => c.theme === theme.key)).toBe(true);
  });

  it("routes representative IDs to the intended theme", () => {
    expect(beattyTheme("J-beatty-slope-gamma-hausdorff")).toBe("gamma");
    expect(beattyTheme("J-beatty-slope-minkowski-content")).toBe("geometry");
    expect(beattyTheme("J-beatty-slope-global-law")).toBe("laws");
    expect(beattyTheme("J-beatty-slope-complete-cluster-set")).toBe("profile");
    expect(beattyTheme("J-beatty-survivor-counting-identity")).toBe("counting");
    expect(() => beattyTheme("J-beatty-unknown")).toThrow();
  });

  it("counts every claim once in the tag totals and the timeline", () => {
    const counts = tagCounts(BEATTY_CLAIMS);
    expect(Object.values(counts).reduce((a, b) => a + b, 0)).toBe(BEATTY_CLAIMS.length);
    const timeline = beattyTimeline(BEATTY_CLAIMS);
    expect(timeline.length).toBe(BEATTY_CLAIMS.filter(c => c.firstRecorded).length);
    for (let i = 1; i < timeline.length; i++) expect(timeline[i].time).toBeGreaterThanOrEqual(timeline[i - 1].time);
    expect(timeline.at(-1)?.lean).toBe(counts["EXACT — LEAN VERIFIED"] ?? 0);
  });
});
