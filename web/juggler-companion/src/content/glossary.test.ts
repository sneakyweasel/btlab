import { describe, expect, it } from "vitest";
import katex from "katex";
import { TOUR_CHAPTERS } from "./glossary";

function mathSpans(text: string): string[] {
  return [...text.matchAll(/\$([^$\n]+)\$/g)].map((match) => match[1]);
}

describe("tour glossary markup", () => {
  it("has no tab characters from mangled LaTeX escapes", () => {
    for (const chapter of TOUR_CHAPTERS) {
      const blob = `${chapter.term}\n${chapter.blurb}\n${chapter.body}\n${chapter.paper}`;
      expect(blob.includes("\t"), chapter.slug).toBe(false);
    }
  });

  it("renders every $...$ span in KaTeX", () => {
    for (const chapter of TOUR_CHAPTERS) {
      const blob = `${chapter.blurb}\n${chapter.body}\n${chapter.paper}`;
      for (const math of mathSpans(blob)) {
        expect(() => katex.renderToString(math, { throwOnError: true }), `${chapter.slug}: $${math}$`).not.toThrow();
      }
    }
  });

  it("keeps fourteen Paper A chapters and the finance voice leads", () => {
    expect(TOUR_CHAPTERS).toHaveLength(14);
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).not.toContain("preimages");
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).not.toContain("oe-fiber");
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).not.toContain("block-average");
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).not.toContain("three-sources");
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).not.toContain("v-ladder");
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).toContain("fan");
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).toContain("cubic-band");
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).toContain("height-gap");
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).toContain("upper-cells");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "finance")?.body).toContain("**The necklace.**");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "gap-transfer")?.body).toContain("`cycleMin_gap_transfer`");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "walk-charge")?.body).toContain("`cycleMin_transport`");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "walk-charge")?.body).toContain("OstrowskiSandwich.lean");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "fan")?.body).toContain("**The progression.**");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "fan")?.body).toContain("fanLambda_55_pos");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "cubic-band")?.body).toContain("mechanical word");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "height-gap")?.body).toContain("m^{15/8}");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "upper-cells")?.body).toContain("520{,}000{,}000");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "upper-cells")?.body).toContain("does not exclude");
  });
});
