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

  it("keeps twelve chapters and the finance voice leads", () => {
    expect(TOUR_CHAPTERS.map((chapter) => chapter.slug)).toContain("gap-transfer");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "finance")?.body).toContain("**The necklace.**");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "gap-transfer")?.body).toContain("`cycleMin_gap_transfer`");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "walk-charge")?.body).toContain("**Transport.**");
    expect(TOUR_CHAPTERS.find((chapter) => chapter.slug === "walk-charge")?.body).toContain("`cycleMin_transport`");
  });
});
