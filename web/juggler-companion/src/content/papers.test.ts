import { describe, expect, it } from "vitest";
import { PAPERS, paperByLetter, paperDoiHref } from "./papers";

describe("published preprint records", () => {
  it("pins Paper A and Paper C to the Zenodo version DOIs", () => {
    expect(paperByLetter("A").doi).toBe("10.5281/zenodo.22676453");
    expect(paperByLetter("A").zenodo).toBe("https://zenodo.org/records/22676453");
    expect(paperDoiHref(paperByLetter("A").doi!)).toBe(
      "https://doi.org/10.5281/zenodo.22676453",
    );
    expect(paperByLetter("C").doi).toBe("10.5281/zenodo.22678165");
    expect(paperByLetter("C").zenodo).toBe("https://zenodo.org/records/22678165");
    expect(paperDoiHref(paperByLetter("C").doi!)).toBe(
      "https://doi.org/10.5281/zenodo.22678165",
    );
  });

  it("pins Paper B to its Zenodo version DOI and keeps it off the guides", () => {
    expect(paperByLetter("B").doi).toBe("10.5281/zenodo.22864934");
    expect(paperByLetter("B").zenodo).toBe("https://zenodo.org/records/22864934");
    expect(paperDoiHref(paperByLetter("B").doi!)).toBe("https://doi.org/10.5281/zenodo.22864934");
    expect(paperByLetter("B").guide).toBeUndefined();
    expect(paperByLetter("B").hint).toContain("Five-step power-envelope certificate density 7/8");
  });

  it("sends Paper A to the tour and Paper C to the contagion walk", () => {
    expect(paperByLetter("A").guide).toEqual({ to: "/tour/the-map", label: "Tour" });
    expect(paperByLetter("C").guide).toEqual({
      to: "/play/preimages",
      label: "Play",
    });
  });

  it("carries all three papers and ships no local PDF copy", () => {
    // The site linked its own public/papers/ copies until every paper had a
    // deposit. It links the records now, so a paper with no Zenodo link would
    // be unreachable rather than merely un-cited.
    expect(PAPERS.map((paper) => paper.letter)).toEqual(["A", "B", "C"]);
    for (const paper of PAPERS) {
      expect(paper.doi).toBeTruthy();
      expect(paper.zenodo).toMatch(/^https:\/\/zenodo\.org\/records\/\d+$/);
      expect(paper).not.toHaveProperty("pdf");
    }
  });
});
