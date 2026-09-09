import { describe, expect, it } from "vitest";
import { PAPERS, paperByLetter, paperDoiHref, paperPdfHref } from "./papers";

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

  it("keeps Paper B as a local PDF until it has a deposit", () => {
    expect(paperByLetter("B").doi).toBeUndefined();
    expect(paperByLetter("B").zenodo).toBeUndefined();
    expect(paperByLetter("B").guide).toBeUndefined();
    expect(paperByLetter("B").hint).toContain("3/4");
  });

  it("sends Paper A to the tour and Paper C to the contagion walk", () => {
    expect(paperByLetter("A").guide).toEqual({ to: "/tour/the-map", label: "Tour" });
    expect(paperByLetter("C").guide).toEqual({
      to: "/play/preimages",
      label: "Play",
    });
  });

  it("serves each manuscript from public/papers", () => {
    expect(PAPERS.map((paper) => paper.letter)).toEqual(["A", "B", "C"]);
    expect(paperPdfHref(paperByLetter("A"))).toContain(
      "papers/juggler_finite_dynamics_note.pdf",
    );
  });
});
