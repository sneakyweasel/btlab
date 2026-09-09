export type PaperLetter = "A" | "B" | "C";

export type PaperRecord = {
  letter: PaperLetter;
  title: string;
  hint: string;
  pdf: string;
  doi?: string;
  zenodo?: string;
  guide?: { to: string; label: string };
};

export const PAPERS: readonly PaperRecord[] = [
  {
    letter: "A",
    title: "Cycles",
    hint: "How long a hypothetical cycle would have to be, given a certified floor. Not a halt theorem.",
    pdf: "juggler_finite_dynamics_note.pdf",
    doi: "10.5281/zenodo.22676453",
    zenodo: "https://zenodo.org/records/22676453",
    guide: { to: "/tour/the-map", label: "Tour" },
  },
  {
    letter: "B",
    title: "Parity",
    hint: "Unconditional certificate subfamily density 27/32 within five steps; full five-step density 7/8 requires OOOEE. The general kernel remains unproved.",
    pdf: "juggler_parity_discrepancy_note.pdf",
  },
  {
    letter: "C",
    title: "Fates",
    hint: "Every nonempty preimage-closed set has a log-mass lower bound. No fate is excluded.",
    pdf: "juggler_fate_almost_all_note.pdf",
    doi: "10.5281/zenodo.22678165",
    zenodo: "https://zenodo.org/records/22678165",
    guide: { to: "/play/preimages", label: "Play" },
  },
];

export function paperPdfHref(paper: PaperRecord): string {
  return `${import.meta.env.BASE_URL}papers/${paper.pdf}`;
}

export function paperDoiHref(doi: string): string {
  return `https://doi.org/${doi}`;
}

export function paperByLetter(letter: PaperLetter): PaperRecord {
  const paper = PAPERS.find((row) => row.letter === letter);
  if (!paper) throw new Error(`Unknown paper ${letter}`);
  return paper;
}
