export type PaperLetter = "A" | "B" | "C" | "D";

export type PaperRecord = {
  letter: PaperLetter;
  title: string;
  hint: string;
  doi?: string;
  zenodo?: string;
  guide?: { to: string; label: string };
};

export const PAPERS: readonly PaperRecord[] = [
  {
    letter: "A",
    title: "Cycles",
    hint: "How long a hypothetical cycle would have to be, given a certified floor. Not a halt theorem.",
    doi: "10.5281/zenodo.22676453",
    zenodo: "https://zenodo.org/records/22676453",
    guide: { to: "/tour/the-map", label: "Tour" },
  },
  {
    letter: "B",
    title: "Five-Step Descent Certificates for the Juggler Map",
    hint: "Five-step power-envelope certificate density 7/8; complete OOOEE proof included. AI-assisted preprint; independent review outstanding.",
    doi: "10.5281/zenodo.22864934",
    zenodo: "https://zenodo.org/records/22864934",
  },
  {
    letter: "C",
    title: "Fates",
    hint: "Every nonempty preimage-closed set has a log-mass lower bound. No fate is excluded.",
    doi: "10.5281/zenodo.22678165",
    zenodo: "https://zenodo.org/records/22678165",
    guide: { to: "/play/preimages", label: "Play" },
  },
  {
    letter: "D",
    title: "No m-cycles of the 3n-1 map for m <= 58",
    hint: "The Collatz side, not the Juggler map: no m-cycle of 3n-1 with m at most 58, from this laboratory's own verification floor. Conditional on Rhin's measure.",
    doi: "10.5281/zenodo.22876190",
    zenodo: "https://zenodo.org/records/22876190",
  },
];

// The site used to ship a copy of each PDF under public/papers/. Every paper
// is deposited on Zenodo now, so the record is the download and the repository
// keeps exactly one copy, in juggler_review/.

export function paperDoiHref(doi: string): string {
  return `https://doi.org/${doi}`;
}

export function paperByLetter(letter: PaperLetter): PaperRecord {
  const paper = PAPERS.find((row) => row.letter === letter);
  if (!paper) throw new Error(`Unknown paper ${letter}`);
  return paper;
}
