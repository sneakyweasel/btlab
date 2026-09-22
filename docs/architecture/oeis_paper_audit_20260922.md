# OEIS MCP paper audit, 22 September 2026

The local MCP was tested through its real stdio protocol against independently
computed terms from the laboratory's papers and their existing OEIS dossier.
All **28 checks passed**, covering all nine tools. The indexed export is
20 September 2026, commit `9cee00061c60192aafbc74726ce4a83ca7040d81`, with
399,397 records. This is an infrastructure audit of known identifications and
counterexamples; it makes no new mathematical claim.

## Paper examples

| Independently computed object | Retrieved entry | Scope checked |
|---|---|---|
| Integer Juggler map | A094683 | 40 terms |
| Steps to reach 1 | A007320 | 40 terms, starting at OEIS index 1 |
| Maximum orbit value | A094716 | 40 terms |
| Dropping time from odd starts | A094778 | 40 terms; 0 at the fixed point is the entry's convention |
| Survivor counts | A076227 | 40 terms |
| Binary lengths of powers of three | A020914 | 40 terms |
| Free lengths with the exceptional leading 1 | A054414 | 26 terms; also matches A136616 over this short range |
| Nonzero minimal-certificate counts | A186009 | 30 terms |
| Same counts after removing the initial term | A100982 | 30 terms |
| Terminal odd words | A260591 | 40 terms |
| Selected semiconvergent denominators | A206788 | 10 terms in order, with gaps |

The arithmetic uses exact integer square roots and a separate integer dynamic
program enforcing the prefix condition `3^o >= 2^d`. It does not copy the
candidate's terms out of OEIS and then search for them. The semiconvergent
selection is the recorded list from the
[existing neighbourhood dossier](../problems/juggler_oeis_neighbourhood.md).

## What the stress cases showed

The first six Juggler values find both A094683 and A094685. Comparing more
independently computed terms rejects A094685 at index 7: the supplied value
is 18 and its stored value is 19.

The reversed-row survivor triangle matches A214494 for the tested 24-term
prefix. Explicit comparison at stored position 1 reveals 29 matching terms
and then 30 versus 1 at stored position 30. Searching the longer 46-term
input no longer finds A214494. This is the known false identification already
recorded in the laboratory.

The free-length query also finds A136616. Extending the same computation
rejects it at index 31, where the supplied value is 84 and the stored value
is 85. Short agreement is useful for candidate retrieval, not identification.

A076227 stores only 40 terms in this export's main entry. Supplying 46
independently computed survivor counts correctly yields `insufficient_data`,
with 40 agreeing and six unchecked, rather than a disagreement.

Crucially, ten rows of A076227's **example table** agree with the joint
survivor counts and their row sums. That table is outside the integer-term
index. The prior-art correction is already recorded in
[Paper B's naming audit](../theory/paper_b_prior_art_and_names.md); this check
ensures the MCP can retrieve the evidence that a term-only search misses.

## Changes made from the audit

- Added `oeis_compare_terms`, which reports a first disagreement, explicit
  alignment, matching prefix and missing-data status for a named candidate.
- Added neighboring terms to numerical matches, plus entry-wide field counts
  so example tables remain visible even when the current page contains comments.
- Included LaTeX and bibliography sources in laboratory links, prioritized
  manuscripts, and added filters for papers, dossiers and negative knowledge.
- Updated the discovery prompt to inspect example tables and distinguish
  absent stored terms from a mismatch.
- Added a reproducible paper audit and regression tests for these behaviors.

The first upgraded run took roughly 6–175 ms per indexed query on this host.
Live laboratory links took about 3.6–3.7 seconds using the Python scan fallback
in this sandbox. These are observed single-run latencies, not performance
guarantees. The local supplementary b-file for A094683 is still an LFS pointer;
the MCP correctly reports that the content is unavailable.

Reproduce with
`python tools/oeis_paper_audit.py --output tmp/oeis_paper_audit.json`.
The JSON captures the snapshot, exact inputs, alignments, diagnoses and timings.
The operating guide describes the [tool interface](oeis_discovery.md).
