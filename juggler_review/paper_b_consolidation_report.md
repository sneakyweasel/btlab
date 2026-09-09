# Paper B: consolidation and publication audit

9 September 2026. Version 2026-09-09-five-step-consolidated.

## Result

The manuscript now contains the entire OOOEE proof chain. Theorem 4.11
proves its four-coordinate mixed-mode bound with exponent 127/128;
Corollary 4.12 counts OOOEE, and Theorem 5.4 proves full five-step
power-envelope certificate density 7/8 with error
O_epsilon(N^(127/128+epsilon)).

Appendices A-C supply the floor reduction, joint carry expansions,
positive Fourier errors, master inventory, wave-bearing bound, and
complete mixed-mode argument. Separate research notes are no longer
required to establish the manuscript's result.

## Mathematical audit

| Obligation | Verified argument |
|---|---|
| Floor errors | Monotone counting on original runs; no extra charge per frequency cell |
| Large floor coefficients | Compare unit exponentials on exceptions; do not multiply their counts by the coefficient |
| Positive Fourier errors | Global nonnegative majorants before an anchor estimate |
| Signs and zero coordinates | All four frequency signs, k=0 cases, integer total Y frequency, half-integer slow D frequency |
| Frozen curvature | Differentiate with labels and centers fixed; substitute their values afterwards |
| Nonzero offset | Complete mixed coefficient -243/512, including the integer-floor term |
| Zero offset | Coefficient 3645/2048 with negative moving centers and separated integer frequency scales |
| Weights and partitions | Logarithmic coefficient mass and variation; all runs, windows, arcs, and permitted floor-level cuts |
| Outer differencing | 31/32 to 63/64 to 127/128; both diagonal terms fit |
| Counting transfer | Discrepancy on each dyadic block with its own cutoff |
| Interpretation | Count of the certificate class; formal signs and actual words distinguished |

No surviving proof gap was identified in this consolidation audit.
The result remains an AI-assisted written proof. This is not independent
mathematical review, and finite controls do not prove cancellation.

Prepared fields were checked against
[Zenodo's record-description guidance](https://help.zenodo.org/docs/deposit/describe-records/).

## Publication preparation

The abstract, main theorem, status table, disclosure, metadata, and
reading guides describe the same result. The stronger 95/96 target,
arbitrary decorations, localization, and all-depth hypotheses stay open.

All 36 pages were rendered and inspected. The build rejects overfull
boxes, missing glyphs, and undefined references. The source archive
contains every build and validator dependency. The release check records
hashes, standalone rebuild verification, and repository test outcomes.

Decision: **PROMOTE** the consolidated manuscript and local package
for author review. No upload, DOI reservation, independent peer-review
certification, or termination claim is made.
