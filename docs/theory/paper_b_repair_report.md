> **OOEOE follow-up, 9 September 2026:** the current manuscript also proves the OOEOE split and a certificate subfamily of density 27/32. The full five-step density 7/8 now requires only OOOEE. This report records an earlier review stage; see [the current report](paper_b_ooeoe_report.md).

# Paper B: proof-repair report

9 September 2026. Version: 2026-09-09-four-step-repair.

**Outcome:** the four-step power-envelope certificate density **13/16 is restored unconditionally**, with a complete replacement proof in the manuscript. The five-step density 7/8 remains conditional. The revised subtitle is *Four-Step Descent and Conditional Extensions for the Juggler Map*.

## What is repaired

Theorem 4.5 proves a mixed exponential-sum bound \(O_C(P^{23/24})\) for the phase
\[
\frac i2 n^{3/2}+\frac j2\lfloor n^{3/2}\rfloor^{3/2}+\frac k2n^{9/8},
\qquad 0<\max(|i|,|j|,|k|)\le CP^{1/24},
\]
for each fixed \(C\). The proof works on odd starting values and includes mixed signs and zero coordinates. It does not invoke the old decorated-kernel lemma.

The key restriction is \(h\le P^{1/12}\), hence \(uh\ll P^{1/8}\) for \(u=|j|/2\). After differencing, deleting the small floor term costs \(O(uhP^{3/4})\). The carry is expanded exactly before Fourier truncation. Its truncated sawtooth error is bounded using the independently proved single-floor discrepancy. The zero mode and every nonzero Fourier mode are estimated separately on **every gap cell**, with monotone amplitudes handled by partial summation. Nonzero Fourier curvature dominates in this range, so the large-parameter collision argument is unnecessary.

Corollary 4.6 transfers this bound to all eight sign classes of
\((\psi(n^{3/2}),\psi(m^{3/2}),\psi(v^{1/2}))\), where
\(m=\lfloor n^{3/2}\rfloor\) and \(v=\lfloor m^{3/2}\rfloor\).
Each count is \(N/16+O(N^{23/24}(\log(2N))^3)\). Theorem 5.2 therefore counts the disjoint minimal certificate prefixes \(E,OE,OOEE\) with total density 13/16. This counts a sufficient certificate class; it does not identify every start that happens to descend within four operations.

Proposition 3.2 repairs the OE-branch third-letter estimate using
\[
\lfloor\sqrt{\lfloor x\rfloor}\rfloor=\lfloor\sqrt{x}\rfloor
\quad(x\ge0).
\]
Thus its parity reduction is exact. A cutoff \(P^{1/6}\) gives the OEE and OEO counts with error \(O(N^{5/6}\log(2N))\), replacing the inconsistent truncation in the historical proof.

Lemma 7.5 supplies a correct second-derivative estimate over a partition when a reference curvature has controlled sublevel sets. Proposition 7.6 verifies those hypotheses for the basic frozen-gap collision phase. The transition cost is paid using a global sublevel count, while the ordinary cell-boundary term remains in the estimate. This repairs the model-level cell-counting issue; applying it to the entire decorated Fourier expansion still requires additional work.

## Status of the original gaps

| Issue | Current result |
|---|---|
| Nested estimate needed for four-step certificates | Repaired by Lemmas 4.3–4.4, Theorem 4.5, and Corollary 4.6 |
| OE-branch truncation | Repaired by the exact square-root identity and a fresh discrepancy proof |
| Gap-cell collision counting | Repaired for the basic model in Lemma 7.5 and Proposition 7.6; full decorated-family assembly unproved |
| Half-integer frequencies | Handled directly in the restricted proof by \(u=\lvert j\rvert/2\ge1/2\); no unproved extension of the general decorated lemma is used |
| Global-to-short-interval rescaling | Not repaired for the general kernel; the old \(P^{29/48+\delta}\) threshold is not restored |
| Effective numerical threshold | Not restored; the new analytic estimates use implicit constants and do not certify \(3.6\cdot10^{13}\) |
| Five-step density 7/8 | Conditional on the two remaining formal-chain hypotheses for OOOEE and OOEOE |
| Density-one certificates | Conditional on fixed-depth itinerary equidistribution; no termination theorem |

## Validation and its limits

The new exact-arithmetic script passes 1,920 differenced-identity checks, 2,000 carry-expansion checks, and 40 exponent comparisons. The existing script's 35,582 exact checks also pass. These are reproducibility and bookkeeping checks; the asymptotic results rest on the printed analytic arguments.

The final PDF is rebuilt from the repaired source, with all pages inspected. Build assets, metadata, and source ZIPs are updated to the repaired version. The original 4 September draft remains preserved for historical audits. This repair adds no Lean formalization and claims no independent peer review.

## Decision

**PROMOTE** the restricted mixed-sum estimate, unconditional four-step density, OE count, and basic partition-aware collision estimate into Paper B. Keep the general decorated kernel and its downstream five-step claims at their stated conditional status.

The best next question is whether every decorated phase and coefficient family in the old kernel proof admits the reference-curvature and partition bounds of Lemma 7.5, with a total weighted cost that preserves the claimed saving. A local-length rescaling cannot replace that verification.

No Zenodo deposit or public upload was made.
