# Paper B: fresh proof audit

10 September 2026. Version 2026-09-10-proof-audit.

## Outcome

This review read the full consolidated manuscript, traced its dependency
chain, checked the analytic estimates against their actual parameter
ranges, and derived the critical curvature coefficients afresh.
It identified one missing extension in the written Fourier lemma and
several notation and citation defects. These are repaired in this version.
No unresolved gap was identified in the stated five-step argument after
those repairs. This is a further AI-assisted review, not independent
expert review or complete formal verification.

The retained conclusion is Theorem 5.4: the power-envelope certificate
class through five operations has count
7N/8 + O_epsilon(N^(127/128+epsilon)). This does not count every actual
five-step descender and does not prove universal termination.

## Findings and repairs

1. **Missing Fourier domain and variation statement.** Lemma 4.7 originally
   covered residuals in [0,1] and monotone residual functions. Appendix C
   applies it to bounded signed residuals, whose remainder need not be
   monotone. The new bounded-residual extension proves the pointwise
   expansion uniformly on any fixed bounded real interval and bounds
   coefficient variation by total variation of the residual. Appendix C
   now explicitly verifies that condition. No extra power of P is lost.
2. **Undefined parity sign.** The paper used psi before defining it. Section
   2 now defines psi(t)=(-1)^floor(t), with its exact half-open interval
   formula, and introduces the exponential and distance notation.
3. **Shift convention.** Appendix A now explicitly distinguishes actual
   translations Delta_d from Section 4.2's half-shift convention.
4. **Ambiguous derivative assertion.** The small derivative following
   (C.17) belongs to the remainder after removing the growing leading
   coefficient. The new text separates the two derivatives and gives
   the variation bound using the original-run length.
5. **Typesetting and symbol collisions.** Multi-digit subscripts now use
   braces; an incorrectly spelled Phi and printed caret expressions are
   repaired. The smooth twist in Appendix C is called phi_0, avoiding
   reuse of the parity-sign symbol psi.
6. **Broken reference.** The Kuipers--Niederreiter URL contained inserted
   mathematics and spaces. Its link is restored and checked. Source
   validation now catches undefined notation and malformed external links.

## Proof obligations examined

| Part | Audit conclusion |
|---|---|
| Proposition 2.1 and Lemma 2.2 | Envelope induction and exact branch product retain floors and endpoint conventions. |
| Theorem 3.1 and Proposition 3.2 | Curvature dominance, weighted modes, and dyadic cutoffs justify the stated single-floor counts. |
| Propositions 4.1--4.2 | Formal-chain correlations imply word counts; all nonzero mixed modes, including zero coordinates, are required. |
| Lemmas 4.3--4.4 and Theorem 4.5 | Small-shift floor deletion, carry cells, harmonic weights, and both differencing terms fit exponent 23/24. |
| Lemmas 4.7--4.8 and Theorem 4.9 | The centered cancellation is exact; local suprema are summed with every interval boundary and a single global positive-error charge. |
| Appendix A | Slow-floor exceptions are counted on original runs; large coefficients do not multiply floor mismatches; master carries give the stated signed inventory. |
| Appendix B | After differencing, widened D1 terms are smaller than the main curvature for all but finitely many shifts; those small shifts fit the diagonal term. D2 errors and all added boundaries fit 15/16 before the final square root. |
| Appendix C, k=0 | Nonzero j, nonzero l with j=0, and the remaining pure i mode are treated separately without using the target estimate. |
| Appendix C, nonzero total Y mode | Fixed labels, piecewise amplitudes, bounded residuals, third-derivative bound, and local partition count meet Theorem B.1. |
| Appendix C, zero total Y mode | Floor levels are included in the derivative partition; the two offset cases have the stated leading coefficients and strict frequency separation. |
| Corollary 4.12 and Theorems 5.2--5.4 | Dyadic discrepancy gives the actual words through formal sign classes; disjoint minimal certificates sum to 7/8. |
| Theorem 6.1 | Density-one certificates remain conditional on fixed-depth fair shares, with the limits taken in the stated order. |
| Section 7 | Exact defect identities and the shift-averaged estimate do not imply the specified unaveraged kernel or localization. The basic collision model retains its separate hypotheses. |

## Fresh symbolic calculation

The optional script derive_paper_b_review.py uses SymPy to differentiate
the exact four-corner powers in an auxiliary shift, extracts their leading
terms, composes with X, differentiates with every label fixed, and only
then substitutes moving label values. It does not import the earlier
curvature validators.

The nonzero-offset pieces are 945/512, -27/16, and -81/128, totaling
-243/512. The zero-offset pieces are -6075/2048, 243/128, and 729/256,
totaling 3645/2048. The k=0 fifth-coordinate calculation gives 81/512.
These confirm the signs and coefficients used by the written proof.
They do not establish uniform remainder bounds or asymptotic cancellation.

## Primary references checked

The second-derivative estimate is Graham--Kolesnik, Theorem 2.2, p. 8:
two continuous derivatives and comparable nonzero absolute curvature on
the tested interval. The differencing inequality is Lemma 2.5, p. 10;
it permits complex sequences supported on an interval. Both were inspected
in the [publisher excerpt](https://beckassets.blob.core.windows.net/product/readingsample/666252/9780521339278_excerpt_001.pdf).

The multidimensional discrepancy inequality and its product weight are
given on p. 116 of
[Kuipers--Niederreiter](https://web.maths.unsw.edu.au/~josefdick/preprints/KuipersNied_book.pdf).
The Juggler definition was checked against the
[OEIS sequence record](https://oeis.org/A094683).

## Remaining limits

The stronger historical 95/96 kernel target, arbitrary decorated kernels,
short-interval localization, and all-depth fair-share hypotheses remain
open. The existing validators check finite algebra and exponent
bookkeeping; they are not proof certificates for cancellation.
The release check records the current build, source hashes, rendered-page
inspection, standalone source rebuild, and repository checks. Earlier
audit reports retain their historical dates and scope.

Decision: **PROMOTE** the corrected manuscript for author and expert
review. No external publication, DOI operation, or claim of independent
mathematical certification was made.
