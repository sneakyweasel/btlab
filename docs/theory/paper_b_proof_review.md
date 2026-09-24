# Paper B: fresh proof audit

10 September 2026. Version 2026-09-10-proof-audit.

**Release note, 24 September 2026:** version 1.2.0 adds Section 6.1 and
Appendix D, Theorem 6.3 with its proof. This audit does not cover them;
their AI audit record and machine checks are listed in Appendix D.8 of
the manuscript. The earlier numbered results and their proofs are
unchanged, and the audit below remains their recorded evidence.

**Release note, 23 September 2026:** this historical analytic audit remains
the evidence recorded below; it is not an independent review of version
1.1.2. The current revision leaves every numbered result and its proof
unchanged. Section 6 now consistently identifies its limiting-profile
claims as conjectural or conditional, removes a broad priority assertion,
and retains the cited public antecedents. Three formula errors in that
discussion are corrected: the logarithm of the tail growth factor equals
log(rho), the coboundary Fourier coefficient is that of log(psi), and
direct integration of the stated ladder profile gives a Fourier
denominator log(r)+2*pi*i*k, not just 2*pi*i*k.
No private source is cited, quoted or packaged. Fresh finite-control,
rebuild and layout results are recorded in paper_b_release_check.json.

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

## Re-audit, 16 September 2026

Version 2026-09-16-proof-audit. The audit above is dated 10 September and the
manuscript has changed six times since, so it no longer covered the text it
certified. This pass closes that gap. It is scoped to the difference — 202 inserted
and 5 deleted lines — and does not re-derive the unchanged bulk, which continues to
rest on the audit above.

Like that one, this is an AI-assisted review. It is not independent expert review
and not formal verification.

### What changed, and what it was checked against

The substantive change is in Theorem 6.1's proof. An unquantified *for all
sufficiently large fixed d* was replaced by the sharp threshold
`q_d = p - (1-p)/(d-1)` with an explicit range `d >= 4`. Every step was checked
numerically:

| Claim | Result |
| --- | --- |
| `q_d` makes `pd - 1 >= q(d-1)` an equality | exact at `d = 3,4,5,10,100` |
| `q_4 > 1/2` reduces to `p > 5/8`, i.e. `2^8 > 3^5` | `256 > 243`, holds |
| `q_3 <= 1/2` reduces to `p <= 2/3`, i.e. `2^3 < 3^2` | `8 < 9`, holds |
| `theta(q) = q^-q (1-q)^(q-1)/2 = exp(-KL(q||1/2))` | agree to `1e-12` |
| `theta_d` decreasing, `theta_d <= theta_4 < 1` | `theta_4 = 0.999875`, monotone |
| density bound to `0`, with `theta_d -> rho` | `theta(p) = 0.9659065532` |

`theta_4 = 0.999875` makes the `d = 4` bound `0.4998`, which is vacuous. That is not
a defect: the proof takes `d -> infinity`, and the manuscript states the limit order
explicitly. The change is a genuine sharpening, and removing the unquantified clause
is worth more than the constant it gains.

Remark 6.2's printed constants were each recomputed:

| Printed | Recomputed |
| --- | --- |
| `-log theta((p+1/2)/2) = 0.0085959587` | exact |
| `-log theta(p) = 0.0346881850` | **wrong**, see below |
| convenient threshold reports `24.8%` | `24.78%` |
| `rho = 0.9659065532`, equal to `theta(p)` | exact |
| closed form `= p`, the `(1-p)` factors cancelling | exact, and the algebra checks |
| overshoot `1.2e6` at `d=320`, `6.9e17` at `d=1280` | `1.246e6`, `6.864e17` |
| `psi/p` samples `16.4, 17.0, 16.6` at `d=640,1280,2560` | `16.39, 17.04, 16.64` |
| mean of `psi` about `10.9` | `10.888` asymptotically |

The count recursion `N_(d+1) = 2N_d - b_d M_d` was checked to be equivalent to
`P_(d+1) = P_d(1 - b_d R_d / 2)` under `P_d = N_d/2^d` and `R_d = M_d/N_d`, and the
stated `T_0`, `T_1` match the implementation they are checked against.

### Finding

One defect. `-log theta(p)` was printed as `0.0346881850`; the value is
`0.0346881852320175`, which rounds to `0.0346881852`. Misrounded in the last two
digits. Repaired in this version. Nothing depends on the digits beyond the eighth,
and no conclusion moves.

Two checks that look like findings and are not. The mean of `psi` reads `10.576` over
`d = 500..3000` against a printed `10.9`; it converges upward — `10.814`, `10.871`,
`10.884`, `10.888` over successive windows to `d = 1.2e5` — so the printed value is
the asymptotic one and is right. And the overshoot figures disagree by a factor of
350 if measured against `p rho^d`; they are measured against the true density
`psi rho^d d^(-3/2)`, and against that they are right. Both are recorded because a
reader repeating the check will hit them.

### What this pass does not cover

The analytic core — Theorem 4.11, Theorem 5.4, Appendices A to C — is unchanged and
was not re-derived here. The estimates were not re-checked against their parameter
ranges; that was the 10 September pass's work and it stands or falls on its own.

Part of the audited difference is text added on 16 September by the same agent
performing this audit — the revised *what is open, and what is excluded* discussion
in Remark 6.2. Self-review carries less weight than the rest of this pass and should
be read as unaudited.

### Decision

Unchanged: **PROMOTE** for author and expert review. This pass removes the
staleness objection — the manuscript is now audited as it stands rather than as it
stood five revisions ago — and repairs one misrounded constant. It does not supply
independent expert review, and it does not extend the formal layer, which by its own
barrel's statement contains no estimate. Those two remain the substantive reasons
not to treat the manuscript as certified, and neither is a defect in the text.
