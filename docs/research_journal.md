# Recent research decisions

The latest twelve entries are kept here for orientation. Durable statements,
proofs and decisions belong in the [claim ledger](theory/theorem_ledger.md),
branch dossiers and proof maps. Search those records before relying on an older
journal claim; later proofs can supersede earlier open boundaries.

Earlier chronology is recoverable from Git; the full journal before this
consolidation is at `e9725762eaf028d1ace354ff20e0fc48f1a3d143`. See
[recovery instructions](history.md).
New entries should name the changed result, its evidence, remaining premise,
decision, and canonical record. Keep the journal brief.

## 2026-09-25 -- Paper B Proposition 7.4 in Lean

**EXACT — LEAN VERIFIED:** `|∫_0^1 |S_λ|^2 - L| ≤ (4/π)(L/a)(1 + log L)` and the
exceptional shifts have measure at most `η`, with the printed constants. Each off-diagonal
term is two affine pieces over a period starting at a breakpoint. Remaining premise: none.
Decision: PROMOTE. Record: [shift-average dossier](problems/juggler_paper_b_shift_average.md).

## 2026-09-25 -- Paper B Lemma 4.3, bound (4.3), in Lean

**EXACT — LEAN VERIFIED:** over odd starts `2r+1`, `r ∈ [r₀, r₁)`,
`∑ E_R(n^{3/2}) ≤ 4 (r₁ - r₀)(⌊log₂ R⌋ + 2)/R + 25344 r₁^{5/6}`, the printed (4.3) with
constants. Theorem 3.1's discrepancy holds for every arc, and a dyadic layer bound on `E_R`
finishes it. Remaining premise: the first assertion `b = b_R + O(E_R)` is not formalized.
Decision: PROMOTE. Record: [carry-expansion dossier](problems/juggler_paper_b_carry_expansion.md).

## 2026-09-25 -- Paper B Proposition 3.2 closed in Lean

**EXACT — LEAN VERIFIED:** for `N ≥ 1` and `w ∈ {OEE, OEO}`,
`|#{n ≤ N : word_3(n) = w} - N/8| ≤ 6849 N^{5/6} (1 + log N)`. The input is the
two-dimensional Erdős–Turán inequality with main term `N/H` (`BTCalculus.ErdosTuranBox`), the
one-dimensional extreme-discrepancy argument lifted with the product Fejér kernel. Remaining
premise: none for Proposition 3.2. Decision: PROMOTE. This entry replaces the morning's
two-dimensional entry. Record: [OE third-letter dossier](problems/juggler_paper_b_oe_third_letter.md).

## 2026-09-25 -- Paper B Theorem 3.1 closed in Lean

**EXACT — LEAN VERIFIED:** `|S_O(N)| ≤ 2112 N^{5/6}` for every `N`, and both
counts are within `1057 N^{5/6}` of `N/4` and `3N/4`. The missing input was an
Erdős–Turán inequality with main term `N/H`. `BTCalculus.ErdosTuran` proves it
from the existing Fejér kernel: arc translates are compared with the extreme
discrepancy rather than with `N`, with no Selberg polynomial. Remaining premise:
none for Theorem 3.1. Proposition 3.2 needs the two-dimensional lift.
Decision: PROMOTE. This entry replaces the two 24 September Theorem 3.1
entries. Record: [single-floor dossier](problems/juggler_paper_b_single_floor.md).

## 2026-09-24 -- Paper C 1.3.0 published with contagion 37/50

**EXACT — HUMAN PROOF (one written input, not human-reviewed):** Paper C's new
Theorem 5.20 feeds the two depth-five productions into the recursion through
Paper B's published Theorem 6.3, raising contagion from `5/8` to `37/50` and
lowering the sufficient rate threshold from `3/8` to `13/50`; the deduction and
the recursion are kernel-checked. The owner chose this headline before human
review, which supersedes the wait noted in the Paper B entry. The log-mass bound
at `5/8`, with the threshold `3/8`, is now kernel-checked, since
`FateOOEEWeighted` proves the OOEE production; Paper C's 1.2.0 text predated
that, and the ledger keeps that row at EXACT — HUMAN PROOF until its statement
coverage is audited. The least depth constants drop to 14 (fair) and 14, 28,
132, 866 (one-sided) at `13/50`, each Arb-certified from `C = 5`. Remaining
premise: human review of Paper B's Appendix D. Decision: published 24 September
2026, doi:10.5281/zenodo.22947659; no Paper B 1.2.1 for its now-stale D.8
sentence. Record: [depth-five dossier](problems/juggler_depth_five_production.md),
Results 37 and 38, and the [deposit record](theory/paper_deposits.md).

## 2026-09-24 -- Paper B 1.2.0 published with the depth-five fair-share theorem

**EXACT — HUMAN PROOF (AI-written, AI-audited, not human-reviewed):** Paper B's
Theorem 6.3 states that, for `OOOEE` and `OOEOE`, the targets whose fibre misses
the share `1/16` by `eta` have reciprocal sums `O(y_0^(-1/55))` and
`O(y_0^(-1/41))` beyond `y_0`. Appendix D writes the proof, dossier Lemmas
E5-E9. An AI review of the new text found two gaps and two overstatements, all
repaired, and every Paper B release gate passes. Remaining premise: human review
of Appendix D. Decision: published 24 September 2026, doi:10.5281/zenodo.22946276;
Paper C's `0.74` update waits for that review. Record: [depth-five dossier](problems/juggler_depth_five_production.md),
Result 36, and the [deposit record](theory/paper_deposits.md).

## 2026-09-24 -- Beatty cluster sets have dimension 2/3 for almost every slope

**EXACT — LEAN VERIFIED** for the whole irrational family: every cluster set
`K_alpha` has finite two-thirds Hausdorff measure, and Diophantine bounds give
matching lower bounds through the family CDF. Mathlib's null set of
`LiouvilleWith` numbers gives `dim_H K_alpha=2/3` for Lebesgue-almost every
`alpha>1`; the quadratic norm form gives positive finite two-thirds measure
for every quadratic irrational slope, including the golden ratio. At every
Liouville slope the dimension is `0`, so Hausdorff dimension depends on the
arithmetic of the slope while Minkowski dimension stays `2/3`; the critical
measure is positive exactly at badly approximable slopes, and exponent-`nu`
approximations bound the dimension by `2/(2+sqrt nu)`.
Continuation, also **EXACT — LEAN VERIFIED**: counts are locally constant
at irrational boundaries, the weights converge in `l1` by a Scheffé argument,
and the laws and Minkowski content are continuous at every irrational slope.
The Gamma-normalized law, density and regularity package now covers the
whole family as well. Total mass is exact at every boundary, and as the
slope decreases to `a/b` the laws converge to the uniform law on `b` atoms.
Global theorem: for every real `alpha>1` the empirical law of the actual
ratios converges; the rational phase theorem `R_r-F^+(delta_r)->0` comes from
a weak counting identity transferred from nearby irrational boundaries. The
slope map `alpha -> mu_alpha` is right-continuous and continuous exactly at
irrational slopes. Hausdorff dimension for Diophantine class `nu` lies in
`[2/(2+nu), 2/(2+sqrt nu)]` (Lean), above the Denjoy-set value `2/(3 nu)`;
`dim_H K_alpha=2/3` exactly when the irrationality exponent is `2`, so at
`log_2 3` the dimension question is equivalent to an open number-theory one.
For regular slopes (`q_(n+1)` of order `q_n^nu` at every level) the dimension
is exactly `2/(2+nu)`; explicit slopes of every class exist, so the
dimensions over all irrational slopes fill exactly `[0,2/3]` (Lean).
**PROMOTE**. See Sections 27–31 of the
[Beatty note](theory/juggler_beatty_first_passage_note.md).

## 2026-09-24 -- Both depth-five productions written; contagion 0.74 conditional

Depth-five branch, Results 7-24. The route rests on the following:

- **EXACT — HUMAN PROOF (AI-written, AI-audited, not human-reviewed):**
  - *Both productions at `1/28`.* Both the `OOOEE` and the `OOEOE` production
    hold at coefficient `1/28`.
  - *Small shifts suffice.* Lemma E9's sub-block averaging shows that the poor
    tails need only differenced sums at shifts below `P^(1/48)`. Those are
    Paper B's printed Appendix C.9 and C.2, plus two new mechanisms: E5's
    `j = 0` diagonal (`243/4096`) and E7's smooth-coefficient `U`-carry for
    `OOEOE` (`-1701/4096`).
  - *Widened lemmas no longer needed.* The widened Lemmas E1-E4 are off the
    critical path.
- **EXACT — LEAN VERIFIED (conditional):** `FateDepthFiveAssembly` turns both
  productions into contagion `(log X)^(37/50)` and thresholds `13/50`. The
  Arb-certified root is `0.74057`.

**PARK:** the promotion criterion `lambda > 0.74` is met in writing; promotion
awaits human review. Depth seven, with root about `0.787`, would need
six-coordinate nested floors. Record:
[depth-five dossier](problems/juggler_depth_five_production.md).

## 2026-09-24 -- Beatty cluster set has positive Hausdorff dimension at log_2 3

Review of the Beatty note. **EXACT — HUMAN PROOF:** Rhin's effective
measure `|u_0+u_1 log 2+u_2 log 3|>=H^(-13.3)` supplies the Diophantine
premise of the Lean-checked implication with `tau=13.3`, so the original
certificate cluster set has `H^(2/39.9)(K)>0`. Wu-Wang's noneffective
exponent `4.1163051+epsilon` raises the bound to
`dim_H K>=2/(3*4.1163051)=0.16195...`. Minkowski dimension stays `2/3`;
exact Hausdorff dimension and critical-measure positivity remain open.
A new interface theorem states the family Minkowski results directly for
the set of subsequential limits of the original ratios. **PROMOTE** within
the dossier; row `J-beatty-rhin-hausdorff-lower-bound`, Section 20 of the
[Beatty note](theory/juggler_beatty_first_passage_note.md).

## 2026-09-24 -- Counting escapes reduces to the all-depth program

Clotho Phase-0. **EXACT — LEAN VERIFIED:** an escape rate above `3/8`
excludes divergent orbits and makes every orbit eventually periodic
(`J-escape-rate-excludes-divergence`), by the generic Tao reduction and the
OOEE contagion. The hope that escapes are easier to count than failures does
not survive: escape can be arbitrarily slow, so at bounded depth an escaping
start is a live start, and Ville's maximal inequality for the fair multiplier
martingale (checked exactly on words to depth 60) needs fair parity at every
depth. **CLOSE** as a reparameterization. See the
[escape-rate dossier](problems/juggler_escape_rate.md).

## 2026-09-24 -- Depth-five productions priced and parked

Atropos Phase-0. The first-descent words through length four are exactly
`E`, `OE`, `OOEE`, so the kernel-checked `5/8` contagion sits at the
depth-four ideal `0.6328`. Depth five adds `OOOEE` and `OOEOE` and would lift
the ideal to `0.7512`, lowering the required failure rate from `3/8` toward
`1/4` (COMPUTATIONALLY VERIFIED, exact multipliers). Their fibres are windows
of length `P^(5/32)` rather than `P^(7/16)`: the depth-four mixed-mode bound
`O(P^(13/32))` is weaker than trivial there, and an averaged poor tail needs
differenced depth-five mixed sums with shifts up to `P^(5/32)`, beyond Paper
B's `P^(1/8)` frozen gaps. **PARK.** See the
[depth-five dossier](problems/juggler_depth_five_production.md) and its
obstruction record.

## 2026-09-24 -- Written-proof rows converted to Lean, with a coverage audit

**EXACT — LEAN VERIFIED**, kernel trust: twelve rows leave the written-proof
category. They are Paper A E.7 (`OOEEscapeResidue`), the hug-flow image gap,
the cube-threshold hidden parity, the first-OOO square cell, the odd-preimage
Type 0/1/2 criterion, the OOE carry substitution (`D - d = 36r^2 + 1` exactly,
by coefficient positivity in `t = (r-3)/2`) and seven post-L envelope rows.
The new row `J-paper-b-barrier-mass-phase-count` proves mass preservation by
the non-rising update, the `fract(t beta)` form of the barrier rise and
`N_(d+1) = 2 N_d - b_d M_d`. A review of 39 further rows that name existing
Lean found none fully covered; 29 now link their partial support.
Corrections: several post-L statements turned an envelope failure into an
orbit claim (reworded, counterexample `n = 6`), and two reviewer errors,
on Rhin's measure and on `lambda**` against `100/203`, were caught at source.
Later the same day, the averaged contagion bound lowered the Section 9.2
corollaries: termination follows from the pressure or the no-momentum
hypothesis at any failure exponent above `3/8`, through the OOEE contagion
at `5/8` (`J-fate-pressure-three-eighths`, `J-fate-no-momentum-three-eighths`);
an intermediate `103/203` form is superseded. Both hypotheses stay open.
**PROMOTE** the conversions. Remaining premise: rows that mix measurements
with theorems stay written proofs pending a split. See the claim ledger and
the dossiers for [hug flow](problems/juggler_hug_flow_depth_two.md),
[first OOO](problems/juggler_first_ooo_escape.md),
[empty odd preimage](problems/juggler_empty_odd_preimage.md),
[cubic induction](problems/juggler_cycle_cubic_induction.md) and
[OOE escape](problems/juggler_ooe_escape_families.md).
