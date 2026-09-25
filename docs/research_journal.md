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

## 2026-09-25 -- Beatty dimension as a growth-sequence game; two-scale slopes in Lean

**OBSERVATION (exponent model):** reduced to exponent recursions, the cover of
Theorem 6.18a and the grid-window measure of Theorem 6.71 give the same Hausdorff
dimension on every periodic growth pattern tested (34 patterns, gaps below `1e-15`
away from marginal thresholds). A jump `nu` followed by a dense stretch `rho` has an
explicit two-scale formula interpolating `2/(2+nu)` and `s*(nu)`, with windows helping
exactly when `rho > 1 + 3/nu`. Phase 1, same day, **EXACT — LEAN VERIFIED**: for
`rho > 1 + 3/nu` the two-scale slopes have `dim_H K_alpha = S(nu, rho)`, the root of
`3(R-1)s^2 + 4(rho-1)s - 4(rho-1) = 0`, and exist in every class `nu > 1`
(`twoScale_dims`). Remaining premise: none for this family; patterns with several
jumps per period stay numerical. Decision: PROMOTE. Record: claim
`J-beatty-slope-two-scale`, note section 33, [phase-collapse dossier](problems/juggler_winkler_phase_collapse.md).

## 2026-09-25 -- Isolated slopes attain s*(nu) in Lean

**EXACT — LEAN VERIFIED:** an isolated-level slope whose good levels admit an
enumeration with `(2Q_(g_l+1))^((l+2)^2) <= Q_(g_(l+1))` has
`dim_H K_alpha = s*(nu)`; for every `nu > 1` an explicit tower gives such a
slope of class exactly `nu`. So the cluster-set dimension is not a function of
the Diophantine class. A grid-window Cantor tree, a descent lemma and three
atom-mass bounds give the Frostman bound. Remaining premise: none; the weaker
`o(1)` sparsity stays written. Decision: PROMOTE. Record: claim
`J-beatty-slope-isolated-exact`, note section 32.

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

## 2026-09-24 -- Beatty first-passage geometry for every slope; dimension 2/3 almost everywhere

**EXACT — LEAN VERIFIED** for every irrational slope `alpha>1`: the actual
integer ratios approach an explicit jump profile; the cluster set `K_alpha` is
null and perfect, with Minkowski dimension `2/3`, exact positive content and an
explicit local content measure; the empirical law is singular continuous, and
the Gamma-normalized law is absolutely continuous with an explicit density,
moments, interval support and dense null blowup. For every real `alpha>1` the
empirical law converges, and the slope map is continuous exactly at irrationals.
Hausdorff dimension depends on the arithmetic of the slope: `2/3` exactly when
the irrationality exponent is `2` (so for almost every slope), `0` at Liouville
slopes, in `[2/(2+nu), 2/(2+sqrt nu)]` for class `nu`, exactly `2/(2+nu)` at
regular slopes, and filling `[0,2/3]` over all slopes. At `log_2 3` the question
is an open number-theory one; **EXACT — HUMAN PROOF** from Rhin and Wu-Wang,
`dim_H K>=0.16195...`, and `h in L^p` for `1<=p<62/41`. **PROMOTE**; this entry
replaces four 24 September Beatty entries. Record: Sections 13–31 of the
[Beatty note](theory/juggler_beatty_first_passage_note.md) and the
[phase-collapse dossier](problems/juggler_winkler_phase_collapse.md).

## 2026-09-24 -- Both depth-five productions written; contagion 0.74 conditional

Depth-five branch, Results 7-24. Depth five adds `OOOEE` and `OOEOE` to the
first-descent words `E`, `OE`, `OOEE`, whose fibres are windows of length
`P^(5/32)`; an earlier PARK priced them beyond Paper B's frozen gaps. The
route rests on the following:

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
