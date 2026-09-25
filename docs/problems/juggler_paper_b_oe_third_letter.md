# Paper B: Proposition 3.2, the OE third letter

## Problem

Machine-check Paper B Proposition 3.2: for `w ∈ {OEE, OEO}`,
`#{n ≤ N : word_3(n) = w} = N/8 + O(N^{5/6} log(2N))`.

## Exact statement

Proposition 3.2 of [juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md).
An odd start `n` has word `OE·` exactly when `⌊n^{3/2}⌋` is even. Its third letter is
the parity of `⌊⌊n^{3/2}⌋^{1/2}⌋ = ⌊n^{3/4}⌋`. The count is therefore a box count for
the torus points `({n^{3/2}/2}, {n^{3/4}/2})` over odd `n`, in boxes of area `1/4`.

## Current literature

`known`: the two-dimensional Erdős–Turán–Koksma inequality and the second-derivative
test (Graham and Kolesnik 1991, as cited in the manuscript). No priority claim.

## Branch budget

- **Target:** a Lean proof of Proposition 3.2 with explicit constants.
- **Novelty hypothesis:** none mathematically; the first kernel-checked two-dimensional
  discrepancy estimate in Paper B.
- **Falsifier:** the extreme-discrepancy argument of `BTCalculus.ErdosTuran` fails to close in
  two dimensions, or the mixed curvature `(3i/8) n^{-1/2} - (3l/32) n^{-5/4}` changes sign
  on a block for some mode with `i ≠ 0` and `|l| ≤ H`.
- **Already killed by?:** none. This is a classical estimate for two monomials in one start,
  not a new termination, cycle or local mechanism. The obstruction search for this question
  returns only the unrelated `K_3` record.
- **Existing machinery:** `BTCalculus.ErdosTuran`, `FejerBox`, `SecondDerivative`,
  `PaperBSingleFloor`, `PaperBSingleFloorBound`.
- **Maximum Phase-0 scope:** the two-dimensional inequality, the mixed block bound, and the
  count. No decorated or nested-floor sums.
- **Promotion criterion:** each step compiles with no `sorry` and Mathlib's three axioms.
- **Stop criterion:** a curvature bound that needs machinery beyond the second-derivative test.

## Balanced-ternary formulation

Not used.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

`boxError`, `extremeBoxError` and `boxModeSum` in `BTCalculus.ErdosTuranBox`.

## Experiments

None. The statements are inequalities proved in Lean.

## Conjectures

None.

## Counterexamples

None.

## Formalization

`formal/BTCalculus/ErdosTuranBox.lean` (2026-09-25). This is the Erdős–Turán–Koksma
inequality with main term `N/H`: `abs_boxError_le_modeSum` and its extreme form
`extremeBoxError_le_modeSum`. For `H ≥ 7` and every box with sides of length at most one,
`|count - N·area| ≤ 32N/(H+1) + 2 ∑_{(k,l) ≠ 0} w(k) w(l) |S_{k,l}|`, where
`w(k) = 1/max(1,|k|)` and `|k|, |l| ≤ H`. The product Fejér kernel at radius `4/(H+1)` has
mass at most `1/8` off each coordinate strip. The translated expanded and contracted boxes
are compared with the extreme box discrepancy, as in the one-dimensional proof, and the
bound closes with a factor two. The double kernel integral is two nested one-dimensional
integrals, so no product measure is used. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Results

`J-erdos-turan-koksma-box` — `EXACT — LEAN VERIFIED`: the two-dimensional inequality above.

Proposition 3.2 itself is not yet proved in Lean. It still needs the identity
`⌊√⌊x⌋⌋ = ⌊√x⌋`, the mixed-mode second-derivative bound on a dyadic block, and the dyadic
recursion.

## Open questions

Does the mixed curvature stay within a factor two of its `i`-term on every block
`[P, 2P]` with `P` above an explicit threshold, for all `0 < |i| ≤ H` and `|l| ≤ H` at
`H = ⌊P^{1/6}⌋`? The manuscript's ratio bound `|l/i| P^{-3/4} ≤ P^{-7/12}` suggests yes.

## Decision

`PROMOTE` — the two-dimensional inequality is kernel-checked. The count remains open.

## Publication assessment

Status: `THEOREM` for the inequality. It supports Paper B Proposition 3.2 but does not
by itself Lean-verify it.
