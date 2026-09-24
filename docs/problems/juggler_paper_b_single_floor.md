# Paper B: Theorem 3.1 exact single-floor bridge

## Problem

Separate the exact counting identity in Paper B Theorem 3.1 from the exponential-sum bound that feeds it.

## Exact statement

For the odd starts in `{1, …, N}`, the single-floor sign sum `S_O` equals `M - 2 · #{word_2 = OO}`. The two-step certificate count is the complement of that class. A bound `|S_O| ≤ E` moves to both printed counts with error `E`. The phase `g(r) = (1/2)(2r+1)^{3/2}` has second derivative `(3/2)(2r+1)^{-1/2}`, and the cutoff `H = Q^{1/6}` makes the classical block majorant at most `3 Q^{5/6}`.

## Current literature

`known`: Theorem 3.1 of [juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md). The exponential-sum estimate is the classical second-derivative test plus Erdős–Turán. No literature-wide priority claim.

## Branch budget

- **Target:** the exact bridge `S_O = M - 2 · #OO`, and the cutoff arithmetic.
- **Novelty hypothesis:** first Lean coverage of Theorem 3.1's counting step.
- **Falsifier:** an odd start whose image parity disagrees with `word_2 = OO`, or a cutoff `H = Q^{1/6}` whose block majorant exceeds `3 Q^{5/6}`.
- **Already killed by?:** none — this is an identity inside a proved theorem; the three tests do not apply.
- **Existing machinery:** `floorPower`, `itinerary`, `pow32`, `Real.floor_real_sqrt_eq_nat_sqrt`.
- **Maximum Phase-0 scope:** one Lean module and a ledger row for the identity. No exponential-sum estimate.
- **Promotion criterion:** `lake env lean` on the module, umbrella import, registry entry.
- **Stop criterion:** any attempt to prove `|S_O| = O(N^{5/6})` inside this module.

## Balanced-ternary formulation

Not used. The objects are parities of `⌊n^{3/2}⌋`.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

`imageSign`, the odd-start sum `singleFloorSum`, and the second derivative of `phaseG`.

## Experiments

None. The statements are identities.

## Conjectures

None.

## Counterexamples

None.

## Formalization

`formal/Problems/Juggler/PaperBSingleFloor.lean`. Theorems `singleFloor_bridge`, `c2_bridge`, `oo_count_of_sum`, `hasDerivAt_phaseG'`, `dyadic_cutoff`, `block_exponential_sum`, `sum_inv_sqrt`. No `sorry`.

`formal/BTCalculus/ErdosTuran.lean` (2026-09-25). This is the Erdős–Turán inequality with main term `N/H`: `abs_arcError_le_modeSum` and its mode-bound form `abs_arcError_le_of_modes`. For `H ≥ 3` and every arc of length at most one, it gives `|count - N·length| ≤ 8N/(H+1) + 4 ∑_{h≤H} B_h/h` when `|∑ e(±h z_n)| ≤ B_h`. The proof uses the existing Fejér kernel at radius `δ = 2/(H+1)`, where the tail mass is `1/4`. It compares the translates of the expanded and contracted arcs with the extreme discrepancy rather than with `N`, so the smoothing loss is `τ · D` and not `τ · N`. The self-referential bound then closes: `D/2 ≤ T + 4N/(H+1)`. No Selberg polynomial is needed.

`formal/Problems/Juggler/PaperBSingleFloorBound.lean` (2026-09-25). This module proves the printed theorem, which the stop criterion above kept out of the bridge module:
`imageSign_eq_arc` puts parity in the arc `[0, 1/2)`; `abs_block_sign_sum_le` gives `528 a^{5/6}` on a block `[a, a+M)` with `M ≤ a` at `H = ⌊a^{1/6}⌋`; `abs_odd_sign_sum_le` recurses at `⌈R/2⌉`; and `abs_singleFloorSum_le`, `abs_ooCount_sub_le` and `abs_c2Count_sub_le` are the three assertions. They depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Results

`J-paper-b-theorem-3-1-bridge` — `EXACT — LEAN VERIFIED` for the bridge, the cutoff arithmetic, and one dyadic exponential sum.

`J-paper-b-theorem-3-1` — `EXACT — LEAN VERIFIED`: `|S_O(N)| ≤ 2112 N^{5/6}` for every `N`. For `N ≥ 1`, `|#OO - N/4| ≤ 1057 N^{5/6}` and `|#(C_2 ∩ [1,N]) - 3N/4| ≤ 1057 N^{5/6}`. This is Theorem 3.1 as printed, with explicit constants. The bound on `S_O` beats the trivial `|S_O| ≤ (N+1)/2` only once `N > 4224^6 ≈ 5.7·10^21`; it is an asymptotic statement, not a finite-range improvement.

## Open questions

Closed on 2026-09-25: `BTCalculus.ErdosTuran` supplies the one-dimensional inequality with main term `N/H` and weights `1/h`. The older `BTCalculus.FejerWeighted` bound, with main term `N/√H`, stays as it was. The new inequality also fits Proposition 3.2, whose two-dimensional form (Erdős–Turán–Koksma) is not formalized.

## Decision

`PROMOTE` — the exact bridge, one dyadic block, and `∑ h^{-1/2} ≤ 2√H` are kernel-checked. On 2026-09-25 the printed `O(N^{5/6})` and both counts were kernel-checked too, through the new `N/H` Erdős–Turán inequality. Best next question: does the extreme-discrepancy argument lift to the two-dimensional box in `BTCalculus.FejerBox`? Proposition 3.2 needs that lift.

## Publication assessment

Status: `THEOREM`. Supports Paper B. With `J-paper-b-theorem-3-1`, Theorem 3.1 is Lean-verified in full.
