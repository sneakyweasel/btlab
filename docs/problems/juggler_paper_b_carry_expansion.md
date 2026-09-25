# Paper B: Lemma 4.3, the near-integer sum (4.3)

## Problem

Machine-check the second assertion of Paper B Lemma 4.3: the bound (4.3) on
`∑ E_R(n^{3/2})` over the odd `n` of an interval, where `E_R(t) = min(1, 1/(R‖t‖))`.

## Exact statement

Lemma 4.3 of [juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md):
for `I ⊆ [P, 3P]`, `∑_{n ∈ I odd} E_R(n^{3/2}) ≪ P log(2R)/R + P^{5/6}`.

## Current literature

`known`: a dyadic layer decomposition of `E_R` against the interval discrepancy of Theorem 3.1.
No priority claim.

## Branch budget

- **Target:** a Lean proof of (4.3) with explicit constants.
- **Novelty hypothesis:** none mathematically; the kernel-checked input of the carry expansion.
- **Falsifier:** the discrepancy of Theorem 3.1 does not transfer from the arc `[0, 1/2)` to
  every arc, or the near-integer set of `n^{3/2}` is not a bounded union of arcs of `n^{3/2}/2`.
- **Already killed by?:** none. This is a classical corollary of a single-monomial estimate,
  with no new termination, cycle or local mechanism.
- **Existing machinery:** `PaperBSingleFloorBound`, `BTCalculus.ErdosTuran`.
- **Maximum Phase-0 scope:** the bound (4.3) only; not the pointwise expansion
  `b = b_R + O(E_R)` of the first assertion.
- **Promotion criterion:** compiles with no `sorry` and Mathlib's three axioms.
- **Stop criterion:** the first assertion, which needs pointwise bounds on sawtooth partial sums.

## Balanced-ternary formulation

Not used.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

`nearestIntDist`, `carryWeight`, `intervalCount` in the module below.

## Experiments

None. The statements are inequalities proved in Lean.

## Conjectures

None.

## Counterexamples

None.

## Formalization

`formal/Problems/Juggler/PaperBCarryExpansion.lean` (2026-09-25). The proof of Theorem 3.1
holds for every arc: `abs_block_arcError_le` (`264 a^{5/6}` on a block `[a, a+M)`, `M ≤ a`)
and `abs_prefix_arcError_le` (`1056 R^{5/6}` on `[0, R)`), hence `2112 r₁^{5/6}` on an
interval `[r₀, r₁)` (`abs_intervalCount_sub_le`). Since `n^{3/2} = 2 g(r)`, a point with
`‖n^{3/2}‖ < z ≤ 1` has `g(r)` in three arcs of total length `2z` (`near_mem_arcs`), so
`nearCount_le` gives `2z (r₁ - r₀) + 6336 r₁^{5/6}`. The layer-cake bound
`E_R(t) ≤ ∑_{j ≤ J} 2^{1-j} [‖t‖ < 2^j/R]` for `2^J ≥ R` (`carryWeight_le_layers`) then gives
`sum_carryWeight_le`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Results

`J-paper-b-lemma-4-3-sum` — `EXACT — LEAN VERIFIED`: for `R ≥ 1` and `r₀ ≤ r₁`, over the odd
starts `n = 2r+1`, `r ∈ [r₀, r₁)`,
`∑ E_R(n^{3/2}) ≤ 4 (r₁ - r₀)(⌊log₂ R⌋ + 2)/R + 25344 r₁^{5/6}`. For `I ⊆ [P, 3P]` this is
(4.3) with explicit constants. The bound holds for every interval, not only inside `[P, 3P]`.

## Open questions

The first assertion of Lemma 4.3, `b(t) = b_R(t) + O(E_R(t))` including at integers, is not
formalized. It needs a pointwise bound on the tail of the sawtooth Fourier series.

## Decision

`PROMOTE` — the bound (4.3) is kernel-checked.

## Publication assessment

Status: `THEOREM`. It Lean-verifies the second assertion of Lemma 4.3 only.
