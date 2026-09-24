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

## Results

`J-paper-b-theorem-3-1-bridge` — `EXACT — LEAN VERIFIED` for the bridge, the cutoff arithmetic, and one dyadic exponential sum. The bound `S_O(N) = O(N^{5/6})` is not proved here.

## Open questions

The missing half is a one-dimensional discrepancy inequality with main term `N/H` and weights `1/h`. The repository Fejér discrepancy has main term `N/√H`, and with `H = Q^{1/6}` that error is `Q^{11/12}`, larger than `Q^{5/6}`. `sum_inv_sqrt` is the harmonic comparison the `N/H` argument uses.

## Decision

`PROMOTE` — the exact bridge, one dyadic block, and `∑ h^{-1/2} ≤ 2√H` are kernel-checked. The printed `O(N^{5/6})` remains open. Best next question: is there an Erdős–Turán inequality in this library whose main term is `N/H` rather than `N/√H`?

## Publication assessment

Status: `THEOREM`. Supports Paper B. It does not by itself Lean-verify Theorem 3.1.
