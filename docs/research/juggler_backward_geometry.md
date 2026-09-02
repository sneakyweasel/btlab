# Juggler backward predecessor geometry

Status: **BACKWARD_COMPLEX**

Standalone Phase-0 study of the inverse graph of the Juggler
floor-power map. Not a Research Engine experiment, not a Collatz
inverse, not a halt theorem, and not a reopening of closed
forward or one-step-cell branches.

## Branch budget

```text
Mathematical target     Does repeated mixed inversion impose a
                        constraint beyond the floor cells?
Novelty hypothesis      mixed-path scale, sparsity, rank, or hard-path rigidity
Falsifier               every candidate is a cell corollary or reverse itinerary
Existing machinery      even_preimage, odd_preimage_integers, floor_power, Preimages.lean
Maximum Phase-0 scope   Pred census m<=4000; bounded BFS; composition; hard reverse
```

## A. Exact predecessor rule

Juggler `T` is the unaccelerated floor-power map. Predecessors are
the existing floor cells (`LEAN-CERTIFIED`):

- `Pred_E(m) = { n even : m^2 <= n < (m+1)^2 }`
- `Pred_O(m) = { n odd : m^2 <= n^3 < (m+1)^2 }`, at most one
- every emitted edge satisfies `T(n) = m` (`EXACT COMPUTATION`)

The Collatz formula `n = (2^k m - 1)/3` is a different map and was
not used. Inverse edges are labelled by the letter `E`/`O` and, for
even edges, the remainder `ρ = n - m^2`.

- `Pred(1) = {1, 2}` with letters O (fixed point) and E
- `Pred(2) = {4, 6, 8}` even-only
- `Pred(5)` contains the odd predecessor `3`

## B. Branching statistics

- targets `m = 1..4000`: `4000`
- nonempty even cells: `4000` (`EXACT COMPUTATION`)
- nonempty odd cells: `126` rate `63/2000`
- `|Pred_E|` range: `1` … `4001`
- equal edges: `1` (the fixed point `1 -> 1`)

`|Pred_E(m)| = m+1` for even `m` and `m` for odd `m` — the number of
evens in an interval of length `2m+1`. This is `KNOWN` from the cell.

- Pred_O occupancy by m mod 2: `{'0': [59, 2000], '1': [67, 2000]}`
- Pred_O occupancy by m mod 3: `{'0': [44, 1333], '1': [40, 1334], '2': [42, 1333]}`

Mod-3 occupancy is not an admissibility rule. It only records how
often an odd cube sits in the image interval.

## C. Ascending versus descending inverse branches

Even predecessors satisfy `n >= m^2 >= m`, and for `m >= 1` the
smallest even cell member is strictly larger than `m`. Odd
predecessors satisfy `n ~ m^{2/3}` and descend for every `m > 1`.
The only equal edge in the window is `1 -> 1`.

- even descending counterexamples: `[]`
- odd ascending counterexamples: `[]`

Label: `LEAN-CERTIFIED` cell bounds, `EXACT COMPUTATION` on the window.

## D. Inverse affine composition

The inverse step is not affine. Even inverse is quadratic;
odd inverse is a cube-interval. The Collatz form `m_r = A_r m_0 - B_r`
does not apply. Composed bounds are the nested cells
`F_-(m,κ) <= n <= F_+(m,κ)`.

- hull wider than exact fiber: `[{'m': 3, 'word': 'EEO'}, {'m': 5, 'word': 'EEO'}, {'m': 7, 'word': 'EEO'}, {'m': 11, 'word': 'EO'}, {'m': 11, 'word': 'EOE'}]`
- EE/EOE holes from skipped odd intermediates: `8` words
- new scale law: `False`

When the exact fiber interval sits inside the parity nest, the nest is the interval hull of a parent range and therefore includes non-predecessors. The exact set is the cell law applied to the actual predecessor set. EE fibers also have holes from skipped odd intermediates. Neither is a new scale inequality.

Label: `REPARAMETERIZATION` of repeated `even_preimage` / `odd_cell`.

## E. Long backward paths

Every `m >= 1` has a nonempty even cell, so an inverse ray of
even letters always exists and leaves every finite bound
(`n_{i+1} >= n_i^2`). Nothing in the window prevents an arbitrarily
long inverse ray. Odd-only rays are unique and stop at the first
empty odd cell. Finite observed depth is not a global theorem.

Selected-root odd spines and min/max even rays:

- root `1` cap `1000000` visited `335807` odd-spine `0` min-even-ray `5` even-in-window `True`
- root `3` cap `1000000` visited `79288` odd-spine `0` min-even-ray `3` even-in-window `True`
- root `5` cap `1000000` visited `153513` odd-spine `1` min-even-ray `3` even-in-window `True`
- root `7` cap `1000000` visited `29200` odd-spine `0` min-even-ray `2` even-in-window `True`
- root `9` cap `1000000` visited `29774` odd-spine `0` min-even-ray `2` even-in-window `True`
- root `37` cap `1000000` visited `38` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `49` cap `1000000` visited `50` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `69` cap `1000000` visited `360` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `77` cap `1000000` visited `927` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `193` cap `10000000` visited `2444` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `243` cap `10000000` visited `84377` odd-spine `1` min-even-ray `1` even-in-window `True`
- root `365` cap `10000000` visited `8225` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `425` cap `10000000` visited `429` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `763` cap `10000000` visited `8991` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `1749` cap `10000000` visited `10745` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `1999` cap `10000000` visited `2004` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `2183` cap `10000000` visited `2189` odd-spine `0` min-even-ray `1` even-in-window `True`
- root `3431` cap `10000000` visited `1` odd-spine `0` min-even-ray `0` even-in-window `False`
- root `3889` cap `10000000` visited `1` odd-spine `0` min-even-ray `0` even-in-window `False`
- root `4447` cap `10000000` visited `1` odd-spine `0` min-even-ray `0` even-in-window `False`

## F. Branching / collision structure

`T` is a function, so the inverse graph from a fixed root is a
tree. Same-root collisions were not searched as a discovery;
the BFS recorded any repeat as a sanity check.

- same-root collisions: `0`

In-window even expansion exists only for `m <= sqrt(N)`. Large
roots show an odd spine plus a scale-limited even cloud starting
at `m^2`. That is geometry of the cap, not emptiness.

Branching `B_r(m)` is the in-window descendant count. It is not entropy.

| root | cap | visited | B_1 | B_2 | B_3 | p_1 | P_1 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 1000000 | 335807 | 1 | 3 | 21 | 2 | 2 |
| 3 | 1000000 | 79288 | 3 | 39 | 6429 | 10 | 14 |
| 5 | 1000000 | 153513 | 6 | 158 | 71459 | 3 | 34 |
| 7 | 1000000 | 29200 | 7 | 400 | 25 | 50 | 62 |
| 9 | 1000000 | 29774 | 9 | 821 | 53 | 82 | 98 |
| 37 | 1000000 | 38 | 37 | 0 | 0 | 1370 | 1442 |
| 49 | 1000000 | 50 | 49 | 0 | 0 | 2402 | 2498 |
| 69 | 1000000 | 360 | 69 | 1 | 287 | 4762 | 4898 |

## G. Exceptional roots

The tree rooted at `1` contains the equal odd edge `1 -> 1`, which
is not expanded, and the even child `2`. Other scanned roots have
no equal predecessor. If `T^r(m) = 1`, the inverse tree of `m` is
the subtree of the tree of `1` sitting at `m`. That is the basin
geometry of the only known positive odd fixed point, already
`LEAN-CERTIFIED` as `floorPower_one`. It is not a termination proof.

- fixed-point summary: `{'m': 1, 'pred_e': 1, 'pred_o': 1, 'pred': 2, 'min_even': 2, 'max_even': 2, 'odd': 1, 'descending': 0, 'equal': 1, 'ascending': 1, 'expected_e': 1, 'e_formula_ok': True, 'even_cloud_start': 1, 'mod2': 1, 'mod3': 1, 'bits': 1}`

## H. Hard-forward-path reverse images

Known walks only. No new forward census. The reverse of a forward
path is the unique inverse path to that start (`KNOWN`). The test
is whether the actual predecessor is distinguished in `Pred(y)`.

- n=`3` steps=`5` word=`OOOEE` kinds=`{'unique_odd': 3, 'min_even': 1, 'interior_even': 1}` ordinary=`True`
- n=`365` steps=`15` word=`OOEOOEOOEOOEOEE` kinds=`{'unique_odd': 9, 'interior_even': 6}` ordinary=`True`
- n=`425` steps=`46` word=`OOOOOOOEOOEEOOOEOEEOOEOOOOOEEEEOOOOOOOEEEOEOEE` kinds=`{'unique_odd': 29, 'interior_even': 17}` ordinary=`True`
- n=`2183` steps=`54` word=`OOEOOOOEOOOOOOOOEOOOEOOOOOOOEOOOEEEOOOEEEEEEOEEOEEOOEE` kinds=`{'unique_odd': 34, 'interior_even': 20}` ordinary=`True`
- n=`3889` steps=`77` word=`OOOOOEOEOOOEOOEOEOEOOOOOOEOOOEOEOOOEOOOOOEEOEOEEOEOEEOOOEEOEOOEEOOEEOOOOOEEEE` kinds=`{'unique_odd': 48, 'interior_even': 29}` ordinary=`True`

Label: `COMPUTATIONALLY OBSERVED`. Hard predecessors are the
unique odd cell member or an ordinary even-cell point (min, max,
or interior remainder). No `BACKWARD_FORWARD_BRIDGE` law.

## I. Candidate structural laws

- Q1_pred_e_formula holds `True` — |Pred_E(m)| = m+1 (m even) or m (m odd)
- Q2_pred_o_unique holds `True` — |Pred_O(m)| in {0,1}
- Q3_even_ascending holds `True` — every even predecessor satisfies n > m
- Q4_odd_descending holds `True` — odd predecessors descend except the fixed point 1
- Q5_composition_is_cell_nest holds `True` — exact fibers are nested cells on the real predecessor set; a wider interval hull is a relaxation, not a new bound
- Q6_hard_preds_ordinary holds `True` — hard-path predecessors are unique-odd or ordinary even-cell points
- Q7_no_mod3_quotient holds `True` — Pred_O occupancy by m mod 3 spreads only 2688/889111
- Q8_no_same_root_collision holds `True` — T is a function; inverse from a fixed root is a tree

Rejected as non-results: the one-step cell formula; k-parity from
`m mod 3` (Collatz, not Juggler); `T(n)=m` as a discovery;
branch counts by enumerating the cell; affine reparameterizations;
a new monotone scalar; a finite-state quotient.

## J. Counterexamples

- census law failures: `[]`
- “composed bounds are a new scale law”: the exact fiber is the cell law on the real set; a wider hull is a relaxation.
- “hard paths have unusual inverse labels”: kinds are unique-odd or ordinary even.
- “m mod 3 organises Pred_O”: occupancy is a thin image-of-odd-T rate in every class.
- “same-root inverse collisions”: none; `T` is a function.

## K. Final classification

**BACKWARD_COMPLEX**

Repeated inversion is the nested floor cells: even steps explode quadratically, odd steps descend along a unique spine until an empty cell, and hard-path reverse images are ordinary cell points. No extra inverse rigidity.

This is not a halt result. Finite backward depth is not a theorem.
An infinite even inverse ray is not a nontermination certificate.

## Lean

- sorry-free: `True`
- `even_preimage_iff`: `True`
- `odd_preimage_iff`: `True`
- `odd_preimage_unique`: `True`
- `floorPower_even_eq_iff_sq_interval`: `True`
- `floorPower_odd_eq_iff_cube_interval`: `True`
- `floorPower_one`: `True`
- no forbidden engines: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- tau_always_finite: `False`
- new_lyapunov_scalar: `False`
- reopen_pe_factors: `False`
- reopen_residual_quotient: `False`
- reopen_sum_rho: `False`
- reopen_realization_geometry: `False`
- reopen_landing_image: `False`
- reopen_nc_boundary: `False`
- reopen_first_return: `False`
- reopen_information_complexity: `False`
- reopen_prefix_nc: `False`
- reopen_preimage_cylinders: `False`
- reopen_adversarial_paths: `False`
- automaton: `False`
- collatz_inverse: `False`
- cell_tree_engine: `False`

## Decision

**CLOSE** — `BACKWARD_COMPLEX`

Repeated inversion is the nested floor cells: even steps explode quadratically, odd steps descend along a unique spine until an empty cell, and hard-path reverse images are ordinary cell points. No extra inverse rigidity.

