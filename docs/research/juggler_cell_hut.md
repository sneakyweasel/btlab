# Juggler cell-hut quotient

Status: **HUT_COMPLEX**

Standalone Phase-0 test of whether Juggler's wide-even / singleton-odd
predecessor cells define a local class whose forward transitions are
simpler than the exact integer map. Not a Research Engine experiment,
not a Collatz hut, not an automaton, and not a halt theorem.

## Branch budget

```text
Mathematical target     Does a compact signature of Pred_E / Pred_O
                        simplify T, or only rename it?
Novelty hypothesis      wide-even / singleton-odd is a natural hut class
Falsifier               bijection with m, unbounded out-degree, or
                        same-class incompatible successors
Existing machinery      even_preimage, pred_odd, floor_power, Preimages.lean
Maximum Phase-0 scope   m<=4000; selected 1e5; no GPU; no Lean pilot
```

## A. Exact geometry, not a class

Juggler `T` is the unaccelerated floor-power map. The raw hut is
`H(m) = (Pred_E(m), Pred_O(m))` from the existing cells
(`LEAN-CERTIFIED`). Endpoints of `Pred_E` recover `m`, so `H(m)`
as a class is a renaming of `T` and is rejected.

The Collatz formula `n = (2^k m - 1)/3` was not used.

- targets `m = 1..4000`: `4000`
- occupied odd cells: `126`
- order types: `{'fixed_1': 1, 'no_odd': 3874, 'o_lt_m_lt_E': 125}`
- Atlas-boundary labels (fixtures only): `['EEEEEE', 'EEEEOE', 'EEEOEO']`

For `m>1` with an odd predecessor the order is `o(m) < m < E(m)`.
The varying odd position is the cube remainder tertile, not a point
inside the even interval.

## B. Frozen signature ladder

Identifying coordinates (`m`, even endpoints, `o(m)`) are excluded
from every class key. Versions were frozen before the census.
Failed versions were not retuned.

| version | classes | compression | max_out | mean_out | density | functional | merge_xy | cycle | rule |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| v1_occupancy | 2 | 2000.00 | 2 | 2.00 | 1.00 | 0 | 2/4 | yes | none |
| v2_type | 4 | 1000.00 | 4 | 3.00 | 0.75 | 0 | 2/4 | yes | none |
| v3_oddpos | 8 | 500.00 | 6 | 4.75 | 0.59 | 0 | 2/4 | yes | none |
| v4_mod3 | 24 | 166.67 | 18 | 7.58 | 0.32 | 0 | 2/8 | yes | none |
| vB_border | 8 | 500.00 | 6 | 2.88 | 0.36 | 2 | 4/10 | yes | none |
| vC_valuation | 32 | 125.00 | 15 | 6.19 | 0.19 | 7 | 2/4 | yes | none |

`v4_mod3` is a falsification rung. A modulus-only success is
rejected. `vC_valuation` is the 2-adic comparison only.

## C. Transition families

Each state has one successor. A hut class has out-degree equal to
the number of distinct successor classes of its members. A finite
label set bounds that number automatically; the bound is vacuous
unless the family is small *and* parameterized.

- `v1_occupancy` first merge: `2` and `4` share `v1_occupancy:0` but go to `v1_occupancy:1` vs `v1_occupancy:0`
- `v1_occupancy` smallest class cycle: `['v1_occupancy:1', 'v1_occupancy:1']`
- `v1_occupancy` self-return: m=`1` -> J(m)=`1` stays `v1_occupancy:1`
- `v2_type` first merge: `2` and `4` share `v2_type:0,0` but go to `v2_type:1,1` vs `v2_type:0,0`
- `v2_type` smallest class cycle: `['v2_type:1,1', 'v2_type:1,1']`
- `v2_type` self-return: m=`1` -> J(m)=`1` stays `v2_type:1,1`
- `v3_oddpos` first merge: `2` and `4` share `v3_oddpos:0,0,0` but go to `v3_oddpos:1,1,1` vs `v3_oddpos:0,0,0`
- `v3_oddpos` smallest class cycle: `['v3_oddpos:1,1,1', 'v3_oddpos:1,1,1']`
- `v3_oddpos` self-return: m=`1` -> J(m)=`1` stays `v3_oddpos:1,1,1`
- `v4_mod3` first merge: `2` and `8` share `v4_mod3:0,0,0,2` but go to `v4_mod3:1,1,1,1` vs `v4_mod3:0,0,0,2`
- `v4_mod3` smallest class cycle: `['v4_mod3:1,1,1,1', 'v4_mod3:1,1,1,1']`
- `v4_mod3` self-return: m=`1` -> J(m)=`1` stays `v4_mod3:1,1,1,1`
- `vB_border` first merge: `4` and `10` share `vB_border:0,0,1,1,0` but go to `vB_border:0,0,0,1,0` vs `vB_border:1,0,-1,-1,0`
- `vB_border` smallest class cycle: `['vB_border:1,1,0,0,0', 'vB_border:1,1,0,0,0']`
- `vB_border` self-return: m=`1` -> J(m)=`1` stays `vB_border:1,1,0,0,0`
- `vC_valuation` first merge: `2` and `4` share `vC_valuation:0,0,0,0` but go to `vC_valuation:-1,1,1,1` vs `vC_valuation:0,0,0,0`
- `vC_valuation` smallest class cycle: `['vC_valuation:-1,1,1,1', 'vC_valuation:-1,1,1,1']`
- `vC_valuation` self-return: m=`1` -> J(m)=`1` stays `vC_valuation:-1,1,1,1`

## D. Odd spines

The unique odd predecessor, when it exists, is iterated until the
odd cell is empty. This is the existing `odd_preimage_unique` spine,
not a new inverse law.

- root `1` depth `1` stop `fixed_point` nodes `[1, 1]`
- root `5` depth `1` stop `empty_odd_cell` nodes `[5, 3]`
- root `9` depth `0` stop `empty_odd_cell` nodes `[9]`
- root `37` depth `0` stop `empty_odd_cell` nodes `[37]`
- root `365` depth `0` stop `empty_odd_cell` nodes `[365]`
- root `1999` depth `0` stop `empty_odd_cell` nodes `[1999]`

## E. Even fans

| version | max_distinct | mean_distinct | max_ratio | grows_like_fan |
| --- | --- | --- | --- | --- |
| v1_occupancy | 2 | 1.95 | 1.000 | False |
| v2_type | 2 | 1.95 | 1.000 | False |
| v3_oddpos | 4 | 3.31 | 1.000 | False |
| v4_mod3 | 12 | 6.38 | 1.000 | False |
| vB_border | 2 | 1.95 | 1.000 | False |
| vC_valuation | 2 | 1.95 | 1.000 | False |

Members of `E(m)` are even, so a fan only occupies the even slice
of a finite label set. For `vC_valuation` the neighbors of an even
`n` are odd, so both 2-adic valuations are 0. Apparent fan
compression is that slice, not `EVEN_FAN_GREEN`.

## F. Selected walks

Exact integer trajectories are retained. Class sequences never
replace them. Fixture walks only; no full census.

- n=`1` steps=`0` distinct v3 classes=`1`
- n=`3` steps=`6` distinct v3 classes=`4`
- n=`5` steps=`5` distinct v3 classes=`3`
- n=`365` steps=`21` distinct v3 classes=`7`
- n=`425` steps=`67` distinct v3 classes=`8`
- n=`2183` steps=`72` distinct v3 classes=`8`
- n=`3889` steps=`80` distinct v3 classes=`8`

## G. Extension m<=10^5

| version | classes | max_out | mean_out | vacuous |
| --- | --- | --- | --- | --- |
| v1_occupancy | 2 | 2 | 2.00 | True |
| v2_type | 4 | 4 | 3.00 | True |
| v3_oddpos | 8 | 8 | 5.62 | True |
| v4_mod3 | 24 | 18 | 14.00 | False |
| vB_border | 8 | 7 | 3.12 | True |
| vC_valuation | 49 | 28 | 9.88 | False |

## H. Balanced ternary

- same signature as `D(m)`: `1230` / `3999`
- same signature as some `I_a(D(m))`: `6503` / `11997`
- length-4 jet buckets: `81` splitting: `81`
- suffix determines hut: `False`
- first suffix split: `{'jet': [1, 0, 0, 0], 'x': 1, 'y': 82, 'version': 'v3_oddpos'}`

A fixed BT suffix determining the hut would reopen the rejected
finite-information projection. `D` / `I_a` are not a hut calculus.

## I. Well-founded rank

No structured transition rule survived, so no rank was invented.
Class cycles and self-returns are recorded as counterexamples to
any later claim of strict descent on these signatures.

## J. Visualizations

A. Cell-hut diagrams for `m=1,2,5,365`.
C. Odd-spine examples for the spine roots.
B/D/E. Withheld: no nontrivial structured class graph, no genuine
even-fan collapse, and no well-founded parameter.

## K. Final classification

**HUT_COMPLEX**

Every frozen cell-hut signature is a finite label set, so out-degree is automatically bounded by the number of labels. Same-class states still take incompatible successors; class graphs are dense or cyclic; even fans only occupy the even slice of those labels; the odd spine is the existing unique-odd descent; BT jets and D/I do not supply a hut calculus. The quotient coarsens T without simplifying the transition algebra. v1_occupancy: classes=2 max_out=2 density=1.000 merge=True rule=None; v2_type: classes=4 max_out=4 density=0.750 merge=True rule=None; v3_oddpos: classes=8 max_out=6 density=0.594 merge=True rule=None; v4_mod3: classes=24 max_out=18 density=0.316 merge=True rule=None; vB_border: classes=8 max_out=6 density=0.359 merge=True rule=None; vC_valuation: classes=32 max_out=15 density=0.193 merge=True rule=None; even-fan distinct counts stay small because every n in E(m) is even, so the fan only sees the even slice of a finite label set; neighbors of an even n are odd, so v2(n-1)=v2(n+1)=0. That is not EVEN_FAN_GREEN; odd spines terminate at an empty odd cell or the fixed point 1; length-4 BT jets split hut classes; no BT hut representation; v3_oddpos out-degree grew from 6 to 8 on m<=1e5; vB_border out-degree grew from 6 to 7 on m<=1e5; vC_valuation out-degree grew from 15 to 28 on m<=1e5

This is not a halt result. Hut descent is not termination.

## Lean

- sorry-free: `True`
- no new Lean module: `True`
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
- hut_descent_is_termination: `False`
- reopen_pe_factors: `False`
- reopen_word_atlas: `False`
- reopen_residual_quotient: `False`
- reopen_sum_rho: `False`
- reopen_realization_geometry: `False`
- reopen_landing_image: `False`
- reopen_nc_boundary: `False`
- reopen_first_return: `False`
- reopen_information_complexity: `False`
- reopen_backward_geometry: `False`
- reopen_accelerated: `False`
- reopen_2adic_bridge: `False`
- reopen_prefix_nc: `False`
- reopen_preimage_cylinders: `False`
- reopen_adversarial_paths: `False`
- automaton: `False`
- collatz_inverse: `False`
- cell_tree_engine: `False`
- scalar_hut_score: `False`
- engine_control_layer_modified: `False`

## Decision

**CLOSE** — `HUT_COMPLEX`

Every frozen cell-hut signature is a finite label set, so out-degree is automatically bounded by the number of labels. Same-class states still take incompatible successors; class graphs are dense or cyclic; even fans only occupy the even slice of those labels; the odd spine is the existing unique-odd descent; BT jets and D/I do not supply a hut calculus. The quotient coarsens T without simplifying the transition algebra. v1_occupancy: classes=2 max_out=2 density=1.000 merge=True rule=None; v2_type: classes=4 max_out=4 density=0.750 merge=True rule=None; v3_oddpos: classes=8 max_out=6 density=0.594 merge=True rule=None; v4_mod3: classes=24 max_out=18 density=0.316 merge=True rule=None; vB_border: classes=8 max_out=6 density=0.359 merge=True rule=None; vC_valuation: classes=32 max_out=15 density=0.193 merge=True rule=None; even-fan distinct counts stay small because every n in E(m) is even, so the fan only sees the even slice of a finite label set; neighbors of an even n are odd, so v2(n-1)=v2(n+1)=0. That is not EVEN_FAN_GREEN; odd spines terminate at an empty odd cell or the fixed point 1; length-4 BT jets split hut classes; no BT hut representation; v3_oddpos out-degree grew from 6 to 8 on m<=1e5; vB_border out-degree grew from 6 to 7 on m<=1e5; vC_valuation out-degree grew from 15 to 28 on m<=1e5

