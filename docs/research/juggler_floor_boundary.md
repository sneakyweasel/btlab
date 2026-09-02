# Juggler Archimedean floor-boundary geometry

Status: **FLOOR_BOUNDARY_COMPLEX**

Standalone Diophantine phase on the exact floor cells. Not a
Research Engine experiment, not a scalar hunt, and not a
termination theorem. Closed symbolic-compression branches stay closed.

## A. Exact floor geometry

For even `n` with `m = floor(sqrt(n))`:

`e_E(n) = n - m^2`, `u_E(n) = (m+1)^2 - n`, and `e_E + u_E = 2m+1`.

For odd `n` with `m = floor(n^(3/2))`:

`e_O(n) = n^3 - m^2`, `u_O(n) = (m+1)^2 - n^3`, and `e_O + u_O = 2m+1`.

`e` is the existing `local_defect`. The identity `e < 2m+1` is
`localDefectEven_lt_succ` / `localDefectOdd_lt_succ`. The pair
`(e,u)` is the complementary rewriting of that cell width.
Label: **LEAN-CERTIFIED** as those lemmas; the pair itself is a
**REPARAMETERIZATION** of `local_defect` plus cell width.

Even cells: every even `n` in `[m^2,(m+1)^2)` has the same image `m`.
On `n<= 4000` there are `63` occupied
even cells and `62` of them contain more than
one integer. Even-cell position is inert for the next step.
Label: **LEAN-CERTIFIED** (`even_preimage_iff`).

Odd cells contain at most one integer. So for odd `n`, `(e,u)` is not
a free coordinate inside a cell; it is a function of that unique `n`.
Label: **LEAN-CERTIFIED** (`odd_preimage_unique`).

## B. Boundary-distance distributions

Unique states `n=1..4000`, one row per integer, not trajectory-weighted.

| population | N | mean theta | median | p10 | p90 | frac<0.1 | frac>0.9 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| even n | 2000 | 0.489 | 0.49 | 0.091 | 0.892 | 0.112 | 0.09 |
| odd n | 2000 | 0.449 | 0.438 | 0.057 | 0.879 | 0.153 | 0.08 |
| next after e_O<=2 | 33 | 0.453 | 0.44 | 0.0 | 0.849 | 0.152 | 0.091 |

Exact hits: even `31`, odd `32`.
Near hits `e<=2` or `u<=2`: even `155`, odd `33`.
Hard-start means sit in the same mid-cell band (section G).
Label: **COMPUTATIONALLY OBSERVED**.

## C. Near-boundary states

Even `e=0` is an even perfect square. Odd `e=0` is an odd perfect
square. Those are `localDefect*_eq_zero_iff`.
Label: **LEAN-CERTIFIED**.

Proximity on an even step does not restrict the next letters beyond
the already-known image `m`. Proximity on an odd step with `e<=2`
has next-step theta mean
`0.453`, a generic mid-cell value.
Label: **EXACT COMPUTATION** on `n<=4000`.

## D. Diophantine small-defect solutions

Odd `n<= 100000` with `e_O<=16`:

| e_O | count | n |
| --- | --- | --- |
| 0 | 158 | [1, 9, 25, 49, 81, 121, 169, 225] |
| 2 | 1 | [3] |
| 4 | 1 | [5] |
| 11 | 1 | [15] |
| 13 | 1 | [17] |

No odd `n` in the window has `e_O = 1`. Every `e_O=0` row is an odd
square. The only `e_O=2` row is `n=3`. The only `e_O=4` row is `n=5`.
`n=15` has `e=11`; `n=17` has `e=13`. gcd is 1 except on the squares,
where `gcd(n,m)=n`.
Label: **COMPUTATIONALLY VERIFIED** on the stated window.
Do not promote a Mordell-rank theorem from the window.

## E. Boundary chains

Unique consecutive runs with `e<=2` on walks from `n<=4000`:

| classification | count |
| --- | --- |
| NEAR_CHAIN | 27 |
| ODD_SQUARE_TOWER | 4 |

Even exact-then-exact pairs on unique states: `[{'n': 16, 'next': 4}, {'n': 256, 'next': 16}, {'n': 1296, 'next': 36}]`.
They are even squares mapping to even squares: the 2-power tower
`16->4`, `256->16`, and the 4th power `1296=6^4->36`. Still perfect-power
equality, not a mixed-boundary law.
Odd both-small pairs: `[{'n': 1, 'e': 0, 'next': 1, 'next_e': 0}, {'n': 81, 'e': 0, 'next': 729, 'next_e': 0}, {'n': 625, 'e': 0, 'next': 15625, 'next_e': 0}, {'n': 2401, 'e': 0, 'next': 117649, 'next_e': 0}]`.
They are `1`, and the 4th-power squares `81,625,2401` whose cubes are
again squares. That is the odd monochrome equality family.
Label: **EXACT COMPUTATION**; the families are **LEAN-CERTIFIED**
equality / `even_tower_to_one`.

## F. Cross-branch constraints

Tested implication `e_O<=2 => e(J(n))<=2` fails. Next theta is generic.
Mixed `O->E` both-small on `n<=4000`: `[]` (empty).
That emptiness is a window count, not a mixed-boundary theorem:
`e_O<=2` occupies only `{1,3}` in the window and both land odd.
No implication stronger than evaluating `J` survived.
Label: **COUNTEREXAMPLE** to a useful next-gap law;
**COMPUTATIONALLY OBSERVED** empty mixed pair.

## G. Hard-trajectory boundary profiles

| n | word prefix | exact steps | near steps | mean theta | frac<0.1 |
| --- | --- | --- | --- | --- | --- |
| 9 | OOEOEEE | 2 | 4 | 0.333 | 0.286 |
| 37 | OOOOEOOOEEOOEEEE | 1 | 3 | 0.591 | 0.118 |
| 49 | OOEOEEOOEEE | 2 | 5 | 0.298 | 0.273 |
| 69 | OOEOOEEEOOOEEE | 1 | 5 | 0.283 | 0.143 |
| 77 | OOOEOEOOEEOEOOEO | 2 | 5 | 0.497 | 0.211 |
| 173 | OOEOOOOOOOOEOOEO | 0 | 0 | 0.43 | 0.059 |
| 193 | OOOEOOOOOOOEOOO | 0 | 0 | 0.492 | 0.067 |
| 365 | OOEOOEOOEOOEOEEE | 1 | 4 | 0.506 | 0.143 |
| 425 | OOOOOOOEOOEEOOOE | 0 | 0 | 0.498 | 0.05 |
| 2183 | OOEOOOOEOOOOOO | 0 | 0 | 0.448 | 0.143 |
| 3889 | OOOOOEOEOOOEOOEO | 0 | 0 | 0.451 | 0.125 |

Hard / PE / first-return starts are not wall-hugging. Record `193`
has mean theta about one half. Label: **COMPUTATIONALLY OBSERVED**.

## H. Root / interior comparison

`EEEEEE` at the even tower has `e=0` on every even square step.
The interior state `4294972782` has first `e=5486` then joins
the same image `65536` and the same suffix. That is `even_preimage_iff`,
not a new root/interior Diophantine law.
Same suffix from step 1: `True`.
Label: **EXACT COMPUTATION** plus **LEAN-CERTIFIED** even cell.

## I. Candidate exact laws

- `(e,u)` is `local_defect` plus complementary width. **REPARAMETERIZATION**.
- Even position does not affect `J`. **LEAN-CERTIFIED** (`even_preimage_iff`).
- `e=0` iff a perfect square. **LEAN-CERTIFIED**.
- Small odd `e` on `n<=1e5` is squares plus `{3,5,15,17}`. **COMPUTATIONALLY VERIFIED**.
- `e_O<=2` forces a small next gap. **COUNTEREXAMPLE**.
- A finite itinerary has a characteristic boundary profile. **COUNTEREXAMPLE** (`OOE`).
- Hard trajectories hug a floor wall. **COUNTEREXAMPLE**.
- `FLOOR_BOUNDARY_GREEN` / `DIOPHANTINE_BOUNDARY_GREEN` /
  `BOUNDARY_CHAIN_GREEN` / `MIXED_BOUNDARY_GREEN` /
  `MACRO_BOUNDARY_GREEN` / `BOUNDARY_CONSTRAINT_GREEN`.
  **REFUTED** as Phase-0 promotion targets.
No **CANDIDATE CONJECTURE** is opened.

## J. Counterexamples

- Even mid-cell vs wall: `36` and `38` both map to `6`.
- `n=3` has `e_O=2` and `J(3)=5` has `e_O=4`, then `11` is generic.
- `OOE` at `5` begins at theta `0.174`; at `1991` it begins at `0.660`.
- `193` mean theta `0.5`-scale, not a wall path.

| word | starts<=4000 | first theta lo | mid | hi |
| --- | --- | --- | --- | --- |
| OOE | 500 | 0.174 | 0.66 | 0.379 |
| OEO | 482 | 0.094 | 0.751 | 0.523 |
| EOO | 491 | 0.333 | 0.341 | 0.983 |
| EEOE | 399 | 0.0 | 0.708 | 0.992 |
| OOOEE | 120 | 0.182 | 0.131 | 0.35 |
| EEEE | 406 | 0.0 | 0.543 | 0.99 |
| OOOO | 282 | 0.0 | 0.66 | 0.927 |

## K. Decision

**FLOOR_BOUNDARY_COMPLEX**. Branch decision: **CLOSE**.

The pair (e,u) is local_defect plus the complementary cell gap. Even-cell position does not change J. Small odd defects on n<=1e5 are odd squares together with n=3 (e=2) and n=5 (e=4). Those isolated defects do not force the next gap to be small. Exact consecutive hits are monochrome towers. The same word admits generic and near-boundary realizers. Hard starts are not concentrated at the floor walls.

Do not invent another distance. Do not reopen Delta, pathDefectSum,
landing theta, or residual quotients.

Best next question: none from this branch.
