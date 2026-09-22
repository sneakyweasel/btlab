# Juggler `winkler_phase_collapse`

Winkler's normalised first-passage count, measured at every order rather than on the
record orders his theorem covers. Probe:
[winkler_phase_collapse.py](../../src/research/juggler_sequence/winkler_phase_collapse.py).
Test: [test_winkler_phase_collapse.py](../../tests/research/juggler_sequence/test_winkler_phase_collapse.py).
Ledger: `J-winkler-ratio-collapses-onto-the-phase`.

## Problem

Is Winkler's normalised count `R+_r = r c_r / C_r` of A100982 a function of the phase
`delta_r = {r log2 3}` alone?

## Exact statement

With `alpha = log2 3`, `m_r = floor(r alpha)`, `c_r = A100982(r) = M_(m_r + 1)` and
`C_r = binom(m_r - 1, r - 1)`: does there exist a function `F` on the circle with
`R+_r = F(delta_r) + o(1)` as `r` tends to infinity, and where is `F` discontinuous?

## Current literature

- `winkler-2026-admissible-qx1-sequences`, Corollary 12: `liminf R+_r = 1` and
  `limsup R+_r = alpha/(alpha - 1)`, attained exactly on the lower and upper record
  orders of `{r alpha}`. An envelope on two sparse sets of orders, with nothing said
  about a general `r`. **Extended** here, numerically, to the whole profile.
- `winkler-2026-marked-rotations`, Proposition 34: the asymptotic scale
  `C_r = kappa rho_alpha^(delta_r) B^r r^(-1/2) (1 + O(1/r))`, so the explicit part of
  the phase dependence sits in `C_r`, and `R+_r` carries the rest, bounded but unknown.
- Paper B, Section 6, and `J-paper-b-meander-prefactor-is-almost-periodic`: the survivor
  prefactor `psi({d beta})` with jumps on the orbit `{n beta}`, conjectural. Since
  `c_r = M_(m_r+1)` and `M_d = 2 N_(d-1) - N_d`, a limit for `psi` predicts one for
  `R+_r`. This branch measures the prediction on the other side.

## Branch budget

- **Target:** decide numerically whether `R+_r` depends on `r` only through `delta_r`.
- **Novelty hypothesis:** no public source describes `R+_r` away from the record orders.
- **Falsifier:** within-bin spread comparable to the across-bin range, or a shape that
  drifts between windows of `r`, or a shuffled-phase control that collapses as well.
- **Already killed by?:** none. Not a cycle, termination or floor claim, so none of the
  Diophantine walls or local-attack clusters in
  [negative_knowledge.md](../negative_knowledge.md) applies; it is a measurement on
  counts the laboratory already owns.
- **Existing machinery:** `jump_spectrum.survivor_counts`, the identity
  `c_r = M_(m_r+1)` of `J-winkler-sandwich-holds-on-the-laboratory-counts`.
- **Maximum Phase-0 scope:** one depth, 5000, three windows, one control.
- **Promotion criterion:** a stable collapse with a failing control.
- **Stop criterion:** any falsifier above.

## Balanced-ternary formulation

None. The object is the binary Beatty staircase of `log2 3`; balanced ternary plays no
role.

## Why BT may be relevant

It is not. The branch lives in the Collatz-side counting that Paper B shares with the
Juggler map.

## Candidate operations / invariants

The phase `delta_r`; the one-sided means of `R+` across an orbit point `{n alpha}`.

## Experiments

Depth 5000 gives the orders `r = 1..3154`. `c_r` reproduces A100982. Binned by
`delta_r` into 20 bins:

| window of r | across-bin range | within-bin spread | signal |
|---|---|---|---|
| 395 to 788 | 1.6852 | 0.0334 | x50.5 |
| 789 to 1577 | 1.6860 | 0.0324 | x52.0 |
| 1578 to 3154 | 1.6869 | 0.0326 | x51.7 |
| shuffled phases, 1578 to 3154 | | | x0.39 |

The per-bin shape drifts by 0.0069 and then 0.0011 between successive windows. Jumps
across the orbit points, one-sided windows of width 0.006, orders `r >= 1052`:

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| jump | +0.633 | +0.148 | +0.188 | +0.066 | +0.098 | +0.039 | +0.023 | +0.042 |

Six control points, at the midpoints of the widest gaps between the first 40 orbit
points, show +0.0017 to +0.0045. The first hand-picked controls were not controls: two
of four sat on orbit points 8 and 11, which is why the controls are now chosen by rule
and checked by a test.

## Conjectures

`R+_r = F(delta_r) + o(1)` with `F` rising from 1 at `delta = 0+` to `alpha/(alpha - 1)`
at `delta = 1-`, and upward jumps exactly on the orbit `{n alpha}`.

## Counterexamples

None found.

## Formalization

None. The existence of `F` is the same missing local limit theorem as for `psi`
(`J-paper-b-tilt-reduction-and-the-phase-factor`); nothing here is Lean-ready.

## Results

`J-winkler-ratio-collapses-onto-the-phase`, computationally verified: the collapse, its
convergence, the failing control, and the jumps on the orbit, as tabulated above.

## Open questions

Is `F` determined by `psi` through `M_d = 2 N_(d-1) - N_d`, and are its jumps the images
of `psi`'s?

## Decision

`PROMOTE` -- a stable collapse, three windows wide, with a control that fails as it
must, on counts the laboratory already owns; it answers numerically what Corollary 12
leaves open away from the record orders. Best next question: derive `F` from `psi` at
the two phases the identity `M_d = 2 N_(d-1) - N_d` pairs, and check the jump sizes
against `psi`'s spectrum.

## Publication assessment

Status: `PAPER_CANDIDATE`, as a remark in Paper B, Section 6, not as a paper of its own:
a nontrivial computation with a clear distinction from Corollary 12, the envelope.
