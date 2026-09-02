# Juggler Archimedean floor-boundary geometry

Status: **EXPLORATORY**

Standalone Diophantine layer on the exact Juggler floor cells. It is
**not** a Research Engine control-layer experiment, not a scalar-invariant
search, and not a claim that every positive integer reaches 1.

## Problem

Does the arithmetic geometry of the exact floor boundaries impose any
restriction on difficult Juggler trajectories that is invisible in the
existing finite-itinerary envelope and cell lemmas?

## Exact statement

Write `e` for the existing `local_defect` and `u = 2m+1-e` for the
complementary gap in the cell of width `2m+1`. Phase 0 asks whether
hard trajectories, small-`e` odd states, or consecutive near-boundary
steps obey an exact implication that is not `even_preimage_iff`,
`odd_preimage_unique`, `localDefect*_eq_zero_iff`, or monochrome equality.
This says nothing about totality.

## Current literature

- `even_preimage_iff` / `odd_preimage_unique` / inverse-floor intervals —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Preimages`.
- `localDefectEven` / `localDefectOdd` and `*_lt_succ` / `*_eq_zero_iff` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Defect`.
- Envelope equality iff monochrome —
  **EXACT — LEAN VERIFIED**.
- `even_tower_to_one` —
  **EXACT — LEAN VERIFIED**.
- Sequential Mordell / landing valuation / summed-rho / information
  complexity / 2-adic bridge / realization geometry / first-return /
  backward cells / acceleration —
  **CLOSE**. Do not reopen.

Project relationship: **extended**. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Do exact floor-boundary positions (e,u) of
                        hard Juggler trajectories obey a Diophantine
                        restriction invisible in the envelope / cell
                        lemmas?
Novelty hypothesis      Small (e,u) forces a next-step gap law, a
                        restricted Mordell family, or a mixed
                        boundary-chain obstruction
Falsifier               (e,u) is generic on hard vs ordinary paths;
                        even-cell position does not affect J;
                        odd small-delta is localDefectOdd; chains
                        reduce to equality / towers
Existing machinery      local_defect, even_preimage, odd_preimage_unique,
                        localDefect*_eq_zero_iff, equality
                        monochrome, even_tower, first-return records
Maximum Phase-0 scope   n<=4000 unique states; odd e<=16 on n<=1e5;
                        length-2/3 chains; hard vs same-word pairs
Promotion criterion     An exact implication e<=C => next gap bound
                        that is not a cell / equality lemma
Stop criterion          Profiles generic; chains are equality;
                        even (e,u) inert; odd small-delta does not
                        constrain the next step
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- `(e,u)` as a new invariant —
  **REPARAMETERIZATION** of `local_defect` plus cell width
- Even-cell position changes `J` —
  **REFUTED**
- `e_O<=2` forces a small next gap —
  **REFUTED**
- An itinerary has a characteristic boundary profile —
  **REFUTED** (`OOE`)
- Hard starts hug a floor wall —
  **REFUTED**
- Small odd `e` on `n<=1e5` is squares plus a few isolates —
  **COMPUTATIONALLY VERIFIED**
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.floor_boundary`
- Records: [juggler_floor_boundary.md](../research/juggler_floor_boundary.md),
  [juggler_floor_boundary.json](../research/juggler_floor_boundary.json)
- Dataset: `data/research/juggler/floor_boundaries/`
- Tests: `tests/research/juggler_sequence/test_floor_boundary.py`

No GPU. No atlas recensus. No new Lean file.

## Conjectures

None opened.

## Counterexamples

- Even wall vs mid-cell: `36` and `38` both map to `6`.
- `e_O<=2` then small next `e`: next theta mean is mid-cell.
- `OOE` at `5` vs `1991` vs `3989`: first thetas differ.
- `193` is not a wall path.

## Formalization

None added. Existing Defect / Cells / Equality / Collapse lemmas stay
as they are. No `sorry`.

## Results

Classification **FLOOR_BOUNDARY_COMPLEX**.

The pair (e,u) is local_defect plus the complementary cell gap. Even-cell position does not change J. Small odd defects on n<=1e5 are odd squares together with n=3 (e=2) and n=5 (e=4). Those isolated defects do not force the next gap to be small. Exact consecutive hits are monochrome towers. The same word admits generic and near-boundary realizers. Hard starts are not concentrated at the floor walls.

## Open questions

None from this branch. Do not invent another distance. Do not reopen
Delta or landing theta.

## Decision

**CLOSE**. The pair (e,u) is local_defect plus the complementary cell gap. Even-cell position does not change J. Small odd defects on n<=1e5 are odd squares together with n=3 (e=2) and n=5 (e=4). Those isolated defects do not force the next gap to be small. Exact consecutive hits are monochrome towers. The same word admits generic and near-boundary realizers. Hard starts are not concentrated at the floor walls. Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A negative Diophantine census of floor-cell
position, not a paper candidate and not a Juggler totality result.
