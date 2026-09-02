# Juggler cycle arrival and collision classification

Status: **CLOSE** (Lean names the cyclic in-edge at every
`CycleItinerary` vertex; the inverse-parent set is still
`parent_cases`)

Not a halt theorem, not a leftover-killer, not a bead rewrite, not
a reopen of seam ancestry / first collision, and not a Paper A
edit. Peak stays terminology.

## Problem

The valley package in `Seam.lean` names the fork at a CycleMin
cut. Local position on a general cyclic spelling is the previous
letter at an actual orbit vertex, not a CycleMin cut and not a
bead station. Does that predecessor type add a fibre law, or does
it only select the cyclic in-edge?

## Exact statement

Let \(w\) be a `CycleItinerary n w` word and let \(k < L\) be an
orbit index, \(L=\lvert w\rvert\). Write \(x=T^k(n)\) and
\(c_{-}=T^{k-1}(n)\) for the cyclic parent
(`cycleParent`). Arrival is the previous letter:

```text
previous O  →  O-arrival  →  c_{-} odd
previous E  →  E-arrival  →  c_{-} even
```

**Collision Factorization at an actual vertex (EXACT — LEAN
VERIFIED).** A first meeting at \(x\) uses an off-orbit parent.
The unique on-orbit parent of \(x\) is \(c_{-}\)
(`cycle_in_edge_unique_onOrbit`). Distinctness is on-orbit versus
off-orbit (`collision_parents_distinct`).

**Arrival taxonomy (EXACT — LEAN VERIFIED).** O-arrival forces
an even first-meeting stem, because the cyclic parent is already
the unique odd parent (`oArrival_stem_even`,
`odd_preimage_unique`). E-arrival places \(c_{-}\) in the even
square cell; the stem is any other parent
(`eArrival_stem_parent_cases` = `parent_cases`). The fibre of
\(x\) does not depend on how the cycle arrived
(`parent_fibre_of_vertex`).

**Valley specialization (EXACT — LEAN VERIFIED).** A CycleMin
cut is E-arrival (`valley_is_eArrival`, by
`cycleMin_not_end_odd`). Valley strength is
`cycle_last_even_interval` plus `odd_parent_lt`.

**Rotation (EXACT — LEAN VERIFIED).** Arrival type and orbit
membership transport under `rotateItinerary`
(`cycleArrival_rotate`, `onOrbit_rotate`).

Peak is not a formal invariant. O-arrival is. No cycle of any
length — not claimed.

## Current literature

- Collision Factorization — **EXACT — HUMAN PROOF** in
  [juggler_cycle_first_collision.md](juggler_cycle_first_collision.md);
  **EXACT — LEAN VERIFIED** at the CycleMin valley in
  [juggler_functional_graph_seam.md](juggler_functional_graph_seam.md)
  (`Seam.lean`); now also at a general `CycleItinerary` vertex
  (`CyclePosition.lean`)
- Parent fibres — **EXACT — LEAN VERIFIED**
  (`parent_cases`, `odd_preimage_unique`)
- CycleMin last even / not end odd — **EXACT — LEAN VERIFIED**
  (`cycle_last_even_interval`, `cycleMin_not_end_odd`)
- Joint leftover-killer / new pair law — **REFUTED**
  (`juggler_cycle_first_collision`, `juggler_cycle_seam_ancestry`)
- Orbit-indexed join table — **REPARAMETERIZATION**
  (`every_orbit_index_is_join_site` in `Seam.lean`)
- Bead schema — **EXACT — LEAN VERIFIED** projection
  (`IdealCycleMin.lean`); this file does not import it

Project relationship: **reparameterization** of the closed local
attack record as predecessor type on a cyclic word.

## Branch budget

```text
Mathematical target     Does predecessor type at a CycleItinerary
                        vertex add a fibre law, or only name the
                        cyclic in-edge?
Novelty hypothesis      a new arithmetic or pair constraint
                        beyond parent_cases, odd_preimage_unique,
                        and cycleMin_not_end_odd
Falsifier               every compiled statement is the existing
                        cell package or Collision Factorization
Existing machinery      CycleItinerary; cycle_iterate_mod;
                        parent_cases; odd_preimage_unique;
                        cycleMin_not_end_odd;
                        cycle_last_even_interval; Seam.lean
                        valley package
Maximum Phase-0 scope   CyclePosition.lean over CycleCore +
                        InverseBranches; no IdealCycleMin import;
                        no finance / DK / Paper A; no UI
Promotion criterion     a genuinely new exact graph constraint
                        that is not CF or the parent cells
Stop criterion          statements are KNOWN or REPARAMETERIZATION
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `cyclePrevIndex` / `cycleParent` / `cycleArrival` —
  **REPARAMETERIZATION** of the previous letter
- `OnOrbit` — **REPARAMETERIZATION** of `CycleItinerary` plus
  an iterate
- `CollisionFactorization` — **EXACT — LEAN VERIFIED** /
  **REPARAMETERIZATION** of first meeting at a general vertex
- `oArrival_stem_even` — **EXACT — LEAN VERIFIED** /
  **REPARAMETERIZATION** of `odd_preimage_unique`
- `eArrival_stem_parent_cases` — **EXACT — LEAN VERIFIED** /
  **REPARAMETERIZATION** of `parent_cases`
- `IsValley` — **REPARAMETERIZATION** of CycleMin at index 0
- Peak as a formal invariant — terminology only; the invariant
  is `CycleArrival.oArrival`
- New leftover emptiness — **REFUTED** as a target (closed
  local-attack record)
- No cycle of any length — not claimed

## Experiments

None. No census, no CLI, no new \(N_0\).

## Conjectures

None.

## Counterexamples

None new. Named forks stay in the closed first-collision
dossier: \(100\to 10\leftarrow 102\), \(25\to 125\) Type 2, and
the sink \(2\to 1\leftarrow 1\).

## Formalization

`formal/Problems/Juggler/CyclePosition.lean`. Imports
`CycleCore` and `InverseBranches` only. Imported by
`Problems.Juggler`. Does not import `IdealCycleMin`. Does not
replace `CycleMin`, `CycleItinerary`, first-even / last-even, or
the `OO` / wrap-`EO` sure-link theorems. No `sorry` / `admit`.
`lake build Problems.Juggler.CyclePosition` succeeded.

The existing valley package in `Seam.lean` stays. CyclePosition
is the CycleItinerary-based general layer.

## Results

Classification **CYCLE_ARRIVAL_COLLISION_REPARAMETERIZATION**.

- Arrival type names the cyclic in-edge. The inverse-parent set
  of \(x\) is still `parent_cases`.
- O-arrival kills an odd stem only via `odd_preimage_unique`.
- E-arrival does not kill the odd stem.
- A valley is E-arrival at a CycleMin cut, by
  `cycleMin_not_end_odd`, not by a six-bead table.
- Peak is terminology. O-arrival is the formal invariant.
- Rotation transports arrival and orbit membership.
- No new leftover constraint.

## Open questions

None from this door. Do not reopen first collision, seam
ancestry, cyclic seam, or cycle-lift drop. Do not treat
`CycleArrival` as a leftover-killer. Peak stays terminology.

## Decision

**CLOSE.** Lean now names predecessor type at every
`CycleItinerary` vertex and proves Collision Factorization
there. Every statement is `KNOWN` or `REPARAMETERIZATION` of
`parent_cases`, `odd_preimage_unique`, `cycleMin_not_end_odd`,
`cycle_last_even_interval`, and forward invariance. That is the
stop criterion. Best next question: none from this door; do not
treat CyclePosition as a leftover-killer.

## Publication assessment

Status: `ARCHIVED`. Laboratory packaging of a closed kill.
Not a paper candidate. No Paper A/B edit.
