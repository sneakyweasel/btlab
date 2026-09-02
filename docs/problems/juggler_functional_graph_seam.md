# Juggler functional-graph seam interface

Status: **CLOSE** (Lean packages Collision Factorization and the
existing parent cells; no new leftover constraint)

Not a halt theorem, not a leftover-killer, not a bead rewrite, not
a reopen of seam ancestry / first collision / cyclic seam, and not
a Paper A edit.

## Problem

The bead file records CycleMin letters and an optional symbolic
stem. The stem–cycle join is a picture. Can Lean name the actual
integer fork where an off-cycle parent and the cyclic parent both
map to a CycleMin valley, and prove the local graph constraints
already known as Collision Factorization?

## Exact statement

Let \(C\) be a `CycleMin n w` orbit. Write \(c_{-}\) for
`cycleParentOf n w` \(= T^{L-1}(n)\). A *seam* is a parent \(t\)
with \(T(t)=n\) and \(t\notin C\).

**Collision Factorization (EXACT — LEAN VERIFIED).**
A first hitting time of \(C\) at \(n\) uses an external parent
(`collision_factorization`). An external parent is a length-1
first meeting (`collision_factorization_one_step`). The unique
on-cycle parent of \(n\) is \(c_{-}\) (`cycle_in_edge_unique`).

**Parent cells (EXACT — LEAN VERIFIED).**
Every parent of \(y\) is an even square-cell point or the unique
odd cube-cell point (`parent_cases`, `odd_parents_eq`). For
\(n\ge 3\), an odd parent satisfies \(t<n\) (`odd_parent_lt`).
On a CycleMin valley that odd parent is automatically off-cycle
(`odd_parent_of_cycleMin_off_cycle`). The cyclic parent is even
and lies in \([n^2,(n+1)^2)\) (`cycleMin_cycleParent_cell`).

**Orientation (EXACT — LEAN VERIFIED).**
Every parent of \(n\) reaches \(c_{-}\) around the orbit
(`seam_stem_ancestor_of_cycleParent`). The cycle cannot reach an
external stem parent (`seam_cycle_not_ancestor_of_stem`).

No cycle of any length — not claimed.

## Current literature

- Collision Factorization — **EXACT — HUMAN PROOF** in
  [juggler_cycle_first_collision.md](juggler_cycle_first_collision.md);
  now also **EXACT — LEAN VERIFIED** in `Seam.lean`
- Parent fibres — **EXACT — LEAN VERIFIED**
  (`even_preimage_iff`, `odd_preimage_iff`, `odd_preimage_unique`)
- CycleMin last even / not end odd — **EXACT — LEAN VERIFIED**
  (`cycle_last_even_interval`, `cycleMin_not_end_odd`)
- Joint leftover-killer / new pair law — **REFUTED**
  (`juggler_cycle_first_collision`, `juggler_cycle_seam_ancestry`)
- Bead schema — **EXACT — LEAN VERIFIED** projection
  (`IdealCycleMin.lean`); unchanged

Project relationship: **reparameterization** of the closed local
attack record as an integer-edge interface.

## Branch budget

```text
Mathematical target     Can Lean express the stem–cycle seam as
                        actual Juggler edges and prove at least
                        the known Collision Factorization /
                        parent-cell restrictions?
Novelty hypothesis      a new arithmetic, parity, or ancestry
                        constraint beyond unique cyclic in-edge,
                        odd_preimage_unique, and cycleMin_not_end_odd
Falsifier               every compiled statement is the existing
                        cell package or Collision Factorization
Existing machinery      floorPower; even_preimage_iff;
                        odd_preimage_unique; CycleMin;
                        cycle_last_even_interval;
                        cycleMin_not_end_odd; cycle_iterate_mod
Maximum Phase-0 scope   FunctionalGraph + InverseBranches + Seam;
                        no CycleBasin library; no bead rewrite;
                        no finance / DK / Paper A
Promotion criterion     a genuinely new exact graph constraint
                        that is not CF or the parent cells
Stop criterion          statements are KNOWN or REPARAMETERIZATION
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `JEdge` / `JPath` / `Ancestor` — **REPARAMETERIZATION** of
  `floorPower` iterates
- `parent_cases` — **EXACT — LEAN VERIFIED** /
  **REPARAMETERIZATION** of the one-step cells
- `SeamData` — **EXACT — LEAN VERIFIED** interface
- `cycle_in_edge_unique` / `collision_factorization` —
  **EXACT — LEAN VERIFIED** / **REPARAMETERIZATION** of
  forward invariance plus periodicity
- `odd_parent_of_cycleMin_off_cycle` — **EXACT — LEAN VERIFIED**
  / **REPARAMETERIZATION** of `odd_parent_lt` plus `cycleMin_ge`
- New leftover emptiness — **REFUTED** as a target (closed
  local-attack record)
- No cycle of any length — not claimed

## Experiments

None. No census, no CLI, no new \(N_0\). The sink instance
`sink_seam_two_to_one` is the recorded \(2\to 1\leftarrow 1\)
loop, compiled as `SeamData`.

## Conjectures

None.

## Counterexamples

- \(2\to 1\leftarrow 1\): external even parent of the unique
  known cycle. Witness that a seam exists on the trivial orbit
  and that \(T^L(t)<n\) fails (`juggler_cycle_lift_ancestry`).
- Named nontrivial forks \(100\to 10\leftarrow 102\) and
  \(25\to 125\) stay in the closed first-collision dossier.

## Formalization

`formal/Problems/Juggler/FunctionalGraph.lean`,
`InverseBranches.lean`, `Seam.lean`. Imported by
`Problems.Juggler`. `IdealCycleMin.lean` does not import the
seam layer. No `sorry` / `admit`.
`lake build Problems.Juggler.Seam` succeeded.

Orbit-indexed join: `every_orbit_index_is_join_site`,
`cycle_in_edge_unique_at`, `join_valley_arrival_even`,
`join_arrives_odd_external_even`,
`join_arrives_even_cycle_parent_cell`,
`rotate_even_not_cycleMin`, `rotate_OE_not_cycleMin`.
Companion table: `web/juggler-companion/src/juggler/joinConfig.ts`.

## Results

Classification **FUNCTIONAL_GRAPH_SEAM_REPARAMETERIZATION**.

- The bead join stays a picture. The integer fork is `SeamData`.
- Collision Factorization and the unique cyclic in-edge compile.
- Valley cyclic parent is even in the last-even cell. An odd
  stem parent is `< n` and off-cycle. An even stem parent is
  another point of the same square cell, required distinct by
  the external-parent hypothesis.
- Ancestry through the valley is true of every parent of \(n\).
  The distinguishing orientation is \(\neg\) cycle \(\leadsto\)
  external stem.
- No new leftover constraint.

## Open questions

None from this door. Do not reopen first collision, seam
ancestry, cyclic seam, seam sliding, or cycle-lift drop. Do
not treat `SeamData` as a halt engine.

## Decision

**CLOSE.** Lean now names the integer stem–cycle fork and
proves Collision Factorization, unique cyclic in-edge, and the
parent-cell split. Every statement is `KNOWN` or
`REPARAMETERIZATION` of `even_preimage_iff`,
`odd_preimage_unique`, `cycleMin_not_end_odd`,
`cycle_last_even_interval`, and forward invariance. That is
the stop criterion. Best next question: none from this door;
the bead file stays a projection, and the seam interface is
not a leftover-killer.

## Publication assessment

Status: `ARCHIVED`. Laboratory packaging of a closed kill.
Not a paper candidate. No Paper A/B edit.
