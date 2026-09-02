# Juggler backward predecessor geometry

Status: **EXPLORATORY**

Standalone Phase-0 study of the inverse graph of the Juggler
floor-power map. It is **not** a Research Engine control-layer
experiment, not a Collatz inverse, not a cell-tree engine, and not
a claim that every positive integer reaches 1. Closed PE-factor,
residual-quotient, prefix-NC, preimage-cylinder, realization-geometry,
first-return, adversarial-path, information-complexity, and sum-rho
branches are not reopened.

## Problem

Does repeated exact inversion of the Juggler floor-power map impose
a structural constraint on inverse histories that is invisible in
the forward \(O/E\) word dynamics?

## Exact statement

Write \(T\) for the unaccelerated floor-power map. For \(m\ge 1\),

\[
\operatorname{Pred}_E(m)=\{n\text{ even}:m^2\le n<(m+1)^2\},
\quad
\operatorname{Pred}_O(m)=\{n\text{ odd}:m^2\le n^3<(m+1)^2\},
\]

and \(\operatorname{Pred}(m)=\operatorname{Pred}_E(m)\cup\operatorname{Pred}_O(m)\).
Every edge must satisfy \(T(n)=m\). The Phase-0 question is whether
a finite inverse letter word \(\kappa\), or a bounded inverse tree
rooted at a selected \(m\), obeys a scale inequality, sparsity bound,
well-founded rank, or hard-path restriction that is not the one-step
cell law, odd-cell uniqueness, or the reverse of a forward itinerary.

The Collatz predecessor \(n=(2^k m-1)/3\) is a different map and is
not used.

This says nothing about totality. An infinite even inverse ray is
not a nontermination certificate. Finite observed depth is not a
bound on inverse rays.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Inverse-floor cells `even_preimage_iff` / `odd_preimage_iff` /
  `odd_preimage_unique` — **EXACT — LEAN VERIFIED** in
  `Problems.Juggler.Preimages`.
- `floorPower_one` — **EXACT — LEAN VERIFIED**.
- Prefix-NC backward admissibility —
  **CLOSE** as `PREFIX_NC_ARITHMETIC_COMPLEX`.
- Predecessor cylinders —
  **CLOSE** as `PREIMAGE_CYLINDER_IS_Y`.
- Realization-set prepend —
  **CLOSE** as `REALIZATION_GEOMETRY_COMPLEX`.
- Iterated odd-landing sets —
  **CLOSE**; unique odd preimages are `odd_preimage_unique`.
- First-return / adversarial paths / information-complexity / PE
  factors / residual quotients / sum-rho — **CLOSE**. Reused as
  fixtures only.

Project relationship: **extended**. The leftover after the closed
one-step and word-cylinder attacks is whether *repeated mixed*
inversion adds rigidity.

## Branch budget

```text
Mathematical target     Does repeated mixed inversion impose a
                        constraint beyond the floor cells?
Novelty hypothesis      mixed-path scale, sparsity, rank, or
                        hard-path rigidity
Falsifier               every candidate is a cell corollary or
                        reverse itinerary
Existing machinery      even_preimage, odd_preimage_integers, floor_power,
                        Preimages.lean, known hard/PE walks
Maximum Phase-0 scope   Pred census m<=4000; bounded BFS on
                        selected roots; nested cell composition;
                        reverse images of known walks; no GPU;
                        no Lean pilot
Promotion criterion     a BACKWARD_*_GREEN law about repeated
                        inverse structure
Stop criterion          BACKWARD_COMPLEX; reparameterization of
                        Cells; machinery gravity; closed-branch reopen
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. Balanced-ternary metadata were not used as a
distinguishing predicate.

## Candidate operations / invariants

- \(\lvert\operatorname{Pred}_E(m)\rvert=m\) or \(m+1\) —
  **KNOWN**; evens in an interval of length \(2m+1\)
- \(\lvert\operatorname{Pred}_O(m)\rvert\in\{0,1\}\) —
  **EXACT — LEAN VERIFIED** (`odd_preimage_unique`)
- Even inverse edges ascend, odd inverse edges descend except \(1\to 1\) —
  **KNOWN** from the cell bounds
- Composed inverse \(m_r=A_r m_0-B_r\) —
  **REPARAMETERIZATION** rejected; the even step is quadratic
- Interval-hull bounds stricter than the exact fiber —
  **REPARAMETERIZATION** of cells on the real predecessor set
  versus a relaxation that fills gaps
- Hard-path predecessors are distinguished in \(\operatorname{Pred}(y)\) —
  **REFUTED** on the fixture walks; labels are unique-odd or
  ordinary even-cell points
- \(m\bmod 3\) organises inverse branching —
  **REFUTED** as an admissibility rule; occupancy is a thin
  image-of-odd-\(T\) rate in every class
- Same-root inverse collisions —
  **KNOWN** absent; \(T\) is a function

## Experiments

- Probe: `research.juggler_sequence.backward_geometry`
- Records: [juggler_backward_geometry.md](../research/juggler_backward_geometry.md)
- Dataset: `data/research/juggler/backward/`
- Tests: `tests/research/juggler_sequence/test_backward_geometry.py`

No GPU. No Lean. No Phase 1.

## Conjectures

None opened.

## Counterexamples

- “composed bounds are a new scale law”: hull-versus-fiber gaps at
  `EEO` on \(3,5,7\) and `EO`/`EOE` on \(11\) are interval relaxations.
- “hard paths have unusual inverse labels”: \(3,365,425,2183,3889\)
  use only unique-odd or ordinary even-cell points.
- “\(m\bmod 3\) organises \(\operatorname{Pred}_O\)”: occupancy
  \(44/1333\), \(40/1334\), \(42/1333\).
- Even descending or odd ascending edges on \(1\le m\le 4000\): none
  except the fixed point \(1\to 1\).

## Formalization

None added. Existing `Preimages.lean` lemmas are reused. No `sorry`.

## Results

Phase 0 is recorded in
[juggler_backward_geometry.md](../research/juggler_backward_geometry.md).
Classification **BACKWARD_COMPLEX**.

Every \(m\) in the window has a nonempty even cell. Odd cells are
occupied at rate \(63/2000\). Repeated inversion is nested cells:
even letters explode quadratically and leave every finite bound;
odd letters form a unique descending spine that stops at an empty
cell. Inverse trees from a fixed root do not collide. Known hard
forward prefixes reverse to ordinary cell points. The tree of \(1\)
is the basin of the only known positive odd fixed point, not a new
exceptional law.

## Open questions

None from this branch. Do not infer totality from the basin of \(1\).
Do not launch a GPU predecessor census without a surviving law.

## Decision

**CLOSE**. Repeated exact inversion does not add a structural law
beyond the existing floor cells. Do not invent another scalar. Do
not reopen closed backward or forward branches.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. Not a paper candidate and not a Juggler
totality result.
