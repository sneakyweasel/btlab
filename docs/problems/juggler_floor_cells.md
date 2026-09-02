# Juggler floor-cell geometry

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Is compensated contraction a geometric intersection of an exact floor
cell with an output threshold, and does the first-even freeze

\[
T_{Ev}(n)=T_v(\lfloor\sqrt n\rfloor)
\]

reuse beyond `EOO`?

## Exact statement

For a realized first-even word \(Ev\), is the block output constant on
each square-root cell \([q^2,(q+1)^2)\) and equal to \(T_v(q)\)? Does
contraction reduce to \(T_v(q)<n\)? How wide are the dual odd cells
\(m^2\le n^3<(m+1)^2\)? Do positive-drift first-even words have
infinitely many contraction cells?

This is a local arithmetic question. It is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Inverse-floor lemmas
  `floorPower_even_eq_iff_sq_interval` /
  `floorPower_odd_eq_iff_cube_interval` —
  **EXACT — LEAN VERIFIED**.
- Previous phase (`juggler_eoo_cell_mechanism`): `EOO` contracts by
  the cell threshold \(n>c(q)\) — **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The EOO cell is the first-even
freeze specialized to the suffix `OO`.

## Branch budget

```text
Mathematical target     Is T_Ev(n)=T_v(⌊√n⌋) reusable, and do
                        positive-drift Ev words have infinitely many
                        contraction cells?
Novelty hypothesis      First-even freeze plus a threshold trichotomy;
                        odd cells are too thin to freeze a suffix
Falsifier               Freeze fails; odd cells are wide; or a
                        parametrized positive-drift family is ignored
Existing machinery      inverse-floor iff, EOO cell threshold, follows
Maximum Phase-0 scope   Generic freeze; recover EOO; Ev scan ≤6;
                        odd-cell uniqueness
Promotion criterion     FIRST_E_FREEZE_GREEN with EOO as a corollary,
                        or CELL_FAMILY_FOUND, or a minimized duality
                        counterexample
Stop criterion          Cell tree; PowerHeight; engine edits; halt
                        claim; census-as-theorem
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Even cell \(T(n)=q\iff q^2\le n<(q+1)^2\) (even \(n\)) —
  **EXACT — LEAN VERIFIED**
- Odd cell \(T(n)=m\iff m^2\le n^3<(m+1)^2\) (odd \(n\)) —
  **EXACT — LEAN VERIFIED**
- First-even freeze \(T_{Ev}(n)=T_v(\lfloor\sqrt n\rfloor)\) —
  **EXACT — LEAN VERIFIED**
- First-even contraction iff \(T_v(\lfloor\sqrt n\rfloor)<n\) —
  **EXACT — LEAN VERIFIED**
- Odd cell uniqueness — **EXACT — LEAN VERIFIED**
- Cell trichotomy (all-contract / all-expand / mixed) —
  **EXACT — LEAN VERIFIED**
- Infinite positive-drift first-even contraction family —
  **REFUTED** on the scanned window; only small cells mix or
  all-contract
- Recursive cell tree — not added
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.floor_preimages`
- Records: [juggler_floor_cells.md](../research/juggler_floor_cells.md),
  [juggler_floor_cells.json](../research/juggler_floor_cells.json)
- Tests: `tests/research/juggler_sequence/test_floor_cells.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- Odd-start words are constant on their first cells only because those
  cells are singletons. That is not a useful freeze.
- `n=10` remains the mixed-cell expander for `EOO` (\(c=11\)).
- Positive-drift `Ev` itineraries of length \(\le6\) produced no parametrized
  family of contraction cells.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `even_preimage_iff` / `odd_preimage_iff`
- `iterate_cons_even` / `iterate_cons_odd`
- `first_even_freeze` / `first_odd_freeze`
- `first_even_contracts_iff` / `eoo_from_first_even`
- `suffix_same_output_on_cell`
- `constant_cell_trichotomy`
- `odd_preimage_unique`

Unchanged: `power_bound_compensated_contracts`,
`floorPower_eoo_contracts_iff`, `eoo_contracts_on_cell`. No cell tree.
No `PowerHeight`. No `sorry`. No ledger row.

## Results

Classification **FIRST_E_FREEZE_GREEN**.

Every realized first-even word obeys

\[
T_{Ev}(n)=T_v(\lfloor\sqrt n\rfloor)
\]

on the square-root cell, and contracts iff \(T_v(q)<n\). `EOO` is the
mixed-cell case \(q=1,3\). `EEOOOO` is an entire-cell case: \(q=2\),
\(c=1<4\), so \(n\in\{4,6,8\}\). Odd cells contain at most one integer,
which is why `OOE` and `OEO` do not freeze a range.

A recursive partition/tree is not justified: one even letter already
freezes the suffix, and an odd letter refines to singletons.

This is not a termination theorem.

## Open questions

Is there a first-even positive-drift suffix whose output stays below
\((q+1)^2\) for infinitely many \(q\), despite formal growth? Do `OOE`
and `OEO` never contract?

## Decision

**PROMOTE** the first-even freeze and odd-cell uniqueness
`FIRST_E_FREEZE_GREEN`. Recover `EOO` as a corollary. Record `EEOOOO`
as a second finite entire-cell example, not a parametrized family. Do
not add a cell tree. Do not register an attack. Do not claim
termination.

Best next question: prove there are only finitely many first-even
positive-drift contraction cells, or find a suffix that stays below
the next square for infinitely many \(q\).

## Publication assessment

Status: `EXPLORATORY`. A local finite-itinerary cell identity, not a paper
candidate and not a Juggler totality result.
