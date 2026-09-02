# Juggler first-even thresholds

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

For a suffix \(v\), is the first-even contraction set

\[
Q_v=\{q:T_v(q)<(q+1)^2\}
\]

finite when \(Ev\) has positive formal drift?

## Exact statement

Write \(\alpha_v=3^{\#O(v)}/2^{|v|}\). The itinerary \(Ev\) has formal
ratio \(\alpha_v/2\), so it is formally expanding iff \(\alpha_v>2\).
On the square-root cell of \(q\), contraction occurs iff
\(T_v(q)<n\). For integers this is any-contraction iff
\(T_v(q)+1<(q+1)^2\), and whole-cell contraction iff \(T_v(q)<q^2\).

Is \(Q_v\) finite for the shortest suffixes with \(\alpha_v>2\),
starting with \(v=OO\) and \(v=OOO\)?

This is a local arithmetic question. It is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Previous phases: first-even freeze and EOO cell classification —
  **EXACT — LEAN VERIFIED**.
- `eoo_cell_output_ge_succ_sq`: \(q\ge5\Rightarrow
  \mathrm{eooCellOutput}\,q\ge(q+1)^2\) —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The EOO bound is reused as the
`OO` eventual threshold.

## Branch budget

```text
Mathematical target     For α_v > 2, is Q_v finite?
Novelty hypothesis      OO and OOO have eventual thresholds
                        q ≥ Q0 ⇒ T_v(q) ≥ (q+1)^2
Falsifier               A large or infinite Q_v for OO/OOO; or
                        monotonicity forced as a theorem after a break
Existing machinery      first_even_freeze, eoo_cell_output_ge_succ_sq
Maximum Phase-0 scope   Exact cell-interval lemmas; Q_v for short
                        suffixes; Lean finiteness for OO and OOO
Promotion criterion     FIRST_E_FINITE_GREEN with an explicit bound,
                        or FIRST_E_INFINITE_FAMILY
Stop criterion          Generic lower envelope; cell tree; PowerHeight;
                        engine edits; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Any-contraction iff \(c+1<(q+1)^2\) —
  **EXACT — LEAN VERIFIED**
- Whole-cell contraction iff \(c<q^2\) —
  **EXACT — LEAN VERIFIED**
- \(Q_{OO}\) finite: \(q\ge5\Rightarrow T_{OO}(q)\ge(q+1)^2\) —
  **EXACT — LEAN VERIFIED**
- \(Q_{OOO}\) finite: \(q\ge3\Rightarrow T_{OOO}(q)\ge(q+1)^2\) —
  **EXACT — LEAN VERIFIED**
- One odd step is nondecreasing —
  **EXACT — LEAN VERIFIED**
- Threshold monotonicity for all suffixes — **not proved**; no
  counterexample on the scanned window
- Infinite positive-drift \(Q_v\) — **not found**. \(Q_O\) is
  infinite, but \(\alpha_O=3/2\le2\), so \(EO\) is formally
  contracting
- Generic lower envelope — not added
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.first_even_thresholds`
- Records: [juggler_first_even_thresholds.md](../research/juggler_first_even_thresholds.md),
  [juggler_first_even_thresholds.json](../research/juggler_first_even_thresholds.json)
- Tests: `tests/research/juggler_sequence/test_first_even_thresholds.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- The continuous test \(c<(q+1)^2\) is not the exact integer
  any-contraction test. The exact condition is \(c+1<(q+1)^2\).
- \(Q_O\) is all realized odd \(q\). That is not a positive-drift
  family: \(EO\) has formal ratio \(3/4<1\).

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `cell_any_contracts_iff` / `cell_all_contracts_iff`
- `first_even_any_contracts_iff` / `first_even_all_contracts_iff`
- `floorPower_odd_ge`
- `oo_suffix_threshold` / `ooo_suffix_threshold`

Unchanged: `first_even_freeze`, `power_bound_compensated_contracts`,
`floorPower_eoo_contracts_iff`. No cell tree. No lower-envelope
structure. No `sorry`. No ledger row.

## Results

Classification **FIRST_E_FINITE_GREEN**.

For the shortest positive-drift suffixes:

- \(v=OO\), \(\alpha=9/4>2\): \(Q=\{1,3\}\). Every realized
  \(q\ge5\) satisfies \(T_{OO}(q)\ge(q+1)^2\).
- \(v=OOO\), \(\alpha=27/8>2\): \(Q=\{1\}\). Every realized
  \(q\ge3\) satisfies \(T_{OOO}(q)\ge(q+1)^2\), because a later odd
  step is nondecreasing.

`EOO` and `EOOO` are the corresponding first-even words. The
enumerated starts \(n=2,12,14\) and \(n=2\) are the realized points
of those finite \(Q_v\).

Suffixes with \(\alpha_v\le2\) can have large or infinite \(Q_v\),
but then \(Ev\) is formally contracting. That is a different regime.

This is not a termination theorem.

## Open questions

Is every suffix with \(\alpha_v>2\) eventually above \((q+1)^2\)? Is
there a borderline \(\alpha_v>2\) suffix whose floors dip below the
next square infinitely often?

## Decision

**PROMOTE** the exact cell-interval law and the `OO`/`OOO`
finiteness theorems `FIRST_E_FINITE_GREEN`. Do not open a generic
lower envelope. Do not claim an infinite compensated family from
\(Q_O\). Do not register an attack. Do not claim termination.

Best next question: prove eventual non-contraction for every suffix
with \(\alpha_v>2\), or find one such suffix with unbounded \(Q_v\).

## Publication assessment

Status: `EXPLORATORY`. A local finite-itinerary threshold statement, not a
paper candidate and not a Juggler totality result.
