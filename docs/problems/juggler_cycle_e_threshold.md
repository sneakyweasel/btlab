# Juggler E-terminating threshold inventory

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Which already-proved suffix thresholds imply that \(vE\) cannot be a
cycle, and does odd-append inheritance from `OOO` close every length-5
E-terminating cycle itinerary?

## Exact statement

`no_cycle_append_even_of_suffix_threshold` is unchanged. If \(T_v(n)\ge(n+1)^2\)
on the realized domain \(n\ge N\), then there is no cycle \(vE\) at
those \(n\).

Inventory of existing next-square conclusions:

- exact `OO`, \(N=5\)
- exact `OOO`, \(N=3\)
- inherited `O^a` for \(a\ge 3\), \(N=3\): an extra realized odd letter
  is nondecreasing, so it preserves a next-square bound
- eventual every superquadratic \(v\), at the huge
  \(Q_0=D_v\cdot 4^{2^{|v|}}\)
- cell-specific `EOO` uses \((\sqrt n+1)^2\), not \((n+1)^2\)

A length-5 word \(vE\) expands iff \(32<3^{\#O(v)}\), so
\(\#O(v)\ge 4\). With \(|v|=4\) this forces \(v=\texttt{OOOO}\). The
only expanding length-5 E-terminating word is `OOOOE`, and it is
excluded by the inherited `OOOO` threshold. Every other length-5
E-word is formally contracting.

This says nothing about cycles ending in `O`. Do not prove that every
cycle itinerary is impossible. Do not prove totality. Do not treat the
eventual \(Q_0\) as a useful uniform bound.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- `OO` / `OOO` suffix thresholds —
  **EXACT — LEAN VERIFIED**.
- Eventual next-square for every superquadratic suffix —
  **EXACT — LEAN VERIFIED**.
- No length-4 E-terminating cycle —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. Existing thresholds are reused; one
odd-append lemma fills the all-odd family. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     existing thresholds forbid vE; OOO inheritance closes length 5
Novelty hypothesis      odd-append lifts OOO to O^a; every expanding vE is superquadratic
Falsifier               expanding length-5 E-word other than OOOOE
Existing machinery      no_cycle_append_even_of_suffix_threshold, ooo_suffix_threshold
Maximum Phase-0 scope   inventory; odd-append; O^a E; length-5 E-exclusion
Promotion criterion     reusable inheritance, or all length-5 E-words excluded
Stop criterion          cycle engine; length-6 census; FloorPower rewrite
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- odd-append inherits a next-square threshold —
  **EXACT — LEAN VERIFIED**
- `O^a` for \(a\ge 3\) has threshold \(N=3\) —
  **EXACT — LEAN VERIFIED**
- no `O^a E` cycle for \(a\ge 3\) and \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- no length-5 E-terminating cycle for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- every expanding \(vE\) is excluded above a huge \(Q_0(v)\) —
  **EXACT — LEAN VERIFIED**
- all E-terminating cycles are impossible — not claimed
- cycles ending in `O` are impossible — not claimed
- a useful uniform \(Q_0\) exists — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_e_threshold`
- Records: [juggler_cycle_e_threshold.md](../research/juggler_cycle_e_threshold.md),
  [juggler_cycle_e_threshold.json](../research/juggler_cycle_e_threshold.json)
- Tests: `tests/research/juggler_sequence/test_cycle_e_threshold.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the inventory or to the length-5 E-terminating exclusion. The
stronger claims that fail:

- “every expanding \(vE\) needs a new exact threshold” — the
  all-odd family inherits from `OOO`; every superquadratic \(v\)
  already has a coarse \(Q_0\).
- “the eventual \(Q_0\) is a practical bound” — it is
  \(D_v\cdot 4^{2^{|v|}}\).
- “cycles ending in `O` are included” — they are not.

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, a small extension. Added:

- `threshold_inherits_odd_append`
- `odd_run_suffix_threshold` / `no_cycle_odd_run_append_even`
- `eventually_no_cycle_append_even`
- `no_cycle_itinerary_length_five_ends_even`

`FloorPower`, `Progress`, and `MinimalNonTerm` are not rewritten. No
`sorry`. No halt theorem. No `no_juggler_cycle`. No `CycleSearch`.
No length-6 theorem. No `PowerBoundEq` attack. No `PowerHeight`.

## Results

Classification **LAST_E_THRESHOLD_COVERAGE_GREEN**, with secondary
**THRESHOLD_INHERITANCE_GREEN** and **E_TERMINATING_LENGTH5_GREEN**.

The first genuine threshold gap is an expanding E-word whose suffix
is not all-odd. That first appears at length 6 and is taken up in
[juggler_cycle_internal_e.md](juggler_cycle_internal_e.md).

## Open questions

Answered in [juggler_cycle_internal_e.md](juggler_cycle_internal_e.md):
an internal even step plus the cycle-minimum scale barrier bootstraps
the existing `OO` / `OOO` thresholds. The remaining mixed cases are
`OOOEOE` and `OOOOEE`. Do not start a length-6 census. Do not open the
O-terminating branch.

## Decision

**PROMOTE** the inventory, the odd-append inheritance, and the length-5
E-terminating exclusion. Do not claim that all cycles are impossible.
Do not claim termination. Do not treat cycles ending in `O`.

Best next question: answered in
[juggler_cycle_internal_e.md](juggler_cycle_internal_e.md).

## Publication assessment

Status: `EXPLORATORY`. A threshold-reuse lemma, not a paper candidate
and not a Juggler totality result.
