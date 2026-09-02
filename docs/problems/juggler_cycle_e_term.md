# Juggler E-terminating cycle exclusion

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can the `OOE` last-even cell argument be lifted to a generic theorem
— whenever the suffix \(v\) of \(vE\) sits at or above the next
square, the cycle is impossible — and does that close every length-4
E-terminating cycle itinerary?

## Exact statement

If `CycleItinerary n (v ++ [E])`, then

\[
n^2\le T_v(n)<(n+1)^2.
\]

If \(n\) is odd, the lower bound is strict. Therefore, if

\[
\forall m\ge N,\qquad
\bigl(\mathrm{follows}(m,v)\Rightarrow T_v(m)\ge(m+1)^2\bigr),
\]

there is no cycle \(vE\) at any \(n\ge N\).

The unique formally expanding length-4 word ending in `E` is `OOOE`:
\(3^3=27>16=2^4\). Every other length-4 E-terminating word has at most
two odds and is formally contracting. The existing `OOO` threshold
gives \(T_{OOO}(n)\ge(n+1)^2\) for \(n\ge 3\). Hence there is no
length-4 E-terminating cycle for \(n\ge 2\).

This says nothing about cycles ending in `O`. Do not prove that every
cycle itinerary is impossible. Do not attack cycles through `PowerBoundEq`.
Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Last-even cycle cell —
  **EXACT — LEAN VERIFIED**.
- `OOO` suffix threshold —
  **EXACT — LEAN VERIFIED**.
- No `OOE` cycle —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The last-even cell is now a reusable
suffix interface. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     suffix threshold ⇒ no cycle vE; close length 4
Novelty hypothesis      OOE cell argument lifts to a reusable class
Falsifier               an expanding length-4 E-cycle other than OOOE
Existing machinery      cycle_last_even_interval, ooo_suffix_threshold
Maximum Phase-0 scope   generic theorem; OOOE; all length-4 E-words
Promotion criterion     the generic threshold theorem, or length-4 closure
Stop criterion          cycle engine; all cycles impossible; FloorPower rewrite
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- suffix threshold forbids an E-terminating cycle —
  **EXACT — LEAN VERIFIED**
- no `OOOE` cycle for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- no length-4 E-terminating cycle for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- all E-terminating cycles are impossible — not claimed
- cycles ending in `O` are impossible — not claimed
- all cycle itineraries are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_e_term`
- Records: [juggler_cycle_e_term.md](../research/juggler_cycle_e_term.md),
  [juggler_cycle_e_term.json](../research/juggler_cycle_e_term.json)
- Tests: `tests/research/juggler_sequence/test_cycle_e_term.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the suffix-threshold interface or to the length-4 E-terminating
exclusion. The stronger claims that fail:

- “every length-4 E-word needs its own cell analysis” — only `OOOE`
  is expanding; the rest are contracting.
- “cycles ending in `O` are included” — they are not.
- “all cycles are impossible” — not claimed.

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, a small extension. Added:

- `cycle_last_even_cell` / `cycle_last_even_cell_odd`
- `no_cycle_append_even_of_suffix_threshold`
- `no_cycle_itinerary_oooe`
- `no_cycle_itinerary_length_four_ends_even`

`FloorPower`, `Progress`, and `MinimalNonTerm` are not rewritten. No
`sorry`. No halt theorem. No `no_juggler_cycle`. No `CycleSearch`.
No `PowerBoundEq` attack. No `PowerHeight`. No length-5 census.

## Results

Classification **LAST_EVEN_CLASS_GREEN**, with secondary
**E_TERMINATING_LENGTH4_GREEN**.

The reusable condition is a suffix threshold \(T_v(n)\ge(n+1)^2\), not
word length. The unbounded residual branch is untouched. Cycles ending
in `O` remain open.

## Open questions

Answered in [juggler_cycle_e_threshold.md](juggler_cycle_e_threshold.md):
odd-append inheritance lifts `OOO` to `O^a` for \(a\ge 3\), and every
length-5 E-terminating word is excluded.

## Decision

**PROMOTE** the generic last-even suffix theorem and the length-4
E-terminating exclusion. Do not claim that all cycles are impossible.
Do not claim termination. Do not treat cycles ending in `O`.

Best next question: answered in
[juggler_cycle_e_threshold.md](juggler_cycle_e_threshold.md).

## Publication assessment

Status: `EXPLORATORY`. A reusable cell-versus-threshold lemma, not a
paper candidate and not a Juggler totality result.
