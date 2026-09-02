# Juggler cycle-itinerary arithmetic

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can exact last-branch cells and a one-letter rotation exclude the first
nontrivial mixed cycle itineraries `OOE` and `OEO`, without tightening
\(D_w\) and without a cycle engine?

## Exact statement

`CycleItinerary n w` is unchanged: `follows n w`, \(T_w(n)=n\), and \(w\)
nonempty. It does not assume `MinimalNonTerm`.

If the last letter is even, write \(z=T_u(n)\) for \(w=uE\). Then

\[
n^2\le z<(n+1)^2.
\]

This is a square cell, not the identity \(z=n^2\). If \(n\) is odd,
then \(z\neq n^2\) because \(n^2\) is odd.

If `CycleItinerary n (b::w)`, then `CycleItinerary (T(n)) (w++[b])`.

If `CycleItinerary n w` and \(n\ge 2\), some state on the itinerary is a
minimum, and that minimum is odd: an even state \(x\ge 2\) satisfies
\(T(x)<x\).

`OOE` is impossible for \(n\ge 2\): the last-even cell gives
\(T^2(n)<(n+1)^2\), while the existing `OO` suffix threshold gives
\((n+1)^2\le T^2(n)\) for \(n\ge 5\), and \(n=3\) fails the even
letter.

`OEO` is impossible for \(n\ge 2\): one rotation is `EOO`, already
excluded.

Do not prove that every cycle itinerary is impossible. Do not treat last-even
return as \(z=n^2\). Do not attack cycles through `PowerBoundEq`. Do
not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Cycle size bound \(n^{3^o-2^k}\le D_w\) —
  **EXACT — LEAN VERIFIED**.
- `OO` suffix threshold \((q+1)^2\le T^2(q)\) for \(q\ge 5\) —
  **EXACT — LEAN VERIFIED**.
- `EOO` has no cycle for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The first mixed expanding itineraries are
excluded by cells and rotation, not by searching \(D_w\). Totality
remains unclaimed.

## Branch budget

```text
Mathematical target     exclude CycleItinerary on OOE and OEO by exact cells
Novelty hypothesis      last-even cell plus OO threshold, or rotation to EOO
Falsifier               an OOE/OEO cycle; or last-even identity z = n^2
Existing machinery      CycleItinerary, oo_suffix_threshold, no_cycle_itinerary_eoo
Maximum Phase-0 scope   last-even interval; min odd; no OOE; no OEO
Promotion criterion     Lean exclusion of OOE, preferably also OEO
Stop criterion          cycle engine; all cycles impossible; FloorPower rewrite
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- last-even cycle return is the square cell —
  **EXACT — LEAN VERIFIED**
- last-even return is not \(z=n^2\) when \(n\) is odd —
  **EXACT — LEAN VERIFIED**
- cycle minimum is odd —
  **EXACT — LEAN VERIFIED**
- no `OOE` cycle for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- no `OEO` cycle for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- all cycle itineraries are impossible — not claimed
- last-even return is the exact square — **REFUTED**
- cycle return is `PowerBoundEq` — **REFUTED** as an attack
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_arith`
- Records: [juggler_cycle_arith.md](../research/juggler_cycle_arith.md),
  [juggler_cycle_arith.json](../research/juggler_cycle_arith.json)
- Tests: `tests/research/juggler_sequence/test_cycle_arith.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the `OOE`/`OEO` exclusions. The stronger claims that fail:

- “last even letter forces \(z=n^2\)” — the inverse of
  \(T(z)=n\) on an even state is the cell \(n^2\le z<(n+1)^2\). For
  odd \(n\), \(n^2\) is odd, so the pre-final even state cannot be
  that square.
- “cycle return contradicts `PowerBoundEq`” — a cycle still has
  \(\Delta=n^{3^o}-n^{2^k}>0\).
- “\(D_w\) must be improved to exclude `OOE`/`OEO`” — the cells and
  the existing `EOO` theorem close both words.

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, a small extension. Added:

- `cycle_last_even_interval` / `cycle_last_even_ne_odd_sq`
- `cycle_last_odd_interval`
- `cycleItinerary_rotate_cons`
- `floorPower_even_lt` / `exists_cycle_min_odd`
- `no_cycle_itinerary_ooe` / `no_cycle_itinerary_oeo`

`FloorPower`, `Progress`, and `MinimalNonTerm` are not rewritten. No
`sorry`. No halt theorem. No `no_juggler_cycle`. No `CycleSearch`.
No `PowerBoundEq` attack. No `PowerHeight`. Cycle theorems do not
take a `MinimalNonTerm` hypothesis.

## Results

Classification **OOE_CYCLE_EXCLUDED**, with secondary
**OEO_CYCLE_EXCLUDED** and **CYCLE_STRUCTURE_GREEN**.

The bounded mixed length-3 words `EOO`, `OOE`, and `OEO` are all
excluded. The unbounded residual branch is untouched.

## Open questions

Answered in [juggler_cycle_e_term.md](juggler_cycle_e_term.md): a
suffix threshold \(T_v\ge(n+1)^2\) forbids any cycle \(vE\). Every
length-4 E-terminating word is excluded.

## Decision

**PROMOTE** the last-even cell, the odd minimum, and the `OOE`/`OEO`
exclusions. Do not claim that all cycles are impossible. Do not claim
termination. Do not treat last-even return as an exact square.

Best next question: answered in
[juggler_cycle_e_term.md](juggler_cycle_e_term.md).

## Publication assessment

Status: `EXPLORATORY`. A finite-itinerary exclusion lemma, not a paper
candidate and not a Juggler totality result.
