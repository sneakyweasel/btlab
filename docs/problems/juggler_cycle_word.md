# Juggler fixed cycle-itinerary size bounds

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can the existing lower-growth theorem turn exact cycle return
\(T_w(n)=n\) into a finite size bound, and can that bound plus
realization exclude short cycle itineraries?

## Exact statement

`CycleItinerary n w` means `follows n w`, `image n w = n`, and \(w\)
nonempty. Cycle return is not envelope equality: generally
\(n^{2^k}<n^{3^o}\).

If `CycleItinerary n w` and \(n\ge 2\), then \(2^{|w|}<3^{\#O(w)}\) and

\[
n^{3^{\#O(w)}-2^{|w|}}\le D_w,
\]

where \(D_w=\mathrm{lowerDenom}(w)\). Hence the crude bound
\(n\le D_w\).

Formally contracting itineraries cannot be cycle itineraries. The itineraries `O` and
`OO` force \(n\le 4\) and are excluded. `EOO` is excluded by the
existing square-root cell analysis. `OOE` satisfies \(n\le 262144\).

Do not prove that every cycle itinerary is impossible. Do not attack cycles
through `PowerBoundEq`. Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Lower-growth composition \(n^{3^o}\le D_w T_w(n)^{2^k}\) —
  **EXACT — LEAN VERIFIED**.
- Cycle itineraries are formally expanding —
  **EXACT — LEAN VERIFIED**.
- `EOO` cell contraction set \(\{2,12,14\}\) —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. Cycle return becomes a finite
arithmetic problem for each fixed word. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     CycleItinerary ⇒ n^{3^o-2^k} ≤ D_w and an explicit n ≤ B_w
Novelty hypothesis      lower-growth turns cycle return into a finite size bound
Falsifier               a cycle with n > lowerDenom w; or PowerBoundEq as the cycle attack
Existing machinery      lower_growth_word, cycle_strict_envelope, EOO cells
Maximum Phase-0 scope   CycleItinerary; size bound; exclude contracting, O, OO, EOO; bound OOE
Promotion criterion     the exact cycle inequality, or exclusion of a short expanding class
Stop criterion          cycle engine; all cycles impossible; FloorPower rewrite; PowerBoundEq attack
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `CycleItinerary` is formally expanding —
  **EXACT — LEAN VERIFIED**
- \(n^{3^o-2^k}\le D_w\) and \(n\le D_w\) —
  **EXACT — LEAN VERIFIED**
- no `O` or `OO` cycle for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- no `EOO` cycle for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- `OOE` cycle states satisfy \(n\le 262144\); none in that range —
  **COMPUTATIONALLY VERIFIED**
- all cycle itineraries are impossible — not claimed
- cycle return is `PowerBoundEq` — **REFUTED** as an attack
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_itinerary`
- Records: [juggler_cycle_word.md](../research/juggler_cycle_itinerary.md),
  [juggler_cycle_itinerary.json](../research/juggler_cycle_itinerary.json)
- Tests: `tests/research/juggler_sequence/test_cycle_itinerary.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the size inequality. The stronger claims that fail:

- “cycle return contradicts `PowerBoundEq` / forces \(\Delta=0\)” —
  a cycle has \(\Delta=n^{3^o}-n^{2^k}>0\).
- “\(D_w\) is a tight bound for every mixed itinerary” — `OEO` has
  \(D_w=67108864\), and `EOO` has \(D_w=274877906944\). The `EOO`
  exclusion uses cells, not that bound.

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, above `ResidualPath`. Added:

- `CycleItinerary`
- `cycle_itinerary_formally_expanding` / `cycle_itinerary_not_contracting`
- `cycle_lower_growth` / `cycle_pow_le_lowerDenom` / `cycle_le_lowerDenom`
- `no_cycle_itinerary_odd` / `no_cycle_itinerary_oo` / `no_cycle_itinerary_eoo`
- `cycle_ooe_le_lowerDenom`

`FloorPower` is not rewritten. No `sorry`. No halt theorem. No
`no_juggler_cycle`. No `CycleSearch`. No `PowerBoundEq` attack. No
`PowerHeight`.

## Results

Classification **CYCLE_BOUND_GREEN**, with secondary
**CYCLE_WORD_EXCLUDED** for contracting itineraries, `O`, `OO`, and `EOO`.

Each fixed cycle itinerary is now a finite arithmetic problem. The crude
bound is \(B_w=D_w\). Short expanding itineraries with large exponent gap
collapse to \(n\le 4\). `EOO` is excluded independently of \(D_w\).

## Open questions

Answered in [juggler_cycle_arith.md](juggler_cycle_arith.md): last-even
return is a square cell, not \(z=n^2\). `OOE` and `OEO` are excluded
without improving \(D_w\).

## Decision

**PROMOTE** the cycle size inequality and the short-word exclusions.
Do not claim that all cycles are impossible. Do not claim termination.
Do not treat cycle return as envelope equality.

Best next question: answered in
[juggler_cycle_arith.md](juggler_cycle_arith.md).

## Publication assessment

Status: `EXPLORATORY`. A finite-reduction lemma, not a paper
candidate and not a Juggler totality result.
