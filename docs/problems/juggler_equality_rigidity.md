# Juggler mixed-word floor-power equality

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Does every odd step make the composed one-sided envelope strict for
\(n\ge 2\), so that a realized mixed itinerary cannot attain equality?

## Exact statement

The weak bound is already a theorem: every realized finite parity itinerary
\(w\) satisfies

\[
T_w(n)^{2^{|w|}}\le n^{3^{\#O(w)}}.
\]

The working hypothesis of this phase was the strict strengthening

\[
n\ge 2,\quad w\text{ contains }O
\qquad\Longrightarrow\qquad
T_w(n)^{2^{|w|}}<n^{3^{\#O(w)}}.
\]

Separately: is the one-step odd inequality \(T(n)^2<n^3\) always strict
for odd \(n\ge 3\)? That would hold if \(n^{3/2}\) were never an integer.

These strictness claims are independent of the contraction criterion
\(3^o<2^k\).

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Phase-13 (`juggler_power_itineraries`): two-sided exponent law **REFUTED**.
- Phase-14 (`juggler_power_composition`): one-sided envelope
  **EXACT — LEAN VERIFIED** as `power_bound_follows`. Mixed-word
  equality was left open.

## Branch budget

```text
Mathematical target     Does every odd step make the composed bound
                        strict for n>=2, forbidding mixed-word equality?
Novelty hypothesis      Mixed-word equality does not occur for n>=2.
Falsifier               A realized mixed itinerary with T_w(n)^{2^k} = n^{3^o}.
Existing machinery      power_itineraries cmp_pow; PowerBound composition.
Maximum Phase-0 scope   Mixed-equality search; one-step odd analysis;
                        stop strictness API if a witness appears.
Promotion criterion     A minimized mixed-equality witness, or a Lean
                        mixed-strictness theorem if none exists.
Stop criterion          MIXED_EQUALITY_FOUND: stop mixed_word_power_lt;
                        a general equality classifier; a frequency theorem.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Weak envelope \(T_w(n)^{2^k}\le n^{3^o}\) —
  **EXACT — LEAN VERIFIED** (prior phase)
- Universal mixed-word strictness for \(n\ge 2\) — **REFUTED**
- One-step odd strictness \(T(n)^2<n^3\) for all odd \(n\ge 3\) —
  **REFUTED**
- Odd squares attain the one-step envelope —
  **EXACT — LEAN VERIFIED** (`floorPower_odd_sq_eq_cube_of_sq`)
- Smallest witness, word `O` at \(n=9\) —
  **EXACT — LEAN VERIFIED** (`floorPower_nine_odd_eq`)
- Both-letter equality on the searched domain — **OBSERVATION**
  (none found)
- `mixed_word_power_lt` / `PowerBoundStrict` — not added

## Experiments

- Probe: `research.juggler_sequence.equality_rigidity`
- Reuses `research.juggler_sequence.power_itineraries` (`cmp_pow`, itinerary)
- Deep layer: all \(n\le 10^4\), depth \(12\), itinerary bit cap \(1024\)
  (54 mixed equalities)
- Wide layer: all \(n\le 10^6\), depth \(8\) (516 mixed equalities)
- Odd squares through \(10^8\) (4999 one-step equalities); odd high
  even powers \(b^{2^j}\); perfect powers through \(10^9\)
- Merged unique \((n,w)\): 15996 mixed equalities, all all-odd; 0
  both-letter; 0 near-critical; 0 alternating
- Records: [juggler_equality_rigidity.md](../research/juggler_equality_rigidity.md),
  [juggler_equality_rigidity.json](../research/juggler_equality_rigidity.json)
- Tests: `tests/research/juggler_sequence/test_equality_rigidity.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened. The mixed-strictness hypothesis is refuted, not conjectural.

## Counterexamples

- Mixed-word equality: word `O`, \(n=9\), \(T(9)=27\),
  \(27^2=9^3=729\). Smallest witness for \(n\ge 2\). **REFUTED**.
- Two-step all-odd equality: word `OO`, \(n=81=3^4\).
- Mechanism: if \(n=m^2\) with \(m\) odd, then \(n^{3/2}=m^3\) is an
  integer, so the odd floor is tight. All-odd tight chains continue on
  odd high even powers \(b^{2^j}\).
- Registry: `conjectures/refuted/juggler_mixed_word_strictness.json`.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `floorPower_odd_sq_eq_cube_of_sq`
- `floorPower_nine_odd_eq`

Existing `power_bound_follows` and `power_bound_contracts` are
unchanged. No `mixed_word_power_lt`. No `floorPower_odd_sq_lt_cube`.
No `PowerBoundStrict`. No `sorry`. No ledger row (elementary floor
arithmetic, same policy as the prior FloorPower lemmas).

## Results

Classification **MIXED_EQUALITY_FOUND**.

The local odd inequality is not universally strict. Odd perfect squares
attain \(T(n)^2=n^3\). On odd \(n\le 10^6\), this one-step equality holds
if and only if \(n\) is a square (**COMPUTATIONALLY VERIFIED**, 0
mismatches). Therefore a single odd letter can be an equality case, and
mixed-word equality occurs.

Merged search: 15996 mixed equalities, all all-odd itineraries. No equality
containing both `O` and `E` was found. A tight odd step from an odd
square has odd image, so `E` cannot follow immediately. That is
**OBSERVATION**, not a theorem of this phase.

The weak envelope and the exponent-gap contraction corollary remain.

This is not a termination theorem.

## Open questions

Is equality for an itinerary that contains `E` impossible for \(n\ge 2\)? Is
all-odd equality exactly the odd \(b^{2^j}\) family?

## Decision

**PROMOTE** the mixed-equality witness and the odd-square mechanism.
Record the classification `MIXED_EQUALITY_FOUND`. Stop the mixed-word
strictness generalization. Do not add `mixed_word_power_lt`. Do not
register an attack. Do not claim termination.

Best next question: is equality for words containing `E` impossible for
\(n\ge 2\), and is all-odd equality exactly the odd \(b^{2^j}\) family?

## Publication assessment

Status: `EXPLORATORY`. A local equality witness and a one-step floor
identity, not a paper candidate and not a Juggler totality result.
