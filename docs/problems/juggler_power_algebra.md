# Juggler finite-itinerary power algebra and equality rigidity

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Does global envelope equality for a realized finite parity itinerary force
every local branch inequality to be tight, and is each local tightness
equivalent to the branch input being a perfect square?

## Exact statement

The weak envelope is already a theorem: every realized finite parity
word \(w\) satisfies

\[
T_w(n)^{2^{|w|}}\le n^{3^{\#O(w)}}.
\]

The questions of this phase are:

1. For even \(n\), is \(T(n)^2=n\) equivalent to \(n\) being a square?
2. For odd \(n\), is \(T(n)^2=n^3\) equivalent to \(n\) being a square?
3. If the composite envelope is an equality, must every local branch
   inequality in the realizing chain be an equality?
4. Therefore, does global equality force every relevant itinerary state
   (every branch input) to be a perfect square?

Mixed-word strictness is not in scope: it is already **REFUTED**.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Phase-13 (`juggler_power_itineraries`): two-sided exponent law **REFUTED**.
- Phase-14 (`juggler_power_composition`): one-sided envelope
  **EXACT — LEAN VERIFIED** as `power_bound_follows`.
- Phase-15 (`juggler_equality_rigidity`): mixed-word strictness
  **REFUTED** at word `O`, \(n=9\). Odd squares attain the one-step
  envelope. **extended** here by asking for the local characterization
  and for equality propagation.

## Branch budget

```text
Mathematical target     Does global envelope equality for a realized finite itinerary
                        force every local branch inequality to be tight, and is
                        each local tightness equivalent to the branch input
                        being a perfect square?
Novelty hypothesis      Equality is a rigid chain of exact local square
                        conditions, not mixed-word strictness (already REFUTED).
Falsifier               LOCAL_SQUARE_EQ_FALSE (tight local bound, non-square
                        input) or GLOBAL_EQ_PROPAGATION_FALSE (global equality
                        with a strict local step).
Existing machinery      PowerBound, power_bound_follows / power_bound_contracts,
                        floorPower_odd_sq_eq_cube_of_sq, Nat.sqrt, integer-root
                        powers_equal in equality_rigidity.py.
Maximum Phase-0 scope   Local iff-square theorems; equality-propagation theorem;
                        square-state corollary; square/root computational probe;
                        thin power_bound_word alias. No PowerHeight, no block
                        algebra, no engine edits, no huge cmp_pow.
Promotion criterion     Lean proves the three rigidity implications, and the
                        probe finds neither falsifier.
Stop criterion          Either falsifier; a PowerBound certificate datatype;
                        an equality-classifier tactic; a complete equality-word
                        census; a termination claim.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Weak envelope \(T_w(n)^{2^k}\le n^{3^o}\) —
  **EXACT — LEAN VERIFIED** (prior phase)
- Local even equality \(T(n)^2=n\) iff square —
  **EXACT — LEAN VERIFIED**
- Local odd equality \(T(n)^2=n^3\) iff square —
  **EXACT — LEAN VERIFIED**
- Global envelope equality implies every local branch is tight —
  **EXACT — LEAN VERIFIED**
- Global equality implies every relevant state is a square —
  **EXACT — LEAN VERIFIED**
- Mixed-word strictness — **REFUTED** (prior phase)
- `PowerHeight` / equality-itinerary census — not added

## Experiments

- Probe: `research.juggler_sequence.power_algebra`
- Reuses itinerary helpers from `research.juggler_sequence.power_itineraries`
  and tiny integer-root sanity checks from
  `research.juggler_sequence.equality_rigidity` (`powers_equal`)
- Search compares local tightness and `isqrt` squares; it does not
  construct \(n^{3^o}\) via `cmp_pow`
- Itinerary layer: \(1\le n\le 10^4\), depth \(8\)
- Local iff-square layer: \(1\le n\le 10^6\) (0 mismatches)
- Records: [juggler_power_algebra.md](../research/juggler_power_algebra.md),
  [juggler_power_algebra.json](../research/juggler_power_algebra.json)
- Tests: `tests/research/juggler_sequence/test_power_algebra.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened. The rigidity chain is a theorem, not a conjecture. A
complete classification of all-odd equality families remains out of
scope.

## Counterexamples

- Mixed-word strictness remains refuted at word `O`, \(n=9\).
- No `LOCAL_SQUARE_EQ_FALSE` witness.
- No `GLOBAL_EQ_PROPAGATION_FALSE` witness.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `power_bound_word`
- `floorPower_even_sq_eq_iff_square`
- `floorPower_odd_sq_eq_cube_iff_square`
- `PowerBoundEq`
- `power_bound_eq_of_append_even`
- `power_bound_eq_of_append_odd`
- `power_bound_eq_implies_local_eq`
- `power_bound_eq_implies_square`

Existing `PowerBound`, `power_bound_follows`, and
`power_bound_contracts` are unchanged. No `mixed_word_power_lt`.
No `PowerBoundStrict`. No `sorry`. No ledger row (elementary floor
arithmetic, same policy as the prior FloorPower lemmas).

## Results

Classification **EQUALITY_RIGIDITY_GREEN**.

Local branch equality is equivalent to the input being a perfect
square (`floorPower_even_sq_eq_iff_square`,
`floorPower_odd_sq_eq_cube_iff_square`). Global envelope equality
forces every local inequality in the realizing chain to be tight
(`power_bound_eq_implies_local_eq`), and therefore every relevant
itinerary state to be a square (`power_bound_eq_implies_square`).
The examples \(9\xrightarrow{O}27\) and \(16\to 4\to 2\) are instances
of that chain. Contraction from the exponent gap \(3^o<2^k\) is
unchanged.

Computational search found 0 `LOCAL_SQUARE_EQ_FALSE` and 0
`GLOBAL_EQ_PROPAGATION_FALSE` witnesses. Predicted equalities on
\(n\le 10^4\), depth \(8\): 118, of which 62 contain `O` and 0 contain
both letters. Both-letter vanishing is **OBSERVATION**, not a
classification of equality words.

This is not a termination theorem.

## Open questions

How do \(O\) and \(E\) act on successive perfect powers (the descending
\(s^2\mapsto s^3\) / \(s^2\mapsto s\) dynamics)? Do not census equality
words in this phase.

## Decision

**PROMOTE** the local square characterization and the equality-propagation
rigidity chain. Record the classification `EQUALITY_RIGIDITY_GREEN`.
Do not register an attack. Do not claim termination. Do not classify
all equality trajectories.

Best next question: how do `O` and `E` act on successive perfect
powers?

## Publication assessment

Status: `EXPLORATORY`. A local exact rigidity lemma, not a paper
candidate and not a Juggler totality result.
