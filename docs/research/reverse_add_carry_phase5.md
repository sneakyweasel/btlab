# Reverse-add balanced-ternary carry Phase-5 falsifier

Status: **PHASE_5_REVERSE_ADD_CARRY_FALSIFIER**

This is not a reverse-and-add solver, not a ranking synthesizer, and not a
composition engine. It tests whether the existing addition trace of
`T(x)=x+W(x)` exposes a one-dimensional carry coordinate that magnitude,
length, parity, reverse-gap, and two-step composition could not see.

## Branch budget

```text
Mathematical target     Does carry in x+W(x) have an exact structural signal
                        invisible to magnitude, bt_length, reverse_gap, and T^2?
Novelty hypothesis      Carry-chain length of the canonical addition is the
                        missing one-step coordinate of representation change.
Falsifier               An exact one-step sample violating each candidate, or
                        a survivor that is only the definition of carry.
Existing machinery      ReverseAddSpec, encode, bt_reverse, bt_length,
                        add_with_trace, WINDOW, seed-196 orbit, ReverseAdd.
Maximum Phase-5 scope   k=1; statistic A; three pre-ranked candidates;
                        frozen window+orbit.
Promotion criterion     Exact nontrivial carry law, not definitional, Lean path.
Stop criterion          new arithmetic engine, k>1, census growth, ranking,
                        digit-language framework.
```

## Metadata

- engine_control_version: `0.2.7`
- source_engine: `v2.3`
- experimental_status: `PHASE_5_REVERSE_ADD_CARRY_FALSIFIER`
- target: `reverse_and_add_base3`
- composition depth: 1
- classification: **CARRY_NEEDS_RICHER_STATE**
- lean: `FORMALIZATION_BLOCKED`
- green loot: `NO_NEW_LOOT`
- decision reason: carry is related to the addition but a one-dimensional chain length does not determine the successor length delta

Candidate list frozen at three. reverse_gap is not reopened.
`DEFAULT_ATTACK_ORDER` is unchanged. No production carry attack.
The Phase-4 two-step length bound is not proved here.

## Carry definition

- Statistic: `carry_chain_length`
- Source: `bt.normalization.add_with_trace`
- Formula: C(x) is the longest run of consecutive LSD-first positions affected by nonzero carry while adding the canonical words for x and W(x).

## Canonicalization

- Digit index: LSD-first: index i is the coefficient of 3^i, matching add_with_trace
- Leading zeros: encode and from_digits_lsd strip canonical leading zeros
- Carry values: rewrite_sum produces carry in {-1, 0, +1}
- Negatives: encode is sign-aware; C is computed on encode(x) and encode(W(x))
- Carry into a new MSD counts: `True`
- Cancellation: A position is affected iff carry_in != 0 or carry_out != 0. Opposite-trit cancellation with carry_in = carry_out = 0 is not a carry event. A nonzero final_carry creates an extra MSD position that counts.

## Candidate 1: `carry_bounds_length_growth` (survived)

- Statement: C(x) >= max(0, bt_length(T(x)) - bt_length(x)) for the one-step addition T(x)=x+W(x)
- Motivation: A canonical word sum grows in length only when carry reaches a new MSD. Carry-chain length is therefore a lower bound on length growth.
- Domain: integers with a defined one-step reverse-plus-add successor
- Expected yield: an exact carry-to-length obstruction from the addition mechanism
- Cheapest falsifier: the first frozen seed whose canonical length grows by more than C(x)
- Checked: 49

## Candidate 2: `zero_carry_preserves_length` (failed)

- Statement: C(x)=0 implies bt_length(T(x))=bt_length(x) for the one-step addition T(x)=x+W(x)
- Motivation: If no position is affected by carry, the digitwise sum never rewrites. The only remaining length change would be leading-digit cancellation, so zero carry should preserve canonical length exactly.
- Domain: integers with C(x)=0 and a defined one-step successor
- Expected yield: an exact zero-carry simplification of the reverse-plus-add word
- Cheapest falsifier: the first frozen seed with C(x)=0 whose canonical length changes
- Checked: 1

- Counterexample: `2 -> 0` (C=0, W=-2, length 2->1)
- Failure class: `REVERSAL_DEPENDENCE`
- Mechanism: Zero carry still changes canonical length: C(2)=0, W(2)=-2, 2->0, bt_length 2->1. Opposite-trit cancellation from reverse-as-negation collapses the word without carry.

## Candidate 3: `positive_carry_forces_length_plus_one` (failed)

- Statement: C(x)>0 implies bt_length(T(x))-bt_length(x)=1 for the one-step addition T(x)=x+W(x)
- Motivation: If carry were the hidden coordinate of representation change, a nonzero chain would force the only nontrivial one-step length delta available to a word sum: growth by exactly one trit.
- Domain: integers with C(x)>0 and a defined one-step successor
- Expected yield: a one-dimensional carry law determining successor length
- Cheapest falsifier: the first frozen seed with C(x)>0 whose length delta is not +1
- Checked: 3

- Counterexample: `5 -> -6` (C=2, W=-11, length 3->3)
- Failure class: `LENGTH_DECOUPLING`
- Mechanism: Positive carry does not force +1 length: C(5)=2, 5->-6 has bt_length 3->3 (delta 0).

## Special probes

- `positive palindrome`: x=1 -> T=2, W=1, C=2, length 1->2
- `packet seed`: x=196 -> T=392, W=196, C=7, length 6->7
- `W(x)<0`: x=2 -> T=0, W=-2, C=0, length 2->1
- `successor 0`: x=8 -> T=0, W=-8, C=0, length 3->1

## Transition window

- Frozen discovery window: range(1, 41)
- Packet orbit seed: 196
- One-step samples: 49

## Decision

**CARRY_NEEDS_RICHER_STATE**

carry is related to the addition but a one-dimensional chain length does not determine the successor length delta.

Green loot: `NO_NEW_LOOT`. Lean: `FORMALIZATION_BLOCKED`.
Not a halt theorem. Not a production attack.

## Best next question

If carry is not a sufficient one-dimensional coordinate, what exact word-level interaction of `x` and `W(x)` should be named instead?
