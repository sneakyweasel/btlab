# Reverse-add two-step composition Phase-4 falsifier

Status: **PHASE_4_REVERSE_ADD_COMPOSITION_FALSIFIER**

This is not a reverse-and-add solver, not a termination attack, and not a
general composition engine. It tests whether k=2 exposes an exact reverse
relation that one-step ranking and reverse_gap could not see.

## Branch budget

```text
Mathematical target     Does T^2(x)=x+W(x)+W(T(x)) have an exact structural
                        relation invisible at one step?
Novelty hypothesis      Two reverse terms cancel, preserve sign, or add at
                        most one trit — the Juggler method on a different map.
Falsifier               An exact two-step sample violating each candidate, or
                        a survivor that is only a finite-table restatement.
Existing machinery      ReverseAddSpec, bt_reverse, encode, bt_length, WINDOW,
                        seed-196 orbit, Problems.Engine.ReverseAdd.
Maximum Phase-4 scope   k=2; three pre-ranked candidates; frozen window+orbit.
Promotion criterion     Exact reverse identity, natural domain, Lean path.
Stop criterion          k>2, palindrome engine, coefficient search, census growth.
```

## Metadata

- engine_control_version: `0.2.7`
- source_engine: `v2.3`
- experimental_status: `PHASE_4_REVERSE_ADD_COMPOSITION_FALSIFIER`
- target: `reverse_and_add_base3`
- composition depth: 2
- classification: **REVERSE_COMPOSITION_NEEDS_RICHER_STRUCTURE**
- lean: `NOT_YET_FORMALIZATION_READY`
- green loot: `NO_NEW_LOOT`
- decision reason: algebraic cancellation and sign preservation fail; the +1 length bound is only a bounded observation and does not explain the reverse interaction

Candidate list frozen at three. reverse_gap is not reopened.
`DEFAULT_ATTACK_ORDER` is unchanged. No production reverse-add attack.

## Candidate 1: `reverse_cancellation` (failed)

- Statement: W(x) + W(T(x)) = 0 whenever T and T^2 are defined
- Motivation: T^2(x) = x + W(x) + W(T(x)). The only simple algebraic simplification is cancellation of the two reverse terms, which would give T^2(x) = x.
- Domain: integers with a defined two-step reverse-plus-add successor
- Expected yield: an exact two-step identity T^2 = id, the reverse analog of Juggler T^2 < n
- Cheapest falsifier: the first frozen-window seed with W(x) + W(T(x)) != 0
- Checked: 1

- Counterexample: `1 -> 2 -> 0` (W=1, W(T)=-2)
- Failure class: `CANCELLATION_FAILURE`
- Mechanism: The second reverse does not cancel the first: W(1)=1 and W(2)=-2, so W(x)+W(T(x))=-1 and T^2(1)=0 != 1.

## Candidate 2: `two_step_sign_preservation` (failed)

- Statement: sign(T^2(x)) = sign(x) for x != 0 with T^2 defined
- Motivation: If two-step reverse-plus-add were a size-simplifying composition, it should at least preserve sign. This is the weakest exact Class-A relation that is not a reopened ranking template.
- Domain: nonzero integers with a defined two-step successor
- Expected yield: a sign law explaining two-step collapse versus growth
- Cheapest falsifier: the smallest nonzero frozen seed whose two-step image has a different sign
- Checked: 1

- Counterexample: `1 -> 2 -> 0` (W=1, W(T)=-2)
- Failure class: `SIGN_REVERSAL`
- Mechanism: Two-step reverse-plus-add changes sign: 1 -> 2 -> 0 has sign 1 -> 0.

## Candidate 3: `two_step_length_plus_one` (survived)

- Statement: bt_length(T^2(x)) <= bt_length(x) + 1 whenever T^2 is defined
- Motivation: Reverse-plus-add is a digit-wise sum of a word and its reverse, so one step can create at most one extra trit. The strongest two-step length law that is not the trivial iterated bound +2 is that two steps still create at most one trit.
- Domain: integers with a defined two-step successor
- Expected yield: an exact length obstruction from reverse-add carry
- Cheapest falsifier: the first frozen seed whose two-step canonical length grows by 2 or more
- Checked: 49

## Transition window

- Frozen discovery window: range(1, 41)
- Packet orbit seed: 196
- Two-step samples: 49

## Decision

**REVERSE_COMPOSITION_NEEDS_RICHER_STRUCTURE**

algebraic cancellation and sign preservation fail; the +1 length bound is only a bounded observation and does not explain the reverse interaction.

Green loot: `NO_NEW_LOOT`. Lean: `NOT_YET_FORMALIZATION_READY`.
Not a halt theorem. Not a production attack.

## Best next question

Is the missing reverse-add coordinate the balanced-ternary carry of `x+W(x)`, and should that be a separate Phase-5 falsifier rather than a composition engine?
