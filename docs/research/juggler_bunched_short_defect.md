# Juggler exact short-cluster closure via defect

Status: **SHORT_DEFECT_PARK**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Exact short-tail return as a
defect identity; not Z5, not a length-11 assembler, and not a
preimage enumerator.

## Branch budget

```text
Mathematical target     Exact T_{O^b E O^c E}(y)=n forces a
                        defect equation CycleMin y cannot meet
Novelty hypothesis      local closure defects have impossible
                        size, parity, or signature
Existing machinery      localDefectEven/Odd; cycle_last_even
                        ne_odd_sq; odd_remainder_even
Maximum Phase-0 scope   c=0/c=1 identities; last-odd defect
                        scan; EE signatures; no Lean
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **SHORT_DEFECT_PARK**
- sorry-free: `True`
- tiny-gap possible for odd n: `False`
- EE signatures unrestricted: `True`
- required defect ordinary: `True`
- parity mismatch: `False`
- leftover-cell rewrite: `True`
- last-odd hits (odd n<49): `15`
- last-odd all delta odd: `True`
- last-odd tiny n^4 hits: `0`
- EE n=13 count / 8-adic pairs: `2366` / `16`
- EE n=15 count / 8-adic pairs: `3600` / `16`

exact EE closure is y = n^4 + 2 eps n^2 + eps^2 + eta with ordinary unrestricted signatures; the c=1 last-odd defect is the same natural window 0 < delta <= 2q and is odd onto an even landing; the tiny-gap equation z^3 = n^4 + delta is impossible for odd n (gap at least 2n^2+1); the composed 1+Q is the leftover EE cell in defect coordinates.

## Identities

- c=0 EE: y = (n^2 + eps)^2 + eta = n^4 + 2 eps n^2 + eps^2 + eta, eps = localDefectEven(t), eta = localDefectEven(y), t even in [n^2, (n+1)^2)
- c=1 last odd: z^3 = t^2 + delta = n^4 + 2 eps n^2 + eps^2 + delta, t = n^2 + eps even, delta = localDefectOdd(z)
- c=0 parameterized by b: after b odd steps, w even in the EE fibre of n and y^{3^b} = w^{2^b} + composed odd defects
- 1+Q: `1 + Q = y / n^4 = (1 + eps/n^2)^2 + eta/n^4`
- minimal gap t^2-n^4 for odd n: `2 n^2 + 1` (n=13 gives `339`)

## Last-odd defect scan

- n with a hit: `13`
- delta mod 8: `{'1': 1, '3': 7, '5': 4, '7': 3}`
- max delta/q: `1.7223310479921645`

- n=`13` eps=`3` z=`31` delta=`207` gap=`1023`
- n=`17` eps=`33` z=`47` delta=`139` gap=`20163`
- n=`19` eps=`3` z=`51` delta=`155` gap=`2175`
- n=`21` eps=`35` z=`61` delta=`405` gap=`32095`
- n=`23` eps=`19` z=`67` delta=`459` gap=`20463`
- n=`27` eps=`27` z=`83` delta=`251` gap=`40095`
- n=`29` eps=`27` z=`91` delta=`147` gap=`46143`
- n=`29` eps=`55` z=`93` delta=`1541` gap=`95535`

## Lean

- `localDefectEven_add`: `True`
- `localDefectOdd_add`: `True`
- `localDefectEven_lt_succ`: `True`
- `localDefectOdd_lt_succ`: `True`
- `cycle_last_even_ne_odd_sq`: `True`
- `odd_remainder_even`: `True`
- `odd_preimage_unique`: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- length_eleven_census: `False`
- z5_cells: `False`
- four_even_assembler: `False`

## Decision

**SHORT_DEFECT_PARK**

exact EE closure is y = n^4 + 2 eps n^2 + eps^2 + eta with ordinary unrestricted signatures; the c=1 last-odd defect is the same natural window 0 < delta <= 2q and is odd onto an even landing; the tiny-gap equation z^3 = n^4 + delta is impossible for odd n (gap at least 2n^2+1); the composed 1+Q is the leftover EE cell in defect coordinates.

This is not a halt result, not a Z5 exclusion, and not a
length-11 assembler.

