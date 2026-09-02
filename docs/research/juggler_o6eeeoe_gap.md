# Juggler O^6 EEEOE +1-chain gap

Status: **O6EEEOE_GAP_PROVED**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. If n follows O^6, then T^6(n)
lies at or above the EEEOE inverse cell of n, so
OOOOOOEEEOE is not a cycle word.

## Branch budget

```text
Mathematical target     Does the O^7 +1-chain kill the unique
                        (3,1) leftover OOOOOOEEEOE?
Novelty hypothesis      T^6 sits above the EEEOE cell at the
                        first O^6 start, not at leftover N0
Falsifier               an O^6 image inside the EEEOE cell, or
                        the chain still needs n ~ 10^8
Existing machinery      (T+1)^2 > x^3; cycle_trailing_evens;
                        O^7 +1-chain; 30-word list
Maximum Phase-0 scope   one word OOOOOOEEEOE; CycleMin
                        Lean corollary; no (1,3) family,
                        no 29-word scan
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **O6EEEOE_GAP_PROVED**
- word: `OOOOOOEEEOE`
- first O^6: `163`
- leftover N0: `437599552`

no O^6 below 163; +1-chain gives T^6(n) >= (v_max+1)^8 for n>=25, with (v_max+1)^8 < (n+1)^11 and n^1995 > (n+1)^1970; pin n<10000 has 170 O^6 starts, zero cell hits, min ratio 37.3179317038586 at n=163; leftover N0=437599552.

## Arithmetic

- step exponents: `[486, 324, 216, 144, 96, 64]`
- plus exponent: `1266`
- comparison n^1995 > (n+1)^1970
- EEEOE cell exponent: `11`
- elementary checks: `{'exponents_match': True, 'plus_exp': True, 'left_exp': True, 'right_exp': True, 'vmax_163': True, 'cell_163': True, 'succ11_from_25': True, 'vmax_from_16': True, 'split_1970': True, 'pow163_beats_e_bound': True}`

## Pin

- n<10000: first_o6=`163` o6=`170` above=`170` misses=`[]` follows_eeeoe=`5` min_ratio=`37.3179317038586` at n=`163`

## Proof

Write x_0 = n and x_{k+1} = floor(x_k^{3/2}) along an O^6
run. The exact odd cell is x_k^3 < (x_{k+1}+1)^2, and
x_k >= n. Raising n^3 < (x_1+1)^2 to 3^5 and crossing
n(x+1) <= (n+1)x through five more odds produces

    n^{1995} < (n+1)^{1266} (T^6(n)+1)^{64}.

The EEEOE inverse of n is z < (v+1)^8 with T(v) even in
[n^2, (n+1)^2), hence v^3 < (n+1)^4. For n >= 16 one has
(v_max+1)^8 < (n+1)^{11} (at n=163: 898^8 < 164^{11}).
For n >= 25 one has n^{1995} > (n+1)^{1970}, because
1970 = 12*163+14 and (1+1/163)^{1970} < 3^{13} < 163^{25}.
Therefore T^6(n)+1 > (n+1)^{11} >= (v_max+1)^8.

No n < 163 follows O^6 (pin). The leftover prefix-cell for
this shape first fires at 437599552 and is not used.

This is not a length-11 census. The five (1,3) words are a
separate job.

## Lean

- `cycle_trailing_evens_lt`: `True`
- `odd_preimage_unique`: `True`
- `o7_image_ge_succ_pow16`: `True`
- `no_cycle_itinerary_oooooooeeee`: `True`
- `no_cycleMin_ooooooeeeoe`: `True`
- `no_cycle_itinerary_ooooooeeeoe`: `True`
- no `no_cycle_itinerary_length_eleven`: `True`
- no `no_cycle_itinerary_four_even`: `True`
- no `juggler_reaches_one`: `True`
- O^6 EEEOE theorem: `True`
- Paper A has no O^6 EEEOE: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycle_impossible: `False`
- length_eleven_census: `False`
- four_even_impossible: `False`
- twenty_nine_word_scan: `False`

## Decision

**O6EEEOE_GAP_PROVED**

no O^6 below 163; +1-chain gives T^6(n) >= (v_max+1)^8 for n>=25, with (v_max+1)^8 < (n+1)^11 and n^1995 > (n+1)^1970; pin n<10000 has 170 O^6 starts, zero cell hits, min ratio 37.3179317038586 at n=163; leftover N0=437599552.

This is not a halt result and not a length-11 census.

