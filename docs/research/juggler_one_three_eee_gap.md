# Juggler (1,3) EEE +1-chain gap

Status: **ONE_THREE_EEE_GAP_PROVED**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. The five first-expanding (1,3)
leftovers are O^a E O^{7-a} EEE. Each prefix image sits at or
above the EEE inverse cell of n, so none is a cycle word.

## Branch budget

```text
Mathematical target     Do all five (1,3) leftovers die by
                        prefix image versus (n+1)^8?
Novelty hypothesis      the same exact +1-chain that killed
                        O^7 EEEE / O^6 EEEOE, now mixed
                        through one internal E, fires at
                        the first prefix start, not leftover N0
Falsifier               a prefix image inside the EEE cell,
                        or the chain only at leftover-scale N0
Existing machinery      O^6 / O^7 +1-chain; cycle_trailing_evens
                        r=3; leftover Z4 PARK
Maximum Phase-0 scope   five named (1,3) words; CycleMin
                        Lean; no (2,2) family, no 23-word scan
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **ONE_THREE_EEE_GAP_PROVED**
- words: `['OOOOOOEOEEE', 'OOOOOEOOEEE', 'OOOOEOOOEEE', 'OOOEOOOOEEE', 'OOEOOOOOEEE']`
- family slack: `3^7 - 2^11 = 139`

five (1,3) words O^a E O^{7-a} EEE; family identity 3^7=2187 > 2^{11}=2048 with slack 139; exact mixed +1-chain n^2187 < (n+1)^2048 (1+1/v)^E contradicts the leading-chain lower bound on v at each first prefix start; leftover N0 unused (1.57e9 to 3.75e12); pin n<10000 empty, closest ratio 5.728451053262999 at n=37 on OOOOEOOOEEE.

## Arithmetic

- surplus `3^7 = 2187` versus cell bits `2^11 = 2048`
- elementary checks: `{'three7_gt_two11': True, 'slack139': True, 'five_words': True, 'a0_plus_a1': True, 'words_are_eee': True, 'o6_left': True, 'o2_left': True, 'fudge_61': True, 'fudge_25': True, 'o6_coroll_k': True, 'isqrt164': True, 'first_starts': True, 'leftover_n0': True, 'lead_6_1': True, 'master_6_1': True, 'no_leftover_at_first_6_1': True, 'lead_5_2': True, 'master_5_2': True, 'no_leftover_at_first_5_2': True, 'lead_4_3': True, 'master_4_3': True, 'no_leftover_at_first_4_3': True, 'lead_3_4': True, 'master_3_4': True, 'no_leftover_at_first_3_4': True, 'lead_2_5': True, 'master_2_5': True, 'no_leftover_at_first_2_5': True}`

## Pin

- `OOOOOOEOEEE` n<10000: first=`163` count=`46` above=`46` misses=`[]` min_ratio=`15.130225814131308` at n=`163` leftover_N0=`1568526333` v_lb=`1000000000000` fudge=`384`
- `OOOOOEOOEEE` n<10000: first=`241` count=`48` above=`48` misses=`[]` min_ratio=`19.000075520853635` at n=`241` leftover_N0=`4086043903` v_lb=`1000000000` fudge=`960`
- `OOOOEOOOEEE` n<10000: first=`37` count=`47` above=`47` misses=`[]` min_ratio=`5.728451053262999` at n=`37` leftover_N0=`17179869199` v_lb=`8000` fudge=`1824`
- `OOOEOOOOEEE` n<10000: first=`113` count=`32` above=`32` misses=`[]` min_ratio=`12.105543869132132` at n=`113` leftover_N0=`148113652199` v_lb=`2000` fudge=`3120`
- `OOEOOOOOEEE` n<10000: first=`173` count=`36` above=`36` misses=`[]` min_ratio=`15.50139821584979` at n=`173` leftover_N0=`3749366963330` v_lb=`200` fudge=`5064`

## Proof

A cycle word O^a E O^{7-a} EEE is the prefix image z in
[n^8, (n+1)^8) by cycle_trailing_evens r=3. Write
u = T^a(n) and v = isqrt(u), and assume z < (n+1)^8.

On the leading O^a run the exact cells x_k^3 < (x_{k+1}+1)^2
with x_k >= n compose to

    n^{3^{a+1}-3·2^a} < (n+1)^{2·3^a-3·2^a} (u+1)^{2^a}.

The even step is u < (v+1)^2, so u+1 <= (v+1)^2. On the
suffix O^{7-a} from v one has x_k >= v and the same
+1-chain, hence

    v^{L'} < (v+1)^{P'} (z+1)^{2^{7-a}} <= (v+1)^{P'} (n+1)^{2^{10-a}}.

Eliminating v produces the family comparison

    n^2187 < (n+1)^2048 (1+1/v)^E,

where E = 2^{a+1}·3·(3^{7-a}-2^{7-a}). This is 3^7 versus
2^{11} with a (1+1/v) fudge. A convenient lower bound V
on v comes from the leading chain at the first prefix
start: n^L > (n+1)^P V^{2^{a+1}} forces u+1 > V^2, so
v >= V. That bound is monotone in n. Integer checks at
the five first starts (37, 113, 163, 173, 241) give

    n^2187 V^E > (n+1)^2048 (V+1)^E.

Contradiction. No smaller odd n follows the corresponding
prefix (pin). Leftover 4-fudge cells first fire at
1.57e9 through 3.75e12 and are not used.

Independently, OOOOOOEOEEE is a corollary of the O^6
+1-chain T^6(n) >= (n+1)^{11}: v >= (n+1)^5 isqrt(n+1),
and isqrt(n+1)*(n) >= 3(n+1) at n=163 already forces
isqrt(v^3) >= (n+1)^8.

This is not a length-11 census. The (2,2) and isolated-E
signatures are a separate job.

## Lean

- `cycle_trailing_evens_lt`: `True`
- `odd_preimage_unique`: `True`
- `o7_image_ge_succ_pow16`: `True`
- `no_cycle_itinerary_oooooooeeee`: `True`
- `no_cycle_itinerary_even_count_le_three`: `True`
- `no_cycle_itinerary_ooooooeoeee`: `True`
- `no_cycleMin_ooooooeoeee`: `True`
- `no_cycleMin_oooooeooeee`: `True`
- `no_cycleMin_ooooeoooeee`: `True`
- `no_cycleMin_oooeooooeee`: `True`
- `no_cycleMin_ooeoooooeee`: `True`
- `no_cycleMin_one_three_eee`: `True`
- no `no_cycle_itinerary_length_eleven`: `True`
- no `no_cycle_itinerary_four_even`: `True`
- no `juggler_reaches_one`: `True`
- no `no_cycle_itinerary_oooooeooeee`: `True`
- no `no_cycle_itinerary_ooooeoooeee`: `True`
- no `no_cycle_itinerary_oooeooooeee`: `True`
- no `no_cycle_itinerary_ooeoooooeee`: `True`
- no non-unique family CycleItinerary: `True`
- Paper A has no family word: `True`

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
- twenty_three_word_scan: `False`

## Decision

**ONE_THREE_EEE_GAP_PROVED**

five (1,3) words O^a E O^{7-a} EEE; family identity 3^7=2187 > 2^{11}=2048 with slack 139; exact mixed +1-chain n^2187 < (n+1)^2048 (1+1/v)^E contradicts the leading-chain lower bound on v at each first prefix start; leftover N0 unused (1.57e9 to 3.75e12); pin n<10000 empty, closest ratio 5.728451053262999 at n=37 on OOOOEOOOEEE.

This is not a halt result and not a length-11 census.

