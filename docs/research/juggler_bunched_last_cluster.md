# Juggler bunched last-cluster leftover tails

Status: **BUNCHED_LAST_CLUSTER_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Seven bunched last-cluster
families only; not a length-8/9 census and not first-E at
e>=4.

## Branch budget

```text
Mathematical target     Do the seven bunched last-cluster
                        tails fire for every large a, with
                        N0 bounded in a?
Novelty hypothesis      Fixed mixed tail plus C_{O^a};
                        cutoffs drop as a grows
Falsifier               A tail whose N0 grows with a
Existing machinery      prefix-cell Z; denomBits; OOOOOOEEE
Maximum Phase-1 scope   Lean all seven bunched families;
                        no length-8/9 census
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **BUNCHED_LAST_CLUSTER_GREEN**
- sorry-free: `True`
- family count: `7`
- max N0: `188`
- plateau N0=5: `True`
- tables empty: `True`
- EEE cubes from 73: `True`
- EOEE cubes from 314: `True`
- EOOEE cubes from 205: `True`

seven bunched last-cluster families fire with N0 bounded in a; Lean excludes all seven as CycleItinerary families; a uniform coarse (n+1)^K cell for the last four is refuted and those four use a tight last-odd cell; not a length-8/9 census.

## Families

- `EEE` tail=`EEE` a>=`6` N0=`[73, 13, 8, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]`
- `EOEE` tail=`EOEE` a>=`5` N0=`[89, 14, 8, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]`
- `EOOEE` tail=`EOOEE` a>=`4` N0=`[120, 15, 9, 7, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]`
- `EOOOEE` tail=`EOOOEE` a>=`3` N0=`[188, 18, 9, 7, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]`
- `EEOE` tail=`EEOE` a>=`5` N0=`[60, 12, 8, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]`
- `EOEOE` tail=`EOEOE` a>=`4` N0=`[81, 13, 8, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]`
- `EOOEOE` tail=`EOOEOE` a>=`3` N0=`[126, 16, 9, 7, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]`

## Lean

- `cycle_trailing_evens_lt`: `True`
- `no_cycle_itinerary_ooooooeee`: `True`
- `no_cycle_itinerary_two_even_ee`: `True`
- `no_cycle_itinerary_two_even_eoe`: `True`
- `no_cycleMin_gapped_three_even_ee`: `True`
- `no_cycleMin_gapped_three_even_eoe`: `True`
- `no_cycle_itinerary_length_le_seven`: `True`
- `CycleMin`: `True`
- `no_cycle_itinerary_three_even_eee`: `True`
- `three_even_eee_tail`: `True`
- `no_cycle_itinerary_three_even_eoee`: `True`
- `three_even_eoee_tail_of_five`: `True`
- `no_cycle_itinerary_three_even_eooee`: `True`
- `three_even_eooee_tail`: `True`
- `no_cycle_itinerary_three_even_eoooee`: `True`
- `no_cycle_itinerary_three_even_eeoe`: `True`
- `no_cycle_itinerary_three_even_eoeoe`: `True`
- `no_cycle_itinerary_three_even_eooeoe`: `True`
- no bunched-tail theorem: `True`
- length eight open in census: `True`
- no length-nine theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- three_even_cycles_impossible: `False`
- bunched_lean: `False`
- eee_lean: `True`
- eoee_lean: `True`
- eooee_lean: `True`
- eoooee_lean: `True`
- eeoe_lean: `True`
- eoeoe_lean: `True`
- eooeoe_lean: `True`
- uniform_coarse_K: `False`
- length_eight_census: `False`
- length_nine_census: `False`
- first_e_at_four: `False`
- induction_on_period: `False`
- induction_on_n: `False`

## Decision

**BUNCHED_LAST_CLUSTER_GREEN**

seven bunched last-cluster families fire with N0 bounded in a; Lean excludes all seven as CycleItinerary families; a uniform coarse (n+1)^K cell for the last four is refuted and those four use a tight last-odd cell; not a length-8/9 census.

This is not a halt result, not a length-8/9 census, and
not a Lean theorem no_cycle_itinerary_bunched.

