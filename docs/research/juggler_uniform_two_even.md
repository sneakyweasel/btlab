# Juggler uniform two-even leftover tails

Status: **TWO_EVEN_UNIFORM_TAIL_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. The two leftover families
`O^{k-2}EE` and `O^{k-3}EOE` only; not a length-8 census and
not induction on period or on n.

## Branch budget

```text
Mathematical target     Do both two-even leftover tails fire
                        for every k>=6 with N0 bounded in k?
Novelty hypothesis      Cutoffs get easier; N0 drops to 5
Falsifier               A k that never fires, or N0(k)->inf
Existing machinery      Lemma 3.5/3.7 cells; lowerDenom(O^a)
Maximum Phase-0 scope   N0(k) for k=6..24; empty tables;
                        no Lean, no length-8 census, no halt
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **TWO_EVEN_UNIFORM_TAIL_GREEN**
- sorry-free: `True`

both leftover families are Lean-excluded for every k>=6 and n>=2 by the shared tail at n>=256 plus the seven-odd obstruction and three Fin 256 tables below 256; N0(6)=205 then 14,8,6,6 and N0=5 for k>=11; not a length-8 census.

## Shared tail

- comparison: `n^{3^{k-2}} > 2^{e_{k-2}} (n+1)^{2^k}`
- `e_a = 2*3^a - 2^{a+1} = log2(lowerDenom(O^a))`
- closed form matches recurrence: `True`
- both families expanding for k=6..24: `True`
- never holds for n<=4: `True`
- EOE auxiliary from n=2: `True`
- max N0: `205`
- plateau N0=5 for k>=11: `True`
- all tables empty: `True`

## Cutoffs

- k=`6` words=`OOOOEE` / `OOOEOE` N0=`205` e=`130` ee_hits=`[]` eoe_hits=`[]`
- k=`7` words=`OOOOOEE` / `OOOOEOE` N0=`14` e=`422` ee_hits=`[]` eoe_hits=`[]`
- k=`8` words=`OOOOOOEE` / `OOOOOEOE` N0=`8` e=`1330` ee_hits=`[]` eoe_hits=`[]`
- k=`9` words=`OOOOOOOEE` / `OOOOOOEOE` N0=`6` e=`4118` ee_hits=`[]` eoe_hits=`[]`
- k=`10` words=`OOOOOOOOEE` / `OOOOOOOEOE` N0=`6` e=`12610` ee_hits=`[]` eoe_hits=`[]`
- k=`11` words=`OOOOOOOOOEE` / `OOOOOOOOEOE` N0=`5` e=`38342` ee_hits=`[]` eoe_hits=`[]`
- k=`12` words=`OOOOOOOOOOEE` / `OOOOOOOOOEOE` N0=`5` e=`116050` ee_hits=`[]` eoe_hits=`[]`
- k=`13` words=`OOOOOOOOOOOEE` / `OOOOOOOOOOEOE` N0=`5` e=`350198` ee_hits=`[]` eoe_hits=`[]`
- k=`14` words=`OOOOOOOOOOOOEE` / `OOOOOOOOOOOEOE` N0=`5` e=`1054690` ee_hits=`[]` eoe_hits=`[]`
- k=`15` words=`OOOOOOOOOOOOOEE` / `OOOOOOOOOOOOEOE` N0=`5` e=`3172262` ee_hits=`[]` eoe_hits=`[]`
- k=`16` words=`OOOOOOOOOOOOOOEE` / `OOOOOOOOOOOOOEOE` N0=`5` e=`9533170` ee_hits=`[]` eoe_hits=`[]`
- k=`17` words=`OOOOOOOOOOOOOOOEE` / `OOOOOOOOOOOOOOEOE` N0=`5` e=`28632278` ee_hits=`[]` eoe_hits=`[]`
- k=`18` words=`OOOOOOOOOOOOOOOOEE` / `OOOOOOOOOOOOOOOEOE` N0=`5` e=`85962370` ee_hits=`[]` eoe_hits=`[]`
- k=`19` words=`OOOOOOOOOOOOOOOOOEE` / `OOOOOOOOOOOOOOOOEOE` N0=`5` e=`258018182` ee_hits=`[]` eoe_hits=`[]`
- k=`20` words=`OOOOOOOOOOOOOOOOOOEE` / `OOOOOOOOOOOOOOOOOEOE` N0=`5` e=`774316690` ee_hits=`[]` eoe_hits=`[]`
- k=`21` words=`OOOOOOOOOOOOOOOOOOOEE` / `OOOOOOOOOOOOOOOOOOEOE` N0=`5` e=`2323474358` ee_hits=`[]` eoe_hits=`[]`
- k=`22` words=`OOOOOOOOOOOOOOOOOOOOEE` / `OOOOOOOOOOOOOOOOOOOEOE` N0=`5` e=`6971471650` ee_hits=`[]` eoe_hits=`[]`
- k=`23` words=`OOOOOOOOOOOOOOOOOOOOOEE` / `OOOOOOOOOOOOOOOOOOOOEOE` N0=`5` e=`20916512102` ee_hits=`[]` eoe_hits=`[]`
- k=`24` words=`OOOOOOOOOOOOOOOOOOOOOOEE` / `OOOOOOOOOOOOOOOOOOOOOEOE` N0=`5` e=`62753730610` ee_hits=`[]` eoe_hits=`[]`

## Lean

- `cycle_itinerary_formally_expanding`: `True`
- `cycle_last_even_interval`: `True`
- `cycle_trailing_evens_lt`: `True`
- `no_cycle_itinerary_ooooee`: `True`
- `no_cycle_itinerary_oooeoe`: `True`
- `no_cycle_itinerary_oooooee`: `True`
- `no_cycle_itinerary_ooooeoe`: `True`
- `no_cycle_itinerary_length_le_seven`: `True`
- `no_cycle_itinerary_two_even_ee`: `True`
- `no_cycle_itinerary_two_even_eoe`: `True`
- `shared_two_even_tail`: `True`
- `denomBits`: `True`
- length eight open in census: `True`
- no length-eight theorem: `True`
- no all-cycles-impossible theorem: `True`
- no cycle engine: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- two_even_cycles_impossible: `False`
- two_even_leftover_families_excluded: `True`
- length_eight_census: `False`
- induction_on_period: `False`
- induction_on_n: `False`
- no_escape_orbits: `False`

## Decision

**TWO_EVEN_UNIFORM_TAIL_GREEN**

both leftover families are Lean-excluded for every k>=6 and n>=2 by the shared tail at n>=256 plus the seven-odd obstruction and three Fin 256 tables below 256; N0(6)=205 then 14,8,6,6 and N0=5 for k>=11; not a length-8 census.

This is not a halt result and not a length-8 census.
The two leftover families are Lean-excluded for every
k>=6. Other two-even words and three-even leftovers
were not opened.

