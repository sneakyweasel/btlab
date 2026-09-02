# Juggler length-8 two-even bootstrap

Status: **LENGTH8_BOOTSTRAP_REPARAMETERIZATION**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. The two length-8 squares only;
not a length-8 census and not a leftover cell.

## Branch budget

```text
Mathematical target     Are OOOOEOOE and OOOEOOOE new
                        leftovers, or OO/OOO bootstrap?
Novelty hypothesis      The square reading (OOE)^2 / (OOOE)^2
                        is a new leftover last cluster
Falsifier               The suffix between the internal E and
                        the last E is already next-square
Existing machinery      no_cycleMin_internal_even_threshold;
                        oo/ooo thresholds; Theorem 3.12;
                        odd-run; repeated-block transients
Maximum Phase-0 scope   Name the eight-word inventory;
                        no Lean, no census, no Paper A
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **LENGTH8_BOOTSTRAP_REPARAMETERIZATION**
- expanding even-terminating length-8 words: `8`
- leftovers: `0`
- squares: `OOOOEOOE`, `OOOEOOOE`

OOOOEOOE = OO(OOE)^2 and OOOEOOOE = (OOOE)^2 are the next OO/OOO bootstrap instances, not leftovers; every even-terminating expanding length-8 word has a named filter; not a length-8 census.

## Inventory

- `OOOOOOOE` filter=`odd_run` suffix=`None` square=`None`
- `OOOOOOEE` filter=`two_even_ee` suffix=`` square=`None`
- `OOOOOEOE` filter=`two_even_eoe` suffix=`O` square=`None`
- `OOOOEOOE` filter=`bootstrap_oo_suffix_threshold` suffix=`OO` square=`OO + (OOE)^2`
- `OOOEOOOE` filter=`bootstrap_ooo_suffix_threshold` suffix=`OOO` square=`(OOOE)^2`
- `OOEOOOOE` filter=`bootstrap_odd_run_suffix_threshold` suffix=`OOOO` square=`None`
- `OEOOOOOE` filter=`cycleMin_not_odd_even` suffix=`OOOOO` square=`None`
- `EOOOOOOE` filter=`rotate_start_even` suffix=`OOOOOO` square=`None`

## Lean

- `no_cycleMin_internal_even_threshold`: `True`
- `oo_suffix_threshold`: `True`
- `ooo_suffix_threshold`: `True`
- `no_cycle_itinerary_ooeooe`: `True`
- `no_cycle_itinerary_oooeooe`: `True`
- no length-8 theorem: `True`
- length eight open in census: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- length_eight_census: `False`
- new_leftover_cell: `False`
- induction_on_period: `False`
- induction_on_n: `False`

## Decision

**LENGTH8_BOOTSTRAP_REPARAMETERIZATION**

OOOOEOOE = OO(OOE)^2 and OOOEOOOE = (OOOE)^2 are the next OO/OOO bootstrap instances, not leftovers; every even-terminating expanding length-8 word has a named filter; not a length-8 census.

This is not a halt result and not a length-8 census.

