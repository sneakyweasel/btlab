# Juggler canonical peak descent

Status: **PEAK_DESCENT_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Peak blocks, not a census.

## Branch budget

```text
Mathematical target     canonical OE^r descent plus finance vs existing ascent scale
Novelty hypothesis      every cycle has a determined contracting peak block
Falsifier               peak image misses p; or finance stronger than top-ascent
Existing machinery      cycle_top_three_level, oddEvenBlock, power_bound_word
Maximum Phase-0 scope   peak descent; contracting; finance=ascent; transient peaks
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **PEAK_DESCENT_GREEN**
- secondary: `['MILESTONE_REPACKAGING']`
- sorry-free: `True`

every cycle maximum has a canonical OE^r descent from its odd predecessor to the landing, and that block is formally contracting. Financing it from p back to x recovers the existing ascent scale, not a stronger envelope.

Transient orbits realise the peak descent but do not close an
ascent from p back to x. That closed financing is cycle-only.
T(p) may be odd or even; no milestone engine is opened.

## Finite-orbit peak blocks

- odd starts: `38`
- peak holds: `38`
- peak fails: `0`
- T(p) odd/even: `20/18`
- closed ascents from landing: `0`

### Hard probes and small examples

- start=`37` M=`24906114455136` x=`852846071` p=`2233` r=`2` peak=`True` contracting=`True` T(p)=`105519` odd=`True`
- start=`77` M=`2322378` x=`17537` p=`1523` r=`1` peak=`True` contracting=`True` T(p)=`59436` odd=`False`
- start=`3` M=`36` x=`11` p=`1` r=`3` peak=`True` contracting=`True` T(p)=`1` odd=`True`
- start=`7` M=`18` x=`7` p=`1` r=`3` peak=`True` contracting=`True` T(p)=`1` odd=`True`
- start=`9` M=`140` x=`27` p=`11` r=`1` peak=`True` contracting=`True` T(p)=`36` odd=`False`
- start=`25` M=`52214` x=`1397` p=`15` r=`2` peak=`True` contracting=`True` T(p)=`58` odd=`False`

- n-search: `False`
- cycle-itinerary census: `False`
- odd-milestone engine: `False`

## Lean

- `peak_block_formally_contracting`: `True`
- `peak_block_contracts`: `True`
- `cycle_peak_descent`: `True`
- `peak_ascent_scale`: `True`
- `cycle_peak_finance`: `True`
- certificate unchanged: `True`
- FloorPower not rewritten: `True`
- orbit-min hypothesis unused: `True`
- PowerBoundEq not used as cycle attack: `True`
- no milestone engine: `True`
- no stronger-scale claim: `True`
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
- O_terminating_cycles_impossible: `False`
- word_independent_obstruction: `False`
- peak_scale_stronger: `False`
- odd_milestone_engine: `False`
- p_equals_min: `False`
- nested_cells_empty: `False`
- top_run_impossible: `False`
- useful_uniform_Q0: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`

## Decision

**PEAK_DESCENT_GREEN**

every cycle maximum has a canonical OE^r descent from its odd predecessor to the landing, and that block is formally contracting. Financing it from p back to x recovers the existing ascent scale, not a stronger envelope.

This is not a halt result. The peak block is contracting.
Its finance law is a repackaging of the top ascent.

