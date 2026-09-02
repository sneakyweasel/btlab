# Juggler maximum predecessors

Status: **TOP_NESTED_CELL_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Nested top cells, not a census.

## Branch budget

```text
Mathematical target     odd predecessor of M plus top window gives a nested-cell restriction
Novelty hypothesis      T^2(x)<x forces p<x<M; nested cells constrain (p,x,M,r)
Falsifier               a cycle-legal (p,x,M,r) with even predecessor; or a true r-obstruction
Existing machinery      cycleMax_top_normal_form, even_iter_*, odd-even two-step, odd cube cell
Maximum Phase-0 scope   predecessor odd; p<x<M; nested cells; x^3≥p^{2^{r+1}}; transient preds
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **TOP_NESTED_CELL_GREEN**
- secondary: `['TOP_SCALE_GAP_GREEN', 'TOP_NESTED_CELL_SURVIVES']`
- sorry-free: `True`

every cycle maximum is reached from an odd predecessor x with p < x < M, nested cells, x^3 ≥ p^{2^{r+1}}, and M < x^2. The integer region stays nonempty; x ≥ p^2 is not forced.

T(M)=p only when r=1. For r>1 the two-step law still gives
T(M)<x, and even descent gives p≤T(M), so p<x remains forced.
The nested cells do not empty any top-run length.

## Finite-orbit predecessors

- odd starts: `38`
- three-level holds: `38`
- structural fails: `0`
- scale checked: `38`
- scale fails: `0`
- x vs p^2: `{'lt': 12, 'eq': 0, 'gt': 26}`
- r=1,2 envelope room: `{'r1': True, 'r2': True}`

### Hard probes and small examples

- start=`37` M=`24906114455136` x=`852846071` p=`2233` r=`2` three=`True` cube=`True` vs_p2=`gt` scale=`True`
- start=`77` M=`2322378` x=`17537` p=`1523` r=`1` three=`True` cube=`True` vs_p2=`lt` scale=`True`
- start=`3` M=`36` x=`11` p=`1` r=`3` three=`True` cube=`True` vs_p2=`gt` scale=`True`
- start=`7` M=`18` x=`7` p=`1` r=`3` three=`True` cube=`True` vs_p2=`gt` scale=`True`
- start=`9` M=`140` x=`27` p=`11` r=`1` three=`True` cube=`True` vs_p2=`lt` scale=`True`
- start=`25` M=`52214` x=`1397` p=`15` r=`2` three=`True` cube=`True` vs_p2=`gt` scale=`True`

- n-search: `False`
- cycle-itinerary census: `False`

## Lean

- `cycleMax_predecessor_odd`: `True`
- `cycleMax_predecessor_lt`: `True`
- `cycle_top_predecessor_cell`: `True`
- `cycle_top_three_level`: `True`
- `cycle_top_nested_cell`: `True`
- `cycle_top_scale_constraint`: `True`
- `cycle_top_pred_scale`: `True`
- `cycle_top_max_lt_pred_sq`: `True`
- certificate unchanged: `True`
- FloorPower not rewritten: `True`
- orbit-min hypothesis unused: `True`
- PowerBoundEq not used as cycle attack: `True`
- no run-obstruction theorem: `True`
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
- top_ascent_impossible: `False`
- top_run_impossible: `False`
- nested_cells_empty: `False`
- pred_ge_p_sq: `False`
- T_of_max_equals_landing_always: `False`
- max_first_cell_impossible: `False`
- useful_uniform_Q0: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`

## Decision

**TOP_NESTED_CELL_GREEN**

every cycle maximum is reached from an odd predecessor x with p < x < M, nested cells, x^3 ≥ p^{2^{r+1}}, and M < x^2. The integer region stays nonempty; x ≥ p^2 is not forced.

This is not a halt result. Nested cells survive. Direct
return x=p is excluded. No top-run length is eliminated.

