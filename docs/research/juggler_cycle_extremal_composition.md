# Juggler extremal composition

Status: **COMPOSITION_REPACKAGING**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Composition of existing cells,
not a census.

## Branch budget

```text
Mathematical target     compose min + first-even + top cell + peak; seek a non-envelope inequality
Novelty hypothesis      distinguished locations interact more strongly than 2^K < 3^O
Falsifier               every composition reduces to an existing envelope or extremal theorem
Existing machinery      CycleMin/Max, square_scale_*, cycle_top_*, cycle_peak_*
Maximum Phase-0 scope   distinguished order; strict window; first-even vs top; stop on repackaging
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **COMPOSITION_REPACKAGING**
- secondary: `[]`
- sorry-free: `True`

distinguished cycle locations package as m ≤ p < x < M with a strict top window, but every scale composition is the ordinary word envelope. Transient starts show that p = m, z < p, z > x, and z ≥ m^2 are not universal.

A transient may realise every local cell without cyclic closure.
Those rows falsify only proposed universal inequalities, not
cycle-only statements.

## Finite-orbit distinguished points

- odd starts: `38`
- local cells hold: `38`
- local cells fail: `0`
- start ≤ p / start > p: `4/34`
- z = M / z ≠ M: `34/4`
- z < x / z > x: `1/37`
- z ≥ start² / z < start²: `18/20`
- start realises m ≤ p < x < M: `4`
- square-scale paths superquadratic: `18/18`

### Hard probes and small examples

- start=`37` M=`24906114455136` x=`852846071` p=`2233` r=`2` a=`4` z=`86818724` b=`1` y=`9317` start≤p=`True` z=M=`False` z_vs_x=`lt` window=`True` fourth=`True`
- start=`77` M=`2322378` x=`17537` p=`1523` r=`1` a=`3` z=`2322378` b=`1` y=`1523` start≤p=`True` z=M=`True` z_vs_x=`gt` window=`True` fourth=`True`
- start=`7` M=`18` x=`7` p=`1` r=`3` a=`1` z=`18` b=`3` y=`1` start≤p=`False` z=M=`True` z_vs_x=`gt` window=`True` fourth=`False`
- start=`9` M=`140` x=`27` p=`11` r=`1` a=`2` z=`140` b=`1` y=`11` start≤p=`True` z=M=`True` z_vs_x=`gt` window=`True` fourth=`True`
- start=`21` M=`140` x=`27` p=`11` r=`1` a=`1` z=`96` b=`1` y=`9` start≤p=`False` z=M=`False` z_vs_x=`gt` window=`True` fourth=`False`
- start=`25` M=`52214` x=`1397` p=`15` r=`2` a=`3` z=`52214` b=`2` y=`15` start≤p=`False` z=M=`True` z_vs_x=`gt` window=`True` fourth=`True`

- n-search: `False`
- cycle-itinerary census: `False`
- odd-landing engine: `False`
- residual graph: `False`
- new energy: `False`

## Lean

- `exists_first_even_iterate`: `True`
- `cycle_top_window_strict`: `True`
- `cycleMax_iterate_le`: `True`
- `cycleMax_not_cycleMin`: `True`
- `cycleMax_min_sq_lt`: `True`
- `cycle_distinguished_order`: `True`
- certificate unchanged: `True`
- forbidden scale theorems absent: `True`
- forbidden engines absent: `True`
- FloorPower not rewritten: `True`
- orbit-min hypothesis unused: `True`
- PowerBoundEq not used as cycle attack: `True`
- no odd-landing type: `True`
- no residual graph: `True`
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
- stronger_than_envelope: `False`
- p_equals_min: `False`
- z_below_p: `False`
- z_above_x: `False`
- odd_landing_engine: `False`
- residual_graph: `False`
- new_energy: `False`
- nested_cells_empty: `False`
- useful_uniform_Q0: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`

## Decision

**COMPOSITION_REPACKAGING**

distinguished cycle locations package as m ≤ p < x < M with a strict top window, but every scale composition is the ordinary word envelope. Transient starts show that p = m, z < p, z > x, and z ≥ m^2 are not universal.

This is not a halt result. The compatible normal form is
m ≤ p < x < M with p^{2^r} < M. Scale compositions do not
beat the ordinary word envelope.

