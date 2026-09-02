# Juggler cyclic rounding

Status: **CYCLIC_ROUNDING_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Exact remainders, not a census.

## Branch budget

```text
Mathematical target     exact local remainders plus cyclic closure, not an exponent budget
Novelty hypothesis      keeping ρ around a cycle sees something the envelope drops
Falsifier               every remainder identity reduces to power_bound_word or a known cell
Existing machinery      localDefect, cube/square cells, CycleItinerary, equality rigidity
Maximum Phase-0 scope   remainder API; cycle balance; all-zero rigidity; peak ρ_O>0; transients
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **CYCLIC_ROUNDING_GREEN**
- secondary: `['CYCLIC_ROUNDING_NEW_CONSTRAINT', 'CYCLE_REMAINDER_RIGIDITY_GREEN']`
- sorry-free: `True`

every cycle branch has an exact remainder in the successor window, cyclic return balances those remainders against the odd/even state gaps, and n≥2 forbids the all-zero pattern. Dropping the remainders recovers the ordinary envelope. Universal remainder amplification is already false on start 9.

A transient realises the local remainder equations without
cyclic closure. The balance identity then fails by the
correction x0^2 - xk^2. Those rows do not refute cycle-only
statements.

## Finite-orbit remainders

- odd starts: `38`
- local identities hold: `38`
- local identities fail: `0`
- later remainder grows / does not: `14/24`
- start 9 remainders: `[0, 83, 19, 35, 0, 2]`
- start 9 later grows: `False`

### Hard probes and small examples

- start=`37` M=`24906114455136` x=`852846071` p=`2233` ρ_O=`32062941637415` ρ_top=`43036463615` identity=`True` correction=`1368` grows=`False`
- start=`77` M=`2322378` x=`17537` p=`1523` ρ_O=`1098269` ρ_top=`2849` identity=`True` correction=`5928` grows=`False`
- start=`3` M=`36` x=`11` p=`1` ρ_O=`35` ρ_top=`35` identity=`True` correction=`8` grows=`True`
- start=`7` M=`18` x=`7` p=`1` ρ_O=`19` ρ_top=`17` identity=`True` correction=`48` grows=`False`
- start=`9` M=`140` x=`27` p=`11` ρ_O=`83` ρ_top=`19` identity=`True` correction=`80` grows=`False`
- start=`21` M=`140` x=`27` p=`11` ρ_O=`83` ρ_top=`19` identity=`True` correction=`440` grows=`False`

- n-search: `False`
- cycle-itinerary census: `False`
- remainder dynamics: `False`
- new energy: `False`

## Lean

- `localDefectOdd_lt_succ`: `True`
- `branchDefect_add`: `True`
- `branchDefect_lt`: `True`
- `cycle_remainder_eq`: `True`
- `cycle_remainder_lt`: `True`
- `cycle_remainder_balance`: `True`
- `cycle_remainders_project_to_envelope`: `True`
- `cycle_not_localsTight`: `True`
- `cycle_exists_pos_remainder`: `True`
- `cycleMax_pred_cube_strict`: `True`
- `cycle_peak_odd_remainder_pos`: `True`
- certificate unchanged: `True`
- FloorPower has no CycleItinerary: `True`
- orbit-min hypothesis unused: `True`
- PowerBoundEq not used as cycle attack: `True`
- no remainder dynamics: `True`
- no energy: `True`
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
- remainder_amplification: `False`
- remainder_dynamics: `False`
- new_energy: `False`
- odd_landing_engine: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`

## Decision

**CYCLIC_ROUNDING_GREEN**

every cycle branch has an exact remainder in the successor window, cyclic return balances those remainders against the odd/even state gaps, and n≥2 forbids the all-zero pattern. Dropping the remainders recovers the ordinary envelope. Universal remainder amplification is already false on start 9.

This is not a halt result. The remainders refine the
envelope. They do not yet forbid a nontrivial cycle.

