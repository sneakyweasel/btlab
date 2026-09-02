# Juggler cycle Diophantine defects

Status: **DIOPHANTINE_REPACKAGING**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Peak defects, not a census.

## Branch budget

```text
Mathematical target     Does the peak pair (δ, ε) impose a congruence
                        or residual-class restriction that the existing
                        scale envelope cannot see?
Novelty hypothesis      sequential x^3 = (p^{2^r}+ε)^2+δ; modular rigidity;
                        R={1..11} may force p≥13 on a nontrivial cycle
Falsifier               composition is the known slack; residues are odd/odd
Existing machinery      localDefectOdd, cycle_top_window_strict,
                        cycle_top_nested_cell, reachesOne_of_lt_twelve
Maximum Phase-0 scope   named defects; composition; residue census; R-avoidance
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **DIOPHANTINE_REPACKAGING**
- secondary: `['CYCLE_R_AVOIDANCE_GREEN']`
- sorry-free: `True`

The sequential identity is the known slack x^3 - p^{2^{r+1}} = 2ε p^{2^r} + ε^2 + δ; every residue law is odd/odd or a known cell; R-avoidance only upgrades 2 ≤ p to 13 ≤ p.

A transient realises the two peak cells without cyclic closure.
Landings in R={1,...,11} therefore appear off-cycle and do not
refute the cycle-only bound p≥13.

## Finite-orbit peak defects

- odd starts: `38`
- composition holds: `38`
- composition fails: `0`
- landings in R: `27` starts `[3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 27, 29, 33, 35, 41, 43, 45, 53, 55, 57, 63, 65, 69, 71, 73, 75]`
- all δ,ε odd: `True`
- distinct (δ,ε) mod 8: `13`
- distinct (δ,ε) mod 16: `24`
- r≥2 peaks: `26`
- p^{2^r} mod 16 for r≥2: `{'1': 26}`
- envelope-only residues: `True`

### Residue pairs (δ,ε)

- mod 4: `{'1,1': 10, '1,3': 6, '3,1': 9, '3,3': 13}`
- mod 8: `{'1,3': 2, '1,5': 4, '1,7': 1, '3,1': 5, '3,3': 9, '3,5': 3, '5,1': 2, '5,3': 2, '5,5': 4, '5,7': 1, '7,3': 2, '7,5': 1, '7,7': 2}`
- mod 16: `{'1,5': 2, '1,11': 1, '1,13': 1, '1,15': 1, '3,1': 2, '3,3': 7, '3,5': 1, '3,13': 1, '5,3': 1, '5,5': 2, '5,11': 1, '5,13': 1, '7,15': 2, '9,5': 1, '9,11': 1, '11,1': 2, '11,3': 2, '11,9': 1, '11,13': 1, '13,1': 2, '13,5': 1, '13,15': 1, '15,3': 2, '15,5': 1}`

### Hard probes and small examples

- start=`37` M=`24906114455136` x=`852846071` p=`2233` r=`2` δ=`32062941637415` ε=`43036463615` compose=`True` slack=`True` in_R=`False`
- start=`77` M=`2322378` x=`17537` p=`1523` r=`1` δ=`1098269` ε=`2849` compose=`True` slack=`True` in_R=`False`
- start=`3` M=`36` x=`11` p=`1` r=`3` δ=`35` ε=`35` compose=`True` slack=`True` in_R=`True`
- start=`7` M=`18` x=`7` p=`1` r=`3` δ=`19` ε=`17` compose=`True` slack=`True` in_R=`True`
- start=`9` M=`140` x=`27` p=`11` r=`1` δ=`83` ε=`19` compose=`True` slack=`True` in_R=`True`
- start=`21` M=`140` x=`27` p=`11` r=`1` δ=`83` ε=`19` compose=`True` slack=`True` in_R=`True`

- n-search: `False`
- cycle-itinerary census: `False`
- remainder dynamics: `False`
- new energy: `False`
- Mordell solver: `False`

## Lean

- `peakOddDefect_add`: `True`
- `peakOddDefect_lt`: `True`
- `peakOddDefect_odd`: `True`
- `peakOddDefect_pos`: `True`
- `topEvenDefect_add`: `True`
- `topEvenDefect_pos`: `True`
- `topEvenDefect_lt`: `True`
- `topEvenDefect_odd`: `True`
- `peak_diophantine_compose`: `True`
- `peak_diophantine_slack`: `True`
- `cycle_peak_diophantine`: `True`
- `cycle_peak_diophantine_slack`: `True`
- `cycleItinerary_not_reachesOne`: `True`
- `cycleItinerary_iterate_not_lt_twelve`: `True`
- `cycle_top_landing_ge_thirteen`: `True`
- certificate unchanged: `True`
- CycleItinerary not rewritten: `True`
- FloorPower not rewritten: `True`
- orbit-min hypothesis unused: `True`
- PowerBoundEq not used as cycle attack: `True`
- no remainder dynamics: `True`
- no energy: `True`
- no Mordell solver: `True`
- no extra modular lemma: `True`
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
- word_independent_obstruction: `False`
- remainder_dynamics: `False`
- new_energy: `False`
- odd_landing_engine: `False`
- mordell_solver: `False`
- stronger_than_envelope_slack: `False`
- modular_restriction_beyond_odd: `False`

## Decision

**DIOPHANTINE_REPACKAGING**

The sequential identity is the known slack x^3 - p^{2^{r+1}} = 2ε p^{2^r} + ε^2 + δ; every residue law is odd/odd or a known cell; R-avoidance only upgrades 2 ≤ p to 13 ≤ p.

This is not a halt result. The sequential identity is the
existing envelope slack. Do not reopen defect composition.

