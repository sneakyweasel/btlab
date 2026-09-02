# Juggler maximal odd-run word

Status: **ODD_RUN_ITINERARY_PARK**

Standalone application phase. Not a Research Engine experiment,
not a residue automaton, and not a halt theorem. The leftover
is read as a sequence of maximal odd-run lengths.

## Branch budget

```text
Mathematical target     exact (a,b) constraints under
                        AboveAnchor, beyond isolated OE
Novelty hypothesis      some later transitions are forbidden,
                        or a long run forces a short next run
Falsifier               T as free as parity; same a-prefix
                        splits; burst tradeoff fails
Existing machinery      isolated-OE r-bound; ooe_oe FP;
                        pe_blocks; leftover controls
Maximum Phase-0 scope   leftovers + odd n<2001; no automaton
```

## Metadata

- classification: **ODD_RUN_ITINERARY_PARK**
- 365 runs: `[2, 2, 2, 2, 1]`
- 1517 runs: `[2, 2, 2, 1, 3]`
- first (2,1) stay: `0`
- later (2,1) stay: `37`
- 222 next: `{'1': 3, '2': 1}`
- burst long-long: `6`

run-length transitions are unrestricted after the first block; the only exact (2,1) ban is the known isolated-OE drop from the anchor; later (2,1) can stay; 365 and 1517 share (2,2,2) then split; long runs need not force short successors.

## Controls

- n=`365` runs=`[2, 2, 2, 2, 1]` Lambda=`19683/16384` drop=`False`
- n=`501` runs=`[2, 3, 2, 2, 2, 2, 1]` Lambda=`4782969/2097152` drop=`False`
- n=`1517` runs=`[2, 2, 2, 1, 3]` Lambda=`59049/32768` drop=`False`
- n=`6187` runs=`[2, 3, 2, 1]` Lambda=`6561/4096` drop=`True`
- n=`69` runs=`[2, 2]` Lambda=`81/64` drop=`False`
- n=`89` runs=`[2, 2, 1]` Lambda=`243/256` drop=`True`
- n=`173` runs=`[2, 8, 2, 2, 1, 1]` Lambda=`43046721/4194304` drop=`False`
- n=`193` runs=`[3, 7, 3, 1, 6, 3, 2, 5, 4, 2, 2, 1, 2, 2, 1]` Lambda=`984770902183611232881/576460752303423488` drop=`False`
- n=`241` runs=`[5, 5, 1, 2, 1, 2, 1]` Lambda=`129140163/16777216` drop=`True`
- n=`565` runs=`[2, 2, 9, 1, 1]` Lambda=`14348907/1048576` drop=`False`

## Existing Lean (unchanged)

- `isolatedOddSurvival_bound`: `True`
- `aboveAnchor_isolated_two`: `True`
- `finiteProgress_of_ooe_oe`: `True`
- `oe_block_contracts`: `True`
- `AboveAnchor`: `True`
- new Lean file: `False`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- run_graph_grammar: `False`
- lambda_balance_theorem: `False`
- burst_tradeoff: `False`
- residue_automaton: `False`

## Decision

**ODD_RUN_ITINERARY_PARK**

run-length transitions are unrestricted after the first block; the only exact (2,1) ban is the known isolated-OE drop from the anchor; later (2,1) can stay; 365 and 1517 share (2,2,2) then split; long runs need not force short successors.

This is not a halt result and not a run-frequency theorem.

