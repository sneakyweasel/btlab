# Juggler long odd-chain minimality

Status: **ODD_CHAIN_MINIMALITY_CLOSED**

Whole-odd-chain compression versus unique inverse and EnvelopeState.
Not a halt theorem. Not a cube-crossing reopen.

## Branch budget

```text
Mathematical target     long odd chain => smaller bad state
                        or good-set contradiction
Novelty hypothesis      the coupled near-power system
                        compresses
Maximum Phase-0 scope   named runs; long starts; no Lean
```

## Metadata

- classification: **ODD_CHAIN_MINIMALITY_CLOSED**
- unique preds: `True`
- monotone: `True`
- pred below anchor: `False`
- shift coupled: `False`
- long lengths: `{'37': 4, '241': 5, '329': 8}`
- L-lab length: `5`

the unique odd inverse of a chain is the chain; pred0 is the start or empty; shift does not couple; mod 8 and growth are floorPower_odd_gt / generic odd-odd; long finite chains exist with the same structure.

## Named orbits

- `37`: runs=`3` max_len=`4`
  - x0=`37` len=`4` pred0=`None` reset=`86818724`
  - x0=`9317` len=`3` pred0=`None` reset=`24906114455136`
  - x0=`2233` len=`2` pred0=`None` reset=`34276462`
- `69`: runs=`2` max_len=`2`
  - x0=`69` len=`2` pred0=`None` reset=`13716`
  - x0=`117` len=`2` pred0=`None` reset=`44992`
- `89`: runs=`3` max_len=`2`
  - x0=`89` len=`2` pred0=`None` reset=`24302`
  - x0=`155` len=`2` pred0=`None` reset=`84722`
  - x0=`291` len=`1` pred0=`None` reset=`4964`
- `365`: runs=`5` max_len=`2`
  - x0=`365` len=`2` pred0=`None` reset=`582276`
  - x0=`763` len=`2` pred0=`None` reset=`3059506`
  - x0=`1749` len=`2` pred0=`None` reset=`19782308`
  - x0=`4447` len=`2` pred0=`None` reset=`161491284`
  - x0=`12707` len=`1` pred0=`None` reset=`1432400`
- `501`: runs=`7` max_len=`3`
  - x0=`501` len=`2` pred0=`None` reset=`1187360`
  - x0=`1089` len=`3` pred0=`None` reset=`17781526790`
  - x0=`133347` len=`2` pred0=`None` reset=`339791341082`
  - x0=`763` len=`2` pred0=`None` reset=`3059506`
  - x0=`1749` len=`2` pred0=`None` reset=`19782308`
  - x0=`4447` len=`2` pred0=`None` reset=`161491284`
  - x0=`12707` len=`1` pred0=`None` reset=`1432400`
- `1517`: runs=`5` max_len=`3`
  - x0=`1517` len=`2` pred0=`None` reset=`14362030`
  - x0=`3789` len=`2` pred0=`None` reset=`112636568`
  - x0=`10613` len=`2` pred0=`None` reset=`1143235850`
  - x0=`33811` len=`1` pred0=`None` reset=`6217088`
  - x0=`2493` len=`3` pred0=`None` reset=`291028018566`
- `6187`: runs=`4` max_len=`3`
  - x0=`6187` len=`2` pred0=`None` reset=`339491658`
  - x0=`18425` len=`3` pred0=`None` reset=`248742471750750`
  - x0=`15771571` len=`2` pred0=`None` reset=`15675400641582836`
  - x0=`11189` len=`1` pred0=`None` reset=`1183550`

## Long initial odd runs

- `37`: x0=`37` len=`4` pred0=`None` reset=`86818724`
- `241`: x0=`241` len=`5` pred0=`None` reset=`1225313838630510914`
- `329`: x0=`329` len=`8` pred0=`None` reset=`32533545863179570755492129120411963721630316057459884067704058780`
- L-lab `33391`: x0=`67709` len=`5` pred0=`None` reset=`4816383738386359112539037957095874424`

## Existing Lean (unchanged)

- `floorPower_odd_gt`: `True`
- `odd_preimage_unique`: `True`
- `odd_run_power_bound`: `True`
- `EnvelopeState`: `True`
- `AboveAnchor`: `True`
- `MinimalNonTerm`: `True`
- new Lean file: `False`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- chain_compression: `False`
- smaller_bad_witness: `False`
- odd_chain_lean: `False`
- universal_odd_run_bound: `False`
- cube_crossing_reopen: `False`
- z5_reopen: `False`

## Decision

**ODD_CHAIN_MINIMALITY_CLOSED**

the unique odd inverse of a chain is the chain; pred0 is the start or empty; shift does not couple; mod 8 and growth are floorPower_odd_gt / generic odd-odd; long finite chains exist with the same structure.

