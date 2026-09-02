# Juggler cube-boundary crossing

Status: **CUBE_CROSSING_CLOSED**

Local arithmetic of an odd cube-band crossing and its first re-entry.
Not a halt theorem. Not a power-cell chain.

## Branch budget

```text
Mathematical target     reusable restriction on first
                        re-entry from x^3 = y^2 + delta
Novelty hypothesis      source-cell position couples to
                        the return / F
Maximum Phase-0 scope   named starts; no Lean; no Sigma
```

## Metadata

- classification: **CUBE_CROSSING_CLOSED**
- crossings: `10`
- F defined: `5`
- F undefined: `5`
- odd lifts: `3`
- even lifts: `7`
- contrast empty: `True`
- defect generic: `True`
- periodic F: `False`

delta parity is generic odd-odd; unique preimage is odd_preimage_unique; F is not defined on a stable class and moves both ways; even-return cannot apply after an odd lift because y already left the cube band.

## Crossings

- `37`: count=`3` F_defined=`2` odd_lifts=`3` even_lifts=`0`
  - x=`3375` y=`196069` odd_lift=`True` delta_frac=`0.7819013156049258` F=`9317` tau=`2`
  - x=`9317` y=`899319` odd_lift=`True` delta_frac=`0.7751705595175018` F=`2233` tau=`3`
  - x=`2233` y=`105519` odd_lift=`True` delta_frac=`0.5874553992390033` F=`None` tau=`2`
- `69`: count=`0` F_defined=`0` odd_lifts=`0` even_lifts=`0`
- `89`: count=`0` F_defined=`0` odd_lifts=`0` even_lifts=`0`
- `365`: count=`1` F_defined=`0` odd_lifts=`0` even_lifts=`1`
  - x=`296551` y=`161491284` odd_lift=`False` delta_frac=`0.6347199962980046` F=`None` tau=`1`
- `501`: count=`3` F_defined=`2` odd_lifts=`0` even_lifts=`3`
  - x=`6812597` y=`17781526790` odd_lift=`False` delta_frac=`0.489367315811654` F=`48693935` tau=`1`
  - x=`48693935` y=`339791341082` odd_lift=`False` delta_frac=`0.1443757282608005` F=`296551` tau=`1`
  - x=`296551` y=`161491284` odd_lift=`False` delta_frac=`0.6347199962980046` F=`None` tau=`1`
- `1517`: count=`1` F_defined=`0` odd_lifts=`0` even_lifts=`1`
  - x=`43916043` y=`291028018566` odd_lift=`False` delta_frac=`0.7383918518704307` F=`None` tau=`1`
- `6187`: count=`2` F_defined=`1` odd_lifts=`0` even_lifts=`2`
  - x=`3955183437` y=`248742471750750` odd_lift=`False` delta_frac=`0.49931775246018784` F=`62634329559` tau=`1`
  - x=`62634329559` y=`15675400641582836` odd_lift=`False` delta_frac=`0.22631099915238137` F=`None` tau=`1`

## 37 crossing map

- x=`3375` y=`196069` F=`9317` F_gt_x=`True` tau=`2`
- x=`9317` y=`899319` F=`2233` F_gt_x=`False` tau=`3`
- x=`2233` y=`105519` F=`None` F_gt_x=`None` tau=`2`

## Existing Lean (unchanged)

- `CubeOddLanding`: `True`
- `cube_odd_lift`: `True`
- `cube_lift_even_reset`: `True`
- `cube_lift_odd_ge_fourth`: `True`
- `cube_lift_odd_continues`: `True`
- `odd_preimage_unique`: `True`
- `EnvelopeState`: `True`
- `envelope_lt_pow`: `True`
- `even_below_anchor_pow`: `True`
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
- independent_crossing_defect: `False`
- stable_crossing_map: `False`
- cube_crossing_lean: `False`
- sigma_automaton: `False`
- z5_reopen: `False`
- power_cell_chain: `False`

## Decision

**CUBE_CROSSING_CLOSED**

delta parity is generic odd-odd; unique preimage is odd_preimage_unique; F is not defined on a stable class and moves both ways; even-return cannot apply after an odd lift because y already left the cube band.

