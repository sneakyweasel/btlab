# Juggler empty-odd-preimage PE landings

Status: **EMPTY_ODD_PREIMAGE_PARK**

Standalone application phase. Not a Research Engine experiment,
not a PredClosure reopen, and not a halt theorem.
PE landings with no odd predecessor are tested for an exact
emptiness criterion and a forward transition law.

## Branch budget

```text
Mathematical target     exact OddPredEmpty, and whether PE
                        landings with empty odd cells force a
                        forward transition law
Novelty hypothesis      emptiness is a geometric state with a
                        local map, not just a missing pred
Falsifier               generic width; no next-step restriction;
                        reduces to odd_preimage_unique
Existing machinery      odd_preimage_unique; odd_preimage_iff; pred_odd;
                        leftover controls; AboveAnchor
Maximum Phase-0 scope   cube iff; Type 0/1/2; 365/501/1517/6187;
                        no new Lean
```

## Metadata

- classification: **EMPTY_ODD_PREIMAGE_PARK**
- cube mismatches: `0`
- ambient Type 0 share: `0.8525641025641025`
- leftover all Type 0: `True`
- mixed next parity: `True`
- offset span: `[0.037640740566259955, 0.9220932520165257]`

OddPredEmpty is the cube test k=ceil_cbrt(x^2), k^3>=(x+1)^2 or k even; leftover PE landings are Type 0 because emptiness is generic; an odd step always makes T(x) Type 2 regardless of emptiness; no next-parity or square-cell restriction.

## Controls

- n=`365` word=`OOEOOEOOEOOEOEE` kinds=`[0, 0, 0, 0, 0]` offset=`0.07007203667321546`..`0.9220932520165257` odd_next=`[1, 1, 1, 0]`
- n=`501` word=`OOEOOOEOOEEOOEOOEOOEOEE` kinds=`[0, 0, 0, 0, 0, 0, 0]` offset=`0.14432695055730208`..`0.9220932520165257` odd_next=`[1, 1, 1, 1, 0]`
- n=`1517` word=`OOEOOEOOEOEOOOEE` kinds=`[0, 0, 0, 0, 0]` offset=`0.037640740566259955`..`0.7708767726956804` odd_next=`[1, 1, 0, 1]`
- n=`6187` word=`OOEOOOEOOEEOE` kinds=`[0, 0, 0, 0]` offset=`0.2536282160427699`..`0.9108045977011494` odd_next=`[1, 1, 0]`
- n=`69` word=`OOEOOEE` kinds=`[1, 0]` offset=`0.11294117647058824`..`0.1148936170212766` odd_next=`[1]`
- n=`89` word=`OOEOOEOE` kinds=`[0, 1, 2]` offset=`0.07032590051457976`..`0.8906752411575563` odd_next=`[1, 0]`

## Existing Lean (unchanged)

- `odd_preimage_unique`: `True`
- `odd_preimage_iff`: `True`
- `floorPower_odd_eq_iff_cube_interval`: `True`
- new Lean file: `False`
- Paper A has new API: `False`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- empty_forces_next_parity: `False`
- empty_forces_square_subinterval: `False`
- empty_persists_along_orbit: `False`
- predclosure_reopened: `False`

## Decision

**EMPTY_ODD_PREIMAGE_PARK**

OddPredEmpty is the cube test k=ceil_cbrt(x^2), k^3>=(x+1)^2 or k even; leftover PE landings are Type 0 because emptiness is generic; an odd step always makes T(x) Type 2 regardless of emptiness; no next-parity or square-cell restriction.

This is not a halt result and not a PredClosure reopen.

