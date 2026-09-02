# Juggler PE-cell intersection

Status: **PE_PREIMAGE_INTERSECTION_PARK**

Standalone application phase. Not a Research Engine experiment,
not a PredClosure reopen, and not a halt theorem. The odd cell
I_y is tested against the PE predecessor envelope J(n).
Forward empty-cell laws are not re-tested.

## Branch budget

```text
Mathematical target     I_y ∩ J(n) empty is a PE-specific
                        Diophantine obstruction
Novelty hypothesis      PE envelope, not generic inversion
Falsifier               scale mismatch; Type II family;
                        leftover Type I is cube-gap sparsity
Existing machinery      odd_preimage_unique; even_preimage_iff;
                        empty_odd_cell Type 0/1/2
Maximum Phase-0 scope   leftover PE words; 69/89; OOE < 4000;
                        no new Lean; no R_{b,c}
```

## Metadata

- classification: **PE_PREIMAGE_INTERSECTION_PARK**
- leftover all Type I: `True`
- any Type III: `False`
- scale mismatch: `True`
- 365 landings: `[763, 1749, 4447, 12707]`
- 69 even cubes: `[[24]]`
- 89 even cubes: `[[], [44]]`
- OOE Type I/II/III: `{'I': 236, 'II': 9, 'III': 0}`

PE predecessors are even and occupy the square cell of y; I_y is the cube-root interval and never contains z; leftover landings are Type I by generic cube gap; a Type II OOE family exists (199 and others) whose odd pred is not the PE state.

## Controls

- n=`365` 763(I,δ=107), 1749(I,δ=505), 4447(I,δ=6499), 12707(I,δ=23435)
- n=`501` 1089(I,δ=1439), 133347(I,δ=104381), 1749(I,δ=505), 4447(I,δ=6499), 12707(I,δ=23435)
- n=`1517` 3789(I,δ=5509), 10613(I,δ=799), 33811(I,δ=52129), 2493(I,δ=2039)
- n=`6187` 18425(I,δ=11033), 15771571(I,δ=19942709)

## Contrast

- n=`69` 117(I,cubes=[24])
- n=`89` 155(I,cubes=[]), 291(I,cubes=[44])

## Existing machinery

- `odd_preimage_unique`: I_y contains at most one integer; never many predecessors
- `even_preimage_iff`: the PE predecessor z lives in [y^2, (y+1)^2)
- `floorPower_odd_eq_iff_cube_interval`: I_y is the cube-root interval, scale y^{2/3}
- `OddPredEmpty`: Type 0 or 1 of empty_odd_cell; already PARKED as a forward law
- `J(n)`: T_u(n) for a PE word ending in E is even and cannot lie in I_y

## Existing Lean (unchanged)

- `odd_preimage_unique`: `True`
- `odd_preimage_iff`: `True`
- `even_preimage_iff`: `True`
- `floorPower_odd_eq_iff_cube_interval`: `True`
- `floorPower_even_eq_iff_sq_interval`: `True`
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
- pe_odd_cell_impossible: `False`
- iy_meets_jn_new_obstruction: `False`
- n0_empty_pe_cells: `False`
- predclosure_reopened: `False`
- rbc_reopened: `False`

## Decision

**PE_PREIMAGE_INTERSECTION_PARK**

PE predecessors are even and occupy the square cell of y; I_y is the cube-root interval and never contains z; leftover landings are Type I by generic cube gap; a Type II OOE family exists (199 and others) whose odd pred is not the PE state.

This is not a halt result and not a PredClosure reopen.

