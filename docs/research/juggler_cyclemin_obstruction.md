# Juggler CycleMin / first-even obstruction

Status: **CYCLEMIN_OBSTRUCTION_GREEN**

Standalone application phase. Not a leftover-cell census, not Z5,
not a length-11 assembler, and not a termination theorem.

## Branch budget

```text
Mathematical target     After current CycleMin filters, what residual
                        family remains, and is there a finite
                        last-cluster split?
Novelty hypothesis      suffix type, not word length, is the
                        unavoidable pattern; OOO upgrades to (n+1)^3
Falsifier               a CycleMin-shaped word outside the split,
                        or the cube/transport inequalities fail
Existing machinery      CycleMin; OO/OOO thresholds; overshoot;
                        bootstrap; leftover suffixes; e<=3
Maximum Phase-0 scope   symbolic last-cluster classification;
                        exact cube/transport inequalities;
                        no Z5, no length-11 assembler
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **CYCLEMIN_OBSTRUCTION_GREEN**
- word count: `23037`
- class counts: `{'bootstrap_last_gap': 10947, 'last_two_even_eoe': 1805, 'last_two_even_ee': 1805, 'bunched_short_last_cluster': 6338, 'last_three_even_bunched': 2142}`
- residual family count: `42`
- e=4 short cluster types: `7`
- e>=5 family count: `28`
- cube upgrade: `True`
- transport holds: `True`
- universal local-overshoot A: `2`

every scanned CycleMin-shaped expanding word hits bootstrap, a last two-even leftover, a last three-even bunched family, or a bunched-short last cluster; OOO residual is (n+1)^3; internal OO transports the next residual to (y+1)^2

## Residual families

- e=4 last=[0, 0] front_internal_OO=False count=16
- e=4 last=[0, 0] front_internal_OO=True count=32
- e=4 last=[0, 1] front_internal_OO=False count=16
- e=4 last=[0, 1] front_internal_OO=True count=24
- e=4 last=[1, 0] front_internal_OO=False count=16
- e=4 last=[1, 0] front_internal_OO=True count=24
- e=4 last=[1, 1] front_internal_OO=False count=16
- e=4 last=[1, 1] front_internal_OO=True count=16
- e=4 last=[2, 0] front_internal_OO=False count=16
- e=4 last=[2, 0] front_internal_OO=True count=16
- e=4 last=[2, 1] front_internal_OO=False count=16
- e=4 last=[2, 1] front_internal_OO=True count=8
- e=4 last=[3, 0] front_internal_OO=False count=16
- e=4 last=[3, 0] front_internal_OO=True count=8
- e=5 last=[0, 0] front_internal_OO=False count=24
- e=5 last=[0, 0] front_internal_OO=True count=264
- e=5 last=[0, 1] front_internal_OO=False count=24
- e=5 last=[0, 1] front_internal_OO=True count=201
- e=5 last=[1, 0] front_internal_OO=False count=24
- e=5 last=[1, 0] front_internal_OO=True count=201
- e=5 last=[1, 1] front_internal_OO=False count=24
- e=5 last=[1, 1] front_internal_OO=True count=144
- e=5 last=[2, 0] front_internal_OO=False count=24
- e=5 last=[2, 0] front_internal_OO=True count=144
- e=5 last=[2, 1] front_internal_OO=False count=24
- e=5 last=[2, 1] front_internal_OO=True count=93
- e=5 last=[3, 0] front_internal_OO=False count=24
- e=5 last=[3, 0] front_internal_OO=True count=93
- e=6 last=[0, 0] front_internal_OO=False count=32
- e=6 last=[0, 0] front_internal_OO=True count=1098
- e=6 last=[0, 1] front_internal_OO=False count=32
- e=6 last=[0, 1] front_internal_OO=True count=808
- e=6 last=[1, 0] front_internal_OO=False count=32
- e=6 last=[1, 0] front_internal_OO=True count=808
- e=6 last=[1, 1] front_internal_OO=False count=32
- e=6 last=[1, 1] front_internal_OO=True count=564
- e=6 last=[2, 0] front_internal_OO=False count=32
- e=6 last=[2, 0] front_internal_OO=True count=564
- e=6 last=[2, 1] front_internal_OO=False count=32
- e=6 last=[2, 1] front_internal_OO=True count=362
- e=6 last=[3, 0] front_internal_OO=False count=32
- e=6 last=[3, 0] front_internal_OO=True count=362

## Cube and transport

- OO holds on `50010` odd starts in 5..200000
- OOO cube holds on `25065` / `25065`
- closest cube gap: `{'n': 25, 'z3': 52214, 'cube': 17576, 'gap': 34638}`
- transport hits: `1905` holds: `1905`
- second residual still outside the last-even cell: `1905`
- OE after OOE contracts: `156` expands: `0`

## Lean

- `CycleMin`: `True`
- `oo_suffix_threshold`: `True`
- `ooo_suffix_threshold`: `True`
- `odd_ge_succ_sq_floorPower_ge_cube`: `True`
- `ooo_residual_ge_cube`: `True`
- `cycleMin_ooo_residual_ge_cube`: `True`
- `cycleMin_transport_second_oo`: `True`
- `cycleMin_first_even_overshoots`: `True`
- `no_cycleMin_bootstrap_last_gap`: `True`
- `no_cycle_itinerary_even_count_le_three`: `True`
- `no_cycleMin_gapped_three_even_ee`: `True`
- `no_cycleMin_gapped_three_even_eoe`: `True`
- `no_cycle_itinerary_two_even_ee`: `True`
- `no_cycle_itinerary_two_even_eoe`: `True`
- `no_cycleMin_cyclemin_fudge`: `True`

- cube in Cells: `True`
- paper A untouched: `True`

## Anti-overclaim

- cycles impossible: `False`
- length-11 census: `False`
- four-even assembler: `False`
- Z5 cells: `False`
