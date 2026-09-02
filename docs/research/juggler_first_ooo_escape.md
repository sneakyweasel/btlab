# Juggler first OOO after controlled OOE

Status: **FIRST_OOO_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. The first odd run of length at
least 3 after the a0=2 first-internal-OO corridor. Not Z5,
not a length-11 assembler, and not a terminal-cluster reopen.

## Branch budget

```text
Mathematical target     first OOO entrance after OOE.{OE,OOE}*
Novelty hypothesis      a narrow pre-OOO corridor C_3(n)
Existing machinery      OOEOOE square cell; (OOE)^k gap;
                        no_cycleMin_prefix_ooe_oe
Maximum Phase-0 scope   language envelope; first-OOO event;
                        no Lean
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **FIRST_OOO_GREEN**
- sorry-free: `True`
- (OOE)^k square max: `5`
- gaps: `{'OOEO': True, 'OOEOE': True, 'OOEOOE': True, 'OOEOOO': False, 'OOEOOOE': True, 'OOEOOEOOE': True, 'OOEOOEOOO': False, 'OOEOOEOOOE': False, 'ooe_k_le_5': True, 'ooe_k_6': False, 'next_o_k_le_2': True, 'next_o_k_3': False, 'lang_q5': True, 'lang_q6': False, 'lang_q6_p1': True}`
- cube fail / OO fail: `0` / `0`
- exits: `{'drop': 92, 'OOO': 12}`
- OOO by OOE-count: `{'1': 11, '2': 1}`
- OOO pre in [n,n^2) / T^2 >= n^2: `12` / `12`
- max OOE before exit: `4`
- early OE drop / late OE: `30` / `3`

first OOO from x >= n has T^2(x) >= n^2; (OOE)^k stays below n^2 iff k <= 5; early OE drops; OOO is not inevitable.

## Attack 1 — language envelope

`(OOE)^k` has the square-cell gap iff `k <= 5`. The next-O
refinement `3*(9/8)^k < 4` holds iff `k <= 2`. The language
`{OE,OOE}* ` has no common sub-`n^2` envelope: `q = 6` needs
at least one `OE`. `OOEO` still has the gap (`32 > 27`), so
the first `OE` after one `OOE` drops. `OOEOOO` is the first
OOO-prefix that loses the gap; completed `OOEOOOE` restores it.

## Attack 2 — first OOO entrance

`isqrt(n^3)^3 >= n^4` for `n >= 3`. If `x >= n` follows `OO`,
then `T^2(x) >= n^2`. Every CycleMin first-OOO therefore loses
the square ceiling at the second odd letter. When that OOO
occurs after `k <= 5` copies of `OOE`, the entrance state lies
in `[n, n^2)`.

## Attack 3 — OOO is not inevitable

`365` does `(OOE)^4` then a late `OE` and drops, never hitting
`OOO`. After `k >= 3`, a following `OE` may survive one step
because the even intermediate is already `>= n^2`.

## Window samples

- n=`105` ooe=`1` oe=`0` pre3=`187`
- n=`173` ooe=`1` oe=`0` pre3=`329`
- n=`229` ooe=`1` oe=`0` pre3=`451`
- n=`269` ooe=`1` oe=`0` pre3=`541`
- n=`319` ooe=`1` oe=`0` pre3=`655`
- n=`483` ooe=`1` oe=`0` pre3=`1045`

## Named witnesses

- n=`365` exit=`drop` blocks=`OOEOOEOOEOOEOEE`
- n=`565` exit=`OOO` blocks=`OOEOOEOOO`
- n=`89` exit=`drop` blocks=`OOEOOEOE`
- n=`429` exit=`drop` blocks=`OOEOOEOOEOEE`
- n=`105` exit=`OOO` blocks=`OOEOOO`

## Lean

- `CycleMin`: `True`
- `cycleMin_not_end_odd`: `True`
- `power_bound_word`: `True`
- `power_bound_contracts`: `True`
- `oe_block_contracts`: `True`
- `no_cycleMin_ooeooe`: `True`
- `no_cycleMin_ooeoooe`: `True`
- `no_cycleMin_prefix_ooe_oe`: `True`
- `no_cycle_itinerary_ooe`: `True`
- `ooo_suffix_threshold`: `True`
- `isolated_oe_r_max_two`: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- length_eleven_census: `False`
- z5_cells: `False`
- four_even_assembler: `False`
- ooo_inevitable: `False`
- bounded_ooe_count: `False`

## Decision

**FIRST_OOO_GREEN**

first OOO from x >= n has T^2(x) >= n^2; (OOE)^k stays below n^2 iff k <= 5; early OE drops; OOO is not inevitable.

This is not a halt result, not a Z5 exclusion, and not a
length-11 assembler. Terminal clusters stay frozen.

