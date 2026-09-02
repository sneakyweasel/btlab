# Juggler non-escape spine

Status: **NON_ESCAPE_SPINE_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Cycle-or-escape plus the CE
OOEOOE trap. Growing residual prefixes are not unbounded
orbits. Not Paper B, not escape-margin M, not bunched-short.

## Branch budget

```text
Mathematical target     MinimalNonTerm is a cycle or escape;
                        OOEOOE forces another OO on a CE
Novelty hypothesis      the even trap does not need image = n
Existing machinery      bounded_prefix_not_nodup; itineraryOOEOOE;
                        even_floorPower_lt_iff
Maximum Phase-0 scope   Lean Escape module; OOEOOE window;
                        one finite escape prefix
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **NON_ESCAPE_SPINE_GREEN**
- sorry-free: `True`
- square cells 64/81 and 128/243: `True` / `True`
- OOEOOE followers: `12`
- even land / survive: `4` / `0`
- Case A / survive: `4` / `0`
- forced OO: `4`
- escape prefix: `[365, 763, 1749, 4447]`

every scanned OOEOOE follower either drops on an even landing or even z, or is forced onto another OO; 365->4447 is a finite escape prefix, not an unbounded orbit.

## Attack 1 — cycle or escape

A bounded orbit of length `M+2` in `[0, M]` repeats. That is
`EventuallyCycles`. The negation is `EscapesToInfinity`.
`ReachesOne` is the 1-cycle. On `MinimalNonTerm` a cycle
stays `>= n`.

## Attack 2 — OOEOOE without CycleMin return

`power_bound_word` gives `x^{64} <= n^{81}`, so `x < n^2`.
An even landing drops. The next odd image satisfies
`z^{128} <= n^{243}`, so `z < n^2`. An even `z` drops. A CE
is therefore forced onto another `OO`.

## Attack 3 — finite escape prefixes

The chain `[365, 763, 1749, 4447]` grows and follows `OOEOOE`.
It is a finite residual prefix, not a proof of escape and
not an unbounded orbit.

## Window samples

- n=`69` x=`212` z=`14` even_x=`True` forced_oo=`False`
- n=`89` x=`291` z=`4964` even_x=`False` forced_oo=`False`
- n=`109` x=`376` z=`19` even_x=`True` forced_oo=`False`
- n=`111` x=`385` z=`7554` even_x=`False` forced_oo=`False`
- n=`349` x=`1651` z=`67084` even_x=`False` forced_oo=`False`
- n=`365` x=`1749` z=`73145` even_x=`False` forced_oo=`True`
- n=`429` x=`2145` z=`99343` even_x=`False` forced_oo=`True`
- n=`431` x=`2156` z=`46` even_x=`True` forced_oo=`False`

## Lean

- `EscapesToInfinity`: `True`
- `EventuallyCycles`: `True`
- `not_escapes_iff_bounded`: `True`
- `bounded_trajectory_eventually_cycles`: `True`
- `cycles_or_escapes`: `True`
- `reachesOne_implies_eventually_cycles`: `True`
- `minimal_nonterm_cycles_or_escapes`: `True`
- `follows_ooeooe_image_lt_sq`: `True`
- `follows_ooeooeo_image_lt_sq`: `True`
- `minimal_ooeooe_not_even_landing`: `True`
- `minimal_ooeooe_forces_oo`: `True`
- `finiteProgress_of_ooeooe_even_landing`: `True`
- `no_nontrivial_cycle_no_bounded_nonterm`: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- no_escape: `False`
- length_eleven_census: `False`
- escape_margin_is_new_progress: `False`

## Decision

**NON_ESCAPE_SPINE_GREEN**

every scanned OOEOOE follower either drops on an even landing or even z, or is forced onto another OO; 365->4447 is a finite escape prefix, not an unbounded orbit.

This is not a halt result, not a cycle exclusion, and not
`FiniteCoeffStopConjecture`.

