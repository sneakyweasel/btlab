# Juggler PE-block walk

Status: **PE_WALK_PARK**

Standalone application phase. Not a Research Engine experiment,
not an OE-contracts reopen, not empty-cell dynamics, and not
a halt theorem. The leftover corridor is read as an O^a E walk.

## Branch budget

```text
Mathematical target     repeated PE recovery moves a forward
                        predictive anchor-relative quantity
Novelty hypothesis      landing/n, remainder, or envelope
                        predicts the next PE landing
Falsifier               same envelope, different next block;
                        no monotone scalar
Existing machinery      oe_block_contracts; power_bound_word;
                        AboveAnchor; leftover controls
Maximum Phase-0 scope   O^a E walk on 365/501/1517/6187;
                        no new Lean
```

## Metadata

- classification: **PE_WALK_PARK**
- ratio monotone on a leftover: `False`
- remainder monotone: `False`
- same alpha different next: `True`
- 365 after three OOE: `OOE`
- 1517 after three OOE: `OE`

the residual is an O^a E walk; landing/n and square remainder are not Lyapunov; the same envelope 729/512 is followed by OOE at 365 and OE at 1517; OE can drop the state and stay above the anchor.

## Controls

- n=`365` words=`['OOE', 'OOE', 'OOE', 'OOE', 'OE', 'E']` landings=`[763, 1749, 4447, 12707, 1196, 34]` alphas=`['9/8', '81/64', '729/512', '6561/4096', '19683/16384', '19683/32768']`
- n=`501` words=`['OOE', 'OOOE', 'OOE', 'E', 'OOE', 'OOE', 'OOE', 'OE', 'E']` landings=`[1089, 133347, 582916, 763, 1749, 4447, 12707, 1196, 34]` alphas=`['9/8', '243/128', '2187/1024', '2187/2048', '19683/16384', '177147/131072', '1594323/1048576', '4782969/4194304', '4782969/8388608']`
- n=`1517` words=`['OOE', 'OOE', 'OOE', 'OE', 'OOOE', 'E']` landings=`[3789, 10613, 33811, 2493, 539470, 734]` alphas=`['9/8', '81/64', '729/512', '2187/2048', '59049/32768', '59049/65536']`
- n=`6187` words=`['OOE', 'OOOE', 'OOE', 'E', 'OE']` landings=`[18425, 15771571, 125201440, 11189, 1087]` alphas=`['9/8', '243/128', '2187/1024', '2187/2048', '6561/8192']`
- n=`69` words=`['OOE', 'OOE', 'E']` landings=`[117, 212, 14]` alphas=`['9/8', '81/64', '81/128']`
- n=`89` words=`['OOE', 'OOE', 'OE']` landings=`[155, 291, 70]` alphas=`['9/8', '81/64', '243/256']`

## Existing Lean (unchanged)

- `itineraryOE`: `True`
- `oe_block_contracts`: `True`
- `repeated_oe_scale`: `True`
- `power_bound_word`: `True`
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
- oe_contracts_implies_halt: `False`
- landing_ratio_lyapunov: `False`
- envelope_predicts_next_block: `False`
- empty_cell_reopened: `False`

## Decision

**PE_WALK_PARK**

the residual is an O^a E walk; landing/n and square remainder are not Lyapunov; the same envelope 729/512 is followed by OOE at 365 and OE at 1517; OE can drop the state and stay above the anchor.

This is not a halt result and not an OE-frequency theorem.

