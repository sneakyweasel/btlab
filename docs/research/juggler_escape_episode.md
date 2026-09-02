# Juggler escape-episode descent

Status: **ESCAPE_EPISODE_PARK**

Standalone application phase. Not a Research Engine experiment,
not a PredClosure reopen, and not a halt theorem. Leftover
AboveAnchor prefixes are partitioned into escape episodes.
Smaller-bad descent is not re-tested.

## Branch budget

```text
Mathematical target     leftover completed escape episode
                        lowers a well-founded quantity or
                        exactly recurs
Novelty hypothesis      episode first-passage / record min,
                        not whole-path rank or first-overshoot Pred
Falsifier               landings climb or oscillate; L frozen;
                        no recurrence; rank-return = even-reset
Existing machinery      AboveAnchor; ReturnBelow; HasFiniteStop;
                        even_below_anchor_pow; FiniteProgress
Maximum Phase-0 scope   365, 501, 1517, 6187; 69/89 contrast;
                        three episode cuts; no new Lean
```

## Metadata

- classification: **ESCAPE_EPISODE_PARK**
- 365 PE climb: `[763, 1749, 4447, 12707, 1196]`
- 1517 landings: `[3789, 10613, 33811, 2493, 539470]`
- rank-2 return drop: `False`
- landing descent law: `False`
- exact recurrence: `False`
- global L frozen: `True`
- first-below is drop: `True`
- rank-return = even-reset: `True`
- 69 landings: `[117, 212]`
- 89 landings: `[155, 291]`

even-reset and rank-return coincide and return to rank 2; PE landings climb or oscillate; global record min is frozen at n; first-below-anchor is the existing terminal drop; no exact episode recurrence; 69/89 show the same pattern.

## Controls

- n=`365` drop=`34` max_rank=`4` rank2 episodes=`5` landings=`[763, 1749, 4447, 12707, 1196]` peaks=`[3, 3, 3, 4, 3]` L_frozen=`True`
- n=`501` drop=`34` max_rank=`5` rank2 episodes=`7` landings=`[1089, 133347, 582916, 1749, 4447, 12707, 1196]` peaks=`[3, 4, 5, 3, 3, 4, 3]` L_frozen=`True`
- n=`1517` drop=`734` max_rank=`4` rank2 episodes=`5` landings=`[3789, 10613, 33811, 2493, 539470]` peaks=`[3, 3, 3, 3, 4]` L_frozen=`True`
- n=`6187` drop=`1087` max_rank=`5` rank2 episodes=`3` landings=`[18425, 15771571, 125201440]` peaks=`[3, 4, 5]` L_frozen=`True`

## Existing machinery

- `AboveAnchor`: every finite prefix of a leftover laboratory stays >= n
- `ReturnBelow`: first later word with image < n; the terminal drop only
- `HasFiniteStop`: the same terminal drop; FirstPassage does not cut mid-corridor
- `even_below_anchor_pow`: an even high state drops its own rank; the return stays rank 2
- `FiniteProgress`: emitted only by the terminal drop on these laboratories
- `trajectoryExponentGap`: Drift is an word-exponent predicate, not an episode rank
- `collapse_on_pow_two`: Collapse is an even-tower identity, not a PE landing law
- `cycles_or_escapes`: bounded recurrence is already a cycle; leftover prefixes are not recurrent

## Existing Lean (unchanged)

- `AboveAnchor`: `True`
- `ReturnBelow`: `True`
- `HasFiniteStop`: `True`
- `FiniteProgress`: `True`
- `even_below_anchor_pow`: `True`
- `finiteProgress_of_aboveAnchor_returnBelow`: `True`
- `cycles_or_escapes`: `True`
- `trajectoryExponentGap`: `True`
- `collapse_on_pow_two`: `True`
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
- episode_descent_dichotomy: `False`
- record_min_implies_recurrence: `False`
- even_reset_lowers_return_rank: `False`
- smaller_bad_descent: `False`
- predclosure_reopened: `False`

## Decision

**ESCAPE_EPISODE_PARK**

even-reset and rank-return coincide and return to rank 2; PE landings climb or oscillate; global record min is frozen at n; first-below-anchor is the existing terminal drop; no exact episode recurrence; 69/89 show the same pattern.

This is not a halt result and not a PredClosure reopen.

