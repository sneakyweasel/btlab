# Juggler minimal-anchor closure

Status: **MINIMAL_ANCHOR_PARK**

Standalone application phase. Not a Research Engine experiment,
not a PredClosure-from-1 reopen, and not a halt theorem.
The leftover odd-escape corridor is tested for a smaller
predecessor or a short structured return into `[1, n-1]`.

## Branch budget

```text
Mathematical target     leftover odd-escape episode of a
                        minimal-bad-looking control encodes a
                        smaller start or Pred_{E,OE,OOE,OOOE}(G)
Novelty hypothesis      unique to a minimal anchor, or inherited
Falsifier               no smaller analogue; no short return;
                        rank is not a potential
Existing machinery      AboveAnchor; ReturnBelow; PredEven/PredOdd;
                        PredClosure <-> ReachesOne (CLOSED);
                        odd_preimage_unique; even_below_anchor_pow
Maximum Phase-0 scope   365, 501, 1517, 6187; 69/89 contrast; no new Lean
```

## Metadata

- classification: **MINIMAL_ANCHOR_PARK**
- generators: `[365, 1517, 6187]`
- inherited: `[501]`
- 501 merges 365: `True`
- short structured return on 365/1517: `False`
- 6187 L-image OE drop: `True`
- rank is potential: `False`

365 and 1517 have a unique odd spine with no smaller predecessor and no short structured return; 501 inherits 365 at 763; 6187 exits by OE from the L-image 11189; corridor rank is not a potential; minimality adds nothing beyond AboveAnchor.

## Controls

- n=`365` word=`OOEOOEOOEOOEOEE` drop=`34` y=`6973` OE→`763` below=`False` merge=`none` empty_odd=`[763, 1749, 4447, 12707]` max_rank=`4` L=`False`
- n=`501` word=`OOEOOOEOOEEOOEOOEOOEOEE` drop=`34` y=`11213` OE→`1089` below=`False` merge=`idx 11 state 763 from 365` empty_odd=`[1089, 133347, 763, 1749, 4447, 12707]` max_rank=`5` L=`True`
- n=`1517` word=`OOEOOEOOEOEOOOEE` drop=`734` y=`59085` OE→`3789` below=`False` merge=`none` empty_odd=`[3789, 10613, 33811, 2493]` max_rank=`4` L=`False`
- n=`6187` word=`OOEOOOEOOEEOE` drop=`1087` y=`486653` OE→`18425` below=`False` merge=`none` empty_odd=`[18425, 15771571, 11189]` max_rank=`5` L=`True`

## Contrast

- 69 word=`OOEOOE` landing=`212` shared square trap=`True`
- 89 word=`OOEOOEOE` drop=`70` high merge=`None`

## Existing Lean (unchanged)

- `AboveAnchor`: `True`
- `finiteProgress_of_aboveAnchor_returnBelow`: `True`
- `predClosure_iff_good`: `True`
- `odd_preimage_unique`: `True`
- `Good`: `True`
- `Bad`: `True`
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
- smaller_bad_descent: `False`
- good_interval_closure: `False`
- corridor_rank_potential: `False`
- predclosure_reopened: `False`

## Decision

**MINIMAL_ANCHOR_PARK**

365 and 1517 have a unique odd spine with no smaller predecessor and no short structured return; 501 inherits 365 at 763; 6187 exits by OE from the L-image 11189; corridor rank is not a potential; minimality adds nothing beyond AboveAnchor.

This is not a halt result and not a PredClosure reopen.

