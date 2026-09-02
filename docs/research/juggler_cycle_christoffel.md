# Juggler cycle Christoffel maximizers

Status: **CYCLE_CHRISTOFFEL_CLOSED**

Fernández–Ibáñez unique-maximizer combinatorics, without Lebel
modular sieving and without the Collatz affine equation.
Not a halt theorem. Not a leftover-itinerary census. No new Lean.

## Metadata

- classification: **CYCLE_CHRISTOFFEL_CLOSED**
- identifications hold: `True`
- L=38 is the square of L=19: `True`
- slogan false: `True`
- L=11 leftover family: `30` contains Christoffel `True` histogram `0:1, 2:16, 4:13`
- L=19 CycleMin count: `12376` median Hamming `6` radius 0 `7` radius <= 2 `389`
- L=19 isolated-even family: `462`

leftover-itinerary / CycleMin candidates are not a one-parameter Christoffel necklace: the thirty L=11 leftovers include Christoffel and 4 Hamming, family 30 versus necklace 4; L=19 CycleMin weight-12 has 12376 words, median cyclic Hamming 6, radius 0 only 7; the isolated-even worst-m family has 462 words. Finance is word-order-independent. Lebel sieving was not used. Cycle-only near-Christoffel rigidity is not claimed refuted.

## Christoffel words at leftover lengths

- L=`11` o=`7` even=`4` kind=`intermediate` balanced=`True` maxO=`2` maxE=`1` m=`4` necklace=`4` start=`OOEOOEOOEOE`
- L=`19` o=`12` even=`7` kind=`principal` balanced=`True` maxO=`2` maxE=`1` m=`7` necklace=`7` start=`OOEOOEOOEOEOOEOOEOE`
- L=`38` o=`24` even=`14` kind=`double` balanced=`True` maxO=`2` maxE=`1` m=`14` necklace=`7` start=`OOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOE`
- L=`84` o=`53` even=`31` kind=`principal` balanced=`True` maxO=`2` maxE=`1` m=`31` necklace=`31` start=`OOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOEOOEOOEOE`
- L=`569` o=`359` even=`210` kind=`intermediate` balanced=`True` maxO=`2` maxE=`1` m=`210` necklace=`210` start=`OOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOEOOEO`
- L=`1054` o=`665` even=`389` kind=`principal` balanced=`True` maxO=`2` maxE=`1` m=`389` necklace=`389` start=`OOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOOEOOEOEOOEO`

## L=11 leftover-itinerary cells versus Christoffel 7/11

- Christoffel: `OOEOOEOOEOE`
- thirty first-expanding short-gap leftovers, all length 11
- cyclic Hamming histogram: `0:1, 2:16, 4:13`
- contains the Christoffel word: `True`
- CycleMin weight-7 census: `84` histogram `0:4, 2:49, 4:31`

## L=19 CycleMin weight-12 versus Christoffel 12/19

- Christoffel: `OOEOOEOOEOEOOEOOEOE`
- CycleMin orientations: `12376` histogram `0:7, 2:382, 4:3580, 6:7766, 8:641`
- median cyclic Hamming: `6`
- isolated-even (max E-run 1, worst m): `462` histogram `0:7, 2:49, 4:196, 6:203, 8:7`
- words with max O-run 2: `27`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- halt_theorem: `False`
- no_cycle_all_lengths: `False`
- new_lean: `False`
- lebel_modular_sieving: `False`
- monochrome_reopened: `False`
- affine_equation: `False`
- leftover_word_census: `False`

## Decision

**CYCLE_CHRISTOFFEL_CLOSED**

leftover-itinerary / CycleMin candidates are not a one-parameter Christoffel necklace: the thirty L=11 leftovers include Christoffel and 4 Hamming, family 30 versus necklace 4; L=19 CycleMin weight-12 has 12376 words, median cyclic Hamming 6, radius 0 only 7; the isolated-even worst-m family has 462 words. Finance is word-order-independent. Lebel sieving was not used. Cycle-only near-Christoffel rigidity is not claimed refuted.

