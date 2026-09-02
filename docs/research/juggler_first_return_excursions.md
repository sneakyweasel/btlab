# Juggler first-return excursion frontier

Status: **EXCURSION_COMPLEX**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Studies observed first-return-below
excursions. A horizon miss is not a bound on tau. Does not reopen
PE-factor, residual-future, sum-rho, realization-set, landing-image,
or N_w-boundary branches.

## Branch budget

```text
Mathematical target     Does first-return maximality force a new relation?
Novelty hypothesis      H1–H5 margin / peak / G-profile / final step / class
Falsifier               T<n, 2^k>3^o, or floorPower_odd_ge restated
Existing machinery      _walk_returns, floorPower_odd_ge, power_bound_contracts
Maximum Phase-0 scope   n=2..4000; extremal profiles only
```

## Metadata

- window: `n=2..4000`
- engine control layer modified: `False`
- classification: **EXCURSION_COMPLEX**
- sorry-free: `True`

H1–H3 and H5 fail. H4 (final E, n<=y<n^2) is floorPower_odd_ge plus isqrt. The G_j pattern is the parked first formally contracting prefix. Maximality adds no new exact relation beyond T^tau(n)<n and the existing envelope.

## A. Coverage

- starts: `3999` returned `3999` horizon-miss `0` bit-cap promoted `[2183, 3431]`
- tau range: `1` … `77`
- distinct first-return words: `272`
- even starts are word E: `True`
- maximality (prefix>=n and final<n): `True`

## B. H1 return margin

- holds: `False` — M>=1 is the definition of a strict return; every stronger F(k,o) fails
- min M: `{'n': 2, 'M': 1, 'word': 'E'}`
- min M/n: `{'n': 425, 'M': 60, 'ratio': '12/85', 'word': 'OOOOOOOEOOEEOOOEOEEOOEOOOOOEEEEOOOOOOOEEEOEOEE'}`
- counterexamples: `{'M>=k': {'n': 3, 'word': 'OOOEE', 'M': 1, 'k': 5, 'o': 3, 'gap': 5}, 'M>=o': {'n': 3, 'word': 'OOOEE', 'M': 1, 'k': 5, 'o': 3, 'gap': 5}, 'M>=|gap|': {'n': 3, 'word': 'OOOEE', 'M': 1, 'k': 5, 'o': 3, 'gap': 5}, 'M>=k-o': {'n': 3, 'word': 'OOOEE', 'M': 1, 'k': 5, 'o': 3, 'gap': 5}}`

## C. H2 peak

- holds: `False` — even starts have peak=n and word E; odd peaks exceed any n-independent word bound
- even peak = n: `True`
- largest odd peak bits: `{'n': 2183, 'tau': 54, 'peak_bits': 19694, 'word': 'OOEOOOOEOOOOOOOOEOOOEOOOOOOOEOOOEEEOOOEEEEEEOEEOEEOOEE'}`

## D. H3 prefix slack

- holds: `False` — G_j<=0 on proper prefixes and G_tau>0 is the known first formally contracting prefix, already parked as EXCURSION_ENVELOPE_GREEN
- prefix-NC then G>0: `True`
- single sign-change count: `1999`
- extra sign changes: `None`

## E. H4 final step

- computationally true: `True`
- novelty: `REPARAMETERIZATION` — final letter E and n<=y<n^2 follow from floorPower_odd_ge (odd steps cannot descend) plus z=isqrt(y)<n
- E-final: `3999` odd-final `0` bad-cell `0`

## F. H5 extremals / Pareto

- holds: `False` — min-margin, min-ratio, max-duration, and max-peak sit in different word classes
- lexicographic extremals: `{'min_M': {'n': 2, 'M': 1, 'word': 'E'}, 'min_M/n': {'n': 425, 'M': 60, 'ratio': '12/85', 'word': 'OOOOOOOEOOEEOOOEOEEOOEOOOOOEEEEOOOOOOOEEEOEOEE'}, 'max_tau': {'n': 3889, 'tau': 77, 'word': 'OOOOOEOEOOOEOOEOEOEOOOOOOEOOOEOEOOOEOOOOOEEOEOEEOEOEEOOOEEOEOOEEOOEEOOOOOEEEE'}, 'max_peak_bits': {'n': 2183, 'tau': 54, 'peak_bits': 19694, 'word': 'OOEOOOOEOOOOOOOOEOOOEOOOOOOOEOOOEEEOOOEEEEEEOEEOEEOOEE'}}`
- Pareto count (min M/n, max peak bits, max tau): `10`
- Pareto records: `[{'n': 425, 'tau': 46, 'M': 60, 'ratio': '12/85', 'peak_bits': 243, 'word': 'OOOOOOOEOOEEOOOEOEEOOEOOOOOEEEEOOOOOOOEEEOEOEE'}, {'n': 557, 'tau': 27, 'M': 119, 'ratio': '119/557', 'peak_bits': 888, 'word': 'OOOOOEOOOOOOOOEOEOEEEOEEOEE'}, {'n': 2183, 'tau': 54, 'M': 950, 'ratio': '950/2183', 'peak_bits': 19694, 'word': 'OOEOOOOEOOOOOOOOEOOOEOOOOOOOEOOOEEEOOOEEEEEEOEEOEEOOEE'}, {'n': 761, 'tau': 62, 'M': 421, 'ratio': '421/761', 'peak_bits': 851, 'word': 'OOOOOOOOOEEOEOEEOOEEOOOEOOOOEOOOEOEOOOEEOOOOEOOOOEEEOOOEEEEOEE'}, {'n': 193, 'tau': 70, 'M': 113, 'ratio': '113/193', 'peak_bits': 900, 'word': 'OOOEOOOOOOOEOOOEEOEEOOOOOOEEEOOOEOOEEOOOOOEOOOOEEOOEOOEOEEOOEOOEEOEEEE'}, {'n': 3439, 'tau': 62, 'M': 2158, 'ratio': '2158/3439', 'peak_bits': 1045, 'word': 'OOOOOOOOOOEOEOOEOOOEEOOEEOOOEEOOEOEOOOOEOOEEOOOOOEEEOEOEOEOEEE'}, {'n': 3547, 'tau': 70, 'M': 2633, 'ratio': '2633/3547', 'peak_bits': 1049, 'word': 'OOOEOOOEOOOOOOOOEEEEOOOOOEOEEOEOOOOOOOEOEOOEEOOOOEEOEOEOOOEEEOOOEOEEEE'}, {'n': 3973, 'tau': 59, 'M': 3326, 'ratio': '3326/3973', 'peak_bits': 1890, 'word': 'OOOOOOOEOOOOEEOOOOOOEOEOOEEOEOOOOOEOEOEOEOOOOEEEEEEOOOOEEEE'}, {'n': 3271, 'tau': 69, 'M': 3181, 'ratio': '3181/3271', 'peak_bits': 2460, 'word': 'OOEOOOOOOOEOEOOOOOOEEEEOEOOOOOOEEOOOEOOOOOOEEOEOOOOEEEEOEEOEEOOOEEOEE'}, {'n': 3889, 'tau': 77, 'M': 3811, 'ratio': '3811/3889', 'peak_bits': 3350, 'word': 'OOOOOEOEOOOEOOEOEOEOOOOOOEOOOEOEOOOEOOOOOEEOEOEEOEOEEOOOEEOEOOEEOOEEOOOOOEEEE'}]`

## G. Same word / same (k,o) / same run

- multi-start words: `49`
- margin varies on an itinerary: `{'word': 'OOEE', 'n_starts': 255, 'min_M': 3, 'max_M': 3878}`
- (k,o) groups that split M: `28`
- strongest (k,o) split: `{'k': 15, 'o': 9, 'min_M': 29, 'max_M': 3691, 'n_words': 21}`
- run-signature groups that split M: `51`
- strongest run-signature split: `{'runs': (4, 3, 2), 'min_M': 21, 'max_M': 3615, 'n_words': 3}`

## H. Extremal profiles (slack / defect / return state)

- n=`2` tau=`1` first_defect=`0` final_defect=`1` word=`E` G_tail=`[1]` s_tail=`[0, -1]`
- n=`3` tau=`5` first_defect=`0` final_defect=`2` word=`OOOEE` G_tail=`[-1, -5, -19, -11, 5]` s_tail=`[8, 33, 3, -1]`
- n=`7` tau=`2` first_defect=`0` final_defect=`2` word=`OE` G_tail=`[-1, 1]` s_tail=`[0, 11, -3]`
- n=`193` tau=`70` first_defect=`0` final_defect=`98` word=`OOOEOOOOOOOEOOOEEOEEOOOOOOEEEOOOEOOEEOOOOOEOOOOEEOOEOOEOEEOOEOOEEOEEEE` G_tail=`[-291363479247117974395, -910983925888773026417, -837196949593934819953, -689622997004258407025, -394475091824905581169, 195820718533800070543]` s_tail=`[1783719959438849, 42233915, 6305, -113]`
- n=`425` tau=`46` first_defect=`0` final_defect=`701` word=`OOOOOOOEOOEEOOOEOEEOOEOOOOOEEEEOOOOOOOEEEOEOEE` G_tail=`[-5426574229435, -18478745943857, -14080699432753, -51038191320467, -33446005276051, 1738366812781]` s_tail=`[6851662, 17936359191, 133501, -60]`
- n=`2183` tau=`54` first_defect=`0` final_defect=`1457` word=`OOEOOOOEOOOOOOOOEOOOEOOOOOOOEOOOEEEOOOEEEEEEOEEOEEOOEE` G_tail=`[-1290070235430529, -727120282009217, -3307260752870275, -12173582072296073, -7669982444925577, 1337216809815415]` s_tail=`[175032018, 2315711083209, 1519563, -950]`
- n=`3889` tau=`77` first_defect=`0` final_defect=`78` word=`OOOOOEOEOOOEOOEOEOEOOOOOOEOOOEOEOOOEOOOOOEEOEOEEOEOEEOOOEEOEOOEEOOEEOOOOOEEEE` G_tail=`[-21866447876087858074091, -70321710111133219435969, -60876977145393929008577, -41987511213915348153793, -4208579350958186444225, 71349284374956136974911]` s_tail=`[1442307256457799, 37973831, 2273, -3811]`

## Lean

- `floorPower_odd_ge`: `True`
- `power_bound_contracts`: `True`
- no forbidden engines: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- tau_always_finite: `False`
- reopen_pe_factors: `False`
- reopen_residual_quotient: `False`
- reopen_sum_rho: `False`
- reopen_realization_geometry: `False`
- reopen_landing_image: `False`
- reopen_nc_boundary: `False`
- automaton: `False`

## I. Structural findings

- first-return maximality on observed returns: **COMPUTATIONALLY VERIFIED**
- even starts are the single letter `E`: **COMPUTATIONALLY VERIFIED**
- odd steps cannot descend: **EXACT — LEAN VERIFIED** (`floorPower_odd_ge`)
- formally contracting itineraries satisfy `T_w(n)<n` for `n>1`: **EXACT — LEAN VERIFIED** (`power_bound_contracts`)
- observed first-return words are the first formally contracting prefix: **COMPUTATIONALLY VERIFIED** (parked `EXCURSION_ENVELOPE_GREEN`)
- H1 margin law stronger than `M>=1`: **REFUTED** (`OOOEE` at 3)
- H2 peak law stronger than the envelope: **REFUTED** (`n=2183`, 19694-bit peak)
- H3 new `G_j` grammar: **REPARAMETERIZATION** of the parked envelope census
- H4 final `E` and `n<=y<n^2`: **REPARAMETERIZATION** of `floorPower_odd_ge` plus `isqrt`
- H5 single extremal class: **REFUTED** (lex records and the Pareto front split)
- first-return word determines margin: **REFUTED** (`OOEE`)
- H6 recursive reduction: not attempted
- candidate conjectures: none

## Decision

**CLOSE** — `EXCURSION_COMPLEX`

H1–H3 and H5 fail. H4 (final E, n<=y<n^2) is floorPower_odd_ge plus isqrt. The G_j pattern is the parked first formally contracting prefix. Maximality adds no new exact relation beyond T^tau(n)<n and the existing envelope.

This is not a halt result and not a proof that tau is finite.

