# Juggler near-extremal non-contracting prefixes

Status: **NEAR_EXTREMAL_STRUCTURE_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. The object is a finite prefix with
`G_j = 2^j - 3^{o_j} ≤ 0` that is not monochrome.

## Branch budget

```text
Mathematical target     realized non-extremal prefixes with G≤0
                        and Δ too small to force T^k(n)<n
Novelty hypothesis      a language obstruction or defect bound
Falsifier               arbitrarily long realized mixed prefix-NC
                        words that also avoid defect contraction
Existing machinery      PowerBound, compensated contraction, O^a E
Maximum Phase-0 scope   combinatorial prefix-NC tree; realized
                        scan; no new Lean unless a new inequality
```

## Metadata

- combinatorial `k <= 16`
- realized `n <= 2000`, `k <= 10`
- engine control layer modified: `False`
- classification: **NEAR_EXTREMAL_STRUCTURE_GREEN**
- sorry-free: `True`

prefix-noncontracting itineraries start with O, length ≥ 2 starts with OO, and include the unbounded mixed family O^k E for k≥2 plus other mixed patterns; defect-driven contraction is already Lean and did not fire on the realized mixed prefixes in range. A finite horizon hit is not an infinite family.

## Combinatorial prefix-NC language

- words: `5017`
- mixed: `5001`
- `O^k E` family: `14`
- other mixed: `4987`
- every itinerary starts with `O`: `True`
- length ≥ 2 starts with `OO`: `True`
- `E` is prefix-NC: `False`
- `OE` is prefix-NC: `False`
- `OOE` is prefix-NC: `True`

A single even step has `G=1>0`, so every prefix-NC word starts
odd. `OE` already has `G_2=1>0`. The mixed family `O^k E` for
`k≥2` is prefix-NC by `2^{k+1} ≤ 3^k`, already Lean as
`two_pow_succ_le_three_pow_iff`. Other mixed patterns exist
(sample `['OOOOOOOOOOOOOOEO', 'OOOOOOOOOOOOOOEE', 'OOOOOOOOOOOOOEO', 'OOOOOOOOOOOOOEOO', 'OOOOOOOOOOOOOEOE', 'OOOOOOOOOOOOOEE', 'OOOOOOOOOOOOOEEO', 'OOOOOOOOOOOOOEEE', 'OOOOOOOOOOOOEO', 'OOOOOOOOOOOOEOO', 'OOOOOOOOOOOOEOOO', 'OOOOOOOOOOOOEOOE', 'OOOOOOOOOOOOEOE', 'OOOOOOOOOOOOEOEO', 'OOOOOOOOOOOOEOEE', 'OOOOOOOOOOOOEE']`).

## Realized mixed prefixes

- mixed prefix-NC rows: `1541`
- max mixed prefix-NC length: `10`
- max opening odd run: `10`
- defect-driven certificates: `0`
- defect avoiders with known gap: `42`
- first contracting prefix defined: `1863`
- no contracting prefix in horizon: `136`
- max `τ`: `10`

Calibration: `n=3` realizes `OOOE` with image `6`; `τ(OE)=2`; `τ(EOO)=1` so `EOO` is not a bad prefix.

## Closest known avoiders of defect contraction

- n `155` word `OOE`: Δ `218485219853305754`, G_formal `51306726471060156250`, image `291`
- n `249` word `OOE`: Δ `16405931570391222713`, G_formal `3664767755095933504248`, image `496`
- n `191` word `OOE`: Δ `1955560860140947135`, G_formal `336527484273921100990`, image `368`
- n `85` word `OOE`: Δ `1423092791036469`, G_formal `228892041032812500`, image `148`
- n `197` word `OOE`: Δ `2868053562625631876`, G_formal `444616812294001522756`, image `381`
- n `117` word `OOE`: Δ `28149261888898901`, G_formal `4073285799929837556`, image `212`
- n `69` word `OOE`: Δ `337555077560388`, G_formal `34938289461147588`, image `117`
- n `157` word `OOE`: Δ `600155858833774332`, G_formal `57586650353448278556`, image `295`

## Longest realized mixed prefix-NC words

- n `37` `OOOOEOOOEE`: image `2233`, contracts `False`
- n `103` `OOOOEOEOOO`: image `7871516405498`, contracts `False`
- n `113` `OOOEOOOOOE`: image `14245160192996`, contracts `False`
- n `163` `OOOOOOEOEE`: image `53045`, contracts `False`
- n `173` `OOEOOOOOOO`: image `10191096955185724142110473921312275306979975`, contracts `False`
- n `193` `OOOEOOOOOO`: image `85357154459746972731761066262612011066679467`, contracts `False`
- n `205` `OOOOEOEOOE`: image `86551`, contracts `False`
- n `225` `OOOEOOOEEO`: image `105519`, contracts `False`
- n `229` `OOEOOOOOOO`: image `2231975102195274135015874268610969460017417753`, contracts `False`
- n `241` `OOOOOEOOOO`: image `6107677170787853046695207664967692662775828615`, contracts `False`
- n `265` `OOOOOEOOOE`: image `3356613790616152`, contracts `False`
- n `289` `OOOOOOOEEE`: image `180236`, contracts `False`

## Lean reused, not extended

- `power_bound_contracts`: `True`
- `power_bound_compensated_contracts`: `True`
- `power_bound_compensated_contracts_follows`: `True`
- `two_pow_succ_le_three_pow_iff`: `True`
- `power_bound_eq_iff_extremal`: `True`
- `PowerHeight` absent: `True`
- new `DefectContracts` structure absent: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**NEAR_EXTREMAL_STRUCTURE_GREEN**

prefix-noncontracting itineraries start with O, length ≥ 2 starts with OO, and include the unbounded mixed family O^k E for k≥2 plus other mixed patterns; defect-driven contraction is already Lean and did not fire on the realized mixed prefixes in range. A finite horizon hit is not an infinite family.

This is a finite-prefix language statement, not a global halt result.

