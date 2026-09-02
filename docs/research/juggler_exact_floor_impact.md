# Juggler exact-floor impact

Phase-0 census of first-descent steps where the Juggler floor is a
no-op because the state is already an integer power (a perfect
square). Local exactness is the existing square package. This note
records the tagged events and their measured impact.

Classification **EXACT_FLOOR_IMPACT_KNOWN**.

## Bounds

- First-descent starts n <= 100000, step cap 40.
- PE subsample odd-odd n <= 4000.
- No GPU. No word-atlas recensus. No new Lean. No Paper A edit.

## Fixtures

- 9 -> 27: exact O, crumb 0, next letter O, isolated (27 is not a square).
- Orbit of 3: isolated exact E at 36, image 6, word `OOOEE`.
- 16 -> 4 -> 2 -> 1: even tower, start not isolated.

## Identity

- mismatches: `0`
- letter-force failures: `0`
- even-square walk increment failures: `0`
- exact events: `374` (isolated `356`, tower `18`)

## Density versus square baseline

| bin | letter | visited | exact | observed | baseline | ratio | ok |
|---|---|---|---|---|---|---|---|
| [2,10) | E | 4 | 1 | 25.000% | 49.223% | 0.508 | True |
| [2,10) | O | 4 | 1 | 25.000% | 43.397% | 0.576 | True |
| [10,100) | E | 45 | 3 | 6.667% | 15.441% | 0.432 | True |
| [10,100) | O | 45 | 3 | 6.667% | 15.192% | 0.439 | True |
| [100,1000) | E | 450 | 11 | 2.444% | 4.813% | 0.508 | True |
| [100,1000) | O | 446 | 11 | 2.466% | 4.800% | 0.514 | True |
| [1000,10000) | E | 4500 | 34 | 0.756% | 1.520% | 0.497 | True |
| [1000,10000) | O | 4443 | 32 | 0.720% | 1.521% | 0.474 | True |
| [10000,100000) | E | 45000 | 109 | 0.242% | 0.481% | 0.504 | True |
| [10000,100000) | O | 44454 | 105 | 0.236% | 0.481% | 0.492 | True |
| [100000,1000000) | E | 8658 | 8 | 0.092% | 0.190% | 0.487 | True |
| [100000,1000000) | O | 8423 | 9 | 0.107% | 0.189% | 0.564 | True |
| [1000000,10000000) | E | 11966 | 5 | 0.042% | 0.054% | 0.768 | True |
| [1000000,10000000) | O | 11539 | 2 | 0.017% | 0.054% | 0.320 | True |
| [10000000,100000000) | E | 17325 | 2 | 0.012% | 0.022% | 0.534 | True |
| [10000000,100000000) | O | 16728 | 3 | 0.018% | 0.022% | 0.830 | True |
| [100000000,1000000000000) | E | 23571 | 0 | 0.000% | 0.002% | 0.000 | True |
| [100000000,1000000000000) | O | 22450 | 2 | 0.009% | 0.002% | 4.146 | True |

## First-descent impact

- E-certificates: `50000` with exact descending even `158` (observed 0.316%, baseline 0.316%, ratio 1.000)
- class mix, start is a square: `{'E': 158, 'leftover': 116, 'OOEE': 36}`
- class mix, mid-path isolated exact: `{'leftover': 29, 'OOEE': 16, 'OE': 8}`
- class mix, no isolated exact: `{'E': 49842, 'OE': 25007, 'OOEE': 6124, 'leftover': 18056}`
- mid-isolated rate by class: `[{'cls': 'E', 'n': 50000, 'n_mid': 0, 'rate': 0.0, 'mean_len': 1.0}, {'cls': 'OE', 'n': 25015, 'n_mid': 8, 'rate': 0.00031980811513092144, 'mean_len': 2.0}, {'cls': 'OOEE', 'n': 6176, 'n_mid': 16, 'rate': 0.0025906735751295338, 'mean_len': 4.0}, {'cls': 'leftover', 'n': 18201, 'n_mid': 29, 'rate': 0.0015933190484039338, 'mean_len': 10.39558266029339}]`
- rates follow word length: `True`
- global TV (odd mid vs none): `0.3575`

| bin | n_mid | n_none | TV | ok |
|---|---|---|---|---|
| [100,1000) | 10 | 425 | 0.3200 | False |
| [1000,10000) | 11 | 4400 | 0.3286 | False |
| [10000,100000) | 28 | 44321 | 0.4009 | False |

## PE subsample

- PE starts: `275`
- exact hits on PE blocks: `8`
- not-square exact hits: `0`
- extra continuation (image ≠ cube / root): `0`

## Decision cue

Local identity, square-density ratios, E-certificate exact share,
size-matched mid-path class TV, and PE continuation all sit inside
the known package if classification is `EXACT_FLOOR_IMPACT_KNOWN`.

