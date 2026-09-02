# Juggler leftover-class certificate harvest

First contracting itinerary after Theorem 4.1 / `OOEE`. Absence is `NOT OBSERVED WITHIN SEARCH BOUND`. Not a halt theorem.

- classification: `CERTIFICATE_HARVEST_PARK`
- reason: leftover mass is a short mixed O/E-block list with small scale drift; a verification bound, not a new law
- n_max: `1000000000`
- k_max: `20`
- backend: `cuda`
- claim: `NOT OBSERVED WITHIN SEARCH BOUND`

## Coarse counts

| class | count |
|---|---|
| E | 500000000 |
| OE | 250000011 |
| OOEE | 62499595 |
| leftover | 148438571 |
| uncapped | 4058691 |
| overflow | 35003131 |
| long | 0 |

Leftover types: `3081`. Unary `O+E+` share: `0.2895`. `OOOO*` share: `0.0789`.

## Scale split

Total-variation of leftover itinerary shares: `0.0133`. Max abs delta: `0.0027`.

## Window `all` (2..1000000000)

Backend `cuda`. Leftover types `3081`.

| word | count | min n | signature | unary |
|---|---|---|---|---|
| `OOOEE` | 31262128 | 3 | `O3,E2` | True |
| `OOEOE` | 31261298 | 9 | `O2,E1,O1,E1` | False |
| `OOEOOEE` | 7815315 | 69 | `O2,E1,O2,E2` | False |
| `OOOEOEE` | 7814454 | 81 | `O3,E1,O1,E2` | False |
| `OOOOEEE` | 7806577 | 271 | `O4,E3` | True |
| `OOEOOEOE` | 3907733 | 89 | `O2,E1,O2,E1,O1,E1` | False |
| `OOEOOOEE` | 3906938 | 105 | `O2,E1,O3,E2` | False |
| `OOOEOEOE` | 3905864 | 629 | `O3,E1,O1,E1,O1,E1` | False |
| `OOOOOEEE` | 3905153 | 129 | `O5,E3` | True |
| `OOOEOOEE` | 3904519 | 99 | `O3,E1,O2,E2` | False |
| `OOOOEEOE` | 3904285 | 971 | `O4,E2,O1,E1` | False |
| `OOOOEOEE` | 3903863 | 519 | `O4,E1,O1,E2` | False |
| `OOEOOEOOEE` | 979330 | 2185 | `O2,E1,O2,E1,O2,E2` | False |
| `OOOOEOOEEE` | 976834 | 739 | `O4,E1,O2,E3` | False |
| `OOOEOOEOEE` | 976743 | 1849 | `O3,E1,O2,E1,O1,E2` | False |
| `OOOEOEOOEE` | 976688 | 77 | `O3,E1,O1,E1,O2,E2` | False |
| `OOOEOOOEEE` | 976579 | 183 | `O3,E1,O3,E3` | False |
| `OOOOOEOEEE` | 976444 | 165 | `O5,E1,O1,E3` | False |
| `OOEOOOOEEE` | 976396 | 2947 | `O2,E1,O4,E3` | False |
| `OOOOOEEOEE` | 975886 | 115 | `O5,E2,O1,E2` | False |

## Window `low` (2..100000000)

Backend `cuda`. Leftover types `3081`.

| word | count | min n | signature | unary |
|---|---|---|---|---|
| `OOEOE` | 3128561 | 9 | `O2,E1,O1,E1` | False |
| `OOOEE` | 3126146 | 3 | `O3,E2` | True |
| `OOEOOEE` | 782419 | 69 | `O2,E1,O2,E2` | False |
| `OOOEOEE` | 781884 | 81 | `O3,E1,O1,E2` | False |
| `OOOOEEE` | 780912 | 271 | `O4,E3` | True |
| `OOEOOEOE` | 391671 | 89 | `O2,E1,O2,E1,O1,E1` | False |
| `OOOOEEOE` | 390776 | 971 | `O4,E2,O1,E1` | False |
| `OOOEOEOE` | 390769 | 629 | `O3,E1,O1,E1,O1,E1` | False |
| `OOEOOOEE` | 390332 | 105 | `O2,E1,O3,E2` | False |
| `OOOEOOEE` | 390331 | 99 | `O3,E1,O2,E2` | False |
| `OOOOOEEE` | 390093 | 129 | `O5,E3` | True |
| `OOOOEOEE` | 389261 | 519 | `O4,E1,O1,E2` | False |
| `OOOEOOEOEE` | 97909 | 1849 | `O3,E1,O2,E1,O1,E2` | False |
| `OOOOOEEOEE` | 97875 | 115 | `O5,E2,O1,E2` | False |
| `OOOOOEOEEE` | 97736 | 165 | `O5,E1,O1,E3` | False |
| `OOEOOOOEEE` | 97655 | 2947 | `O2,E1,O4,E3` | False |
| `OOOEOEOOEE` | 97642 | 77 | `O3,E1,O1,E1,O2,E2` | False |
| `OOOEOOOEEE` | 97620 | 183 | `O3,E1,O3,E3` | False |
| `OOOOEEOOEE` | 97540 | 1555 | `O4,E2,O2,E2` | False |
| `OOEOOOEOEE` | 97470 | 319 | `O2,E1,O3,E1,O1,E2` | False |

## Window `high` (100000001..1000000000)

Backend `cuda`. Leftover types `2158`.

| word | count | min n | signature | unary |
|---|---|---|---|---|
| `OOOEE` | 28135982 | 100000175 | `O3,E2` | True |
| `OOEOE` | 28132737 | 100000171 | `O2,E1,O1,E1` | False |
| `OOEOOEE` | 7032896 | 100000179 | `O2,E1,O2,E2` | False |
| `OOOEOEE` | 7032570 | 100000317 | `O3,E1,O1,E2` | False |
| `OOOOEEE` | 7025665 | 100000193 | `O4,E3` | True |
| `OOEOOOEE` | 3516606 | 100001145 | `O2,E1,O3,E2` | False |
| `OOEOOEOE` | 3516062 | 100000187 | `O2,E1,O2,E1,O1,E1` | False |
| `OOOEOEOE` | 3515095 | 100000299 | `O3,E1,O1,E1,O1,E1` | False |
| `OOOOOEEE` | 3515060 | 100000287 | `O5,E3` | True |
| `OOOOEOEE` | 3514602 | 100000167 | `O4,E1,O1,E2` | False |
| `OOOEOOEE` | 3514188 | 100000721 | `O3,E1,O2,E2` | False |
| `OOOOEEOE` | 3513509 | 100000385 | `O4,E2,O1,E1` | False |
| `OOEOOEOOEE` | 882164 | 100000209 | `O2,E1,O2,E1,O2,E2` | False |
| `OOOOEOOEEE` | 879655 | 100001285 | `O4,E1,O2,E3` | False |
| `OOOEOEOOEE` | 879046 | 100001527 | `O3,E1,O1,E1,O2,E2` | False |
| `OOOEOOOEEE` | 878959 | 100000391 | `O3,E1,O3,E3` | False |
| `OOOEOOEOEE` | 878834 | 100000501 | `O3,E1,O2,E1,O1,E2` | False |
| `OOEOOOOEEE` | 878741 | 100001123 | `O2,E1,O4,E3` | False |
| `OOOOOEOEEE` | 878708 | 100000393 | `O5,E1,O1,E3` | False |
| `OOEOOOEOEE` | 878283 | 100000723 | `O2,E1,O3,E1,O1,E2` | False |

## Anti-overclaim

Not a termination theorem. Not a new atlas language. Not a density theorem unless classification is GREEN.

