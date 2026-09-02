# Juggler certificate-transition closure

Iterate `{E, OE, OOEE, R}` from each first-descent landing. Every realized descent is already `FiniteProgress`. Absence is `NOT OBSERVED WITHIN SEARCH BOUND`. Not a halt theorem.

- classification: `CERTIFICATE_TRANSITIONS_CLOSED`
- reason: every first descent is already FiniteProgress via finiteProgress_of_imageLt; the first certificate word is the Q-itinerary; R->R is a strictly decreasing landing quotient; the layer is a 4-letter label on T<n
- n_max: `20000`
- claim: `NOT OBSERVED WITHIN SEARCH BOUND`

## Certificate definitions

| C | Lean output | meaning |
|---|---|---|
| E | `even_finiteProgress` | even n≥2; landing `isqrt(n)<n` |
| OE | `odd_even_finiteProgress` | odd-to-even; landing `T^2(n)<n` |
| OOEE | `finiteProgress_of_imageLt` | first descent is exactly OOEE |
| R | `finiteProgress_of_imageLt` | leftover first descent |

R does not remain `AboveAnchor` after the leftover itinerary fires. The leftover itinerary is a descent.

## Coarse first certificates

`{'E': 10000, 'R': 3785, 'OOEE': 1225, 'OE': 4989}`

Q-itinerary identity on first words: `True`.

## Transition support

| from \ to | E | OE | OOEE | R |
|---|---|---|---|---|
| E | 1 | 1 | 1 | 1 |
| OE | 1 | 1 | 1 | 1 |
| OOEE | 1 | 1 | 1 | 1 |
| R | 1 | 1 | 1 | 1 |

## Transition counts

| from \ to | E | OE | OOEE | R |
|---|---|---|---|---|
| E | 30996 | 6139 | 2726 | 7592 |
| OE | 12016 | 4649 | 707 | 2942 |
| OOEE | 2763 | 1804 | 171 | 509 |
| R | 11677 | 2733 | 418 | 1113 |

R→R count: `1113`. Type A / Type B from a residual start: `3073` / `712`.

## Residual depth

max τ_R = `4` at n=`1891`. max interior R-run = `4` at n=`1891`. max d_C = `9`.

| X | max τ_R | n | max R-run | Type B |
|---|---|---|---|---|
| 200 | 2 | 163 | 2 | 3 |
| 2000 | 4 | 1891 | 4 | 70 |
| 20000 | 4 | 1891 | 4 | 712 |

## SCCs

`[['E', 'OE', 'OOEE', 'R']]`

Numerical landings are strictly decreasing, so any semantic SCC is a quotient artifact (Section 12A), not a numerical cycle.

## Laboratory sequences

| n | certificates | τ_R | first word |
|---|---|---|---|
| 37 | `R E E` | 1 | `OOOOEOOOEEOOEEE` |
| 69 | `R E R E` | 1 | `OOEOOEE` |
| 89 | `R E E E` | 1 | `OOEOOEOE` |
| 365 | `R E OOEE E` | 1 | `OOEOOEOOEOOEOEE` |
| 501 | `R E OOEE E` | 1 | `OOEOOOEOOEEOOEOOEOOEOEE` |
| 1517 | `R E OE OE E E` | 1 | `OOEOOEOOEOEOOOEE` |
| 6187 | `R OE OE E OE E E` | 1 | `OOEOOOEOOEEOE` |

## Forced compositions (window)

None. No pair forces a unique third certificate.

## Absorbing states

None in the transition graph. Every class has outgoing edges to all four classes. Semantically every certificate, including R, is already `FiniteProgress` at the current state.

## Strongest falsifiers

- C: first certificate word is the Q-itinerary.
- every descent is FiniteProgress via `finiteProgress_of_imageLt`.
- D: all 16 edges occur; residual concatenates freely at this alphabet.
- A does not arise: landings strictly decrease.
- E avoided: T<n is recorded as REPARAMETERIZATION, not a new theorem.

## Anti-overclaim

Not a termination calculus. Not `CertificateAutomaton.lean`. Not a reopen of Q-episode or source descent.

