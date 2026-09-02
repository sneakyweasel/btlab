# Juggler multi-step itinerary-parity census

Status: **COMPUTATIONALLY VERIFIED** counts; every depth-4 word
class is **EXACT — HUMAN PROOF**
(`J-nested-parity-discrepancy`, `J-triple-parity-discrepancy`,
`J-even-branch-third-letter`, `J-four-step-descent-density`,
`J-depth4-slow-branch`, `J-kernel-cancellation`,
`J-depth4-complete`; proofs in
`juggler_two_step_parity_lemma.md`). Laboratory certified
descent density 7/8 (Phase 27 length-5 repair). Paper B
prints 13/16. Length-7/8 harvest rows stay CONJECTURE
(Phase 26). OOOO* kernel isolated (Lemma V1); the
scale-invariant copy of Theorem R, the increment-first
K3 attack, and X1-absorption of K3 are **REFUTED**;
the K3 toolkit is **PARKED**.

Exact census of the joint parity itinerary of the first four itinerary
letters on odd starts. Phase-0 falsifier for iterating the one-step
discrepancy bound (Theorem 5.1 in the finite-dynamics note) to
depth two and beyond. Not a frequency theorem, not a predictive
state, not a termination claim.

Window: odd `n <= 10000000`. Expected class fraction of a
depth-`d` word within odd starts is `2^{-(d-1)}`.

| depth | max|D_w| on window | max|D|/N^{1/2} | max|D|/N^{1/3} | fitted exponent |
| --- | --- | --- | --- | --- |
| 2 | 195.0 | 0.061664 | 0.90511 | 0.2841 |
| 3 | 1156.5 | 0.365717 | 5.367997 | 0.625 |
| 4 | 3020.75 | 0.955245 | 14.021079 | 0.6634 |

Depth-4 counts at `N = 10000000` (odds = 4999999):

| word | count | D_w |
| --- | --- | --- |
| OEEE | 625279 | 279.125 |
| OEEO | 624031 | -968.875 |
| OEOE | 625515 | 515.125 |
| OEOO | 625279 | 279.125 |
| OOEE | 625193 | 193.125 |
| OOEO | 625551 | 551.125 |
| OOOE | 625236 | 236.125 |
| OOOO | 623915 | -1084.875 |

## OOEE class

`OOEE` count 625193 = 0.125039 of odd
starts (product density 0.125). Every census
OOEE start satisfied the four-step descent `T^4(n) < n`
(violations: 0); this instantiates the
contraction `3^2 < 2^4` and is a guard, not a new theorem.

## Reading

The fitted exponents are envelope slopes on a geometric sample,
label **OBSERVATION**. The analytic statements they probe are
now theorems at every depth <= 4. Laboratory certified
descent density is 7/8 (J-five-step-descent-density,
Phase 27). Paper B prints 13/16. Length-7/8 densities
57/64 and 29/32 stay CONJECTURE (Phase 26 holes).
The OOOO* kernel K3 is isolated and the
scale-invariant copy of Theorem R, the increment-first K3
attack, and X1-absorption of K3 are REFUTED; the K3 toolkit is
PARKED.
