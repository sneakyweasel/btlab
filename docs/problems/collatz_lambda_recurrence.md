# Collatz: where lambda-recurrence sits on the trajectory

## Problem

Williams (arXiv:2607.01718, `williams-2026-collatz-coordinates`) writes every
odd `n` uniquely as `n = lambda * 2^a * 3^b - 1` with `gcd(lambda, 6) = 1` and
`a >= 1`. Her `lambda(n)` is `n + 1` stripped of its twos and threes, so
`lambda = 1` exactly when `n + 1` is 3-smooth. Her open problem (3) records
that every trajectory she tested reaches some `n` with `lambda(n) = 1`, notes
that this is implied by the Collatz conjecture, and asks whether proving it --
lambda-recurrence -- "might be easier than proving full convergence", and
whether the number of steps can be bounded.

The question this dossier answers is narrower and empirical: **where on the
trajectory does the event happen?** If it happens early, it is a genuinely
weaker milestone worth attacking. If it happens at the bottom, it is
convergence wearing a different hat.

## Exact statement

Counting Syracuse steps (`n` odd, next odd is the odd part of `3n + 1`), over
odd starts in `[3, 1e4)`, `[1e4, 1e5)`, `[1e5, 4e5)` and `[4e5, 1e6)`:

| quantity | value across the four ranges |
|---|---|
| mean `log2` of the first `lambda = 1` value, nontrivial starts | 4.365, 4.382, 4.395, 4.395 |
| share of nontrivial starts landing at `n* <= 63` | 83.9%, 83.1%, 83.1%, 83.2% |
| mean `collatz_time - lambda_time` | 14.78, 14.63, 14.77, 14.75 |
| mean `lambda_time` / mean `collatz_time` | 0.518, 0.623, 0.668, 0.693 |

So the landing value does not grow with the start -- the typical one is about
21 however large the start -- and the gap to convergence does not grow either,
while the times themselves grow from 30.7 to 48.1 and the ratio climbs toward
one. Five values (11, 7, 23, 47, 31) take 71 per cent of all nontrivial
landings below `1e6`.

The mechanism is a density statement and has nothing to do with Collatz: there
are 142 3-smooth numbers below `1e6` and 306 below `1e9`, densities `1.4e-4`
and `3.1e-7`, so an orbit of about fifty Syracuse steps near `1e6` expects
0.007 hits and near `1e9` essentially none. The orbit has to descend into the
range where `n + 1` is commonly 3-smooth before the event can happen.

## What this does not say

- **It is not a proof of equivalence.** The set of `lambda = 1` values is
  infinite, and from a large member such as `2^19 * 3 - 1` an orbit still has
  far to go. What is shown is that orbits do not land on those.
- **The gap is not bounded per trajectory.** Individual gaps run 0 to 80 below
  `1e6`. 27 is the instructive case: it reaches `lambda = 1` after two steps,
  at the value 31, and then takes 39 more steps to reach 1. The constancy is
  in the mean.
- **`lambda_time <= collatz_time` is trivial** and is not evidence of
  anything: `lam(1) = 1` because `1 + 1 = 2`, so arriving at 1 is itself an
  occurrence of the event. It was checked and then discarded as vacuous.

## Current literature

Williams 2026 is the source of the coordinate and of the open problem; see
`williams-2026-collatz-coordinates` and the negative-knowledge entry on
`claude/exponent-floor-3n1-2adic-mvwa96` recording that the `(lambda, a, b)`
coordinate is hers and not this laboratory's. Nothing here claims her
framework. Her open problems (1), (2) and (4) are untouched by this dossier;
(2) is answered inside her own paper.

## Branch budget

Target: say where the event sits, on measurement, and no more.
Novelty hypothesis: none about the coordinate; the placement measurement is new.
Falsifier: a range where the mean gap or the mean landing size grows with the start.
Already killed by?: no; her open problem (3) is open and stays open.
Existing machinery: `src/research/collatz/lambda_recurrence.py`, four tests.
Maximum scope: measurement and its density heuristic. No proof attempt.
Promotion criterion: a bound on the gap that is uniform rather than averaged.
Stop criterion: reached -- the placement question is answered; the open problem is not.

## Decision

`CLOSE` on the placement question. The answer to "is lambda-recurrence an
easier target" is: not for the reason one would hope. It is reached only after
the orbit has already collapsed, so a proof of it would have to contain
essentially a proof of descent. That is a reason to spend effort elsewhere,
not a theorem.

## Publication assessment

Status: `EXPLORATORY`.

Not a paper candidate. The placement measurement is new and the coordinate is
not; the result is a reason to spend effort elsewhere rather than a theorem,
and Lagarias's open problem (3) is untouched by it.
