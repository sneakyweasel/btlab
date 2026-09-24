# Juggler `escape_rate`

Status: **CLOSE** (24 September 2026), with one promoted Lean corollary.
Clotho Phase-0: counting escapes instead of failures.

## Problem

Does counting escaping starts give a premise for excluding divergent orbits that
is weaker, and more reachable, than the failure rate?

## Exact statement

Let `E` be the set of starts whose orbit is unbounded (`EscapesToInfinity`). For
`e > 3/8`, does some route prove
`#{n in (y, 2y] : n odd, n in E} <= y (log y)^(-e)` for all large `y`, other than
through the failure rate or the live pressure hypothesis? By the corollary below,
such a bound excludes divergent orbits.

## Current literature

`extended`. Tao's almost-all theorem for Collatz controls orbit minima, not escape;
the Juggler escape set's structure is internal: `Escape.lean`
(`cycles_or_escapes`), `FateContagion.lean` (`escapes_backwardClosed`,
`escapes_forwardClosed`) and the flight branches. Ville's maximal inequality for
nonnegative supermartingales is classical.

## Branch budget

- **Target:** a premise on escapes that excludes divergent orbits and is not
  implied by, or equivalent to, the live pressure or the failure rate.
- **Novelty hypothesis:** escapes are a subset of failures and must grow, which
  might give them a signature that failures such as large-cycle basins lack.
- **Falsifier:** escape can be arbitrarily slow, so at any fixed depth an escaping
  start looks like a merely live start, and every counting handle needs parity
  control at unbounded depth.
- **Already killed by?:** partly. Tao dossier §10: the live pressure is the weakest
  hypothesis on the concentration route, and intermediate forms are
  reparameterizations. The [flights](../negative_knowledge/flights.md) record
  closes orbit-local exclusion, and
  [flight walk divergence](juggler_flight_walk_divergence.md) routes the flight
  frontier into the cycle and all-depth equidistribution programs. The
  escape-count form was not yet recorded.
- **Existing machinery:** `EscapesToInfinity`, `cycles_or_escapes`, escape
  contagion, the generic `tao_rate_implies_empty`, `logMass_growth` at `5/8`.
- **Maximum Phase-0 scope:** the Lean corollary from an escape rate, a fair-word
  check of Ville's bound, and a desk analysis of every counting handle.
- **Promotion criterion:** an escape premise visible at depth `O(log log y)` and
  not implied by live pressure.
- **Stop criterion:** slow escapes are indistinguishable from live starts at every
  fixed depth.

## Balanced-ternary formulation

None used.

## Why BT may be relevant

Not relevant to this question.

## Candidate operations / invariants

- The multiplier `rho_k = (3/2)^a (1/2)^b` of a word is a fair-coin martingale,
  and `log x_k = rho_k log x_0` along an actual orbit up to floor errors;
  **KNOWN** (Paper C's martingale identity).
- An escaping orbit tends to infinity: if it met a bounded set infinitely often, a
  value would repeat and the orbit would be periodic; **EXACT — HUMAN PROOF**
  (pigeonhole, as in `cycles_or_escapes`).

## Experiments

Probe `research.juggler_sequence.escape_rate`, output
`data/research/juggler/escape_rate/ville.json` with its manifest, test
`tests/research/juggler_sequence/test_escape_rate.py`. Exact rational dynamic
programming over fair binary words of length up to 60, thresholds
`R = 2, 4, 16, 256`. Every hitting frequency of `max_k rho_k >= R` lies below the
Ville bound `1/R` and increases with depth (at depth 40: `0.422 < 1/2`,
`0.196 < 1/4`, `0.047 < 1/16`, `0.0017 < 1/256`).

## Conjectures

None.

## Counterexamples

None.

## Formalization

`EscapeRate.lean`: `one_not_escapes`; `no_escape_of_escape_rate`, which applies the
generic Tao reduction to the forward-closed escape set with the OOEE contagion at
`5/8`; and `eventuallyCycles_of_escape_rate`, which adds `cycles_or_escapes`.
Kernel-checked with the standard axioms only; not in a paper build root.

## Results

**1. An escape rate above `3/8` excludes divergent orbits (EXACT — LEAN
VERIFIED).** If the odd escaping starts in `(y, 2y]` number at most
`y (log y)^(-e)` for some `e > 3/8` and all large `y`, no positive start escapes,
and every orbit is eventually periodic. The premise is weaker than the failure rate
of `J-ooee-tao-rate-termination`; the conclusion excludes escape only.

**2. Every counting handle on escapes needs unbounded depth.**

- *Depth-bounded signature.* An escaping start above the verified floor never
  enters it, so at depth `C log log y` it is a live start. Escape adds only
  unboundedness, which can take arbitrarily long to show. The only
  depth-bounded premise is the live pressure, the existing failure-side hypothesis.
- *Maximal inequality.* In the fair model Ville's inequality bounds the frequency
  of ever reaching height `H` from `(y, 2y]` by about `log y / log H`, and escaping
  starts reach every height. Transferring the bound to actual starts needs fair
  parity counts at every depth an orbit may use before climbing: the all-depth
  equidistribution program.
- *First moment.* A bound on the average log-height over `(y, 2y]` uniform in the
  step `k` is equivalent to the absence of escapes in that block, since an
  escaping start makes the average diverge. It restates the target.

## Open questions

None on this line beyond the all-depth equidistribution program already named by
the flight branches.

## Decision

**CLOSE** the escape-count route as a `REPARAMETERIZATION` of the all-depth
equidistribution program: its depth-bounded content is the live pressure, and its
natural maximal-inequality form needs fair parity at unbounded depth. **PROMOTE**
the Lean corollary `no_escape_of_escape_rate`, which records the reduction. Best
next question: none on the escape side that does not pass through all-depth
parity equidistribution; a new Clotho attempt needs a growth invariant of
escaping orbits that is visible at bounded depth.

## Publication assessment

Status: `STRUCTURAL`.
