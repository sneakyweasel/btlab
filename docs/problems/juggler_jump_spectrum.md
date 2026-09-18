# Juggler: what are the jumps of the meander prefactor?

## Problem

The measured prefactor `psi` of `J-paper-b-meander-prefactor-is-almost-periodic`
is a function of the rotation coordinate `frac(d * beta)`, `beta = log2/log3`,
and it is discontinuous at every point of the orbit. What are the amplitudes?

## Exact statement

Write `N_d` for the count of length-`d` parity words no prefix of which
contracts, `theta = beta^(-beta) (1-beta)^(beta-1) / 2` for its exponential
rate, and

    psi(x) = lim N_d / (2 theta)^d * d^(3/2),   frac(d * beta) -> x.

Let `a_n = psi(frac(n*beta)^-) - psi(frac(n*beta)^+)`. The claim:

    a_n = a_1 * N_n / (2 theta)^(n-1),   n >= 1,

with `a_1` the single measured constant, and `a_0 = 2 theta a_1` the jump at
`x = 0`.

## Current literature

`independent`. A laboratory question about a laboratory quantity. The function
it is about is `J-paper-b-meander-prefactor-is-almost-periodic`; the shape it
sits inside is the `MeanderShape` hypothesis of `PaperBSurvivorAsymptotic`,
which no module proves.

## Branch budget

- **Target:** the jump amplitudes of `psi` at the rotation orbit.
- **Novelty hypothesis:** that they have a closed form rather than only a
  measured law.
- **Falsifier:** a fitted amplitude disagreeing with the closed form by more
  than the fit's own known bias.
- **Already killed by?:** none. The jump structure itself was only established
  in this cluster; the previous branch reached the barrier-index constants to
  about `j = 25` by local differencing and stopped there.
- **Existing machinery:** the `(length, oddCount)` program, the float-log
  prefactor profile, `psi` to `d = 1e6`, the recursion
  `N_(d+1) + M_(d+1) = 2 N_d`, and the empty-window theorem.
- **Maximum Phase-0 scope:** one probe, its test, this dossier, ledger rows, a
  journal entry, one Lean module for the combinatorial core.
- **Promotion criterion:** an exact identity verified two independent ways.
- **Stop criterion:** if the amplitudes stay fit-dependent, record the reach and
  `PARK`.

## Balanced-ternary formulation

Not used.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

The barrier word `s_m = ceil(m*beta) - ceil((m-1)*beta)`, extended to negative
`m`; the height profile of survivors above the barrier; the transposition of
two adjacent letters; the barrier mass, meaning the survivors sitting exactly
on the barrier.

## Experiments

`python -m research.juggler_sequence.jump_spectrum`.

**The mechanism.** `psi(x)` depends on `x` only through the barrier word read
backwards from `x`. The letter `i` steps back is `1` exactly when
`frac(x - i*beta) > 1 - beta`, so it switches as `x` crosses `frac((i-1)*beta)`
and again as `x` crosses `frac(i*beta)`. Crossing one orbit point therefore
moves two letters at once, and it moves them as a *transposition*: `odd, even`
becomes `even, odd`. The odd-count, hence the barrier, is unchanged.

Propagating both words gives profiles that agree at every height above the
barrier and differ at the barrier by exactly the mass standing on it -- a single
point mass, verified to `9e-308` against a float propagation. An odd letter
fixes that point mass, so the difference is the survivor problem itself, started
from one walker. Hence `a_n / a_1 = N_n / (2 theta)^(n-1)`.

**Two independent verifications.** A transfer-operator propagation from a
burn-in profile reproduces the identity to `2.3e-14` over `n <= 3000`, using no
measured data at all. Independently, modelling `psi` on `d` in `[2e5, 1e6]` as
its jumps plus the linear rise periodicity demands leaves one free amplitude,
and that amplitude reads `0.42629` -- stable to `5e-4` across `d`-subranges, to
`1e-4` across the number of modelled jumps from `1e4` to `1e6`, and to between
`0.03%` and `0.35%` against a freely fitted head amplitude for splits of the
spectrum at `n >= 5`. The tightest split, a head of three jumps, reads `1.4%`
high; below that the head carries too little of the variance to be pinned.

## Conjectures

None. The identity is exact; the one constant is measured.

## Counterexamples

None for the identity. Two for readings of it:

- **The `1/rho` law is trivial.** This cluster recorded that the amplitude ratio
  across a Sturmian zero is exactly `1/rho = 1.0352968376`. True, and now
  bit-exact at 184 zeros. But `rho` and `theta` are the same number under two
  names, a Sturmian zero is an even barrier letter, an even letter kills nothing
  and doubles the count, and `2/(2 theta)` is `1/theta`. The law carries no
  information beyond the empty-window theorem of `PaperBCertificateLengths`, and
  the two names are what made it look like a finding.
- **A global fit cannot reach `C_j`.** The stated motivation for the global fit
  was to reach the barrier-index constants past `j = 25`. It does not, and the
  reason is structural rather than statistical: the column a high-`n` jump
  contributes to the design is its own ramp minus its own staircase, which
  collapses toward zero as the jumps get fine. More data does not help, and the
  free-amplitude fits' errors are one-signed, growing with `j`, in both the
  number of modelled jumps and in `d`.

## Formalization

`formal/Problems/Juggler/PaperBJumpTransposition.lean`, 30 declarations, no
real number in any statement and nothing but `Nat` arithmetic.

*The objects.* `Profile` is a survivor count graded by height above the
barrier. `stepFlat` and `stepRise` are the two barrier letters acting on it,
with `stepFlat_zero`, `stepFlat_succ` and `stepRise_apply` the unfolding
lemmas. `barrierMass` is the point mass at height zero, with `barrierMass_zero`,
`barrierMass_succ` and `barrierMass_eq_ite`. `run` applies a whole barrier word,
unfolded by `run_nil`, `run_cons_true` and `run_cons_false`, and `total` sums a
profile over a height window.

*The exchange cost.* `stepRise_stepFlat_eq_add_barrierMass` is the whole
mechanism at one height: the two orders differ by exactly the barrier mass.
`stepFlat_stepRise_le` records that they are comparable, one dominating.
`stepFlat_add`, `stepRise_add` and `run_add` make a history linear, and
`run_stepRise_stepFlat` is the consequence -- transposing one adjacent pair
changes the whole later history by exactly the history of a point mass on the
barrier -- with `run_stepFlat_stepRise_le` its ordered form and
`total_run_stepRise_stepFlat` its reading through `total` (via `total_add`).
`stepRise_barrierMass` is why that history is the survivor problem itself: a
rising letter fixes the point mass.

*The letters, counted.* `total_succ`, `total_stepFlat` and `total_stepRise` give
the exact effect of each letter on a window, and the two corollaries are the
statements the amplitudes are read from: `total_stepFlat_eq_two_mul`, a flat
letter doubles -- this is the retracted `1/rho` law in its proper size -- and
`total_stepRise_add_barrierMass`, a rising letter doubles less the barrier mass.

What is not formalized, and is not close to it: that `psi` exists, that the
`d^(-3/2)` is right, and that the propagated difference converges to the jump.
Those are measured.

## Results

`J-paper-b-jump-spectrum-is-the-survivor-sequence` --
`COMPUTATIONALLY VERIFIED`. `a_n = a_1 N_n / (2 theta)^(n-1)`.

`J-paper-b-transposition-costs-the-barrier-mass` -- `EXACT — LEAN VERIFIED`.

`J-paper-b-jump-sum-is-the-meander-series` -- `COMPUTATIONALLY VERIFIED`. The
sum of the downward jumps is `2 theta a_1 (G(1) - 1)`, so the jump spectrum and
the one factor of the meander constant that `J-paper-b-meander-constant-derived`
leaves numerical are the same object.

`J-paper-b-sturmian-zero-law-is-the-empty-window` -- `REPARAMETERIZATION`.
Retracts the `1/rho` reading recorded in this cluster.

Three consequences follow immediately. `psi` is of bounded variation.
`a_n ~ 2 theta a_1 psi(frac(n*beta)) n^(-3/2)`, so the jump of `psi` at the
`n`-th orbit point is `psi` at that same point to a constant and a power.
`C_j = 2 a_1 theta^(1-j) N_n / 2^n` for any `n` with `ceil(n*beta) = j`, well
defined by the empty-window theorem and available at every `j`.

## Open questions

The jumps are not the function. Modelling `psi` as its jump spectrum plus the
linear rise leaves a residual of `1.35e-02` against a level-fit noise floor of
`4.4e-03`, and `89%` of that residual variance is a reproducible function of the
coordinate. It does not shrink with `d`, so it is structure in `psi` and not
finite-depth contamination. What that component is, this branch does not say.

`a_1` itself has no closed form here. The self-referential relation
`a_n = A psi(x_n) n^(-3/2)` together with periodicity is a fixed-point equation
for `psi` in which `A` is scale-invariant, so `A` is in principle determined by
the equation rather than by measurement. That is the obvious next question and
is not attempted here.

## Decision

`PROMOTE` -- an exact identity, verified two independent ways, that reduces a
measured spectrum to a sequence Paper B already owns and ties it to `G(1)`. The
retraction it carries is recorded in
[negative_knowledge.md](../negative_knowledge.md).

## Publication assessment

Status: `EXPLORATORY`. A closed form for a laboratory quantity, resting on a
Lean-verified finite identity and on measured asymptotics that are not proved.
No theorem about the Juggler map, no density, no bound.
