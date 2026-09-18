# Juggler: is the certificate increment a rotation function?

## Problem

Whether the per-step death rate of Paper B's survivors is a function of the
rotation coordinate `frac(d * beta)` alone, `beta = log2/log3`.

## Exact statement

Let `N_d` count the length-`d` parity words no prefix of which contracts and
`M_d` the minimal certificates of length `d`. By
`J-paper-b-survivor-certificate-recursion`, `N_(d+1) + M_(d+1) = 2 N_d`, so

    N_d = 2^d * prod_(k<=d) (1 - r_k),   r_k = M_k / (2 N_(k-1)),

and `r_k` is the fraction of survivors dying at step `k`. The question: is
`r_d = F(frac(d * beta))` for some `F`?

If it were, the product above would be almost-periodic outright and the
prefactor of `J-paper-b-meander-prefactor-is-almost-periodic` would follow from
the recursion rather than needing a local limit theorem.

## Current literature

**Corrected 18 September 2026.** An earlier reading here said `independent`.
The counting sequence underneath this branch is **OEIS A076227**, a Collatz
quantity known since 2002 -- see `J-paper-b-survivors-are-oeis-a076227`. The
*question* asked here, whether the increment is a function of the rotation
coordinate, remains a laboratory question about it. The
measured prefactor it bears on is
`J-paper-b-meander-prefactor-is-almost-periodic`; the shape it is tested against
is the `MeanderShape` hypothesis of `PaperBSurvivorAsymptotic`, which no module
proves.

## Branch budget

- **Target:** is `r_d` a function of `frac(d * beta)` alone?
- **Novelty hypothesis:** none mathematically. The value is in the answer being
  decidable from counts already available, and negative.
- **Falsifier:** residue classes mod a convergent denominator holding one value
  of `r_d` to within what the residual coordinate motion explains.
- **Already killed by?:** none; the question is new with the recursion.
- **Existing machinery:** the `(length, oddCount)` dynamic program, which is
  exact integer arithmetic and reproduces the brute-force enumeration.
- **Maximum Phase-0 scope:** one probe, its test, this dossier, a ledger row and
  a negative-knowledge entry.
- **Promotion criterion:** a decisive answer either way on a statistic that is
  not threshold-tuned.
- **Stop criterion:** if the classes are too thin to separate `d`-motion from
  coordinate motion, `PARK`.

## Balanced-ternary formulation

Not used.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

The increment `r_d`; residue classes modulo a convergent denominator of `beta`,
which fix the rotation coordinate; monotonicity in `d` within a class.

## Experiments

`python -m research.juggler_sequence.certificate_increment`. The dynamic program
over `(length, oddCount)` is exact in integers and reproduces the enumerated
`N_1..9 = 1,1,2,3,4,8,13,19,38` and
`M_1..16 = 1,1,0,1,2,0,3,7,0,12,0,30,85,0,173,476`.

Depths to 3000, fits on `d >= 1000`, residue classes mod `485` -- the denominator
of the convergent `306/485`, which fixes the coordinate to `9.3e-4`. 306 classes
carry four or five depths each.

Result: **every one of the 306 classes is strictly monotone in `d`.** Scattered
values would be monotone by chance about two to eight percent of the time. The
median within-class spread is `9.9e-4` against a median `a + b/d` fit residual of
`3.2e-6`, a factor of 309, and 264 of 306 classes exceed tenfold what the
residual coordinate motion can explain (`6.5e-5`, the limiting function's slope
`-0.070` times the `9.3e-4` drift).

A coarser period (`84`, coordinate fixed to `1.9e-3`) sees the same effect at
85% monotonicity; it is the resolution that falls off, not the effect.

## Conjectures

None.

## Counterexamples

The refutation itself. The clearest single witness: at `d = 300, 785, 1270` --
one class, coordinate fixed to `9.3e-4` -- the increment reads `0.05279228`,
`0.04912429`, `0.04821094`, monotone decreasing, a spread of `4.6e-3` against a
`6.5e-5` drift bound.

## Formalization

None, and none is appropriate: this is a measurement about asymptotics. The
recursion it rests on is Lean-verified in
`formal/Problems/Juggler/PaperBCertificateRecursion.lean`, and the tests assert
that the dynamic program satisfies it at every depth to 400.

## Results

`J-paper-b-increment-is-not-a-rotation-function` —
`COMPUTATIONALLY VERIFIED` / `REFUTED`.

`r_d` is not a function of `frac(d * beta)` alone. It carries a `1/d` correction,
fitted to a residual of `3.2e-6` in the median class.

## Open questions

**Answered 18 September 2026; see the Correction below.** The `1/d`
correction does not have the size the measured exponent `-3/2`
predicts. Under `N_d/2^d ~ psi(frac(d*beta)) * theta^d * d^(-3/2)` the increment
expands as `a + b/d` with `b = (3/2) * theta * psi_d/psi_(d-1)`, giving `b` near
`1.45`; the fits give larger values that vary by class. **This is a tension and
not a refutation of the shape.**

**Correction, same day.** An earlier reading of this branch called `b/a`
"nearly constant at 40.8" and proposed explaining that number. Both halves were
wrong, and the way they were wrong is worth recording:

- Over *all* 305 classes `b/a` is not constant: it scatters by 125% at two fit
  parameters and by far more at three. The apparent constancy came from six to
  eight classes chosen by eye after seeing the numbers, which is how one
  manufactures a constant rather than finds one.
- On an objectively defined well-conditioned subset (fit residual below `1e-5`,
  225 of 305 classes, a criterion on the fit and not on the answer) `b/a` does
  cluster, at `40.98` with a `1.0%` spread. But adding a `1/d^2` term moves it to
  `42.70`, a `4.2%` shift, while the limit `a` barely moves. So `b/a` is
  determined to a few percent at best.

A few percent identifies no closed form. `13*pi = 40.84` sits inside the
two-parameter value and outside the three-parameter one, which is the signature
of numerology rather than of a constant.

**Resolved, 18 September 2026.** The tension was this method, and neither
reading of `b` was measuring anything. Once `psi`'s jump spectrum is known
(`J-paper-b-jump-spectrum-is-the-survivor-sequence`) the shape's prediction has
no free parameter at all: `r_d = 1 - theta t_d/t_(d-1)` exactly, so within a
fixed coordinate `r_d = a + b/d` with `b = (3/2)(1 - a)`, and the testable
statement is `b/(1-a) = 3/2`.

But a class modulo `q` fixes the coordinate only to `delta = |frac(q beta)|`,
and `psi` is a jump function on a dense orbit, so it varies across the class by
about `17 sqrt(delta)` -- a square root more than the method assumes. At `485`
that is `4.8%` of `psi`, against a `1/d` signal of a few percent at the depths
used here. Across convergent denominators `65, 84, 485, 1054, 24727, 50508` the
coordinate drift falls from `1.0e-2` to `6.6e-6`, `psi`'s variation from `1.74`
to `0.044`, and the interquartile spread of `b/(1-a)` collapses from `51` to
`1.06` while the median goes from chaos to `2.22` and then `1.99`, extrapolating
to `1.59` against the predicted `1.50`.

So the tension is withdrawn as evidence about the shape. It is **not**
confirmation of the shape either: `b` is still unmeasured, and on this evidence
cannot be measured at any depth reachable here, since fixing the coordinate
tightly enough needs a class finer than the sample can fill. The general form of
the lesson is `J-residue-classes-lose-a-square-root-on-jump-functions`.

Where pi does belong in this cluster is settled and elsewhere:
`J-paper-b-meander-constant-derived` derives `kappa = 1/(sqrt(2*pi)*theta*sigma)`,
the `sqrt(2*pi)` being the non-lattice local limit theorem for
`S_n = o*log3 - n*log2`, whose step ratio is irrational; a second `sqrt(pi)`
enters through the Wiener-Hopf singularity `-2*sqrt(pi)*kappa*sqrt(1-z)` whose
coefficient extraction produces the `d^(-3/2)` itself. Pi and the exponent are
one fact, and neither is in `b/a`.

## Decision

`CLOSE` — the question is answered, negatively and decisively, and the route it
was testing (derive the almost-periodic prefactor from the recursion alone) is
shut. Recorded in [negative_knowledge.md](../negative_knowledge.md). Best next
question, after the correction above removed the one this branch first proposed:
`G(1) = sum_d N_d/(2*rho)^d` is the single factor of the meander constant that
`J-paper-b-meander-constant-derived` leaves numerical (`~7.07`) while `kappa`,
`sigma^2` and `theta*` are all closed. The recursion of this cluster rewrites it
as `sum_d prod_(k<=d) (1 - r_k) / rho^d`, a product-form series. Does that form
evaluate?

## Publication assessment

Status: `EXPLORATORY`. A checked negative about a laboratory quantity, plus a
quantitative tension worth carrying. No theorem, no density, no bound.
