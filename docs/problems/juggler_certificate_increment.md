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

`independent`. This is a laboratory question about a laboratory quantity. The
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

The `1/d` correction does not have the size the measured exponent `-3/2`
predicts. Under `N_d/2^d ~ psi(frac(d*beta)) * theta^d * d^(-3/2)` the increment
expands as `a + b/d` with `b = (3/2) * theta * psi_d/psi_(d-1)`, giving
`b` near `1.45`; the fits give `b` from `1.93` to `3.01`, varying by class, while
`b/a` is nearly constant at `40.8`. Either `psi` carries its own `1/d` structure
that compensates, or the expansion is too crude, or the exponent is not `-3/2`.
**This is a tension and not a refutation of the shape**, and it is the first
quantitative check the shape has had beyond the direct measurement.

## Decision

`CLOSE` — the question is answered, negatively and decisively, and the route it
was testing (derive the almost-periodic prefactor from the recursion alone) is
shut. Recorded in [negative_knowledge.md](../negative_knowledge.md). Best next
question, and the one this opened: the `b/a` constancy at `40.8` across classes
whose `a` varies by 60% is not explained by the `d^(-3/2)` expansion. What is it?

## Publication assessment

Status: `EXPLORATORY`. A checked negative about a laboratory quantity, plus a
quantitative tension worth carrying. No theorem, no density, no bound.
