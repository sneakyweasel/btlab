# Juggler failure margin: the tilted momentum that the conjecture's failure forces

Status: **CLOSE** (an exact calibration of the no-momentum hypothesis;
no estimate of the map)

Not a new hypothesis, not a census, not a third formulation. The
objects are Paper C Theorem 9.2, Proposition 9.3 and
`J-tao-rate-implies-conjecture`, combined in their contrapositive.

## Problem

If the conjecture is false, by how much must the tilted odd share of
live starts exceed \(q\), on average over the Tao depths? And is that
amount within reach of the pressure census?

## Exact statement

**Proposition (EXACT — HUMAN PROOF, elementary).** Let
\(p_C=(1-1/C)\log2/\log3\), \(\theta=\log\bigl(p_C(1-q)/(q(1-p_C))\bigr)\),
\(a_{\theta,q}=1+(e^\theta-1)q\), \(c_\theta=(e^\theta-1)/a_{\theta,q}\),
\(d=\lceil CL\rceil\), and \(e_*=1-\lambda^{**}=0.5074\). If the
conjecture is false then for every \(\varepsilon>0\) there are
infinitely many \(y\) with
\[
\frac1d\sum_{t<d}\bigl(s_\theta(t)-q\bigr)^+\ \ge\ m(C,q)-\varepsilon,
\qquad
m(C,q)=\frac{D(p_C\,\|\,q)-e_*\ln2/C}{c_\theta}.
\]

*Proof.* Theorem 9.2 gives \(\#\{\tau>d\}\le e^{-\theta p_Cd}\sum_{\tau>d}e^{\theta o_d}\)
unconditionally; Proposition 9.3 gives
\(\sum_{\tau>d}e^{\theta o_d}\le Ne^\theta a_{\theta,q}^{d-1}\exp(c_\theta\sum_{t<d}(s_\theta(t)-q)^+)\)
unconditionally; `J-tao-rate-implies-conjecture` says the count
\(\le y(\log y)^{-e}\) for all large \(y\) with \(e>e_*\) implies the
conjecture, so its failure gives \(\#\{\tau>d\}>y(\log y)^{-e_*-\varepsilon}\)
infinitely often. Take logs; \(\theta p_C-\ln a_{\theta,q}=D(p_C\|q)\)
at this \(\theta\), and \(\ln\log y=L\ln2+O(1)\). \(\square\)

## Current literature

- Paper C §9 / Tao note §10 — `known`: the three ingredients; the
  least \(C\) per \(q\) (`least_C_pressure`: \(19,41,214\) at
  \(q=0.5,0.55,0.6\) for the current \(e_*\)) is exactly where \(m\)
  becomes positive.
- The pressure census (`tao_reduction.pressure_census`, depth \(40\),
  \(\pm0.06\)) — `known`; this branch prices its depth against the
  margin.

## Branch budget

```text
Mathematical target     The per-step tilted excess that failure forces,
                        as a function of (C, q), and whether the census
                        depth and resolution can see it.
Novelty hypothesis      The margin is a clean closed form and is small.
Falsifier               None; the statement is an identity.
Existing machinery      kl_bernoulli, p_of_C, scale_L of tao_reduction.
Maximum Phase-0 scope   One table; the census depth in units of L. No
                        census, no Lean, no note edit.
Promotion criterion     Not applicable: a calibration.
Stop criterion          The table is computed.
```

## Balanced-ternary formulation

None.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- The identity \(\theta p-\ln a_{\theta,q}=D(p\|q)\) at
  \(\theta=\log(p(1-q)/(q(1-p)))\) — **EXACT — HUMAN PROOF**
  (\(a_{\theta,q}=(1-q)/(1-p)\) at that \(\theta\)).
- The margin table and its limit — **COMPUTATIONALLY VERIFIED**
  (closed forms evaluated).

## Experiments

- Probe: `research.juggler_sequence.failure_margin`.
- Artifact: `data/research/juggler/failure_margin/summary.json`.
- Tests: `tests/research/juggler_sequence/test_failure_margin.py`.

## Conjectures

None new.

## Counterexamples

None.

## Formalization

The two unconditional ingredients are now kernel-checked on the
word-weight framework of `RateFreeDensity`
(`formal/Problems/Juggler/TiltedShare.lean`; axioms `propext`,
`Classical.choice`, `Quot.sound` only): `weightGen_succ_le_share` is
the one-depth telescoping \(Z_{d+1}\le Z_d(1+(x-1)s_d)\) with
`tiltedShare` the tilted odd share; `one_add_le_exp_excess` is
\(1+(x-1)s\le a_q\exp(c_q(s-q)^+)\); `weightGen_le_pressure` is
Proposition 9.3, \(Z_d\le Z_0a_q^d\exp(c_q\sum_{t<d}(s_t-q)^+)\); and
`count_le_pressure` joins it to the existing `weight_markov` for the
Tao-type count \(\le Z_0a_q^d\exp(\cdots)/x^k\). The only Juggler
input is `WeightSplit` (children carry at most the parent's weight),
which the live counts satisfy. `NoMomentum` states the hypothesis as
a proposition, `count_le_of_noMomentum` the count under it, and
`tilt_exponent_eq_kl` the identity \(\theta p-\ln a_{\theta,q}=D(p\|q)\)
at the re-centring tilt. The contagion rate theorem stays prose.

## Results

Classification **FAILURE_MARGIN_IS_SUB_PERCENT_AT_C20_AND_BELOW_CENSUS_RESOLUTION**.

```text
  m(C, q), the forced average tilted excess per step
  q      C=20    C=25    C=30    C=43    C=50    C=100   C=230   C=1000   C->inf
  0.50   0.58%   2.00%   2.87%   4.11%   4.49%   5.59%   6.18%   6.52%    6.62%
  0.55   0       0       0       0.30%   0.91%   2.62%   3.48%   3.97%    4.11%
  0.60   0       0       0       0       0       0       0.12%   1.25%    1.56%
```

- Below the laboratory's least \(C\) the margin is exactly \(0\), and
  it turns positive precisely at `least_C_pressure(q)` (\(19,41,214\)):
  failure requires no momentum at all below that. It grows with \(C\)
  and saturates
  at \(D(\log2/\log3\,\|\,q)/c_{\theta_\infty,q}\) — \(6.62\%\) at
  \(q=\tfrac12\). So the conjecture's failure forces the tilted odd
  share to exceed \(\tfrac12\) by \(\ge6.6\%\) on average at every
  sufficiently large \(C\), infinitely often in \(y\); and it forces
  only \(0.58\%\) at \(C=20\).
- The census runs to depth \(40\). At \(10^{12}\) that is
  \(C=76\) (margin \(5.25\%\)); at \(10^{50}\) it is \(C=15.6\) and at
  \(10^{100}\) \(C=11.3\), both below the least \(C=19\), where the
  margin is \(0\): at those two scales the census depth is one at
  which failure would require no momentum, so the observation
  \(s_\theta=0.50\pm0.06\) there cannot bear on \(\mathrm M_{\theta,q}\)
  in principle. At \(10^{12}\) the resolution \(\pm0.06\) is comparable
  to the \(5\%\) margin and the sample is the smallest.
- Conversely, to *see* the required momentum one would need depth
  \(\ge50L\) (\(128\) at \(10^{50}\), \(178\) at \(10^{100}\)) and a
  resolution below \(4\%\) — and even then only the contrapositive
  direction (failure ⇒ momentum) is observable; the hypothesis itself
  is asymptotic.

Not claimed: \(\mathrm M_{\theta,q}\), the conjecture, or that the
census is evidence either way.

## Open questions

None in this laboratory.

## Decision

**CLOSE.** A calibration: the failure margin is a closed form, zero
below the least \(C\) and positive from it, \(0.58\%\) at \(C=20\),
\(6.6\%\) in the limit, and the
existing census sits at depths where it is zero at the two larger
scales. Do not run a deeper census on its account — a floor raise
dominates. Best next question: none on this line.

## Publication assessment

Status: `STRUCTURAL`. One sentence for Paper C §9.4: the failure of the
conjecture forces an average tilted excess of \(m(C,q)\) per step,
\(6.6\%\) in the limit, zero below the least \(C\).
