# Juggler pressure: external averaging of \(M_{\theta,q}\) / \(P_\theta\)

Status: **PROMOTE** (9 September 2026 correction: the existing
scale-averaged pressure bound does suffice for contagion; its
arithmetic estimate remains open)

This corrects the sufficiency claim for the already-written \(\Pi\),
not a third formulation of the frontier, not a proof of
\(\mathrm M_{\theta,q}\) or \(\mathrm P_\theta\), not a halt theorem,
and not a Paper C rewrite. The objects stay `J-tao-pressure-form`.

## Problem

Tao note §10.5 / Paper C §9.4 recorded the pressure / no-momentum
hypotheses as a mean-over-cylinders question for analytic number theory
and did not pursue an approach. The notes’ own phrase “mean over
characters, not a supremum” is already the pair-correlation form of
\(\mathrm H(C,A)\) (`J-tao-cylinder-forms-reparameterization`); do not
re-derive it. After the laboratory routes were classified
([juggler_pressure_direct](juggler_pressure_direct.md)), two other
natural readings remain: complete the single live-tilted odd sum
without a Walsh expansion of the tilt, and take a harmonic / dyadic
average of \(\mathrm P_\theta\). Is either a new sufficient inequality?
The original rejection of the second was incorrect: a growing
harmonic upper bound can still contradict the faster-growing
contagion lower bound. The correction below concerns sufficiency,
not an estimate of the actual Juggler average.

## Exact statement

Let \(\tau(n)\) be the entrance time into \([1,N_0]\), \(o_t(n)\) the
odd count of the first \(t\) letters, \(N=y/2\),
\(d=\lceil C L(y)\rceil\), \(a_\theta=\tfrac12(1+e^\theta)\), and
\[
Z_t(y)=\sum_{\substack{n\text{ odd}\in(y,2y]\\ \tau(n)>t}}e^{\theta o_t(n)}.
\]
Write \(s_\theta(t)=Z_t^{\mathrm{odd}}(y)/Z_t(y)\) with
\(Z_t^{\mathrm{odd}}\) as in Identity A. Live restriction and tilt
are as in `J-tao-pressure-form`.

**Parseval / large sieve (already classified; not re-derived).** The
notes’ “mean over characters” is the \(L^2\) mean of the Walsh sums
\(W_T=\sum_n\prod_{s\in T}(-1)^{J^s(n)}\). Parseval converts that mean
into the collision count \(\mathcal C_t\), and Walsh inversion converts
any two-sided bound back into \(\mathrm H(C,A)\) with another \(A\).
That is `J-tao-cylinder-forms-reparameterization`.

**Identity A (completed single sum).**
\[
Z_t^{\mathrm{odd}}(y)=\sum_{\substack{n\text{ odd}\in(y,2y]\\ \tau(n)>t}}e^{\theta o_t(n)}\,1_{\mathrm{odd}}(J^t(n)).
\]
The averaging reading: estimate this as one arithmetic sum by
completing \(1_{\mathrm{odd}}(m)=(1-(-1)^m)/2\) and smoothing
\((y,2y]\), without expanding \(e^{\theta o_t}\) in Walsh characters.

The identity \(1_{\mathrm{odd}}(m)=(1-(-1)^m)/2\) is elementary, so
\[
Z_t^{\mathrm{odd}}=\tfrac12 Z_t-\tfrac12\sum_{\tau(n)>t}e^{\theta o_t(n)}\,(-1)^{J^t(n)}.
\]
Vaaler replaces \((-1)^{J^t(n)}=e(J^t(n)/2)\) by a short Fourier
polynomial in the nested floor \(J^t(n)\). The amplitude
\(e^{\theta o_t(n)}1_{\{\tau>t\}}\) is constant on every depth-\(t\)
cylinder. The completed sum is therefore a cylinder-weighted nested
phase
\[
\sum_w e^{\theta o(w)}\,1_{\mathrm{live}(w)}\sum_{n\in[w]\cap(y,2y]}e\bigl(h\,J^t(n)/2\bigr).
\]
Three laboratory inputs, all recorded:

- Expand the amplitude in Walsh characters: pressure-direct route B2.
  Fixed order is \(e^{o(d)}\); the tail is \(e^{\Theta(d)}\); two-sided
  tail control is `J-tao-cylinder-forms-reparameterization`.
- Apply van der Corput / Weyl differencing to the nested phase
  \(e(h J^t(n)/2)\) without expanding the amplitude: the two-monomial
  leftover, or the depth-uniformity budget \(cC<1\) (Paper C
  Proposition 10.3). Differencing has \(c\ge 1\).
- Drop the amplitude, or truncate it to the first \(k=o(d)\) letters:
  Paper B at depth \(t\to\infty\), killed by Tao note §10.4(e).

Completing \(1_{\mathrm{odd}}\) without a Walsh expansion of the tilt
does not evade the cylinder partition: the tilt *is* that partition.
Identity A is not a new sufficient inequality.

**Identity B (harmonic / dyadic average).**
\[
\Pi(Y)=\frac1{\log Y}\sum_{2^k\le Y}\frac{Z_{d(2^k)}(2^k)}{N_k\,a_\theta^{d(2^k)}}.
\]

**Corrected sufficiency of \(\Pi\) as written.** Omit finitely many
small scales, so \(2^{k_0}>N_0\) and \(d_k\ge1\). Let
\(\rho_k=Z_{d_k}(2^k)/(N_k a_\theta^{d_k})\), with
\(N_k=2^{k-1}\) and \(d_k=d(2^k)\). Since
\(d(2^K)\asymp\log K\), the bound
\(\Pi(2^K)\le e^{o(d(2^K))}\) is exactly the upper-growth condition
\[
A(K):=\sum_{k=k_0}^K\rho_k\le K^{1+o(1)}.
\tag{A1}
\]
Here and below an upper bound \(K^{a+o(1)}\) means that for every
\(\varepsilon>0\) it is \(O_\varepsilon(K^{a+\varepsilon})\).

**Theorem (`J-pressure-scale-average-suffices`, EXACT — HUMAN PROOF).**
Fix \(C>1\), \(\theta>0\), and \(0<q<1\). Put
\[
p_C=(1-1/C)\frac{\log2}{\log3},\qquad
a=1-q+qe^\theta,\qquad
r=\frac{C}{\log2}(\theta p_C-\log a)>0,
\]
and use \(a\) instead of \(a_\theta\) in \(\rho_k\). Suppose
\([1,N_0]\) consists of terminating starts. If, for some
\(\eta\ge0\),
\[
A(K)\le K^{1+\eta+o(1)},\qquad
r-\eta>1-\lambda^{**},
\tag{A2}
\]
then every positive integer reaches \(1\). In particular the original
\(\Pi\) bound (A1), at the fair optimizing tilt and \(C\ge19\),
is sufficient. This is a conditional implication; (A1) and (A2)
have not been proved for Juggler.

*Proof.* Let \(F\) be the set of nonterminating starts. On block
\((2^k,2^{k+1}]\), every member of \(F\) is live at depth \(d_k\).
The envelope and \(d_k\ge C L(2^k)\) give
\(o_{d_k}>p_Cd_k\). Thus exponential Markov, still applied separately
on each block, gives
\[
\begin{aligned}
b_k&:=\sum_{\substack{n\in F\text{ odd}\\2^k<n\le2^{k+1}}}\frac1n\\
&\le 2^{-k}e^{-\theta p_Cd_k}Z_{d_k}(2^k)
=\tfrac12\rho_k e^{-(\theta p_C-\log a)d_k}
\ll_{N_0,C,\theta,q}\rho_k(k+1)^{-r}.
\end{aligned}
\tag{A3}
\]
The ceiling helps because the exponent in parentheses is positive;
indeed \(e^{-(\theta p_C-\log a)d_k}\le
(((k+1)\log2)/\log N_0)^{-r}\).

For every \(\varepsilon>0\), (A2) bounds \(A(K)\) by a constant
times \(K^{1+\eta+\varepsilon}\). Grouping the indices into blocks
\([2^j,2^{j+1})\) yields
\[
\sum_{k=k_0}^K\rho_k(k+1)^{-r}
\ll_\varepsilon
\sum_{j\le\log_2 K}2^{j(1+\eta+\varepsilon-r)}.
\tag{A4}
\]
Consequently this is \(O(K^\beta)\) for every
\(\beta>\max\{1+\eta-r,0\}\), including the zero-exponent boundary
by absorbing its logarithm. With
\(H_o(x)=\sum_{n\le x,n\in F\text{ odd}}1/n\), (A3) therefore gives
\(H_o(x)=O((\log x)^\beta)\).

For completeness, the odd-to-all-starts passage can avoid even the
harmless \(\log\log x\) multiplier in the original Tao proof. If
\(H_F(x)=\sum_{n\le x,n\in F}1/n\), every even failure has a
failure parent \(m\le\sqrt x\). Its complete even fiber has at most
\(m+1\) elements, all at least \(m^2\). Therefore
\[
H_F(x)\le H_o(x)+H_F(\sqrt x)+\sum_{m\ge1}m^{-2}.
\tag{A5}
\]
Iterate until the argument is bounded. The odd terms form a geometric
sum \(O((\log x)^\beta\sum_{j\ge0}2^{-j\beta})\), and the errors
are \(O(\log\log x)\). For \(\beta>0\) this gives
\(H_F(x)=O((\log x)^\beta)\).

The strict inequality in (A2) permits
\(\max\{1+\eta-r,0\}<\beta<\lambda<\lambda^{**}\).
If \(F\ne\emptyset\), fate contagion gives
\(H_F(x)\gg(\log x)^\lambda\), a contradiction. \(\square\)

**Why the old objection fails.** A spike can contribute
\(K^{1-r+o(1)}\), which need not tend to zero. But contagion requires
growth at least \(K^\lambda\). At \(r>1-\lambda^{**}\), the spike
and the whole summed upper bound grow more slowly than some such
lower bound. Summation does not need to preserve a per-scale theorem.

**Genuine weakening at the level of numerical hypotheses.** The
nonnegative sequence \(\rho_k=1+k\,1_{\{k\text{ is a power of }2\}}\)
satisfies \(A(K)\le3K\), but violates \(\rho_k\le k^{o(1)}\) along
the powers of two. This separates scale-averaged from pointwise
pressure assumptions. It is not asserted to be a realized Juggler
sequence of moments.

**Allowance and the requested tilted share.** At the optimizing tilt
\(\theta=\log(p_C(1-q)/(q(1-p_C)))\), one has
\(r=C D(p_C\|q)/\log2\). The allowed power growth of the normalized
scale average is any
\(\eta<r+\lambda^{**}-1\), not only \(\eta=0\).

| \(C,q\) | optimized \(r\) | strict upper limit for \(\eta\) |
|---|---:|---:|
| \(19,1/2\) | 0.5269265491 | 0.0195265491 |
| \(41,0.55\) | 0.5194493967 | 0.0120493967 |

For the cumulative tilted excess
\(E_k=\sum_{1\le t<d_k}(s_\theta(t)-q)^+\), the existing stopped
recurrence gives (set \(s_\theta(t)=0\) if the live population is
empty, in which case all subsequent pressures are zero)
\[
\rho_k\le\frac{e^\theta}{a}\exp(cE_k),\qquad
c=\frac{e^\theta-1}{a}.
\tag{A6}
\]
Thus an upper bound \(\sum_{k\le K}\exp(cE_k)\le
K^{1+\eta+o(1)}\) with the same allowance would suffice. This
estimates the same existing pressure object; no third named
hypothesis is introduced. A small arithmetic mean of \(E_k\)
alone does not give this exponential bound. No such estimate on
the actual dyadic population has been obtained here.

*Sufficiency of the harmonic average of live counts.* The sum
\(\sum_{n\le x}1_{\{\tau(n)>d(n)\}}/n\), restricted to a window
\((\sqrt x,x]\), is the log-measure
\(\mathbb P^{\log}_x(\tau>d)\). Proposition 11.1 of the Tao note
identifies the \(OO\)-restriction of the \(d\to\infty\) limit with
the free term \(\psi_F\). The finite-depth all-odds form differs by a
bounded factor (Paper B, depth two, on the first two letters). That
object is `J-tao-free-term-is-live-mass`. It is not named as a new
hypothesis.

*Estimate by even-block / \(OE\)-fiber productions.* A recursion for
the tilted harmonic live mass has an easy even step (backward
intervals) and an odd step that is unique-odd-preimage sampling of
the live tilted weight: tilted \(S\)-fairness of the live set,
pressure-direct route B1 / `J-tao-free-term-is-live-mass`. Even-block
and \(OE\)-fiber geometry is backward and does not intervalize a
forward cylinder \(J^t((y,2y])\); contagion productions are not the
law of \(J^t(n)\). The exact map (6.1) cannot replace contagion
(Corollary 11.2). Do not run a production estimate.

No fate is excluded. No halt theorem.

## Current literature

- Tao note §10–11 / Paper C §§9–10, §12 — `known`: the estimate those
  notes recorded as a question; the “mean over characters” sentence
  is already `J-tao-cylinder-forms-reparameterization`.
- [juggler_pressure_direct](juggler_pressure_direct.md) /
  `J-pressure-direct-routes` — `known`: last-even reset, \(S\)-sampling,
  Walsh product. Not reopened.
- `J-tao-pressure-form`, `J-tao-free-term-is-live-mass` — `known`.
- Exponent-pair two-monomial leftover — `known`; not reopened.
- Paper C Proposition 10.3 (depth-uniformity budget) — `known`.
- The 9 September correction uses elementary summation of nonnegative
  sequences and the already-proved contagion theorem. Its contribution
  is the project-specific weaker conditional input, not a new
  summation method or a literature-priority claim.

## Branch budget

**Correction budget, 9 September 2026 (before implementation):**

```text
Mathematical target     Does the existing scale-averaged pressure
                        bound suffice for contagion?
Novelty hypothesis      Sum the per-block Markov bounds before
                        comparing with harmonic failure growth.
Falsifier               The summed exponent or odd-to-all-starts
                        conversion loses the required saving.
Already killed by?      The earlier Cesaro rejection used the wrong
                        comparison; other arithmetic barriers remain.
Existing machinery      Live pressure, envelope, and contagion.
Maximum Phase-0 scope   Correct implication, quantify error allowance,
                        repair affected record; no census or framework.
Promotion criterion     A valid weaker sufficient averaging condition.
Stop criterion          Record implication; leave actual arithmetic
                        estimate open. Do not auto-open another route.
```

**Original budget (its blanket conclusion is superseded):**

```text
Mathematical target     Is either natural ANT reading of “external
                        averaging” a sufficient inequality for
                        M_{θ,q} or P_θ that is not H, H_q,
                        S-fairness, pair-correlation, Weyl, or
                        §10.4(e)?
Novelty hypothesis      Completion of the single live-tilted odd
                        sum, or a harmonic/dyadic average of P_θ,
                        might be strictly weaker than H and not
                        already named.
Falsifier               Each identity’s error is a recorded kill
                        or a third formulation of the frontier.
Existing machinery      Tao note §10–11; Paper C §9–10, §12;
                        pressure_direct CLOSE;
                        J-tao-cylinder-forms-reparameterization;
                        J-tao-free-term-is-live-mass;
                        J-pressure-direct-routes.
Maximum Phase-0 scope   Write two identities; classify; decide.
                        No Lean, no Paper C/Tao rewrite, no
                        census, no Walsh expansion, no reset,
                        no S-sampling campaign, no N_0 raise.
Promotion criterion     A new sufficient inequality that is not H.
Stop criterion          Both identities reparameterize, hit a
                        recorded kill, or open a third
                        formulation.
```

## Balanced-ternary formulation

None. The objects are the exponent walk and nested-floor parities on
ordinary positive integers.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Parseval / large sieve of Walsh characters — already
  **REPARAMETERIZATION** (`J-tao-cylinder-forms-reparameterization`).
  Pointed at, not re-derived.
- Identity A, completed single sum — **REPARAMETERIZATION** of
  pressure-direct B2 / nested-phase Weyl / §10.4(e). Completing
  \(1_{\mathrm{odd}}\) leaves a cylinder-constant amplitude.
- Identity B, \(\Pi\) as written — **EXACT — HUMAN PROOF** sufficient
  at the contagion threshold, by (A1)–(A5). The prior rejection was
  incorrect; Markov is used per block and its conclusions are summed.
- Identity B, harmonic average of live counts — **REPARAMETERIZATION**
  of `J-tao-free-term-is-live-mass` (finite-depth log-measure live
  mass). Not named as a third formulation.
- Identity B, production estimate — **REPARAMETERIZATION** of tilted
  \(S\)-fairness / pressure-direct B1.

## Experiments

No probe, census, or new CLI. Regression tests in
`tests/research/juggler_sequence/test_pressure_external_average.py`
check the summation identity, the sparse numerical separator, the
ceiling inequality, and the exponent allowances. These finite tests
are not a proof of the asymptotic implication or of its hypothesis.

## Conjectures

None new. `juggler_loglog_depth_cylinder_bound` stays **ACTIVE**;
\(\mathrm P_\theta\) / \(\mathrm M_{\theta,q}\) remain its weakest
per-scale form. The already-written scale average \(\Pi\) is now
known to suffice; no new named conjecture is registered and its
arithmetic bound is unproved.

## Counterexamples

There is no counterexample to \(\mathrm M_{\theta,q}\), pressure, or
the scale-average bound. The numerical sequence after (A5) separates
averaged from pointwise assumptions but is not a Juggler realization.
The former claim that the Cesàro bound cannot beat contagion is
withdrawn: the explicit implication (A1)–(A5) disproves that claim.
The completed-sum and inverse-production methods retain their
recorded limitations.

## Formalization

No new Lean file. The scale-average implication has a complete
analytic human proof above. The completion identity and comparison
with Proposition 11.1 remain elementary identities, not estimates.

## Results

The original blanket classification is corrected.
`J-pressure-external-average` retains only the closed methods;
`J-pressure-scale-average-suffices` records the conditional theorem.

- The notes’ “mean over characters” is the pair-correlation form of
  \(\mathrm H(C,A)\). Not re-derived.
- Identity A: Vaaler of \(1_{\mathrm{odd}}(J^t(n))\) produces a
  cylinder-weighted nested phase. Every input is Walsh-tail
  pair-correlation, the two-monomial / Weyl budget, or §10.4(e).
- Identity B: \(\Pi\) does suffice. More generally the normalized
  average may grow by \(K^{\eta+o(1)}\) when
  \(\eta<r+\lambda^{**}-1\). No pointwise pressure conclusion is
  needed. The harmonic live-count identity and the tilted
  \(S\)-fairness limitation of the proposed production method remain.
- Not claimed: \(\mathrm M_{\theta,q}\), \(\mathrm P_\theta\),
  termination without a hypothesis, any new cylinder bound, or any
  actual estimate of \(\Pi\).

## Open questions

Can the actual normalized pressure average \(\Pi\) be bounded within
the allowance \(\eta<r+\lambda^{**}-1\)? No specific arithmetic
method for that estimate is established here. A first moment of the
excess is not a substitute for the exponential quantity in (A6).

## Decision

**PROMOTE**, limited to the corrected conditional scale-averaged
implication (A2). The promotion criterion is met: the existing
\(\Pi\) is sufficient without pointwise pressure control. Its former
rejection compared the upper bound with boundedness instead of the
contagion growth rate. No estimate of the actual average is proved,
so this is not a halt theorem without a hypothesis.

The completed-sum, Walsh, sparse-forward-image and inverse-production
methods remain closed. No third formulation, census, potential
framework, floor increase or paper rewrite is introduced. The phase
ends with the conditional theorem. **Best next question:** can a
Juggler-specific estimate bound \(\Pi\) within the explicit power
allowance, allowing exceptional dyadic scales?

## Publication assessment

Status: `WORKING NOTE`. The original method classification now has
a corrected conditional theorem. Canonical Tao-note cross-reference
updated; no Paper A, Paper B, Paper C, or reviewer PDF edit.
