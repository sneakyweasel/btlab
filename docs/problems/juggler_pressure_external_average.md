# Juggler pressure: external averaging of \(M_{\theta,q}\) / \(P_\theta\)

Status: **PARK** (arithmetic-estimate follow-up, 9 September 2026).
The previously promoted scale-average sufficiency theorem remains
valid. A sparse-source part is now bounded; the full average remains
unproved. The one-sided sieve follow-up below establishes only an
abstract low-order-information obstruction, not an arithmetic bound.

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
| \(19,1/2\) | 0.5269265491 | 0.0194980938 |
| \(41,0.55\) | 0.5194493967 | 0.0120209415 |

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

**Shorter-prefix counting follow-up (9 September 2026).**

| Triage item | Scope |
|---|---|
| Mathematical target | Can a shorter all-odd prefix bound control the all-odd contribution at the required full depth, and can the recorded error estimates provide it? |
| Novelty hypothesis | Use inclusion of actual source sets to reduce the depth at which this single cylinder needs to be counted. |
| Falsifier | The shorter prefix still needs more uniformity than the available estimates supply. |
| Already killed by? | Fixed-prefix statistics, target-image interval averaging and the full-depth uniformity barrier are recorded. This check varies the prefix length with the source scale and tracks its precise cost; it does not reopen those mechanisms. |
| Existing machinery | Scale-average pressure sufficiency, the finite V6 contagion root, source-set inclusion and the recorded model of depth loss. |
| Maximum Phase-0 scope | Derive the two exponent thresholds, the shorter-prefix implication and its error budget; check the numerical constants. No orbit census. |
| Promotion criterion | An actual arithmetic estimate uniform over the derived depth range. |
| Stop criterion | Leave the count PARK if only a conditional calibration follows. |


**Prefix-selected boundary follow-up budget (9 September 2026).**
Check whether earlier non-boundary conditions supply a source-count
advantage at growing depth, and audit the available second-strip
estimate in Paper B. The already-closed ambient completion is not
reopened. Maximum scope: the existing mode estimate and the exact
constancy-cell argument; no new probe or fixed-depth ladder. Promote
only usable depth dependence. Close margin-based interval averaging
if its cells still contain at most one source integer; leave the
actual arithmetic count PARK if no new cancellation estimate emerges.

**Boundary-trimming follow-up budget (9 September 2026).** Bound the
pressure carried by starts whose fractional odd-step error approaches
an integer boundary. First prove the initial-strip source count and
price a shrinking strip with the existing pressure cap; then check
whether it transfers to later prefix-selected sources. The known
sparse-image and fixed-depth limitations forbid automatic iteration.
Maximum scope: this corollary, its transfer check, and one algebraic
regression. Promote only a growing-depth source estimate; otherwise
retain the initial deletion and PARK the deeper count. No census,
new analytic framework, or additional named hypothesis.

**Two-step fractional-gap follow-up budget (9 September 2026).**
Test a uniform positive lower bound for the sum of two fractional
rounding errors on all-odd triples after removing square states.
The explicit candidate is \(n=a^4-8\). Prove or reject its two
floor identities, parity, nonsquareness, and error bounds. The
one-step gap and general defect-composition routes are already
closed; no three-step Mordell attack or growing-depth family is
opened. A counting consequence is the promotion gate; a correct
thin counterexample closes only the proposed two-step gap shortcut.
Maximum scope: the elementary proof and one existing-file regression.

**Direct-source follow-up budget (9 September 2026).** Test whether
the necessary count (C3) follows from source covering, free-defect
congruence elimination, or freezing depth across nearby logarithmic
scales. These are bounded analytical checks against the existing
fixed-prefix, landing-defect, and sparse-image limitations. Promote
only an actual logarithmic-power count. Close the tested shortcuts
if their saving is too small, their arithmetic relaxation is vacuous,
or their depth still grows. No census, new code, or new named hypothesis.

**Squarefree-source follow-up budget (before implementation):**

```text
Mathematical target     Does squarefreeness supply an arithmetic saving
                        for the required all-odd count?
Novelty hypothesis      Removing repeated prime factors may exclude
                        near-integer floor behavior.
Falsifier               That behavior persists, while the counting
                        expansion still needs cancellation.
Already killed by?      Local valuation and near-Mordell routes are
                        closed; test the extra squarefree restriction.
Existing machinery      Integer cube-square identities and elementary sieving.
Maximum Phase-0 scope   One family and a depth-uniform truncation check;
                        no orbit census or new framework.
Promotion criterion     A saving for actual growing-depth cylinder counts.
Stop criterion          Only a local obstruction or an unestimated sum.
```

**Square-dilation follow-up budget (before implementation):**

```text
Mathematical target     Can square-dilation averaging bound the
                        growing-depth all-odd population?
Novelty hypothesis      The dilation identity exposes a polynomial
                        phase at the first landing.
Falsifier               Useful averaging misses the bulk, or later
                        floors destroy the simplification.
Already killed by?      Inverse completion is closed; this tests
                        the extra dilation identity and coverage.
Existing machinery      Exact floor arithmetic and source counting.
Maximum Phase-0 scope   Coverage bound and second-step expansion.
Promotion criterion     A bound covering the bulk of actual starts.
Stop criterion          Only thin families or a known nested-floor sum.
```

**One-sided sieve follow-up budget (before implementation):**

```text
Mathematical target     Can a one-sided sieve prove the all-odd bound
                        using sublinear-order parity correlations?
Novelty hypothesis      An upper bound may require fewer correlations
                        than full joint equidistribution.
Falsifier               Exactly fair low-order marginals coexist with
                        an all-odd atom larger than the target.
Already killed by?      Fixed-depth and sparse-image transfer are closed;
                        this tests growing correlation order o(d).
Existing machinery      Parity indicators and elementary binary algebra.
Maximum Phase-0 scope   One information test and its proof; no new
                        counting framework or orbit census.
Promotion criterion     An arithmetic upper bound for actual starts.
Stop criterion          Only a method limitation; retain the open count.
```

**Exceptional-amplitude follow-up budget (before implementation):**

```text
Mathematical target     Improve exceptional amplitudes using certified
                        finite prefixes and the remaining suffix bound.
Novelty hypothesis      Prefix savings or fair tilt/depth tuning may
                        make that bound fit the scale-average budget.
Falsifier               The cap retains an exponent above the allowance.
Already killed by?      Fixed-depth insufficiency is known; this prices
                        its exceptional-scale cost quantitatively.
Existing machinery      Stopped moments, envelope, Chernoff exponents.
Maximum Phase-0 scope   Audit the bound and record the unresolved count;
                        no new probe, framework, or floor campaign.
Promotion criterion     Arithmetic amplitude saving at growing depth.
Stop criterion          No such saving; close this attempted reuse.
```

**Arithmetic-estimate follow-up budget (before implementation):**

```text
Mathematical target     Can sparse-start and exceptional-scale bounds
                        control the actual pressure average?
Novelty hypothesis      Arithmetic sparsity may absorb the tilted cost.
Falsifier               Remaining scale amplitudes exceed the budget.
Already killed by?      Pointwise weights and generic inverse norms are
                        closed; this bounds actual source subsets.
Existing machinery      Exact towers, elementary counts, and the
                        corrected scale-average threshold.
Maximum Phase-0 scope   Sparse-subset estimate and exceptional-scale
                        cost; no census, framework or floor increase.
Promotion criterion     An upper bound covering the full population.
Stop criterion          Only sparse subsets are controlled; record the
                        gap without claiming the averaging theorem.
```

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
The estimate follow-up also checks exact square/square-successor
counts, actual finite live subset moments, and the convergent
majorant. It does not sample the asymptotic scale average.
The one-sided sieve check adds a finite three-wise fair binary model
with an unusually large all-odd atom, and checks the binomial bounds
used below. Neither test models the actual distribution of Juggler
starts; the general information obstruction is proved in prose.

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

### Estimate follow-up: sparse sources are harmless, the bulk is open

Retain \(C>1\), \(\theta>0\), \(0<q<1\), and
\(a=1-q+qe^\theta\). For a set \(B\) of source integers define
\[
\rho_k(B)=\frac1{N_k a^{d_k}}
\sum_{\substack{n\in B\text{ odd},\ 2^k<n\le2^{k+1}\\
                 \tau(n)>d_k}} e^{\theta o_{d_k}(n)}.
\]
This is a restricted sum on actual Juggler starts, not a model
distribution or a normalized share within the surviving population.

**Lemma (`J-pressure-sparse-starts`, EXACT — HUMAN PROOF).** If for
some fixed \(\delta>0\),
\(\#(B\cap(2^k,2^{k+1}])=O(2^{(1-\delta)k})\), then
\[
\rho_k(B)\ll 2^{-\delta k}(k+1)^\kappa,\qquad
\kappa=\frac{C(\theta-\log a)}{\log2},\qquad
\sum_{k\ge k_0}\rho_k(B)<\infty.
\tag{B1}
\]
Indeed, give every start survival to \(d_k\) and \(d_k\) odd letters.
This bounds its normalized contribution by
\(N_k^{-1}(e^\theta/a)^{d_k}\).
Since \(e^\theta/a>1\) and
\(d_k\le C\log_2(((k+1)\log2)/\log N_0)+1\), the tilt factor is
\(O((k+1)^\kappa)\). Exponential decay in \(k\) beats this fixed
power. No information about the later orbit is used. \(\square\)

**Actual arithmetic subset.** Take
\[
B_\square=\{n:\ n\text{ is a square or }J(n)\text{ is a square}\}.
\]
Among odd starts in \((y,2y]\), square starts number at most
\(\lfloor\sqrt{2y}\rfloor\). The odd branch is injective; its images
are at most \((2y)^{3/2}\), so at most
\(\lfloor(2y)^{3/4}\rfloor\) odd starts have square image. Thus
\[
\#\{n\in B_\square\text{ odd}:y<n\le2y\}
\le\lfloor\sqrt{2y}\rfloor+\lfloor(2y)^{3/4}\rfloor
\le4y^{3/4}\quad(y\ge1).
\tag{B2}
\]
Apply the same proof as (B1), using this odd-start count, to obtain
\(\rho_k(B_\square)\ll2^{-k/4}(k+1)^\kappa\).
Its contribution to \(K^{-1}\sum_{k\le K}\rho_k\) is therefore
\(O(K^{-1})\). The exact odd towers \(n=b^{2^j}\), \(j\ge1\),
are square starts and already satisfy the stronger \(\delta=1/2\)
bound. This removes those particular pointwise-certificate
obstructions from the cumulative pressure estimate.

This is only a sparse-subset estimate. It gives no bound on the
complement, on arbitrary iterated inverse closures, or on starts
that meet a square at an unbounded later time. It also gives no
bound on their *relative* share of the live tilted population:
the total live mass may itself be small. It does not prove
\(\mathrm M_{\theta,q}\).

**Why exceptional-scale counts alone do not finish the estimate.**
The trivial full-population bound is
\(\rho_k\le(e^\theta/a)^{d_k}\ll k^\kappa\). At the fair optimized
\(C=19\),
\[
\kappa=4.89342683035\ldots,
\qquad 1+\eta<1.01949809383\ldots.
\tag{B3}
\]
Suppose a proposed proof controls good scales and uses only this
cap on an unbounded exceptional set \(\mathcal B\). These data alone
cannot imply the desired average: the scalar sequence
\(\widehat\rho_k=k^\kappa\) on \(\mathcal B\) and \(0\) elsewhere
obeys them, yet at \(K\in\mathcal B\) its cumulative sum is at least
\(K^\kappa\). Superlacunarity does not help this worst-case cap.
This is an insufficiency of the proposed estimates, **not** a lower
bound for actual Juggler pressure or a refutation of (A2). A useful
exceptional-scale argument needs control of their weighted
amplitudes, not just how many scales are exceptional.

### Exceptional-amplitude follow-up: the finite-prefix cap still fails

This is a quantitative check of an already-limited method, not a new
averaging theorem or a new named hypothesis.

**Finite prefixes only change the constant.** For \(m<d\),
\[
Z_d(y)\le e^{\theta(d-m)}Z_m(y).
\tag{C1}
\]
Every start surviving to \(d\) survives to \(m\), and the suffix adds
at most \(d-m\) odd letters. Moreover
\(J^j(n)\ge\lfloor n^{2^{-j}}\rfloor\): compare each step with the
monotone integer square-root map and iterate. Thus all sufficiently
large starts stay above a fixed floor through any fixed \(m\).
Fixed-depth descent below the starting value is not absorption at
\(N_0\).

For this comparison set \(q=1/2\) and \(a=(1+e^\theta)/2\).
Even granting complete fair prefix statistics at a fixed \(m\),
\(Z_m/N=e^\theta a^{m-1}+o(1)\), (C1) gives only
\[
\rho_k\le
\bigl((a/e^\theta)^{m-1}+o(1)\bigr)(e^\theta/a)^{d_k}
=O(k^\kappa).
\]
The sparse-source deletion changes this fixed-prefix moment by at
most \(O(e^{\theta m}y^{-1/4})\) after division by \(N\); it does
not change the exponent. Repeating a fixed-depth estimate on the
evolving weighted population requires the missing arithmetic input,
not just its validity on the original dyadic starts.

**Fair-normalized tilt/depth tuning cannot fix this cap.** Here fix
\(q=1/2\), \(a=(1+e^\theta)/2\),
\(b=1-\lambda^{**}=0.507428455274\ldots\), and
\(\Delta=2\log2/\log3-1=0.2618595071\ldots\).
For every \(C>1\), \(\theta>0\), and \(\eta\ge0\) satisfying
the sufficient rate condition \(r-\eta>b\), one has
\[
\kappa-1-\eta>
\frac{b}{\Delta}-1=0.9377889342\ldots.
\tag{C2}
\]
To prove this, put \(s=\log a/\theta\). The identity
\(\log a=\theta/2+\log\cosh(\theta/2)\) gives \(1/2<s<1\).
Since \(r>0\), also \(s<p_C<1\). Hence
\[
\frac r\kappa=\frac{p_C-s}{1-s}
<2p_C-1<\Delta.
\]
It follows that
\(\kappa-1-\eta>(r-\eta)/\Delta-1+
\eta(1/\Delta-1)>b/\Delta-1\), proving (C2).
The claim is restricted to fair normalization and \(\eta\ge0\);
it does not rule out stronger arithmetic hypotheses, other
normalizations, or bounds that use actual mortality. It is not a
lower bound on actual pressure. In this cap-based method, no choice
of the fair tilt or depth makes exceptional-scale counts alone
adequate.

**An actual necessary count, not an estimate.** At the original fair
optimized \(C=19\), let \(Q_k\) count odd starts in
\((2^k,2^{k+1}]\) for which neither \(n\) nor \(J(n)\) is square
and the first \(d_k\) letters are all odd. Such starts are live:
an odd step increases every odd integer above the stopping floor.
Their contribution to \(\rho_k\) is exactly
\((Q_k/N_k)(e^\theta/a)^{d_k}\). Positivity and (A2) therefore require
\[
\frac{Q_k}{N_k}\le
k^{-(\kappa-1-\eta)+o(1)},\qquad
\kappa-1-\eta>3.8739287365\ldots.
\tag{C3}
\]
No such arithmetic bound is obtained here. Odd-branch injectivity
gives no density saving for these sources, and the fixed-prefix
argument above gives no logarithmic power. Even proving (C3) would not by itself control the accumulated all-odd
contribution, the other high-odd-count words, or establish (A2).
The distinction and a shorter sufficient counting target are detailed
in the following calibration.

### Shorter-prefix calibration (9 September 2026)


Set \(N_0=350000000\), \(L(y)=\log_2(\log(2y)/\log N_0)\),
\(d(y)=\lceil19L(y)\rceil\), and
\[
\mathcal O_t(y)=\{n\in(y,2y]:J^j(n)\text{ is odd for }0\le j<t\}.
\]
All floors in \(J(n)=\lfloor n^{3/2}\rfloor\) on odd states are
retained. These starts remain above the stopping floor while the
specified odd steps are taken.

At \(y=2^k\), write \(Q_k=|\mathcal O_{d(2^k)}(2^k)|\) and
\(N_k=2^{k-1}\). At the fair optimized tilt, their exact normalized
pressure contribution is
\[
\rho_k^{O}=\frac{Q_k}{N_k}(e^\theta/a)^{d(2^k)}
\asymp \frac{Q_k}{N_k}k^\kappa,\qquad
\kappa=4.893426830351912\ldots.
\]
Here \(p=(18/19)\log2/\log3\),
\(\theta=\log(p/(1-p))\), and \(a=(1+e^\theta)/2\).

The existing termination implication requires the **full** pressure
sum to be at most \(K^{1+\eta+o(1)}\), where
\[
0\le\eta<0.019498093834503\ldots.
\]
This value uses the actual finite V6 root
\(\lambda^{**}=0.492571544725356259\ldots\), rather than substituting
the rounded display \(0.4926\) as an exact constant.

Positivity implies the necessary individual-scale condition
\[
Q_k/N_k\le k^{-(\kappa-1-\eta)+o(1)}.
\]
The infimum of this exponent over the admissible choices of \(\eta\)
is \(3.873928736517410\ldots\). This is the source of the earlier
benchmark \(3.874\).

However, a **uniform** estimate \(Q_k/N_k\ll k^{-\gamma}\) gives
\[
\sum_{k\le K}\rho_k^{O}
\ll
\begin{cases}
K^{1+\kappa-\gamma},&\gamma<\kappa+1,\\
\log K,&\gamma=\kappa+1,\\
1,&\gamma>\kappa+1.
\end{cases}
\]
Thus this upper-bound argument fits some permitted pressure budget
when
\[
\boxed{\gamma>4.873928736517410\ldots.}
\]
This is a sufficient uniform exponent for the all-odd contribution;
it is not a necessary pointwise bound on every actual scale.
For example, the abstract scalar densities \(Q_k/N_k=k^{-4}\)
pass the necessary benchmark but give cumulative exponent
\(1.8934268\ldots\), too large. They are not claimed to be realized
by Juggler starts.

The canonical (C3) count excludes starts that are squares or have
square first images. Adding these starts back has summable pressure
by the already-proved sparse-source estimate, so the distinction
does not change these thresholds.

**A shorter prefix suffices for this contribution.**

Take
\[
m(y)=\lceil5L(y)\rceil.
\]
For sufficiently large \(y\), \(1\le m(y)\le d(y)\) and, exactly,
\(\mathcal O_{d(y)}(y)\subseteq\mathcal O_{m(y)}(y)\).
Consequently the concrete sufficient target
\[
\boxed{\quad
|\mathcal O_{m(y)}(y)|\ll y\,2^{-m(y)}
\asymp \frac{y}{(\log y)^5}
\quad}
\]
would imply
\[
\sum_{k\le K}\rho_k^O\ll K^{0.893426830351912\ldots}.
\]
The first odd letter being forced changes only an absolute factor
of two. A constant multiple of the fair single-cylinder count is
enough; exact asymptotic equidistribution is unnecessary.

This argument uses inclusion on the original integer sources. It
does not replace their images by a full interval or discard floor
corrections. The inclusion is elementary, and no new counting
theorem is claimed. The shorter depth still tends to infinity:
it is not a fixed five-step result.

**What an error estimate would need.**

For calibration, suppose one had, with constants independent of
both \(y\) and \(m\),
\[
\frac{|\mathcal O_m(y)|}{y/2}
\le B\,2^{-(m-1)}
+\exp(Dm)y^{-\delta_0 2^{-cm}},
\qquad B>0,\ D\ge0,\ \delta_0>0.
\]
This estimate has **not** been established here for the actual map.
At \(m(y)=\lceil\alpha L(y)\rceil\), the logarithm of the error is
\[
O(\log\log y)-\Theta((\log y)^{1-c\alpha}).
\]
It beats every negative logarithmic power if \(c\alpha<1\).
Thus the concrete choice \(\alpha=5\) needs \(c<1/5\), meaning
the error exponent loses a factor less than
\(2^{1/5}=1.148698354997\ldots\) per additional step.

Optimizing the shorter depth just above
\(4.873928736517410\ldots\) relaxes the condition to
\[
c<0.205173291211\ldots,\qquad
2^c<1.152824811550\ldots.
\]
At \(c\alpha\ge1\), the displayed error bound does not give a
vanishing density error, let alone the required saving. The
recorded differencing model has \(c\ge1\); it fails even this
relaxed single-cylinder budget. This is a limit of those bounds,
not an impossibility result for a different arithmetic method.


**PARK** the actual arithmetic count. This is a conditional calibration of the existing pressure route, not a new counting theorem or named frontier hypothesis. No available estimate checked here meets the derived uniformity requirement. The remaining high-odd-count words also remain uncontrolled. No paper edit, orbit census, runtime module or formalization is introduced.

### One-sided sieve check: sublinear-order marginals are insufficient

This refines the recorded fixed-order/Walsh information barrier. It
does not estimate an arithmetic sum or refute (C3).

**Elementary information test.** For every total depth \(d\ge2\)
and integer \(1\le h\le D:=d-1\), there is a probability measure
on parity words with first letter forced odd, all marginals of at
most \(h\) remaining positions exactly independent and fair, but
\[
\Pr(O^d)\ge\frac1{2V(D,h)},\qquad
V(D,h)=\sum_{j=1}^h\binom Dj.
\tag{D1}
\]

*Proof.* Put \(m=\lfloor\log_2 V(D,h)\rfloor+1\), so
\(V(D,h)2^{-m}<1\) and \(2^m\le2V(D,h)\). Choose an
\(m\)-by-\(D\) binary matrix \(A\) with independent uniform
entries. For each nonzero vector \(v\in\mathbb F_2^D\),
\(\Pr(Av=0)=2^{-m}\). The union bound over the \(V(D,h)\)
vectors of Hamming weight at most \(h\) is strictly less than
one. Therefore some \(A\) has no such vector in its kernel.
Every set of at most \(h\) columns of this matrix is linearly
independent.

For uniform \(U\in\mathbb F_2^m\), set
\(X=\mathbf1+A^\top U\) over \(\mathbb F_2\), interpreting
\(1\) as odd. Each projection onto at most \(h\) coordinates
is uniform, by the column independence. But \(U=0\) gives
\(X=\mathbf1\), so its probability is at least
\(2^{-m}\ge1/(2V(D,h))\). Prepend the forced odd letter. This
proves (D1).

For completeness, with \(t=h/D\le1\),
\[
V(D,h)\le\sum_{j=0}^h\binom Dj
\le t^{-h}(1+t)^D\le(eD/h)^h.
\tag{D2}
\]
The middle inequality follows from \(t^j\ge t^h\) for
\(j\le h\). If \(h=o(D)\), then
\(h\log(eD/h)=o(D)\). Hence these exactly fair low-order
marginals can coexist with
\(\Pr(O^d)\ge\exp[-o(d)]\).

By contrast, (C3), with \(\gamma=\kappa-1-\eta>0\), requires
\[
k^{-\gamma+o(1)}
=\exp\!\left[-\frac{\gamma\log2}{C}d_k+o(d_k)\right],
\tag{D3}
\]
an exponential saving in depth. At the specified \(C=19\),
\(\gamma>3.8739287365\ldots\). Consequently even **exact**
fairness for all collections of \(o(d)\) remaining time positions cannot,
by itself, imply the required one-sided all-odd bound. In particular,
a sieve whose only inputs are those joint statistics cannot certify
it. Granting such statistics is not a claim that they have been
proved at growing depth for Juggler.

These are abstract binary probability models, one for each depth,
not realized Juggler cylinders. The obstruction concerns deductions
from only the specified marginals; it does not exclude sieves using
additional map-specific arithmetic information. It also neither
refutes the all-odd count nor changes the conditional implication
(A2). No arithmetic estimate for the actual remaining starts was
obtained in this follow-up.

### Square-dilation check: long parameter averages miss the bulk

This is a scope check of another proposed arithmetic input, not a
new counting theorem for the all-odd cylinder. Write
\(F(n)=\lfloor n^{3/2}\rfloor\), so \(F\) agrees with \(J\)
along an odd run. In particular, the \(F^2\) formula below is
an actual \(J^2\) formula on odd sources only when their first
image is also odd. For positive integers \(a,b\),
\[
F(a^2b)=a^3F(b)+\lfloor a^3\{b^{3/2}\}\rfloor.
\]
For fixed nonsquare \(b\), this exposes an irrational cubic
phase in \(a\) at the first landing. However, even granting
perfect first-step balance on every long odd-\(a\) family would
not bound its singleton \(a=1\) member.

**Coverage.** For \(y\ge1\) and integer \(A\ge2\),
\[
\#\{n\in(y,2y]:a^2\mid n\text{ for some integer }a\ge A\}
\le\sum_{a=A}^{\lfloor\sqrt{2y}\rfloor}
\left\lfloor\frac{2y}{a^2}\right\rfloor
\le\frac{2y}{A-1}.
\tag{E1}
\]
The last bound follows by comparing \(\sum_{a\ge A}a^{-2}\)
with \(\int_{A-1}^\infty t^{-2}\,dt\). Thus the sources
accessible with a large integer dilation parameter form a thin
subset, irrespective of their dynamics.

Every odd integer has a unique representation \(n=a^2b\)
with \(b\) squarefree. Squarefree sources have only \(a=1\),
even if one allows non-squarefree bases in other representations.
They cannot be discarded: an elementary lower bound is
\[
\#\{n\in(y,2y]:n\text{ odd and squarefree}\}
\ge\frac{3y}{8}-\sqrt{2y}-1.
\tag{E2}
\]
Indeed there are at least \(y/2-1\) odd starts. For each odd
\(a\ge3\), at most \(y/(2a^2)+1\) are divisible by \(a^2\).
The union bound suffices, since
\[
\sum_{j\ge1}\frac1{(2j+1)^2}
<\sum_{j\ge1}\frac1{4j(j+1)}=\frac14,
\]
and fewer than \(\sqrt{2y}\) possible divisors contribute the
additive errors. This is a count of all odd squarefree starts,
not of those whose trajectories remain odd.

All-odd membership is not dilation-invariant even at two letters:
\(F(3)=5\) is odd but \(F(3^2\cdot3)=140\) is even;
\(F(7)=18\) is even but \(F(5^2\cdot7)=2315\) is odd.
These exact examples rule out an unconditional invariance shortcut,
not a quantitative estimate at growing depth.

**Second-step cost.** Put \(x=a^3b^{3/2}>1\) and
\(v=\{x\}\). Taylor's theorem gives the exact form
\[
F^2(a^2b)=\left\lfloor x^{3/2}-\frac32\sqrt{x}\,v+R\right\rfloor,
\qquad 0\le R\le\frac{3v^2}{8\sqrt{x-1}}.
\tag{E3}
\]
Here \(F(a^2b)=x-v\), and the remainder bound uses the
second derivative \(3/(4\sqrt{x})\). The coefficient of the
fractional-part term is \(\tfrac32a^{3/2}b^{3/4}\): it grows
with the averaging parameter. Replacing (E3) by its leading
monomial is not justified. Indeed, for fixed nonsquare \(b\),
this term is unbounded over odd \(a\). Otherwise \(v\to0\).
Writing \(a=2m+1\) and taking third finite differences would
then force \(48b^{3/2}\) to be a limit of integers, hence an
integer, a contradiction. This argument concerns all odd dilations,
not just those surviving an all-odd prefix. Retaining this term returns the
recorded superlinear nested-floor difficulty; no bound for it is
asserted here.

**CLOSE** the transfer from fixed-base, long-dilation averages to
the full source population. The source bound (E1) is elementary
sparsity, not an improvement to (C3). The positive-density
squarefree population lacks the proposed averaging parameter, and
no arithmetic relation transferring an all-odd estimate back to it
was found. This does not exclude a future dilation method using
additional identities or uniform arithmetic estimates.

### Squarefree-source check: near-integer odd landings persist

No growing-depth estimate is obtained by this restriction. There is,
however, an elementary infinite family showing that squarefreeness
does not give a uniform positive fractional-floor gap, even when
the first two letters are odd and the successor is nonsquare.

**Exact local family.** Let \(c>1\), \(c\equiv1\pmod{18}\),
with \(c,2c-1,2c+1\) squarefree, and set
\[
n=4c^2-1,\qquad m=8c^3-3c.
\]
Then \(n\) is odd and squarefree, \(J(n)=m\) is odd and
nonsquare, and
\[
0<n^{3/2}-J(n)<\frac1{5c}.
\tag{F1}
\]
Indeed \(\gcd(2c-1,2c+1)=1\) proves squarefreeness of \(n\).
Since \(\gcd(c,8c^2-3)=\gcd(c,3)=1\), any prime dividing
the squarefree integer \(c>1\) has exponent one in
\(m=c(8c^2-3)\), so \(m\) is nonsquare. Both integers are
odd. The integer identities
\[
n^3-m^2=3c^2-1>0,\qquad
(5cm+1)^2-25c^2n^3=5c^4-5c^2+1>0
\]
give \(m<n^{3/2}<m+1/(5c)<m+1\), proving (F1) and
\(J(n)=m\) without a floating-point approximation.

There are infinitely many admissible \(c\). Among \(c\le X\)
with \(c\equiv1\pmod{18}\), the primes \(2,3\) have no
square dividing any of the three forms: modulo \(9\) their
values are \(1,1,3\). Each prime \(p\ge5\) forbids three
residues modulo \(p^2\), hence removes at most
\(3(X/(18p^2)+1)\) candidates. Only
\(p\le\sqrt{2X+1}\) can occur. Since
\(\sum_{p\ge5}p^{-2}\le\sum_{k\ge5}k^{-2}<1/4\),
the union bound, also removing \(c=1\), gives
\[
\#\{1<c\le X:c\text{ admissible}\}
\ge\frac X{72}-3\sqrt{2X+1}-2.
\tag{F2}
\]
This tends to infinity. Thus no constant \(\varepsilon>0\)
can bound \(\{n^{3/2}\}\) from below on all sufficiently large
squarefree odd starts having a nonsquare odd successor. This is
only a two-letter counterexample to uniform positive separation:
the family has \(O(\sqrt y)\) sources in \((y,2y]\), makes
no assertion about later letters, and is harmless for the sparse
pressure bound (B1). It neither proves nor refutes (C3).

**What elementary squarefree sieving leaves.** For any function
\(0\le c_d(n)\le1\) on odd starts and integer \(A\ge1\),
the standard identity \(\mu^2(n)=\sum_{a^2\mid n}\mu(a)\)
gives
\[
\begin{aligned}
\sum_{\substack{y<n\le2y\\n\text{ odd}}}\mu^2(n)c_d(n)
&=\sum_{\substack{a\le A\\a\text{ odd}}}\mu(a)
\sum_{\substack{y/a^2<m\le2y/a^2\\m\text{ odd}}}c_d(a^2m)+E_A,\\
|E_A|&\le\sum_{a>A}\left\lfloor\frac{2y}{a^2}\right\rfloor
\le\frac{2y}{A}.
\end{aligned}
\tag{F3}
\]
Swapping the discarded divisor sum proves the bound; it is uniform
in \(d\). The squarefree identity itself follows prime by prime:
a squared prime divisor contributes the factor \(1-1\), while
there is no such factor for squarefree \(n\). In particular (F3)
applies to the actual all-odd indicator, optionally also excluding
square successors. For a target \(y(\log y)^{-\gamma}\), choosing
\(A=\lceil(\log y)^B\rceil\) with \(B>\gamma\) makes the
tail negligible. It does not estimate the retained sum.

Unlike the previous long-dilation proposal, (F3) has exact coverage.
Its possible advantage would be cancellation in the signed sum;
there is no need to bound every inner sum separately. Conversely,
the presence of the \(a=1\) term is not an impossibility argument:
the other terms can cancel nonsquarefree contributions. No such
growing-depth cancellation was proved. This standard identity is
recorded as a scope check, not as a third named frontier hypothesis.

**CLOSE** the uniform-positive-gap shortcut by (F1)–(F2).
**PARK** the actual squarefree all-odd count: (F3) has a controlled
tail but an unestimated main sum. Squarefreeness neither yields a
termination theorem nor makes the missing arithmetic estimate false.

### Two-step fractional-gap check: both errors can be small off squares

This refines (F1) in a different direction: two successive fractional
errors are small, and all three states can be nonsquares. It does
**not** establish squarefreeness of the new starting family.

**Two-step nonsquare family (EXACT — HUMAN PROOF).** For every odd
integer \(a\ge7\), set
\[
n=a^4-8,\qquad m=a^6-12a^2,\qquad
z=a^9-18a^5+54a.
\]
Then \(J(n)=m\), \(J(m)=z\), and \(n,m,z\) are odd. The
first two states are nonsquares. If \(a\) is prime, \(z\) is also
nonsquare. With
\(\varepsilon_1=n^{3/2}-m\),
\(\varepsilon_2=m^{3/2}-z\), one has
\[
0<\varepsilon_1<\frac{25}{a^2},\qquad
0<\varepsilon_2<\frac{225}{2a^3},
\qquad
a^2\varepsilon_1\longrightarrow24,\quad
a^3\varepsilon_2\longrightarrow108.
\tag{F4}
\]

*Proof.* Direct expansion gives the positive integer defects
\[
\Delta_1=n^3-m^2=48a^4-512>0,\qquad
\Delta_2=m^3-z^2=216a^6-2916a^2>0.
\tag{F5}
\]
Also \(m>(24/25)a^6\) and \(z>(24/25)a^9\), since
\(12/a^4<1/25\) and \(18/a^4<1/25\). Rationalizing gives
\[
0<n^{3/2}-m=\frac{\Delta_1}{n^{3/2}+m}
 <\frac{48a^4}{2m}<\frac{25}{a^2}<1,
\]
\[
0<m^{3/2}-z=\frac{\Delta_2}{m^{3/2}+z}
 <\frac{216a^6}{2z}<\frac{225}{2a^3}<1.
\]
Thus both asserted floors are exact. Their parity follows directly
from the formulas and oddness of \(a\). Moreover,
\[
(a^2-1)^2<n<a^4,\qquad
(a^3-1)^2<m<a^6,
\]
where the second lower bound uses \(12a^2<2a^3-1\) for
\(a\ge7\). Hence \(n,m\) are nonsquares. If \(a\ge7\) is
prime, then \(z=a(a^8-18a^4+54)\) has valuation exactly one at
\(a\), because \(a\nmid54\); so \(z\) is nonsquare as well.
Finally \(n^{3/2}/a^6,m/a^6\to1\) and
\(m^{3/2}/a^9,z/a^9\to1\). The two rationalized identities
give the limits in (F4). \(\square\)

Unboundedness of the primes now refutes any constant positive lower
bound on \(\varepsilon_1+\varepsilon_2\) for all sufficiently
large all-odd triples with every state nonsquare. This is a statement
about the **unweighted fractional errors**, not the integer defects
in (F5), which grow. Nor is it about transported error: by the
mean value theorem, for some \(m<\xi<n^{3/2}\),
\[
n^{9/4}-z=\tfrac32\sqrt\xi\,\varepsilon_1+
\varepsilon_2\sim36a\longrightarrow\infty.
\tag{F6}
\]
Thus the two-step family does not refute arbitrary weighted-error
budgets or a lower bound at growing depth.

Even allowing all odd parameters, there are only \(O(y^{1/4})\)
sources of this form in \((y,2y]\). They lie outside the square-source
and square-successor exclusions but are still covered by (B1), with
\(\delta=3/4\). No assertion about the remaining population follows.
One exact regression in the existing pressure test file checks the
identities and rational error bounds; it is not the asymptotic proof.

**CLOSE** the uniform positive two-step fractional-gap shortcut.
**PARK** the actual all-odd count (C3). No growing-depth family,
squarefree-quartic theorem, new runtime probe, or Lean claim is made.

### Initial boundary-strip deletion: summable cost, no iteration

**Corollary (EXACT — HUMAN PROOF).** For \(y\ge2\) and
\(0<\delta\le1/2\), put
\[
B_\delta(y)=\{n\text{ odd}:y<n\le2y,\ \|n^{3/2}\|\le\delta\},
\]
where \(\|x\|\) is distance to the nearest integer. Uniformly in
\(\delta\),
\[
\#B_\delta(y)\ll\delta y+y^{5/6}.
\tag{G1}
\]
This is a first-step consequence of
[Paper B, Lemmas 3.3–3.4](../theory/juggler_parity_discrepancy_note.md),
not a nested-floor estimate or a new exponential-sum method.

**Proof.** Write \(n=2r+1\). For \(h\ge1\), the phase
\(f_h(r)=h(2r+1)^{3/2}\) has
\(f_h''(r)=3h/\sqrt{2r+1}\asymp h y^{-1/2}\).
The second-derivative estimate gives
\[
\left|\sum_{y<2r+1\le2y}e(h(2r+1)^{3/2})\right|
\ll h^{1/2}y^{3/4}+h^{-1/2}y^{1/4}.
\]
Erdős–Turán bounds the interval discrepancy by
\[
O\!\left(y/H+y^{3/4}H^{1/2}+y^{1/4}\right).
\]
Choose \(H\asymp y^{1/6}\) and apply the estimate to the two
boundary intervals, whose total length is \(2\delta\). Closed
endpoints are covered by slightly enlarging these intervals and
taking the enlargement to zero; the discrepancy constant is uniform
in the endpoints. The case \(\delta=1/2\) is also trivial. This
proves (G1), including the exact-square sources. \(\square\)

Now specialize the existing pressure normalization to the fair
optimized \(C=19\):
\[
p_{19}=\frac{18}{19}\frac{\log2}{\log3},\qquad
\theta=\log\frac{p_{19}}{1-p_{19}},\qquad
a_\theta=\frac{1+e^\theta}{2},\qquad
\kappa=19\log_2(2p_{19})=4.89342683035\ldots.
\]
For sufficiently large \(k\), take
\(\delta_k=(\log 2^k)^{-6}\) and \(B_k=B_{\delta_k}(2^k)\).
Since \(N_k=2^{k-1}\) and \(d_k=19\log_2k+O(1)\), giving
every source survival and \(d_k\) odd letters, exactly as in (B1),
yields
\[
\rho_k(B_k)\le\frac{\#B_k}{N_k}
             \left(\frac{e^\theta}{a_\theta}\right)^{d_k}
\ll k^{\kappa-6}+2^{-k/6}k^\kappa,
\qquad \sum_k\rho_k(B_k)<\infty.
\tag{G2}
\]
Here summability has an exact certificate, independent of the printed
decimal: \(2^{30}<3^{19}\) implies \(p_{19}<3/5\), and
\(6^{19}<2^5 5^{19}\) implies
\(\kappa<19\log_2(6/5)<5\). Thus \(\kappa-6<-1\).
The strip contributes \(O(K^{-1})\) to the Cesàro normalized
pressure. No assumption about the sources' later orbits was used.

**Scope and transfer check.** This removes an entire shrinking
initial boundary strip, not just the explicit families in (F1) or
(F4). It gives no estimate for the complement or for the strip's
*relative* share of the live tilted population. It does not control
starts first encountering a boundary at an unbounded later time.
Already after one odd step, the original sources occupy a sparse
image at scale \(Y\asymp y^{3/2}\). Completing that image to
ambient intervals and using (G1) gives only
\[
O(\delta y^{3/2}+y^{5/4}),
\]
which supplies no saving over the \(O(y)\) source count for
logarithmically shrinking \(\delta\). Injectivity does not improve
this beyond taking the minimum with \(O(y)\). A union bound over
later times requires pulled-back source estimates that have not
been proved. This is the existing sparse-image transfer obstruction,
not a counterexample to such estimates.

Retain (G1)–(G2); **CLOSE** automatic ambient-strip iteration and
**PARK** growing-depth boundary trimming and (C3). One regression
checks the cutoff exponents, exact integer certificate, and pressure
calibration; it is not the analytic proof. No new probe or Lean module.

### Prefix-selected follow-up: fixed-depth removal, no averaging interval

**The second strip is already accessible to Paper B.** Put
\(F(x)=\lfloor x^{3/2}\rfloor\) and let \(N(y)\) count odd
integers in \((y,2y]\). For \(0<\delta\le1/2\), define
\[
B^{(1)}_\delta(y)=
\{n\text{ odd}:y<n\le2y,\ F(n)\text{ odd},
                    \|F(n)^{3/2}\|\le\delta\}.
\]
The mode estimate in Paper B, Theorem 4.4, Steps 1–7, gives
\[
\#B^{(1)}_\delta(y)
\le2\delta N(y)+O_\varepsilon(y^{23/24+\varepsilon}),
\tag{G3}
\]
uniformly in \(\delta\). To see this without any new nested-phase
argument, drop the condition that \(F(n)\) is odd. The Fourier
sums for the resulting boundary strip are exactly \(S_{0,2h}(y)\),
with \(1\le h\le H=\lfloor y^{1/24}\rfloor\), inside the
existing uniform mode range. Erdős–Turán adds \(N(y)/H\) and a
harmonic logarithm. Apply the mode estimate with a smaller positive
\(\varepsilon\) to absorb that logarithm. Endpoint enlargement
works as in (G1). This proves the stated upper bound; no conditional
share or asymptotic within a longer selected prefix is asserted.

At \(\delta_k=(\log 2^k)^{-6}\), take
\(\varepsilon=1/48\). The same worst-case pressure cap gives
\[
\rho_k(B^{(1)}_{\delta_k}(2^k))
\ll k^{\kappa-6}+2^{-k/48}k^\kappa.
\tag{G4}
\]
Thus the union of the initial and second strips also has summable
restricted pressure. This is an **EXACT — HUMAN PROOF** corollary
of the existing fixed-depth estimate, not new analytic machinery.
It bypasses the failed ambient completion for this one fixed depth;
it supplies no estimate uniform in growing depth.

**Why earlier margins give no interval-averaging advantage.** For
the auxiliary unbranched map \(F\) on real \(x\ge1\), the
first-step constancy cells are
\[
I_m=[m^{2/3},(m+1)^{2/3}),\qquad
|I_m|\le\tfrac23m^{-1/3}<1\quad(m\ge1).
\]
The restriction of \(F\) to positive integers is strictly increasing:
\((m+1)^{3/2}-m^{3/2}>1\). Consequently every iterate of that
restriction is injective. On \(I_m\),
\(F^t(x)=F^{t-1}(m)\); these values are distinct for distinct
\(m\). The constancy cells of every \(F^t\), \(t\ge1\),
therefore remain exactly the first-step cells. Imposing an initial
margin \(\delta\) shrinks them to
\([(m+\delta)^{2/3},(m+1-\delta)^{2/3}]\).
Later parity, margin, or first-hit conditions select cells; they do
not produce a cell containing several integer sources.

This applies to Juggler along an all-odd prefix; it is not an assertion
that the even branch is injective. Exact real-source stability merely
keeps the first image, hence all later images, unchanged inside one
sub-integer cell. It must not be confused with differentiating an
unrounded composition through later floors. Counting lattice points
in the selected cells still requires the missing arithmetic estimate.
In particular, an additional prefix indicator cannot be inserted into
\(S_{0,2h}\) using its unweighted bound alone.

**CLOSE** the margin-based interval-averaging shortcut. The growing-depth
arithmetic question remains **PARK**. No counterexample to it is claimed;
no new runtime code, formal module, or fixed-depth ladder is introduced.

## Open questions

**Full-phase follow-up (9 September 2026): no new estimate.** Exact
source pairing, partial summation, and grouping that retains the floor
corrections were checked for a new cancellation mechanism. None was
found. Complete-sum cancellation still needs control after restriction
to the preceding odd prefix; grouping still needs an estimate for the
actual source-weighted image. The moving Fourier frequencies and the
failure of independent shift averaging to control the actual phase
are already recorded in
[the parity laboratory note, Parts XVI–XVIII](../research/juggler_two_step_parity_lemma.md).
Those observations are not renamed as new theorems. This closes the
duplicate-method follow-up, not the arithmetic question. No new probe,
formal module, or conjecture was introduced.

**First-step locality follow-up (9 September 2026).**
[Parity neighbor scale](juggler_parity_neighbor_scale.md) now proves
the sharp worst-case distance exponent 1/4 for finding an odd source
with opposite first-image parity. It neither preserves a preceding
odd prefix nor controls assignment multiplicity. Its explicit lower
clusters are covered by (B1), so the necessary growing-depth count
(C3) and the full pressure estimate in (A2) remain unproved.

**Direct-source follow-up (9 September 2026): no new count.** Three
checks leave the existing arithmetic gap unchanged.

1. For \(y\ge4096\), let \(N\) count odd sources in \((y,2y]\)
   and put \(B=4\lceil(2y)^{1/4}\rceil+1\). Partition into complete
   \(B\)-point blocks of consecutive odd sources. The neighbor theorem
   gives both first-image parities in each block, hence
   \(\#OO\le N-\lfloor N/B\rfloor\). The guaranteed deletion
   fraction is only of order \(y^{-1/4}\), weaker than the existing
   first-step distribution theorem. Even if this fractional loss could
   be repeated independently for \(O(\log\log y)\) levels, its
   resulting bound would have surviving fraction \(1-o(1)\), not a
   logarithmic-power saving. That repetition on selected sources is
   itself unproved.
2. For an actual all-odd chain, the exact defects satisfy
   \(\rho_j=n_j^3-n_{j+1}^2\), \(0\le\rho_j\le2n_{j+1}\),
   and \(\rho_j\equiv n_j-1\pmod8\). These are the existing
   [sequential-Mordell](juggler_sequential_mordell.md) and
   [landing-valuation](juggler_landing_valuation.md) facts. If the exact
   equalities are weakened to congruences modulo an even \(Q\), with
   free auxiliary defects in windows containing \([0,Q-1]\), then
   **every** odd state-residue chain is compatible: choose each defect
   as the least nonnegative residue of
   \(r_j^3-r_{j+1}^2\pmod Q\). Eliminating these free residues
   excludes no source residue class. A useful sieve would need new
   information on the actual defects, not merely this relaxation.
   Neither finite residue censuses nor this observation refutes all
   possible higher-order arithmetic couplings.
3. At \(C=19\), for sufficiently large \(K\) and
   \(K\le k\le2K\), the defined depths satisfy
   \(0\le d_k-d_K\le19\), since
   \((k+1)/(K+1)<2\). The stopped-moment inequality (C1) gives
   \[
   \rho_k\le
   (e^\theta/a)^{19}\,
   \frac{Z_{d_K}(2^k)}{N_k a^{d_K}}.
   \]
   Thus depth can be frozen across this block at constant cost, but
   \(d_K\asymp19\log_2K\) still grows. Replacing it by fixed depth
   restores exactly the suffix cap in (C1), with unchanged exponent
   \(\kappa\). This supplies no uniformity from a fixed-depth theorem.

**CLOSE** these three transfer shortcuts; **PARK** the actual source
count. These are applications and scope checks of recorded limitations,
not new counting theorems, new named hypotheses, or a refutation of
(C3). No new probe, computation campaign, or formalization was added.

Can a one-sided arithmetic counting argument prove the necessary
all-odd bound (C3) at growing depth? No bound for it, or for the
remaining high-odd-count words, is established here.

## Decision

**PARK** the arithmetic-estimate follow-up. The conditional
scale-averaged implication (A2), promoted in the preceding phase,
remains valid: no part of that correction is withdrawn. The current
phase proves the sparse-subset bound (B1)–(B2), but does not meet its
promotion criterion of controlling the full population. The
exceptional-scale calculation (B3) identifies the missing amplitude
estimate; it is not an impossibility theorem for such an estimate.
The later finite-prefix/suffix-cap attempt is closed by (C1)–(C2),
including all admissible fair tilt/depth choices. Those elementary
diagnostics are not promoted as an arithmetic advance.
The one-sided sieve follow-up closes only the attempt based solely
on sublinear-order joint parity statistics, by (D1)–(D3); the actual
all-odd arithmetic count remains open.
The square-dilation follow-up also fails to supply that estimate:
long parameter averages cover only the sources in (E1), and (E3)
does not extend the first-step polynomial simplification.
The squarefree follow-up refutes only a uniform positive local
floor gap, by (F1)–(F2). The exact truncation (F3) leaves the
growing-depth arithmetic sum unestimated, so it is not promoted.
The direct-source covering, free-defect congruence, and depth-freezing
checks likewise supply no growing-depth saving; those shortcuts are
closed without declaring the actual source count false.
The explicit family (F4)–(F6) closes only the uniform positive sum
of two unweighted fractional errors after removing square states;
its transported error grows and its source set is sparse. It supplies
no growing-depth count or refutation of such a count.
The initial boundary-strip corollary (G1)–(G2) removes a summable
restricted-pressure contribution, but the ambient estimate cannot be
iterated onto the sparse orbit images. The separate source-mode
estimate in Paper B also removes the second strip, by (G3)–(G4).
Both are fixed-depth corollaries. Margin-based interval averaging is
closed because all-odd constancy cells remain shorter than one integer
spacing at every depth. Neither growing-depth boundary hits nor the
complementary pressure has been bounded.

The completed-sum, Walsh, sparse-forward-image and inverse-production
methods remain closed. No third formulation, census, potential
framework, floor increase or paper rewrite is introduced. The phase
ends here. **Best next question:** what arithmetic estimate can bound
the actual growing-depth all-odd count (C3) while retaining the floor
corrections?

## Publication assessment

Status: `WORKING NOTE`. The original method classification now has
a corrected conditional theorem. Canonical Tao-note cross-reference
updated; no Paper A, Paper B, Paper C, or reviewer PDF edit.
