# Juggler pressure: a direct attack on \(M_{\theta,q}\) / \(P_\theta\)

Status: **CLOSE** (the original routes are reparameterizations or
§10.4(e) kills; the 9 September pointwise-weight addendum has a sharp
obstruction; no live averaging estimate is proved)

Not a third formulation of the frontier, not a new orbit census, not a
halt theorem, and not a Paper C rewrite. The objects are the existing
hypotheses `J-tao-pressure-form`.

## Problem

Paper C Theorem 4(c) / Tao note §10 isolated the live pressure
\(\mathrm P_\theta(C)\) and the no-momentum form \(\mathrm M_{\theta,q}(C)\)
as the weakest sufficient conditions on the concentration route, and
explicitly left open an *estimate* of those objects (a method that
addresses the pressure statement directly is not covered by the Weyl
budget). Do either of the two remaining laboratory estimates bound
them without becoming \(\mathrm H(C,A)\), a killed Paper B sum, or a
bounded-depth statement?

## Exact statement

**9 September 2026 addendum.** `J-pressure-log-order-obstruction`
(EXACT — HUMAN PROOF): for any positive state weight of fixed
logarithmic order \(h(n)=(\log n)^{s+o(1)}\), the asymptotic
pointwise rate of the killed tilted operator is at least
\(\max\{2^{-s},e^\theta(3/2)^s\}\ge e^{\theta\log2/\log3}\).
The last bound is sharp as an asymptotic pointwise rate. It lies
strictly above the required pressure factor at every optimizing tilt
with \(0<q<p_C\). Proof and scope below under Results. This does not
refute the actual dyadic live-pressure or no-momentum hypothesis.

Let \(\tau(n)\) be the entrance time into \([1,N_0]\), \(o_t(n)\) the
odd count of the first \(t\) letters, \(N=y/2\),
\(d=\lceil C L(y)\rceil\), \(a_\theta=\tfrac12(1+e^\theta)\), and
\(\mu_{\theta,t}\) the measure on live starts with density
\(\propto e^{\theta o_t}\). Write \(s_\theta(t)=\mu_{\theta,t}(J^t(n)\ \mathrm{odd})\)
and \(\mu_k=\mu_{\theta,t}(\mathrm{suffix}\ O^{\ge k})\).

**Reset split (EXACT — HUMAN PROOF, elementary).** If complementary
cylinders (an even letter among the last \(k\) steps) have odd-share
at most \(\tfrac12+\varepsilon\) and the suffix-\(O^{\ge k}\) mass is
allowed to split at 1, then
\(s_\theta(t)\le\tfrac12+\tfrac12\mu_k+\varepsilon\). Usable for
\(\mathrm M_{\theta,q}\) only if \(q_\star=\tfrac12+\tfrac12\mu_k<p_C\).

**Fair-coin suffix masses (COMPUTATIONALLY VERIFIED).** On the
odd-start fair-coin walk-live measure at the Tao depths, with the
Theorem B‴ tilt \(\theta_C=\log(p_C/(1-p_C))\):

- \(k=3\): \(\mu_3\in[0.22,0.25]\), so \(q_\star\in[0.611,0.625]\),
  above \(p_{19}=0.598\) and at \(C=41\) still above \(p_{41}=0.616\).
  No room.
- \(k=4\): \(\mu_4\in[0.13,0.17]\), so \(q_\star\in[0.567,0.584]\),
  below \(p_{19}\) at every scale \(y=10^{12},10^{50},10^{100}\).
  Numerical room exists.

**High-walk reset images are sparse (COMPUTATIONALLY VERIFIED;
geometry EXACT).** After a letter \(E\), \(J^t([w]\cap(y,2y])\) is the
forward image of a start-cylinder, not a dyadic block of odd starts.
At \(y=10^5\):

- contracted \(\mathtt{OEE}\) (\(u<0\)): 12455 members fill a span of
  24, density 1;
- high-walk \(\mathtt{OOOE}\) (\(u=0.755\)): 6342 members in a span
  \(6.08\cdot 10^8\), density \(1.04\cdot 10^{-5}\);
- high-walk \(\mathtt{OOOOE}\) (\(u=1.34\)): density \(1.45\cdot 10^{-10}\).

Paper B Theorems 4.1 / 4.4 / 4.7 apply to dyadic odd *starts*, not to
those images. The complementary term of the reset split is therefore
\(\mathrm H_q\) at unbounded depth, and dies by Tao note §10.4(e).
Even-block / OE-fiber geometry is backward and does not intervalize a
forward cylinder. Contagion productions are not the law of \(J^t(n)\).

**Forward \(S\)-sampling (REPARAMETERIZATION).** For odd starts,
odd preimages are unique, so
\(Z_d(y)=e^\theta\sum_{m\in S\cap I(y),\ \tau(m)>d-1}e^{\theta o_{d-1}(m)}\)
with \(I(y)=(y^{3/2},(2y)^{3/2}]\) and
\(S=\{\lfloor n^{3/2}\rfloor:n\ \mathrm{odd}\}\). Bounding this
sample is \(S\)-fairness of the live set: already odd generation
(Paper C Theorem 2) and `J-tao-free-term-is-live-mass`. Not a new wall.

**Walk-live Walsh product (REPARAMETERIZATION / §10.4(e)).**
\(\{\tau>d\}\subseteq\{\mathrm{walk\ live}\}\). The unstopped expansion
is Tao note §10.4(c), weight \(\rho=\tanh(\theta/2)\approx 0.196\) at
\(\theta_{19}\). Crude \(|W_T|\le N\) on \(|T|\le k_0\) fixed costs
\(e^{O(\log d)}=e^{o(d)}\). The tail is
\((1+\rho)^d=e^{\Theta(d)}\) (\(\log(1+\rho)\approx 0.179\); at
\(d=49\), \(\log\mathrm{full}=8.75\) versus \(\log\mathrm{partial}_{k_0=4}=6.22\)).
Two-sided control of the tail is
`J-tao-cylinder-forms-reparameterization`. Vaaler plus van der Corput
on \(e(\tfrac12\sum_{s\in T}J^s(n))\) is a nested-floor phase: the
two-monomial leftover or the Weyl budget \(cC<1\) (Paper C Prop. 10.3).
Paper B on \(\max T\le 4\) is §10.4(e).

No fate is excluded. No halt theorem.

## Current literature

- [Walk coboundary](juggler_walk_coboundary.md) — the bounded
  correction was already killed by an even tower. The addendum here
  uses both even and odd exact towers to price the different,
  killed-tilted pointwise inequality for arbitrary fixed logarithmic
  orders, including unbounded weights. This is a project-specific
  method obstruction, not a literature-priority claim or a rescue of
  the old walk/cycle Lyapunov program.

- Tao note §10–11 / Paper C §§9–10 — `extended`: the estimate those
  notes recorded as a question, not an approach.
- Paper B Theorems 4.1, 4.4, 4.7 — `known`: dyadic odd starts, depth
  \(\le 4\); not forward images of deep cylinders.
- `J-tao-pressure-form`, `J-tao-cylinder-forms-reparameterization`,
  `J-tao-free-term-is-live-mass` — `known`.
- Exponent-pair two-monomial leftover — `known`; not reopened.

## Branch budget

**Addendum budget, 9 September 2026 (written before implementation).**

```text
Mathematical target     Can a logarithmic state weight yield a
                        pointwise tilted rate below the pressure target?
Novelty hypothesis      Allow any fixed logarithmic order, including
                        subpower arithmetic fluctuations, and price
                        the optimal rate using exact live towers.
Falsifier               The two tower directions force a critical
                        rate strictly above the target.
Already killed by?      Bounded walk corrections and location-free
                        concentration are closed; neither computes
                        this tilted minimax rate for all log orders.
Existing machinery      Exact square/cube powers; stopped pressure.
Maximum Phase-0 scope   One analytic obstruction and finite regression
                        checks. No new probe, census, Lean or paper edit.
Promotion criterion     A new drift bound usable for live averaging.
Stop criterion          A sharp obstruction for the proposed class;
                        do not infer that averaged drift is impossible.
```

**Original budget:**

```text
Mathematical target     Is there an upper bound on Z_d or on
                        Σ_t (s_θ(t)-q)^+ that uses the Juggler step
                        and is not a reparameterization of H(C,A)?
Novelty hypothesis      Either a last-even reset splits s_θ into a
                        Paper-B-controlled piece plus a suffix whose
                        worst-case mass still leaves q < p_C, or the
                        live generating function organises errors as
                        one object rather than 2^d cylinder counts.
Falsifier               The identity's error is H(C,A); the needed sum
                        is a killed Paper B / two-monomial object;
                        the argument only sees o(log log y) depths;
                        Weyl loss per depth is ≥ 2^{1/C}; after an
                        even letter the image of a deep cylinder is
                        still sparse; fair-coin μ_k already exceeds
                        2q-1 for every q < p_C.
Existing machinery      Tao note §10–11; Paper B Thms 4.1 / 4.4 / 4.7;
                        FateContagion productions; fair_tilted_live
                        in tao_reduction.py.
Maximum Phase-0 scope   Write the two identities; one fair-coin suffix
                        DP; classify; decide. No Lean, no Paper C
                        rewrite, no new CLI, no orbit census.
Promotion criterion     A new sufficient inequality that is not H(C,A).
Stop criterion          Every route is REPARAMETERIZATION, a killed
                        exponential sum, or insufficient by §10.4(e).
```

## Balanced-ternary formulation

None. The objects are the exponent walk and cylinder images on ordinary
positive integers.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Reset split of \(s_\theta\) — **EXACT — HUMAN PROOF** (elementary);
  fair-coin \(\mu_k\) — **COMPUTATIONALLY VERIFIED**; complementary
  geometry — **COMPUTATIONALLY VERIFIED** sparse, hence
  **REPARAMETERIZATION** of \(\mathrm H_q\) / §10.4(e).
- Forward \(S\)-sampling of \(Z_d\) — **REPARAMETERIZATION** of
  \(S\)-fairness / `J-tao-free-term-is-live-mass`.
- Walk-live Walsh product — **REPARAMETERIZATION** of
  `J-tao-cylinder-forms-reparameterization` (two-sided tail) or
  §10.4(e) (fixed-depth characters) or the recorded Weyl / two-monomial
  kills (unexpanded phase).

## Experiments

The 9 September addendum has no new probe or data census. The existing
test file checks exact tower identities above the certified floor,
the minimax algebra, and the two displayed numerical pressure gaps.
Those finite checks are not the proof of the asymptotic theorem.

- Probe: `research.juggler_sequence.pressure_direct`
  (`python -m research.juggler_sequence.pressure_direct`).
- Artifact: `data/research/juggler/pressure_direct/summary.json`.
- Tests: `tests/research/juggler_sequence/test_pressure_direct.py`.
- No orbit sample. The suffix DP reuses the exponent-walk state of
  `fair_tilted_live`; the geometry check is exhaustive on
  \((10^5,2\cdot 10^5]\).

## Conjectures

None new. `juggler_loglog_depth_cylinder_bound` stays **ACTIVE**;
\(\mathrm P_\theta\) / \(\mathrm M_{\theta,q}\) remain its weakest
form.

## Counterexamples

No counterexample to live pressure or no-momentum. The original routes
died by reparameterization and by the recorded
bounded-depth barrier, not by a counterexample to \(\mathrm M_{\theta,q}\).
The fair-coin \(\mu_4\) is compatible with no-momentum; it does not
prove it.

For the pointwise-weight addendum, the exact families are
\(b^{2^k}\to b\) in \(k\) even steps and
\(a^{2^k}\to a^{3^k}\) in \(k\) odd steps, with a fixed even
\(b>N_0\) and a fixed odd \(a>N_0\). Both remain live. They refute
the proposed uniform certificate class, not a dyadic average.

## Formalization

None. The reset split and the \(S\)-sampling identity are elementary
consequences of unique odd preimages and of the definition of
\(\mu_{\theta,t}\). Lean-ifying them ahead of an estimate would be
machinery gravity.

The log-order obstruction is an analytic human proof, not a new Lean
theorem. No formal file is added or changed by this addendum.

## Results

Classification **PRESSURE_DIRECT_ROUTES_ARE_H_OR_REPARAM**
(`J-pressure-direct-routes`).

- Route A has numerical room at \(k=4\) and none at \(k=3\). The
  complementary term is not Paper B: high-walk E-ending images are
  sparse. The split is \(\mathrm H_q\) at unbounded depth.
- Route B1 is \(S\)-fairness of the live set.
- Route B2: fixed-order Walsh is \(e^{o(d)}\); the tail is
  \(e^{\Theta(d)}\); every laboratory input for the tail is already
  recorded as a reparameterization or a kill.
- Not claimed: \(\mathrm M_{\theta,q}\), \(\mathrm P_\theta\),
  termination, any new cylinder bound.

### Fixed-logarithmic-order weights: a sharp pointwise obstruction

Fix \(N_0\ge2\) and \(\theta>0\). For positive \(h\) on the
integers above \(N_0\), define the killed tilted operator
\[
(\mathcal K_\theta h)(n)=
\begin{cases}
 e^{\theta\mathbf1_{n\text{ odd}}}h(J(n)),&J(n)>N_0,\\
 0,&J(n)\le N_0.
\end{cases}
\]
This is a pointwise operator on test functions, not the dyadic
distribution of current states. Write
\(q_*=\log2/\log3\) and
\(R(h)=\limsup_{n\to\infty}(\mathcal K_\theta h)(n)/h(n)\).

**Theorem (`J-pressure-log-order-obstruction`, EXACT — HUMAN PROOF).**
If \(\log h(n)/\log\log n\to s\in\mathbb R\), then
\[
R(h)\ge \max\{2^{-s},e^\theta(3/2)^s\}
       \ge e^{\theta q_*}.
\tag{P1}
\]
Moreover
\[
\inf_{s\in\mathbb R}\ \inf_{\log h/\log\log\to s}R(h)
=e^{\theta q_*},
\tag{P2}
\]
with the limsup attained by \(h(n)=(\log n)^{-\theta/\log3}\).
The lower bound is unchanged if a pointwise certificate is imposed
only every fixed \(\ell\ge1\) steps, with per-step rate measured as
\(\limsup_n((\mathcal K_\theta^\ell h)(n)/h(n))^{1/\ell}\).

*Proof.* Suppose an eventual one-step bound
\(\mathcal K_\theta h\le R h\) holds, with \(R>0\), for all states
above a cutoff \(M>N_0\). Choose a fixed even \(b>M\) and a fixed
odd \(a>M\). For all \(0\le j\le k\), the exact live towers are
\[
J^j(b^{2^k})=b^{2^{k-j}},\qquad
J^j(a^{2^k})=a^{3^j2^{k-j}}.
\tag{P3}
\]
The square roots and odd powers are exact integers, with the stated
parities. Every state is above \(M\). Multiplying the one-step
inequalities gives
\[
R^k h(b^{2^k})\ge h(b),\qquad
R^k h(a^{2^k})\ge e^{\theta k}h(a^{3^k}).
\]
Because
\(\log h(c^{r^k})=s(k\log r+\log\log c)+o(k)\) for fixed
\(c>1,r>1\), taking logarithms and dividing by \(k\) gives
\[
\log R\ge-s\log2,\qquad
\log R\ge\theta+s\log(3/2).
\tag{P4}
\]
Apply this to every \(R>R(h)\) when the limsup is finite, and let
\(R\downarrow R(h)\); if the limsup is infinite the conclusion is
immediate. The two affine bounds in (P4) are equal at
\(s=-\theta/\log3\), where their maximum is \(\theta q_*\).
This proves (P1).

For the pure weight \(h_s(n)=(\log n)^s\),
\(\log J(n)/\log n\to1/2\) through even integers and
\(\to3/2\) through odd integers. Hence its two pointwise ratios tend
to \(2^{-s}\) and \(e^\theta(3/2)^s\), proving (P2). This is
attainment of the limsup, **not** an assertion that the exact factor
\(e^{\theta q_*}\) is a uniform inequality at a finite cutoff;
floor errors need not have the favorable sign. Finally, for a fixed
block length \(\ell\), use (P3) with \(k\) a multiple of \(\ell\)
and multiply the block inequalities. The same limits give (P4).
\(\square\)

**Subpower fluctuations are included.** No monotonicity or regularity
of \(h\) is assumed beyond its logarithmic order. Multiplication by
any arithmetic factor bounded above and bounded away from zero, or
by any positive factor whose
logarithm is \(o(\log\log n)\), cannot evade the theorem.

**Corollary (a necessary oscillation size, not a rescue claim).** If
\[
s_-:=\liminf\frac{\log h(n)}{\log\log n},\qquad
s_+:=\limsup\frac{\log h(n)}{\log\log n}
\]
are both finite, put \(\Delta=s_+-s_-\). The same towers give
\[
\log R(h)\ge
\max\{-s_+\log2,\ \theta+s_-\log3-s_+\log2\}
\ge\theta q_*-\Delta\log2.
\tag{P5}
\]
For the last inequality, take the convex combination of the two
entries with weights \(1-q_*\) and \(q_*\). This is only a necessary
condition for an irregular weight; existence of such a weight is not
proved or proposed as the next branch.

**Comparison with the requested pressure rate.** For
\(C>1\) and \(0<q<p_C=(1-1/C)q_*\), use the optimizing tilt
\[
\theta=\log\frac{p_C(1-q)}{q(1-p_C)},\qquad
a_{\theta,q}=1-q+qe^\theta.
\]
Then
\[
\theta q_*-\log a_{\theta,q}
=\theta(q_*-p_C)+D(p_C\|q)>0.
\tag{P6}
\]
Thus the proposed pointwise bound with factor \(a_{\theta,q}\) is
impossible for every fixed logarithmic order. It fails even before
accounting for the endpoint-weight comparisons needed to turn a
weighted estimate into the unweighted live pressure. For finite
orders (P5) requires
\(\Delta\ge(\theta q_*-\log a_{\theta,q})/\log2\).

| \(C,q\) | \(\theta\) | unavoidable factor / target factor | necessary \(\Delta\) |
|---|---:|---:|---:|
| \(19,1/2\) | 0.395986 | 1.032902 | 0.046704 |
| \(41,0.55\) | 0.269995 | 1.013021 | 0.018664 |

**Boundary of the result.** Both test families remain above the
certified floor, so stopping does not repair the uniform certificate.
But a pointwise counterexample says nothing about its tilted mass
among all odd starts in \((y,2y]\). No dyadic mass lower bound for
these odd towers is obtained. The theorem therefore does **not**
refute \(\mathrm M_{\theta,q}\), \(\mathrm P_\theta\), an averaged
state-weight estimate, arbitrary irregular weights, or time-dependent
averaging methods. The desired sublinear cumulative excess is still
unproved. No failure-density upper bound is improved.

## Open questions

None for the closed uniform logarithmic-state certificate class. The
unresolved statement remains \(\mathrm M_{\theta,q}(C)\) on the
actual dyadic tilted population, as the Tao dossier already recorded.

## Decision

**CLOSE.** The original stop criterion fired: those direct estimates
are \(\mathrm H_q\) at unbounded depth, a
reparameterization of \(S\)-fairness or of the Walsh pair-correlation
form, a killed nested-floor exponential sum, or a bounded-depth
statement excluded by Tao note §10.4(e). Numerical room for the
\(k=4\) reset is real and recorded; it does not promote the route,
because the complementary cylinders are not dyadic intervals.
Do not reopen as a short-interval Paper B, a \(K_3\) rescue of
\(k=5\), a third formulation, or another pressure census. Best next
question for the original routes: none on this line.

The 9 September follow-up also closes: exact live towers rule out the
entire fixed-logarithmic-order pointwise certificate class, including
every fixed block length. Keep the sharp bound (P1)–(P2), not a new
potential-search framework. The no-momentum form stays open. **Best
next question:** can the excess be bounded on the actual dyadic tilted
population without requiring a drift inequality on every live state?

## Publication assessment

Status: `ARCHIVED`. A classification of the original deferred estimates
with an exact human-proof method obstruction added on 9 September.
Not a termination paper; no Paper A or Paper C edit.
