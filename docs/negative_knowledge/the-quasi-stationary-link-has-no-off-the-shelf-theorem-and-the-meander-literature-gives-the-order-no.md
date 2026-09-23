# The quasi-stationary link has no off-the-shelf theorem, and the meander literature gives the order not the prefactor

Literature search, 15 September 2026, on the one link still missing in
`J-boundary-fraction-is-the-clean-coordinate`: the convergence
\(R_d\to R(\{d\beta\})\).

**The uncited import, and its discount.** Denisov--Sakhanenko--Wachtel,
*First-passage times over moving boundaries for asymptotically stable
walks* (arXiv:1801.04136), give the tail of \(T_g\) and convergence of
the conditioned walk to the stable meander for **every** boundary with
\(g_n=o(c_n)\). A Sturmian barrier's sawtooth is \(O(1)=o(\sqrt n)\), so
it qualifies, and nothing in `docs/` cited this line before today. What
it is NOT: its conclusion is about the *rescaled* walk, so it supplies
the order and the meander limit, which the laboratory already derives by
Wiener--Hopf / Spitzer with the non-lattice local limit theorem
(`J-paper-b-meander-constant-derived`, \(\kappa=1.541814521\)). The open
link is finer --- the phase-indexed profile \(R(\{d\beta\})\) --- and a
diffusive limit averages exactly that away. Import it for the
moving-boundary framing and the first-passage tail; do not expect it to
produce \(\psi\).

**The gap that is in the literature, not only here.** Operator renewal
theory handles polynomial memory loss --- Sarig, and Gouëzel
(arXiv:math/0202147) --- but for *autonomous* maps: Pomeau--Manneville
intermittent interval maps, Chernov--Markarian--Zhang billiards.
Transfer-operator *cocycles* are handled by semi-invertible Oseledets
theorems (Froyland--Lloyd--Quas, arXiv:1001.5313; González-Tokman--Quas)
--- but under quasi-compactness, that is, a spectral gap, which is
geometric memory. This operator is **driven** (the Sturmian word over
the rotation by \(\beta\)) **and critical** (polynomial forgetting,
`J-killed-walk-forgets-polynomially`). Searches surfaced each half and
nothing combining them.
Kind: `EXTERNAL_GAP`.
Consequence: do not spend a session looking for an off-the-shelf theorem
for the quasi-stationary convergence. **Amended 16 September 2026:** there IS a
literature and it is Ocafrain's three papers above --- the searching is done, and
the result of it is recorded rather than the absence. What those papers lack is
precisely statable: every general theorem among them assumes (A'), which is
equivalent to exponential uniform convergence and which this process fails by
being critical. Two things they DO give: the strict quasi-stationary distribution
provably does not exist once the boundary moves (Ocafrain 2018, Proposition 2.1),
so the phase-indexed family is forced and not a modelling choice; and for a FINITE
state space with a periodic boundary the quasi-ergodic distribution exists by
Darroch--Seneta, which covers the capped rational barrier at fixed `q` and cap.
Do not re-run this search; cite these instead.
**NARROWED 16 September 2026**
(`J-yaglom-rate-is-one-over-d`): the UNDRIVEN continuum case IS covered ---
Ocafrain, ECP 2020, gives \(1/t\) to the Yaglom limit for Brownian motion
with drift conditioned not to hit zero, with Q-process Bessel-3, both of
which match what is measured here. So the missing combination is
driven-and-lattice, not driven-and-critical; the criticality has a rate in
the literature and it is the right one. If the
link closes it will be by proving the combination, and the laboratory
already holds the input such a proof consumes ---
`J-bump-kernel-factorises-into-distance-and-phase` gives
\(K(n)=n^{-2-\varepsilon}g(\{-ns\})\) with \(\varepsilon\approx0.22\),
additive to \(0.1\%\) at separations \(\ge70\).

**NARROWED AGAIN, same day** (`J-sturmian-driving-is-uniform-in-q`): and the
DRIVING is now measured rather than feared. For a rational barrier the period
map is autonomous, so Ocafrain applies at each \(q\); the irrational Sturmian
barrier is the limit \(q\to\infty\), and that limit is benign. Across six
convergents of \(\beta\) spanning \(q=19\) to \(q=24727\) the exponent stays
\(d^{-1}\) (\(-0.9987\) to \(-1.0231\)) and the constant stays \(20.1\), the
last two convergents agreeing to six digits --- it converges, it does not
merely stay bounded. The residual scatter is phase (a \(3.96\%\) spread over
one period at fixed \(q\)), not denominator. The mechanism is not
homogenisation, which would need \(d\gg q^2\); it is that every barrier in the
family is a bounded perturbation of the SAME line,
\(|\lceil ts\rceil-ts|<1\) uniformly in \(t\) and \(s\) --- far inside the
\(g_n=o(c_n)\) regime Denisov--Sakhanenko--Wachtel assume. So the missing
combination is now driven-and-LATTICE alone, and the driving costs four
percent of a constant. What is still absent is a THEOREM; the numbers now say
what it should assert.

**THAT NARROWING WAS WRONG, corrected 16 September 2026**
(`J-moving-boundary-qsd-literature-exists-and-excludes-us`). The moving-boundary
literature was then read at source, and the driven half IS covered --- Ocafrain,
ALEA 15:429-451 (2018) for discrete-time chains with periodically moving
absorbing boundaries; Stoch. Proc. Appl. 130(6) (2020) and arXiv:2010.05483 for
the general theory. But all of the general machinery runs on Assumption (A'), a
conditional Doeblin condition plus a Harnack-like survival comparison, and
arXiv:2010.05483 states that in the time-homogeneous framework this IS the
Champagnat--Villemonais condition, *equivalent to exponential uniform convergence*
to quasi-stationarity. This process converges polynomially and has no spectral gap
in any exponential weight (`no_weight_separates`, Lean), so (A') provably fails.
The driven theory covers the non-critical regime; criticality is exactly what it
excludes. So the uncovered combination is driven-AND-critical after all, as this
entry originally said, and the lattice is not the obstruction. I narrowed on the
strength of a fixed-boundary result and should not have.

**The tail does not determine the boundary fraction, and the shortfall IS the
boundary layer** (`J-tail-does-not-determine-the-boundary-fraction`, 16 September
2026). Killed claim: the quasi-stationary profile is normalised, so
`R + sum_(m>=1) Pi_phi(m) = 1` exactly; with the measured tail form
`Pi_phi(m) = A(phi)(m + gamma - phi) r*^m` that sum is closed in `A` and `c`
(`J-profile-is-linear-times-geometric-in-the-line-coordinate`,
`J-tail-amplitude-is-a-cocycle-over-the-boundary-fraction`), so if the form held
down to `m = 1` then `R = 1 - A r* [1/(1-r*)^2 + c/(1-r*)]`, the phase-indexed
apparatus would collapse to a single scalar recursion over the rotation, and the
laboratory's clean coordinate would be computable rather than measured.
Kill: the residual `R - R_predicted` converges, and not to zero --- `+2.33e-2`,
`+7.12e-3`, `+3.52e-3`, `+3.52e-3` at caps `400, 800, 1600, 3200` for phase 0 at
`306/485`, identical at the last two caps to three figures; likewise `-7.38e-4`,
`-2.76e-4` and `+3.90e-3` at phases 23, 46 and 69. It is not a fitting artefact:
the normalisation is exact, so the residual *is* minus the boundary-layer mass ---
the extrapolated tail sum minus the true sum over `m >= 1`, which is the mass the
pure tail misses near the barrier. Those are the complex modes of
`J-tail-spectral-gap-closes-like-one-over-root-q`, that is, this cluster's
criticality read off the other side of the ledger, and the reason the shortfall
cannot be tuned away. Over 200 phases it runs `-2.941e-3` to `+7.318e-3`, mean
`+1.076e-3`, being `-3.3%` to `+9.8%` of `R`, and it has no simple rule on this
evidence: not explained by the rise letter (means `8.7e-4` against `1.19e-3`, with
standard deviations `8.9e-4` and `2.25e-3` swamping the gap), and correlating only
weakly with the phase (`0.19`) or with `R` itself (`-0.16`).
Kind: `REFUTED`.
Consequence: the profile costs one constant, one cocycle, and `R`; this measures
how close the first two come to determining the third --- about five percent
typically, never exactly. `R` stays the fundamental unknown, and the open
obligation of `J-boundary-fraction-is-the-clean-coordinate` is not reduced by any
of the structure work that produced the tail form.
Do not: re-derive the normalisation closure as a route to `R`; read a shrinking
residual here as convergence to zero without carrying a fourth cap --- the first
three alone would have reported the reduction as holding; or look for the
boundary-layer mass in the rise letter or the phase.
Machinery: `tail_predicts_boundary`. No bound moves.


**The certificate increment is not a function of the rotation coordinate, so
the almost-periodic prefactor does not follow from the recursion**
(`J-paper-b-increment-is-not-a-rotation-function`, 18 September 2026).
Killed claim: that `r_d = M_d / (2 N_(d-1))`, the fraction of Paper B's survivors
dying at step `d`, is a function of `frac(d * beta)` alone, `beta = log2/log3`.
It is an attractive claim because `J-paper-b-survivor-certificate-recursion`
writes `N_d = 2^d * prod (1 - r_k)` exactly, so an `r_k` depending only on the
rotation would make the survivor count almost-periodic outright and hand over
the prefactor of `J-paper-b-meander-prefactor-is-almost-periodic` without a
local limit theorem.
Kill: residue classes modulo `485`, the denominator of the convergent `306/485`,
fix the coordinate to `9.3e-4`. Over depths to `3000`, fitting `d >= 1000`, all
306 such classes are **strictly monotone in `d`** -- scattered values would be
monotone by chance two to eight percent of the time. The median within-class
spread is `9.9e-4` against a median `a + b/d` residual of `3.2e-6`, and 264 of
306 classes exceed tenfold the `6.5e-5` that the residual coordinate motion can
explain. One witness: at `d = 300, 785, 1270` the increment reads `0.05279228`,
`0.04912429`, `0.04821094`.
Kind: `REFUTED`.
Consequence: the prefactor still needs the local limit theorem for a walk
against a Sturmian barrier; the recursion gives `r_d` an exact finite meaning at
every depth but does not make it a rotation function. `MeanderShape` in
`PaperBSurvivorAsymptotic` remains a hypothesis.
Do not: re-derive the prefactor from the product formula as though `r_k` were
almost-periodic; read the recursion as supplying the shape; or test this on a
coarse period -- `84` fixes the coordinate only to `1.9e-3` and sees 85%
monotonicity, which looks like noise and is resolution.
Left open, and not killed: the fitted `1/d` coefficient `b` runs `1.93` to
`3.01` by class against the `3 theta / 2 = 1.45` that the exponent `-3/2`
predicts, while `b/a` is nearly constant at `40.8`. That is a tension in the
measured shape, not a refutation of it.
Machinery: `certificate_increment`; dossier
[juggler_certificate_increment](../problems/juggler_certificate_increment.md).
No bound moves.

**And the laboratory's own structure does not produce \(R\) either,
16 September 2026**
(`J-tail-does-not-determine-the-boundary-fraction`). Killed claim: that
the settled tail determines the boundary fraction. With the profile
fixed as \(\Pi_\phi(m)=A(\phi)(m+\gamma-\phi)r_*^m\) for \(m\ge1\)
(`J-profile-is-linear-times-geometric-in-the-line-coordinate`) and \(A\)
following an explicit cocycle whose only input is \(R\)
(`J-tail-amplitude-is-a-cocycle-over-the-boundary-fraction`), the
normalisation \(R+\sum_{m\ge1}\Pi_\phi(m)=1\) is exact and that tail sum
is closed-form, so extrapolating the tail down to \(m=1\) would
*compute* \(R\): the phase-indexed apparatus would collapse to a single
scalar recursion over the rotation and the clean coordinate would stop
being measured. **It fails, and the failure is converged.** At
\(306/485\) the residual \(R-R_{\mathrm{pred}}\) reads
\(+2.33\cdot10^{-2}\), \(+7.12\cdot10^{-3}\), \(+3.52\cdot10^{-3}\),
\(+3.52\cdot10^{-3}\) at caps \(400,800,1600,3200\) for phase \(0\) ---
identical at the last two to three figures --- and likewise
\(-7.38\cdot10^{-4}\), \(-2.76\cdot10^{-4}\) and \(+3.90\cdot10^{-3}\)
at phases \(23\), \(46\) and \(69\).
**What the residual is: exactly minus the boundary-layer mass.** The
normalisation being exact, the residual equals the extrapolated tail sum
less the true sum over \(m\ge1\), which is the mass the pure tail misses
at the barrier --- the complex boundary modes
`J-tail-spectral-gap-closes-like-one-over-root-q` locates numerically at
\(0.44893\pm0.11047i\) for this barrier. Over 200 phases it runs
\(-2.941\cdot10^{-3}\) to \(+7.318\cdot10^{-3}\) with mean
\(+1.076\cdot10^{-3}\), that is \(-3.3\%\) to \(+9.8\%\) of \(R\), and on
this evidence it has no simple rule: not the rise letter (means
\(8.7\cdot10^{-4}\) against \(1.19\cdot10^{-3}\), with standard
deviations \(8.9\cdot10^{-4}\) and \(2.25\cdot10^{-3}\) swamping the
gap), and correlating only weakly with the phase (\(0.19\)) or with
\(R\) itself (\(-0.16\)).
Kind: `REFUTED`.
Consequence: the description of the profile costs one constant, one
cocycle and \(R\), and this measures how close the first two come to
determining the third --- within about five percent typically, and never
exactly. Do not reopen the closed-form tail sum as a route to \(R\), and
do not expect a finer extrapolation or a deeper cap to close the gap:
the residual is already converged by cap \(1600\), so what is missing is
the boundary layer itself and not precision. \(R\) stays the fundamental
unknown, and the open obligation of
`J-boundary-fraction-is-the-clean-coordinate` is not reduced by
structure work of this kind. Machinery: `tail_predicts_boundary`.

**Externals that are already imported; do not propose them as new.** The
ANTEDB of Tao--Trudgian--Yang (arXiv:2501.16779) is already consulted at
its August 2026 vertices and moves neither \(95/112\) nor \(275/388\)
([exponent_pair_two_monomial](../theory/exponent_pair_two_monomial.md));
and the question there needs \(\tfrac54p+q<\tfrac23\) against a hull
minimum \(95/112\), so any pair below the line is itself a subconvexity
result past \(1/12\) --- not an optimisation run. Wiener--Hopf, Spitzer
and the Brownian meander are in use. Piatetski--Shapiro is a dossier
already ([juggler_ps_inversion_barrier](../problems/juggler_ps_inversion_barrier.md)).

**The nearest external result stops short of the exponent.**
Spiegelhofer's normality of the Thue--Morse sequence along
\(\lfloor n^c\rfloor\) is proved for \(1<c<4/3\) (arXiv:1707.05112) and
extended to \(c<3/2\); \(c=3/2\) is excluded either way. It is in any
case a *harder* statistic than the one needed --- Thue--Morse is the
digit-sum parity, while the Juggler letter is \(\lfloor n^{3/2}\rfloor
\bmod 2\), whose single-step equidistribution is classical --- and the
difficulty here is the iterated/joint version. Adjacent, not applicable.

There is no research literature on Juggler termination; public
verification stands at \(7110200\) against the laboratory's certified
floor \(N_0=3.5\cdot10^8\).
**Rhin equation (8) is dead, read at source 16 September 2026**
(`J-rhin-eight-has-no-computed-threshold`). It had stood in the audit as the
best available improvement --- \(L^{14.3}\to L^{8.616}\) on the effective cycle
threshold --- pending only a look at p. 160. The Proposition gives (7)
\(\lvert\Lambda\rvert\ge H^{-13.3}\) for \(H\ge2\) unconditionally, and (8)
\(\lvert\Lambda\rvert\ge H^{-7.616}\) only for \(H\ge H_0\) with \(H_0\)
*effectivement calculable* and never calculated. That is the Wu-Wang failure
mode exactly, and by `J-wuwang-effectivity-is-a-saddle-point-cost`
\(H_0=\exp(\Theta(n_0))\) sits astronomically above the \(L\lesssim10^6\) a
cycle search reaches. Appendix 2 p. 162 does print the entire construction
(two integrals, six explicit \(Q_i\) and \(b_i\), verified here by the degree
identity \(\sum b_i\deg Q_i=2\) and by the two Laplace rates agreeing to
\(7.3\cdot10^{-6}\)), so \(H_0\) is computable in principle --- computing it
still would not help, for the reason just given.

Do not: re-propose ANTEDB, Wiener--Hopf, Piatetski--Shapiro or the
digit-sum line as new external inputs; expect Denisov--Sakhanenko--Wachtel
to supply the prefactor; search again for a driven-critical renewal theorem;
re-run the \(q\)-uniformity measurement --- it is done, and its answer is
that the driving is benign; or reopen Rhin (8), whose constant does not
exist in print and would not close anything if it did.
Members: `J-tail-does-not-determine-the-boundary-fraction`. The rest of this
cluster records the state of the external literature rather than a laboratory
claim.
