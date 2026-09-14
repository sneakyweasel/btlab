# Juggler Paper C formal layer: three small formal attacks and a build root

Status: **PROMOTE** (three lemmas of Paper C moved from human proof to
kernel-checked Lean and the paper's table, Appendix A and Appendix B
updated in place; Paper C now has a barrel and an axiom artifact like
Papers A and B; nothing with analytic content was touched)

Not a new theorem about the map, not a density estimate, not a halt
theorem. The objects are Paper C
([juggler_fate_almost_all_note.md](../theory/juggler_fate_almost_all_note.md))
Lemma 4.1, Lemma 5.1 and Proposition 6.3(i), and the paper's own
verification table.

## Problem

How much of Paper C is Lean, and which of its human-proof statements are
small enough to formalize without inventing anything?

## Exact statement

Three statements, each now a Lean theorem with the paper's proof, and
(second pass, same day) Lemma 8.2 with the exact skeleton of Theorem 8.3.

**Lemma 4.1 (sweep; EXACT — LEAN VERIFIED, `FateSweep.lean`).** Let
\(x_0<\dots<x_{H-1}\) be reals with consecutive gaps in \([a,b]\),
\(0<a\le b\le\tfrac12\), \(b\le\tfrac{21}{20}a\) and \((H-1)a\ge 12\).
Then \(\#\{j:\{x_j\}<\tfrac12\}\ge H/7\) and
\(\#\{j:\{x_j\}\ge\tfrac12\}\ge H/7\); with the left-open half-cells,
i.e. the representative \(x-\lceil x\rceil+1\in(0,1]\), at least \(H/7\)
have representative \(\le\tfrac12\) and at least \(H/7\) have it
\(>\tfrac12\). Lean: `sweep_fract_lt_half`, `sweep_fract_ge_half`,
`sweep_rep_le_half`, `sweep_rep_gt_half`, all instances of
`Sweep.sweep_cell` (each residue of \(\lfloor 2x_j\rfloor\bmod 2\) holds
at least \(H/7\) terms).

**Lemma 5.1 (recursion; EXACT — LEAN VERIFIED, `FateRecursion.lean`).**
With \(e_i\in[e_{\min},e_{\max}]\subset(0,1)\), \(\lambda>0\),
\(\zeta=\sum_ic_ie_i^\lambda-1>0\), errors \(0\le\eta_i\le c_i\),
\(\sum_i\eta_i(t)e_i^\lambda\le\zeta/3\), \(\eta_0(t)\le\tfrac{2\zeta}3c_0\)
for \(t\ge t_1\), a seed \(g\ge c_0>0\) on \([e_{\min}t_1,t_1]\), and
\(g(t)\ge\sum_i(c_i-\eta_i(t))g(e_it)-\eta_0(t)\) for \(t\ge t_1\):
\(g(t)\ge c_0t_1^{-\lambda}t^\lambda\) for all \(t\ge e_{\min}t_1\).
Lean: `recursion_lemma`. The hypotheses \(\lambda<1\) and \(g\ge 0\) of
the paper are not needed.

**Proposition 6.3(i) (EXACT — LEAN VERIFIED, `FateFirstLetter.lean`).**
If some positive integer does not reach \(1\), the failure set has a
least positive member, and it is odd with an odd image. Lean:
`exists_minimal_failure`, `minimal_failure_odd_odd`, stated for any
forward-closed class excluding \(1\) (`minimalMember_odd`,
`minimalMember_image_odd`). The three first-letter pieces of Section
6.2 are `first_letter_trichotomy` and `first_letter_pieces_disjoint`.

**Lemma 8.2 and Theorem 8.3 (EXACT — LEAN VERIFIED, `FateChernoff.lean`).**
For \(C\ge 5\), \(d\ge CL\), \(d\ge 1\): at most \(2^d2^{-e(C)L}\) words
of length \(d\) are \(L\)-bad (`LBad_count_le`), by the Markov tilt of
`RateFreeDensity` on the constant weight at \(x=p_C/(1-p_C)\) and Gibbs'
inequality. With a floor \(N_0\ge 2\), the odd failures in \((y,2y]\)
lie in the cylinders of the envelope-bad words
(`oddFailures_subset_bad_cylinders`), which are \(L(y)\)-bad
(`LBad_of_envelopeBad`), so a bound \(M\) on every bad cylinder of depth
\(d\ge CL(y)\) gives \(\#\{\text{odd failures}\}\le 2^d2^{-e(C)L(y)}M\)
(`oddFailures_card_le_chernoff`), and with \(d=\lceil CL(y)
ceil\) and
\(\mathrm H(C,A)\)'s bound on the \(O\)-rooted bad cylinders,
\(\#\{\text{odd failures}\}\le y\Lambda^{-e(C)}+2\Lambda^Cy(\log y)^{-A}\)
at every \(y\ge 2\) (`oddFailures_card_le_explicit`), a factor \(2\)
against the paper's \(y/2\) and no \(arepsilon\). The absorption into
the displayed form and Corollary 8.4 stay human proofs.

**Theorem 9.2 (EXACT — LEAN VERIFIED, `FatePressure.lean`).** On the
live weight of `LiveCountWeight`: the live pressure is the generating
function of the live weight, a live start at depth \(d\ge CL(N)\) has
at least \(p_Cd\) odd letters (Lemma 8.1 on live starts), and a
pressure bound \(Na_\theta^dE\) at the tilt \(x=p_C/(1-p_C)\) gives at
most \(N\exp(-dD(p_C\|\tfrac12))E\) live starts
(`live_count_le_of_pressure`). The \(o(d)\) bookkeeping stays human.

**Lemma 5.2 (seed; EXACT — LEAN VERIFIED, `FateSeed.lean`).** A nonempty
backward-closed class contains some \(m\ge 3\)
(`exists_ge_three_of_backwardClosed`). For every \(y\ge(m+1)^4\), the
log-mass on \((\sqrt y,y]\) is at least the paper's
\(c_A=(1-2/m^4)(3/8\cdot 1/(m+1)-1/((m+1)^2-1))\) (`seed_lemma`,
`seed_constant_pos`).

**Theorem 7.2 (EXACT — LEAN VERIFIED given Theorem 5.3,
`FateTaoReduction.lean`).** A forward-closed class excluding \(1\)
whose odd members satisfy the rate \(y(\log y)^{-e}\) and whose
log-mass is at least \(K(\log x)^\lambda\) whenever nonempty, with
\(e>1-\lambda\), is empty of positive members
(`tao_rate_implies_empty`, `tao_rate_implies_conjecture` on the
failure set). The contagion bound itself stays a human proof.

**Theorem 5.3 given (5.2), Theorem 7.3, and Corollary 8.4 through (5.2)
(EXACT — LEAN VERIFIED given hypotheses, `FateContagionBound.lean`).** For
a backward-closed class with a positive member, every \(0<\lambda\le 0.49\),
and the production inequality
\(g_A(t)\ge\sum_i(c_i-\eta_i(t))g_A(e_it)-\eta_0(t)\) for \(t\ge t_0\)
with vanishing errors, \(g_A(t)\ge Kt^\lambda\) for all large \(t\)
(`contagion_of_production_inequality`), hence
\(\sum_{n\le x,n\in A}1/n\ge K(\log x)^\lambda\)
(`logMass_contagion_of_production`); \(\zeta(0.49)>0\) is `zeta_pos_49`,
by eight exact rational bounds \(r_i^{100}\le e_i^{49}\), and \(\zeta\)
is antitone (`zeta_antitone`). Theorem 7.3 with the contagion bound as a
hypothesis is `tao_rate_iff_conjecture`; Corollary 8.4 with Theorem 5.3
discharged through (5.2) is `conjecture_of_cylinder_bound_of_production`.
The production inequality itself and the root \(\lambda^{**}\) stay
human.

**The build root (COMPUTATIONALLY VERIFIED).**
`formal/Problems/JugglerFatePaper.lean` imports exactly the twenty-seven
modules Paper C cites; `formal/AxiomCheckPaperC.lean` prints the axioms
of the 351 cited declarations and `AxiomCheckPaperC.expected` records
them, every list a subset of `propext`, `Classical.choice`,
`Quot.sound`, no `sorryAx`, no `native_decide`.

**Shared numerics (EXACT — LEAN VERIFIED, 13 September 2026).** Lemmas
4.2, 4.3 and 8.2 certified their real powers by one move, raise both
sides to the \(n\)-th power where \(pn\) is an integer, and stepped
their fibers by Bernoulli's inequality about a point, each with a
private copy. `FateNumerics.lean` holds the two moves once:
`Numerics.rpow_le_iff_pow` and its three siblings
(\(x^p\le c\iff x^{pn}\le c^n\), the reverse, the strict forms) and
`Numerics.bernoulli_ge` / `Numerics.bernoulli_le`
(\((a+h)^p\gtrless a^p+pa^{q}h\) with \(p=q+1\)). The eleven sites in
`FateFiberParity`, `FateThinFibers` and `FateChernoff` are one to three
lines each; no statement changed. Nothing here is about the map.

**Shared counting (EXACT — LEAN VERIFIED, 13 September 2026).** Lemmas
4.1, 4.1' and 4.3 all count a separated sequence inside a window: the
steps telescope, so a sequence rising by at least \(d\) puts at most
\(w/d+1\) terms into a window of width \(w\). Lemma 4.1 reads the
window as a half-cell and gets \(\lfloor 1/(2a)\rfloor+1\) per cell;
Lemma 4.3 reads it as an arc inside an integer window.
`FateWindowCount.lean` states both for an arbitrary \(f\colon\mathbb{N}\to\mathbb{R}\)
(`WindowCount.span_ge`, `WindowCount.span_le`,
`WindowCount.mono_of_stepGe`, `WindowCount.window_card_le`,
`WindowCount.window_card_le_nat`), and `FateSweep` and `FateThinFibers`
call them: four inductions and two `min'`/`max'` arguments became one
of each, 111 lines out for 43 in, no statement changed. The six further
copies in `FateSweepMonotone` belong to the WIZARD session and were
left alone; that session has been sent the interface.

**The exact layer of identity (6.1) (EXACT — LEAN VERIFIED, 13
September 2026).** The paper's table called (6.1) a human proof of
exact combinatorics. The exact part is now Lean: `first_letter_split`
says that for any weight and any finite index set the weighted mass of
a two-way closed class is the sum of its even, \(OE\)-type and
\(OO\)-type pieces, each indexed by its image lying in the class as
the paper indexes it; `shellLogMass_split` is the log-mass form on a
shell. The free term's \(n(m)\) is well defined because \(J\) is
strictly increasing on the odd integers (`floorPower_odd_lt`,
`floorPower_odd_injective`), and `sum_image_ooPiece` rewrites that
piece as the paper's sum over the odd images. What stays human is the
normalization: the densities \(\varphi_A\), \(\varphi^{\rm fib}_A\)
and \(\psi_A\), the identification of each piece with its term, and
the boundary error \(O(e^{-t/4}/t)\) of Lemma 3.1.

**The exact landing window of a nested production (EXACT — LEAN
VERIFIED, 13 September 2026).** Appendix D.1 opens with an exact
claim, (D.1): along a production the two-step map is
\(F(u)=\lfloor u^{3/4}\rfloor\), and
\(\{n:a\le F(n)<b\}=[\Phi(a),\Phi(b))\) with
\(\Phi(a)=\lceil a^{4/3}\rceil\). In exact arithmetic
\(\Phi(a)\) is the least \(n\) with \(a^4\le n^3\), and the
two maps are a Galois connection: `windowStart a ≤ n` and
`a ≤ cell34 n` are both the inequality \(a^4\le n^3\). (D.1) is
then one rewrite (`exact_endpoints`), and the nested window (D.2)
one induction (`exact_endpoints_iterate`). `cell34_eq_floorPower_two`
records that \(J^2=F\) on an \(OE\) step. What stays human is what
the appendix does with the window: the smooth comparison (D.3), the
endpoint error, the multiplicities, and the production inequality
(5.2) they feed.

**The cylinder-splitting identity (EXACT — LEAN VERIFIED, 13
September 2026).** Section 10(d) records
\(\sum_wD(w)^2=2^{-t-2}\sum_S|W_{S\cup\{t\}}|^2
=\tfrac12\mathcal C_{t+1}-\tfrac14\mathcal C_t\) for the
first-letter biases \(D(w)=\#[wO]-\#[w]/2\). The second equality
is counting, and is the one the argument uses: it is
`CylinderEnergy.sum_bias_sq`, for an arbitrary finite set of starts.
The input is that a cylinder splits into its two children
(`wordCount_split`), because the \((t+1)\)-st letter of an
itinerary is the parity of the \(t\)-th image
(`itinerary_succ_append`); the rest is
\((b-\tfrac{a+b}2)^2=\tfrac{a^2+b^2}2-\tfrac{(a+b)^2}4\). The
Parseval equality with the Walsh sums is not formalized, and neither
is the exceptional-atom estimate it is meant to supply.
Twenty-four Lean rows, four human.

**Proposition 4.4 given its exponential-sum bounds (EXACT — LEAN
VERIFIED for the deduction; the bounds are HYPOTHESES, 13 September
2026).** The proposition is an exponential-sum estimate, and the
estimate is not formalized: Vaaler's interval approximation, the
second-derivative test and Kusmin--Landau are nowhere in the
repository, and Mathlib does not carry them. What
`FateBlockAverage.lean` has is the layer around it. The paper's
\(I(m')=[m'^{8/3},(m'+1)^{8/3})\) is exactly the odd \(n\) with
\(m'^2\le\lfloor n^{3/4}\rfloor<(m'+1)^2\), by the landing window
(`mem_oddBlock`); \(U(m')\) is the disjoint union of the even-image
parts of the fibers \(\Phi(m)\) over the even \(m\) of the block,
so the block average is an average of Lemma 4.2's fiber counts
(`U_card_eq`); and expanding the two parity indicators gives the
four sums exactly, \(4|U(m')|=M+S_1+S_2+S_{12}\)
(`four_card_U`). Equation (4.1) then follows from bounds on the
three parity sums by a triangle inequality
(`block_average_of_bounds`, `block_average_bound`), the bounds being
hypotheses.

**Second pass, the same day.** One of the three sums needs no
analysis. The slow sum \(S_1=\sum\psi(\lfloor n^{3/4}\rfloor)\) is
the alternating sum \(\sum_m(-1)^m|\Phi(m)|\) over the block
(`slowSum_eq_fibers`); the fiber bounds
\(\tfrac23m^{1/3}-1\le|\Phi(m)|\le\tfrac23(m+1)^{1/3}+1\)
(`FiberParity.oeFiber_card_ge`, the new `FiberParity.oeFiber_card_le`
by the descending Bernoulli step of `FateNumerics`) make consecutive
fibers differ by at most two members (`oeFiber_card_succ_diff`), and
the block pairs off into \(m'\) differences plus one fiber, so
\(|S_1|\le 2m'+\tfrac23(m'+1)^{2/3}+1\) (`slowSum_abs_le`), the
paper's \(O(m')\) with a constant. The same fiber bounds pin the odd
count of the block two-sidedly (`oddBlock_card_le`,
`oddBlock_card_ge`), so \(|M/4-m'^{5/3}/3|\le m'+1\)
(`oddBlock_quarter_close`). Equation (4.1) now needs only the fast sum
and the product sum (`block_average_two_bounds`;
`block_average_bound_two` in the paper's shape, \(C_B=C/2+2\)), and
the asymptotic form holds with the explicit error \(B/2+2(m'+1)\)
(`block_average_asymptotic`). The row stays **human proof**, because
the two remaining sums are the exponential sums and are the
proposition; the row says which parts are Lean.

**The share law's exact layer (EXACT — LEAN VERIFIED, 13 September
2026).** Lemma 4.5 is an equidistribution statement and Corollary
4.6 is measure theory; neither is formalized. `FateShareLaw.lean`
has the exact mathematics both rest on. The expansion of the fiber
phase about its first term,
\(x_j=x_1+\tfrac32\sqrt{n_1}(j-1)+\tfrac34(j-1)^2/\sqrt{n_1}+E_j\)
with \(|E_j|\le\tfrac14(j-1)^3n_1^{-3/2}\), is `xval_expansion`;
the paper's Taylor step becomes, after \(v=\sqrt{1+u}\), the
polynomial inequality
\(0\le1+\tfrac32(v^2-1)+\tfrac38(v^2-1)^2-v^3\le(v^2-1)^3/16\)
(`taylor_three_halves`), and on a fiber the remainder is at most
\(\tfrac2{27}(m+1)/m^2\) (`xval_expansion_fiber`, the paper's
\(O(1/m)\) with a constant). The range of the quadratic phase
\(\beta s+\tfrac13s^2\) on \([0,1]\) in Corollary 4.6(2)'s three
cases is `phiRange`, attained and never exceeded, and it is at most
\(\tfrac12\) exactly for \(\beta\in[-\tfrac56,\tfrac16]\)
(`phiRange_le_half_iff`). The integral of Corollary 4.6(3),
\(\tfrac1{72}+\tfrac{11}{108}+\tfrac{11}{108}+\tfrac1{72}=\tfrac{25}{108}\),
is `integral_extremeMeasure`, an interval integral over the four
polynomial pieces. What stays human: the reduction modulo 1 with its
\(O(1/H_m)\) error, the inverse-image and grid-sampling estimates,
Fubini in (1), and the identification of the \(\theta\)-measure
with \(\max(0,\tfrac12-\text{range})\). The row stays **human
proof** and says which parts are Lean. Nothing in Sections 5--10
depends on this subsection.

**The production inequality without its exponential sums, and an
unconditional theorem (EXACT — LEAN VERIFIED, 13 September 2026).**
Section 5.1 builds (5.2) from three families. Two of them need no
analysis: the \(E\)-images of the members at scale \(t/2\) through
Lemma 3.1 (`Production.family_E`), and the \(OE\)-fibers of the
members at scale \(3t/4\) through Lemma 4.2 on the good fibers and
Lemma 4.3 for the bad ones (`Production.family_OE`, on the per-fiber
bound `good_fiber_logMass_ge`, \((2/9)(1-\tfrac{25}2m^{-1/3})/m\)).
Together, with the paper's \(\sqrt x\) read as \(\lfloor e^{t/2}\rfloor\)
(`sqrt_floor_exp`), they give
\(g_A(t)\ge(1-4e^{-t/4})g_A(t/2)+(\tfrac29-\tfrac{50}9e^{-t/8})g_A(3t/4)-\eta_0(t)\)
for \(t\ge40\), every error explicit (`production_two`). The recursion
lemma on these two productions, with \(\zeta(3/10)>0\) certified by
two rational bounds (`zeta2_pos`), then gives **Theorem 5.3 for every
\(0<\lambda\le3/10\) with no hypothesis at all**
(`contagion_elementary`, `logMass_contagion_elementary`), and Corollary
5.5(2) at that exponent (`failures_logMass_ge`). The root of
\(2^{-\lambda}+\tfrac29(\tfrac34)^\lambda=1\) is about \(0.325\). The
third family, the \(OE\)-images of \(E\)-blocks through Proposition
4.4, is what carries the exponent to \(0.49\), and it needs the two
exponential-sum bounds that `FateBlockAverage` takes as hypotheses; the
ladder (5.10) needs Appendix D. So (5.2) itself stays a human row, and
the table gains a Lean row for the unconditional \(3/10\).

**The conjecture from a rate, with no other hypothesis (EXACT — LEAN
VERIFIED, 13 September 2026).** Theorem 7.2 and Corollary 8.4 take the
contagion bound as a hypothesis in exactly the shape
`failures_logMass_ge` provides at exponent \(3/10\). Composing them:
if the odd failures in \((y,2y]\) number at most \(y(\log y)^{-e}\)
for all large \(y\) and some \(e>\tfrac7{10}\), every positive integer
reaches \(1\) (`Production.conjecture_of_tao_rate`); and a
cylinder bound \(\mathrm H(C,A)\) at all large scales with
\(A>C+e(C)\) and \(e(C)>\tfrac7{10}\), above a certified floor,
does the same (`Production.conjecture_of_cylinder_bound`).
Nothing is assumed on the contagion side. The paper's conditional
forms need \(e>1-\lambda^{**}\approx0.51\) together with (5.2); the
price of dropping the exponential sums is the rate \(0.7\) in place
of \(0.51\). Whether a cylinder bound of that strength is provable is
the open analytic question of Appendix C; nothing here decides it.

**Theorem 9.1 without the martingale (EXACT — LEAN VERIFIED, 13
September 2026).** The paper proves the one-sided form with the
Azuma--Hoeffding inequality on a stopped martingale and remarks, after
Proposition 9.3, that exponential moments give an exponent at least as
good. `FateOneSided.lean` carries out the remark exactly. The tilted
mass of the \(L\)-bad cylinders of depth \(t\),
\(\sum_{w\ \text{bad}}\#[w]\,x^{o(w)}\) (`OneSided.badMass`), obeys
\(\mathrm{badMass}(t+1)\le(1+(x-1)q)\,\mathrm{badMass}(t)+(x-1)\,\mathrm{err}\,(2x)^t\)
under the one-sided hypothesis (`OneSided.badMass_succ_le`), because
bad words are prefix-closed and a cylinder splits into its two
children; unrolled (`OneSided.badMass_le`) and combined with Lemma 8.1
and the Markov tilt (`OneSided.oddFailures_card_le_badMass`), the odd
failures of \((y,2y]\) number at most
\((xa_q^{d-1}N+(x-1)\,\mathrm{err}\,(d-1)(2x)^{d-1})/x^{p_Cd}\) at
every scale, every depth \(d\ge CL(y)\) and every tilt \(x\ge1\)
(`OneSided.one_sided_bound`), with main term \((x/a_q)Ne^{-dD(p_C\|q)}\)
at the re-centring tilt (`OneSided.one_sided_bound_kl`). No martingale,
no stopping, no \(\varepsilon\). What is not Lean: the error carries
\((2x)^{d-1}/x^{p_Cd}\) where the paper's Markov step carries \(2^d\),
so absorbing it into the rate needs \(A>C(1+(1-p_C)\log_2x)+r\) rather
than \(A>C+r\); that absorption, the substitution
\(d=\lceil CL(y)\rceil\) and the displayed asymptotic form stay human,
and so does the rest of the Section 8--10 bookkeeping, which keeps its
human row with Theorem 9.1 added to the exact exceptions. Twenty-six
Lean rows, four human.

**The conjecture from the one-sided hypothesis (EXACT — LEAN VERIFIED,
14 September 2026).** The rate-side jaw of the pincer, closed for the
one-sided form as Corollary 8.4 closed it for the cylinder form.
`FateOneSidedCorollary.lean` takes \(\mathrm H_q(C,A)\) at all large
scales (`OneSided.OneSidedBound`), absorbs the exact bound of Theorem
9.1 into the rate \(y(\log y)^{-e}\) for every \(e\) below the Chernoff
exponent \(e^{\rm Ch}_q(C)=CD(p_C\|q)/\ln2\) and every
\(A>C(1+\log_2x)+1+e\) (`OneSided.oddFailures_le_of_one_sided`, on
Gibbs' inequality and two scale comparisons), and composes with
Theorem 7.2: with the contagion bound as a hypothesis
(`OneSided.implies_conjecture_of_contagion`), or with nothing else
assumed when \(e^{\rm Ch}_q(C)>\tfrac7{10}\)
(`OneSided.one_sided_implies_conjecture`); the paper's remark after
Theorem 9.1, a share bound with no error term, needs no \(A\) at all
(`OneSided.exact_share_implies_conjecture`). So the most concrete
hypothesis in the corpus that implies no cycle and no divergent orbit
now runs to the conjecture inside Lean: if no \(L(y)\)-bad cylinder of
depth below \(\lceil CL(y)\rceil\) sends more than the share \(q<p_C\)
of its members to an odd letter, above the floor and at all large
scales, with \(CD(p_C\|q)/\ln2>0.7\), every positive integer reaches
\(1\). What is not Lean: the condition on \(A\) is sufficient and not
the paper's \(A>C+e_q(C)\), and the numerical forms (the least \(C\)
at each \(q\)) are human. Nothing here proves the hypothesis; it is
the analytic question of Appendix C in its one-sided dress.
Twenty-seven Lean rows, four human.

**The conjecture from the pressure and no-momentum hypotheses (EXACT —
LEAN VERIFIED, 14 September 2026).** The same jaw for the two other
forms of Section 9. A failure never enters the floor, so the odd
failures of \((y,2y]\) are live starts of \(\{1,\dots,2y\}\) at every
depth (`Pressure.oddFailures_subset_live`), which is the bridge from
the live weight of `LiveCountWeight`, where Theorem 9.2 and Proposition
9.3 live, to the failure set. `FatePressureCorollary.lean` takes
\(\mathrm P_\theta(C)\) at all large scales with the paper's
\(e^{o(d)}\) quantified as \((\log y)^\varepsilon\)
(`Pressure.PressureBound`), or \(\mathrm M_{\theta,q}(C)\) on the live
weight at the re-centring tilt with the \(o(d)\) as \(\delta d\)
(`Pressure.NoMomentumBound`), bounds the failures by
\(2y\,e^{-dD}(\log y)^\varepsilon\) through the exact forms, and absorbs
that into the rate \(y(\log y)^{-e}\) for every \(e<CD/\ln2-\varepsilon\)
by one shared lemma (`Pressure.absorb`). Then Theorem 7.2, with the
contagion bound as a hypothesis or with nothing else assumed when the
exponent exceeds \(\tfrac7{10}\) (`Pressure.pressure_implies_conjecture`,
`Pressure.noMomentum_implies_conjecture`). With the one-sided corollary
this closes the rate-side jaw of the pincer, in Lean, for every
hypothesis Paper C states on that side: cylinder, one-sided, pressure
and no-momentum. The numerical forms are human, and nothing here
proves any of the hypotheses. Twenty-eight Lean rows, four human.

**Theorem 9.1 with exceptional atoms (EXACT — LEAN VERIFIED, 14
September 2026).** Section 10(d)'s first paragraph says the one-sided
proof survives if the share bound fails on bad atoms of total mass
\(O((\log y)^{-B})\) at each depth. On the exponential-moment proof
this is one extra term: an exceptional bad atom sends at most its
whole mass to its odd child, which costs \((x-a_q)\#[w]x^{o(w)}\) in
the tilted mass, so the recursion gains \((x-1)(1-q)\,\mathrm{exc}\,x^t\)
next to the error's \((x-1)\,\mathrm{err}\,(2x)^t\)
(`OneSided.badMass_succ_le_exc`), and the rest is the same
bookkeeping through a one-tail lemma used twice (`OneSided.tail_le`).
The absorption needs \(B>C\log_2x+1+e\) for the exceptional mass,
\(C\) less than the error's \(A>C(1+\log_2x)+1+e\), because the
exceptional atoms are not doubled at each depth
(`OneSided.oddFailures_le_of_exc`); `OneSided.exc_implies_conjecture`
runs this weakest one-sided hypothesis to the conjecture with nothing
else assumed. The original hypothesis is the case of no exceptional
atoms (`OneSided.oneSidedBoundExc_of_bound`). What is not Lean: the
paper's \(B>e_q(C)\) is the Markov absorption of the martingale
proof and is not restated; the condition here is sufficient, not
sharp. This is the form the cylinder-energy statistic of Section
10(d) is meant to supply, so the analytic question now has a formal
target one Cauchy--Schwarz step away. Twenty-nine Lean rows, four
human.

## Current literature

- Paper C §1.4, Appendix A — `known`: the paper's own list of what is
  Lean. It was stale in one place: Proposition 9.3 was listed as a
  human proof after `TiltedShare.lean`
  ([failure margin](juggler_failure_margin.md)) proved it.
- Paper B's barrel `Problems.JugglerParityPaper` and
  `AxiomCheckPaperB` — `reproduced`: the same construction for Paper C.
- `Int.Ico_filter_modEq_card` (Mathlib) — `known`: the count of one
  residue class in an integer interval, used for the interior cells of
  one colour.

## Branch budget

```text
Mathematical target     Which human-proof statements of Paper C are
                        exact enough to be Lean, and are they.
Novelty hypothesis      None mathematical; the proofs are the paper's.
                        The laboratory gains a build root and an axiom
                        artifact for the third manuscript.
Falsifier               A proof that does not close in Lean without a
                        new idea, or a statement the Lean cannot cover
                        (then the row stays EXACT — HUMAN PROOF).
Already killed by?      none: no prior branch attempted these lemmas;
                        the ledger had no row for 4.1, 5.1 or 6.3(i).
Existing machinery      FateContagion.lean (closures, blocks, fibers),
                        floorPower_even_lt, floorPower_odd_even_two_step_lt,
                        RateFreeDensity / TiltedShare, formalpedia.
Maximum Phase-0 scope   Three modules, one barrel, one axiom artifact,
                        the paper's table and appendices. No analysis.
Promotion criterion     Not applicable: the statements are the paper's.
Stop criterion          All three compile without sorry, or one does not
                        and is recorded as deferred.
```

## Balanced-ternary formulation

None.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- The half-cell index \(\lfloor 2x\rfloor\): monotone along the
  sequence, rises by at most one per step when \(b\le\tfrac12\), even
  iff \(\{x\}<\tfrac12\) — **EXACT — LEAN VERIFIED** (`Sweep.cell_eq`,
  `Sweep.cell_succ_le`, `Sweep.cell_modEq_zero_iff`).
- The reflection \(x_j\mapsto -x_{H-1-j}\) carries closed half-cells to
  left-open ones and swaps nothing else — **EXACT — LEAN VERIFIED**
  (`sweep_ceil` from `Sweep.sweep_cell` with `Finset.sum_range_reflect`).
- Interior cells in place of traversed cells: at least \((T-3)/2\) of
  one colour against the paper's \(T_g\ge 10\); ratio \(11/25\) against
  \(10/23\); the final constant \(11/75>1/7\) is unchanged in kind —
  **EXACT — LEAN VERIFIED** (`Sweep.colour_cells_ge`, `Sweep.sweep_cell`).

## Experiments

- Probe: `research.juggler_sequence.paper_c_formal_layer` (reads the
  barrel, the artifact, Appendix A and the table; no computation on the
  map).
- Artifact: `data/research/juggler/paper_c_formal_layer/summary.json`.
- Tests: `tests/research/juggler_sequence/test_paper_c_formal_layer.py`,
  `tests/tools/test_formalpedia.py` (Paper C surface kernel-checked),
  `tests/research/juggler_sequence/test_layer_architecture.py`.
- Lean: `lake build Problems.JugglerFatePaper`;
  `lake env lean AxiomCheckPaperC.lean` reproduces the `.expected` file.

## Conjectures

None new.

## Counterexamples

None.

## Formalization

`formal/Problems/Juggler/FateSweep.lean` (26 declarations, namespace
`Sweep` for the cell machinery, five top-level theorems),
`formal/Problems/Juggler/FateSweepMonotone.lean` (Lemma 4.1'),
`formal/Problems/Juggler/FateRecursion.lean` (`recursion_lemma`),
`formal/Problems/Juggler/FateFirstLetter.lean` (7 declarations),
`formal/Problems/Juggler/FateChernoff.lean` (Lemma 8.2 and Theorem 8.3 in
explicit form, 31 declarations on `RateFreeDensity`'s word weights),
`formal/Problems/Juggler/FatePressure.lean` (Theorem 9.2 in exact form, 6
declarations on the live weight),
`formal/Problems/Juggler/FateTaoReduction.lean` (Theorem 7.2 given
contagion),
`formal/Problems/Juggler/FateSeed.lean` (Lemma 5.2),
`formal/Problems/Juggler/FateCylinderCorollary.lean` (Corollary 8.4 as the
composition of Theorems 8.3 and 7.2, 5 declarations),
`formal/Problems/Juggler/FateFiberParity.lean` (Lemma 4.2, fiber parity, 41
declarations in namespace `FiberParity`),
`formal/Problems/Juggler/FateThinFibers.lean` (Lemma 4.3, thin fibers, 17
declarations in namespace `FiberParity`),
`formal/Problems/Juggler/FateContagionBound.lean` (Theorem 5.3 given (5.2),
Theorem 7.3, Corollary 8.4 through (5.2), 21 declarations),
`formal/Problems/Juggler/FateOneSided.lean` (Theorem 9.1 in exact form by
exponential moments, 20 declarations in namespace `OneSided`),
`formal/Problems/Juggler/FateOneSidedCorollary.lean` (the conjecture from the
one-sided hypothesis, 12 declarations in namespace `OneSided`),
`formal/Problems/Juggler/FatePressureCorollary.lean` (the conjecture from the
pressure and no-momentum hypotheses, 11 declarations in namespace `Pressure`),
`formal/Problems/Juggler/FateOneSidedAtoms.lean` (Theorem 9.1 with exceptional
atoms, 14 declarations in namespace `OneSided`),
`formal/Problems/JugglerFatePaper.lean` (barrel),
`formal/AxiomCheckPaperC.lean` and `.expected`. All kernel-checked; the
Paper C surface (root `Problems.JugglerFatePaper`, 59 modules reached,
1745 declarations) carries no `native_decide` and cites none.

Not formalized, and not claimed:
Proposition 4.4, the share law 4.5–4.6, the production inequality (5.2)
(Theorem 5.3 is Lean given it, for \(\lambda\le 0.49\)), the unconditional
Theorems 7.2 and 7.3, the root \(\lambda^{**}\),
the asymptotic forms of Theorems 8.3 and 9.2, Theorem 9.1, Section 10, Appendix C, and the log-mass bookkeeping
that turns the first-letter trichotomy into the identity (6.1).

## Results

Classification **PAPER_C_LEAN_SURFACE_CONSISTENT**.

```text
  Paper C verification table, before and after
  Lean rows      15 -> 29  (Lemma 4.1', Corollary 8.4, Lemmas 4.2, 4.3, Theorem 5.3 given (5.2) and at 3/10, Theorem 7.3, (6.1), Section 10(d), (D.1), Theorem 9.1 exact, the three Section 9 consequences and the exceptional-atom form new)
  human rows     7 -> 4    (Proposition 4.4, the share law, the production inequality (5.2), Sections 8--10's asymptotics)
  cited names    135 -> 369, all on subsets of Mathlib's three axioms; none native_decide
```

- The three proofs are the paper's; the sweep count is the paper's
  with interior cells for traversed cells, which is one notion fewer
  and the same constant in kind.
- The recursion lemma holds under weaker hypotheses than printed:
  \(\lambda<1\) and \(g\ge 0\) are never used, and the extrema
  \(e_{\min},e_{\max}\) may be any bounds.
- The stale table line: Proposition 9.3 was Lean since
  `TiltedShare.lean` (row `J-tilted-share-telescoping`) and the paper
  still said human proof. Corrected in §1.4, §9.2 and Appendix A.
- Lemma 4.2 (13 September): the step of \(x(n)=n\sqrt n/2\) over two
  units is \((u^2+uv+v^2)/(u+v)\), bounded by \(\tfrac32v\) and
  \(\tfrac32u\) through two factorizations, monotone because the upper
  bound at \(n\) is the lower bound at \(n+2\); the paper's integral is
  not needed, and its \(1.02m^{-1/3}\) becomes \(m^{-1/3}\) because the
  upper step is taken at a fiber member. Both cases of the paper go
  through the monotone sweep of `FateSweepMonotone`.
- Lemma 4.3 (13 September): badness is membership in one of two arcs
  after a shift by \(22u^{-1/3}\) that unwraps the arc around \(0\);
  the arc count is the sweep's fibre-per-window argument with
  \(d=(2u)^{-1/3}\) in place of the paper's \((3u)^{-1/3}\), and the
  dyadic sum is a geometric series with \(2^{-1/3}\le 0.794\).
- Corollary 8.4 (13 September): the explicit bound of Theorem 8.3 is
  absorbed into the rate \(y(\log y)^{-e}\) for every \(e<e(C)\) once
  \(\log y\) is large (`oddFailures_eventually_le`), and the composition
  with Theorem 7.2 gives the conjecture from \(\mathrm H(C,A)\) with the
  contagion bound as the only analytic hypothesis
  (`cylinder_bound_implies_conjecture`). The threshold \(C\ge 19\) is a
  statement about \(\lambda^{**}\) and stays with the audit.
- Theorem 5.3 given (5.2), and Theorem 7.3 (13 September, later): the
  root \(\lambda^{**}\) is replaced by the rational \(\lambda=0.49\),
  where \(\zeta(0.49)=0.00168>0\) is certified by eight exact
  inequalities \(r_i^{100}\le e_i^{49}\) between 400-digit integers
  (`zeta_pos_49`); \(\zeta\) is antitone, so every \(\lambda\le 0.49\)
  inherits the theorem, and \(C\ge 19\) still clears the rate threshold
  (\(e(19)=0.527>0.51\)). The recursion never needs \(\eta_0\ge 0\).
  Theorem 7.3 is Theorem 7.2 plus the empty failure set, and Corollary
  8.4 now closes with (5.2) in place of the contagion bound
  (`conjecture_of_cylinder_bound_of_production`): from
  \(\mathrm H(C,A)\) to the conjecture, (5.2) is the only analytic input.

## Open questions

- Proposition 4.4 (the block average) is the first analytic step: an
  exponential-sum estimate. Not a small attack; with it, the whole
  fiber input of (5.2) would be Lean.
- The numerical threshold of Corollary 8.4 is now \(e(19)>0.51\)
  (with \(\lambda=0.49\)); it needs bounds on \(D(p_{19}\Vert 1/2)\) in
  Lean, not done. The range \(0.49<\lambda<\lambda^{**}\) of Theorem 5.3
  needs \(\lambda^{**}\) as a root (intermediate value theorem on
  \(\zeta\)); the constant certified is \(0.49\).

## Decision

**PROMOTE.** Lemmas 4.1', 4.2, 4.3 and Corollary 8.4 are now on the
barrel with the rest of the exact layer; the paper's headline
conditional result is one Lean theorem with one analytic hypothesis,
and every elementary step below the block average is Lean. Nothing here
changes a constant or an exponent. Best next question: none that is
small; Proposition 4.4 is the first analytic step. Later the same day,
Theorem 5.3 given (5.2) and Theorem 7.3 joined the Lean column
(`FateContagionBound.lean`). On 13 September the exact layer was
finished: the decomposition behind the identity (6.1) with the
uniqueness of the odd preimage (`FateFirstLetter.lean`), the landing
windows (D.1) and (D.2) of Appendix D.1 (`FateLandingWindow.lean`), and
the counting half of the Section 10(d) display
(`FateCylinderEnergy.lean`), together with two consolidations,
`FateNumerics.lean` and `FateWindowCount.lean`. The verification table
is twenty-nine Lean rows and four human, and the four are analysis: the
block average 4.4, the share law 4.5--4.6, the production inequality
(5.2), and the asymptotic bookkeeping of Sections 8--10, whose exact
forms (Lemma 8.2, Theorems 8.3, 9.1, 9.2, Proposition 9.3) are Lean. No small attack remains on this paper; what is left
needs either a genuine analytic argument or the hypothesis-as-input
treatment the large attacks use. The consolidation still open
(`FateSweepMonotone`'s six span inductions, its two window counts, the
log-mass forms, the repeated sweep hypotheses) sits in files the WIZARD
session owns and has been sent to it.

## Publication assessment

Status: `STRUCTURAL`. Paper C §1.4 and Appendix A updated in place; no
new manuscript sentence beyond the Lean citations.
