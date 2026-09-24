# Juggler `winkler_phase_collapse`

Winkler's normalised first-passage count, measured at every order rather than on the
record orders his theorem covers. Probe:
[winkler_phase_collapse.py](../../src/research/juggler_sequence/winkler_phase_collapse.py).
Test: [test_winkler_phase_collapse.py](../../tests/research/juggler_sequence/test_winkler_phase_collapse.py).
Ledger: `J-winkler-ratio-collapses-onto-the-phase`.

## Problem

Is Winkler's normalised count `R+_r = r c_r / C_r` of A100982 a function of the phase
`delta_r = {r log2 3}` alone?

## Exact statement

With `alpha = log2 3`, `m_r = floor(r alpha)`, `c_r = A100982(r) = M_(m_r + 1)` and
`C_r = binom(m_r - 1, r - 1)`: does there exist a function `F` on the circle with
`R+_r = F(delta_r) + o(1)` as `r` tends to infinity, and where is `F` discontinuous?

## Current literature

- `winkler-2026-admissible-qx1-sequences`, Corollary 12: `liminf R+_r = 1` and
  `limsup R+_r = alpha/(alpha - 1)`, attained exactly on the lower and upper record
  orders of `{r alpha}`. An envelope on two sparse sets of orders, with nothing said
  about a general `r`. The whole profile was first measured here; the qualitative specialization is now Lean-checked (Section 13 of the comparison note).
- `winkler-2026-marked-rotations`, Proposition 34: the asymptotic scale
  `C_r = kappa rho_alpha^(delta_r) B^r r^(-1/2) (1 + O(1/r))`, so the explicit part of
  the phase dependence sits in `C_r`, and `R+_r` carries the rest, bounded but unknown.
- Paper B, Section 6, and `J-paper-b-meander-prefactor-is-almost-periodic`: the survivor
  prefactor `psi({d beta})` with jumps on the orbit `{n beta}`, conjectural. Since
  `c_r = M_(m_r+1)` and `M_d = 2 N_(d-1) - N_d`, a limit for `psi` predicts one for
  `R+_r`. This branch measures the prediction on the other side.

## Branch budget

- **Target:** decide numerically whether `R+_r` depends on `r` only through `delta_r`.
- **Novelty hypothesis:** no public source describes `R+_r` away from the record orders.
- **Falsifier:** within-bin spread comparable to the across-bin range, or a shape that
  drifts between windows of `r`, or a shuffled-phase control that collapses as well.
- **Already killed by?:** none. Not a cycle, termination or floor claim, so none of the
  Diophantine walls or local-attack clusters in
  [negative_knowledge.md](../negative_knowledge.md) applies; it is a measurement on
  counts the laboratory already owns.
- **Existing machinery:** `jump_spectrum.survivor_counts`, the identity
  `c_r = M_(m_r+1)` of `J-winkler-sandwich-holds-on-the-laboratory-counts`.
- **Maximum Phase-0 scope:** one depth, 5000, three windows, one control.
- **Promotion criterion:** a stable collapse with a failing control.
- **Stop criterion:** any falsifier above.

## Balanced-ternary formulation

None. The object is the binary Beatty staircase of `log2 3`; balanced ternary plays no
role.

## Why BT may be relevant

It is not. The branch lives in the Collatz-side counting that Paper B shares with the
Juggler map.

## Candidate operations / invariants

The phase `delta_r`; the one-sided means of `R+` across an orbit point `{n alpha}`.

## Experiments

Depth 5000 gives the orders `r = 1..3154`. `c_r` reproduces A100982. Binned by
`delta_r` into 20 bins:

| window of r | across-bin range | within-bin spread | signal |
|---|---|---|---|
| 395 to 788 | 1.6852 | 0.0334 | x50.5 |
| 789 to 1577 | 1.6860 | 0.0324 | x52.0 |
| 1578 to 3154 | 1.6869 | 0.0326 | x51.7 |
| shuffled phases, 1578 to 3154 | | | x0.39 |

The per-bin shape drifts by 0.0069 and then 0.0011 between successive windows. Jumps
across the orbit points, one-sided windows of width 0.006, orders `r >= 1052`:

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| jump | +0.633 | +0.148 | +0.188 | +0.066 | +0.098 | +0.039 | +0.023 | +0.042 |

Six control points, at the midpoints of the widest gaps between the first 40 orbit
points, show +0.0017 to +0.0045. The first hand-picked controls were not controls: two
of four sat on orbit points 8 and 11, which is why the controls are now chosen by rule
and checked by a test.

## Conjectures

`R+_r = F(delta_r) + o(1)` with `F` rising from 1 at `delta = 0+` to `alpha/(alpha - 1)`
at `delta = 1-`, and upward jumps exactly on the orbit `{n alpha}`.

## Counterexamples

None found.

## Formalization

The original numerical investigation supplied no formalization. The 23 September
extension [BeattyPhaseTransfer.lean](../../formal/Problems/Juggler/BeattyPhaseTransfer.lean)
checks the two phase coordinates, exact normalized count identity, cancellation of
survivor jumps into certificate counts, and monotonicity, one-sided limits and jump
sizes of a summable positive series. Its moving-kernel convergence theorem assumes
uniform domination, fixed-index approximation and a vanishing far remainder.
The continuation in
[BeattyRenewalLimit.lean](../../formal/Problems/Juggler/BeattyRenewalLimit.lean)
and [BeattyRenewalSeries.lean](../../formal/Problems/Juggler/BeattyRenewalSeries.lean)
now proves the analytic inputs for coefficients of the formal exponential:
recurrence, summability, three-halves decay, the near/far split and moving limit.
[BeattySurvivorProfile.lean](../../formal/Problems/Juggler/BeattySurvivorProfile.lean)
reaches the existing `MeanderShape` for an explicit positive profile using the
actual survivor counts, conditional on the exact counting exponential identity
and the terminal binomial asymptotic. The new
[BeattyCounting.lean](../../formal/Problems/Juggler/BeattyCounting.lean)
discharges the actual counting input, and
[BeattyBinomialBounds.lean](../../formal/Problems/Juggler/BeattyBinomialBounds.lean)
proves coarse terminal bounds and unconditional sharp three-halves order.
The subsequent endpoint and certificate modules discharge the fine terminal
input and identify the complete jump series. The formal limit is `o(1)`;
the quantitative error remains written mathematics.

Extracted corollaries: the actual exponential identity is equivalent to the
purely integer recurrence `n N_n = sum_{j<n} T_(n-j) N_j`; coarse two-sided
square-root terminal bounds already imply sharp three-halves coefficient
order without a phase limit; and summability yields a uniform finite-profile
error bound at every phase, including jumps. These compile in the same
modules. Section 12 discharges the counting, coarse-bound and summability
premises at the logarithmic slope. See the
[comparison note](../theory/juggler_beatty_first_passage_note.md).

## Results

`J-winkler-ratio-collapses-onto-the-phase`, computationally verified: the collapse, its
convergence, the failing control, and the jumps on the orbit, as tabulated above.

**23 September: explicit profile and written convergence argument.** With
`beta = 1/alpha`, `q = 1-beta`, `B = alpha^alpha/(alpha-1)^(alpha-1)` and
`w_r = c_r/(B^r q^delta_r) = c_r beta^r q^(m_r-r)`, the new
[comparison note](../theory/juggler_beatty_first_passage_note.md) derives

    F(delta) = 1 + sum_{delta_r < delta} w_r,
    sum_r w_r = 1/(alpha-1),
    R+_r = F(delta_r) + O(r^(-1/2)).

The first jump is exactly `beta = 0.630929753571457...`. The written proof constructs
the survivor profile from the binomial-tail Spitzer series; it obtains the necessary
coefficient bound before passing to a limit, and handles the moving discontinuities
without continuity assumptions. The qualitative logarithmic-slope specialization is now an end-to-end Lean
theorem. The general irrational-slope statement and the quantitative rate
remain written mathematics; no manuscript revision is made.

New probe: [beatty_phase_transfer.py](../../src/research/juggler_sequence/beatty_phase_transfer.py).
Test: [test_beatty_phase_transfer.py](../../tests/research/juggler_sequence/test_beatty_phase_transfer.py).
Exact counts through depth 8000 give orders 1–5047; an independent binomial-coefficient
recurrence is checked through depth 256. The first eight predicted jumps agree with
the earlier window estimates at their resolution. Floating-point profile diagnostics
are not interval certificates.

**23 September: unconditional sharp order in Lean.** The exact integer
recurrence now holds for every degree, not merely through the finite check.
The first-term comparison `binom(n,k) <= T_n <= (5/2) binom(n,k)`, with
`k=floor(n*beta)+1`, and coarse global Stirling estimates imply square-root
terminal bounds. The compiled conclusion is `N_n=Theta(v^n/(n sqrt(n)))`,
with positive constants uniform at every positive depth. The existing
`survivorDensity =Theta[atTop] model` is therefore unconditional.
Summability of `N_n/v^n` is unconditional too; it makes the existing profile
bounds and uniform finite approximation applicable. The next continuation, recorded below, completes the fine phase limit
and the full certificate profile. No priority or
integer-trajectory termination claim is attached to this formalization.

Continuation triage: target the exact normalization and full jump formula; possible
novelty is the positive cumulative series, not the classical counting identity.
Falsifiers are a normalization mismatch, wrong jump signs or a nonvanishing
uncontrolled remainder. Already killed by? Neither the closed recurrence-only route
nor residue-class fitting applies: this uses the full generating-function identity.
Existing machinery is the exact DP, certificate recurrence and ladder profile.
Maximum scope: this comparison note, one bounded probe and one Lean transfer module.
Promote a checked formula with an explicit proof boundary; park the limit if its
tail interchange is unjustified. No next branch is opened.

**23 September: completed qualitative phase theorem.** The new endpoint module
proves the exact fractional-part Stirling correction and geometric-tail limit.
The critical mass module uses finite first moments and survivor decay to prove
first-passage mass one. The certificate series module proves positive weights,
total jump mass `1/(alpha-1)`, first jump `beta`, phase injectivity and exact
one-sided traces. The identification module proves equality of the full
transferred profile with `1+sum_{delta_r<delta}w_r` on `(0,1)`, including at
atoms. Finally `certificate_phase_asymptotic` proves the original
`r c_r/binom(m_r-1,r-1)-F(delta_r) -> 0` without unproved inputs. See Section 13
of the [comparison note](../theory/juggler_beatty_first_passage_note.md).

**23 September: complete accumulation set.** The new
[certificate cluster module](../../formal/Problems/Juggler/BeattyCertificateCluster.lean)
proves that all subsequential limits of `R+_r` form exactly the envelope
`[1,alpha/(alpha-1)]` with the open intervals
`(F(delta_j),F(delta_j)+w_j)` removed. This is a nonempty compact perfect set
of Lebesgue measure zero. Both endpoints of every gap are subsequential
limits; every closed interval strictly inside a gap is eventually avoided.
The generic geometry and recurrent-sampling argument are in
[BeattyProfileGeometry.lean](../../formal/Problems/Juggler/BeattyProfileGeometry.lean).
Section 14 of the comparison note records the proof and scope.

Continuation triage:

```text
Mathematical target     Identify all certificate accumulation values and exact gaps.
Novelty hypothesis      The specialization refines the known extremal envelopes;
                        the generic pure-jump geometry is not claimed new.
Falsifier               A missing continuous component or overlapping gaps.
Already killed by?      No matching obstruction; the proved exact series identity
                        removes the missing-component issue. No recurrence-only
                        shortcut or unproved frequency assumption is used.
Existing machinery      Positive weights, total mass, one-sided traces, phase limit.
Maximum Phase-0 scope   Generic range geometry and logarithmic-slope specialization.
Promotion criterion     Kernel-checked exact cluster set and null perfect geometry.
Stop criterion          A new unproved analytic premise is needed.
PROMOTE
```

**23 September: singular continuous empirical law.**
[BeattyCertificateDistribution.lean](../../formal/Problems/Juggler/BeattyCertificateDistribution.lean)
proves weak convergence of the actual normalized counts to the law of `F(U)`
for uniform `U`. Irrational Fourier cancellation proves equidistribution of
the exact phases. Almost-everywhere continuity of the monotone profile and
the existing vanishing count error then give the empirical limit. Strict
increase makes the law atomless; concentration on the null accumulation
set makes it singular. Its CDF is continuous, satisfies `G(F(t))=t` on
`[0,1]`, and equals `delta_j` throughout each closed jump interval. Empirical
frequencies converge at every real threshold. Section 15 of the
[comparison note](../theory/juggler_beatty_first_passage_note.md) records
the exact formulas and the distinction between limiting concentration and
finite-depth membership in the accumulation set.

Continuation triage:

```text
Mathematical target     Prove the empirical singular continuous certificate law.
Novelty hypothesis      Its explicit application to the original certificate counts;
                        the generic measure arguments are standard.
Falsifier               A positive-measure discontinuity obstruction.
Already killed by?      No matching obstruction; recurrence alone is insufficient,
                        so Fourier cancellation must establish equidistribution.
Existing machinery      Weyl criterion, exact phase asymptotic, null perfect limit set.
Maximum Phase-0 scope   Phase equidistribution, passage through F, and law properties.
Promotion criterion     Kernel-checked empirical convergence with all inputs discharged.
Stop criterion          An additional unproved analytic premise remains.
PROMOTE
```

**23 September: two-thirds Cantor geometry.**
[BeattyCertificateWeights.lean](../../formal/Problems/Juggler/BeattyCertificateWeights.lean)
proves `r sqrt(r) w_r-kappa F(delta_r)->0` and global positive two-sided
`r^(-3/2)` gap bounds. The exact metric neighbourhood formula
`lambda(K_epsilon)=2 epsilon+sum_r min(w_r,2 epsilon)` and the bounds
`c epsilon^(1/3)<=lambda(K_epsilon)<=C epsilon^(1/3)` are checked in
[BeattyCertificateCantor.lean](../../formal/Problems/Juggler/BeattyCertificateCantor.lean).
The logarithmic neighbourhood-volume limit is exactly `2/3`, giving
Minkowski dimension in the tube convention. Section 16 of the working note
also records the elementary covering-number equivalence with box dimension.
This gives positive finite lower and upper Minkowski contents; the next
continuation identifies their common value. The original-count consumer audit
checks the public interfaces and their standard dependency sets.

Continuation triage:

```text
Mathematical target     Prove |K_epsilon| comparable to epsilon^(1/3).
Novelty hypothesis      Exact geometry of this certificate accumulation set;
                        the generic gap-length method is classical.
Falsifier               Failure of positive two-sided r^(-3/2) gap bounds.
Already killed by?      No matching obstruction: the complete phase theorem
                        supplies the input missing from recurrence-only routes.
Existing machinery      Stirling limit, exact positive gaps and total jump mass.
Maximum Phase-0 scope   Gap bounds, exact tube formula and dimension limit.
Promotion criterion     Kernel-checked result for the actual count cluster set.
Stop criterion          An additional unproved analytic premise is required.
PROMOTE
```

**23 September: exact Minkowski content.** The actual gap-counting function
`N(x)=#{r>=1:w_r>=x}` satisfies `x^(2/3)N(x)->A`, where
`A=kappa^(2/3) integral_0^1 F(t)^(2/3) dt>0`.
[BeattyPhaseCounting.lean](../../formal/Problems/Juggler/BeattyPhaseCounting.lean)
proves the moving-cutoff limit by finite phase partitions and its stability
under vanishing perturbations. The certificate weights are specialized in
[BeattyGapCounting.lean](../../formal/Problems/Juggler/BeattyGapCounting.lean).
Integration of the counting function gives
`lambda(K_epsilon)/epsilon^(1/3)->3*2^(1/3)*A` in
[BeattyCertificateContent.lean](../../formal/Problems/Juggler/BeattyCertificateContent.lean).
Moreover `A=kappa^(2/3) integral y^(2/3) dmu(y)`, identifying the geometric
constant through the singular empirical law. All concrete premises are
discharged. The generic gap-to-content implication is classical.

```text
Mathematical target     Exact positive cube-root tube-volume constant.
Novelty hypothesis      Identify this certificate set's content through
                        the two-thirds moment of its singular limiting law.
Falsifier               A persistent moving index-phase cutoff error.
Already killed by?      No: proved weight asymptotics and equidistribution
                        supply the inputs; dense jumps admit Darboux bounds.
Existing machinery      Exact weights, empirical law and metric tube formula.
Maximum Phase-0 scope   Moving-cutoff counting, integration and specialization.
Promotion criterion     Lean checks the limit for the actual certificate set.
Stop criterion          A new unproved analytic or arithmetic premise is needed.
PROMOTE
```

**23 September: the whole geometric limiting measure.** The cube-root-rescaled
Lebesgue measures of the actual metric tubes converge weakly to
`dnu(y)=3*2^(1/3)*kappa^(2/3)*y^(2/3) dmu(y)`. Consequently a uniform
point in the shrinking tube has limiting probability law
`y^(2/3) dmu(y) / integral y^(2/3) dmu(y)`. This identifies every bounded
continuous spatial average, in addition to the total content. The local
gap-counting theorem permits zero retained weights; at each spatial threshold
the marked truncated-gap sum differs from the true tube-tail volume by at
most `4*epsilon`. No new arithmetic premise is used. The result is weak
convergence, not convergence on arbitrary measurable sets: the null set `K`
has zero tube probability at every radius and full limiting probability.
The public proof is
[BeattyCertificateLocalContent.lean](../../formal/Problems/Juggler/BeattyCertificateLocalContent.lean),
with original-count consumers in
[InterfaceCheckBeattyLocalContent.lean](../../formal/InterfaceCheckBeattyLocalContent.lean).
See Section 18 of the working note for the formulas and proof structure.

```text
Mathematical target     The local tube-volume limit and its probability normalization.
Novelty hypothesis      The geometric limit is the y^(2/3)-weighted certificate law.
Falsifier               Localized gap counts or boundary terms contradict that limit.
Already killed by?      No matching obstruction; gap locations and weights are explicit.
Existing machinery      Moving-cutoff counts, exact tube volumes, singular law.
Maximum Phase-0 scope   Localized counts, tube limits, weak convergence.
Promotion criterion     Lean checks the result for the actual certificate cluster set.
Stop criterion          A new unproved arithmetic premise is required.
PROMOTE
```

**23 September: the Hausdorff boundary.** Finite two-thirds Hausdorff measure
and `dim_H K<=2/3` are now proved for the actual cluster set from its tube
bound. The matching direction has an explicit arithmetic interface:
if every `(a,b)` inside `[0,1]` contains `delta_(n+1)` with
`(n+1)*(b-a)^tau<=H`, then the certificate CDF is Hölder with exponent
`2/(3*tau)`, `H^(2/(3*tau))(K)>0`, and `dim_H K>=2/(3*tau)`.
At `tau=1`, the conditional result is positive finite two-thirds Hausdorff
measure and dimension exactly `2/3`. The hitting premise is not supplied
for `alpha=log_2 3`. Qualitative equidistribution and the local Minkowski
measure do not remove it. The original-count consumer exposes the phase
as `frac((n+1)/beta)`. See Section 19 of the working note and
[BeattyPhaseHolder.lean](../../formal/Problems/Juggler/BeattyPhaseHolder.lean).

```text
Mathematical target     Hausdorff bounds for the actual certificate cluster set.
Novelty hypothesis      Isolate the exact phase-coverage input for equality.
Falsifier               Tube geometry or gap placement fails to support the bounds.
Already killed by?      No matching obstruction; Minkowski content alone
                        does not provide a Hausdorff lower bound.
Existing machinery      Tube bounds, positive gap decay, inverse CDF and plateaus.
Maximum Phase-0 scope   Upper bound, quantitative CDF regularity, conditional lower bound.
Promotion criterion     Lean checks the claims with the arithmetic premise explicit.
Stop criterion          The conditional premise is silently assumed at log_2 3.
PROMOTE
```

**23 September: Diophantine bounds without exponent loss.** A uniform
bound `|q*xi-p|>=c*q^(-tau)` gives phase hitting with constant
`H=4^tau/c+1` and the same exponent `tau`. Dirichlet approximation forces
a large reduced denominator; its rational grid supplies a strictly positive
orbit index inside every open interval. Specializing to `xi=1/beta` gives
positive Hausdorff measure at `2/(3*tau)` and the same dimension lower bound.
Bounds for every `tau>1`, with constants allowed to depend on `tau`, already
give dimension exactly `2/3`. A bound at `tau=1` also gives positive finite
critical measure. Both are conditional for the logarithmic slope: no
Diophantine constant is supplied. See Section 20 and
[BeattyDiophantineGeometry.lean](../../formal/Problems/Juggler/BeattyDiophantineGeometry.lean).

```text
Mathematical target     Convert Diophantine lower bounds into phase hitting
                        and certificate Hausdorff lower bounds.
Novelty hypothesis      Replace the geometric premise by a standard,
                        explicit arithmetic inequality for the actual slope.
Falsifier               Rational-grid approximation loses the claimed exponent.
Already killed by?      The Denjoy–Koksma obstruction concerns a different
                        counting bound and termination claim.
Existing machinery      Dirichlet approximation, coprime rational grids,
                        gap decay and the proved Holder/Hausdorff transfer.
Maximum Phase-0 scope   Rational-grid covering, polynomial hitting,
                        and the resulting conditional geometry.
Promotion criterion     Lean checks the exponent and original-count interfaces.
Stop criterion          A Diophantine bound for log_2 3 must be assumed silently.
PROMOTE
```

The [all-paper Arb MCP audit](../research/arb_paper_audit.md) computes the
first 256 exact atoms and bounds the entire remaining mass by subtracting
their mass from the proved total `1/(alpha-1)`. Positivity and
`0 <= F^(2/3)-F_256^(2/3) <= (2/3)*tail` give the full moment interval
`[1.40531077, 1.46506386]` and the Minkowski content interval
`[2.95207917, 3.07760004]`, rounded outward. These finite enclosures are
**COMPUTATIONALLY VERIFIED** consequences of the established identities.
They give no effective convergence rate or new Hausdorff lower bound.

**23 September: the exact BGL Gamma normalization is now checked.**
For `D_r=Gamma(r/beta)/(r! Gamma(r(1-beta)/beta+1))`, Lean proves
`c_r/D_r-(1-beta)^(delta_r) F(delta_r) -> 0` at the logarithmic slope.
The explicit amplitude `B(t)=(1-beta)^{fract(t)} F(fract(t))` is
unit-periodic, and the original Gamma-normalized integer counts approach
`B(r/beta)`. A direct binomial/Gamma identity and log-convex interpolation
control arbitrary moving phases in `[0,1]`; no real-variable Stirling
asymptotic or phase-convergence premise is left open. The eight consumer
dependency records permit only `propext`, `Classical.choice` and `Quot.sound`.
See [BeattyFirstPassageAmplitude.lean](../../formal/Problems/Juggler/BeattyFirstPassageAmplitude.lean),
[BeattyGammaNormalization.lean](../../formal/Problems/Juggler/BeattyGammaNormalization.lean)
and [InterfaceCheckBeattyAmplitude.lean](../../formal/InterfaceCheckBeattyAmplitude.lean).
This formalizes the explicit specialization of BGL's proposed amplitude;
the path dictionary is still written mathematics and no priority is asserted.

```text
Mathematical target     Check BGL's exact Gamma-normalized first-passage amplitude.
Novelty hypothesis      A checked identification for these counts, not a new Gamma inequality.
Falsifier               An index shift or normalization factor prevents the stated limit.
Already killed by?      No matching obstruction; this is a first-passage comparison.
Existing machinery      The phase theorem, exact binomial identities, Gamma log-convexity.
Maximum Phase-0 scope   Uniform Gamma interpolation and the concrete normalization bridge.
Promotion criterion     Compiled original-count theorem and standard-dependency audit.
Stop criterion          Record any remaining analytic premise explicitly.
PROMOTE
```

**23 September: the BGL normalization has an absolutely continuous law.**
The exact Gamma-normalized integers converge in distribution to
`eta=Law(q^U F(U))`. Lean proves `eta << Lebesgue`, continuity of its CDF,
every threshold frequency, and every bounded continuous observable limit.
Thus `eta(K)=0` and `eta` is mutually singular with the original law
`mu=Law(F(U))`, which has `mu(K)=1`. The key regularity fact is
`F'=0` almost everywhere, obtained from its null monotone range; multiplying
by `q^t` gives a nonzero derivative almost everywhere. A general checked
null-preimage criterion supplies absolute continuity without global
injectivity. The thirteen consumer dependency records use only standard
Lean axioms. See
[BeattyPassageDistribution.lean](../../formal/Problems/Juggler/BeattyPassageDistribution.lean)
and [its consumer](../../formal/InterfaceCheckBeattyPassageLaw.lean).

**23 September: the entire occupation density and moments are now checked.**
Section 21 identifies the entire density as
`h(y)=sum_r 1_(L_r,U_r)(y)/(-y log q)`, with
`L_r=q^delta_r F(delta_r)` and `U_r=q^delta_r(F(delta_r)+w_r)`.
The intervals may overlap. A finite-jump occupation identity has an
endpoint term, vanishing only in the limit because `qF(1)=1`.
Uniform truncation and summable domination justify the dense-jump limit.
This gives the logarithmic normalization and every real-power moment.
These explicit identities are now **EXACT — LEAN VERIFIED**, including
all real exponents different from zero and negative-power integrability.
The generic finite calculus, primitive bounds, dominated limit and measure
identification are in the four `Beatty*Occupation*` modules. The concrete
interfaces are
[BeattyPassageDensity.lean](../../formal/Problems/Juggler/BeattyPassageDensity.lean)
and [BeattyPassageMoments.lean](../../formal/Problems/Juggler/BeattyPassageMoments.lean).
The [independent consumer](../../formal/InterfaceCheckBeattyDensity.lean)
checks twenty dependency records with only standard Lean axioms, including
the original integer counts converging to the explicit density law.
The density is extended nonnegative, with finite values almost everywhere;
overlapping intervals are counted with multiplicity.
The finite-piece calculus has classical level-crossing precedents; no
priority is inferred from the BGL comparison.

```text
Mathematical target     Identify the limiting law of the Gamma-normalized counts.
Novelty hypothesis      An explicit law for this amplitude; the calculus is classical.
Falsifier               A missing continuous term or endpoint flux in the density.
Already killed by?      No matching obstruction; the harvest-counting obstruction is unrelated.
Existing machinery      Exact jump profile, total mass, phase equidistribution, Gamma limit.
Maximum Phase-0 scope   Prove the occupation identity and formalize its consequences.
Promotion criterion     A checked original-count limit with an explicit proof boundary.
Stop criterion          An analytic premise remains unproved or the density formula fails.
PROMOTE
```

**23 September: exact interval support and dense null density blowup.**
The Gamma-normalized counts have the single interval
`[inf_r L_r, sup_r U_r]` as their full cluster set and limiting-law support.
It is nondegenerate and lies in `[q,1/q]`; the CDF is continuous and strictly
increasing on it. The canonical density is lower semicontinuous and infinite
on a dense null G-delta in the support interior. Every finite threshold is
exceeded on a positive-measure subset of every open set meeting that
interior. Thus no almost-everywhere equal density version is locally
essentially bounded there. These are **EXACT — LEAN VERIFIED**, with
twenty-four consumer dependency records allowing only standard Lean axioms.
The original integer ratios and exact endpoint formulas are expanded in
[InterfaceCheckBeattySupport.lean](../../formal/InterfaceCheckBeattySupport.lean).
Section 22 of the working note gives the proof and module map. No finite
jump is asserted to supply either extremum; `L^p` integrability for `p>1`
is not decided by the unboundedness theorem.

```text
Mathematical target     Determine the Gamma-law support and whether it has gaps.
Novelty hypothesis      An exact specialization for these counts; the topology is classical.
Falsifier               A genuine gap inside the amplitude's value envelope.
Already killed by?      No matching obstruction; continuity of the dense-jump profile is not assumed.
Existing machinery      Explicit density, summable jumps, endpoint identity, Gamma limit.
Maximum Phase-0 scope   Support theorem and immediate distributional consequences.
Promotion criterion     Compiled concrete theorem with audited dependencies.
Stop criterion          An unproved regularity or arithmetic premise is needed.
PROMOTE
```

**24 September: quantitative regularity and the full blowup set.**
The concrete Gamma law satisfies `eta(A)<=C lambda(A)^(1/3)` for every
measurable finite-measure set, and its canonical density has superlevel
measure `O(T^(-3/2))`. It belongs to every `L^p`, `1<=p<3/2`.
The CDF is globally one-third Holder and fails every local Lipschitz bound
on open sets meeting the support interior. The whole infinite-density set
equals the previously constructed dense null G-delta and has zero
`s`-dimensional Hausdorff measure for every `s>2/3`, hence dimension at
most `2/3`. These are **EXACT — LEAN VERIFIED**, with fifteen consumer
dependency records allowing only standard Lean axioms. Section 23 of the
working note records the proofs and the distinction from law moments.
No endpoint integrability, optimal exponent or matching dimension is claimed.

```text
Mathematical target     Quantitative regularity and blowup-set upper dimension.
Novelty hypothesis      Concrete consequences; the general estimates are classical.
Falsifier               A mismatch between density intervals and proved decay bounds.
Already killed by?      No matching recorded obstruction; the direct estimates close.
Existing machinery      Density formula, positive envelope, three-halves truncated sums.
Maximum Phase-0 scope   These inequalities and their concrete Lean interfaces.
Promotion criterion     Unconditional statements for the actual limiting law, audited.
Stop criterion          Do not claim sharpness without overlap estimates.
PROMOTE
```

### Bounded overlap investigation (24 September)

**EXACT — LEAN VERIFIED (criterion only).** Write `I_r=(L_r,U_r)` for the
actual rescaled jump intervals, `M(y)=sum_r 1_(I_r)(y)`, and

\[
 \mathcal E=\sum_{r,s\ge1}|I_r\cap I_s|
 =\sum_{r,s\ge1}(\min(U_r,U_s)-\max(L_r,L_s))_+.
\]

Tonelli gives `integral M^2 = E`, including the case of infinite values.
Since `h(y)=M(y)/(a*y)` and all intervals lie in the positive compact
envelope `[q,1/q]`, the actual density belongs to `L^2` if and only if
`E<infinity`. [BeattyOverlapEnergy.lean](../../formal/Problems/Juggler/BeattyOverlapEnergy.lean)
proves the general multiplicity identity, the concrete equality, the
kernel factorization, and the equivalence for both the extended density
integral and its almost-everywhere real representative. The
[expanded consumer](../../formal/InterfaceCheckBeattyOverlap.lean) and
[executable audit](../../tests/research/juggler_sequence/test_beatty_overlap_interface.py)
check seven dependency records, allowing only `propext`, `Classical.choice`
and `Quot.sound`. This formal criterion does **not** prove its finiteness side.
The generic identities are classical; no novelty is claimed for Tonelli.

**COMPUTATIONALLY VERIFIED (finite scope).** The
[overlap audit](../../tools/check_beatty_overlap.py) uses exact survivor
counts through depth 6493 and Arb at 256 bits for 4096 atoms. For each
dyadic profile cutoff `M=16,...,4096`, it computes every dyadic chronological
head `N<=M`. Here `I_(r,M)` uses the finite profile `F_M` in both endpoints,
and `h_(N,M)(y)=(a*y)^(-1) sum_(r<=N) 1_(I_(r,M))(y)`.
This finite interval sum is not asserted to be a probability density or
the entire occupation law of the truncated amplitude; the finite-cutoff
endpoint term is not included. Rational outward bounds and actual-run
provenance are in the [report](../../data/research/juggler/winkler_phase_collapse/overlap_energy.json)
and [manifest](../../data/research/juggler/winkler_phase_collapse/overlap_energy.research.json).

| Profile and head cutoff `M=N` | `integral h_(N,N)^2` (rounded display) | Last-block overlap energy / sum of its interval lengths (rounded display) |
|---|---:|---:|
| 128 | 3.209585 | 1.015752 |
| 512 | 3.357811 | 1.022268 |
| 1024 | 3.397190 | 1.026024 |
| 2048 | 3.409648 | 1.016919 |
| 4096 | 3.435221 | 1.014959 |

The last block contains indices `N/2<r<=N`; its finite-model maximum
multiplicity is exactly two at all nine diagonal cutoffs in this run.
This statement is a finite check, **not** an all-orders overlap bound.

The audit also encloses true finite heads using
`0<=F-F_M<=T_M=1/q-F_M(1)`. At `M=4096`,
`0.02244448<T_M<0.02244449`, and the true ordered overlap sum through
`r,s<=4096` lies in `[2.75903,12.54709]` (outward decimal rounding).
That interval is for the multiplicity energy of the true finite head,
not the density-square integral or the infinite sum. Position uncertainty
does not enlarge a jump's known width: the code bounds the intersection by
`max(0,min(width_i,width_j,U_i-L_j,U_j-L_i))`, keeping the diagonal widths
exactly enclosed. All proposed phase/event orders are checked by Arb;
an unresolved comparison fails the run. Independent interval examples,
position-uncertainty checks and a two-precision small run pass in
[the numerical tests](../../tests/tools/test_beatty_overlap.py).

**EXACT — HUMAN PROOF (sufficient route only).** Put
`D_k=integral (sum_(2^k<r<=2^(k+1)) 1_(I_r))^2`. Then

\[
 \sum_{k\ge0}\sqrt{D_k}<\infty \quad\Longrightarrow\quad h\in L^2.
\]

For every finite number of blocks, the `L^2` triangle inequality bounds
the norm of their sum by `sqrt(|I_1|)+sum sqrt(D_k)`. Monotone convergence
of its square then bounds the full energy. In particular,
`D_k<=C*2^(-epsilon*k)` for some positive `C,epsilon` would suffice.
The diagonal length sum has order `2^(-k/2)` by the proved weight bounds;
the unresolved input is control of the off-diagonal overlaps. No such
uniform estimate is established by the finite block table.

There is another sufficient route: a uniform bound on the diagonal
finite-profile energies `integral h_(M,M)^2` would imply `h in L^2`.
For each fixed `r`, uniform convergence `F_M -> F` gives convergence of
both endpoints. Outside the countable set of true endpoints, each fixed
indicator converges. Finite heads therefore give
`h<=liminf_M h_(M,M)` almost everywhere, and Fatou proves the implication.
The displayed finite sequence does not supply the required uniform bound.
These two sufficient-route arguments are written deductions, separate
from the compiled exact overlap equivalence.

### Arithmetic improvement across the endpoint (written proof)

**EXACT — HUMAN PROOF; not yet an end-to-end Lean theorem.** For the
concrete logarithmic slope, the canonical Gamma density satisfies

\[
 h\in L^p(\mathbb R)\qquad(1\le p<62/41).
\]

In particular `h in L^(3/2)`. More precisely, the law satisfies
`eta(A)<=C lambda(A)^(21/62)` for every finite-measure measurable set,
the density belongs to weak `L^(62/41)`, and the CDF is globally
`21/62`-Holder. Constants are finite and uniform, but no numerical value
is asserted. These exponents are conservative, not claimed optimal.
The proof uses the classical Wu-Wang logarithmic-form theorem and the
Erdos-Turan discrepancy inequality as external mathematics. Neither these
inputs nor their analytic assembly below are added as axioms in Lean.

**1. A weak but sufficient arithmetic input.** Wu and Wang,
*On the irrationality measure of log 3*, J. Number Theory 142 (2014),
264--273, [Theorem 1](https://doi.org/10.1016/j.jnt.2014.03.007), give a
linear-form exponent `4.1163051+epsilon` for `1,log 2,log 3`.
Use `epsilon=1/2` and coefficients `(0,-j,n)`, where `j` is a nearest
integer to `n*alpha`. Then `max(|j|,n)<=2n`, and division by `log 2`,
weakening the exponent to five, and absorbing finitely many small `n`
give a constant `c>0` with

\[
 \|n\alpha\|_{\mathbb R/\mathbb Z}\ge c n^{-5}\quad(n\ge1).
\]

Irrationality ensures the finitely many absorbed distances are positive.
This uses the linear-form theorem itself, not merely the irrationality
measure of the different number `log 3`. The floor-finance obstruction in
[Diophantine walls](../negative_knowledge/diophantine-walls.md) concerns
cycle exclusion and does not apply to this rotation-discrepancy estimate.

**2. Uniform discrepancy on every consecutive phase block.** The geometric
sum for frequency `h` has absolute value at most `1/(2||h alpha||)`,
uniformly in the initial index. The
[Erdos-Turan inequality](https://www.renyi.hu/~p_erdos/1948-02.pdf)
(1948, Theorem III) therefore gives normalized interval discrepancy

\[
 \mathscr D_N\ll K^{-1}+\frac1N\sum_{h=1}^K h^4
 \ll K^{-1}+K^5/N\ll N^{-1/6},
 \qquad K=\lfloor N^{1/6}\rfloor.
\]

The implicit constant is independent of the block's initial index and
the phase interval. Changing endpoint conventions costs at most `2/N`,
since the rotation phases are distinct; this is absorbed by the estimate.

**3. Transfer the discrepancy to amplitude values.** Let `B(t)=q^t F(t)`,
`B_M(t)=q^t F_M(t)`, and `H` be the CDF of `B(U)`. The proved weight
bound yields
`0<=B-B_M<=T_M<<M^(-1/2)` uniformly on `[0,1]`.
On each of the `M+1` phase cells, `B_M` is a positive constant times
`q^t` and strictly decreases. A sublevel set of `B_M` is therefore a
union of at most `M+1` intervals, with at most `M+2` boundary points to
handle separately. Rotation discrepancy controls its sampled frequency
by its phase measure with error `O(M N^(-1/6))`.

If `H_N` denotes the empirical CDF of `B(delta_r)` on any consecutive
block of `N` indices, the inclusions
`{B_M<=x-T_M} subset {B<=x} subset {B_M<=x}` and the reverse inclusions
for their phase measures give

\[
 H(x-T_M)-O(MN^{-1/6})\le H_N(x)
 \le H(x+T_M)+O(MN^{-1/6}).
\]

The already formalized one-third Holder bound for `H` implies
`sup_x |H_N(x)-H(x)|<<M^(-1/6)+M N^(-1/6)`.
Choose `M=max(1,floor(N^(1/7)))`; thus, uniformly over all such blocks,

\[
 \sup_x|H_N(x)-H(x)|\ll N^{-1/42}.                 \tag{O1}
\]

This is a rate for the exact amplitude samples `B(delta_r)`, not for
the integer ratios `c_r/D_r`; transferring a rate to those ratios still
requires a quantitative first-passage asymptotic. Taking left limits
of the CDF bounds controls closed value intervals as well, because `H`
is continuous; no distinctness of the amplitude values is assumed.

**4. A uniform overlap bound at each dyadic scale.** For `n=2^k`, put
`A_k(y)=sum_(n<r<=2n) 1_(I_r)(y)`.
Each interval in this block has length at most `C n^(-3/2)` and left
endpoint `B(delta_r)`. Consequently an interval covering `y` has its
left endpoint in `[y-C n^(-3/2),y]`. By (O1) and the established
concentration estimate for `eta`,

\[
 \|A_k\|_\infty\ll n\bigl((n^{-3/2})^{1/3}+n^{-1/42}\bigr)
 \ll n^{41/42},\qquad
 \|A_k\|_1=\sum_{n<r\le2n}|I_r|\ll n^{-1/2}.       \tag{O2}
\]

These are bounds for the **true** infinite-profile intervals, not their
finite numerical approximations. In particular their block overlap
energies satisfy `D_k=integral A_k^2<<2^(10k/21)`. This supplies a power
saving over the length-only bound `O(2^(k/2))`, although it does not
give the decay sufficient for `L^2`.

**5. Integrability, concentration and CDF consequences.** For `1<=p<2`,
`integral A_k^p <= ||A_k||_infinity^(p-1) ||A_k||_1`, so (O2) gives

\[
 \|A_k\|_p\ll_p
 2^{k(41p-62)/(42p)}.
\]

The block norms are summable precisely in the asserted range `p<62/41`.
The triangle inequality for finite sums and monotone convergence prove
`M in L^p`, hence `h in L^p` by the positive compact envelope. The
single interval `I_1` contributes a finite norm. At `p=3/2` the displayed
exponent is `-1/126`, so the endpoint is included without a logarithmic
borderline argument.

For the sharper set estimate, let `v=lambda(A)` with `0<v<=1` and split
the dyadic blocks at `2^K` comparable to `v^(-21/31)`. Equations (O2)
give

\[
 \int_A M\ll v+v\sum_{k\le K}2^{41k/42}
                   +\sum_{k>K}2^{-k/2}
 \ll v^{21/62}.
\]

The zero-measure case follows from absolute continuity; for `v>=1`,
`eta(A)<=1` suffices. The bounded kernel transfers this bound to `eta`.
Applying it to a density superlevel of measure `m` gives
`T*m<=C*m^(21/62)`, hence `m<<T^(-62/41)`. Applying it to `(x,y]`
gives global `21/62`-Holder continuity of `H`. No membership at the new
endpoint `p=62/41`, no sharp exponent, and no `L^2` conclusion follows.

**Proof boundary.** The overlap identity and `L^2` equivalence above are
Lean-checked. Steps 1--5 here are a complete written argument using two
named classical inputs; their additional arithmetic and discrepancy
estimates have **not** been formalized. The numerical audit is independent
of this argument and is not used to prove any infinite estimate. The
working paper retains its previously audited formal range until this
written strengthening is incorporated with its distinct evidence label.

```text
Mathematical target     Cross the Gamma-density three-halves endpoint using overlap control.
Novelty hypothesis      Actual interval placement improves the length-only p<3/2 range.
Falsifier               Failure of the uniform discrepancy or finite-sublevel-complexity bound.
Already killed by?      No; the recorded Diophantine wall concerns cycle finance, not phase discrepancy.
Existing machinery      Density, decay, concentration, exact counts, Arb, Wu-Wang and Erdos-Turan.
Maximum Phase-0 scope   Cutoffs through 4096 and a written uniform block estimate; no larger campaign.
Promotion criterion     A uniform analytic power saving sufficient for the actual density endpoint.
Stop criterion          No optimality, L2 assertion or full Lean label without its missing proof.
PROMOTE
```

**PROMOTE the written arithmetic improvement and the formal overlap
criterion.** The `L^2` question remains unresolved: both the finite evidence
and the analytic block bound stop short of proving it. The original
`L^(3/2)` endpoint is now supplied by the written argument, with its
external inputs explicit. Full Lean formalization of that improvement is
a separate remaining task. No larger numerical campaign or new research
branch is opened automatically.

## Open questions

The qualitative logarithmic-slope phase theorem and normalization are complete
in Lean, as are the complete accumulation set and its singular continuous
empirical limiting law. Its tube-volume order and Minkowski dimension `2/3`
and its exact positive Minkowski content are now checked too, together with
the whole local content measure and the normalized geometric limiting law.
The Gamma-normalized empirical law and its absolute continuity are also
checked, together with its explicit occupation density, exact logarithmic
normalization and all real-power moment identities. Its exact interval
support, full cluster set, strict CDF, dense null density blowup and local
essential unboundedness are now checked too. Remaining
mathematical extensions are exact Hausdorff dimension and critical-measure
positivity, supplying a Diophantine bound for the quantitative hitting theorem,
a quantitative phase remainder, evaluation of the support endpoints,
full Lean formalization of the written `p<62/41` arithmetic improvement,
`L^p` density integrability at `p=62/41` and above, optimal CDF Holder regularity,
and a matching Hausdorff lower bound for the infinite-density set,
effective numerical constants, and generalization from the concrete
logarithmic slope to arbitrary irrational `1<alpha<2`. Literature comparison
is separate from proof checking; existing paper claims and releases retain
their earlier evidence labels.

## Decision

`PROMOTE` -- the actual normalized certificate counts have the explicit positive
jump-series asymptotic, with its full normalization and strict atom convention
proved. The continuation identifies the full null perfect accumulation set,
its exact gaps, the singular continuous empirical law with exact threshold
frequencies and plateau levels, and the cube-root neighbourhood-volume law
with dimension `2/3` and exact content given by the two-thirds law moment.
The whole geometric limiting measure is the explicitly scaled
`y^(2/3)` reweighting of the empirical law, with its probability normalization.
The Hausdorff upper bound and finite critical measure are unconditional;
matching lower bounds are proved under an explicit phase-hitting estimate,
now derived from a standard uniform Diophantine lower bound without exponent
loss. Bounds for every exponent above one suffice for dimension equality;
the stronger exponent-one bound supplies positive critical measure.
The Gamma normalization gives an absolutely continuous limiting law,
mutually singular with the original law. Its explicit density series,
logarithmic normalization and every real-power moment are formalized,
with a complete finite-cutoff proof and no remaining occupation premise.
Its exact support and full count cluster set are a nondegenerate interval;
the density is lower semicontinuous with dense null blowup and unavoidable
local essential unboundedness throughout the support interior. Quantitative
concentration, weak three-halves tails, subcritical `L^p` integrability,
Holder/non-Lipschitz CDF regularity and the full blowup-set Hausdorff upper
bound are checked without further arithmetic assumptions.
The subsequent written arithmetic argument gives density integrability for
`1<=p<62/41`, weak `L^(62/41)` and `21/62`-Holder CDF regularity using
Wu-Wang and Erdos-Turan. This strengthening is **EXACT — HUMAN PROOF**;
its arithmetic inputs and discrepancy assembly are not Lean-checked.
No new branch, publication, priority claim or
trajectory-termination claim is opened.

## Publication assessment

Status: `PAPER_CANDIDATE`. The completed profile, accumulation-set and
empirical-law theorems are presented together in the standalone working note
*A Jump Profile and Singular Geometry for Beatty First-Passage Counts*.
It supports Paper B, Section 6. The comparison with Bauer, Godrèche and Luck
(1999) identifies their crossing counts and survivor-amplitude series exactly;
the profile realizes their proposed irrational first-passage amplitude as
`q^t F(t)` at the logarithmic slope. The exposition focuses on the cumulative
profile, complete cluster set, singular law and explicit local geometric
measure. The global gap-to-content criterion is attributed to
Lapidus–Pomerance (1993). The exact Gamma-normalized amplitude is now
Lean-checked, as are its absolutely continuous empirical law, explicit
occupation density, real-power moments, interval support and density topology.
The resulting
contrast between two measure types belongs with the geometric results;
the path dictionary and spectral corollary remain written deductions.
Whether to publish separately or
incorporate this into Paper B remains an editorial decision; literature
priority requires a wider search. The working note is not a new deposit.
