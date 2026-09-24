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

### Arbitrary-boundary counting foundation (24 September)

The sustained generalization programme begins with the actual integer counts,
before extending the analytic estimates. This is a formal generalization of
classical counting machinery, not a claim of a new counting identity.

```text
Mathematical target     Exact survivor counting for every irrational boundary 0 < beta < 1.
Novelty hypothesis      Reusable formal foundation for the general-slope theorem;
                        the underlying counting identity is classical.
Falsifier               An endpoint or first-crossing convention breaks the identity.
Already killed by?      No matching obstruction; this is a counting generalization.
Existing machinery      Binary-word enumeration and the formal-series support proof.
Maximum Phase-0 scope   General counts, crossing decomposition, counting recurrence,
                        and recovery of the existing logarithmic counts.
Promotion criterion     Lean checks the general statement and its specialization.
Stop criterion          Keep any analytic or geometric assumptions explicit.
```

For a real boundary `beta`, let `S_beta(n)` count binary words of length `n`
whose first `k` letters contain at least `beta*k` odd letters, for every
`0<=k<=n`. Let `P_beta(n)` count words whose first strict crossing below that
boundary occurs at their endpoint. The empty word survives. Put

\[
 A_\beta(n)=\sum_{\substack{0\le k\le n\\n\beta<k}}\binom nk.
\]

The new checked statements are:

1. For **every real** `beta`,
   `S_beta(n+1)+P_beta(n+1)=2*S_beta(n)`, with `S_beta(0)=1` and
   `P_beta(0)=0`.
2. For **every irrational real** `beta` and every natural `n`,
   \[
   nS_\beta(n)=\sum_{j=0}^{n-1}A_\beta(n-j)S_\beta(j).
   \]
   At every nonempty prefix, weak survival is equivalent to strict survival.
   No Diophantine estimate, generating-identity premise or bound on `beta`
   occurs in this recurrence.
3. For `0<beta<=1`, a first-passage word with `r` odd letters ends in an even
   letter and has length `floor(r/beta)+1`. This includes rational boundaries
   with the weak-survival/strict-crossing convention. It recovers the BGL
   crossing-edge location directly from the word definition.
4. At `beta=log(2)/log(3)`, both finite word sets agree exactly with the
   existing survivor and minimal-certificate sets. The old counting and
   exponential-identity theorems now use the general recurrence through this
   equality. Their public statements are unchanged.

The sources are
[`BeattySlopeWords.lean`](../../formal/Problems/Juggler/BeattySlopeWords.lean),
[`BeattySlopeCounting.lean`](../../formal/Problems/Juggler/BeattySlopeCounting.lean)
and
[`BeattySlopeSpecialization.lean`](../../formal/Problems/Juggler/BeattySlopeSpecialization.lean).
The original
[`BeattyCounting.lean`](../../formal/Problems/Juggler/BeattyCounting.lean)
is a specialization, rather than a second copy of the proof.
[`InterfaceCheckBeattySlope.lean`](../../formal/InterfaceCheckBeattySlope.lean)
expands the binomial sum, the prefix convention, the reciprocal parameter
`beta=1/alpha`, the crossing edge and the finite-set equalities.
Its thirty consumer records and the seventy-seven public-theorem records in
[`AxiomCheckBeattySlope.lean`](../../formal/AxiomCheckBeattySlope.lean)
allow only the standard Lean dependencies.

The current coverage map is deliberately asymmetric:

| Statement | Parameter range | Formal status |
|---|---|---|
| One-step survivor/first-passage partition | Every real `beta` | Checked |
| Positive-partial-sum integer recurrence | Every irrational real `beta` | Checked |
| Weighted recurrence and exact normalized renewal exponential | Every irrational real `beta`, every real letter weight and base | Checked |
| Crossing edge `floor(r/beta)+1` | Every real `0<beta<=1` | Checked |
| Exact removal of the crossing weight | Every real `0<beta<=1`, nonzero letter weight | Checked |
| Subcritical bias with terminal ratio `1/2` | Every real `0<beta<1` | Checked algebraic identity |
| Tilted finite tail between its first term and twice that term | Every real `0<beta<1`, every positive depth | Checked; no irrationality or Stirling premise |
| Weighted survivor phase transfer | Every irrational real `beta`, nonnegative weight and base | Checked implication; bounded terminal phase asymptotic is an explicit premise |
| Explicit tilted terminal phase | Every real `0<beta<1` | Checked without an asymptotic premise |
| Explicit tilted survivor phase | Every irrational `0<beta<1`, equivalently every irrational `alpha>1` | Checked without an asymptotic premise; summable, positive, bounded and periodic profile |
| Critical survival vanishes and first-passage probabilities sum to one | Every irrational `0<beta<1` | Checked; finite mass and height bounds also cover rational boundaries |
| Beatty jump weights sum to `1/(alpha-1)` | Every irrational `alpha>1` | Checked for the actual integer counts, with the auxiliary zero atom removed |
| Exact original logarithmic word sets | `beta=log(2)/log(3)` | Checked |
| Original fair-weight survivor phase formula | Logarithmic boundary | Checked; the full-interval theorem uses the chosen bias instead |
| Explicit jump profile and original integer first-passage asymptotic | Every irrational `alpha>1` | Checked with actual counts, strict atoms and additive `o(1)` error |
| Positive actual crossing counts | Every real `0<beta<=1` | Checked with an explicit odd-then-even word witness |
| Complete null perfect cluster set and singular empirical law | Every irrational `alpha>1` | Checked with exact gaps, envelope extrema and CDF plateaus |
| Three-halves gaps, exact Minkowski content and local geometric measure | Every irrational `alpha>1` | Checked for actual counts and metric tubes |
| Gamma-law and density regularity | Every irrational `alpha>1` | Checked for actual counts and the exact Gamma quotient |
| Matching Hausdorff lower bounds | Explicit Diophantine hypotheses | Conditional concrete results; arithmetic inputs and a family theorem still need assembly |

The weighted version of `BeattyEndpointAsymptotic` is now proved below.
The original fair-walk route requires
`1/2<beta<1`; the tilt below removes that restriction at the algebraic level.
The lower cutoff for the Stirling estimates must still depend on `beta`.
A family theorem should first quantify **for each fixed irrational slope**,
with slope-dependent constants; this is weaker than uniformity as the slope
approaches the endpoints. Rational boundary ties need their own analytic
statement.

The weighted continuation supplies the exact foundation beyond the fair-walk interval.
BGL's [Section 2.1, equation (2.15)](https://arxiv.org/html/cond-mat/9905252)
allows any Bernoulli bias `0<p<beta`. For any `0<beta<1`, the choice
`p=beta/(2-beta)` puts the walk in that regime and makes the limiting
binomial-tail ratio `((1-beta)*p)/(beta*(1-p))` exactly `1/2`.
Equivalently, evaluate the odd-letter counting polynomial at
`z=p/(1-p)=beta/(2*(1-beta))`, instead of at `1`.
At a crossing edge with exactly `r` odd letters, this weighting multiplies
the path count by `z^r`, so it can be removed exactly. The weighted recurrence,
that removal, the normalization, and the conditional phase transfer are now
checked in Lean, as detailed below. This remains a classical change of bias,
not a checked extension of the full profile theorem to every irrational
`alpha>1`.

**PROMOTE** this formal foundation within the existing phase programme.
It does not promote the general analytic or geometric conclusions, and it
does not establish a new number-theoretic bound or any trajectory result.

### Weighted continuation across the full boundary interval (24 September)

```text
Mathematical target     Weighted survivor and first-passage identities at every
                        irrational boundary, with a useful bias for 0 < beta < 1.
Novelty hypothesis      A formal route to the full slope family; the weighted
                        counting identity itself is classical.
Falsifier               Weighting changes the crossing convention or cannot be
                        removed exactly at a crossing edge.
Already killed by?      No matching obstruction; BGL supports this change of bias.
Existing machinery      The odd-letter polynomial proof and generic renewal theorem.
Maximum Phase-0 scope   Weighted recurrence, exact removal of crossing weights,
                        and the normalized renewal identity.
Promotion criterion     Lean checks actual weighted word sums and their specialization.
Stop criterion          Keep the general Stirling and phase-transfer inputs explicit.
```

Give each odd letter weight `z` and each even letter weight one. Write
`S_beta,z(n)` and `P_beta,z(n)` for the sums of these weights over the actual
survivor and first-passage word sets, and put

\[
 A_{\beta,z}(n)=\sum_{\substack{0\le k\le n\\n\beta<k}}\binom nk z^k.
\]

The single polynomial proof now gives

\[
 S_{\beta,z}(n+1)+P_{\beta,z}(n+1)=(1+z)S_{\beta,z}(n),
 \qquad
 nS_{\beta,z}(n)=\sum_{j=0}^{n-1}A_{\beta,z}(n-j)S_{\beta,z}(j).
\]

The first identity holds for every real `beta,z`; the second requires only
irrationality of `beta`. Taking `z=1` recovers the original integer theorem.
For `0<beta<=1`, the crossing-depth map `r -> floor(r/beta)+1` is strictly
increasing. Every first-passage word at that depth has exactly `r` odd letters,
so

\[
 P_{\beta,z}(\lfloor r/\beta\rfloor+1)
   =z^r P_\beta(\lfloor r/\beta\rfloor+1).
\]

This finite identity includes rational boundaries and permits exact division
when `z` is nonzero. It is checked against the word definitions, rather than
assumed from an interpretation of a generating function.

The new
[`BeattySlopeRenewal.lean`](../../formal/Problems/Juggler/BeattySlopeRenewal.lean)
then identifies
`u(n)=S_beta,z(n)/v^n` with the formal renewal exponential of
`a(n)=A_beta,z(n)/v^n`. It proves the corresponding three-halves bound and phase
transfer **conditionally on the terminal estimates**. In particular, for
nonnegative `z,v`, a bounded function `Phi` satisfying

\[
 \sqrt n\,a(n)-\Phi(n\beta)\longrightarrow0
\]

implies

\[
 n^{3/2}u(n)-\sum_{j\ge0}u(j)\Phi((n-j)\beta)\longrightarrow0.
\]

The expanded consumer states both actual finite sums and the terminal-limit
premise. The exact renewal identity itself requires no terminal estimate.
The full-range choice `z=beta/(2*(1-beta))`, its Bernoulli bias
`p=beta/(2-beta)`, the inequalities `0<p<beta`, and
`z*(1-beta)/beta=1/2` are also Lean-checked.

The precise endpoint target, now proved in the continuation below, is obtained by
putting `q=1-beta`,

\[
 v=2^{-\beta}/q,
 \qquad \Phi_\beta(t)=\frac{2^{\{t\}}}{\sqrt{2\pi\beta q}}.
\]

The limit is `sqrt(n)*A_beta,z(n)/v^n-Phi_beta(n*beta) -> 0`.
The strict cutoff `floor(n*beta)+1` contributes
`2^(-(1-frac(n*beta)))`; summing the limiting geometric tail supplies the
factor two. This calculation specifies the Stirling proof and its jump
convention; the continuation below now supplies the full Lean proof.
Even after this estimate, the first-passage
transfer, critical total mass, jump-profile identification and geometric
assembly must be generalized before claiming the full family theorem.

**PROMOTE** the checked weighted foundation within the existing programme.
The new scope is an unconditional finite/renewal identity plus an explicitly
conditional analytic transfer, not a novelty claim for the classical identity
or a completed theorem for arbitrary irrational slopes.

The finite-tail continuation asks a narrower analytic preparation question:

```text
Mathematical target     Bound the tilted terminal tail by twice its first term.
Novelty hypothesis      A reusable formal estimate; the comparison is classical.
Falsifier               A term beyond the strict cutoff has ratio above 1/2.
Already killed by?      No matching obstruction; the existing proof uses 3/5
                        at the fixed logarithmic slope.
Existing machinery      Binomial recurrence and the checked tilt.
Maximum Phase-0 scope   Cutoff, adjacent-term bound, geometric sum bound.
Promotion criterion     Lean checks the bounds for every 0 < beta < 1.
Stop criterion          Leave the Stirling asymptotic as the next input.
```

This is now **EXACT — LEAN VERIFIED** in
[`BeattySlopeBinomial.lean`](../../formal/Problems/Juggler/BeattySlopeBinomial.lean).
Put `k=floor(n*beta)+1` and `z=beta/(2*(1-beta))`. For every real
`0<beta<1`, every natural `n,j`,

\[
 \binom n{k+j}z^{k+j}\le \binom nk z^k\,2^{-j}.
\]

Consequently, for every positive `n`,

\[
 \binom nk z^k\le A_{\beta,z}(n)\le2\binom nk z^k.
\]

The convention that binomial coefficients vanish outside their support is
included in the proof. The constant two is uniform over all these boundaries
and depths; it does not make the subsequent Stirling remainder uniform near
`beta=0` or `beta=1`. The expanded consumer checks the full endpoint sum,
strict cutoff and tilt. **PROMOTE** this finite geometric bound within the
existing programme. The next continuation discharges the endpoint phase limit.

### Unconditional tilted survivor phase for every irrational slope (24 September)

```text
Mathematical target     Prove the tilted endpoint phase limit for every 0 < beta < 1,
                        then the survivor phase limit for irrational beta.
Novelty hypothesis      Formal generalization of the classical survival asymptotic;
                        the geometric family theorem is still the larger target.
Falsifier               The cutoff phase or normalization changes the leading term.
Already killed by?      No matching obstruction; the finite half-ratio bound is checked.
Existing machinery      Mathlib Stirling, the concrete phase proof, and weighted renewal.
Maximum Phase-0 scope   First-term Stirling limit, tail ratio limit, survivor transfer.
Promotion criterion     Expanded Lean consumers with no assumed asymptotic input.
Stop criterion          Keep critical mass and explicit jump identification separate.
```

The new
[`BeattySlopeEndpointAsymptotic.lean`](../../formal/Problems/Juggler/BeattySlopeEndpointAsymptotic.lean)
proves the terminal theorem for **every fixed real** `0<beta<1` and the
survivor theorem for **every fixed irrational** boundary in that interval.
The reciprocal consumer explicitly quantifies over every irrational
`alpha>1`, with no upper slope cutoff. These are statements about actual
weighted word sums, not an abstract sequence satisfying an assumed recurrence.

Put

\[
 q=1-\beta,\quad z=\frac{\beta}{2q},\quad
 v=\frac{2^{-\beta}}q,\quad C_\beta=(2\pi\beta q)^{-1/2},\quad
 u_\beta(n)=\frac{S_{\beta,z}(n)}{v^n}.
\]

Lean checks both explicit normalizations. With the strict endpoint convention,

\[
 \sqrt n\,\frac{A_{\beta,z}(n)}{v^n}
       -C_\beta 2^{\{n\beta\}}\longrightarrow0.
\]

The first term contributes
`C_beta*2^(-(1-frac(n*beta)))`; its full tail divided by that first term
tends to two. The Stirling proof lets the cutoff and complementary index
tend to infinity for each fixed boundary, avoiding the previous fixed
numerical cutoff. The finite half-geometric majorant justifies passage from
individual tail terms to their infinite sum.

For irrational `beta`, define the **weighted survivor profile**

\[
 \psi_\beta(t)=C_\beta\sum_{j\ge0}u_\beta(j)\,2^{\{t-j\beta\}}.
\]

Then the following facts are **EXACT — LEAN VERIFIED**, with no assumed
Stirling estimate, terminal limit or counting identity:

\[
 \sum_{j\ge0}u_\beta(j)<\infty,\qquad
 n^{3/2}u_\beta(n)-\psi_\beta(n\beta)\longrightarrow0,
\]

\[
 C_\beta\le\psi_\beta(t)
   \le2C_\beta\sum_{j\ge0}u_\beta(j),\qquad
 \psi_\beta(t+1)=\psi_\beta(t).
\]

The profile series is absolutely summable at every real phase. The lower
bound comes from the empty surviving word. The expanded consumers display
the actual finite word sums, real-power base and fractional-part kernel,
and make the absence of an asymptotic premise explicit. The public axiom
audit records only `propext`, `Classical.choice` and `Quot.sound`.

This advances the classical BGL-type survival part of the family programme.
It does **not** yet identify the original first-passage jump profile `F` for
all slopes. In particular, weighted survivor sums cannot simply be called
unweighted survivor counts; the exact removal of the tilt applies at each
fixed first-crossing class. No rate or uniform error near `beta=0,1` is
claimed. Rational boundaries are covered by the terminal theorem, while the
survivor theorem retains irrationality because its strict endpoint renewal
identity requires it.

The critical-mass continuation below now completes the probability-flow
input for the family. Identifying the explicit jump profile remains a
separate step: the survivor theorem alone does not identify it.

**PROMOTE** the unconditional tilted endpoint and survivor phase theorems,
including finite positive periodic profile bounds. The full first-passage
profile and geometric family theorem remain the active objective.

### Critical first-passage mass for the whole irrational family (24 September)

```text
Mathematical target     Total critical first-passage probability is one for every
                        irrational boundary 0 < beta < 1.
Novelty hypothesis      A formal family version of the classical probability-flow law.
Falsifier               The centered-moment bound or removal of the tilt fails.
Already killed by?      No matching obstruction; the logarithmic proof uses the same
                        finite-word partition and survivor decay now available here.
Existing machinery      General word partition, crossing bounds, summable tilted survivors.
Maximum Phase-0 scope   Critical survival tends to zero; first-passage masses sum to one.
Promotion criterion     Lean checks actual critical word sums with all slope assumptions.
Stop criterion          Leave Beatty reindexing and jump-profile identification explicit.
```

[`BeattySlopeCriticalMass.lean`](../../formal/Problems/Juggler/BeattySlopeCriticalMass.lean)
defines the actual critical Bernoulli word mass

\[
 b_\beta(n,k)=(1-\beta)^n\left(\frac\beta{1-\beta}\right)^k,
\]

and its sums `Q_n` over surviving words and `P_n` over first-passage words.
The last-letter partition conserves both mass and centered first moment.
First-crossing heights lie in `[-beta,0)`, while survivor heights are
nonnegative, giving the surviving first-moment bound `M_n<=beta`.
For endpoint height `h=k-beta*n`, Lean checks the exact tilt identity
`b_beta(n,k)=z^k*2^h/v^n`. Splitting at any `H>0` gives

\[
 Q_n\le 2^H u_\beta(n)+\frac\beta H.
\]

For each fixed height, the first term tends to zero by summability of
`u_beta`; then increasing the height forces `Q_n->0`. The finite identity
`sum_{j=0}^n P_j+Q_n=1` therefore proves

\[
 \sum_{n\ge0}P_n=1.
\]

These are **EXACT — LEAN VERIFIED** statements about the actual word sets,
not hypotheses on an abstract random walk. The finite bound and mass
partition cover rational boundaries in `(0,1)` too; the infinite limit
currently retains irrationality. The proof needs no convergence rate or
Diophantine estimate. The expanded audit at this stage checks 22 consumers
and 52 public theorem records, with only the three standard Lean axioms.

**PROMOTE** the formal probability-flow theorem for the whole irrational
family, acknowledging its classical role. The sum here is indexed by
crossing depths; the Beatty jump-weight normalization requires the explicit
reindexing in the next bounded continuation.

### Beatty reindexing of the general critical mass

```text
Mathematical target     Reindex critical crossing probabilities as exact jump weights;
                        prove sum_{r>=1} w_r = beta/(1-beta).
Novelty hypothesis      Formal family normalization, an input to the geometric theorem.
Falsifier               A crossing is omitted, counted twice, or has the wrong zero atom.
Already killed by?      No matching obstruction found; crossingDepth is strictly monotone
                        and every first-passage word has its unique crossing edge.
Existing machinery      General crossing theorem and total critical probability one.
Maximum Phase-0 scope   Exact reindexing, zero atom, and positive-index total mass.
Promotion criterion     Actual-count Lean statements with all slope assumptions expanded.
Stop criterion          Do not assert a first-passage phase limit from mass alone.
```

[`BeattySlopeSeries.lean`](../../formal/Problems/Juggler/BeattySlopeSeries.lean)
now proves this normalization for the actual counts. Put

\[
 m_r=\lfloor r/\beta\rfloor,\qquad
 c_r=P_\beta(m_r+1),\qquad
 w_r=c_r\beta^r(1-\beta)^{m_r-r}.
\]

Here `P_beta` denotes the integer word count, whereas `P_n` in the preceding
section denotes a probability. Lean checks `m_r>=r`, and every first-passage
word at `m_r+1` has exactly `r` odd letters. Its critical probability is
therefore `(1-beta)*w_r`. There is no first-passage mass outside these edges,
and strict increase of the edge map prevents double counting. Reindexing
the proved mass-one series gives

\[
 \sum_{r\ge0}w_r=\frac1{1-\beta},\qquad w_0=1,\qquad
 \sum_{r\ge1}w_r=\frac\beta{1-\beta}=\frac1{\alpha-1}.
\]

These identities are **EXACT — LEAN VERIFIED** for every irrational
`alpha>1`. The public reciprocal-slope interface and expanded consumer
explicitly cover slopes above two. The finite crossing identities require
only `0<beta<1`. At this stage the combined audit has 25 expanded consumers
and 61 public theorem records.

**PROMOTE** the exact family normalization. Its classical probability-flow
origin is acknowledged; the contribution here is the checked connection to
the actual Beatty counts over the entire slope range. The continuations below
now telescope the survivor profile into this series and transfer the
asymptotic to the original counts. Geometry remains a separate family theorem.

For the already checked tilt, the exact identification is now

\[
 (1+z)\psi_\beta(-\beta\delta)-v\psi_\beta(\beta(1-\delta))
   =C_\beta 2^{-\beta\delta}
     \left(1+\sum_{r\ge1,\ \{r/\beta\}<\delta}w_r\right),
 \qquad 0<\delta<1.
\]

This identity is **EXACT — LEAN VERIFIED** in
[`BeattySlopeIdentification.lean`](../../formal/Problems/Juggler/BeattySlopeIdentification.lean).
The exact one-step partition supplies the left side; after reindexing, the
kernel doubles exactly when the crossing phase is strictly below `delta`.
The total-mass identity cancels the remaining constant. The strict inequality
is retained at the atoms. The count transfer uses the normalization
`R_r^+=m_r*c_r/binom(m_r,r)` for positive `r`.

### Exact profile identification and original count asymptotic (24 September)

The identification continuation has the following bounded scope:

```text
Mathematical target     Identify the consecutive-survivor transfer with the exact
                        strict jump profile for every irrational 0 < beta < 1.
Novelty hypothesis      A checked explicit profile identity across the entire slope range.
Falsifier               The tilt leaves an extra constant or reverses a jump convention.
Already killed by?      No matching obstruction found; total mass and unique crossing
                        reindexing are proved, including slopes alpha > 2.
Existing machinery      Summable tilted survivors, kernel bounds, critical jump weights.
Maximum Phase-0 scope   Exact profile identity on 0 < delta < 1 and normalization bounds.
Promotion criterion     Expanded Lean identity with actual count weights and strict atoms.
Stop criterion          Leave the count asymptotic and geometric assembly separate.
```

The identity and its monotonicity, normalization bounds and exact endpoint
corollaries are checked in `BeattySlopeIdentification.lean`. **PROMOTE** the
exact identity, including its value at each atom. The count continuation
has the following separate scope:

```text
Mathematical target     Prove R_r^+ - F_beta({r/beta}) -> 0 for every irrational
                        0 < beta < 1 using the original integer count ratio.
Novelty hypothesis      Full explicit first-passage profile across all irrational slopes.
Falsifier               The moving quotient loses its lower bound or leaves a tilt factor.
Already killed by?      No matching obstruction; the weighted survivor limit, first-term
                        Stirling limit and exact profile identity are now checked.
Existing machinery      Consecutive-survivor difference, positive kernel and Beatty edges.
Maximum Phase-0 scope   Additive phase asymptotic in the two equivalent integer normalizations.
Promotion criterion     Expanded actual-count Lean theorem with no asymptotic premise.
Stop criterion          Leave convergence rates and the geometric family assembly explicit.
```

[`BeattySlopeAsymptotic.lean`](../../formal/Problems/Juggler/BeattySlopeAsymptotic.lean)
now proves, for **every fixed irrational** `alpha>1`,

\[
 R_r^+=\frac{m_r c_r}{\binom{m_r}{r}}
       =\frac{r c_r}{\binom{m_r-1}{r-1}},\qquad
 R_r^+-F_\alpha(\delta_r)\longrightarrow0,
\]

where `m_r=floor(alpha*r)`, `delta_r=alpha*r-m_r`, and

\[
 F_\alpha(t)=1+\sum_{j\ge1,\ \delta_j<t}
   c_j\alpha^{-j}(1-\alpha^{-1})^{m_j-j}.
\]

The finite ratio identity is for positive `r`; both sequences have the same
limit statement. The proof first transfers the weighted survivor asymptotic
to the actual weighted first-passage sequence, retaining the consecutive-depth
correction until its limit is taken. The first binomial term has a moving
phase factor bounded below by `C_beta/2`. This justifies division even at
phases approaching jumps. At every positive crossing the strict cutoff is
exactly `r`, so the letter weight cancels from the quotient. Periodicity and
the exact profile identity finish the argument.

The formal corollaries include monotonicity of `F_alpha`, its bounds
`1<=F_alpha(t)<=alpha/(alpha-1)`, and exact values
`F_alpha(0)=1`, `F_alpha(1)=alpha/(alpha-1)`. The expanded reciprocal consumer
shows the actual integer counts, `floor(alpha*r)`, both slope hypotheses,
and the strict inequality in the jump series. The combined audit checks 30
expanded consumers and 77 public records using only the three standard Lean
axioms. No asymptotic premise, Diophantine estimate, rate or uniformity as
the slope approaches one or infinity is assumed or concluded.

**PROMOTE** the full qualitative first-passage phase theorem for the entire
irrational slope family. The two-thirds gap law, complete cluster set,
empirical law and local Minkowski measure still need their family assembly.
The classical survival and probability-flow inputs retain their existing
attribution; this proof does not establish a literature-priority claim.

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
positivity (a written positive lower bound `0.16195...` now follows from
Wu-Wang), a Lean formalization of that arithmetic input,
a quantitative phase remainder, evaluation of the support endpoints,
full Lean formalization of the written `p<62/41` arithmetic improvement,
`L^p` density integrability at `p=62/41` and above, optimal CDF Holder regularity,
and a matching Hausdorff lower bound for the infinite-density set,
effective numerical constants, and the Gamma-law generalization to
arbitrary irrational `alpha>1`. The weighted survivor phase,
its absolute summability, positivity and periodicity now cover every such
irrational slope. Critical survival now tends to zero and the actual
first-passage probabilities sum to one; the actual positive-index Beatty
weights sum to `1/(alpha-1)`. The explicit strict jump profile and the
original integer-count asymptotic now cover that whole family too. The complete null perfect cluster set, singular empirical law, exact
CDF plateaus and envelope extrema now cover the family as well. The sharp
three-halves gap asymptotic, exact Minkowski content and whole local geometric
measure now cover every irrational slope too, and so does the Gamma-law package. Literature comparison
is separate from proof checking; existing paper claims and releases retain
their earlier evidence labels.

### Family cluster set, empirical law and consolidation (24 September)

```text
Mathematical target     Complete cluster set and singular empirical law for every irrational alpha>1.
Novelty hypothesis      Extend the explicit geometric consequences to the full slope family.
Falsifier               A zero crossing count or a mismatch of phase and endpoint conventions.
Already killed by?      No matching recorded obstruction; these are word counts, not a termination claim.
Existing machinery      Family phase theorem, generic jump-range geometry and irrational rotation.
Maximum Phase-0 scope   Exact logarithmic bridge, positive dense atoms, cluster set and empirical law.
Promotion criterion     Compiled public statements and expanded actual-count consumers with standard axioms.
Stop criterion          Keep any new analytic premise explicit; leave the gap asymptotic to the next stage.
```

**EXACT — LEAN VERIFIED.** The all-odd then all-even word proves every
crossing count positive, even at rational boundaries in `(0,1]` with weak
survival. The generic irrational-rotation proof is extracted once and reused
by the original and general developments. Positive dense distinct atoms,
the exact weight sum and the original-count phase theorem identify the full
family cluster set with the gap complement. It is nonempty, compact,
perfect and null, with actual subsequences at both traces of every gap and
eventual avoidance of compact gap interiors. Its exact envelope values are
`liminf=1` and `limsup=alpha/(alpha-1)`.

The empirical law of the actual ratios converges weakly to `F_*Uniform`.
It is atomless and concentrated on the null cluster set, so is singular
continuous. Its CDF satisfies `G(F(t))=t`, with value `delta_r` across the
closed r-th gap. Threshold frequencies converge at every real threshold,
and bounded continuous observables have the explicit phase-integral limit.
The family quantifies over every irrational slope greater than one, without
a rate or Diophantine hypothesis.

The exact specialization module identifies general and logarithmic indices,
phases, critical masses, weights and strict profiles. The original phase
asymptotic now follows from the family proof; duplicate asymptotic machinery
has been removed. This does not identify the differently tilted survivor
profiles. The new statements and precise remaining scope are in Section 25
of the [working note](../theory/juggler_beatty_first_passage_note.md).

**PROMOTE** this bounded family geometry and law continuation. The sharp
three-halves gap asymptotic, family Minkowski content and local geometric
measure remain next; the canonical rotation comparison and arithmetic
Hausdorff classification are prospective, not proved corollaries.

### Sharp gaps and the complete geometric family theorem (24 September)

```text
Mathematical target     Sharp gap asymptotics, exact Minkowski content and local geometric measure for every irrational alpha>1.
Novelty hypothesis      Extend the explicit first-passage geometry to the whole family; no priority claim for the general machinery.
Falsifier               A surviving slope restriction or normalization mismatch.
Already killed by?      No matching obstruction found; this is count geometry, not trajectory termination.
Existing machinery      Family phase theorem, tilted Stirling, equidistribution, gap counting and tube convergence.
Maximum Phase-0 scope   This extension and its direct geometric corollaries.
Promotion criterion     Actual-count Lean statements, expanded geometric consumers and standard axiom audit.
Stop criterion          Record any unresolved mathematical premise explicitly.
```

**EXACT — LEAN VERIFIED.** The auxiliary tilt cancels at every crossing.
The resulting amplitude is exactly `kappa_alpha=1/sqrt(2*pi*alpha*(alpha-1))`.
For each fixed irrational `alpha>1`, `r^(3/2)*w_r-kappa_alpha*F_alpha(delta_r)`
tends to zero, and positive two-sided three-halves bounds hold for every gap.
The exact gap-count constant is `A_alpha=kappa_alpha^(2/3)*integral_0^1 F_alpha^(2/3)`.
The actual open metric tube volume divided by `epsilon^(1/3)` tends to the
positive constant `M_alpha=3*2^(1/3)*A_alpha`; the Minkowski dimension is `2/3`.
The entire rescaled tube measure converges weakly to
`3*2^(1/3)*kappa_alpha^(2/3)*y^(2/3)*mu_alpha(dy)`. Its normalization gives
the limit of uniform spatial sampling in the shrinking neighbourhoods.
Both spatial tail masses and bounded-continuous observable averages are checked.

Seven registered family modules implement these statements. The public family
audit contains 160 theorem records; the three consumer modules contain 48
expanded statements, including seven new consumers for actual weights, all-slope
quantifiers, metric tubes and integrals. See Section 26 of the working note.
No convergence rate, uniformity in the slope, Hausdorff lower bound or Gamma-law
family extension is supplied. The classical precursors remain acknowledged.
**PROMOTE** this whole-family geometric theorem. Canonical rotation comparison
and arithmetic Hausdorff classification remain future work; no new branch opens here.

A review consumer, `actual_family_cluster_content`, now states the dimension,
content and tube-sampling limits directly for the set of real subsequential
limits of the original integer ratios, bringing the consumer count to 49.
Eight over-length family declaration names were shortened.

### Positive Hausdorff dimension at the logarithmic slope (24 September)

```text
Mathematical target     Discharge the Diophantine premise of Section 20 at log_2 3.
Novelty hypothesis      A known linear-form measure already gives a positive exponent.
Falsifier               A height or sign condition in the measure that the reduction violates.
Already killed by?      No; the Diophantine walls concern cycle finance, and Rhin (8) stays unused.
Existing machinery      Lean implication (42)->(44), Rhin (7), Wu-Wang Theorem 1.
Maximum Phase-0 scope   Written corollary only; no new Lean or arithmetic formalization.
Promotion criterion     An explicit reduction to (42) valid for every k>=1.
Stop criterion          Do not claim dimension 2/3 or critical-measure positivity.
```

**EXACT — HUMAN PROOF.** Rhin's (7), `|u_0+u_1 log 2+u_2 log 3|>=H^(-13.3)`
for `H>=2` with no constant, gives `|k log_2 3-p|>=c k^(-13.3)` for every
`k>=1` with `c=2^(-13.3)/log 2`: a near approximation has `2<=H<=2k`.
The Lean-checked implication then gives `H^(2/39.9)(K)>0` for the original
certificate cluster set. Positivity needs only some constant, so Wu-Wang's
noneffective exponent `4.1163051+epsilon` gives
`dim_H K>=2/(3*4.1163051)=0.16195...`. Minkowski dimension remains `2/3`;
exact Hausdorff dimension and critical-measure positivity stay open.
**PROMOTE** within this dossier as `J-beatty-rhin-hausdorff-lower-bound`;
Section 20 of the working note gives the proof.

### Hausdorff geometry for the whole family (24 September)

```text
Mathematical target     Hausdorff measure and dimension of K_alpha across all irrational alpha>1.
Novelty hypothesis      Almost-every-slope dimension 2/3 and quadratic positive measure for these count sets.
Falsifier               A log-slope-only ingredient in the Hoelder argument, or LiouvilleWith not matching (45).
Already killed by?      No; no obstruction record, and the Diophantine walls concern cycle finance.
Existing machinery      Generic tube-to-Hausdorff bound, Dirichlet hitting, family CDF, Mathlib ae_not_liouvilleWith.
Maximum Phase-0 scope   One family Hausdorff module, one arithmetic module and an interface consumer.
Promotion criterion     Actual-count Lean statements with standard axioms only.
Stop criterion          Any premise that cannot be discharged stays explicit.
```

**EXACT — LEAN VERIFIED.** Every family cluster set has finite two-thirds
Hausdorff measure. The family CDF inverts the profile, is flat on gaps and
maps `K_alpha` onto `[0,1]`, so phase hitting and Diophantine bounds give
Hölder regularity and matching lower bounds exactly as at the logarithmic
slope. Mathlib's null set of `LiouvilleWith` numbers gives
`dim_H K_alpha=2/3` for Lebesgue-almost every `alpha>1`. The quadratic norm
form gives explicit bad approximability for every quadratic irrational, so
those slopes, including the golden ratio, have positive finite two-thirds
measure. Five expanded consumers and 20 new audit records use only standard
axioms; see Section 27 of the working note. **PROMOTE**.

Continuation, **EXACT — LEAN VERIFIED**: at every Liouville slope the
cluster set has zero Hausdorff measure in every positive dimension, so
`dim_H K_alpha=0` while `dim_M K_alpha=2/3`. Exact rotation chains labelled
by `Z(r)=rp-q floor(r alpha)` and a generic cut cover of the jump range give
the covers. Hausdorff dimension therefore depends on the arithmetic of the
slope. Further, **EXACT — LEAN VERIFIED**: the critical two-thirds measure
is positive exactly at badly approximable slopes, and approximations of
order `q^(-nu)` bound the dimension by `2/(2+sqrt nu)`, so the dimension is
`2/3` exactly when the irrationality exponent is `2`, up to the written
combination with the Section 20 lower bound. Open: the exact dimension for
exponents strictly between `2` and infinity.

### Continuity in the slope (24 September)

```text
Mathematical target     Dependence of weights, laws and Minkowski content on the slope.
Novelty hypothesis      Continuity at every irrational slope without uniform constants.
Falsifier               A count that is not locally constant, or mass escaping to infinity.
Already killed by?      No; no obstruction record concerns slope dependence.
Existing machinery      Exact total mass, strict comparisons at irrational boundaries, Tannery's theorem.
Maximum Phase-0 scope   One continuity module and an interface consumer.
Promotion criterion     Actual-count statements with standard axioms only.
Stop criterion          Rational endpoints stay out of scope.
```

**EXACT — LEAN VERIFIED.** At an irrational boundary each actual count and
crossing index is locally constant, so each weight is continuous. The exact
total mass `beta/(1-beta)` and a Scheffé argument give `l1` convergence of
the weights along irrational boundaries, with no uniform tail constant. The
profiles converge at every non-atom phase, the singular laws converge weakly
and the exact Minkowski content is continuous at every irrational slope.
Section 28 of the working note. **PROMOTE**. Open: one-sided limits at
rational slopes, expected to be finite atomic laws.

### The Gamma-normalized law for the whole family (24 September)

**EXACT — LEAN VERIFIED.** The logarithmic Gamma package ports to every
irrational slope with no added hypothesis: the periodic amplitude
`q^t F_alpha(t)`, the absolutely continuous law mutually singular with the
binomial law, the explicit density series and its normalization, all real
moments, interval support equal to the full Gamma-count cluster set, dense
null blowup, weak `L^(3/2)`, `L^p` for `p<3/2`, the `1/3`-Hölder but
nowhere Lipschitz CDF and the `2/3` dimension bound for infinite values.
Ten family modules, four expanded consumers, 266 audit records. Section 29
of the working note. **PROMOTE**. The written `p<62/41` improvement stays
specific to `log_2 3`.

### Rational slopes and the family map (24 September)

**EXACT — LEAN VERIFIED.** Total critical first-passage mass is one and the
jump weights sum to `beta/(1-beta)` at every boundary, rational included.
As the slope decreases to `a/b`, counts freeze, weights converge in `l1`,
and the singular laws converge to the uniform law on `b` distinct atoms
`F_(a/b)((j+1)/b)`. Section 30 of the working note tabulates the family
map. **PROMOTE**. Open: the other one-sided limit, the counts at a rational
slope itself, exact dimensions for exponents in `(2,infinity)`, rates.

## Decision

`PROMOTE` -- for every irrational slope above one, the actual normalized
first-passage counts approach the exact strict jump series with its full
normalization. The complete cluster set is nonempty, compact, perfect and
null; both traces of every gap are actual cluster values, and the liminf
and limsup are exactly `1` and `alpha/(alpha-1)`. The family empirical law
is singular continuous, with exact threshold frequencies and CDF plateaus.
The original logarithmic phase theorem now specializes the general proof
through exact weight and profile equalities.

The three-halves gap law, cube-root neighbourhood volume, Minkowski dimension
`2/3` and exact content given by the two-thirds law moment now hold for every
irrational slope above one. The whole geometric limiting measure is the explicitly
scaled `y^(2/3)` reweighting of the empirical law throughout the family, with
its probability normalization. The following refinements remain at the logarithmic slope.
The Hausdorff upper bound and finite critical measure are unconditional;
matching lower bounds are proved under an explicit phase-hitting estimate,
now derived from a standard uniform Diophantine lower bound without exponent
loss. Bounds for every exponent above one suffice for dimension equality;
the stronger exponent-one bound supplies positive critical measure.
Written corollaries from the Rhin and Wu-Wang measures give
`H^(2/39.9)(K)>0` and `dim_H K>=0.16195...` at `log_2 3`
(**EXACT — HUMAN PROOF**).
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
