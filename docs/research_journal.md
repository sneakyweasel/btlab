# Recent research decisions

The latest twelve entries are kept here for orientation. Durable statements,
proofs and decisions belong in the [claim ledger](theory/theorem_ledger.md),
branch dossiers and proof maps. Search those records before relying on an older
journal claim; later proofs can supersede earlier open boundaries.

Earlier chronology is recoverable from Git; the full journal before this
consolidation is at `e9725762eaf028d1ace354ff20e0fc48f1a3d143`. See
[recovery instructions](history.md).
New entries should name the changed result, its evidence, remaining premise,
decision, and canonical record. Keep the journal brief.

## 2026-09-24 -- Counting escapes reduces to the all-depth program

Clotho Phase-0. **EXACT — LEAN VERIFIED:** an escape rate above `3/8`
excludes divergent orbits and makes every orbit eventually periodic
(`J-escape-rate-excludes-divergence`), by the generic Tao reduction and the
OOEE contagion. The hope that escapes are easier to count than failures does
not survive: escape can be arbitrarily slow, so at bounded depth an escaping
start is a live start, and Ville's maximal inequality for the fair multiplier
martingale (checked exactly on words to depth 60) needs fair parity at every
depth. **CLOSE** as a reparameterization. See the
[escape-rate dossier](problems/juggler_escape_rate.md).

## 2026-09-24 -- Depth-five productions priced and parked

Atropos Phase-0. The first-descent words through length four are exactly
`E`, `OE`, `OOEE`, so the kernel-checked `5/8` contagion sits at the
depth-four ideal `0.6328`. Depth five adds `OOOEE` and `OOEOE` and would lift
the ideal to `0.7512`, lowering the required failure rate from `3/8` toward
`1/4` (COMPUTATIONALLY VERIFIED, exact multipliers). Their fibres are windows
of length `P^(5/32)` rather than `P^(7/16)`: the depth-four mixed-mode bound
`O(P^(13/32))` is weaker than trivial there, and an averaged poor tail needs
differenced depth-five mixed sums with shifts up to `P^(5/32)`, beyond Paper
B's `P^(1/8)` frozen gaps. **PARK.** See the
[depth-five dossier](problems/juggler_depth_five_production.md) and its
obstruction record.

## 2026-09-24 -- Written-proof rows converted to Lean, with a coverage audit

**EXACT — LEAN VERIFIED**, kernel trust: twelve rows leave the written-proof
category. They are Paper A E.7 (`OOEEscapeResidue`), the hug-flow image gap,
the cube-threshold hidden parity, the first-OOO square cell, the odd-preimage
Type 0/1/2 criterion, the OOE carry substitution (`D - d = 36r^2 + 1` exactly,
by coefficient positivity in `t = (r-3)/2`) and seven post-L envelope rows.
The new row `J-paper-b-barrier-mass-phase-count` proves mass preservation by
the non-rising update, the `fract(t beta)` form of the barrier rise and
`N_(d+1) = 2 N_d - b_d M_d`. A review of 39 further rows that name existing
Lean found none fully covered; 29 now link their partial support.
Corrections: several post-L statements turned an envelope failure into an
orbit claim (reworded, counterexample `n = 6`), and two reviewer errors,
on Rhin's measure and on `lambda**` against `100/203`, were caught at source.
Later the same day, the averaged contagion bound lowered the Section 9.2
corollaries: termination follows from the pressure or the no-momentum
hypothesis at any failure exponent above `3/8`, through the OOEE contagion
at `5/8` (`J-fate-pressure-three-eighths`, `J-fate-no-momentum-three-eighths`);
an intermediate `103/203` form is superseded. Both hypotheses stay open.
**PROMOTE** the conversions. Remaining premise: rows that mix measurements
with theorems stay written proofs pending a split. See the claim ledger and
the dossiers for [hug flow](problems/juggler_hug_flow_depth_two.md),
[first OOO](problems/juggler_first_ooo_escape.md),
[empty odd preimage](problems/juggler_empty_odd_preimage.md),
[cubic induction](problems/juggler_cycle_cubic_induction.md) and
[OOE escape](problems/juggler_ooe_escape_families.md).

## 2026-09-24 -- Beatty phase geometry and quantitative Gamma-law regularity

**EXACT — LEAN VERIFIED** at the logarithmic slope: the actual integer ratios
approach the explicit positive jump profile, including its critical total
mass and strict atom convention. Its complete cluster set is null and
perfect; the empirical law is singular continuous with exact CDF plateaus.
The set has Minkowski dimension `2/3`, exact positive content, and local
content measure `3*2^(1/3)*kappa^(2/3)*y^(2/3) dmu(y)`.
Finite two-thirds Hausdorff measure is unconditional; matching lower bounds
retain explicit Diophantine premises. The exact BGL Gamma quotient gives
amplitude `q^t F(t)` and an absolutely continuous empirical law, mutually
singular with the original law. The explicit occupation density, logarithmic
normalization and all real-power moment series are now Lean-checked too,
including the finite-cutoff endpoint term and negative-power integrability.
Its support and full Gamma-count cluster set are a nondegenerate interval.
The density is lower semicontinuous, infinite on a dense null G-delta,
and locally essentially unbounded throughout the support interior,
independently of its almost-everywhere version. The density and support
consumer audits check twenty and twenty-four dependency records with only
standard Lean axioms. A further fifteen-record audit checks cube-root
set concentration, weak three-halves density tails, `L^p` for `1<=p<3/2`,
a Holder but nowhere locally Lipschitz CDF, and Hausdorff dimension at
most `2/3` for the entire infinite-density set. Rates, general slopes,
endpoint evaluation, endpoint/supercritical integrability and matching
Hausdorff lower bounds remain open.
**PROMOTE** the quantitative regularity and exceptional-set upper bounds. No new
deposit, priority or trajectory-termination claim. Canonical proof boundary:
Sections 13–23 of the
[comparison note](theory/juggler_beatty_first_passage_note.md) and the
[dossier](problems/juggler_winkler_phase_collapse.md).

The bounded overlap continuation adds an **EXACT — LEAN VERIFIED** criterion:
the density is in `L^2` exactly when the explicit ordered pair-overlap sum
is finite. A separate **EXACT — HUMAN PROOF** combines Wu-Wang and
Erdos-Turan with profile truncation to give `h in L^p` for `1<=p<62/41`,
including the original three-halves endpoint, weak `L^(62/41)`, and a
`21/62`-Holder CDF. **PROMOTE** that written arithmetic improvement;
its discrepancy argument and classical inputs are not formalized in Lean.
The 4096-atom Arb audit is finite evidence only. `L^2` remains unresolved.
The complete proof and trust boundary are in the same dossier; the paper
retains its previously audited formal range pending incorporation.

The arbitrary-slope continuation now checks the actual binary-word counting
recurrence for every irrational real boundary, the survivor/first-passage
partition for every real boundary, and the crossing edge
`floor(r/beta)+1` for `0<beta<=1`. Exact finite-set equalities recover the old
logarithmic counts, whose counting theorem now specializes the general proof.
**PROMOTE** this reusable formal foundation, without a novelty claim for the
classical identity. Exact removal of crossing weights and the normalized
renewal identity support the bias `p=beta/(2-beta)`. The finite tilted tail
is between its first term and twice that term at every positive depth.
The Stirling continuation proves the explicit tilted terminal phase for
every real `0<beta<1` and the unconditional weighted survivor phase for every
irrational `alpha>1`. Its convolution series is summable, positive, bounded
and periodic. The centered-moment and tilt argument also proves zero critical
survival mass and total first-passage probability one for the family.
Beatty reindexing fixes the actual positive-index jump mass at `1/(alpha-1)`.
The exact strict profile identity and original integer-count phase asymptotic
are now checked for every irrational `alpha>1`, in both binomial normalizations.
**PROMOTE** the full qualitative phase theorem and its family cluster set
and singular empirical law: positive dense atoms give a nonempty compact
perfect null set, exact gaps and envelope extrema. Threshold frequencies
and CDF plateaus are checked for every irrational slope above one. The
original phase theorem now specializes the family proof through an exact
profile bridge; irrational recurrence and equidistribution are shared.
The sharp three-halves gap law, universal Minkowski dimension `2/3`, exact
positive content and whole geometric measure now cover every irrational slope.
Uniform spatial sampling tends to the normalized two-thirds-weighted empirical law.
**PROMOTE** this family extension: 160 public audit records and 48 expanded
consumers. Sections 25–26 record the scope. Rates, the Gamma-law family and
arithmetic Hausdorff classification remain separate.

## 2026-09-23 -- OEIS generator corrections and exact modified-map descent

The bounded A325904 check found an empty-sum error at order two in the
printed A100982 transform, plus six stored generator terms inconsistent
with their recurrence. Exact coefficients and the repaired upper limit
reproduce 256 certificate counts and survivor depths 0..406.
**CLOSE** as a new counting method; the all-orders repaired identity
remains unproved here. See the [audit](problems/juggler_oeis_generator_check.md).

For A095396, a written floor-equality proof gives exactly one unit of
descent at every actual OE pair; actual EO pairs also strictly descend.
**PROMOTE** the bounded structural identity, with regressions through
10000 and at large perfect powers. No Lean or novelty claim, no termination
result, and no manuscript change. See [modified-map descent](problems/juggler_modified_juggler_descent.md).

## 2026-09-23 -- Cross-sign pairing has an actual two-generation deficit

Pairing the signed inverse coefficients gives a one-step lower bound 9/7,
but keeping each sign fixed for two steps gives joint coefficient
20064/29127 < 1 on the class 4 modulo 27. Lean checks both identities,
the exact complete sums, the affine bound and now the complete actual
reciprocal sums. Inverse-exponent pairs enumerate ordinary ancestors
without duplication, and the normalized paired mass on a=31+54t is below
3/4. Real summability is checked; signed positivity and oddness are shared.
**CLOSE** automatic compensation: iterating the one-step gain counts
mixed-sign paths; Juggler's two signed codes are negatives of one another,
not independent filters. The 3/8 pressure target is unchanged. See the
[dossier](problems/collatz_fibre_sign_coupling.md).

## 2026-09-23 -- Ancestor generating functions retain the harmonic-mass problem

The generating-function audit finds no lower estimate in the published
Hardy fixed-point or natural-boundary results. A nonperiodic root has a
single-source equation, not a fixed-point equation; harmonic mass uses
the Bergman norm, where expansiveness fails. Lean checks the ancestor
indicator's source equation, minimality, and the exact finite-energy
equivalence for arbitrary nonnegative weights. The known ancestor ray of
3 has finite harmonic mass and a natural boundary for both signs.
**CLOSE** this automatic analytic transfer; the unit-root word-count
target and Juggler pressure remain open. See the
[dossier](problems/collatz_ancestor_generating_audit.md).

## 2026-09-23 -- Every fixed repeated inverse block has summable mass off cycles

Lean extends the one-halving tail to any fixed positive inverse block w:
after one free exponent, D repetitions contribute at most
6*D_w(a)/2^(D*sum(w)) at a nonperiodic root, for either sign. The complete
first-exponent sum and total over all D are bounded. A zero affine anchor
forces a periodic root; the negative 5,7 cycle supplies a growing exception.
**PROMOTE** this family reduction. Finite unions of pure repeated-block
families cannot supply divergence; arbitrary switching remains unbounded.
The next signed-word target is a depth-averaged lower count for varying
actual words at a fixed integer. Juggler pressure and termination remain
open. See the [dossier](problems/collatz_fibre_word_tail.md).

## 2026-09-23 -- Near-critical periodic weights already require the global cell rate

Lean now transports any nonzero subsolution coordinate to a global
geometric lower bound at the same rate, with cost 3/2^(2*3^r) and one
depth shift. Therefore nonzero periodic tables at rates tending to one
already imply uniform subexponential cell lower decay. **CLOSE** treating
the capped family as an easier local shortcut; its root-prefactor bound
is additional. This downgrades the proposed 1-1/r scale, without refuting
it. The next target is a direct actual-word lower count at one ordinary
integer. No coefficient divergence or Juggler input follows. See the
[dossier](problems/collatz_fibre_rate_barrier.md).

## 2026-09-23 -- Capped weights improve fixed-root constants; the near-critical bound remains open

Lean constructs the greatest bounded periodic subsolution at each rate and
level, with monotonicity under ternary refinement at a fixed rate. Exact
lower/upper iteration brackets all coordinates within 10^(-9) at levels
1–4. At level four and q=3/4, the root-to-deficit ratios improve from
0.281 to 0.466 for plus root 7 and from 0.146 to 0.256 for minus root 47.
**PARK** further finite tables. The remaining target is a positive lower
bound on that ratio along rates tending to one; no coefficient divergence,
Juggler pressure or termination follows. See the
[dossier](problems/collatz_fibre_subsolutions.md).

## 2026-09-23 -- Fixed-root coefficients are at most linear; block-minimum weights lose their prefactor

Lean now bounds both signed complete unit coefficients by A_s(a)*(d+1)
at each nonperiodic positive odd root, using actual endpoints, harmonic
mass and the finite-height tail. The all-source bound loses only 21/5.
For geometric generation blocks whose rate is certified by the block
minimum, the normalized root weight divided by 1-q is at most
4*A_s(a)*N^3*(2/3)^(N-1), and tends to zero. **CLOSE** that construction;
other periodic subsolutions and fixed-root divergence remain open. Fifteen
exact controls pass. No Juggler pressure or termination follows. See the
[dossier](problems/collatz_fibre_block_weights.md).

## 2026-09-23 -- Subcritical weights isolate the missing fixed-root constant

Lean checks that L_s h>=q*h with 0<=h<=1 gives C_d(a)>=q^d*h(a),
and that a family q_i tending to one forces divergence if its normalized
root values stay above c*(1-q_i). Both family premises remain open.
Eight exact Python certificates at levels 1–4 reach q=0.771500620;
they establish no asymptotic rate or root constant. **PARK** further finite
tables; the next target is the analytic family estimate. The newly located
Nikpour–Rabbani preprint is registered as an unchecked abstract claim,
not a verified input. No Juggler pressure or termination follows. See the
[dossier](problems/collatz_fibre_critical_minorants.md).
