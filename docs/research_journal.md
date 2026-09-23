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

## 2026-09-23 -- Beatty phase profile as a positive jump series

The qualitative logarithmic-slope theorem is now **EXACT — LEAN VERIFIED**:
`r c_r/binom(m_r-1,r-1)-F(delta_r) -> 0`, with
`F(delta)=1+sum_{delta_r<delta} c_r beta^r (1-beta)^(m_r-r)`.
The finer binomial phase limit discharges the survivor asymptotic input;
finite first moments prove critical first-passage mass one; exact reindexing
identifies the whole jump series, with total mass `1/(alpha-1)` and first
jump `beta`. The complete accumulation set is now also Lean-checked: the
envelope minus the explicit open jumps is compact, perfect and Lebesgue-null.
Every gap endpoint is a subsequential limit, and closed intervals strictly
inside gaps are eventually avoided. The empirical law is now proved to be
`F_*(uniform[0,1])`, atomless and singular with respect to Lebesgue measure,
with continuous CDF `G`, exact identity `G(F(t))=t` and plateau height `delta_j`
on the j-th closed jump interval. The gap weights now have checked sharp
order `r^(-3/2)`; the exact tube formula gives `lambda(K_epsilon)` of order
`epsilon^(1/3)` and Minkowski dimension `2/3`. The exact content is now
`3*2^(1/3)*kappa^(2/3) integral_0^1 F(t)^(2/3) dt`, equivalently the
two-thirds moment of the singular law times the explicit scale factor.
The whole geometric law is now checked too: cube-root-rescaled tube measures
converge weakly to `3*2^(1/3)*kappa^(2/3)*y^(2/3) dmu(y)`; uniform tube
probabilities converge to its normalization. Localized gap counts and a
`4*epsilon` geometric comparison give every bounded continuous spatial
average. Nineteen consumer dependency records check the new interfaces,
including statements directly over the original integer certificate counts.
Hausdorff dimension, quantitative phase rates, effective numerical
constants and arbitrary irrational slope remain separate extensions.
**PROMOTE** the completed qualitative
specialization; no paper/release, priority or trajectory-termination claim is
changed. Canonical proof boundary: Sections 13–18 of the
[comparison note](theory/juggler_beatty_first_passage_note.md) and the
[dossier](problems/juggler_winkler_phase_collapse.md).

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

## 2026-09-23 -- One fixed ternary class already transports lower bounds globally

The previous recommendation supplied no new fixed-root lower count. The
proposed neighborhood shortcut now has an exact limitation: every positive
odd unit root has an actual predecessor in any class modulo 3^r, with
exponent at most 2*3^r. Lean checks simultaneous coefficient transport and
finite-block bounds at cost 3/2^(2*3^r), plus equivalence of class-wide and
global divergence at nonperiodic unit roots. **CLOSE** this route as a weaker
uniform arithmetic target. Six exact controls pass. No lower-count premise,
Juggler pressure or termination is proved. See the
[dossier](problems/collatz_fibre_lower_transfer.md).

## 2026-09-23 -- One-halving runs have summable fixed-root weight

At a fixed positive root a, all actual words with one arbitrary first
exponent followed by d one-halving steps contribute at most 3a/2^(d+1),
with total allowance 3a. Lean checks both signs, actual returns and the
necessary divisor; the negative fixed point a=1 is retained as a growing
exception. **PROMOTE** this summable-family reduction. Five exact controls
pass. Transported peaks cannot themselves supply fixed-root divergence;
the remaining word count and Juggler pressure stay open. See the
[dossier](problems/collatz_fibre_run_tail.md).

## 2026-09-23 -- Actual coefficient peaks defeat local Harnack comparison

A fixed exponent branch transports the actual one-halving spike into every
ternary unit neighborhood, for both signs. Lean proves coefficient values
above every bound at arbitrarily large depths and positive odd heights;
four independent actual-word and mean controls pass. **CLOSE** uniform local
Harnack comparison as a route from averages to a fixed-root lower bound.
The peak's integer target varies with depth, so fixed-integer divergence and
Juggler termination remain open. See the
[dossier](problems/collatz_fibre_local_bounds.md).
