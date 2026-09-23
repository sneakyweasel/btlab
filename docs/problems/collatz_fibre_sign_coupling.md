# Combining signed arithmetic: one-step gain, two-step joint deficit

23 September 2026. Decision: **CLOSE** automatic cross-sign compensation.
This does not close more selective couplings or prove convergence of any
fixed-root coefficient series.

## Problem

Can the complementary arithmetic of 3n+1 and 3n-1 compensate for poor
inverse fibres, and can that gain strengthen the Juggler termination route?

## Exact statement

Let S_s(n) be the positive odd accelerated signed map. Let K_d^s(a) be
the complete depth-d inverse coefficient, retaining odd sources prime to
three, as in [the fibre dossier](collatz_fibre_mass.md). Thus an actual
inverse word with halving exponents k_1,...,k_d contributes
3^d/2^(k_1+...+k_d). The sign is fixed throughout the word.

For every positive odd n,

\[
 S_-(2n+1)=S_+(n),\qquad S_+(2n-1)=S_-(n).
\]

For every unit target a, K_1^+(a)+K_1^-(a)>=9/7. Nevertheless,
for every a congruent to 4 modulo 27,

\[
 K_2^+(a)=\frac{12076}{29127},\qquad
 K_2^-(a)=\frac{7988}{29127},\qquad
 K_2^+(a)+K_2^-(a)=\frac{20064}{29127}<1.
\]

These are full infinite exponent sums, not cutoff values. The scalar
affine bound below further gives, for every a=31+54t with t>=0,

\[
 a\sum_{s\in\{+1,-1\}}\sum_{\substack{n\ge1\text{ odd},\ 3\nmid n\\S_s^2(n)=a}}
       \frac1n < \frac34.
\]

The sum counts the two signs separately, even if an ancestor belongs to
both sets. Thus taking the union cannot repair this two-generation deficit.
This is not a statement about the union over all depths.

## Current literature

The exact parity conjugacy is classical Bernstein--Lagarias,
`bernstein-lagarias-1996-conjugacy-map`, whose
[publisher record](https://doi.org/10.4153/CJM-1996-060-x) was checked again.
The signed Juggler code and its integer-realization obstruction are in
[Paper E](../theory/juggler_signed_collatz_note.md). Negation is not a
new independent parity constraint. The displayed simultaneous deficit is
a project-specific exact audit of the existing coefficient operator;
no literature-priority claim is made.

## Branch budget

- **Target:** whether opposite signs compensate at the same target under fixed-sign iteration.
- **Novelty hypothesis:** complementary inverse congruences could remove individual deficits.
- **Falsifier:** a complete joint coefficient below one, persisting for actual integers.
- **Already killed by?:** individual finite-weight deficits and failed integer transport are known; they do not by themselves exhibit a simultaneous deficit for the paired unweighted coefficients.
- **Existing machinery:** complete residue transfer, actual inverse paths, geometric tail bounds and the signed Juggler code.
- **Maximum Phase-0 scope:** depths 1 through 4 for controls; prove the pairing and depth-two obstruction, with the actual-mass correction.
- **Promotion criterion:** a quantitative bound for genuine fixed-sign trajectories that improves the open arithmetic target.
- **Stop criterion:** close automatic compensation when joint deficits survive; do not start a different coupling search in this phase.

## Balanced-ternary formulation

Only residues modulo 9 and 27 are needed. Balanced ternary is an optional
representation of these ordinary congruences, not an extra restriction.

## Why BT may be relevant

The relevant arithmetic is ternary residue dependence. Changing digit
notation does not make the two signs independent.

## Candidate operations / invariants

**EXACT — HUMAN PROOF**, with the pairing, coefficient bounds and scalar
inequality compiled in Lean: the statements above. The complete actual-mass
summation consequence below is a written proof; it is not claimed as an
additional compiled theorem. Independent review remains outstanding.

The paired one-step operator is L_++L_-. Its square contains L_+L_- and
L_-L_+ as well as L_+^2 and L_-^2. These cross terms describe trajectories
that switch maps. They cannot be used as additional ancestors of either
fixed-sign system.

## Experiments

Run `python tools/lab.py run research.collatz.fibre_sign_coupling`.
The [report](../../data/research/collatz/fibre_sign_coupling.json) retains
exact rational values, with depths limited to 1 through 4 and four actual
targets. The minima of the paired coefficients are approximately 1.286,
0.689, 0.521 and 0.384, respectively. The minimizing targets vary; no
decay or summability at a fixed integer is inferred.

At a=31, a certified interval for the actual paired normalized mass is
0.69124 < mass < 0.69192. The omitted infinite tail is included in the
upper bound. Independent forward enumeration checks actual path membership.

## Conjectures

None introduced. The pre-existing fixed-root coefficient divergence and
Juggler stopped-pressure estimates remain open.

## Counterexamples

The class 4 modulo 27 refutes uniform two-step reproduction even after
adding both signs. Every positive odd member is 31+54t.

Equal first images do not imply equal next images: S_+(3)=S_-(7)=5,
but S_+(5)=1 and S_-(5)=7. Thus the cross-sign affine pairing is not
a conjugacy of the subsequent fixed-sign dynamics.

## Formalization

[FibreSignCoupling.lean](../../formal/Problems/Collatz/FibreSignCoupling.lean)
proves both cross-sign identities, the uniform one-step lower bound, the
two exact depth-two coefficients for every natural target in the specified
class, and the scalar two-step reciprocal estimate. The general finite
period formula in [FibreMass.lean](../../formal/Problems/Collatz/FibreMass.lean)
certifies the full geometric sums rather than truncating them.

The [axiom audit](../../formal/AxiomCheckFibreSignCoupling.lean) records the
public interfaces. Ledger tag: written proof with local kernel evidence;
external advisory coverage is pending and no statement was sent externally.

Validation: the active Lean build passes all 9,033 jobs. The six-interface
axiom audit contains only propext, Classical.choice and Quot.sound. The
four new regression checks, existing fibre checks, ledger checks and
documentation links pass; the Lean style gate reports no new violations.

## Results

### Exact one-step table and why it fails to iterate

The plus one-step values, in residue order 0 through 8, are

\[
 (0,20,40,0,17,10,0,5,34)/21.
\]

The minus values are their residue reflection. Pairing gives 18/7 on
classes +/-1, 15/7 on +/-2 and 9/7 on +/-4. This is a genuine one-step
gain. At depth two the complete residue periods have lengths 6 then 18;
summing those geometric periods gives the rational values stated above.

If one iterates L_++L_- instead, positivity propagates the one-step lower
bound and gives at least (9/7)^d at depth d on unit targets. This counts
all sign strings, not just the two constant sign strings. Already at
depth two the mixed strings account for the missing reproduction. That
enlarged system supplies no estimate for the omitted fixed-sign words.

### Actual masses, with the affine error retained

Write an actual two-step inverse path as a <- b <- c, with positive
halving powers p,q>=2. For either fixed sign s,

\[
 3b=pa-s,\quad 3c=qb-s,\quad
 9c=pqa-s(q+3).
\]

Since (q+3)/(pq)<=5/4, for a>=2,

\[
 \frac ac\le \frac9{pq}\,\frac a{a-5/4}.
\]

Each actual ancestor has a unique forward intermediate state and unique
halving exponents. Summing this nonnegative inequality over all admissible
unit paths is therefore legitimate and is bounded by the complete
coefficient sum. The bound also proves finiteness of the reciprocal sum.
For a=31+54t,

\[
 a(M_2^+(a)+M_2^-(a))
 \le \frac a{a-5/4}\frac{20064}{29127}
 \le \frac{124}{119}\frac{20064}{29127}<\frac34.
\]

This proves an infinite progression of actual joint deficits, with no
periodicity hypothesis and no extrapolation from the finite controls.

### What this says about combining with Juggler

The two exact Juggler codes are H(n) for minus and -H(n) for plus.
Consequently a joint cylinder condition H(n)=r, -H(n)=s modulo 2^d is
empty unless r+s=0 modulo 2^d; when that relation holds it is exactly
the single condition H(n)=r. This is perfect dependence, not two
independent arithmetic filters whose densities can be multiplied.

Actual Juggler floor equations supply additional information. However,
the already-proved arbitrarily precise modular-return examples show why
their mere congruence compatibility does not force integral signed codes:
see [denominator coupling](juggler_cycle_denominator_coupling.md).
Likewise the [exact coded Juggler mass](juggler_code_mass_transport.md)
retains source multiplicities; it is not ordinary Collatz reciprocal mass.

Thus neither adding both signed inverse masses nor intersecting the two
signed code conditions supplies the missing Juggler arithmetic estimate.
The current contagion exponent 5/8 and required decay exponent >3/8 are
unchanged by this audit.

## Open questions

A genuinely useful joint estimate must retain actual floor realizations,
source heights and fixed signs. The signed fixed-root lower count and
Juggler upper pressure estimate remain distinct open problems. This
finite-depth deficit is not a refutation of either.

## Decision

**CLOSE** automatic cross-sign compensation as a repair of inverse-fibre
reproduction or a route to a tighter Juggler rate. The one-step gain is
real, but its repeated use introduces mixed-sign trajectories; actual
fixed-sign joint deficits already occur at depth two. The best next
question is whether Juggler's actual floor realizations constrain the
distribution of the common code at growing depth strongly enough for the
existing pressure bound. That question is not answered or opened anew here.

## Publication assessment

Status: **STRUCTURAL**. An exact obstruction and reusable finite-period
sum, not a new termination theorem or an independent paper proposal.
