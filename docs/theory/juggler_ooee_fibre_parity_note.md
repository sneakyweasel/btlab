# Exact OOEE fibres and their nonresonant parity count

22 September 2026. The two Lean modules below discharge the exact
source-window geometry required by the joint-parity estimate. Advisory
statement coverage is pending. The result is a count theorem; the
weighted poor-fibre tail and OOEE production remain separate obligations.

## Exact inverse geometry

Write O(n)=isqrt(n^3), Q(n)=isqrt(n), and define

\[
 I(a)=\lceil a^{2/3}\rceil,\qquad L_m=I(I(m^4)),\qquad
 P_m=m^{16/9},\qquad S_m=m^{7/9}.
\]

[OOEEFibreGeometry.lean](../../formal/Problems/Juggler/OOEEFibreGeometry.lean)
proves the adjunction I(a)<=n if and only if a<=O(n). Applying it twice
and using the exact square-root cells gives

\[
 Q^2(O^2(n))=m\quad\Longleftrightarrow\quad L_m\le n<L_{m+1}.
\]

The odd candidates are exactly a_m+2j for 0<=j<H_m, where
a_m=2*floor(L_m/2)+1 and H_m=floor(L_(m+1)/2)-floor(L_m/2).
Filtering these candidates by the actual OOEE guard gives precisely
the integers with that itinerary and fourth iterate m. Every parity
and integer boundary is included.

For m>=1 the module proves

\[
 P_m\le L_m\le P_m+2,\qquad
 \left|H_m-\frac89 S_m\right|\le3.
\]

The first bound uses concavity of the inverse power and both ceiling
errors. Convexity bounds P_(m+1)-P_m between (16/9)S_m and
(16/9)S_m+2. Rounding the odd count then gives the displayed constant.
For m>=64,

\[
 S_m/2\le H_m\le3S_m,\qquad
 P_m\le n\le2P_m,\qquad n\le P_m+3S_m
\]

for every candidate n. In particular H_m is positive. The threshold 64
is a geometry bound, not a change to the verified stopping floor.

## Applying the proved parity theorem

Let F_m be the exact guarded fibre above, and A_H=1+2*harmonic(H).
[OOEEFibreParity.lean](../../formal/Problems/Juggler/OOEEFibreParity.lean)
proves: for every integer H>=3 there exist B>0 and a natural M0>=64,
independent of C, such that for every m>=M0 and C>0 with C>=(27/32)H,
if

\[
 C m^{-7/9}\le\left|k\frac98m^{2/9}-z\right|
 \qquad(0<|k|\le H,\ k,z\in\mathbb Z),
\]

then

\[
 \left|\frac{|F_m|}{H_m}-\frac18\right|
 \le \frac{15}{\sqrt{H+1}}+(A_H^3+6A_H)
 \left(2B m^{-1/18}+\frac4C+
              18\pi Hm^{-2/3}+2m^{-7/9}\right). \tag{1}
\]

The unnormalized version retains numerator
B*m^(13/18)+(2/C)*m^(7/9)+9*pi*H*m^(1/9)+1, divided by H_m.
The proof substitutes P=P_m and D=3 in the
[joint-parity theorem](juggler_ooee_joint_parity_note.md), supplies all
window hypotheses from the exact geometry, and uses H_m>=S_m/2.
There is no cancellation or interval-geometry premise beyond the
displayed nonresonance condition.

Equation (1) retains the needed order of choices: H first, C second,
then m large. Its three target-dependent terms vanish. This supports
the next fixed-deficit argument, but that quantified inclusion, the
count of resonant targets, conversion from counts to conserved weight,
and physical production cutoffs are not claimed by these modules.

## Verification and decision

Both modules compile. The
[dependency audit](../../formal/AxiomCheckOOEEFibre.lean) covers all 26
new theorems, each using only propext, Classical.choice and Quot.sound.
The full live Lean build passes 9,085 jobs, including the concurrent OOE
return module. The initial live repository run passes 173 tests with
15 skips and five failures: stale theorem indexing, concurrent Paper E
release/mirror changes, and the concurrent OOE ledger row's missing trust
field. The local theorem artifacts were subsequently regenerated; both
the live module-attribution and documentation-link checks then passed.

A snapshot of committed source 25619904 plus this phase passes all 106
selected theorem-index, ledger, layer, branch-index and Paper E release
tests. Its archive refresh changes only the registry input hash and
deterministic source archive; manuscript, PDF, TeX and metadata bytes are
unchanged. This scoped validation excludes the concurrent OOE publication
edits and is not a claim that every live publication gate passes.

**PROMOTE** the exact fibre count estimate. The unconditional Lean
contagion exponent is still 100/203; the 5/8 implication retains
OOEEProductionBound. The actual growing-depth pressure bound and
universal termination remain open.
