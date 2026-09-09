# Two boundary transfers strengthen the cubic-height exclusion

Status: **PROMOTE** the scoped two-transfer theorem.
Authorized continuation, 9 September 2026.

For an actual Juggler cycle with minimum \(m\ge2^{24}\) and maximum
\(M<m^3\), the argument below gives
\[
\boxed{M<m^3-\frac12m^{253/128}.}
\]
The exponent \(253/128\) improves the earlier \(15/8=240/128\).
This is a written research result, not a global no-cycle theorem.
The canonical written proof is now in [Paper A](../theory/juggler_finite_dynamics_note.md),
Section 3.12 and Appendix F. This dossier retains the research gate,
fixed controls and decision; it is not a second editable proof source.

## Problem

Propagate the exact parity gap at the first genuine change of direction
in the Euclidean induction of a complete cubic-band periodic set.
Consecutive left steps reuse the same boundary pair, so they cannot
be counted as independent parity gains.

## Exact statement

Write \(O(x)=\operatorname{isqrt}(x^3)\), \(E(x)=\operatorname{isqrt}(x)\),
and use chronological word composition. Put
\[
A=OOE,\quad B=OE,\quad C=A^2B=OOEOOEOE,\quad D=AC^2,
\qquad \gamma=\frac{243}{256}.
\]
The same symbols denote the prescribed word maps where unambiguous.

**Theorem DC (two boundary transfers).** Suppose an actual Juggler cycle
has minimum \(m\ge2^{24}=16777216\) and maximum \(M<m^3\).
Let
\[
Y=\mathcal C\cap[m,O(m)),\quad t=\max Y=E(M),\quad
z=A(m),\quad w=B(t),\quad d_0=z-w.
\]
Then the first maximal left and right Euclidean batches each have
quotient \(2\), with nonzero remainders. Both applications of \(C\)
to the boundary pair are genuine cycle returns. In particular,
\[
d_0\ge6,\qquad
d_0>\frac{26240}{59049}m^{13/128},
\tag{DC1}
\]
\[
t^3+2\le[(z-6)(z-4)]^2,\qquad M+2\le(t+1)^2,
\tag{DC2}
\]
and
\[
M<m^3-\frac12m^{253/128}.
\tag{DC3}
\]
The equivalent integer form of (DC3), under \(M<m^3\), is
\[
m^{253}<\bigl[2(m^3-M)\bigr]^{128}.
\]

The local contraction used in the proof does not require parity guards:
for integers \(z>w\ge2^{24}\), with \(d=z-w\ge2\),
\[
0\le C(z)-C(w)
 <\gamma w^{-13/256}d+\frac98<d.
\tag{DC4}
\]
For two actual returns with odd inputs and distinct odd outputs,
this implies a decrease of at least two in their even gap.

## Current literature

**PROJECT-SPECIFIC internal extension; external priority is not claimed.**
[Paper A](../theory/juggler_finite_dynamics_note.md), Section 3.11 and
Appendix E, supplies the normalized retained set, exact initial seam,
short return cells, and floor-loss identity.
The [periodic-carry dossier](juggler_cycle_periodic_carries.md) records
the preceding height theorem. The
[Euclidean-induction dossier](juggler_cycle_cubic_induction.md) records
the rank substitutions and full guard transport.
No new external theorem or empirical parity law is used.

## Branch budget

Mathematical target: Can an exact boundary transfer across the first
Euclidean direction change give a cycle restriction beyond the existing
floor cells and one-boundary height theorem?

Novelty hypothesis: The images of the two inputs remain distinct members
of the same odd periodic set, whereas isolated prescribed blocks may merge.

Falsifier: The resulting bound is an existing cell identity, repeated
counting of the same gap, or a smooth contraction defeated by an
uncontrolled difference of floor errors.

Already killed by?: Fixed-residue guard summaries, omitted intermediate
parities, and endpoint-only cycle criteria are already insufficient.
The present proof retains all actual-cycle guards and uses a quantitative
error smaller than the discrete two-unit separation.

Existing machinery: Exact \(OE/OOE\) cells, finite rank first returns,
the normalized periodic seam, and the seven archived threshold cycles.

Maximum Phase-0 scope: Symbolic \(OOEOOEOE\) error and seam analysis,
the first and following induction directions, and the seven literal
archived threshold cycles. No source census, trajectory extension,
new descent floor, or period search.

Promotion criterion: A proved new cycle-specific inequality that survives
the required direction change and all terminal cases.

Stop criterion: Retain a precise reduction or obstruction if no such
inequality survives; do not infer arbitrary-depth propagation.

Post-proof verification scope, fixed before implementation: the same
seven cycles, exact rational constants in this proof, and conditional
ceiling evaluations at the two previously used large minima
\(214358889\) and \(10828567056280809\). These evaluations do not run
trajectories or assert that cycles exist.

## Balanced-ternary formulation

All branch cells, ranks, gaps and polynomial ceiling certificates are
integer relations and may be represented in balanced ternary.

## Why BT may be relevant

No representation advantage is used or claimed in this argument.

## Candidate operations / invariants

The useful quantity is the positive even distance between two neighboring
retained cycle states. The exact \(C\)-map contracts that distance on the
stated domain while its two images remain distinct in the same odd set.
Floor errors are bounded as real nonnegative quantities before parity
is applied; no residue approximation replaces an intermediate state.

The repository label is **EXACT — HUMAN PROOF**, its written-proof tier.
These arguments were developed and cross-checked with AI assistance.
That label does not claim independent human review or Lean verification.

## Experiments

The [bounded verifier](../../src/research/juggler_sequence/cycle_direction_change.py)
and [tests](../../tests/research/juggler_sequence/test_cycle_direction_change.py)
check only the fixed scope above. The generated
[record](../../data/research/juggler/cycle_direction_change/summary.json)
certifies each archived block by adjacent square cells, checks complete
return towers, and preserves every original parity mismatch.

    python -m research.juggler_sequence.cycle_direction_change

The conditional integer ceiling uses the least even \(G\ge6\) for which
\[
(59049G)^{128}>26240^{128}m^{13}.
\]
Thus (DC1) implies \(d_0\ge G\). Let \(z\) be the greatest odd integer
with \(z^8\le m^9\), and let \(T\) be the greatest positive odd integer
satisfying
\[
T^3+2\le[(z-G)(z-G+2)]^2.
\]
Then \(M\le(T+1)^2-2\). The verifier checks the corresponding integer
form of (DC3), with positive cube gap. It does not apply this ceiling
below \(2^{24}\).

## Conjectures

No new conjecture file is opened. Uniform propagation through all later
induced words, the remaining cubic region, and taller cycles stay open.

## Counterexamples

The archived \(S_9\) example is outside the large-minimum hypothesis.
At its final two-base stage, \(A(9)=11\) and \(C(11)=9\).
The second block fails the \(O\)-source guards at \(36,14,52\).
Although \(C(9)=7\), that computation is not another threshold return
in this stage: its last \(E\) is applied at \(52<9^2\). It must not
be used as a pair of genuine cycle returns.

The example also illustrates the terminal obstruction: a two-point
return can close using different branch words, without either word
fixing both points. No positive two-point gap is asserted to survive
the final one-point induction.

## Formalization

The registered Lean implementation and its exact hypotheses are recorded in
[Paper A's formalization map](../theory/juggler_finite_dynamics_formalization.md).
Appendix A identifies the audited declarations statement by statement.
A formal helper with an explicit transfer hypothesis is not, by itself,
an unconditional cycle theorem. The release audit records the final scope.

## Results

The complete written proof is consolidated in [Paper A](../theory/juggler_finite_dynamics_note.md),
Sections 3.12 and Appendix F.1, F.2, F.4. Theorem 3.40 states both height restrictions with
their different lower cutoffs. Proposition 3.41 isolates the terminal
mixed passage and its still-uncontrolled common prefix.

The exact statements above summarize this gate's contribution. The
archived probe and data remain bounded consistency controls. Any later
proof correction belongs in the canonical manuscript and must be
propagated to the formalization map and ledger as appropriate.

## Open questions

The remaining region \(M<m^3-\frac12m^{253/128}\), and every taller
cycle with \(M\ge m^3\), are unexcluded. No period bound is increased.
The new strip is wider than the preceding one by the factor
\((1/2)m^{13/128}>2\) throughout \(m\ge2^{24}\), but is still a
proper portion of the cubic band.

## Decision

**PROMOTE** the unconditional short-word gap contraction, the forced
first two batches, and the resulting cycle-specific height restriction.
The wider exclusion uses two genuine transfers and is not repeated
counting of one boundary or an assumption that smooth contraction
survives floors.

The one best next question is: **can the later contracting return
words satisfy a paired floor-error estimate that remains useful as
their ideal exponent approaches one, while accounting for the terminal
mixed-branch boundary?** No automatic continuation or larger scan is
authorized by this decision.

## Publication assessment

Status: **STRUCTURAL**. The written results are consolidated in Paper A.
Its formalization map and cited-declaration audit specify the Lean scope.
AI-assisted cross-checks are not independent human review. The local
revision does not alter the published Zenodo record. The descent floor
\(350000000\), period bound \(780239\), and unresolved global no-cycle
question are unchanged.
