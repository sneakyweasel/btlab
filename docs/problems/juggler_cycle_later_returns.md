# A third boundary transfer and the limit of uniform floor-error bounds

Status: **PROMOTE** the scoped third-transfer theorem.
Authorized continuation begun 9 September 2026; completed 10 September 2026.

For every actual Juggler cycle with minimum \(m\ge2^{128}\) and
maximum \(M<m^3\), the following argument proves
\[
\boxed{M<m^3-\frac12m^{127/64}.}
\]
The sharper consolidated exponent is
\[
\theta=\frac{381}{128}-\frac{3^{41}}{2^{65}}
       \approx1.9879599522703875>\frac{127}{64}.
\]
The stronger restriction requires a much larger minimum than the
preceding \(253/128\) result, which applies from \(2^{24}\).
Neither result excludes the whole cubic region or taller cycles.
The canonical written proof is now in [Paper A](../theory/juggler_finite_dynamics_note.md),
Sections 3.12–3.13 and Appendix F. This dossier retains the research
gate, fixed controls and decision; it is not a second editable proof source.

## Problem

Determine whether paired floor-error estimates survive later Euclidean
return words and the terminal step of a complete periodic set.

## Exact statement

Let \(O(x)=\lfloor x^{3/2}\rfloor\), \(E(x)=\lfloor x^{1/2}\rfloor\).
Word composition is chronological. Put
\[
A=OOE,\quad B=OE,\quad C=A^2B,\quad D=AC^2,\quad
W=D^3C,\quad V=D^4C.
\]
Their relevant ideal exponents are
\[
\alpha=\frac98,\quad \gamma=\frac{243}{256},\quad
\delta=\frac{531441}{524288},\quad
\rho=\delta^3\gamma=\frac{3^{41}}{2^{65}}<1,\quad
\eta=\delta^4\gamma=\frac{3^{53}}{2^{84}}>1.
\]
The words \(W,V\) have lengths \(65,84\), respectively.

**Theorem LR (third boundary transfer).** Suppose an actual Juggler
cycle has minimum \(m\ge2^{128}\) and maximum \(M<m^3\).
Use the retained odd section and original seam from Theorem DC:
\[
Y=\{y_0<\cdots<y_{a+b-1}\},\quad y_0=m,\quad
t=\max Y=E(M),\quad w=B(t),\quad z=A(m),\quad d_0=z-w.
\]
Then, in addition to \(a=2b+r,\ b=2r+s,\ 0<s<r\),
\[
r=3s+u,\qquad 0<u<s.
\tag{LR1}
\]
There is a third genuine right boundary transfer, now through \(W\).
With
\[
\sigma=\frac{13}{128}+1-\rho\in\left(\frac7{64},\frac18\right),
\]
the original seam satisfies
\[
d_0\ge8,\qquad d_0>\frac25m^\sigma>\frac25m^{7/64}.
\tag{LR2}
\]
Consequently
\[
t^3+2\le[(z-8)(z-6)]^2,
\qquad M<m^3-\frac12m^\theta,
\quad \theta=\frac{15}{8}+\sigma.
\tag{LR3}
\]
In particular \(M<m^3-\frac12m^{127/64}\). The clean corollary,
under \(M<m^3\), has the equivalent integer form
\[
m^{127}<\bigl[2(m^3-M)\bigr]^{64}.
\]

The word estimate supporting the third transfer is unconditional:
for integers \(x\ge2^{128}\),
\[
0\le x^\rho-W(x)<\frac65.
\tag{LR4}
\]
For integers \(z>w\ge2^{128}\) with \(d=z-w\ge2\),
\[
0\le W(z)-W(w)<\rho w^{\rho-1}d+\frac65<d.
\tag{LR5}
\]
Its use on a cycle still requires the complete genuine return towers.

## Current literature

**PROJECT-SPECIFIC internal extension; no external priority claim.**
The prerequisites are [Paper A](../theory/juggler_finite_dynamics_note.md),
the [exact Euclidean induction dossier](juggler_cycle_cubic_induction.md),
and [Theorem DC](juggler_cycle_direction_change.md).
The general error calculation uses the exact transported-loss identity
already recorded there. The new contribution is the forced next batch,
its quantitative 65-letter estimate, and the third-transfer consequence.
No external theorem or heuristic parity law is used.

## Branch budget

- **Target:** extend useful paired error control to later words and determine
  what is still needed at the terminal return.
- **Novelty hypothesis:** common periodic placement preserves distinct odd
  endpoints while a new word-specific floor bound controls their gap.
- **Falsifier:** accumulating errors defeat the estimate, a transfer repeats
  an old seam, or the terminal step removes the required pair.
- **Already killed by?:** the negative-knowledge entry on Euclidean induction
  rules out discarding guards; local cell and defect identities alone are
  insufficient. A new quantified cycle restriction is required.
- **Existing machinery:** exact square remainders, return towers, the two
  proved \(C\) transfers, and the seven archived threshold cycles.
- **Maximum Phase-0 scope:** symbolic later-word estimates and terminal
  cases; no orbit census, source search, rank-pair scan, or floor increase.
- **Promotion criterion:** a new proved cycle restriction after a later
  change of direction, or a precise new obstruction to the proposed estimate.
- **Stop criterion:** do not infer uniform contraction or a terminal
  contradiction from finitely many surviving transfers.

Post-proof verification, specified before implementation: exact rational
constants and prefix products for the fixed words above; replay only the
seven archived cycles; one conditional integer ceiling at \(2^{128}+1\).
That last input is an arithmetic evaluation, not an orbit or cycle.

## Balanced-ternary formulation

All word cells, ranks, gaps and the clean polynomial certificate are exact
integer relations and can be represented in balanced ternary.

## Why BT may be relevant

No representation advantage is used or claimed.

## Candidate operations / invariants

The relevant quantities are the positive even seam gap, the transported
absolute floor loss, and the ideal exponent invariant of the return
permutation. Their different roles must be kept separate at termination.

The repository tag **EXACT — HUMAN PROOF** denotes its written-proof tier.
The present arguments were developed and cross-checked with AI assistance.
The tag does not claim independent human review or Lean verification.

## Experiments

The [bounded verifier](../../src/research/juggler_sequence/cycle_later_returns.py)
and [tests](../../tests/research/juggler_sequence/test_cycle_later_returns.py)
produce the [fixed record](../../data/research/juggler/cycle_later_returns/summary.json):

    python -m research.juggler_sequence.cycle_later_returns

The conditional integer ceiling uses the least even \(G\ge8\) satisfying
\[
(5G)^{64}>2^{64}m^7.
\]
Then (LR2) implies \(d_0\ge G\). Let \(z_*\) be the greatest odd integer
with \(z_*^8\le m^9\), and let \(T\) be the greatest positive odd integer
satisfying
\[
T^3+2\le[(z_*-G)(z_*-G+2)]^2.
\]
It follows that \(M\le(T+1)^2-2\). The numerical record checks the clean
\(127/64\) corollary and the preceding ceiling at the one declared input.
It does not numerically evaluate the enormous denominator in the sharper
exponent \(\theta\), or assert that any input is periodic.

## Conjectures

No new conjecture file is opened. Universal wrong-parity forcing and
global no-cycle remain open.

## Counterexamples

No actual large guarded cycle, or counterexample to strict contraction
of every possible later word, is claimed.

The obstruction below is a failure of a specified error certificate,
not proof that the actual maps fail to contract. The archived cycles
only illustrate rank and terminal identities; all have parity failures
and lie below the large-minimum hypotheses.

## Formalization

The registered Lean implementation and its exact hypotheses are recorded in
[Paper A's formalization map](../theory/juggler_finite_dynamics_formalization.md).
Appendix A identifies the audited declarations statement by statement.
A formal helper with an explicit transfer hypothesis is not, by itself,
an unconditional cycle theorem. The release audit records the final scope.

## Results

The complete written proof is consolidated in [Paper A](../theory/juggler_finite_dynamics_note.md),
Sections 3.12–3.13 and Appendix F.1–F.6. Theorem 3.40 states both height restrictions with
their different lower cutoffs. Proposition 3.41 isolates the terminal
mixed passage and its still-uncontrolled common prefix.

The exact statements above summarize this gate's contribution. The
archived probe and data remain bounded consistency controls. Any later
proof correction belongs in the canonical manuscript and must be
propagated to the formalization map and ledger as appropriate.

## Open questions

The new bound applies only when \(m\ge2^{128}\), about \(3.4\cdot10^{38}\).
The earlier \(253/128\) theorem remains the applicable result from
\(2^{24}\). At the new cutoff the clean strip is at least twice as
wide as the earlier strip, but it still occupies only a portion near
the top of the cubic region.

Uniform exact paired contraction, the terminal absolute-loss
calibration or equivalent prefix/suffix gap comparison, the rest
of the cubic region, and every taller cycle
remain open. No descent floor or period bound is increased.

## Decision

**PROMOTE** the third-transfer theorem and record the precise limitation
of the one-sided error certificate. The later-word estimate yields a
new cycle restriction, but continuing these estimates at a fixed
minimum cannot justify uniform contraction or remove the terminal
mixed-word requirement.

The one best next question is: **can the shared absolute cells bound
amplification through the terminal prefix \(P\) tightly enough that
the mixed \(OE/EO\) passage and common suffix \(Q\) force a net gap
decrease?** An answer must improve on the closure identity and
existing finance bounds; merely renaming the terminal closure or ideal-product identities would be
a closed reformulation. This gate does not automatically open
another branch.

## Publication assessment

Status: **STRUCTURAL**. The written results are consolidated in Paper A.
Its formalization map and cited-declaration audit specify the Lean scope.
AI-assisted cross-checks are not independent human review. The local
revision does not alter the published Zenodo record. The descent floor
\(350000000\), period bound \(780239\), and unresolved global no-cycle
question are unchanged.
