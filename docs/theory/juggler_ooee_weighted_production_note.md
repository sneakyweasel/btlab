# Actual OOEE production and unconditional contagion at 5/8

22 September 2026. Kernel-checked completion of the retained OOEE
production argument. Advisory statement coverage and independent
mathematical review remain pending.

## Exact statement

Use the actual OOEE guard, conserved weight, sourceMass, fullMass and
cutoff(t)=floor(exp(t)) of FateOOEEAssembly. There is a single constant
C>=0 such that for every backward-closed predicate A and every real t,

\[
 \frac{11}{100}\operatorname{fullMass}_A(9t/16-4)
 \le\operatorname{sourceMass}_{A,OOEE}(\lfloor e^t\rfloor)+C.
\]

Thus OOEEProductionBound holds without an additional analytic hypothesis.
For every such A containing a positive integer, there exist K>0 and N
such that for every X>=N,

\[
 \sum_{\substack{1\le n\le X\\A(n)}}\frac1n\ge K(\log X)^{5/8}.
\]

Consequently, if for some e>3/8 the actual odd nonterminating starts in
every sufficiently large block (y,2y] number at most y*(log y)^(-e),
every positive start reaches one. The existing cumulative stopped-pressure
bound also suffices at r-eta>3/8, with the certified target interval and
all pressure parameters unchanged. Both rate hypotheses remain open.

## Count-to-weight proof

Fix eta=1/10000. For m>=10^9, put S=m^(7/9) and P=m*S.
The established geometry gives S>=10000, candidate count H with
abs(H-(8/9)*S)<=3, and every source n in the actual fibre F_m satisfies
P<=n<=P+3S. Outside CountPoor eta, the normalized count differs from
1/8 by less than eta. Therefore

\[
 H\ge\frac{887}{1000}S,\qquad
 \#F_m\ge\frac{1107}{10000}S,\qquad
 \sum_{n\in F_m}\frac1n\ge\frac{\#F_m}{P+3S}\ge\frac{11}{100m}.
\]

The threshold 10^9 is an analytic size condition, not a computational
verification floor. No additional seeds were checked.

The [count-poor tail](juggler_ooee_count_poor_tail_note.md) provides D>0
and M such that poor targets above U have reciprocal mass at most
D*U^(-7/9), uniformly in the finite upper cutoff, for U>=M. Choose
U=max(M,10^9). Discarding targets up to U and the poor targets costs at
most B=logMass(True,U)+D*U^(-7/9), independently of A.

For accepted targets m<=floor(exp(9t/16-4)), the exact source bound
gives n<=2*m^(16/9)<=2*exp(t-64/9)<=exp(t). Thus every source lies
below floor(exp(t)). Backward closure places it in A; distinct fibres
are disjoint because their fourth iterates differ. Summing gives
reciprocal production with loss B. The proved uniform comparison
abs(mass(A,N)-2*logMass(A,N))<=6 gives conserved-weight production
with loss C=2B+8.

The existing three-production assembly now applies without an odd-production
hypothesis. Its exact exponent certificate gives 5/8; its conditional
Tao and scale-average reductions give the threshold 3/8.

## Proof map and validation

[FateOOEEWeighted.lean](../../formal/Problems/Juggler/FateOOEEWeighted.lean)
proves all count-to-weight, cutoff, exceptional-mass and disjoint-source
steps. `ooee_production_uniform` has one constant for every backward-closed
A and every real t. `ooee_production` supplies the existing interface;
`logMass_growth` is unconditional for every nonempty positive
backward-closed class. `conjecture_of_tao_rate` and
`pressure_average_conjecture` retain exactly their rate inputs.

The full Lean build passes 9,089 jobs. The complete
[dependency audit](../../formal/AxiomCheckOOEEWeighted.lean) checks all
11 new theorems, with only propext, Classical.choice and Quot.sound.
Ledger rendering and branch-index consistency pass. The targeted run
passes 274 tests and skips 15; its sole failure was a Paper C provenance
gate after an edit to the frozen written contagion note. Restoring that
publication input resolves the gate. The exact failed test and documentation
links both pass on rerun, yielding 275 passing selected tests and 15 skips
with no unresolved failures. The new result is recorded in this follow-up;
the frozen manuscript inputs are preserved. Paper E's registry-only refresh
passes without changing its manuscript, PDF, TeX or metadata.

## Decision

**PROMOTE.** The actual OOEE production and unconditional 5/8 contagion
are proved in Lean. The next mathematical obstruction is the actual
stopped pressure or failure-rate estimate at growing depth. This phase
does not prove termination, an infinite escape trajectory, or any new
cycle exclusion, and does not open a longer-fibre attack.
