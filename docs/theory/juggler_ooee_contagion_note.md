# Three actual productions: contagion at 5/8

22 September 2026. **EXACT — HUMAN PROOF** for the complete mathematical
implication, using the new AI-assisted
[OOEE poor-fibre theorem](juggler_ooee_poor_fibre_tail_note.md).
Independent review of that analytic input is outstanding.
The assembly is kernel-checked in
[FateOOEEAssembly.lean](../../formal/Problems/Juggler/FateOOEEAssembly.lean),
with its two precise odd-production inequalities retained as hypotheses.
The follow-up [FateOEWeighted.lean](../../formal/Problems/Juggler/FateOEWeighted.lean)
now discharges OE, leaving only the OOEE production input in the strengthened
formal implication. The new OOEE analytic theorem is still not proved in Lean.

## 1. Consequences

Let A be a set of positive integers closed under actual Juggler preimages,
with at least one positive member. Then there exist K>0 and X_0 such that

\[
 \sum_{n\le X,\ n\in A}\frac1n\ge K(\log X)^{5/8}
                           \qquad(X\ge X_0).
 \tag{1}
\]

This is a written improvement over the fully kernel-checked exponent
100/203. It inherits the analytic review boundary of the OOEE theorem.
The corresponding Tao-type sufficient condition is now: if, for some e>3/8,
the number of odd failures in every sufficiently large dyadic interval
(y,2y] is at most y*(log y)^(-e), then every positive integer reaches 1.
The failure-rate bound remains open; (1) proves no termination theorem.

## 2. Actual source sets and their weights

Use the positive weight

\[
 w(n)=\log\frac{a(n)+1}{a(n)-1},\qquad a(n)=n+(n\bmod2),
 \quad \mu_A(X)=\sum_{1\le n\le X,\ n\in A}w(n),
 \quad F_A(t)=\mu_A(\lfloor e^t\rfloor).
\]

The coarse comparison is kernel-checked in `weight_reciprocal_bounds`:

\[
 1/n\le w(n)\le4/n\quad(n\ge1),\qquad
 \sum_{n\le X,\ n\in A}1/n\le\mu_A(X)
                    \le4\sum_{n\le X,\ n\in A}1/n.
 \tag{2}
\]

It uses the elementary logarithm bounds, not an assumed asymptotic.
Let S_E(A,t), S_OE(A,t), S_OOEE(A,t) be the w-masses of members n of A
with n<=floor(exp(t)) and those actual initial parity words. These three
source sets are pairwise disjoint: E starts even; the two odd sources
have opposite second letters. Consequently

\[
 S_E(A,t)+S_{OE}(A,t)+S_{OOEE}(A,t)\le F_A(t).
 \tag{3}
\]

No further continuation of a source is constrained. In particular,
OOEE is not a restriction to terminating sources. `source_partition`
proves (3) directly with the actual `floorPower` guards.

## 3. Matching the analytic inputs to physical cutoffs

The following two inequalities are exactly `OddProductionBounds A`:
there exist C>=0 and T such that, for all t>=T,

\[
 \frac{33}{100}F_A(3t/4-4)\le S_{OE}(A,t)+C,\qquad
 \frac{11}{100}F_A(9t/16-4)\le S_{OOEE}(A,t)+C.
 \tag{4}
\]

Both are actual source-height statements. We justify each component
of their written derivation here; (4) is not silently discharged in Lean.

### 3.1 OE mass

The kernel-checked [OE poor-fibre theorem](juggler_oe_poor_fiber_tail_note.md)
states that, for each fixed epsilon>0, the targets whose even-image share
sigma_m is below 1/2-epsilon have finite reciprocal mass. The number of
odd candidates is (2/3)m^(1/3)+O(1), and their sources lie in
[m^(4/3),(m+1)^(4/3)). On this interval, w(n)=2m^(-4/3) times
1+O(1/m), while w(m)=2/m times 1+O(1/m). Thus the actual OE fibre mass,
divided by w(m), is

\[
 (2/3)\sigma_m+O(m^{-1/3}).
\]

Choose a fixed sufficiently small epsilon, then discard a finite initial
set so this ratio is at least 33/100 outside the poor set. The discarded
target w-mass is finite by (2). For every target subset B and cutoff Y,

\[
 \sum_{m\in B,\ m\le Y} W^{OE}_m
       \ge (33/100)\mu_B(Y)-C_1,
 \tag{5}
\]

where C_1 is independent of B and Y. The original OE poor-share theorem
is already Lean verified. Section 7 now supplies a fully formal weighted
conversion with physical source cutoffs, using a uniform finite error
instead of requiring an asymptotic weight estimate as an input.

### 3.2 OOEE mass

Apply the new OOEE theorem with eta=1/900, so 1/9-eta=11/100.
Its arbitrary-target consequence gives

\[
 \sum_{m\in B,\ m\le Y} W^{OOEE}_m
       \ge (11/100)\mu_B(Y)-C_2,
 \tag{6}
\]

uniformly in B and Y. The four actual parity guards remain in the fibres.
This step inherits the written analytic proof and its review boundary.

### 3.3 Source height

For positive parent m, any actual E predecessor n satisfies
n<(m+1)^2. Any actual OE predecessor satisfies n^3<(m+1)^4:
put v=O(n); then v+1<=(m+1)^2 and n^3<(v+1)^2.
For an actual OOEE predecessor, put v=O^2(n). The kernel-checked
`OddPredecessorTransport.two_step_scale` gives

\[
 n^9<64(v+1)^4\le64(m+1)^{16}.
 \tag{7}
\]

Here Q^2(v)=m implies v+1<=(m+1)^4, with no smoothed composition.
Since m+1<=2m for m>=1, the common conservative target cutoff
m<=exp(r*t-4) has the following consequences:

| Word | r | Bound implied for the source |
|---|---:|---|
| E | 1/2 | n<4 exp(t-8)<exp(t) |
| OE | 3/4 | n^3<16 exp(3t-16)<exp(3t) |
| OOEE | 9/16 | n^9<2^22 exp(9t-64)<exp(9t) |

The strict numerical inequalities follow already from exp(1)>2.
Taking floors therefore puts every such integer source below floor(exp(t)).
Backward closure puts it in A when its parent is in A. Distinct parents
have disjoint fibres, because the parent is the actual second or fourth
iterate. Use B=A and the indicated target cutoff in (5)--(6), and take
C=max(0,C_1,C_2). This proves precisely (4).

For E, exact fibre conservation additionally gives

\[
 F_A(t/2-4)\le S_E(A,t)\qquad(t\ge8).
 \tag{8}
\]

This part, including the integer square-root boundary, is fully formal:
`even_cutoff_bound` proves that the accepted parent cutoff is at most
sqrt(floor(exp(t)))-1; `even_source_lower` then uses the existing exact
even-fibre mass law. Partial top fibres are dropped with nonnegative mass.

## 4. Removing the shifts and additive loss

Equations (3), (4), and (8) give, eventually,

\[
 F_A(t)\ge F_A(t/2-4)+(33/100)F_A(3t/4-4)
                   +(11/100)F_A(9t/16-4)-2C.
 \tag{9}
\]

Define G(t)=F_A(t-16)-5C. For each r in {1/2,3/4,9/16},
r*t-16<=r*(t-16)-4. Monotonicity of F_A, (9), and
the coefficient sum 1+33/100+11/100=36/25 give

\[
 G(t)\ge G(t/2)+(33/100)G(3t/4)+(11/100)G(9t/16)
 \tag{10}
\]

for all sufficiently large t: the remaining constant is
5C*(36/25-1)-2C=C/5>=0. This is `shifted_recurrence`.
It avoids silently dropping a constant error or replacing a shifted
cutoff by a larger one. The previously established unconditional
contagion at any exponent up to 100/203 and (2) show F_A(t) tends to
infinity. Hence G has a positive seed on an entire sufficiently late
initial interval. This argument is kernel-checked in `mass_exists_ge`
and `fullMass_eventually_ge`.

## 5. The exact exponent certificate

At lambda=5/8, the three rational lower bounds

\[
 (1/2)^{5/8}\ge648/1000,\quad
 (3/4)^{5/8}\ge835/1000,\quad
 (9/16)^{5/8}\ge697/1000
\]

are checked by taking eighth powers and comparing exact rationals.
Consequently

\[
 2^{-5/8}+\frac{33}{100}(3/4)^{5/8}
       +\frac{11}{100}(9/16)^{5/8}
 \ge\frac{50011}{50000}>1.
 \tag{11}
\]

`certificate_five_eighths` verifies these comparisons. Apply the existing
generic `recursion_lemma` to (10), with zero errors and the positive seed.
It gives G(t)>=K*t^(5/8), hence F_A(t)>=K*t^(5/8). Evaluate at t=log X
and use (2) to prove (1). These steps are `fullMass_growth` and
`logMass_growth`, with (4) retained as the sole additional production input.

The limiting formal equation with coefficients 1,1/3,1/9 has root
approximately 0.6327671418. That decimal is diagnostic, not the exact
certificate used here. This note asserts the rational exponent 5/8.

## 6. Tao implication and trust boundary

The existing `tao_rate_implies_conjecture` needs a failure-class log-mass
lower bound at lambda and a dyadic odd-failure rate e>1-lambda.
Substituting (1) gives e>3/8. The new
`FateOOEEAssembly.conjecture_of_tao_rate` checks this implication in Lean,
with `OddProductionBounds` for the failure set and the actual failure-rate
estimate both explicit. It establishes neither input by declaration.

The unconditional written bound (1) has the following proof chain:
the old OE theorem, its weighted conversion, the new written OOEE theorem,
the physical source-cutoff argument, and the kernel-checked assembly.
The conditional Lean theorem covers the assembly from precisely (4).
No result is labelled an unconditional Lean proof at 5/8.

No published manuscript, verification floor, or cycle bound is changed.
The OE input is discharged in the follow-up below. The remaining
production obligation is formalizing the actual OOEE poor-fibre theorem
and its source-cutoff consequence.
Growing-depth stopped pressure and the required Tao rate remain open.

## 7. OE is now unconditional in the conserved weight

The follow-up module `FateOEWeighted.lean` proves, for every predicate A
and natural cutoff N,

\[
 \left|\mu_A(N)-2\sum_{1\le n\le N,\ n\in A}\frac1n\right|\le6.
 \tag{12}
\]

This is an exact finite statement, uniform over all target or source sets.
The paired weight satisfies 2/a(n)<=w(n)<=2/(a(n)-1). Using
n<=a(n)<=n+1, and handling n=1 separately, gives

\[
 |w(n)-2/n|\le6\left(\frac1n-\frac1{n+1}\right)\qquad(n\ge1).
\]

The majorant telescopes to 6*(1-1/(N+1)); positivity lets any subset use
the same bound. These are `weight_reciprocal_error`,
`reciprocal_telescoping`, and `mass_reciprocal_error`.

To use the existing OE tail theorem directly, fix eta=1/1000 and
U=10^36. `base_parameters` checks its hypotheses by the rational
certificate U^(1/3)>=10^12. This U is an analytic cutoff chosen to absorb
a finite initial mass; it is not a computed verification floor and
does not change N_0. Put

\[
 C_0=\sum_{1\le m\le U}\frac1m+
              \frac{2100\,\operatorname{eps}(U)}{\eta^2}.
\]

Outside m<=U and the existing `Poor eta` set, every OE fibre has
reciprocal source mass at least (33/100)/m. This follows from the proved
`nonpoor_fiber_logMass_ge`: eps(m)<=1/1000 and
(2/3)*(1/2-1/1000)-1/1000>33/100. The discarded reciprocal target mass
is at most C_0, independently of A and the target cutoff.

The accepted fibres are disjoint. For a backward-closed A they consist
of members of A satisfying the actual OE guard. `oe_fibre_cutoff` proves
that m<=floor(exp(3t/4-4)) puts every source below floor(exp(t)), using
n^3<(m+1)^4. Thus `reciprocal_oe_production` gives the OE reciprocal
inequality with additive loss C_0 for every real t. Applying (12) at
the target and source cutoffs proves `oe_production`:

\[
 (33/100)F_A(3t/4-4)\le S_{OE}(A,t)+2C_0+8
                           \qquad(t\in\mathbb R).
 \tag{13}
\]

There is no extra analytic hypothesis in (13). The new
`OOEEProductionBound A` is exactly the second inequality in (4), with
its own nonnegative constant and eventual threshold. For backward-closed
A, `oddProductionBounds_of_ooee` combines it with (13).
`logMass_growth_of_ooee` and `conjecture_of_tao_rate_of_ooee` consequently
retain only this OOEE production input (and, for the latter, the open
Tao failure-rate estimate). The written OOEE short-interval argument
and its exceptional-target bound remain the next analytic formalization
obligation. No unconditional Lean result at exponent 5/8 is asserted.
