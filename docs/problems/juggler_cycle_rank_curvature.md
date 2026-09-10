# Juggler cubic cycles: first-rank curvature and signed floor loss

Status: **ARCHIVED**. Decision: **CLOSE** the automatic transfer of the
polynomial-family finite-difference obstruction using the sorted grid and
total floor loss. This is the canonical record for the gate of 10 September
2026. The actual integer-cell question remains unresolved. The analysis is
AI-assisted and has not received independent human review or new Lean
verification.

The authorized continuation below evaluates all three rank-envelope cap
sums, retains the CW44 compulsory-charge effects, and derives the exact
adjacent-cap/slack identity. Its signed test also produces no exclusion.
One numerical corollary of the existing grid-charge theorem restricts the
minimum at the specified counts to m<520000000.

## Problem

Can cyclic rank order, odd spacing, and correlated rounding losses force an
impossible integer second difference in an actual cubic Juggler cycle?

## Exact statement

Assume a primitive nontrivial cycle with odd minimum m>=5, maximum M<m^3,
period L>2, and o>=3 odd states. Let e=L-o. Existing cubic ordering gives
gcd(e,L)=1 and sorted states c_0=m<c_1<...<c_(L-1), with the first o odd and
the remaining e even. The rank permutation is i -> i+e modulo L.

The proposed exclusion seeks a proof that

\[
0<c_2-2c_1+m<2.
\tag{RC1}
\]

This would contradict the shared odd parity. We derive the exact equivalent
condition on signed floor loss, then test whether the existing total-loss
model forces it. It does not at the fixed scale tested below. No exclusion
using all actual pointwise floor cells is proved or refuted.

## Current literature

- [Paper A](../theory/juggler_finite_dynamics_note.md), Theorem 3.33 and
  Proposition 3.36: exact cubic rank rotation and sorted log-log grid.
  **Reproduced**. The proposition already states the integer-parity precision
  limitation of its grid enclosure.
- [Weighted remainder transport](juggler_cycle_weighted_remainders.md),
  CW41--CW44: initialized signed-arc identities and compulsory floor charges.
  The three-rank formulas below are **REPARAMETERIZATION** of that transport.
- [OOE escape families](juggler_ooe_escape_families.md): full polynomial
  parameter tails have an integer finite-difference obstruction. Its full-tail
  hypothesis does not hold for arbitrary finite sorted cycle states.
- [Preimage capacity](juggler_cycle_preimage_capacity.md): ordinary density,
  multiplicity and scalar counting do not settle the selected-state problem.
  No density or polynomial-occupancy premise is introduced here.
- [Absolute cells](juggler_cycle_absolute_cells.md), Result 1: the existing
  upper-cell/grid charge theorem already gives the logarithm-squared scale
  restriction. Result 9 below is a fixed numerical corollary of that theorem.

## Branch budget

```text
Mathematical target     An impossible integer second difference in a cubic cycle
Novelty hypothesis      Correlated floor losses sharpen separate grid intervals
Falsifier               Even integer curvature survives the stated relaxation
Already killed by?      Bare grid parity inference; full polynomial-family
                        assumptions on arbitrary finite cycles; ordinary density
Existing machinery      Exact rank rotation, sorted grid, signed floor transport
Maximum Phase-0 scope   Symbolic three-rank criterion and one boundary-scale tuple
                        L=780239, o=492276, e=287963, m=350000001;
                        no source/rank/orbit census or increase of the floor
Promotion criterion     A new necessary restriction with a proved implication
Stop criterion          Record the missing estimate if no contradiction follows
```

The user subsequently authorized the missing full-cap comparison. Its scope
is the same count pair at the existing floor: all three sums of the fixed
rank-envelope caps, evaluated by monotone rank blocks with exact modular
counts; the CW44 charge correction; and a symbolic audit of the common
integer cells. One scalar cutoff m=520000000 verifies the resulting minimum
upper-bound consequence. No trajectory, minimum sweep, or floor expansion
is performed. A finer numerical integration is unnecessary once the signed
interval remains separated from the exclusion window by a proved margin.

## Balanced-ternary formulation

The states and even integer second differences can be represented in balanced
ternary. The logarithmic and floor-cell arguments do not depend on a numeral
representation.

## Why BT may be relevant

No representation-specific advantage is established in this gate.

## Candidate operations / invariants

- J-cycle-rank-curvature-window: **REPARAMETERIZATION**. The exact signed-loss
  condition is the forbidden even-lattice gap expressed in existing coordinates.
- Fixed interval controls: **COMPUTATIONALLY VERIFIED**, restricted to the
  one stated tuple and the relaxed hypotheses listed below.
- J-cycle-rank-capacity-envelope: **COMPUTATIONALLY VERIFIED**, the complete
  fixed cap-sum enclosures and the one cutoff corollary of the existing
  absolute-cell theorem. No new global inequality is claimed.
- Exclusion from all actual integer cells: unresolved; no new conjecture is
  registered as a consequence of these controls.

## Experiments

The runner is `research.juggler_sequence.cycle_rank_curvature`, with output
[controls.json](../../data/research/juggler/cycle_rank_curvature/controls.json).
Its default prints a summary; `--write` reproduces the fixed data artifact.
It performs no rank enumeration or trajectory search.

The calculation uses `mpmath.iv`, exact integer inputs,
and outward binary endpoints stored as exact rational numbers. Decimal
displays are rounded outward. Assertions compare the rational endpoints.
The first-triple control uses 120 decimal digits; the capacity calculation
records its separate precision and block count in the output.
This is interval computation, not a formal-kernel certificate. The proof of
the symbolic identities and the real-grid extension is given below; tests
of the fixed report do not replace that proof.

## Conjectures

No new conjecture or cycle-existence claim is made.

## Counterexamples

Two ordered odd triples survive the total-defect relaxation:

| c_0 | c_1 | c_2 | c_2-2c_1+c_0 |
|---:|---:|---:|---:|
| 350000001 | 350009697 | 350019393 | 0 |
| 350000001 | 350009697 | 350019395 | 2 |

These are controls against a coarse inference, not actual cycles. In fact
O(350000001)=6547900454916 is even, so this literal m already fails the
required odd image of a cubic-cycle minimum. It is used only as the fixed
boundary scale. The real extension below does not impose all integer states,
parity guards, or upper unit-cell inequalities.

## Formalization

No new Lean module is supplied. Existing cubic order, grid, and signed-arc
kernels are indexed in Paper A and the weighted-remainder dossier. The new
record is an AI-assisted written re-expression and an interval control, not
an additional Lean-verified cycle exclusion.

## Results

### 1. The exact shared defect simplex

Put T=log 3, Lambda=o log 3-L log 2>0, and

\[
v_i=\log\frac{\log c_i}{\log m},\qquad w_i=v_i-iT/L.
\]

Extend v_(i+L)=v_i+T and w periodically. The initialized actual defects obey

\[
w_{i+e}-w_i=\Lambda/L-\delta_i,\qquad
0\le\delta_i<\eta(c_{(i+e)\bmod L}),\qquad
\sum_i\delta_i=\Lambda,
\quad\eta(x)=\log\frac{\log(x+1)}{\log x}.
\tag{RC2}
\]

The upper cap is evaluated at the actual target. Discarding those caps gives
the nonnegative total-defect simplex; it does not preserve all actual cells.

Let k be the inverse of e modulo L, a=k/L, d_j=delta_(je mod L), and
S_j=sum_(0<=n<j)d_n. Telescoping RC2 gives

\[
w_1=a\Lambda-S_k,\qquad w_2=(h/L)\Lambda-S_h,
\qquad h=2k\bmod L.
\tag{RC3}
\]

All three groups below are nonempty: k=L/2 would contradict gcd(k,L)=1
and L>2. If k<L/2, set p=S_k, q=S_(2k)-S_k, r=Lambda-S_(2k). Then

\[
p,q,r\ge0,\quad p+q+r=\Lambda,\quad
w_1=a\Lambda-p,\quad w_2=2a\Lambda-p-q,
\quad \chi:=w_2-2w_1=p-q.
\tag{RC4}
\]

If k>L/2, set p=S_h, q=S_k-S_h, r=Lambda-S_k. Then

\[
p,q,r\ge0,\quad p+q+r=\Lambda,\quad
w_1=a\Lambda-p-q,\quad w_2=(2a-1)\Lambda-p,
\quad\chi=q-r.
\tag{RC5}
\]

These are exact images of the nonnegative simplex: any prescribed group
masses can be distributed among their nonempty groups. In particular its
range for chi is exactly [-Lambda,Lambda]. This assertion alone imposes
neither sortedness nor the target-dependent caps.

The distinguished first defect is
gamma=log(((3/2)log m)/log O(m)), in group p. The even return into m gives
the lower charge beta=eta(m^2), in group r. Thus actual cycles also require
p>=gamma and r>=beta, and gamma+beta<=Lambda. With these retained faces the
ranges for chi become [2gamma+beta-Lambda,Lambda-beta] in RC4 and
[-Lambda+gamma,Lambda-gamma-2beta] in RC5. If the first group has length one,
fixing the initial edge requires p=gamma; its range may be smaller.

### 2. The exact forbidden window

Fix y=c_1>m, and for t=0,2 define

\[
H_t(y)=\log\frac{\log(2y-m+t)\log m}{(\log y)^2}.
\tag{RC6}
\]

Directly from the definitions,
chi=log((log c_2 log m)/(log y)^2), strictly increasing in c_2. Therefore

\[
H_0(y)<\chi<H_2(y)
\quad\Longleftrightarrow\quad 0<c_2-2y+m<2.
\tag{RC7}
\]

Because m,y,c_2 are odd, an actual cycle must instead satisfy
chi<=H_0(y) or chi>=H_2(y). This is a necessary disjunction, not a sufficient
condition for all even integer curvatures. Its exact interval width is

\[
H_2(y)-H_0(y)=\int_{2y-m}^{2y-m+2}\frac{dx}{x\log x}.
\tag{RC8}
\]

If H_0<0<H_2, the bound |chi|<=Lambda implies the conditional necessary
inequality Lambda>=min(-H_0,H_2). No uniform improvement follows without
further information on the actual y and signed loss. Odd spacing gives an
even curvature; it does not imply that curvature is positive.

### 3. What individual floor caps would have to accomplish

Consider RC5, the case of the fixed tuple below. Let valid bounds be
b_i<=delta_i<=U_i, replacing strict upper caps by closed ones for a necessary
estimate. Subtract the lower bounds, set H=Lambda-sum b_i, and let C_P,C_Q,C_R
be the sums of U_i-b_i over the three chronological groups. Set
chi_b=sum_Q b_i-sum_R b_i. Feasibility requires nonnegative capacities and
0<=H<=C_P+C_Q+C_R. The exact extrema in this closed box relaxation are

\[
\chi_b+\max(0,H-C_R-C_P)-\min(H,C_R)\ \le\ \chi
\ \le\ \chi_b+\min(H,C_Q)-\max(0,H-C_Q-C_P).
\tag{RC9}
\]

For the minimum, allocate as much residual mass as possible to R, then P,
and finally Q. The total-capacity condition makes this allocation possible.
For the maximum interchange Q and R. Every aggregate mass up to a finite
sum of coordinate capacities can be distributed among those coordinates.
Thus the bounds are attained in the closed relaxation; with strict caps
they need only be infimum and supremum. This optimization does not assert
that the allocations correspond to actual common integer states.

Using U_i=eta(c_(i+e mod L)), a successful exclusion would put the lower
endpoint of RC9 strictly above H_0(y) and the upper endpoint strictly below
H_2(y). This gate does not evaluate the three actual-state capacity sums or prove
that interval containment. The caps depend on the same unknown selected
states; a few local caps do not determine the sums.

### 4. One outward interval control

For (L,o,e,m)=(780239,492276,287963,350000001), one has k=478245 and
h=176251. This is RC5 with group lengths 176251,301994,301994. The ideal
grid f_i=exp(log m exp(iT/L)) has

\[
\begin{aligned}
\Lambda&\approx3.4711981668939710\cdot10^{-6},\\
f_1&\approx350009696.5299378356,\\
f_2&\approx350019392.3421088575,\\
f_2-2f_1+m&\approx0.2822331861938528.
\end{aligned}
\tag{RC10}
\]

The outward enclosure of the ideal curvature has width less than 10^(-110)
and lies strictly between 0 and 2. The published separate position bounds,
however, allow deviations of about 23902 in state units at these ranks.

For each odd triple in Counterexamples, recover w_1,w_2 from its integer
values and set

\[
p=h\Lambda/L-w_2,\quad
q=(k-h)\Lambda/L+w_2-w_1,\quad
r=(L-k)\Lambda/L+w_1.
\tag{RC11}
\]

The report proves p,q,r>0 and p+q+r=Lambda by RC11; it also checks the
necessary retained-face inequalities p>gamma and r>beta. For D=0 the
offsets are w_1 approximately 6.82644e-11 and w_2 approximately 9.55389e-11;
for D=2, w_1 is unchanged and w_2 is approximately 3.85979e-10. Both obey
0<w_1<w_2<T/L-Lambda/L and w_2<(1-1/L)Lambda.

At y=350009697 the exact exclusion window is H_0(y)<chi<H_2(y), with
approximate endpoint values

\[
H_0(y)\approx-4.0989863414838914\cdot10^{-11},\qquad
H_2(y)\approx2.4945003543399277\cdot10^{-10}.
\tag{RC12}
\]

The two triples lie exactly at H_0(y) and H_2(y) by substitution in RC6.
Their separately computed interval enclosures intersect those of H_0 and
H_2; this is a consistency check, not the proof of equality.

The even-return target cap eta(m) is approximately 1.4522840464721422e-10,
larger than the negative clearance -H_0 by a factor of about 3.54. At these
counts the edges targeting c_0,c_1,c_2 lie respectively in R,Q,P and have
coefficients -1,+1,0 in chi. This comparison measures required precision;
it does not show that any actual defect can vary independently through its
cap while retaining all the other cells.

### 5. An ordered real extension of each control

Three-state feasibility can be strengthened without enumerating ranks.
Write alpha=T/L and define W_j in chronological time by linear interpolation
through (0,0), (h,w_2), (k,w_1), (L,0). Set
d_j=Lambda/L-(W_(j+1)-W_j). The three positive constant rates are
p/h, q/(k-h), r/(L-k); their sum over all times is Lambda.
Assign w_i=W_(ki mod L) and

\[
\widetilde c_i=\exp(\log m\,\exp(i\alpha+w_i)).
\tag{RC13}
\]

This realizes the first three prescribed integers and the cyclic defect
equation. All W values lie in [0,w_2], so every lifted adjacent rank gap
is at least alpha-w_2>0, including the wraparound. Hence the full real
grid is strictly ordered, satisfies M<m^3 and the anchored grid bound.
The stronger w_2<alpha-Lambda/L also puts rank o-1 below m^2, while rank o
is above m^2 because o alpha=log 2+Lambda/L.

Only the nonnegative total-defect model is realized here. The uniform group
rates do not satisfy every actual upper floor cap; integer states and all
guards are not supplied. The retained-face checks in Result 4 are separate
necessary checks, not a claim that this uniform extension fixes the actual
initial edge. Neither extension is an actual or threshold Juggler cycle.

### 6. Complete target-cap sums from the fixed rank envelopes

Write m_0=350000001 and retain the fixed L,o,e,k,h. For every actual minimum
m>=m_0, the same target state c_j has the valid lower bound

\[
\ell_j=\max\{P_j,\exp(\log m_0\,\exp(jT/L-\omega))\},
\quad\omega=(1-1/L)\Lambda,
\tag{RC14}
\]

where P_j=m_0+2j for j<o and
P_j=m_0^2+1+2(j-o) for j>=o. Both the grid and parity-packing bounds increase
with the actual minimum, which justifies evaluating this lower envelope at
m_0. Thus every actual edge targeting c_j has delta<eta(c_j)<=eta(ell_j).
This is a universal upper cap, not an assertion that m_0 itself is admissible.

For chronological source time t, its target rank is (t+1)e modulo L.
Consequently the target phase at sorted rank j is kj modulo L, and its
source time is kj-1 modulo L. This offset matters: group P has target
phases 1 through h, group Q has h+1 through k, and group R contains the
remaining phases, including zero.

The runner partitions ranks into 24383 intervals of at most 32 ranks,
splitting at the odd/even cut. The weights eta(ell_j) decrease. On a block
of ranks from a through b-1, each group's contribution therefore lies
between its exact block count times eta(ell_(b-1)) and that count times
eta(ell_a). The counts use Euclidean integer floor sums of the modular
phases. Their full totals are exactly 176251,301994,301994. No actual state
or trajectory is enumerated. Summing outward intervals gives:

| Envelope capacity | Lower bound | Upper bound |
|---|---:|---:|
| U_P | 1.078867710e-6 | 1.079884728e-6 |
| U_Q | 1.848485656e-6 | 1.850228192e-6 |
| U_R | 1.848541792e-6 | 1.850284378e-6 |
| Total | 4.775895159e-6 | 4.780397296e-6 |

The table bounds are widened decimal displays; exact endpoints are stored
in the report. The total enclosure width is less than 4.503e-9. Its lower
endpoint already exceeds Lambda approximately 3.471198167e-6.

Using these three complete cap sums in RC9 with zero lower faces gives

\[
\begin{aligned}
-1.310\cdot10^{-6}&<\ell_0<-1.304\cdot10^{-6},\\
1.304\cdot10^{-6}&<u_0<1.310\cdot10^{-6},
\end{aligned}
\tag{RC15}
\]

where ell_0,u_0 are the exact endpoints of the envelope box's signed-loss
interval. Both boundaries in RC12 lie well inside this interval. The two
earlier integer triples also have group masses strictly smaller than the
lower capacity enclosures. Thus their masses fit this capped aggregate box.

This is a different relaxation from Result 5. Arbitrarily distributing the
masses below these coordinate caps need not give sorted states satisfying
the full potential equations and those same caps. The two separate controls
must not be combined into a claim that one configuration satisfies all of
their constraints. Actual cap values eta(c_j) also need not equal the
universal envelope values eta(ell_j).

### 7. Compulsory charges cannot repair this envelope box

Fix the coordinate caps U_i used in Result 6. For any valid lower faces
0<=b_i<=U_i with B=sum b_i<=Lambda, write B_P,B_Q,B_R for their group sums.
Eliminating the residual notation in RC9 gives

\[
\begin{aligned}
\ell_b&=\max(B_Q,\Lambda-U_R-U_P)
       -\min(\Lambda-B_P-B_Q,U_R),\\
u_b&=\min(\Lambda-B_P-B_R,U_Q)
       -\max(B_R,\Lambda-U_Q-U_P).
\end{aligned}
\tag{RC16}
\]

Changing either argument of a minimum or maximum changes its value by at
most the change in that argument. Comparison with b=0 therefore proves

\[
0\le\ell_b-\ell_0\le B_P+2B_Q\le2B,\qquad
0\le u_0-u_b\le B_P+2B_R\le2B.
\tag{RC17}
\]

The exact CW44 charges are b_i=eta(c_target^2) at parity switches and zero
otherwise. Switched targets are the first e odd states and all e even
states. In particular, for every actual minimum m>=m_0,

\[
B\le e\eta(m_0^2)+e\eta((m_0^2+1)^2)
\le L\eta(m_0^2)<1.619\cdot10^{-13}.
\tag{RC18}
\]

This is an upper bound on the charge, the direction needed in RC17.
Substituting a lower state bound directly into eta(c_target^2) would not
give a valid lower charge. The correction of at most 2B is far too small
to move RC15 inside RC12. Hence even the CW44 lower charges evaluated on
the actual states cannot repair this particular universal-cap box.

Parity also slightly lowers the independent upper faces. Put Z=log log.
With s=2 at a
switch and s=1 otherwise, the valid upper cap is
V_s(y)=Z((y+1)^2-s)-Z(y^2). It decreases in y>1. Its difference from the
raw cap is bounded by

\[
0<\eta(y)-V_s(y)
=\int_{(y+1)^2-s}^{(y+1)^2}\frac{du}{u\log u}
\le\frac1{y^2\log y}.
\tag{RC18a}
\]

Indeed the integration interval has length at most two and starts above
y^2. Across all envelope targets the total cap reduction is at most
D_max=L/(m_0^2 log m_0)<3.238e-13. Reducing capacities by nonnegative amounts
d_P,d_Q,d_R shifts the lower box endpoint upward by at most d_P+2d_R
and the upper endpoint downward by at most d_P+2d_Q, provided enough total
capacity remains. These inequalities follow from the same minimum/maximum
comparison as RC17. Total capacity exceeds Lambda by more than 1.304e-6,
so feasibility of this cap box is retained. Combining both corrections
changes either endpoint by at most 2(B_max+D_max)<9.714e-13. The computed
separation from the forbidden window remains greater than 1.303e-6.

The statement concerns these specified charges. It does not include every
later located or coupled remainder inequality, and it does not assert
feasibility of a genuine integer cycle with all actual caps.

### 8. Adjacent actual cap totals expose the missing upper-cell slack

There is an exact dependence between the actual cap totals which is lost
if they are treated as arbitrary numbers. For any k>L/2, set r=L-k and
h=2k-L. Adding r maps chronological Q=[h,k) bijectively to R=[k,L).
Since re is -1 modulo L, a Q target rank j is paired with R target j-1.
There is no wrap: Q cannot target rank zero, whose source time is L-1.

Let C_P,C_Q,C_R now denote sums of the actual caps eta(c_target). Because
eta decreases strictly on x>1,

\[
0<\varepsilon:=C_R-C_Q
=\sum_{j\in\operatorname{targets}(Q)}
  [\eta(c_{j-1})-\eta(c_j)]
\le\eta(m)-\eta(M)<\eta(m).
\tag{RC19}
\]

The upper bound completes a positive subsum to the full telescoping sum.
This controls cap totals, not the actual difference q-r of used losses.

On an actual edge x->y, put N=x^3 on O and N=x on E, and Z=log log.
The positive unused cap is exactly

\[
s=\eta(y)-\delta=Z((y+1)^2)-Z(N)>0,
\qquad U=(y+1)^2-N\in\mathbb Z_{>0}.
\tag{RC20}
\]

Here U is the integer distance to the next square boundary. Let s_P,s_Q,s_R
be the group sums of s. Since the same edges define caps and losses,

\[
\boxed{\chi=q-r=-\varepsilon+s_R-s_Q},\qquad
s_P+s_Q+s_R=C_P+C_Q+C_R-\Lambda.
\tag{RC21}
\]

Thus almost equal cap totals do not imply almost equal losses: the missing
quantity is the signed difference of unused upper-cell capacity. To force
the forbidden interval one would need

\[
H_0(c_1)+\varepsilon<s_R-s_Q<H_2(c_1)+\varepsilon.
\tag{RC22}
\]

This identity retains the actual shared states and integer square/cube
complements, but provides no sign by itself. Eliminating those complements
through the exact edge equations recovers the existing signed transport;
it is not an additional arithmetic inequality.

### 9. A fixed minimum upper bound from the existing theorem

The absolute-cell dossier already proves, with A=(log m)exp(-omega),

\[
\Lambda<\frac{e^{-A}}A\left(1+\frac{L}{T(A+1)}\right).
\tag{RC23}
\]

That source owns the proof and its logarithm-squared asymptotic consequence.
At the single cutoff m_*=520000000 and the present fixed counts, outward
intervals give

\[
\frac{e^{-A_*}}{A_*}\left(1+\frac{L}{T(A_*+1)}\right)
<3.230293215\cdot10^{-6}<\Lambda,
\tag{RC24}
\]

with separation greater than 2.409049519e-7. For fixed counts, A increases
with m, and both positive factors on the right of RC23 decrease. Therefore
every actual cubic cycle with (L,o,e)=(780239,492276,287963) must satisfy

\[
350000000<m<520000000.
\tag{RC25}
\]

The lower bound is the existing certified descent floor. The upper bound is
a numerical corollary of RC23, not a new charge theorem or a raised floor.
The forbidden literal endpoint m_0 from earlier controls is not restored
as a candidate. No assertion about taller cycles or other count pairs is
made, and these inequalities do not exclude the stated period.

## Open questions

The unresolved input is a signed estimate retaining the common actual
integer states and their target-dependent floor caps. The complete fixed
envelope sums do not place RC9 within RC7. The exact adjacent-cap relation
reduces the remaining sign question to RC22 for the integer upper-cell
complements, with all shared-state constraints still imposed.

## Decision

**CLOSE** the automatic finite-difference transfer from the sorted grid and
total defect. The exact window is a re-expression of parity, and both
boundary curvatures survive the stated relaxation. The authorized complete
cap-sum continuation likewise fails its signed test, including the CW44
charge correction. More precise integration of these same envelopes
cannot close the proved gap. The fixed cutoff RC25 is retained as a
corollary of existing machinery, without promoting a new no-cycle mechanism.
The single best next question is whether the actual integer upper-cell
complements obey the signed comparison RC22 along the two complete arcs.
That question is left open; no further gate is automatically pursued.

## Publication assessment

Status: **ARCHIVED**. This gate records a precision limitation, an exact
conditional criterion, and a fixed minimum upper-bound corollary. It changes
neither the certified descent floor nor the period bound and edits neither
Paper A nor its generated copies. Independent human review and formal
verification of the new written calculations remain outstanding.
