# Juggler cubic cycles: first-rank curvature and signed floor loss

Status: **STRUCTURAL**. Decision: **PROMOTE** the quantitative
bounded-run and selected-pair localization theorem in Result 21.
Result 22 adds conditional family cost and adjacency restrictions, while
closing the tested standalone charge and window-only shortcuts. Result 23
consolidates the integer interfaces, constructs arbitrarily cheap distinct
paired OOE returns, and bounds exactly lossless starts in a fixed rank prefix.
Result 18's complete integer-cell
feasibility continuation remains PARK; the earlier finite-difference,
cap-transfer and automatic crossing-payment mechanisms are closed.
This is the canonical research record for the gates of 10–11 September
2026. The actual integer-cell and no-cycle questions remain unresolved.
The analysis is AI-assisted and has not received independent human review.
Result 10's integer inequality, Result 17's square-start cell bridge, and
Results 19–23's explicitly identified integer and counting kernels are Lean verified.
Their complete actual-cycle applications remain written proofs.

The authorized continuation below evaluates all three rank-envelope cap
sums, retains the CW44 compulsory-charge effects, and derives the exact
adjacent-cap/slack identity. Its signed test also produces no exclusion.
One numerical corollary of the existing grid-charge theorem restricts the
minimum at the specified counts to m<520000000.

The further actual-complement audit below retains one local Lean theorem:
on an odd-to-odd edge, the next-square complement is at least three.
Complete-arc products, congruence elimination, and rotation weighting do
not supply the missing signed inequality. Their precise limitations are
recorded in Results 11--13.


**Publication consolidation.** The subsequent user-authorized publication
pass makes [Paper A](../theory/juggler_finite_dynamics_note.md), Section
6.3, the editorial source for the local upper-square proof, upper-cell
charge theorem, fixed minimum corollary, and printed signed criterion.
This dossier retains the research derivations, scoped controls and gate
decision. Historical statements below about preserving the paper refer
to the earlier exploratory gate, before that publication pass.

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

The next authorized continuation is symbolic: test actual upper-square
complements through complete-arc products, globally linked congruences,
and the exact rotation indicator. It performs no new numerical census.
Only a surviving local arithmetic lemma is added to the Lean laboratory;
it did not change the Paper A review object during that gate.

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
- J-odd-image-upper-square-gap: **EXACT — LEAN VERIFIED**. An actual
  odd-to-odd edge x->y satisfies x^3+3<=(y+1)^2. This is local arithmetic,
  without a cycle exclusion or a claim of external novelty.
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

The laboratory module
[UpperSquareGap.lean](../../formal/Problems/Juggler/UpperSquareGap.lean)
proves `odd_mul_add_two_ne_cube`, `cube_add_one_ne_odd_succ_sq`,
`cube_add_three_le_odd_succ_sq`, `odd_image_upper_gap`, and
`floorPower_odd_image_upper_gap` in `Problems.Juggler.UpperSquareGap`.
Its hypotheses and proof are stated in Result 10. It is registered in the
laboratory barrel, layer map, and, after the publication consolidation,
in the Paper A review barrel.

Existing cubic order, grid, and signed-arc kernels are indexed in Paper A
and the weighted-remainder dossier. The new analytic identities, cap
estimates, and symbolic limitation arguments below remain written proofs;
none is a Lean-verified cycle exclusion.

Result 17 additionally uses ReturnCells' \(\texttt{ooe_sq_eq_iff}\),
\(\texttt{ooe_sq_cell}\), and \(\texttt{ooe_sq_actual_of_cells}\).
They verify the square-start reduction and actual source guards from
integer cells. The joint equidistribution and infinitude theorem are
outside this formal claim.

CriticalCostKernel's \(\texttt{oo_equal_gap_triple}\) formalizes the
integer Result 15 family: cells, parities, raw remainders, complements
and opposite raw complement signs for every odd \(t\ge 9\). The
normalized comparison RC48 remains written.

The laboratory module
[CubicRemainderAssembly.lean](../../formal/Problems/Juggler/CubicRemainderAssembly.lean)
lifts an \(\texttt{OrbitUpperChargeCertificate}\) to positive gaps,
square remainders and the ordinary RC68 remainder difference. It proves
the leftover height \(H\le 86\) from \(m<520000000\), and it feeds the
existing Result 19/20 kernels once an even-denominator hypothesis and a
three-block cover (respectively supplied even-gap block costs) are
given. It does not yet prove those cover facts or extract RC75 blocks,
and it claims no missing cycle, signed RC37--RC38, or floor or period
change. RC72 remains written. The module is laboratory-only and is not
on the Paper A review barrel.

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

### 10. A local upper-square gap on every odd-to-odd edge

Let x and y be odd natural numbers with x^3<(y+1)^2. Then

\[
x^3+3\le(y+1)^2.
\tag{RC26}
\]

The canonical proof is Lemma 6.3a of Paper A, with the exact Lean
names listed in Formalization. This upper-face result differs from the
earlier lower-square remainder bound on odd-to-even edges.

For y>1 put V_s(y)=Z((y+1)^2-s)-Z(y^2), where Z=log log. The old
odd-to-odd upper cap V_1 is improved to V_3, and

\[
0<V_1(y)-V_3(y)
=\int_{(y+1)^2-3}^{(y+1)^2-1}\frac{du}{u\log u}
\le\frac1{y^2\log y}.
\tag{RC27}
\]

The interval has length two and starts above y^2 for y>1. V_3 is
positive and decreasing on y>=2: write its defining ratio as
1+log(1+2/y-2/y^2)/(2 log y), whose numerator decreases there and
whose denominator increases. It can therefore be used at the existing
lower envelope targets. The total additional reduction is at most the
same D_max from Result 7. Including both earlier corrections gives the
conservative bound

\[
2(B_{\max}+2D_{\max})<1.62\cdot10^{-12}
\tag{RC28}
\]

on either signed box endpoint's movement. This follows from the saved
outward bounds B_max<1.619e-13 and D_max<3.238e-13; it needs no new
scan. The proved separation greater than 1.303e-6 is unaffected at the
displayed precision. The lemma strengthens a local cell constraint but
does not establish a signed restriction for the actual common states.

### 11. Complete-arc products cancel to the endpoint criterion

Set ell=L-k and h=2k-L. Adding ell pairs Q=[h,k) with R=[k,L),
shifting both source and target ranks down by one. No Q source crosses
rank zero or the odd/even cutoff under this shift: those exceptional
source times are zero and L-1, outside Q. The entire branch word W is
therefore shared by the two actual paths, not merely its odd/even counts:

\[
F_W(c_2)=c_1,\qquad F_W(c_1)=m.
\tag{RC29}
\]

For any actual length-n arc X_0,...,X_n with u odd steps, (RC20) gives

\[
\exp(s_{\rm arc})=
\frac{2^n}{3^u}\frac{\log X_n}{\log X_0}
\prod_{i=1}^{n}\frac{\log(X_i+1)}{\log X_i}.
\tag{RC30}
\]

This follows by telescoping the log-log source/target terms on each
edge, retaining its factor two or three. Taking the R/Q ratio cancels
their identical word factors:

\[
\exp(s_R-s_Q)=e^\varepsilon
\frac{\log m\,\log c_2}{(\log c_1)^2}.
\tag{RC31}
\]

Substitution in RC22 cancels e^epsilon and returns exactly
2c_1-m<c_2<2c_1-m+2. Thus this complete product is RC21, with no
new inequality. Its logarithmic factors are not rational integer
products, so an integer numerator/denominator gap cannot be applied.

One can instead multiply the rational factors (y+1)^2/x^nu. Writing
b=log((y+1)^2/x^nu), however, the relevant slack is
s=log(1+b/log(x^nu)). The varying source normalization prevents
transferring a signed b-sum to a signed s-sum. Even conditional rational
nonvanishing only gives |log(A/B)|>=1/max(A,B). Bounding the unreduced
numerator and denominator by [(M+1)^2 M^3]^ell yields only the
exponentially small lower estimate [(M+1)^2 M^3]^(-ell). Neither the
required sign nor nonvanishing of that different statistic has been
established here.

### 12. Congruence elimination needs additional cell information

The exact definitions U_i=(c_(i+e)+1)^2-c_i^(nu_i), with cyclic
indices and nu_i=3 or 1, imply

\[
\sum_i U_i=\sum_i(c_i+1)^2
-\sum_{i<o}c_i^3-\sum_{i\ge o}c_i.
\tag{RC32}
\]

For example its reductions modulo two and three give respectively
sum U_i=L and sum U_i=L-#{i:c_i=1 mod 3} in those residue rings.
These contain no new controlled residue count. Likewise the product of
[(c_(i+e)+1)^2-U_i] is the already prescribed source product.

More generally, over any commutative ring K, the ideal I generated by
U_i-[(C_(i+e)+1)^2-C_i^(nu_i)] has

\[
K[C,U]/I\simeq K[C],\qquad I\cap K[C]=0.
\tag{RC33}
\]

Substitution of the displayed expressions proves this isomorphism.
Eliminating the auxiliary complements from their definitions alone
cannot create a restriction on the state variables. Integer cell ranges
and shared size estimates are extra hypotheses, not consequences of
this algebraic observation.

A limited modular control makes this distinction explicit. Given q>=1,
let Q=lcm(4,q), m=1+Qn with n>=L+1, and set c_i=m+Qi for i<o and
c_(o+t)=m^2+1+Qt for 0<=t<e. These are sorted, have the correct odd
cutoff and cubic threshold, and have residues one on O and two on E
modulo Q. The synthetic complements U_OO=3, U_OE=8, U_EO=2 satisfy
all edge congruences simultaneously, the positive complement boxes,
the prior OE lower-square gap, and the new OO bound RC26.

This is only a modular projection: the complements do not satisfy the
exact integer edge equalities, actual defects, sorted grid, or total-loss
identity. At fixed counts, sufficiently large m also violates RC23.
It is not a counterexample with the full constraints or with the fixed
minimum range RC25. A modulus larger than an independently established
magnitude bound could recover exact equality; no impossibility claim
for all congruence methods follows.

### 13. Balanced rotation counts do not bound actual slack variation

Let theta=ell/L<1/2. The Q target set and its periodic indicator are

\[
J=\{j:\ell\le(\ell j\bmod L)<2\ell\},\qquad
a_j=\left\lfloor(j-1)\theta\right\rfloor
    -\left\lfloor(j-2)\theta\right\rfloor.
\tag{RC34}
\]

Telescoping shows that the number of J indices in any integer interval
differs from its length times theta by less than one. For the actual
target-indexed periodic slack vector s_j, put S=s_R-s_Q. Then

\[
S=\sum_{j\in J}(s_{j-1}-s_j),\qquad
|S|\le\frac{L-1}{2L}\sum_j|s_{j+1}-2s_j+s_{j-1}|,
\qquad |S|\le\frac12\sum_j|s_j-s_{j-1}|.
\tag{RC35}
\]

For the second-difference bound, the partial discrepancy is
D_n=1-2theta-{(n-2)theta}, periodically extended, with oscillation
(L-1)/L. Twice summing by parts expresses S as its scalar product
with the second differences of s; subtract the midpoint of D's range.
For the first-difference bound, the positive and negative parts of a
periodic first difference have equal total size. These bounds apply to
actual slacks but supply neither a bound on their variation nor a sign.

The normalization matters. With A_j=(c_j+1)^2 and actual complement
U_j, one has

\[
s_j=-\log(1-\rho_j),\qquad
\rho_j=\frac{-\log(1-U_j/A_j)}{\log A_j}.
\tag{RC36}
\]

For j in J, a nonpositive paired contribution s_(j-1)-s_j requires

\[
U_j\ge A_j\left[1-
(1-U_{j-1}/A_{j-1})^{\log A_j/\log A_{j-1}}\right]
>\frac{A_j}{A_{j-1}}U_{j-1}>U_{j-1}.
\tag{RC37}
\]

Exponentiating RC36 gives the first inequality; 1-(1-t)^b>t for
0<t<1 and b>1 gives the second. Paired sources and targets retain
their respective parity, so this requires U_j>=U_(j-1)+2. Yet their
exact common-source secant, for source pair x_-<x_+ on exponent nu,

\[
U_j-U_{j-1}=(c_j-c_{j-1})(c_j+c_{j-1}+2)
-(x_+^\nu-x_-^\nu),
\tag{RC38}
\]

does not order its competing terms. Substituting the exact slacks back
into RC35 again gives S=epsilon+chi. The balanced indicator cannot by
itself control the frequency or size of the normalized increases in
RC37. Such control would require additional arithmetic information.

### 14. Whole paired words and the located upper-slack baseline

The next user-authorized test retains the complete actual paths from
RC29. Write x^-_0=c_1, x^+_0=c_2, x^-_n=m, x^+_n=c_1, with
x^-_t<x^+_t at each paired time. Both paths have the same genuine
branch word. Its OE/OOE return blocks use the actual odd predecessors
and even middle states, with every guard retained.

Set g_t=Z(x^+_t)-Z(x^-_t), where Z=log log. Subtracting the actual
edge losses on the common branch gives

\[
s^-_t-s^+_t=
\eta(x^-_{t+1})-\eta(x^+_{t+1})+g_t-g_{t+1}.
\tag{RC39}
\]

It holds separately on O and E. Summing any genuine return block
cancels its internal gaps; summing the full word gives
s_R-s_Q=epsilon+g_0-g_n=epsilon+chi. Thus this cancellation does not
depend on substituting a free E cell for an actual odd predecessor.
Downstream ordinary-log weights similarly give the exact endpoint
loss identity and require a further normalization comparison.

There is a positive located baseline from the integer upper gap.
Index edges by target rank j. Put u_j=3 on OO and u_j=2 on switched
edges, A_j=(c_j+1)^2, and

\[
b_j=Z(A_j)-Z(A_j-u_j)>0,\qquad
V_j=\eta(c_j)-b_j.
\tag{RC40}
\]

The actual inequalities imply b_j<=s_j<=eta(c_j). Paired source and
target parities agree, so corresponding edges use the same u_j.
Since Z(A)-Z(A-u) decreases with A, the baseline totals satisfy
B_R-B_Q>0. This is a located positive contribution, but its residual
has no supplied orientation. In fact, writing r_j=s_j-b_j gives

\[
r_j=V_j-\delta_j,\qquad
0\le r_j\le V_j,\qquad
\sum_jr_j=\sum_jV_j-\Lambda.
\tag{RC41}
\]

The transformation r_j=V_j-delta_j is an affine bijection between
this closed residual box and the original defect box
0<=delta_j<=V_j, sum delta_j=Lambda. It preserves every target cap
and its Q/R placement. In particular

\[
(B_R-B_Q)+(V_R-V_Q)=\varepsilon,
\qquad s_R-s_Q-\varepsilon=\delta_Q-\delta_R.
\tag{RC42}
\]

Optimizing only those residual bounds is exactly RC9 with the refined
caps. Adding known compulsory lower charges on delta translates to
upper bounds on r and does not break the equivalence. Counting the
positive baseline again after applying V_j would double count the
same upper-cell information. The previously proved <1.62e-12 movement
bound concerns the fixed universal envelope, not every cap vector
arising from actual states.

This closes the tested independent-charge propagation through the
genuine whole word. The exact integer secants impose more than the
box; no actual cycle or full guarded-word realization of its extrema
is supplied. A further bound on the residual's signed distribution
remains an unproved additional input. These are written algebraic
identities, not new Lean theorems or a no-cycle result.

### 15. Shared integer gaps quantize the change but do not orient it

The user-authorized continuation of 11 September 2026 tests the
divisibility hidden in RC38 and the proposed three-point extension.
Its scope is symbolic transport and one exact family, without a
minimum or orbit census. The new formulas below are written proofs,
not Lean results.

**Exact gap lattice.** Take two genuine edges on the same branch,
with sources \(x,x+d\) and targets \(y,y+D\), where \(d,D>0\) are
even. Let \(U_-,U_+\) be their actual upper complements and put
\(g=\gcd(d,D)\), \(A=(y+1)^2\), \(H=D(2y+D+2)\). Then

\[
\Delta U:=U_+-U_-\equiv d\pmod{2g}.
\tag{RC43}
\]

Indeed, \(H/g\) is even. On E the source-power difference is \(d\);
on O it is \(d(3x^2+3xd+d^2)\), whose parenthesized factor is odd.
Dividing RC38 by \(g\) proves RC43. In particular a positive change
is at least \(g\) when \(d/g\) is odd, and at least \(2g\) otherwise.
When \(d/g\) is odd, a zero change is impossible.

For the logarithmic assertions assume \(x>1\), as holds in the
intended cycle application. RC37 gives a precise necessary test. Set
\(a=g((d/g)\bmod2)\). If \(s_--s_+\le0\), then

\[
\Delta U>\frac{U_-H}{A},\qquad
\Delta U\ge
K:=a+2g\left(
\left\lfloor\frac{U_-H-aA}{2gA}\right\rfloor+1\right).
\tag{RC44}
\]

Here \(K\) is the least member of \(a+2g\mathbb Z\) strictly above
the rational threshold. Thus \(\Delta U<K\) certifies a positive
paired slack. Passing this test is only necessary for a nonpositive
slack; RC37's full logarithmic threshold is stronger. Summing RC44
over the disjoint selected pairs still requires a bound on their
positive complement variation, which has not been established.

The exact mod-eight projection is

\[
\Delta U\equiv
\begin{cases}
2D-d & y\text{ odd},\\
-d & y\text{ even}
\end{cases}
\pmod8.
\tag{RC45}
\]

For O use \(x^3\equiv x\pmod8\); for E the source power is \(x\).
Odd squares are one modulo eight, and the difference of the even
target-successor squares is \(2D\) modulo eight. Along a common
word, let \(d_t\) be the paired state gap and \(a_t\) its shared odd
indicator. Ordinary summation of RC45 gives
\[
\sum_{t=0}^{n-1}\Delta U_t\equiv
-d_0+2a_nd_n+\sum_{t=1}^{n-1}(2a_t-1)d_t\pmod8.
\]
The interior coefficients are \(1\) or \(-1\). The paired arcs in
RC29 are open paths, so their complement difference cannot be set
to zero. This congruence supplies no orientation of their real,
normalized slack difference.

**An exact equal-gap triple with opposite signs.** For every odd
integer \(t\ge9\), put

\[
(x_-,x_0,x_+)=(t^2-4,t^2,t^2+4),\qquad
(y_-,y_0,y_+)=(t^3-6t,t^3,t^3+6t).
\tag{RC46}
\]

All six numbers are odd and \(O(x_i)=y_i\). The lower remainders
are \(12t^2-64,0,12t^2+64\), respectively, and the upper
complements are

\[
(U_-,U_0,U_+)=
(2t^3-12t^2-12t+65,\ 2t^3+1,\
 2t^3-12t^2+12t-63).
\tag{RC47}
\]

These lower remainders are nonnegative and all upper complements
are positive: use \(2t^3-12t^2\ge6t^2\) for \(t\ge9\).
This proves every stated floor cell and parity guard directly.
Both adjacent pairs have \(d=4,D=6t,g=2\), but their complement
changes are \(12t^2+12t-64\) and \(-12t^2+12t-64\).

More strongly, for
\(\sigma_i=Z((y_i+1)^2)-Z(x_i^3)\), the normalized signs are

\[
\sigma_- -\sigma_0<0<\sigma_0-\sigma_+.
\tag{RC48}
\]

For the right inequality, \(U_+<U_0\) and
\((y_++1)^2>(y_0+1)^2\); the function
\(Z(A)-Z(A-U)\) increases with \(U\) and decreases with \(A\).
For the left inequality let \(\delta_-=Z(x_-^3)-Z(y_-^2)\).
Since \(12t^2-64\ge11t^2\), integration of \(Z'(u)=1/(u\log u)\)
gives
\[
\delta_->\frac{11}{6t^4\log t}.
\]
Write \(\eta(u)=Z(u+1)-Z(u)\), equal to the earlier cap definition.
On \(y_-\le u\le t^3\), one has \(u\ge3t^3/4\),
\(\log u\ge2\log t\ge2\), and
\[
0<-\eta'(u)\le -Z''(u)
=\frac{\log u+1}{u^2(\log u)^2}
\le\frac4{3t^6\log t}.
\]
The first bound follows because \(-Z''\) decreases on \(u>1\).
Consequently
\[
\eta(y_-)-\eta(t^3)\le\frac8{t^5\log t},\qquad
\sigma_0-\sigma_->
\frac{11t-48}{6t^5\log t}>0.
\]
This proves RC48 uniformly, including at arbitrarily large heights.
For example \(77,81,85\) map to \(675,729,783\), with complements
\(443,1459,531\). The family consists of actual OO edges; it is
not a closed orbit or an assertion of adjacency in a cycle.

Thus the input gap, output gap, their gcd, and sharing the middle
edge do not determine a uniform normalized sign. Both ordinary
three-point curvatures in RC46 are zero despite the convex O power.
This refutes that specific inference, not an estimate using further
global cycle placement or the full absolute states.

For completeness, a general common-branch triple has input gaps
\(d_0,d_1\), output gaps \(D_0,D_1\), and curvature
\(\kappa=d_1-d_0,\ \kappa'=D_1-D_0\). Subtracting two copies of
RC38 gives exactly
\[
2(y_1+1)\kappa'+D_0^2+D_1^2
=x_2^\nu-2x_1^\nu+x_0^\nu+U_2-2U_1+U_0.
\]
It retains a signed second difference of the actual complements.
There is still a weak parity cone: when all three images share parity,
\(\kappa\ge0\) on O implies \(\kappa'\ge0\), while
\(\kappa\le0\) on E implies \(\kappa'\le0\). Ideal convexity or
concavity gives the corresponding sign, rounding changes the second
difference by strictly less than two in absolute value, and
\(\kappa'\) is even. These opposite cones do not yield a preserved
full-cycle sign; RC46 shows that the O conclusion need not be strict.
On the periodic log-log lift, the corresponding curvature equation
is the difference of two existing gap equations, so its full-cycle
sum cancels. A synchronized triple also encounters mixed source
parities and rank wrap; it cannot follow one common branch word for
the full cycle.

**Decision: CLOSE** the gap/gcd-only sign inference and the automatic
strict or global three-point convexity transfer. Retain RC43--RC44 as conditional
arithmetic tests, without a new global consumer or a production Lean
module. Exact symbolic cell expansions and three fixed interval
controls at \(t=9,101,1000001\) agree with the written proof; they
are supplementary checks, not its justification. No period or
minimum bound changes. Paper A and all PDFs are unchanged by this gate.

### 16. Many-rank determinants and global matching: bounded triage

The next authorized triage asks whether more consecutive ranks or global
source/target matching supplies the information missing in Result 15.
It yields no new cycle restriction. The observations below distinguish
three tested inferences from the unresolved simultaneous integer cells.

**Rank-polynomial determinants have the same precision as differences.**
For \(r\ge1\), let \(D_r(z)\) be the determinant with rows
\((1,j,\ldots,j^{r-1},z_j)\), \(0\le j\le r\). Then
\[
D_r(z)=\left(\prod_{q=0}^{r-1}q!\right)\Delta^r z_0.
\tag{RC49}
\]
Both sides are linear in \(z\), vanish on every polynomial of degree
less than \(r\), and have the same coefficient
\(\prod_{q=0}^{r-1}q!\) on \(z_r\), the Vandermonde determinant
at \(0,\ldots,r-1\). This proves RC49.
If all \(z_j\) are odd integers, \(\Delta^r z_0\) is even.
If \(z_j=F(j)+e_j\), \(|e_j|\le E\), the independent error box
allows
\[
|\Delta^r z_0-\Delta^r F(0)|\le2^r E.
\tag{RC50}
\]
The determinant multiplies both this radius and the even-lattice
spacing by the same factorial product. It gives no additional
precision. This statement concerns the specified rank-polynomial
determinant, not every possible determinant involving actual cells.

For example, in the already illustrative regime
\(\Lambda\asymp L^{-1}\), \(m\asymp L^2/(\log L)^2\), the ideal
grid is \(F(i)=m^{3^{i/L}}\). At a fixed number of low unanchored
ranks, its allowed state-coordinate radius is
\[
E\asymp m\log(m)\Lambda\asymp L/\log L,
\quad
\Delta^rF(i)\asymp
L^{2-r}(\log L)^{r-2}
\quad(r\text{ fixed}).
\tag{RC51}
\]
The radius follows by differentiating
\(\exp(\log(m)e^v)\); the fixed-order derivative has leading term
\(F(i)((\log3)\log(F(i))/L)^r\). The local condition
\(\Lambda\log m\to0\) justifies these comparisons. Thus higher
differences of the ideal grid can be small while the available
independent error interval still contains even integers. The
minimum remains anchored exactly; no uncertainty is assigned to it.
This is a precision test of the grid relaxation, not a construction
satisfying all nonnegative defects or actual cells.

**Long exact affine cells are already in Lean.** The existing theorem
\(\texttt{Problems.Juggler.cube_fiber_sqrt_odd}\) in
[CubeFiber.lean](../../formal/Problems/Juggler/CubeFiber.lean)
implies, for every odd \(k\ge3\) and \(0\le j\le\lfloor k/3\rfloor\),
\[
x_j=k^4+4j,\qquad O(x_j)=k^6+6k^2j.
\tag{RC52}
\]
In that theorem write \(k=2a+1\) and take its parameter \(s=2j\).
Its guard \(3s\le2k\) is exactly \(3j\le k\).
All displayed sources and images are odd. Their higher differences
vanish for every order at least two for which the window is long
enough. Consequently no height-independent finite-window assertion
can force a wrong O-output parity merely from this affine pattern.
This is reuse of an established formal result, not a new family
theorem. These are parallel single-step edges indexed by \(j\), not
consecutive times on one orbit. There is no assertion that they also
fit RC51's full grid, the other branch, or a closed cycle.

**Global rearrangement returns the known rank rotation.** Put
\(a_i=c_i^{\nu_i}\), \(b_j=c_j^2\). The actual cubic band gives
\[
a_o<\cdots<a_{L-1}<a_0<\cdots<a_{o-1},
\]
because the even-source radicands are at most \(M<m^3\).
For the squared matching cost \(C(i,j)=(a_i-b_j)^2\),
\[
C(i,p)+C(j,q)-C(i,q)-C(j,p)
=2(a_i-a_j)(b_q-b_p).
\tag{RC53}
\]
Its sign reverses across the source branch cut. Reordering the even
sources before the odd sources restores increasing radicands; the
strict swap inequality then selects exactly the already known
matching \(i\mapsto i+e\bmod L\). It proves no empty target cell.
Likewise the global moment with \(Z=\log\log\) is
\(\sum_i Z(a_i)-\sum_j Z(b_j)=\Lambda\), the existing finance
identity. Other moments retain state-dependent residual information;
no useful new comparison of them is established in this triage.

**Wrong states near an edge need not be periodic.** For \(b\ge3\),
let \(S_b\) be the threshold map on
\(I_b=[b,b^3)\cap\mathbb Z\), using O below \(b^2\) and E at or
above it. Suppose an even upper periodic state \(x\) maps to an
odd state \(y\). Then both \(x-1\) and \(y^2\) are odd upper
states and map to \(y\): \(y^2\le x-1<x<(y+1)^2\).
Here \(y\ge b\), so both remain at or above \(b^2\).
They violate the upper branch's desired parity. Neither is periodic,
since the map is injective on its full periodic set and \(x\)
already maps to \(y\). Thus even an exact square-cell boundary can
be a wrong-parity transient entering a cycle, rather than a wrong
point on that cycle. For a parity-compatible cycle with \(e\) upper states,
the distinct partners \(x-1\) give at least \(e\) such transients.
This is a conditional statement, not a construction of a compatible
cycle.

**Decision: CLOSE** these automatic determinant-precision,
rearrangement-only, and nearby-hole inferences. The full actual
integer-cell problem remains unresolved. No new production Lean
module or claim of a distinct successful arithmetic attack follows.
The finite-window control reuses CubeFiber; the remaining comparisons
are written arguments. No state census, floor increase, Paper A edit,
or PDF operation was performed.

### 17. An exact OO edge need not force a fixed fraction of the nearby caps

This continuation tests a scalar alternative to the signed criterion:
could a zero-loss OO edge force a uniformly substantial rounding charge
elsewhere in its genuine OOE return? The answer is negative for a
positive constant fraction of the actual target caps.
The infinitude argument below is an AI-assisted written proof using
classical equidistribution, with independent human review outstanding.
The exact integer-cell reduction is separately formalized in ReturnCells.

For an actual edge with target \(y>1\) and ideal real image \(y+\theta\),
write \(Z=\log\log\),
\[
\delta=Z(y+\theta)-Z(y),\qquad
\eta(y)=Z(y+1)-Z(y).
\]
For \(y\ge2\), \(0\le\theta<\epsilon<1\), monotonicity of
\(Z'(y)=1/(y\log y)\) gives
\[
0\le\frac{\delta}{\eta(y)}
\le\theta\,\frac{(y+1)\log(y+1)}{y\log y}
<3\epsilon.
\tag{RC54}
\]
Here \(y+1\le3y/2\) and \(y+1\le y^2\) bound the derivative
ratio by three.

**Small-charge return theorem.** For every \(c>0\) and every height
\(H\), there is an actual OOE block
\[
x\longmapsto u\longmapsto v\longmapsto z,\qquad x>H,
\]
with parities odd, odd, even, odd, such that
\[
x<z<u<x^2\le v<x^3,\qquad
\delta_1=0,\quad
0<\frac{\delta_2}{\eta(v)}<c,\quad
0<\frac{\delta_3}{\eta(z)}<c.
\tag{RC55}
\]
In particular its total loss is less than
\(c(\eta(u)+\eta(v)+\eta(z))\).
The displayed order makes it a genuine first return to
\([x,O(x))=[x,u)\), with all states in the cubic threshold band
\([x,x^3)\). It asserts neither periodic membership nor closure of
the set of constructed starts under this return.

**Joint smooth phases.** The sequence
\[
\left(\frac{(2n+1)^{9/2}}2,\,
      \frac{(2n+1)^{9/4}}2\right)
\quad(n=1,2,\ldots)
\tag{RC56}
\]
is uniformly distributed modulo one in the unit square.
For a fixed nonzero integer pair \((h_1,h_2)\), apply the classical
derivative test to
\(f(s)=(h_1(2s+1)^{9/2}+h_2(2s+1)^{9/4})/2\).
On a dyadic interval of size \(N\), its fifth derivative has fixed
sign and size comparable to \(N^{-1/2}\) if \(h_1\ne0\).
If \(h_1=0\), its third derivative has size comparable to
\(N^{-3/4}\). The lower power cannot cancel the leading term
eventually. The standard estimates give
\[
\frac1N\left|\sum_{N<n\le2N}e^{2\pi i f(n)}\right|
\ll_{h_1,h_2}
\begin{cases}
N^{-1/60}+N^{-13/120},&h_1\ne0,\\
N^{-1/8}+N^{-3/8},&h_1=0.
\end{cases}
\tag{RC57}
\]
These are applications of the third- and fifth-derivative bounds
in [Robert, Theorem 3](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf).
Dyadic decomposition and the
[multivariate Weyl criterion](https://doi.org/10.1017/S0305004100032886)
prove RC56. Frequencies are fixed in this argument; no discrepancy
bound uniform over shrinking target boxes is asserted.

**All floor and parity guards.** Fix \(0<\epsilon<1\). Use the
phase rectangle
\[
(0,\epsilon/2)\ \times\ (1/2,(1+\epsilon)/2).
\tag{RC58}
\]
Its area is \(\epsilon^2/4\). By RC56 a proportion tending to that
area of the odd parameters \(t=2n+1\) belongs to this rectangle.
For these arbitrarily large \(t\), put
\[
x=t^2,\quad u=t^3,\quad
A=t^{9/2},\quad v=\lfloor A\rfloor,\quad
B=t^{9/4}=\sqrt A,\quad z=\lfloor B\rfloor.
\tag{RC59}
\]
The first phase gives \(v\) even and \(0<A-v<\epsilon\); the
second gives \(z\) odd and \(0<B-z<\epsilon\).
Both \(x,u\) are odd and \(x^3=u^2\), so the first O step is
exact. The second O step is exactly \(u\mapsto v\).
Finally
\[
\lfloor\sqrt{\lfloor A\rfloor}\rfloor
=\lfloor\sqrt A\rfloor=z,
\tag{RC60}
\]
because the two bounding squares for \(A\) are integers.
Thus \(v\mapsto z\) is the genuine E step, with
\[
0<\sqrt v-z\le B-z<\epsilon.
\]
Its strict positivity follows from the opposite parity of \(v\)
and \(z^2\). No equidistribution theorem is applied to a nested
floor: the exact square start and RC60 reduce the construction to
the two smooth phases in RC56.

For \(t\ge3\), \(t^{1/4}>5/4\) gives \(z>t^2\), while
\(B<t^3\) gives \(z<u\). Also \(u<t^4=x^2\),
\(\sqrt t>3/2\) gives \(v\ge t^4\), and \(A<t^6=x^3\).
This proves the order and first-return geometry in RC55.
Apply RC54 to the two nonzero raw losses, then take
e.g. \(0<\epsilon<\min(1,c/3)\) and \(t\) large enough that
\(t^2>H\). The first loss is zero, completing the theorem.

**The contracting return also has no positive constant charge.**
There is a simpler explicit OE family: for odd \(b\ge3\),
\[
b^4+2\longmapsto b^6+3b^2\longmapsto b^3.
\tag{RC61}
\]
The parities are odd, even, odd. The O lower square remainder is
\(3b^4+8\), and its upper complement is
\(2b^6-3b^4+6b^2-7>0\). The E lower remainder is \(3b^2\)
and its upper complement is \((b-1)^2(2b+1)>0\).
Hence both cells are exact. Rationalizing the two square-root
errors bounds them by \(2/b^2\) and \(3/(2b)\), respectively.
Their cap-normalized losses are therefore below \(6/b^2\) and
\(9/(2b)\), and tend to zero. This OE family alone would not
have answered the OOE compensation question.

**Formal and numerical boundary.** ReturnCells supplies
\(\texttt{ooe_sq_eq_iff}\), \(\texttt{ooe_sq_cell}\), and
\(\texttt{ooe_sq_actual_of_cells}\). They certify the exact
fourth-power cell and the guarded chain from the supplied integer
square/fourth-power cells. They do not prove RC56, infinitude, or
the analytic inequalities RC54--RC55.
The two fixed controls in
[small_loss_returns.json](../../data/research/juggler/cycle_rank_curvature/small_loss_returns.json)
are checked solely by integer powers:
at \(t=275\) both smooth fractional errors are below \(1/10\);
at \(t=15587\) they are below \(1/100\). The latter trace is
\[
242954569\to3786932867003\to7369387770836580146
\to2714661631.
\]
For denominator \(q\), the exact certificates are
\(q^2t^9<(qv+1)^2\) and \(q^4t^9<(qz+1)^4\).
These bounded witnesses illustrate the argument; they do not prove
infinitude or expand the certified descent floor.

**Decision: CLOSE** the proposed positive-constant local compensation
mechanism. Retain RC55 as a construction-class obstruction and its
exact Lean bridge. This does not refute the existing smaller,
height-dependent integer charges, nor a lower bound requiring
complete cyclic selection. The limits are taken with fixed
\(\epsilon\); a prescribed rate \(\epsilon(t)\), concatenation into
one orbit, escape to infinity, and a cycle realization are not
established. No paper PDF is rebuilt by this gate.


### 18. Complete integer-cell propagation: exact fixed points, no bounded exclusion

This gate tests the first proposed arithmetic continuation after Result 17:
combine exact integer cells on the same complete rank vector with real
interval bounds and residue information. The count tuple is fixed at
\((L,o,e)=(780239,492276,287963)\), with the initial minimum bracket
\(350000001\le m\le519999999\). It neither subdivides that bracket nor
enumerates candidate minima or trajectories.

**Bounded triage.** The novelty hypothesis is that shared forward and
backward cells retain information discarded by independent remainder
boxes. The maximum experiment is four full directed edge sweeps through
one rank box, with small exact controls and a symbolic audit of residue
saturation. The promotion criterion is an arithmetic restriction or a
class exclusion. Elementary solver completeness is a method fact, not
a new no-cycle theorem. If four sweeps do not exclude the box, the
feasibility campaign stops without a larger search.

**Exact interval updates.** Put \(\sigma(i)=i+e\bmod L\), with
\(\nu_i=3\) for \(i<o\) and \(\nu_i=1\) otherwise. Each node has a
single shared integer variable, fixed odd or even parity, and a current
interval \([a_i,b_i]\). Write
\(f_\nu(x)=\lfloor\sqrt{x^\nu}\rfloor\), and let
\(\operatorname{ceilroot}_\nu(N)\) be the least natural \(x\) with
\(N\le x^\nu\). An edge \(i\to j=\sigma(i)\) permits the updates
\[
\begin{aligned}
a_j&\gets\max(a_j,f_{\nu_i}(a_i)),&
b_j&\gets\min(b_j,f_{\nu_i}(b_i)),\\
a_i&\gets\max(a_i,\operatorname{ceilroot}_{\nu_i}(a_j^2)),&
b_i&\gets\min(b_i,\operatorname{ceilroot}_{\nu_i}((b_j+1)^2)-1).
\end{aligned}
\tag{RC62}
\]
Every new lower endpoint is rounded up to its node's parity and every
upper endpoint down to that parity. Adjacent order similarly imposes
\(a_{i+1}\ge a_i+1\) and \(b_i\le b_{i+1}-1\), with parity rounding.
Each update preserves every genuine solution in the current box.
The strict upper inverse is essential even at a perfect-power boundary.
An O image has at most one integer predecessor candidate when the target
is positive, but that candidate need not satisfy its upper cell or parity.

For a variable minimum, the initial global ceiling is computed from
the **upper** minimum endpoint. Using \(a_0^3\) as a ceiling for every
candidate maximum would incorrectly discard larger minima.

**A common fixed point is already an actual cycle.** This is stronger
than nonempty intermediate intervals. At a common lower-endpoint fixed
point, the forward and backward inequalities give
\[
f_{\nu_i}(a_i)\le a_{\sigma(i)},\qquad
a_{\sigma(i)}^2\le a_i^{\nu_i}.
\]
The second inequality implies the reverse root inequality, hence
\[
\boxed{f_{\nu_i}(a_i)=a_{\sigma(i)}\quad\hbox{for every }i.}
\tag{RC63}
\]
All equations hold on the same endpoint vector. An unattained target
cannot persist: its backward threshold overshoots it under the forward
map and forces a further update. With the source parities and strict
order retained, RC63 is the actual Juggler map. Since
\(\gcd(e,L)=1\), the sorted distinct endpoints form one primitive
\(L\)-cycle.

The cubic band also follows at such an exact vector. If
\(q=a_e=O(a_0)\), \(t=a_{e-1}=E(a_{L-1})\), strict integer order gives
\[
a_{L-1}<(t+1)^2\le q^2\le a_0^3.
\]
There is therefore no missing band assumption in this fixed-point
interpretation.

Finite upper bounds and fair updates ensure eventual exhaustion or
an exact fixed point: every changed endpoint moves by a positive
integer inside its original finite range. This is a standard
monotone-constraint argument. It gives no useful bound on the required
number of updates. Even the generic one-node constraint \(f(n)=n+2\)
on a bounded parity class can advance only one permitted value per
pass until it fails; that example concerns the method, not Juggler.

A workspace Lean consumer verifies the generic fixed-point implication,
preservation of solutions under both lower updates, and its actual-step
specialization with source parity. It is an exploratory check, not a
new registered module or a Paper A formalization claim. No finite
iteration bound or interval-exhaustion certificate is formalized.

**Small moduli do not repair independent remainder boxes.** Write
\(R_i=c_i^{\nu_i}-c_{\sigma(i)}^2\), with target \(y=c_{\sigma(i)}\).
After the known local integer improvements, the independently allowed
remainders contain the following complete parity progressions:
\[
\begin{array}{c|c|c}
\text{edge}&\text{allowed remainder box}&\text{number of values}\\ \hline
OO&0,2,\ldots,2y-2&y\\
OE&3,5,\ldots,2y-1&y-1\\
EO&1,3,\ldots,2y-1&y .
\end{array}
\tag{RC64}
\]
These are the local boxes, not an assertion that every listed remainder
has an actual source. A progression of step two and length at least
\(Q/\gcd(2,Q)\) covers all compatible residue classes modulo \(Q\).
Consequently the modular equation
\[
R_i\equiv c_i^{\nu_i}-c_{\sigma(i)}^2\pmod Q
\]
adds no restriction to shared state residues if each \(R_i\) is kept
only in its independent box and
\[
\frac{Q}{\gcd(2,Q)}\le m_0-1,\qquad m_0=350000001.
\tag{RC65}
\]
This includes every even \(Q\le700000000\), in particular powers of
two through \(2^{29}\). When several moduli constrain the same remainder,
use their least common multiple; choosing a different remainder witness
for each modulus would lose their joint content. RC65 does not cover
narrowed, jointly coupled remainder intervals, the exact difference
equation, or an additional aggregate loss constraint. Such information
could still accelerate the complete procedure. Moduli are unnecessary
for the correctness of RC63.

**The four-sweep experiment.** Initial rank bounds use the already proved
log-log grid, with outward interval arithmetic at 60 decimal digits.
On each of 4086 monotone rank blocks, the lower value uses its first
rank and the lower minimum, and the upper value uses its last rank
and the upper minimum. The maximum block size is 191 ranks. Odd/even
packing, the global upper cubic ceiling, and the exact minimum bracket
are imposed. Each sweep enforces adjacent order and then visits every
edge with both directions of RC62; edge order alternates increasing
and decreasing rank. There is no parameter subdivision.

The small controls recover the threshold cycle \(3\to5\to11\to3\)
when its wrong parity is allowed, exclude it when the high source
must be even, and preserve the trivial actual fixed point \(1\).
Integer root-boundary controls also pass. An independent agent audited
the outward initialization and update formulas and replayed only these
small controls.

The saved [bounded result](../../data/research/juggler/cycle_rank_curvature/cyclic_cell_propagation.json)
has the following outcome:
\[
\begin{array}{c|c|c}
\text{sweep}&\text{remaining minimum bracket}&\text{empty domains}\\ \hline
1&[350000003,519999999]&0\\
2&[350000003,519999997]&0\\
3&[350000003,519999997]&0\\
4&[350000005,519999995]&0 .
\end{array}
\tag{RC66}
\]
No domain becomes a singleton. A direct check after the fourth sweep
finds that the lower endpoints do **not** satisfy all actual edges,
so this is not a fixed point or a cycle witness. The run removes four
odd endpoint minima from the fixed cubic model; it does not exclude
the count pair. These are bounded computational observations, not a
new certified descent floor or period bound.

**Decision: PARK** the complete-cell feasibility campaign at the stated
budget. Retain exact fixed-point completeness and the scoped residue
saturation test as method facts. The independent-remainder small-modulus
shortcut supplies no extra condition. A continuation would need a
justified acceleration or a new arithmetic restriction that excludes
a whole permitted class; more unfinished sweeps alone are not such a
result. Paper A, its PDFs, and production Lean sources are unchanged.

### 19. Global charging and unavoidable three-block remainder variation

The bounded charging audit has two outcomes. Pairing level crossings
alone does not improve the existing cap budget. The integer gap
recurrence does, however, force a quantitative amount of raw remainder
variation on every actual cubic cycle. This is a new necessary
restriction, not a signed-loss or no-cycle theorem.

The triage allowed one symbolic crossing assignment, its exact donor
comparison, and an adjacent-gap valuation audit, with small fixed
controls. A theorem phase was reserved for a surviving arithmetic
claim. No interval campaign, source census, or minimum subdivision
was continued.

**The automatic donor assignment is already in the old budget.**
Index defects by target as \(d_j=\delta_{\sigma^{-1}(j)}\), so
\(s_j=\eta(c_j)-d_j\). For the disjoint nonwrapping pairs selected
in RC34, write \(h_j=(s_j-s_{j-1})_+\). Then
\[
h_j=\bigl(d_{j-1}-d_j-[\eta(c_{j-1})-\eta(c_j)]\bigr)_+
\le d_{j-1}.
\tag{RC67}
\]
Thus an injective donor assignment already exists: charge the rise
to its earlier target's actual defect. It supplies no extra budget.
For fixed caps, any weighted signed sum of slack differences is a
linear function of the same defect coordinates; its exact support
bounds are the capped-simplex optimization already used in RC9.
A positive-part objective is a maximum of these linear objectives
over masks. Every feasible defect vector already satisfies its own
cyclic level-crossing identities. Adding those identities therefore
cannot remove the old optimizers.

Raw complement levels do not have constant logarithmic cost:
the sensitivity at target square \(A\) and level \(u\) is
\(1/((A-u)\log(A-u))\), decreasing with \(A\). A matched raw crossing
does not by itself compare the receiving edge's actual defect.
Nor can the circular seam be assigned zero cost: its cap jump is
\(\eta(m)-\eta(M)>0\). These observations close automatic crossing
payment, while leaving stronger assignments using exact arithmetic
open.

**Remainder variation theorem.** Let an actual primitive cubic
Juggler cycle have \(m>1\), \(M<m^3\), sorted states
\(c_0=m<\cdots<c_{L-1}=M\), odd count \(o\), even count \(e\),
and the usual rank rotation \(\sigma(i)=i+e\bmod L\). Put
\(a=o-e>0\). The source-rank blocks are
\[
OO:\ 0\le i<a,\qquad
OE:\ a\le i<o,\qquad
EO:\ o\le i<L.
\]
Let
\[
R_i=c_i^{\nu_i}-c_{\sigma(i)}^2,\quad
\nu_i=\begin{cases}3&i<o,\\1&i\ge o,\end{cases}
\]
and introduce the positive integer gaps
\[
\ell_i=c_{i+1}-c_i\ (i<L-1),\qquad
\ell_{L-1}=m^3-M,\qquad
H=\max_i v_2(\ell_i).
\]
Choose any three constants \(\beta_{OO},\beta_{OE},\beta_{EO}\);
they need not be the previously known lower remainders. Let \(S\)
be the number of ranks where \(R_i\) differs from the constant
chosen for its block. Then
\[
\boxed{L\le(H+1)(3+2S).}
\tag{RC70}
\]
In particular this applies to the most frequent remainder in each
block, as well as to each block's actual minimum.

**Exact lifted recurrence.** The initialized recurrence is
[CW13--CW15](juggler_cycle_weighted_remainders.md):
\[
B_i\ell_{\sigma(i)}=N_i\ell_i-r_i.
\tag{RC68}
\]
Here \(N_i,B_i\) are positive integers. Away from \(i=o-1,L-1\),
\[
N_i=\begin{cases}c_i^2+c_ic_{i+1}+c_{i+1}^2&i<o,\\1&i\ge o,\end{cases}
\quad
B_i=c_{\sigma(i)}+c_{\sigma(i+1)},\quad
r_i=R_{i+1}-R_i.
\]
Write \(h=c_{o-1}\), \(s=c_o\), \(q=c_e=O(m)\), and
\(t=c_{e-1}=E(M)\). At the two special transitions,
\[
\begin{array}{c|c|c|c}
i&N_i&B_i&r_i\\ \hline
o-1&h^2+hs+s^2&m^3+M&(s^2+sm^2+m^4)R_o-R_{o-1}\\
L-1&1&q+t&R_0-R_{L-1}.
\end{array}
\]
The cut formula uses \(s=m^2+R_o\). It is a polynomial lift of the
actual E cell at the even state \(s\), not an O step from that state.

Every \(N_i\) is odd. Exactly two denominators are odd, at
\(i=a-1,o-1\). Both of these indices have nonzero correction:
\(r_{a-1}=R_a-R_{a-1}\) is odd because the two remainders have
opposite parity. At the cut, \(R_o\ge1\) and \(s\ge m^2+1\), so
\[
s^2+sm^2+m^4\ge3m^4+3m^2+1>2m^3>R_{o-1}.
\]
The last comparison follows from
\(R_{o-1}\le2M-1<2m^3\). Therefore \(r_{o-1}>0\).
Consequently **every zero correction has an even denominator**.

Let \(T=\#\{i:r_i\ne0\}\), and put \(v_i=v_2(\ell_i)\).
If \(r_i=0\), valuation of RC68 gives
\[
v_i=v_2(B_i)+v_{\sigma(i)}\ge1+v_{\sigma(i)}.
\]
Each zero correction consumes at least one unit of valuation.
Since \(\sigma\) is a permutation, \(\sum_i(v_i-v_{\sigma(i)})=0\).
The nonzero corrections can restore at most \(H\) units each.
Hence
\[
L-T\le HT,\qquad
\boxed{L\le(H+1)T.}
\tag{RC69}
\]
This strengthens the earlier product nonvanishing CW23--CW24 to
a lower bound on the number of nonzero corrections.

Away from the three block boundaries
\(\{a-1,o-1,L-1\}\), the two adjacent remainders have the same
chosen block constant. Thus \(r_i\ne0\) requires a deviation at
\(i\) or \(i+1\). A deviating rank touches at most two such edges,
so \(T\le3+2S\). Combining this with RC69 proves RC70.
This counts deviations from **any** three chosen constants; it
does not assert that there are \(S\) different remainder values.

**Fixed-count consequence.** In the already established regime
\((L,o,e)=(780239,492276,287963)\), RC25 gives \(m<520000000\).
Every positive lifted gap is less than \(m^3\), and the pure integer
comparison
\[
520000000^3<2^{87}
\]
therefore gives \(H\le86\). It follows that
\[
\boxed{T\ge8969,\qquad S\ge4483.}
\tag{RC71}
\]
The thresholds use integer ceilings, not floating-point logarithms.
These counts refer only to the stated cubic cycle regime. They do
not exclude the count pair or apply to taller cycles without further
structure.

If each chosen constant is the actual minimum remainder in its
block, every deviation is a positive even integer. Therefore
\[
\sum_i(R_i-\beta_{\mathrm{type}(i)})\ge2S,
\quad\hbox{in particular at least }8966
\hbox{ in the fixed-count regime.}
\tag{RC72}
\]
This is raw square-remainder mass. The conversion to log-log loss
depends on the actual target squares, and its placement among
signed arcs is not supplied by the theorem.

**Verification and formal boundary.** The laboratory module
\(\texttt{CubicRemainderVariation}\) verifies finite-permutation
valuation-drop counting, the boundary/deviation support estimate,
the fixed numerical cardinality implications, and the valuation
balance and drop from an exact positive integer product equality.
Its generic version with exceptional positions retains a separate
nonincrease assumption off the reset set; omitting it is false.
The actual application above uses the stronger strict-drop case,
because both odd-denominator positions are proved to be resets.

The complete conversion from an actual cubic cycle to the lifted
recurrence, the three source-rank blocks, and the forced special
corrections is the written proof above. CubicRemainderAssembly now
extracts gaps, remainders and the ordinary RC68 difference from a
charge certificate and proves leftover H<=86; the even-denominator
cover and special-cut nonvanishing remain hypotheses or written.
Independent AI audits agree on the written proof; independent human
review remains outstanding.

[Fixed controls](../../data/research/juggler/cycle_rank_curvature/remainder_variation_controls.json)
check the integer ceiling arithmetic and a sharp generic valuation
reset pattern. They also retain three parallel genuine OO edges,
\(45\to301,\ 49\to343,\ 95\to925\), illustrating the limitation of
paying an entire rise from the next raw downcrossing edge. These
are separate edges, not a cycle or consecutive orbit steps.
The controls do not prove RC70 or construct its hypothetical cycle.

For completeness, write \(Z=\log\log\) and label the three
slacks by their source. Their upper complements are respectively
\(79,687,101\). Monotonicity of \(Z'\) gives
\[
s_{49}=\eta(343)>\frac1{3096\log2},\qquad
s_{45}<\frac{79}{1458000\log2},\qquad
\delta_{95}<\frac{1750}{16256875\log2}.
\]
The elementary logarithmic comparisons are \(344<2^9\),
\(91125>2^{16}\), and \(855625>2^{19}\). Since
\(1/3096-79/1458000>1750/16256875\), the entire slack rise
\(s_{49}-s_{45}\) exceeds the next edge's actual defect.
This refutes that whole-rise payment on these local ordered cells;
it does not exclude every subdivided matching with additional
full-cycle restrictions.

**Decision: PROMOTE** the quantitative remainder-variation theorem
RC70 and its fixed-count consequence RC71. The automatic coarea
payment mechanism is closed. The new support count supplies neither
the sign nor the target-weighted magnitude needed by RC7. No cycle,
escape, new descent floor, or new period exclusion is claimed.
Paper A and all PDF artifacts are unchanged; the formal kernels
belong to the laboratory rather than its current manuscript claim.

### 20. Splitting and merging valuation, itinerary and gap budgets

The user-authorized fusion pass asks which existing constraints become
stronger when imposed on the same hypothetical cycle. The successful
combination is:

1. the exact signed integer-gap recurrence;
2. divisibility of sums and differences of even states;
3. the exact odd/even visit counts of the rank rotation;
4. the single telescoping budget for all positive integer gaps.

Splitting the rotation into stretches without a valuation-critical
correction and then summing their costs gives a stronger distribution
constraint. Merely splitting the old support count among signed-loss
groups still gives no orientation.

**A correction must have the right valuation to interrupt descent.**
Keep all notation and actual primitive cubic-cycle hypotheses of Result
19. Put \(h_i=v_2(\ell_i)\). Call an index critical when
\[
r_i\ne0,\qquad v_2(|r_i|)=h_i,
\]
and let \(C\) be the number of critical indices. This is more selective
than the nonzero-correction count \(T\). If an index is not critical,
the exact equation \(r_i=N_i\ell_i-B_i\ell_{\sigma(i)}\), with
\(N_i\) odd, implies
\[
h_i\ge v_2(B_i)+h_{\sigma(i)}.
\tag{RC73}
\]
Indeed, if the right side exceeded \(h_i\), the two products would have
unequal valuations, and their difference would be nonzero with
valuation exactly \(h_i\). This would make the index critical.
Thus a nonzero correction can still enforce the full valuation drop;
its magnitude alone does not identify a reset.

The odd gaps are exactly at \(u=o-1\) and \(w=L-1\), with
\(\sigma(u)=w\). The special indices behave as follows:

- At \(a-1\), the source gap is even and the correction is odd,
  so this index is not critical.
- At \(u\), both consecutive lifted gaps are odd. The odd numerator
  and odd denominator make \(r_u\) even, so this index is not critical.
- At \(w\), the source gap is odd and \(B_w\ell_{\sigma(w)}\) is even.
  The correction is odd, so this index is critical.

Every other denominator is even. Consequently the valuation strictly
drops at every ordinary noncritical edge.

A useful level-by-level form is obtained by writing
\(n_k=\#\{i:h_i=k\}\) and
\(C_k=\#\{i:i\hbox{ critical},\ h_i=k\}\). For every \(k\ge1\),
each noncritical vertex of height \(k\) exits the set \(h\ge k\).
Permutation invariance balances exits with entries; every entry starts
at a critical vertex below level \(k\). Hence
\[
n_k\le\sum_{j=0}^k C_j,\qquad C_0=1.
\tag{RC74}
\]
In particular \(L-2\le H C\). This already improves the old reset
count, but discards the actual size of the gaps.

**Remove the two odd gaps, then split at critical edges.**
Contract the consecutive vertices \(u,w\) in the rank-rotation cycle.
The remaining \(N=L-2\) vertices are all even positive gaps.
The new edge from \(a-1\) to \(e-1\) is declared a reset; it replaces
the path through \(u,w\), whose only critical edge starts at \(w\).
All other critical edges are retained. There are therefore exactly
\(C\) reset edges and \(C\) nonempty blocks, with lengths
\[
n_1+\cdots+n_C=N.
\]
Every block interior is an unchanged consecutive segment of the original
rotation. No denominator formula is assigned to the contracted edge.

A block of \(n\) even gaps has at least the elementary cost
\(2(2^n-1)\): its valuations strictly decrease and end at least at one.
The old three-boundary count did not combine these costs against one
common size budget.

**The actual itinerary increases the block cost.**
Consider a suffix of a block containing \(d\ge1\) transitions.
Its first \(d-1\) target gaps have valuation at least two. If such a
target rank is even-source, its two actual endpoints are even and
their difference is divisible by four. Their sum is then divisible
by four as well, so the associated denominator contributes at least
two valuation units.

For \(\sigma(i)=i+e\bmod L\), being an even-source rank is exactly
the carry in adding \(e\), since \(o=L-e\). A consecutive
\(\sigma\)-orbit segment of \(k\) ranks has either \(\lfloor ke/L\rfloor\) or
\(\lceil ke/L\rceil\) even-source ranks. Applying this to those
first \(d-1\) targets gives
\[
h_{\mathrm{start}}\ge d+1+\left\lfloor\frac{(d-1)e}{L}\right\rfloor.
\tag{RC75}
\]
The segment excludes both odd-gap vertices, so all sums here use
ordinary actual state pairs. The cut's polynomial lift is never
treated as an odd step from an even state.

Define, for \(n\ge0\),
\[
F(n)=\sum_{d=0}^{n-1}2^{f(d)},\qquad
f(0)=1,\quad
f(d)=d+1+\left\lfloor\frac{(d-1)e}{L}\right\rfloor\ (d\ge1).
\]
A positive integer of valuation at least \(f(d)\) is at least
\(2^{f(d)}\). Summing RC75 over all suffixes of a block and then
over the \(C\) blocks gives
\[
\boxed{m^3-m\ge4+\sum_{j=1}^{C}F(n_j).}
\tag{RC76}
\]
The additive four uses \(\ell_u\ge3\) and \(\ell_w\ge1\).
For the first inequality, the last odd state satisfies
\(c_{o-1}\le m^2-2\), and the first even state satisfies
\(c_o\ge m^2+1\). The simpler additive two would also give the
numerical conclusion below.

**Merge the block costs by a convex inequality.**
The increments \(F(n+1)-F(n)=2^{f(n)}\) increase with \(n\).
Moving one unit of length from a longer block to a block at least
two shorter therefore cannot increase total cost. With
\(q=\lfloor N/C\rfloor\) and \(r=N-qC\),
\[
m^3-m\ge4+(C-r)F(q)+rF(q+1).
\tag{RC77}
\]
This is a necessary bound for the actual cycle. Balancing makes the
bound exact for the reduced block-cost problem; it does not assert
that balanced blocks realize the joint integer cells.

An equivalent family of useful certificates avoids division by the
unknown critical count. For any fixed \(q\ge1\), put
\[
D_q=F(q+1)-F(q),\qquad B_q=qD_q-F(q)>0.
\]
Increasing increments give \(F(n)\ge nD_q-B_q\) for every \(n\).
Consequently
\[
\boxed{C B_q+(m^3-m)\ge (L-2)D_q+4.}
\tag{RC78}
\]
This merges the entire cycle's arithmetic and size constraints;
it does not assign an independent height budget to each block.

**Stronger fixed-count restriction.**
At \((L,o,e)=(780239,492276,287963)\), the established upper
cutoff and odd minimum give \(m\le519999999\). Use \(q=53\):
\[
F(53)=4387864922893216308702,\qquad
F(54)=13832597888632506736094,\qquad D_{53}=2^{73}.
\]
For \(C=14568\), the affine lower bound for total gap size is
\[
140736429407066024231149876,
\]
strictly exceeding the allowed budget
\[
519999999^3-519999999
=140607999188800001040000000.
\]
The coefficient \(B_{53}\) is positive, so every smaller \(C\)
also fails. Thus
\[
\boxed{C\ge14569,\qquad T\ge14571.}
\tag{RC79}
\]
Only the wrap can be critical among the three source-type boundaries:
the other two are explicitly excluded above. Away from those
boundaries, a critical correction requires a deviation at one of its
two adjacent source ranks. Therefore \(C\le1+2S\), for deviations
from any chosen three typewise constants, and
\[
\boxed{S\ge7284.}
\tag{RC80}
\]
Choosing each block's actual minimum remainder gives at least
\(14568\) excess raw square-remainder units. This strengthens the
previous \(S\ge4483\); it does not count distinct remainder values.
The intermediate parity/gap-budget fusion, without RC75's itinerary
information, already gives \(S\ge5390\). These are successive
combinations of constraints, not separate searches over cycle states.

**What splitting into signed groups does and does not yield.**
Let \(y_i=c_{\sigma(i)}\), \(Z=\log\log\), and let \(\beta_t\)
be the actual minimum remainder in source-type block \(t\). Put
\[
b_i=Z(y_i^2+\beta_t)-Z(y_i^2),\qquad
w_i=\frac1{(y_i+1)^2\log((y_i+1)^2)}.
\]
The exact defect increment is the integral of \(Z'\) from
\(y_i^2+\beta_t\) to \(y_i^2+R_i\). Each deviation supplies at
least two raw units, below the strict upper square endpoint. If
\(w_{(j)}\) are the weights in increasing order and \(s_0\le S\),
then
\[
\Lambda>\sum_i b_i+2\sum_{j=1}^{s_0}w_{(j)}
\quad(s_0\ge1).
\tag{RC81}
\]
This is a valid unsigned, target-normalized consequence.

The support count by itself gives, for any selected union \(A\) of
rank bins, only
\(\#(\mathrm{deviations}\cap A)\ge\max(0,s_0-|A^c|)\).
Refining and remerging the partition does not improve that projection.
At the fixed tuple, the neutral signed-loss group has 176251 positions.
Its intersection with some source type has at least 58751 positions,
so it can accommodate all 7284 deviations in the support-only model.
The affected type still has a strict majority at its baseline value;
the quantifier over all three chosen constants is respected.
This is not an actual source-cell or critical-block realization.

The mandatory first two units at any \(s_0=7284\) deviation positions
have total exact defect cost at most
\(s_0/(m^2\log m)<5\cdot10^{-15}\) at the established lower floor.
Thus this minimum additional charge alone cannot bridge the old
signed-cap clearance, which exceeds \(10^{-6}\). Actual excesses
can be larger, and the three unknown block minima are not bounded
above by this calculation. Their location, amplitude and correlations
with the signed coefficients remain essential.

**Verification and scope.**
The [fixed integer controls](../../data/research/juggler/cycle_rank_curvature/constraint_fusion_controls.json)
evaluate the two adjacent critical-count
budgets and the earlier elementary run cost. They also check small
rotation visit counts and valuation-transport examples. No source,
minimum, orbit or interval census was run.

The laboratory module [CubicConstraintFusion.lean](../../formal/Problems/Juggler/CubicConstraintFusion.lean) formalizes
the noncritical arithmetic transport, the extra divisibility from even
state pairs, weighted run telescoping, and the finite block-budget
and numerical implications described in its declaration signatures.
The extraction of blocks from an actual cubic cycle, the use of
mechanical visit counts on those blocks, and the complete assembly
RC76--RC80 remain the written argument above. Independent AI audits
agree; independent human review remains outstanding.

**Decision: PROMOTE** the merged critical-run gap-budget restriction.
The support-only signed partition shortcut is closed; the full
signed integer-cell problem remains open. No count pair is excluded,
and no descent floor or period bound is changed. Paper A and every
PDF artifact remain unchanged.

### 21. Rank ceilings force frequent critical events in the selected pairs

The authorized continuation merges the critical-run inequality with the
absolute rank envelopes. It answers a placement question that the support
count alone could not answer: some compulsory variation must occur in
the selected signed comparison. All conclusions in this section assume
the actual primitive cubic-cycle hypotheses of Results 19--20 and the
fixed counts
\[
(L,o,e)=(780239,492276,287963).
\]
The established minimum window gives the odd bound
\(350000000<m\le m_*=519999999\). Retain the positive lifted gaps
\(\ell_i\), their valuations \(h_i\), the critical count \(C\), and
the contracted even-gap blocks from Result 20. No cycle satisfying these
hypotheses has been constructed.

**Two absolute gap ceilings.** Put
\[
\Lambda=o\log3-L\log2,\quad \alpha=\frac{\log3}{L},\quad
\Omega=\left(1-\frac1L\right)\Lambda,\quad \Gamma=\alpha+\Omega.
\]
The existing sharp log-log grid gives an adjacent log-log gap at most
\(\Gamma\), including its lifted seam. For an ordinary adjacent gap,
with upper endpoint \(z=c_{i+1}\), integration of the decreasing
derivative \(Z'(x)=1/(x\log x)\) gives
\[
\frac{\ell_i}{z\log z}\le Z(c_{i+1})-Z(c_i)\le\Gamma.
\tag{RC82}
\]
The anchored grid also implies
\[
c_j\le U_j:=\exp\bigl(\log(m_*)\exp(j\alpha+\Omega)\bigr).
\]
Both \(U_j\) and \(z\log z\) increase at the positive states in
question. Define
\[
a=L-2e=204313,\qquad b=3e-L=e-a=83650.
\]
Outward interval evaluation at these two prescribed boundaries yields
\[
\begin{aligned}
\Gamma U_a\log U_a&<54601376.830<2^{26},\\
\Gamma U_b\log U_b&<704007.113<2^{20}.
\end{aligned}
\tag{RC83}
\]
The [scalar certificate](../../data/research/juggler/cycle_rank_curvature/critical_location_controls.json)
retains exact dyadic endpoints, with outward decimal displays.
Only these two rank boundaries are evaluated; there is no rank scan.
For \(i<a\), the upper endpoint has rank \(i+1\le a\); similarly
\(i<b\) has endpoint rank at most \(b\). A positive integer smaller
than \(2^{H+1}\) has binary valuation at most \(H\). Thus
\[
i<a\Longrightarrow h_i\le25,\qquad
i<b\Longrightarrow h_i\le19.
\tag{RC84}
\]
These bounds cover every indicated source gap, including the last gap
before each boundary; they are not bounds only at the two endpoints.

**Every critical-free even block has at most 21 vertices.** RC75 says
that a suffix with \(d\) transitions has initial height at least
\[
f(d)=d+1+\left\lfloor\frac{\max(d-1,0)e}{L}\right\rfloor.
\]
In particular \(f(19)=26\) and \(f(15)=21\). If a block suffix
starts below \(a\), it cannot have 19 remaining transitions, so it
has at most 19 vertices. If its first rank satisfies \(a\le i<e\),
then
\[
\sigma(i)=i+e,\qquad \sigma^2(i)=i-a<b.
\]
If two transitions remain, the suffix after them has at most 15
vertices by the second cap in RC84. The original suffix therefore has
at most 17 vertices. Shorter suffixes satisfy the same bound directly.

Every three consecutive rotation vertices meet \([0,e)\). Indeed,
if \(i\ge o\), then \(\sigma(i)=i-o<e\); if \(e\le i<o\),
then \(\sigma^2(i)=i-a\in[b,e)\). These cases, together with
\(i<e\), cover all ranks. All tested edges lie inside one block,
so they are unchanged ordinary rotation edges, not the synthetic
contracted reset. At most two vertices precede a low rank, and its
suffix has at most 19 vertices. Consequently
\[
\boxed{n_j\le21\quad\hbox{for every contracted even-gap block}.}
\tag{RC85}
\]
Since the \(C\) nonempty blocks partition \(L-2=780237\) vertices,
Result 20's additional-correction and support inequalities give
\[
\boxed{C\ge37155,\qquad T\ge37157,\qquad S\ge18577.}
\tag{RC86}
\]
Here \(S\) counts deviations from any chosen one remainder constant
for each of OO, OE and EO. Choosing actual type minima forces at least
\(37154\) raw excess remainder units. These are stronger necessary
conditions than RC79--RC80; neither set excludes the count tuple.

**The signed arcs must contain many of those events.** Use chronological
time \(t\), so its source rank is \(i_t=te\bmod L\). Set
\[
k=e^{-1}\bmod L=478245,\quad r=L-k=301994,\quad h=2k-L=176251.
\]
The three chronological groups in the signed-loss identity are
\[
P=[0,h),\qquad Q=[h,k),\qquad R=[k,L).
\]
They are consecutive time arcs, not consecutive sorted-rank intervals.
The three exceptional source ranks \(a-1,o-1,L-1\) occur at times
\(r-2,r-1,r\), respectively, all in \(Q\). Therefore every edge
with source time in \(R\) is ordinary and joins two retained even-gap
vertices; the last such edge ends at time zero, also ordinary.

If 21 consecutive source positions in \(R\) contained no critical
event, their 21 edges would join 22 vertices within one noncritical
block, contradicting RC85. Partitioning the \(301994\) positions of
\(R\) into disjoint full windows of width 21 proves
\[
\boxed{C_R\ge\left\lfloor\frac{301994}{21}\right\rfloor=14380.}
\tag{RC87}
\]
The unassigned tail has 14 positions. The critical wrap, which was
replaced by the synthetic reset, belongs to \(Q\), so it cannot pay
for any of these \(R\) windows.

For \(t\in R\), the source of adjacent rank \(i_t+1\) occurs at
time \(t+k\bmod L\). Translation by \(k\) maps \(R\) bijectively
to \(Q\), since its endpoints become \(h\) and \(k\). Hence these
are disjoint pairs, each consisting of one \(R\) and one \(Q\)
position. Absence of the three boundaries ensures that both endpoints
have the same OO/OE/EO source type. These are the same paired actual
edges used in RC34--RC38, not newly selected comparison pairs.

At every critical \(R\) source, the ordinary recurrence gives
\[
r_{i_t}=R_{i_t+1}-R_{i_t}\ne0.
\]
At least one member of each pair differs from its chosen type constant.
Disjointness prevents a single deviation from serving two pairs. Thus,
for every choice of the three constants,
\[
\boxed{S_{Q\cup R}\ge C_R\ge14380.}
\tag{RC88}
\]
Within each source type, raw remainders have fixed parity, so every
nonzero paired difference has absolute value at least two. Consequently
the absolute differences over the critical \(R\) pairs sum to at
least \(28760\). For the actual type minima \(\beta_t\), the
two nonnegative excesses in a pair sum to at least its absolute
difference. Disjointness then gives
\[
\boxed{\sum_{i:\,\operatorname{time}(i)\in Q\cup R}
 (R_i-\beta_{\operatorname{type}(i)})\ge28760.}
\tag{RC89}
\]
This rules out placing all deviations in the neutral group under the
full hypotheses of this result. The earlier all-neutral construction
remains a valid control for its explicitly weaker support-only model.

**Criticality still does not determine the helpful sign.** The exact
OO triple RC46--RC48, valid for every odd \(t\ge9\), already has
input gaps 4 and raw remainders \((12t^2-64,0,12t^2+64)\). Its
adjacent corrections are
\[
-4(3t^2-16),\qquad 4(3t^2+16).
\]
Both have valuation two, the valuation of the source gap, so both
are critical. Their normalized slack differences have opposite signs
by RC48. At \(t=9\), the genuine parallel cells are
\(77,81,85\mapsto675,729,783\), with remainders \(908,0,1036\).
They are not claimed to belong to one cycle. This refutes a local
critical-implies-helpful-sign rule, while leaving a global signed
estimate open. Unequal raw remainders by themselves also need not imply
unequal log-log defects, because their targets differ.

**Verification and scope.** The laboratory module
[CubicCriticalLocation.lean](../../formal/Problems/Juggler/CubicCriticalLocation.lean)
proves the positive-gap valuation ceiling, the 21-vertex finite-path
bound, its numerical counting consequences, generic window hitting,
and disjoint-pair deviation transfer. The finite-path theorem explicitly
requires the rank path, both valuation caps and every-suffix cost.
The localized consumers explicitly require window hitting, interval
membership and disjoint responsible pairs where used. These signatures
do not silently assume a completed actual-cycle extraction.

The real interval comparisons, extraction of the contracted blocks,
mechanical suffix costs and actual selected-pair assembly remain the
written argument above and in Result 20. Independent AI audits agree;
independent human mathematical review remains outstanding. The fixed
scalar replay and exact integer controls accompany the Lean kernels.
No minimum, orbit or rank census, cap reintegration or further interval
propagation was performed.

**Decision: PROMOTE** the bounded-run and selected-pair localization
theorem. The remaining input is a signed, target-normalized bound on
these compulsory pairs. No count pair or cycle class is excluded, and
no descent floor, period or escape statement changes. Paper A and all
PDF artifacts remain unchanged.

### 22. Critical correction cost and shared two-step cells

The user authorized two attacks: an arithmetic charge for compulsory
critical corrections, and stronger exact-cell propagation using critical
windows. The bounded gate retains the same actual states in every
equation. It uses symbolic family calculations, a few exact controls and
the saved marginal-domain summary; no full propagation sweep, minimum
subdivision, rank census or cap integration is added.

**Criticality and its exact residue class.** For positive \(N,B,\ell,\ell'\),
with \(N\) odd and \(r=N\ell-B\ell'\), put
\(h=v_2(\ell)\) and \(w=v_2(B)+v_2(\ell')\). Binary valuation gives
\[
r\ne0\ \hbox{and}\ v_2(|r|)=h
\quad\Longleftrightarrow\quad h<w.
\tag{RC90}
\]
If the two product valuations differ, their difference takes the smaller
valuation. If they agree, division by their common power of two leaves
two odd integers, whose difference is even. This proves both directions,
including the zero-correction case.

At a critical index let \(d=w-h>0\), \(u=\ell/2^h\), and
\(v=B\ell'/2^w\), both odd. The recurrence becomes
\[
\frac r{2^h}=Nu-2^dv
\equiv Nu-2^d\pmod{2^{d+1}}.
\tag{RC91}
\]
Thus its absolute scaled size is at least the least absolute residue
\(\rho=\operatorname{dist}(Nu-2^d,2^{d+1}\mathbb Z)\ge1\).
This refines the congruence modulo \(2^d\), but does not itself force
\(\rho\) to grow.

There is a rigorous conditional conversion to the total loss budget.
For each of the disjoint critical \(R/Q\) pairs of Result 21, use its
ordinary correction, height \(h_i\), residue distance \(\rho_i\), and
larger target \(y_i^+\). Both raw remainders are nonnegative, so their
sum is at least their absolute difference, hence at least
\(2^{h_i}\rho_i\). Integration of \(Z'(x)=1/(x\log x)\), below
the two strict upper-square endpoints, then yields
\[
\Lambda>
\sum_{i\in\mathcal C_R}
\frac{2^{h_i}\rho_i}
 { (y_i^++1)^2\log((y_i^++1)^2)}.
\tag{RC92}
\]
The pairs are disjoint, so no edge loss is counted twice. All coefficients
and residues here belong to the actual common cycle. This is a conditional
charge formula, not a new lower estimate for its right-hand side. Replacing
every \(\rho_i\) by one recovers the existing elementary quantization.

**The smallest possible correction can restore arbitrarily much valuation.**
For every integer \(s\ge1\), the neighboring odd sources
\[
x_\pm=4s^2\pm1,
\qquad O(x_\pm)=y_\pm=8s^3\pm3s
\tag{RC93}
\]
have exact remainders \(R_\pm=3s^2\pm1\). The two upper-cell margins
are \(16s^3-3s^2-6s+2\) and \(16s^3-3s^2+6s\), both positive.
For example substituting \(s=1+t\) gives polynomials with strictly
positive coefficients. Thus the displayed floor identities hold for
every stated parameter, not only asymptotically.

Their source gap is two, target gap \(6s\), and correction \(r=2\).
Moreover \(N=48s^4+1\), \(B=16s^3\). If \(k=v_2(s)\), the gap
valuation increases by \(k\), while \(d=4+4k\). The exact scaled
correction and the refined residue distance in RC91 both equal one.
Odd \(s\) gives OO pairs; even \(s\) gives OE pairs. Therefore no
charge growing solely with valuation restoration holds for individual
genuine O pairs.

Writing \(\eta(y)=Z(y+1)-Z(y)\), their individual O losses satisfy
\(\delta_\pm/\eta(y_\pm)<6/(5s)\), hence tend to zero. To see this,
put \(\theta=\sqrt{y^2+R}-y\in(0,1)\). The square factors cancel in
\(Z\), and the decreasing derivative gives
\(\delta/\eta(y)<3\theta\le3R/(2y)\) for \(y\ge2\).
Here \(R\le4s^2\) and \(y\ge5s^3\).

The even-\(s\) examples fail an additional cycle requirement. For
\(s\ge2\), \(y_->9s^2\), so
\[
\sqrt{y_+}-\sqrt{y_-}
=\frac{6s}{\sqrt{y_+}+\sqrt{y_-}}<1.
\]
The next E images are equal or consecutive; they cannot be distinct
odd selected states. At \(s=6\), both actual guarded paths end at the
same state: \(143\to1710\to41\) and \(145\to1746\to41\).
At \(s=2\), the endpoints are 7 and 8, with a parity failure.
The first example lies within the cubic band anchored at 41, but cannot
be two distinct return paths on a periodic set because of its collision.

**A positive cost theorem for the symmetric family.** More generally,
let \(s\ge2\), let \(a\) be positive odd with \(a\le s\), and put
\[
x_\pm=4s^2\pm a,\qquad y_\pm=8s^3\pm3sa.
\]
Assume both displayed O cells are exact, both \(y_\pm\) are even,
and their E images \(t_-<t_+\) are distinct odd integers. The O-cell
hypothesis is essential: \(a\le s\) alone does not imply it.
Exact expansion gives \(R_\pm=3s^2a^2\pm a^3\) and \(r=2a^3\).

For any even inputs \(Y<Y+D\) with distinct odd E images \(t<q\),
parity sharpens the cells to
\(Y\le(t+1)^2-2\) and \(Y+D\ge q^2+1\). Since \(q\ge t+2\),
\[
D\ge2t+6,\qquad D^2>4Y.
\tag{RC94}
\]
Apply this to \(D=6sa\), \(Y=8s^3-3sa\). It gives
\(9sa^2+3a>8s^2\), which implies \(3a^2>2s\): otherwise
\(a\le a^2\le2s/3\) makes the left side at most
\(6s^2+2s\le8s^2\). Consequently
\[
27r^2>32s^3,\qquad R_->s^3,
\qquad
\boxed{\frac{\delta_-}{\eta(y_-)}>\frac1{23},\quad
       \frac{\delta_+}{\eta(y_+)}>\frac1{23}.}
\tag{RC95}
\]
For the last inequalities, \(a\le s\) gives
\(R_-\ge2s^2a^2>s^3\), \(R_+\ge R_-\), and
\(2y_++1\le23s^3\). Concavity of \(Z\) gives the exact lower comparison
\[
\frac{\delta}{\eta(y)}\ge\theta
=\frac{R}{\sqrt{y^2+R}+y}>\frac{R}{2y+1}.
\]
The compatible control \(61\to476\to21\), \(67\to548\to23\)
uses \(s=4,a=3\), with remainders 405 and 459 and correction 54.
It verifies that the family hypotheses are nonempty. This is a family
theorem, not a uniform charge for arbitrary critical OE pairs.

**Complete guarded OE pairs can nevertheless remain cheap.** The already
established RC61 family supplies the necessary contrasting control:
for every odd \(b\ge3\),
\[
b^4+2\longmapsto b^6+3b^2\longmapsto b^3.
\tag{RC96}
\]
Pair it at odd \(b<c\). The O remainder is \(3b^4+8\), so the
paired O correction is exactly \(3(c^4-b^4)\), three times its
source gap. It is therefore critical. Both complete returns have
distinct odd endpoints. The previous normalized bounds
\(6/b^2\) on O and \(9/(2b)\) on E show that all four normalized
losses tend to zero along \(c=b+2\), \(b\to\infty\).
Thus even complete OE guards, injectivity and criticality do not imply
a universal positive normalized charge.

These paired paths also fit one common cubic band anchored at \(m=b^3\)
when \(c=b+2\). Indeed \(c\le5b/3\), and elementary power comparisons
give \(c^4+2<b^6\), \(c^6+3c^2<b^9\). The control
\(83\to756\to27\), \(627\to15700\to125\) lies in the band
anchored at 27. The paths do not constitute a cycle or establish
adjacency in a complete sorted cycle.

**The fixed rank grid excludes that particular cheap family from adjacent
positions.** At the counts and minimum window of Result 21, suppose two
O sources from RC96, with odd \(3\le b<c\), were adjacent sorted states.
Let \(z=c^4+2\) be the larger source. The cubic odd-state cutoff gives
\(z<m^2\), hence \(c<23000\). Also
\(z<520000000^2<2^{58}\), so \(\log z<41\), using
\(\log2<7/10\). The already certified \(\Gamma<1/200000\) and RC82
would give
\[
c^4-b^4\le\Gamma z\log z<z/4800.
\tag{RC97}
\]
But the reverse strict inequality holds arithmetically throughout this
parameter range. At \(c=5\), necessarily \(b=3\), and it is immediate.
For \(c\ge7\), odd spacing gives \(b\le c-2\), and
\[
c^4-b^4\ge c^4-(c-2)^4>5c^3,
\qquad z<(c+1)c^3\le23000c^3<4800\cdot5c^3.
\]
The first strict inequality follows by writing \(c=u+7\): its difference
from \(5c^3\) is \(3u^3+39u^2+137u+61>0\).
This contradicts RC97. Thus two distinct O sources of the RC61 family
cannot form one adjacent source pair in the fixed cubic regime. This is
a corollary of the existing grid, not an exclusion of the count tuple.
It shows why a fully guarded open family is still insufficient as a
counterexample to a bound requiring actual adjacent cycle states.

**Critical-window propagation: what the saved domains can establish.**
On every ordinary same-type pair, \(v_2(\ell_i)=1\) already forces
criticality: the target product is a difference of same-parity squares,
which is divisible by four. Consider the shared state-residue pattern
\[
c_i\equiv
\begin{cases}1+2i&i<o,\\2(i-o)&i\ge o\end{cases}\pmod4.
\tag{RC98}
\]
Every ordinary source gap then has valuation one. All selected \(R\)
positions are critical, satisfying every 21-source window and both
pointwise upper valuation caps. Remainder congruences use these same
state residues. This is a simultaneous modular projection, not an exact
integer-cell or sorted-grid realization.

The four-sweep record saved eight sample domains and the aggregate
minimum width 169999990, not the full domain arrays. Every marginal
parity interval of that width supports its prescribed class modulo four;
the eight saved examples confirm the endpoint convention. Adding two
to either parity block's residue phase preserves all ordinary gap
heights. For any value of any one marginal variable, choose that
block's phase to match it; all other marginal intervals support the
required phases. Thus every marginal value has support in this modular
projection with all selected events critical. These window clauses
alone do not prune that relaxation. This argument omits the joint
integer order, real grid values, exact floor equalities and loss budget.
An all-undecided Boolean window also remains unchanged; twenty forced
noncritical positions would force its remaining position critical, and
twenty-one would yield a contradiction. No such collection of forced
noncritical positions has been derived from the saved domains.

The exact two-step inequality RC94 rejects the collision/parity controls
and preserves the compatible pair. It expresses constraints already
present in the complete integer-cell system and may serve as a direct
propagation rule. No whole minimum interval was eliminated in this gate;
the unavailable full arrays were not reconstructed or swept again.

**Verification and decision.** The [fixed controls](../../data/research/juggler/cycle_rank_curvature/critical_cost_controls.json)
retain the genuine pairs, the successful symmetric cost example, and
the explicitly weaker residue/window projection. The laboratory module
[CriticalCostKernel.lean](../../formal/Problems/Juggler/CriticalCostKernel.lean)
verifies RC90, the integer two-step separation implication, the supplied
symmetric-cell raw-cost consequence, and the quartic parameter-gap
inequality used in RC97. Its hypotheses are explicit; the real logarithmic
comparisons, infinite-family proofs and complete cycle applications remain
written arguments. Independent AI audits agree; independent human review
remains outstanding.

**PROMOTE** the conditional symmetric-family cost and the fixed-regime
adjacency exclusion for RC61, with the reusable arithmetic interfaces.
**CLOSE** the proposed standalone restoration-cost inference and the
window-only enhancement of the stated relaxation. The general joint
residue-cost estimate and complete integer-cell elimination remain
**PARK** at this gate. No count pair is excluded, no floor
or period changes, and Paper A and all PDFs remain unchanged.

### 23. Complete paired OOE returns and finite square-start packing

The authorized continuation first consolidates CriticalCostKernel, retaining
its existing public statements and adding actual-root and polynomial cost
consumers. It then asks whether the exact OOE continuation of a cheap
critical OO pair, together with simultaneous adjacent-gap ceilings, forces
a useful aggregate loss. The answer separates two issues: there is no
uniform positive local charge even for these paired returns, whereas the
finite rank window limits the number of exactly lossless first steps.
Neither statement settles complete cyclic selection.

**The same two paths at every step.** For odd integers \(s\ge3\), put
\[
x_\pm=4s^2\pm1,\qquad u_\pm=8s^3\pm3s,\qquad
A_\pm=u_\pm^{3/2},\quad B_\pm=u_\pm^{3/4}.
\tag{RC99}
\]
Result 22 gives the exact first O cells, with both \(x_\pm,u_\pm\)
odd, raw remainders \(3s^2\pm1\), and paired correction exactly two.
The source gap is two, so this correction is critical and has the smallest
possible nonzero magnitude for an ordinary same-type pair. These first O
losses, divided by their respective caps, are below \(6/(5s)\).

Define \(v_\pm=\lfloor A_\pm\rfloor\) and
\(z_\pm=\lfloor B_\pm\rfloor\). The exact identity
\(\lfloor\sqrt{\lfloor A\rfloor}\rfloor=\lfloor\sqrt A\rfloor\)
shows that \(E(v_\pm)=z_\pm\). To obtain two actual OOE returns it
remains to impose the even parity of \(v_\pm\) and the odd parity of
\(z_\pm\); these guards are not assumed to hold for every odd \(s\).

**Four simultaneous smooth phases.** The sequence
\[
\left(\frac{A_-}2,\frac{A_+}2,\frac{B_-}2,\frac{B_+}2\right)
\quad(s=2n+1)
\tag{RC100}
\]
is uniformly distributed modulo one in the four-dimensional unit cube.
Here is the full noncancellation check. With \(K=2^{9/4}\), the binomial
expansions are
\[
\begin{aligned}
A_\pm&=16\sqrt2\,s^{9/2}\pm9\sqrt2\,s^{5/2}
       +\frac{27\sqrt2}{32}s^{1/2}+O(s^{-3/2}),\\
B_\pm&=K s^{9/4}\pm\frac{9K}{32}s^{1/4}+O(s^{-7/4}).
\end{aligned}
\tag{RC101}
\]
The expansions can be differentiated any fixed number of times, with the
corresponding differentiated remainder bounds: they are convergent analytic
binomial expansions in \(3/(8s^2)\) on every sufficiently large dyadic
interval.

For a nonzero integer frequency \((h_-,h_+,k_-,k_+)\), examine its scalar
combination of RC100. If \(h_-+h_+\ne0\), the leading exponent is
\(9/2\). If that sum vanishes but the \(h\)'s are nonzero, their
difference is nonzero and the leading exponent is \(5/2\). Otherwise
the \(h\)'s both vanish; the leading exponent is \(9/4\) when
\(k_-+k_+\ne0\), and \(1/4\) in the final nonzero case. In
particular there is no nonzero frequency with all four modes cancelled.

Apply the derivative estimate in
[Robert, Theorem 3](https://perso.univ-st-etienne.fr/rool6510/robert-2015-indag.pdf)
on \(N<n\le2N\), with derivative order \(5,3,3,2\), respectively.
The four bounds for the exponential sum divided by \(N\) are
\[
\begin{array}{c|c}
\text{leading exponent}&\text{normalized bound, fixed frequency}\\\hline
9/2&O(N^{-1/60}+N^{-13/120})\\
5/2&O(N^{-1/12}+N^{-5/12})\\
9/4&O(N^{-1/8}+N^{-3/8})\\
1/4&O(N^{-7/8}+N^{-1/8}).
\end{array}
\tag{RC102}
\]
All tend to zero. Dyadic summation and the multivariate Weyl criterion
give RC100. This applies smooth phases only, with each frequency and target
box fixed. It supplies no uniform shrinking-box discrepancy estimate or
effective hit inside the current fixed minimum interval.

**Arbitrarily cheap distinct complete OOE pairs.** Fix \(0<\epsilon<1\).
The phase box
\[
(0,\epsilon/2)^2\times
(1/2,(1+\epsilon)/2)^2
\tag{RC103}
\]
has volume \(\epsilon^4/16\), so it contains the phases of arbitrarily
large odd parameters. At each such parameter, both \(v_\pm\) are even,
both \(z_\pm\) are odd, and
\[
0<A_\pm-v_\pm<\epsilon,\qquad
0<\sqrt{v_\pm}-z_\pm\le B_\pm-z_\pm<\epsilon.
\]
The last strict positivity follows from the opposite parities of
\(v_\pm\) and \(z_\pm^2\). RC54 bounds each of the four later
cap-normalized losses by \(3\epsilon\). The first two normalized
losses tend to zero independently of these phases.

Moreover
\[
B_+-B_-\sim\frac{9K}{16}s^{1/4}\longrightarrow\infty.
\tag{RC104}
\]
Consequently the odd returns \(z_-<z_+\) are distinct for every
sufficiently large selected parameter; the second O images are also
distinct. Power growth gives, eventually,
\[
x_-<x_+<z_-<z_+<u_-<u_+<x_-^2\le v_-<v_+<x_-^3.
\tag{RC105}
\]
Thus all eight states lie in the same cubic band anchored at \(x_-\),
with genuine OOE first returns to \([x_-,u_-)\). For every \(c>0\)
and height \(H\), choose \(\epsilon<c/3\) and then a sufficiently
large selected parameter: both paths start above \(H\), their initial
paired correction is two, and all six individual cap-normalized losses
are less than \(c\). This is a paired open-path theorem, not a cycle or
an unbounded orbit.

**Simultaneous rank placement remains an additional obligation.** In the
fixed cubic regime, write \(a=o-e=204313\) and
\(b=3e-L=83650\). Two ordinary adjacent OOE sources have ranks
\(i,i+1\) with \(0\le i\le a-2\). Their four successive pair gaps
occupy ranks
\[
i,\qquad i+e,\qquad i+2e,\qquad i+b.
\tag{RC106}
\]
The third transition wraps once; the endpoints still remain adjacent.
These are four gaps in the same complete sorted vector, not independently
chosen paths. For the open pairs in RC99, all four actual log-log gaps
are asymptotic to \(1/(4s^2\log s)\). They therefore meet any fixed
positive gap ceiling for sufficiently large \(s\).

A coarse bound includes every floor error explicitly. For \(s\ge5\),
\(x_->3s^2\) and \(5s^3<u_-<u_+<16s^3\). The first two
log-log gaps are below \(2/(3s^2)\) and \(6/(5s^2)\), respectively.
The mean value theorem and an error of less than one from the floors give
\[
v_+-v_-<37s^{5/2},\quad v_->10s^{9/2},\qquad
z_+-z_-<\tfrac{11}{2}s^{1/4},\quad z_->2s^{9/4}.
\]
For example \(A_+-A_-<36s^{5/2}\),
\(A_->11s^{9/2}\), \(B_+-B_-<(9/2)s^{1/4}\), and
\(B_->3s^{9/4}\) imply those four inequalities. Every lower
endpoint has logarithm greater than one, so the last two log-log gaps
are below \(37/(10s^2)\) and \(11/(4s^2)\). All four gaps are
therefore strictly below \(4/s^2\).

Whenever \(x_->350000000\), one has
\(s^2>87500000>4L\), hence \(4/s^2<1/L<\Gamma\).
Thus any guarded pair from this family at that scale passes all four
isolated upper-gap tests. There is still no assertion of a phase hit
inside the fixed minimum window or a full rank vector with the
prescribed counts, loss budget and remaining states. Extending the
isolated ceiling test to all three transitions cannot by itself supply
a uniform positive local charge at unbounded height.

For an actual OOE start let
\(D_i=\delta_i+\delta_{i+e}+\delta_{i+2e}\). The exact paired
transport gives
\[
g_{i+b}=g_i+D_i-D_{i+1}.
\tag{RC107}
\]
Upper bounds on both gaps do not give a positive lower bound on both
block losses. The OOE blocks for \(i<a\), together with the OE blocks
for \(a\le i<e\), partition the complete cycle's edges, since
\(3a+2b=L\). A valid lower bound on these selected block costs would
therefore have an aggregate consumer without double counting. This is
the existing return partition and signed transport, not a new cost bound.

**Finite packing of exactly lossless first steps.** All of the first
\(b=83650\) ranks are OOE starts because \(b<a\). For them, the
previously certified boundary envelope gives
\[
m\le c_i<c_b\le U_b<6390543529.057.
\]
An odd source has zero first O remainder if and only if it is a square.
This classification is already formalized by
\(\texttt{Problems.Juggler.localDefectOdd_eq_zero_iff}\) and
\(\texttt{Problems.Juggler.floorPower_odd_sq_eq_cube_iff_square}\).
Thus the square root of any such source is an odd integer in
\[
18709\le t\le79939.
\tag{RC108}
\]
The endpoint checks use the saved rational enclosure: the first permitted
odd square root is 18709, and that enclosure lies between
\(79940^2\) and \(79941^2\). There are exactly
\((79939-18709)/2+1=30616\) odd parameters in RC108. Distinct selected
states have distinct square roots, hence
\[
\boxed{\#\{0\le i<83650:R_i>0\}\ge53034.}
\tag{RC109}
\]
The first targets are also odd, so each positive remainder is even and
at least two, giving at least 106068 raw first-O remainder units.
For comparison, the other saved boundary \(U_a\) admits 313986 odd
square parameters, more than its 204313 source ranks; it gives no
positive-count conclusion by this same argument. No new boundary was
evaluated. RC109 counts positive remainders, not deviations from the
actual OO type minimum, which might itself be positive.

Let \(u_i=c_{i+e}\) and
\(w_i=((u_i+1)^2\log((u_i+1)^2))^{-1}\). The weights decrease
with \(i\). Integration of the decreasing derivative of \(Z\) gives
\(\delta_i>R_iw_i\) when \(R_i>0\). The last 53034 indices
minimize the weight of any subset of that size. Consequently
\[
\sum_{i<83650}\delta_i>
2\sum_{i=30616}^{83649}w_i.
\tag{RC110}
\]
These are distinct first edges of actual OOE blocks. In particular,
\(U_b<80000^2\) gives \(u_i+1\le Y=80000^3=512000000000000\).
Since \(Y<2^{49}\) and \(\log2<7/10\),
\(\log(Y^2)<69\), hence
\[
\Lambda\ge\sum_{i<83650}\delta_i>
\frac{106068}{69\,(512000000000000)^2}
\approx5.86401897928\times10^{-27}.
\tag{RC111}
\]
The displayed rational lower bound is less than \(10^{-26}\), whereas
the saved surplus is greater than \(3\times10^{-6}\). This particular
comparison supplies no contradiction; it is not an upper bound on the
actual loss, nor a lower fraction of the later E caps.

**Consolidation and scope.** CriticalCostKernel retains all four original
declaration signatures. The criticality proof now reuses the existing
noncritical valuation budget. The square-cell geometry is separated from
its polynomial consequence, and actual \(\texttt{Nat.sqrt}\) consumers
provide their own cell witnesses while retaining the exit parities and
distinctness premises. Its new interfaces are
\(\texttt{even_sqrt_separation}\),
\(\texttt{symmetric_family_cost_of_separation}\),
\(\texttt{symmetric_family_sqrt_cost}\), and
\(\texttt{symmetric_unit_odd_cells}\).

The polynomial consumer proves \(3a^2>2s\),
\(27(2a^3)^2>32s^3\), the cubic lower remainder bound, and
\(2y_++1<23R_-\), filling the integer bridge behind the written
normalized \(1/23\) estimate. The unit-offset theorem proves both exact
prescribed O outputs and their raw remainder identities for every
\(s\ge1\). Three compiled consumer examples connect the interfaces to
actual square roots and the existing guarded OOE machinery. All eight
public declarations passed the exact-source dependency audit using only
standard logical dependencies. The real inequalities, four-phase
equidistribution, infinitude, and complete cycle packing remain written;
independent human review is outstanding.

The [fixed controls](../../data/research/juggler/cycle_rank_curvature/ooe_rank_cost_controls.json)
retain the original two dyadic enclosures and exactly eight prescribed
odd parameters, with integer cells, parity outcomes and rational phase
enclosures. Only \(s=19999\) gives two guarded OOE paths among these
controls. Its common-band minimum is 1599840003, outside the fixed
minimum window. The four tested parameters whose minima are inside that
window fail at least one guard. No further parameter was tested; this
does not prove any exclusion or infer infinitude from the controls.

**Decision.** The aggregate loss question remains **PARK**. The proposed
uniform positive local OOE-pair charge is **CLOSE**, including minimum
critical correction, distinct returns, a common cubic band, and isolated
upper-spacing constraints. The finite square-start packing consequence
and the consolidated integer interfaces are retained as structural
restrictions. No count pair is excluded and no source, minimum or rank
census, propagation sweep, cap integration, or PDF work was performed.

## Open questions

The unresolved input is a signed estimate retaining the common actual
integer states and their target-dependent floor caps. The complete fixed
envelope sums do not place RC9 within RC7. The exact adjacent-cap relation
reduces the remaining sign question to RC22 for the integer upper-cell
complements, with all shared-state constraints still imposed. Result 21 forces at least
18577 deviations globally and 14380 within the selected Q/R pairs at the
fixed counts. Result 22 derives an exact residue-distance charge but no
new lower bound for its total. It rejects specific cheap families through
shared E cells or adjacent-rank spacing; standalone criticality, even
with complete open OE guards, has no uniform positive charge. Result 23
extends that obstruction to distinct paired OOE returns with minimum
critical correction and simultaneous isolated gap ceilings. Finite
square-start packing forces 53034 positive first O remainders in the
first 83650 ranks, but supplies no useful total-loss comparison.
The remaining input must use simultaneous selection by the complete
cycle, beyond these local guards and spacing ceilings. The signed
weighted estimate in RC37--RC38 remains unresolved.

## Decision

Laboratory Lean wrappers for Results 15, 19 and 20 are registered and
do not change this decision: the equal-gap OO integer family is
kernel-checked, leftover height is assembled from a charge certificate,
and the Result 19/20 count consumers remain conditional on an explicit
cover or supplied block costs.

**PROMOTE** Result 21's bounded-run and selected-pair localization.
Combining two absolute rank gap ceilings with critical suffix costs
forces every contracted even-gap block to have at most 21 vertices.
At the fixed cubic count tuple, C>=37155, T>=37157 and S>=18577;
at least 14380 deviations lie in the disjoint selected Q/R pairs.
Choosing actual type minima gives at least 28760 raw excess units
there. The conditional finite-path and counting kernels are formalized;
the analytic ceilings and complete actual-cycle assembly remain written.
Criticality alone does not orient the normalized signed contribution.
Results 19--20 remain valid weaker restrictions.

Result 22 retains a conditional positive cost within a symmetric family
and excludes the separate RC61 cheap family from adjacent source ranks
at the fixed scale. Its exact valuation classifier and integer pair
interfaces are Lean verified. These conclusions exclude no count pair.
The standalone restoration-cost inference and the window-only marginal
enhancement are closed; the joint aggregate cost and complete-cell
elimination are PARK pending a new arithmetic restriction.

**PARK** the complete integer-cell feasibility continuation of Result 18.
Exact propagation is complete at a common fixed point, but the four-sweep
trial reached neither a fixed point nor an exclusion. A justified
acceleration or additional arithmetic restriction remains missing.

The automatic finite-difference transfer from the sorted grid and total
defect remains closed. The exact window is a re-expression of parity, and both
boundary curvatures survive the stated relaxation. The authorized complete
cap-sum continuation likewise fails its signed test, including the CW44
charge correction. More precise integration of these same envelopes
cannot close the proved gap. The fixed cutoff RC25 is retained as a
corollary of existing machinery, without promoting a new no-cycle mechanism.
The actual-complement continuation closes the tested product cancellation,
definition-only congruence elimination, and indicator-only weighting
shortcuts. The subsequent complete-word audit also closes independent
propagation of the same OO charge: RC41 is the prior cap box under an
exact change of variables. It retains the local Lean theorem RC26; its additional cap
improvement is insufficient. This is not a proof that every arithmetic
approach to actual upper-cell complements must fail.

The shared-state signed estimate in RC37--RC38 remains open. Result 15
rules out obtaining its orientation solely from equal adjacent gaps,
their gcd, or automatic three-point convexity. A further attempt needs a
nonlocal estimate linking absolute cell placement to the selected cycle
ranks; restating the missing signed bound is not a distinct attack.
Result 16 also supplies no such estimate: rank-polynomial determinants
retain the existing grid precision, while corrected matching recovers
rank rotation. Its local exact windows and grid relaxation are separate
controls, not a simultaneous realization of the full constraints.
Result 17 closes a uniform positive local compensation fraction even
on genuine OOE first returns. It leaves a lower bound requiring the
simultaneous selection of blocks by a complete cycle unresolved.
No further gate is automatically pursued.

## Publication assessment

Status: **STRUCTURAL**. This record includes a precision limitation, an exact
conditional criterion, a fixed minimum upper-bound corollary, and a local
Lean-verified upper-square gap. It changes neither the certified descent
floor nor the period bound and edits neither Paper A nor its generated
copies. Independent human review remains outstanding. The new formal
statements are Result 10's integer inequality, Result 15's equal-gap OO
triple, Result 17's exact square-start cell bridge, Result 19's
conditional valuation, reset-count and deviation-support kernels, and
the laboratory assembly that lifts a charge certificate to leftover
height and those kernels. The analytic comparisons, joint equidistribution,
infinitude, and global shortcut audits remain written calculations.
Result 18 adds a bounded computational observation and an elementary
fixed-point correctness proof. Its workspace Lean check is not a new
production module or a Paper A claim. No class exclusion was obtained.

Result 19 adds a new written necessary distribution theorem for actual
cubic cycles, with separately Lean-verified arithmetic and counting
kernels. CubicRemainderAssembly now supplies the certificate-to-gap
lift, the ordinary RC68 remainder difference and leftover H<=86; the
even-denominator cover that unlocks S>=4483 remains a hypothesis, and
RC72 remains written. The 4483-deviation consequence is conditional on
the already established fixed count tuple and height bound. It excludes
neither that tuple nor cycles in general. The manuscript and its review
copies remain unchanged; the complete cycle application still needs
independent human review.

Result 20 merges actual integer recurrence, even-pair divisibility,
mechanical visit counts and the common gap-size budget. It strengthens
the fixed deviation count to 7284 and supplies an unsigned weighted-loss
corollary. Lean exposes the fixed-tuple runCost consumer; RC75 block
extraction remains written. No count-pair exclusion or manuscript
change is claimed.

Result 21 adds a written localization theorem using two certified rank
ceilings, a maximum block length of 21, and disjoint selected Q/R pairs.
Lean verifies the separately stated finite-path, valuation and counting
kernels. Real interval certification and the complete cycle extraction
remain outside the formal module. The localized raw support bound does
not prove the required signed normalized estimate. Independent human
review is outstanding; no Paper A or PDF change is included.

Result 22 distinguishes a family-specific normalized charge from actual
cheap complete OE pairs, and excludes the latter family's adjacency at
the fixed rank scale. The real proofs and cycle applications remain
written. CriticalCostKernel initially proved four explicit integer
interfaces; Result 23 adds consumers and exact unit-offset cells. The saved domain projection supplies no new whole-interval
exclusion. Paper A and all PDF snapshots remain unchanged.

Result 23 adds four-phase written equidistribution and paired OOE
counterexamples to a uniform local charge, together with a finite
square-start packing corollary of the saved grid enclosure. Neither
infinitude nor the complete cycle packing proof is formalized. The eight
CriticalCostKernel declarations verify only their stated integer/root
interfaces; the new actual-root consumers remove supplied cell witnesses,
not the parity and distinctness hypotheses. Paper A and PDFs are unchanged.
