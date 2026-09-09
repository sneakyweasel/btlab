# Paper B: assembly of a weaker dyadic kernel bound

9 September 2026. Research supplement to the 27/32 manuscript.

## Outcome and scope

The dyadic monomial kernel admits the following written bound:
\[
K_k(P)=\sum_{\substack{P<n\le2P\\n\ {\rm odd}}}
 e\left(\tfrac{3k}{4}n^{9/8}
          \{\lfloor n^{3/2}\rfloor^{3/2}\}\right)
 \ll_\varepsilon P^{127/128+\varepsilon},
 \qquad 1\le k\le P^{1/24}. \tag{K1}
\]
Here k is an integer and e(x)=exp(2 pi i x). Constants are uniform
in k in this range. They are implicit; no numerical threshold is claimed.

This is a weaker exponent than the historical target 95/96.
It is an undecorated dyadic kernel estimate, not a theorem for all
mixed modes or short intervals. The OOOEE correlation and the full
five-step density 7/8 remain unproved. The 27/32 manuscript and
existing deposit package are unchanged.

The assembly uses the wave-bearing and nonzero-offset supplements,
and proves the needed zero-offset specialization with its actual
moving coefficients. Two additional points are made explicit:
positive Fourier errors are controlled without retaining the anchor,
and frequency windows are counted as part of a common partition,
not as separate applications of an ambient-scale bound.

Decision: **PROMOTE** (K1), the stated reduction, and its auxiliary
estimates. These are AI-assisted written proofs with exact algebra
and exponent controls; independent mathematical review and Lean
verification remain outstanding.

## 1. Ranges and the two outer differencings

Let
\[
X=x^{3/2},\quad m(n)=\lfloor X(n)\rfloor,\quad Y(n)=m(n)^{3/2},
\quad c(x)=\tfrac34kx^{9/8},\quad \vartheta(n)=\{Y(n)\}.
\]
Take
\[
H_1=\lfloor P^{1/48}\rfloor,\quad H_2=\lfloor P^{1/24}\rfloor,
\quad 1\le h_i<H_i,\quad d_i=2h_i,
\quad p=h_1h_2,\quad \Pi=kp.
\]
Harmless changes in the endpoint conventions do not affect the proof.
In particular,
\[
p\le P^{1/16},\qquad \Pi\le P^{5/48}. \tag{K2}
\]
This last inequality is stricter than Pi<=P^(1/8) and will be used.

Write Delta_i f(x)=f(x+d_i)-f(x), and put
\[
W_1=\Delta_1Y,\quad W_2=\Delta_2Y,\quad D=\Delta_1\Delta_2Y,
\quad c_{11}(x)=c(x+d_1+d_2).
\]
Twice applying van der Corput differencing on the odd lattice gives
\[
\begin{split}
|K_k|^2&\ll P^2/H_1+(P/H_1)\sum_{h_1<H_1}|T_1(h_1)|,\\
|T_1(h_1)|^2&\ll P^2/H_2+(P/H_2)\sum_{h_2<H_2}|T_2(h_1,h_2)|.
\end{split} \tag{K3}
\]
The phase of T_2 is Delta_1 Delta_2(c vartheta), on the appropriate
overlap interval. We may replace that interval by the full dyadic
block at cost O(h_1+h_2), or restrict all estimates below to the
overlap. All auxiliary bounds use the ambient scale P, including
their endpoint costs.

We will prove uniformly that
\[
|T_2(h_1,h_2)|\ll_\varepsilon P^{31/32+\varepsilon}. \tag{K4}
\]

## 2. Positive Fourier errors before using any anchor estimate

Set \(J=\lfloor P^{1/24}\rfloor\), and use
\(E_J(z)=\min(1,(J\|z\|)^{-1})\), with value one at integers.
For every argument occurring in the carry expansion below,
\[
\sum_{P<n\le2P,\ n\ {\rm odd}} E_J(Z(n))
 \ll P^{23/24}(\log(2P))^C, \tag{K5}
\]
where
\[
Z\in\{Y(n),Y(n+d_1),Y(n+d_2),Y(n+d_1+d_2),
       W_1(n),W_2(n),W_1(n+d_2),D(n)\}.
\]
The constant C is absolute. This is an unweighted positive bound;
it does not assume that an anchor is still present.

For Y at any of these even translations, Theorem 4.5 of the
[current manuscript](juggler_parity_discrepancy_note.md), with modes
(i,j,k)=(0,2q,0), gives O(P^(23/24)) for 1<=|q|<=J.
The discrepancy inequality at cutoff J, followed by dyadic distance
bands, proves (K5). The same argument for W uses Lemma 4.4 with
i=k=0 and j=2q. Its bound is
O(P^(7/8)(1+h_i^(1/2)))=O(P^(43/48)), which also fits (K5).
The proofs of those results work on any subinterval of [P,3P]:
their length, gap-cell, and positive-error bounds are all in the
ambient scale P. No proportional rescaling of an exceptional set
is used for the translated intervals here.

For D, a separate elementary argument is needed. Put
\[
j(n)=\Delta_1\Delta_2m(n),\qquad -1\le j(n)\le2.
\]
The exact frozen-branch integral formulas imply the global
value approximation
\[
D(n)=g_{j(n)}(n)+O((h_1+h_2)P^{-1/4}),\qquad
g_j(x)=\tfrac32j x^{3/4}+\tfrac{27}{4}p x^{1/4}. \tag{K6}
\]
To verify the error, the first-floor offsets satisfy
beta_i=3h_i sqrt(n)+O(1), hence
beta_1 beta_2=9pn+O((h_1+h_2)sqrt(P)+1).
In the zero-offset integral, replacing its argument by n^(3/2)
has relative error O((h_1+h_2)/P); in the offset integral the
corresponding absolute error is O((h_1+h_2)P^(-1/4)).
The resulting extra zero-offset error
O(p(h_1+h_2)P^(-3/4)) is smaller than the displayed error.
This is a comparison of values, not of frozen derivatives.

The error in (K6) is O(P^(-5/24)), so J times that error tends to zero.
For |u-v|<=1/(2J), one has E_J(u)<=2E_J(v).
On a branch j=0, g_j has derivative comparable to pP^(-3/4).
On a nonzero branch it has derivative comparable to P^(-1/4),
of the sign of j. Both are monotone slow variables on the whole
dyadic block. The monotone counting lemma (D2) of the
[D2 supplement](paper_b_d2_report.md) gives
\[
\sum E_J(g_j(n))
 \ll (P+a_j^{-1})\log(2J)/J+Pa_j+1,
\quad
a_0\asymp pP^{-3/4},\quad a_j\asymp P^{-1/4}\ (j\ne0).
\]
Every term is O(P^(23/24) log P). Bound a branch-restricted positive
sum by this full-block sum and add the four possible j values.
This proves (K5) for D without multiplying a floor-error estimate
by the number of original gap runs.

## 3. Exact master identity and a shorter centered expansion

Define the binary carry C(A,B)={A}+{B}-{A+B}, and set
\[
\kappa_1=C(Y,W_1),\quad \kappa_2=C(Y,W_2),\quad
\kappa_1^+=C(Y(n+d_2),W_1(n+d_2)),\quad
\kappa_*=C(W_1,D).
\]
Let
\[
B_2(x)=\Delta_2c(x+d_1),\qquad
B_1(x)=\Delta_1c(x+d_2),\qquad N_i(x)=\lfloor B_i(x)\rfloor .
\]
The product rule and the exact carry identity give
\[
\begin{split}
\Delta_1\Delta_2(c\vartheta)
={}&(\Delta_1\Delta_2c)\vartheta
 +B_2(\{W_1\}-\kappa_1)+B_1(\{W_2\}-\kappa_2)\\
 &+c_{11}(\{D\}-\kappa_*-\kappa_1^++\kappa_1). 
\end{split} \tag{K7}
\]
The first term has total deletion cost
O(Pi P^(1/8))=O(P^(11/48)).

For each factor e(B_i{W}), center at the integer N_i:
\[
e(B_i\{W\})=e(N_iW)e(\beta_i\{W\}),\qquad
\beta_i=B_i-N_i\in[0,1).
\]
Here beta_i denotes a coefficient residual only; it is not a
first-floor offset used in a branch formula.
Expand the last factor at the short cutoff J:
\[
e(\beta_i\{W\})=\sum_{|r|\le J}a_r(\beta_i)e(rW)+O(E_J(W)),
\quad a_r(\beta)=\int_0^1e((\beta-r)y)\,dy. \tag{K8}
\]
Its coefficients satisfy
|a_r|+|a_r'|<<1/(1+|r|), including removable singularities.
The error is covered by (K5), independently of the large center N_i.
There is no uncentered large-coefficient tail to discard.

For each of the five carry exponentials in (K7), use exactly
\[
e(g\kappa)=1+\kappa(e(g)-1).
\]
Expand the factor e(g)-1 into two terms and move e(g) into the
smooth phase. Expand kappa additively using its three unit
fractional parts, each at cutoff J by Lemma 4.3 of the manuscript.
The only arguments are those in (K5), because
\[
Y+W_i=Y(n+d_i),\quad W_1+D=W_1(n+d_2),\quad
Y(n+d_2)+W_1(n+d_2)=Y(n+d_1+d_2).
\]
The smooth phases introduced this way are bounded integer
combinations of B_1,B_2,c_11.

There are two centered Fourier layers and at most five carry layers.
Their total coefficient mass is O((log(2P))^7); a larger fixed
logarithmic power covers all errors. Indeed, pointwise truncated
factors have O(log P) bounds, so telescoping products multiplies
each error in (K5) only by a fixed logarithmic power.

The N_i windows are retained globally as functions of x.
Both B_i are increasing, with
\[
B_i\asymp kh_iP^{1/8},\quad B_i'\asymp kh_iP^{-7/8}.
\]
Their common partition has local count
O(1+k(h_1+h_2)LP^(-7/8)) and total count O(P^(5/24)).
On each cell the residuals beta_i are monotone in [0,1), so
the same logarithmic bound holds for summed coefficient
sup norms plus variations.

## 4. The complete retained inventory

For arbitrary four corner coefficients, the exact identity is
\[
\sum_{d\in\{0,d_1,d_2,d_1+d_2\}}q_dY(n+d)
=tY+(q_{d_1}+q_{d_1+d_2})W_1
 +(q_{d_2}+q_{d_1+d_2})W_2+q_{d_1+d_2}D,
\quad t=\sum_dq_d. \tag{K9}
\]
Use also W_1(n+d_2)=W_1+D.

Consequently (K7)--(K8) reduce T_2, with absolute error
O(P^(23/24) log^C(P)), to a finite weighted family with phases
\[
c_{11}\{D\}+tY+(N_2+u)W_1+(N_1+v)W_2+qD+\phi . \tag{K10}
\]
Here t,u,v,q are fixed integers for each Fourier multi-index,
\[
|t|,|u|,|v|,|q|\le6J,
\]
and phi is a bounded integer combination of B_1,B_2,c_11.
In particular
\[
|\phi''|\ll kP^{-7/8},\qquad |\phi'''|\ll kP^{-15/8}. \tag{K11}
\]
The two centered residual frequencies account for the extra unit
in the bound 6J; each carry layer contributes at most one mode.
All signs and zero coordinates are included.

More precisely there are nonnegative numbers rho_nu, one for each
multi-index, with sum rho_nu=O(log^7(P)), such that its amplitude
divided by rho_nu has bounded sup norm plus variation on each
N_1,N_2 cell. This follows by multiplying the harmonic coefficient
bounds in Section 3 and applying the product variation inequality.
Thus it suffices to prove a uniform bound for each normalized
amplitude; no estimate is multiplied by the number of frequency
windows.

The first-difference coefficients satisfy
\[
|(N_2+u)h_1|+|(N_1+v)h_2|
 \ll \Pi P^{1/8}+J(h_1+h_2)\ll P^{11/48}, \tag{K12}
\]
well within the widened P^(1/2) budget.

## 5. Nonzero total Y frequency: verify the wave-bearing hypotheses

Suppose t is nonzero. Freeze the original first-floor gap runs
and use the actual carry-branch decomposition D=F(m), G=F(X).
Split the anchor exactly as
\[
c_{11}\{D\}=c_{11}F(m)-c_{11}A,\qquad A=\lfloor F(m)\rfloor .
\]
The labels defining A remain fixed on their original gap runs.
In particular, do not introduce the integer level sets of A
before applying the wave-bearing theorem.

Taylor expansion in m gives
\[
c_{11}F(m)=c_{11}G-B_a\{X\}+\mathcal E,\qquad B_a=c_{11}F'(X),
\]
with total error
O(kP^(-1/8)+Pi P^(-5/8))=O(1).
Replacing qD by qG has total cost O(P^(7/24)).
On a branch of offset j,
\[
B_a=\tfrac9{16}kjx^{3/8}+O(1).
\]
Center at \(N_a=\lfloor(9/16)kjx^{3/8}\rfloor\) on that
original run; at j=0 this is zero.
The residual B_a-N_a has bounded sup norm and variation after
intersecting with its center windows. This follows from the
frozen derivative bounds in Section 3 of the
[offset-anchor supplement](paper_b_offset_anchor_report.md).

Expand that bounded residual at R=floor(P^(5/16)) and the actual
first-floor carry indicators at R_c=floor(P^(1/4)).
Their errors total O(P^(5/6) log^C(P)); moving endpoints yield
phases sX(x+d), not uncontrolled-variation coefficients.
The retained smooth part, apart from tY and the two first differences,
is
\[
\Phi=c_{11}G+qG+\phi+(r-N_a)X+sX(x+d).
\]
With all integer labels and centers frozen on a cell,
\[
|\Phi'''|\ll
 kP^{-9/8}+\Pi P^{-13/8}
 +(R+|N_a|+R_c)P^{-3/2}
 \ll P^{-13/12}. \tag{K13}
\]
Here |N_a|<<kP^(3/8)<<P^(5/12); derivatives of the smaller
qG term fit the bound as well.

The common coarse partition consists of original gap runs,
N_1,N_2 windows, N_a windows, and the finitely many endpoint-order
cuts per run. Its local cell count is O(1+LP^(-11/24)):
the respective densities are at most
P^(-11/24), P^(-19/24), and P^(-7/12).
If a carry pattern has empty support on a run, fill its branch
extension with any admissible label and use zero amplitude there;
no new label changes are introduced inside an original run.

Thus every retained mode is precisely a (W3) sum of the
[wave-bearing supplement](paper_b_wave_bearing_report.md):
1<=|t|<=6P^(1/24), piecewise constant first-difference coefficients
satisfying (K12), one undifferenced fixed-label D2 floor anchor
-c_11 A, a twist satisfying (K13), and the required coarse partition.
The coefficients have logarithmic mass and bounded variation per cell.
Its total contribution is
\[
O_\varepsilon(P^{31/32+\varepsilon}). \tag{K14}
\]
The D2 reduction is used inside that theorem after its additional
A-process. It is not applied here to an arbitrary undifferenced floor.

## 6. Zero total Y frequency, nonzero first-floor offset

For t=0 and j=Delta_1 Delta_2m nonzero, (K10) is directly the
family (O4) of the offset-anchor supplement. Its input cells are
the N_1,N_2 windows, on which N_2+u,N_1+v,q are constant.
Their density fits O(1+LP^(-1/4)); (K12) is within its widened
coefficient range, and (K11) is smaller than its allowed
|psi''|<<P^(-1/4). The shift of c is d_1+d_2.
Normalized amplitudes have the required variation bounds.

The corrected composite coefficient 81/64 and every floor-level
boundary are already included in that theorem. It gives
\[
O_\varepsilon(P^{23/24+\varepsilon}) \tag{K15}
\]
for the total of these weighted modes. No extra undifferenced
floor anchor is added to this application.

## 7. Zero total Y frequency and zero offset: moving-center specialization

The general signed zero-offset statement is for fixed wave
coefficients. It must not simply be applied afresh on every
N_1,N_2 window. We prove the actual specialization of (K10) here.

Set
\[
a_1=N_2+u,\quad a_2=N_1+v,\quad
\alpha_0=uh_1+vh_2.
\]
On the actual zero-offset set the branch function is F_0,
with beta_12=beta_1+beta_2. Replace floor(F_0(m)) by floor(G)
at the original-run exception cost O(P^(13/24)), as in (S6)
of the [signed zero-offset supplement](paper_b_signed_waves_report.md).
Taylor-expand in m, retaining the coefficient of theta={X}.
The retained phase is
\[
c_{11}(G-J_F)+a_1V_1(X)+a_2V_2(X)+qG+\phi-B\theta,
\quad J_F=\lfloor G\rfloor,
\]
where V_i(z)=(z+beta_i)^(3/2)-z^(3/2) and
\[
B=c_{11}F_0'(X)+a_1V_1'(X)+a_2V_2'(X).
\]
By (K12) and the frozen integral estimates,
\[
|B|\ll \Pi P^{-1/8}+J(h_1+h_2)P^{-1/4}
       \ll P^{-1/48}+P^{-1/6}\ll1. \tag{K16}
\]
Its variation is bounded on each original gap run intersected with
the N_i windows: with N_i frozen,
|B'|<<Pi P^(-9/8)+J(h_1+h_2)P^(-5/4)<<P^(-1),
and an original run has length O(sqrt(P)).
All Taylor errors fit O(P^(3/4)); in fact they are smaller at (K12).

Expand e(-B theta) directly at R=P^(5/16), without a new integer
center, and the carry indicators at R_c=P^(1/4). The positive
errors total O(P^(5/6) log^C(P)).
For frequencies r,s from the two expansions put ell=r+s.
The combined coefficient sup norms plus variations at each ell
are O(log(2P)/(1+|ell|)), by the harmonic convolution estimate (S9).
The shifted endpoint remainder s Delta_d X has curvature
O(P^(-29/24)).

Differentiate with beta_i,J_F,N_i frozen, then substitute their
approximating values only in the resulting curvature formula.
The wave curvature is
\(-27(a_1h_1+a_2h_2)x^{-3/4}/32\), with the smaller errors
listed in (S11). The anchor contributes
\(-243\Pi x^{-5/8}/128\).
Moreover
\[
h_1N_2+h_2N_1
 =\tfrac{27}{8}\Pi x^{1/8}
  +O\big(h_1+h_2+\Pi(h_1+h_2)P^{-7/8}\big). \tag{K17}
\]
The first error includes both floor roundings.
Consequently every retained phase obeys
\[
f''=-\tfrac{27}{32}\alpha_0x^{-3/4}
     -\tfrac{1215}{256}\Pi x^{-5/8}
     +\tfrac34\ell x^{-1/2}
     +O(\Pi P^{-3/4}). \tag{K18}
\]
The new coefficient is
\(-243/128-(27/32)(27/8)=-1215/256\).

For completeness, the error in (K18) includes
\[
\begin{split}
&(h_1+h_2)P^{-3/4}
 +( |a_1|+|a_2| )P^{-5/4}
 +( |a_1|h_1^2+|a_2|h_2^2 )P^{-7/4}\\
&\quad+k(h_1+h_2)P^{-9/8}
 +\Pi(h_1+h_2)P^{-13/8}
 +kP^{-7/8}+|q|pP^{-7/4}
 +P^{-29/24}+|\phi''|.
\end{split}
\]
All are O(Pi P^(-3/4)). For the leading rounding term use
h_1+h_2<=2h_1h_2<=2Pi before imposing the shift caps.
This avoids losing a power by bounding the shifts independently.

There is a gap between ell=0 and ell nonzero:
\[
\frac{|\alpha_0|P^{-3/4}}{\Pi P^{-5/8}}
 \ll JP^{-1/8}\ll P^{-1/12},\qquad
\frac{\Pi P^{-5/8}}{P^{-1/2}}
 \le P^{-1/48}. \tag{K19}
\]
The first estimate uses (h_1+h_2)/Pi<=2; the second uses (K2).
Thus ell=0 has one-signed curvature comparable to Pi P^(-5/8),
whereas every nonzero integer ell has one-signed curvature
comparable to |ell|P^(-1/2), for large P. No collision sublevel
estimate or bound for individual signed waves is substituted here.

The full partition has O(P^(13/24)) cells. Indeed the original gaps
give that count, the zero-offset G floor adds at most
O(pP^(1/4)+P^(13/24)), the N_i windows number O(P^(5/24)),
and the endpoint-order cuts give only a fixed multiple.
For ell=0 the summed second-derivative bound is
\[
O\big(\Pi^{1/2}P^{11/16}
       +\Pi^{-1/2}P^{41/48}\big)\log^C(P).
\]
For ell nonzero, summing its harmonic weights and all cell endpoints
gives
\[
O\big(R^{1/2}P^{3/4}+P^{13/24+1/4}\big)\log^C(P)
 =O(P^{29/32}\log^C(P)).
\]
The zero-mode and positive-error terms are smaller. Hence the
moving-center zero-offset specialization contributes
\[
O_\varepsilon(P^{29/32+\varepsilon}). \tag{K20}
\]
This proof addresses the particular varying coefficients in (K10);
it does not silently enlarge the earlier fixed-coefficient theorem.

## 8. Sum the inventory and return through the outer shifts

The complete accounting is:
| Contribution | Bound, up to a fixed power of log P |
|---|---|
| Deleted first master-identity term | P^(11/48) |
| Positive errors from both centered factors and all five carries | P^(23/24) |
| Nonzero total Y frequency | P^(31/32) |
| Zero total Y frequency, nonzero offset | P^(23/24) |
| Zero total Y frequency, zero offset, with the actual moving centers | P^(29/32) |

All Fourier multi-indices are summed with their coefficient masses
from Section 4. The finite support costs logarithms only, so no
separate power saving in |t| is required. The original gap runs,
coefficient windows, carry endpoints, and permitted floor-level
intervals have all been included. This proves (K4).

Inserting (K4) into (K3) gives
\[
|T_1|^2\ll P^{47/24}+P^{63/32+\varepsilon},
\qquad |T_1|\ll P^{63/64+\varepsilon},
\]
and then
\[
|K_k|^2\ll P^{95/48}+P^{127/64+\varepsilon},
\qquad |K_k|\ll P^{127/128+\varepsilon}.
\]
Both diagonal terms fit. This establishes (K1).

## 9. What changes and what remains open

This supplement proves the stated weaker dyadic monomial kernel.
It does not establish the historical 95/96 exponent, arbitrary
decorations, localization, or any OOOEE mixed-mode count.

The next bounded question is to list the precise mixed modes needed
for OOOEE and determine whether their phases reduce to a controlled
kernel family. That must be done before inferring the full five-step
density 7/8. The known 27/32 certificate subfamily is unchanged.
This branch stops at the dyadic assembly.

The companion validate_paper_b_kernel_assembly.py checks the exact
master identity, the binary carry expansions, the complete Fourier
argument inventory in the basis (Y,W_1,W_2,D), the moving-center
coefficient, and rational error/partition/exponent budgets.
Finite tests support the derivation; they do not independently
establish analytic cancellation.

The local ingredients are linked above. The classical tools are
van der Corput differencing and second-derivative estimates, and
the Fourier discrepancy inequality; see S. W. Graham and G. Kolesnik,
Van der Corput's Method of Exponential Sums, Cambridge University
Press, 1991
([publisher excerpt](https://beckassets.blob.core.windows.net/product/readingsample/666252/9780521339278_excerpt_001.pdf)).
No literature-wide priority claim, independent review, numerical
threshold certificate, new density, or Zenodo upload is asserted.

