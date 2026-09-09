# Paper B: the nonzero-offset anchor family

9 September 2026. Research supplement to the 27/32 manuscript.

## Outcome and scope

For the actual nonzero-offset anchor, with zero total undifferenced
Y frequency, the family specified below satisfies
\[
Z_j(P)\ll_{C,M,\varepsilon}P^{23/24+\varepsilon}\qquad (j\ne0).
\]
The estimate allows finitely many signed first-difference decorations
over the widened range, the specified slow and smooth terms, and the
already-differenced D2 factors in Section 7.

The proof centers the large anchor coefficient and truncates the
residual Fourier expansion below its first curvature-cancellation
range. Every retained mode then has curvature comparable to
\(k|j|P^{-1/8}\). In particular, no maximum-of-individual-waves
dominance criterion or collision-band estimate is needed.

There is also a correction to the historical Step 5(a): its displayed
composite coefficient 729/512 omits the frozen-floor subtraction.
The coefficient for the full phase is **81/64**. It remains nonzero
and gives the same exponent after the corrected argument.

Decision: **PROMOTE** the stated family estimate and correction.
These are AI-assisted written proofs with exact algebra and exponent
controls, not independently reviewed or Lean verified. The full
kernel and the OOOEE mixed-mode transfer remain unproved.
The 27/32 manuscript and its deposit package are unchanged.

## 1. Statement

Write e(v)=exp(2 pi i v), and set
\[
X(x)=x^{3/2},\quad m(n)=\lfloor X(n)\rfloor,\quad
Y(n)=m(n)^{3/2},\quad \Delta_d f(x)=f(x+d)-f(x).
\]
Fix C,M. Let the positive integers k,h_1,h_2 satisfy
\[
k,h_1,h_2\le CP^{1/24},\quad
d_i=2h_i,\quad p=h_1h_2,\quad K=kp.
\]
Let v be a nonnegative even integer O_C(P^(1/24)), and put
\[
c(x)=\tfrac34 k(x+v)^{9/8},\qquad
\mathcal J(n)=\Delta_{d_1}\Delta_{d_2}m(n).
\]
The usual anchor uses v=d_1+d_2; the bounded translation does not
change the proof. Fix a nonzero integer j with |j|<=2.
For large P these choices include every nonzero value of
mathcal J. Empty branches contribute zero.

There are at most M signed first-difference terms
\(a_b(n)\Delta_{2r_b}Y(n+e_b)\), where e_b are nonnegative even
integers, r_b are positive integers, and
\[
e_b,r_b\le CP^{1/24},\qquad |a_b(n)|r_b\le CP^{1/2}. \tag{O1}
\]
The real coefficients a_b and q are constant separately on an
input interval partition \(\mathcal P\) of [P,3P]. Assume
\[
|q|\le CP^{1/24},\qquad
\#\{\text{cells meeting an interval of length }L\}
 \le C(1+LP^{-1/4}). \tag{O2}
\]
The real twist psi is C^2 on each cell, with
\[
|\psi''|\le CP^{-1/4}. \tag{O3}
\]
The complex amplitude eta obeys
\(\|\eta\|_{\infty,I}+\operatorname{TV}_I(\eta)\le C\)
on each input cell I. Jumps at the cell boundaries are allowed.

Then, for every epsilon>0,
\[
\begin{split}
Z_j(P)=\sum_{\substack{P<n\le2P\\n\ {\rm odd}\\\mathcal J(n)=j}}
 \eta(n)e\left(
 c(n)\{\Delta_{d_1}\Delta_{d_2}Y(n)\}
 +\sum_b a_b(n)\Delta_{2r_b}Y(n+e_b)
 +q(n)\Delta_{d_1}\Delta_{d_2}Y(n)+\psi(n)\right),\\
|Z_j(P)|\ll_{C,M,\varepsilon}P^{23/24+\varepsilon}. \tag{O4}
\end{split}
\]
The sum over all nonzero j has the same bound.
There is no undifferenced tY term in (O4). Applications must verify
(O1)--(O3); the statement does not cover arbitrary extra floor terms.

## 2. Exact branch functions and the first errors

Partition by the floors of X(x+s)-X(x) for all shifts s occurring
in the anchor and the decorations. These are finitely many
nonnegative even shifts O_C,M(P^(1/24)), including d_1,d_2,d_1+d_2.
The original gap runs have total count O_C,M(P^(13/24)) and local
count O_C,M(1+L P^(-11/24)). Each such run has length O_C(sqrt(P)):
the gap at d_1 alone has derivative comparable to h_1 P^(-1/2).

With theta={X(n)}, a joint carry pattern specifies integers beta_s
such that m(n+s)=m(n)+beta_s. There are only O_C,M(1) patterns on
each original run. On a pattern contributing to mathcal J=j, put
\[
\begin{split}
F_j(z)&=(z+\beta_1+\beta_2+j)^{3/2}
 -(z+\beta_1)^{3/2}-(z+\beta_2)^{3/2}+z^{3/2},\\
G(x)&=F_j(X(x)),\\
V_b(z)&=(z+\beta_{e_b+2r_b})^{3/2}
                -(z+\beta_{e_b})^{3/2}.
\end{split}
\]
Here beta_i denotes the offset at d_i, and beta_0=0.
Thus the anchor argument is F_j(m(n)) and each decorated wave is
V_b(m(n)). Every derivative below holds these integers fixed.
The carry indicators are reassembled in Section 5, not ignored.

The exact integral formulas in (W4) of the
[wave-bearing supplement](paper_b_wave_bearing_report.md) give, on
nonzero-offset branches,
\[
\begin{split}
|G'|&\asymp |j|P^{-1/4},\\
|F_j'(X)|&\ll |j|P^{-3/4}+pP^{-5/4},\\
|F_j''(X)|&\ll |j|P^{-9/4}+pP^{-11/4}.
\end{split} \tag{O5}
\]
The derivative of G has a fixed sign on each run. Its zero-offset
part is smaller because pP^(-1/2)=o(1).

Replacing floor(F_j(m)) by floor(G) is allowed after counting the
exceptional integers on these original runs. A mismatch requires
\(\|G(n)\|\ll P^{-3/4}+pP^{-5/4}\). The monotone counting lemma
(D3) in the [D2 supplement](paper_b_d2_report.md), at derivative
scale P^(-1/4), gives
\[
\#\{n:\lfloor F_j(m(n))\rfloor\ne\lfloor G(n)\rfloor\}
 \ll_{C,M}P^{3/4}. \tag{O6}
\]
This estimate includes exact integer values and both signs of j.
It is charged once before the later input and frequency refinements.
Changing a unit exponential on the exceptional set costs at most two;
the large coefficient c is never multiplied by a floor mismatch.

Taylor expansion in the variable z=m, with 0<=theta<1, gives
\[
c F_j(m)=cG-cF_j'(X)\theta
       +O_C(kP^{-9/8}+K P^{-13/8}).
\]
Its total error is
O_C(kP^(-1/8)+K P^(-5/8)), which is bounded in the parameter range.
For a decorated wave, beta_{e+2r}-beta_e is comparable to r sqrt(P),
and differentiation of its exact two-term formula gives
\[
|V_b''(X)|\ll_C r_bP^{-7/4}.
\]
Consequently
\[
a_b V_b(m)=a_b V_b(X)-a_b V_b'(X)\theta
            +O_C(|a_b|r_bP^{-7/4}), \tag{O7}
\]
with total error O_C,M(P^(-1/4)) after summing all integers.
Replace qF_j(m) directly by qG at total cost O_C(P^(7/24)).
All these bounds apply with either sign of each coefficient.

The retained phase is therefore
\[
F_{\rm sm}(x)-B(x)\theta,\quad
F_{\rm sm}=c(G-J)+\sum_b a_b V_b(X)+qG+\psi,\quad
J=\lfloor G\rfloor,\quad
B=cF_j'(X)+\sum_b a_bV_b'(X). \tag{O8}
\]
The floor J will be frozen only when differentiating on its own
level intervals.

## 3. Center a smooth leading coefficient

On each input cell let alpha=sum_b a_b r_b and define
\[
B_*(x)=\tfrac9{16}kjx^{3/8}+\tfrac94\alpha x^{-1/4},
\quad N=\lfloor B_*\rfloor,\quad D=B-N. \tag{O9}
\]
This center is chosen before introducing J-level intervals.
It is not a frequency that will be differentiated in the phase.

The frozen branch formulas and
\[
\beta_{e+2r}-\beta_e
 =3r\sqrt{x}+O_C(1+r(e+r)P^{-1/2})
\]
give
\[
\begin{split}
cF_j'(X)&=\tfrac9{16}kjx^{3/8}
 +O_C\big(k(h_1+h_2+v)P^{-5/8}+K P^{-1/8}\big),\\
\sum_b a_bV_b'(X)&=\tfrac94\alpha x^{-1/4}
 +O_{C,M}(P^{-1/4}+P^{-17/24}).
\end{split} \tag{O10}
\]
In particular B-B_* is bounded by a constant depending on C,M.
Differentiating the frozen formulas, not the approximations to beta,
also gives
\[
|(B-B_*)'|\ll_{C,M}P^{-3/4} \tag{O11}
\]
on an original run intersected with an input cell. For example, the
zero-offset contribution to the anchor coefficient has derivative
O(KP^(-9/8)); the difference between the frozen wave derivative and
the moving leading approximation is O(sum |a_b|r_b P^(-5/4)).
Both fit (O11).

The derivative
\[
B_*'=\tfrac{27}{128}kjx^{-5/8}
                     -\tfrac9{16}\alpha x^{-5/4}
\]
has the sign of j for sufficiently large P. The ratio of its second
term to the first is O_C,M(P^(-1/8)/k). Thus B_* is monotone on each
input cell. There it creates O_C,M(1+k L P^(-5/8)) N-windows in
length L. On each window, B_*-N has variation at most one; (O11)
and the O(sqrt(P)) original-run length bound show that D is bounded
and has bounded total variation after intersecting with a run.

Use the exact identity
\[
e(-B\{X\})=e(-NX)e(-D\{X\}). \tag{O12}
\]
At R=floor(P^(5/16)), the bounded-coefficient Fourier expansion is
\[
e(-D\{X\})=\sum_{|r|\le R}a_r(D)e(rX)+O_{C,M}(E_R(X)),
\quad
a_r(D)=\int_0^1 e(-(D+r)y)\,dy.
\]
The integral includes removable singularities. On the fixed bounded
range of D,
\[
|a_r|+|a_r'|\ll_{C,M}(1+|r|)^{-1}.
\]
Thus the total coefficient sup norms plus variations per refined
cell are O_C,M(log P). The positive error sum is O(P^(5/6) log P),
as in (W15), and is charged globally.

The cutoff R is smaller than the anchor coefficient scale:
\[
R=o(k|j|P^{3/8}). \tag{O13}
\]
This strict separation is the reason the following proof does not
need a collision-band estimate.

## 4. The full frozen curvature, including the integer floor

On a refined interval freeze beta_s,J,N and all input coefficients.
The anchor curvature is
\[
(c(G-J))''=2c'G'+cG''+c''(G-J). \tag{O14}
\]
For the offset part, G has leading term (3j/2)x^(3/4). Hence
\[
2c'G'+cG''
 =\tfrac{27}{16}kjx^{-1/8}
  +O_C\big(KP^{-5/8}+k(h_1+h_2+v)P^{-9/8}\big).
\]
The last term of (O14) is O_C(kP^(-7/8)), because 0<=G-J<1.
All three identities hold for negative j as well.

The center mode in (O12) contributes \(-NX''\). Substituting
the value N=B_*+O(1), only after taking this derivative, gives
\[
-NX''=-\tfrac{27}{64}kjx^{-1/8}
       -\tfrac{27}{16}\alpha x^{-3/4}+O(P^{-1/2}).
\]
Therefore the anchor-plus-center leading coefficient is
\[
\tfrac{27}{16}-\tfrac{27}{64}=\boxed{\tfrac{81}{64}}. \tag{O15}
\]

This corrects the historical 729/512 in Theorem 5.3, Step 5(a).
The exact coefficient audit is
\[
\underbrace{\tfrac{945}{512}}_{(cG_{\rm offset})''}
-\underbrace{\tfrac{81}{512}}_{c''J\text{ at leading order}}
-\underbrace{\tfrac{216}{512}}_{NX''\text{ at leading order}}
=\tfrac{648}{512}=\tfrac{81}{64}.
\]
Indeed J=G+O(1), so c''J has the same leading term as c''G.
Omitting that term gives the older 729/512. This is a correction to
a curvature identity, not a refutation of a power-saving estimate.

The complete signed wave contribution is bounded without selecting
an individual dominant wave:
\[
\left|\sum_b a_b(V_b\circ X)''\right|
 \ll_{C,M}\sum_b|a_b|r_b P^{-3/4}
 \ll_{C,M}P^{-1/4}.
\]
The alpha term from the center obeys the same bound, including
alpha=0 and exact cancellation. Also
\[
|qG''|\ll_C P^{-29/24},\qquad |\psi''|\le CP^{-1/4}.
\]
The residual Fourier frequency r has curvature at most
O(RP^(-1/2))=O(P^(-3/16)), strictly smaller than (O15).

## 5. Reassemble carries and count every interval

A joint carry pattern is a finite union of intervals in theta,
whose endpoints are 0,1, or 1-{X(x+s)-X(x)}. Sorting endpoints
adds O_C,M(1) cuts on each original run: the difference between
two distinct real gaps is monotone, so their fractional endpoints
cross at most once there. Equal shifts give identical endpoints.

Expand these interval indicators at R_c=floor(P^(1/4)).
The zero coefficient has bounded variation. Every nonzero endpoint
mode has weight O_C,M(1/|s'|), with phase s'X(x+d) for an allowed
shift d, |s'|<=R_c. Its endpoint error is a sum of
E_(R_c)(X(n+d)), whose total is O_C,M(P^(5/6) log P).
Combining the centered and carry expansions introduces only a fixed
power of log P. Their pointwise remainder estimates allow all such
errors to be charged once over the common input interval.

The retained phases are
\[
f_{r,s'}=F_{\rm sm}+(r-N)X+s'X(x+d).
\]
Rewrite s'X(x+d)=s'X+s'Delta_d X. The additional small shifted
curvature is O_C,M(P^(-29/24)), while |r+s'|=O(P^(5/16)).
Together with Section 4, this proves uniformly for every retained
mode and every admissible branch that
\[
f_{r,s'}''=\tfrac{81}{64}kjx^{-1/8}
                       +O_{C,M}(P^{-3/16}). \tag{O16}
\]
The error includes the bounded shift of c and all signed decorations.
Its ratio to k|j|P^(-1/8) is O_C,M(P^(-1/16)).
For large P, all these phases have one-signed curvature comparable
to \(\lambda=k|j|P^{-1/8}\).

Here is the full partition count. Original gap and arc-order cuts
number O_C,M(P^(13/24)). The input cells number O_C(P^(3/4)).
On each original anchor run, |G'| is comparable to P^(-1/4), so
J=floor(G) adds O_C(1+L P^(-1/4)) intervals there. Its total number
of level intervals is O_C,M(P^(3/4)). The N-windows, including a
possible new endpoint in each input cell, contribute at most
O_C,M(P^(3/4)+kP^(3/8)). Since kP^(3/8)<=CP^(5/12), the final count is
\[
D_{\rm all}\ll_{C,M}P^{3/4}. \tag{O17}
\]
These are total counts; no lower bound on every refined interval's
length is asserted or needed. Endpoints and restrictions to a branch
are included. The product amplitude and Fourier coefficient masses
have bounded variation, up to logarithms, on each final cell.

## 6. The exponential-sum bound

On a final cell of length L, the second-derivative estimate, also
for the odd lattice and every subinterval, is
O(L sqrt(lambda)+lambda^(-1/2)). Partial summation and the summed
coefficient sup norms plus variations give a fixed logarithmic
factor. Summing every length and every cell endpoint gives
\[
\begin{split}
|Z_j(P)|
&\ll_{C,M}
 \left((k|j|)^{1/2}P^{15/16}
       +(k|j|)^{-1/2}P^{13/16}
       +P^{5/6}+P^{3/4}\right)(\log(2P))^B\\
&\ll_{C,M}P^{23/24}(\log(2P))^B. \tag{O18}
\end{split}
\]
Here B depends only on M; the smaller Taylor errors fit as well.
The first term is at most P^(15/16+1/48)=P^(23/24).
Small values of P excluded by curvature dominance are covered by
the implied constant. Absorbing logarithms into P^epsilon proves (O4).

## 7. Specified slow modes and already-differenced D2 factors

The same proof permits a fixed number of additional slow terms
\(q_\ell\Delta_{2s_{\ell,1}}\Delta_{2s_{\ell,2}}Y(n+f_\ell)\),
with nonnegative even f_ell=O_C(P^(1/24)),
1<=s_ell,i<=CP^(1/24), and |q_ell|<=CP^(1/24) constant on input
cells. On each of their frozen branches the replacement by the
smooth G_ell costs O_C(P^(7/24)) globally, and its curvature is
O_C(P^(-29/24)). Their finitely many carry endpoints fit Section 5.

One may also multiply the summand by a fixed number of factors
\[
e\big(-\sigma_\ell\Delta_{2g_\ell}(c_\ell A_\ell)(n)\big),
\quad \sigma_\ell\in\{-1,0,1\},\quad 1\le g_\ell\le CP^{1/8}, \tag{O19}
\]
where c_ell,A_ell are exactly the translated fixed-label objects in
Section 1 of the [wave-bearing supplement](paper_b_wave_bearing_report.md),
with their own k_ell,h_ell,i<=CP^(1/24).

These are already-differenced D2 factors as displayed in (O19).
This extension does not assert a bound with arbitrary undifferenced
c_ell A_ell added to (O4). The labels must stay fixed on their original
D2 gap runs, even if the common partition is further refined.

The D2 reduction (D9) has absolute error O_C(P^(15/16) log P),
retained curvature O_C(P^(-15/16)), and logarithmic coefficient
sup norm plus variation per window. Its original runs number
O_C(P^(13/24)); its additional coefficient windows number
O_C(1+k_ell g_ell P^(1/8))=O_C(P^(7/24)).
Both fit (O17), and the retained curvature fits the error in (O16).
Charge the D2 errors on their original runs, before further
refinement. A fixed number of factors is expanded by telescoping;
their coefficient masses add only a fixed logarithmic power.
Thus (O4) remains valid with (O19).

## 8. Remaining assembly question and validation

The signed zero-offset supplement gives exponent 31/32; the
wave-bearing supplement gives 31/32; this nonzero-offset family
gives 23/24. These are separate family estimates with explicit
hypotheses. Their coexistence is not yet a proof of a kernel bound.

The next bounded question is whether every term produced by the
twice-differenced kernel decomposition satisfies one of these family
statements, with total coefficient mass and all exceptional sets
accounted for. That audit must distinguish undifferenced floor
anchors from already-differenced D2 factors and must verify the
input partitions and smooth-twist conditions. The later transfer
to all OOOEE mixed modes is another requirement.
This branch stops at (O4).

The companion validate_paper_b_offset_anchor.py checks the frozen
curvature coefficients and the corrected subtraction, exact
centering and carry identities, commuting-shift identities, and
all exponent comparisons using rational arithmetic.
These finite controls support the derivation; they do not independently
establish asymptotic cancellation.

The Fourier and discrepancy tools are stated in the
[current manuscript](juggler_parity_discrepancy_note.md) and the cited
local supplements. Classical second-derivative and Fourier-discrepancy
estimates are used in their standard forms; see S. W. Graham and
G. Kolesnik, Van der Corput's Method of Exponential Sums,
Cambridge University Press, 1991
([publisher excerpt](https://beckassets.blob.core.windows.net/product/readingsample/666252/9780521339278_excerpt_001.pdf)).
There is no literature-wide priority claim, independent review,
new certificate density, or Zenodo upload.

