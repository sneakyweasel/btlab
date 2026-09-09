# Paper B: the combined signed zero-offset family

9 September 2026. Research supplement to the 27/32 manuscript.

## Outcome

The combined zero-offset family admits a written power-saving estimate:
\[
Z_0(P;u,u')\ll_\varepsilon P^{31/32+\varepsilon}.
\]
Both signs, zero frequencies, equal shifts, and exact leading
cancellation are included. The proof uses the signed combination
u h_1+u' h_2, and retains every gap, floor, and Fourier window boundary.
The D2 factors from the preceding supplement can be included.

This is one family needed by the kernel argument. The wave-bearing
and nonzero-offset families, and the transfer to OOOEE mixed modes,
still require a complete assembly audit. No new kernel theorem,
OOOEE count, or certificate density is asserted.
The 27/32 manuscript and release package are unchanged.

Decision: **PROMOTE** the signed zero-offset estimate.
This is an AI-assisted written proof with exact algebra and exponent
controls; it has not received independent mathematical review.

## 1. Statement

Let
\[
X(x)=x^{3/2},\quad m(n)=\lfloor X(n)\rfloor,\quad
Y(n)=m(n)^{3/2},\quad d_i=2h_i,
\]
and let Delta_i f(x)=f(x+d_i)-f(x).
Write p=h_1 h_2, K=kp, and
\[
c_d(x)={3k\over4}(x+d_1+d_2)^{9/8}.
\]
Assume
\[
1\le k,h_1,h_2\le P^{1/24},\qquad
|u|h_1\le P^{1/2},\quad |u'|h_2\le P^{1/2}. \tag{S1}
\]
Here k and the shifts are integers; u,u' may be real.

Define the actual zero-offset set
\[
\mathcal Z=\{n:\Delta_1\Delta_2m(n)=0\}.
\]
Let psi be real and C^2 on an interval partition of [P,3P].
Assume, with fixed C, that every interval of length L meets at most
C(1+LP^(-3/8)) cells and
\[
|\psi''|\le CP^{-3/4}
\]
on every cell. Jumps at cell boundaries are allowed.
For each epsilon>0,
\[
\begin{split}
Z_0&=\sum_{\substack{P<n\le2P\\n\ {\rm odd}\\n\in\mathcal Z}}
 e\left(c_d(n)\{\Delta_1\Delta_2Y(n)\}
       +u\Delta_1Y(n)+u'\Delta_2Y(n)+\psi(n)\right),\\
|Z_0|&\ll_{C,\varepsilon}P^{31/32+\varepsilon}. \tag{S2}
\end{split}
\]
An additional term q Delta_1 Delta_2 Y is allowed for |q|<=P^(1/24).

The small-curvature condition on psi is essential. This statement
does not permit an arbitrary smooth term that cancels the anchor.
The derivative and partition conditions must be checked at each
application.

## 2. A quadratic sublevel estimate over a partition

Consider
\[
\Lambda(x)=a x^{-3/4}+b x^{-5/8}+w_0 x^{-1/2},\qquad
S=\max(|a|P^{-3/4},|b|P^{-5/8},|w_0|P^{-1/2})>0.
\]
On [P,2P], both the sublevel set |Lambda|<=sS and each dyadic
band sS<|Lambda|<=2sS have O(1) components, and
\[
|\{|\Lambda|\le sS\}|\ll P\sqrt{s},\qquad 0<s\le1. \tag{S3}
\]
To see this, put t=(x/P)^(1/8). After division by S and multiplication
by t^6, the expression becomes a quadratic polynomial in t.
Its coefficient maximum is one. If that polynomial is O(s) on a
set of length ell, choose three points separated by constants
times ell. Lagrange interpolation bounds all its coefficients by
O(s/ell^2). Thus ell is O(sqrt(s)); the change of variables has
derivative comparable to P. For component counts, the boundaries
solve a quadratic equal to plus or minus s t^6, so there are
uniformly finitely many. The same reasoning applies to bands.

Suppose f is C^2 separately on cells whose local count is
O(1+nu L), and
\[
|f''-\Lambda|\le \rho S,\quad
0\le\rho\le1/8,\quad S\le1,\quad SP^2\ge1.
\]
For any interval I within [P,2P],
\[
\left|\sum_{n\in I}e(f(n))\right|
\ll P\sqrt S+
 (1+\nu P)S^{-1/2}\log(2P)
 +P^{1/2}S^{-1/4}+P\sqrt\rho+1. \tag{S4}
\]
The same bound holds over odd integers.

Here is a proof that includes the endpoints. Take
tau=max(4rho,1/(P sqrt(S))). If tau is bounded below by a positive
constant, the last two main terms give the trivial bound.
Otherwise discard |Lambda|<=tau S; (S3) bounds its integer count
by O(P sqrt(tau)+1).
At a dyadic scale s>=tau, the remaining band has length
O(P sqrt(s)) and meets O(1+nu P sqrt(s)) cells. On each
intersection the second derivative has one sign and size
comparable to sS. The second-derivative estimate, summed over
those intersections, gives
\[
P\sqrt S\,s^{3/4}+S^{-1/2}s^{-1/2}+\nu P S^{-1/2}.
\]
Summing the bands gives the first two terms of (S4), together with
S^(-1/2) tau^(-1/2). The choice of tau bounds that term by
P^(1/2) S^(-1/4), and bounds the discarded count by
O(P sqrt(rho)+P^(1/2) S^(-1/4)+1).

A weighted version will be useful. If a finite family f_j has the
same reference Lambda and error bound, and on every cell
\[
\sum_j\left(\|a_j\|_\infty+\operatorname{TV}(a_j)\right)\le M_0,
\]
then the bound for the sum of a_j e(f_j) is (S4) multiplied by M_0.
On the discarded set use the sup norms; on good cell intersections
use partial summation. This allows several Fourier decompositions
to be assembled without assuming a single global variation bound.

## 3. Exact branch representation and the first errors

Partition by the floors of Delta_1 X, Delta_2 X, and
X(x+d_1+d_2)-X(x). Their number is
O((h_1+h_2)P^(1/2)), with local density
O((h_1+h_2)P^(-1/2)).
On a fixed carry branch write
\[
m(n+d_i)=m(n)+\beta_i.
\]
The condition defining Z forces beta_12=beta_1+beta_2. Hence
\[
\Delta_1\Delta_2Y=F(m),\qquad
F(t)=(t+\beta_1+\beta_2)^{3/2}
 -(t+\beta_1)^{3/2}-(t+\beta_2)^{3/2}+t^{3/2}.
\]
Put G(x)=F(X(x)). The offsets are frozen when taking derivatives.
They obey
\[
\beta_i=3h_i\sqrt{x}+O(1+h_i^2P^{-1/2})
\]
as a comparison of values.

The integral representation in the D2 supplement gives
\[
\begin{split}
F'(X)&=-{3\over8}\beta_1\beta_2x^{-9/4}
 (1+O((h_1+h_2)/P)),\\
G'&=-{9\over16}\beta_1\beta_2x^{-7/4}(1+O((h_1+h_2)/P)),\\
G''&={63\over64}\beta_1\beta_2x^{-11/4}(1+O((h_1+h_2)/P)).
\end{split} \tag{S5}
\]
The relative errors are uniform on each run.

The slow-variable count from the D2 supplement, used only on
these original runs, gives
\[
\#\{n:\lfloor F(m(n))\rfloor\ne\lfloor G(n)\rfloor\}
 \ll pP^{1/4}+(h_1+h_2)P^{1/2}
 \ll P^{13/24}. \tag{S6}
\]
All exact integer endpoints are included. Each phase change costs
at most two on this exceptional set.

Writing theta={X}, Taylor's theorem also gives
\[
c_d F(m)=c_dG-c_dF'(X)\theta+O(KP^{-13/8}).
\]
For the waves use the exact m-linear identity
\[
\Delta_iY=A_{h_i}(x)+{3\over2}\beta_i(x+d_i)^{3/4}
 -{3\over2}\theta\Delta_i(x^{3/4})+\Delta_iE,
\]
where
\[
A_h={3\over2}x^{3/2}\Delta_h(x^{3/4})
 -{1\over2}\Delta_h(x^{9/4}),\quad
A_h''=O(h^2P^{-7/4}),\quad E=O(P^{-3/4}).
\]
Deleting the E terms costs O((|u|+|u'|)P^(1/4))=O(P^(3/4)).
The anchor Taylor error costs O(KP^(-5/8)).
These estimates are charged once, before further partitions.

Thus on a zero-offset branch the remaining phase is
\[
\begin{split}
F_{\rm sm}(x)-\bigl(B_{\rm w}(x)+B_{\rm a}(x)\bigr)\theta,\qquad
B_{\rm w}&={3\over2}\left(u\Delta_1x^{3/4}+u'\Delta_2x^{3/4}\right),\\
B_{\rm a}&=c_d F'(X),\\
F_{\rm sm}&=uA_{h_1}+u'A_{h_2}
 +{3\over2}\left(u\beta_1(x+d_1)^{3/4}
                 +u'\beta_2(x+d_2)^{3/4}\right)\\
&\qquad+c_d(G-\lfloor G\rfloor)+\psi.
\end{split} \tag{S7}
\]
The anchor coefficient is bounded:
|B_a| is O(KP^(-1/8))=O(1).

## 4. Center only the wave coefficient

Set
\[
\alpha=uh_1+u'h_2,\quad
A=|\alpha|P^{-1/4},\quad
N=\lfloor B_{\rm w}\rfloor,\quad
D=B_{\rm w}-N+B_{\rm a}.
\]
Here A is a nonnegative scale, not the function A_h.
Only B_w is centered; the bounded anchor coefficient stays in D.
Uniformly,
\[
\begin{split}
B_{\rm w}&={9\over4}\alpha x^{-1/4}+O(P^{-17/24}),\\
B_{\rm w}'&=-{9\over16}\alpha x^{-5/4}+O(P^{-41/24}),\\
|B_{\rm a}'|&\ll KP^{-9/8}.
\end{split} \tag{S8}
\]
The first two remainders follow by retaining the second shift term
and using |u|h_i<=P^(1/2). They do not assume alpha is nonzero.

The smooth function B_w has a bounded number of monotonic pieces.
For completeness, its derivative is a linear combination of three
fourth roots of reciprocal affine functions of x. Repeated algebraic
elimination gives a polynomial relation of uniformly bounded degree
in x and its value. Unless the derivative is identically zero, the
minimal such relation has nonzero constant term; its zeros therefore
lie among the roots of a polynomial of bounded degree. In the
identically zero case no monotonic subdivision is necessary.
Consequently (S8) gives O(1+A) N-windows in the whole block.
On each original run intersected with one such window, D is bounded
and has bounded total variation.

The exact centering identity is
\[
e(-(B_{\rm w}+B_{\rm a})\{X\})=e(-NX)e(-D\{X\}).
\]
Take R=floor(P^(5/16)). The bounded-coefficient version of the
centered Fourier lemma gives
\[
e(-D\{X\})=\sum_{|r|\le R}a_r(D)e(rX)+O(E_R(X)),
\quad
a_r(D)=\int_0^1 e(-(D+r)t)\,dt.
\]
Uniformly on the fixed compact range of D,
|a_r|+|a_r'| is O(1/(1+|r|)); the integral handles removable
singularities. The lemma for D in [0,1] extends to any fixed compact
range by the same Fourier tail proof.
The total error is O(P^(5/6)+P log(P)/R).

The actual carry-branch indicator is a finite union of arcs in
theta. Its endpoints are 0, 1, or 1-{Delta_i X}, including the
combined shift d_1+d_2. Subdivide by their order if needed; this
adds only a constant multiple of the original run count.
Expand an arc indicator at R_c=floor(P^(1/4)).
Its nonzero endpoint modes have coefficients O(1/|s|) and phases
sX(x+d_i); the zero coefficient has bounded variation per run.
The endpoint errors are E_(R_c)(X(x+d_i)), or E_(R_c)(X(x)),
whose positive sums are O(P^(5/6) log P).
If the indicator is expanded after the centered phase, its error
is multiplied by at most O(log P). No global error is multiplied
by the number of branch runs.

Every resulting mode has phase
\[
f_{r,s}=F_{\rm sm}+(r-N)X+sX(x+d_i).
\]
Put ell=r+s and write sX(x+d_i)=sX+s Delta_iX.
The extra curvature is O(|s|(h_1+h_2)P^(-3/2))=O(P^(-29/24)).
For fixed ell, the sum of coefficient sup norms plus variations
on a refined cell is bounded by
\[
M_\ell\ll{\log(2P)\over1+|\ell|},\qquad
|\ell|\ll P^{5/16}. \tag{S9}
\]
This follows by convolution of 1/(1+|r|) with 1/(1+|s|).
It includes zero modes and the constant arc coefficient.
The phases for different pairs (r,s) need not be identified:
the weighted version of (S4) uses their common curvature reference.

## 5. The combined curvature and its error

Freeze beta_i, floor(G), and N on a refined cell.
Direct differentiation of (S7) gives the reference
\[
\Lambda_{\ell,N}(x)
 =-{27\over32}\alpha x^{-3/4}
  -{243\over128}Kx^{-5/8}
  +{3\over4}(\ell-N)x^{-1/2}. \tag{S10}
\]
The anchor coefficient is nonzero. In particular, no lower bound
on |alpha| is assumed.

Here the frozen anchor identity is
\[
2c_d'G'+c_dG''
 =-{27\over128}k\beta_1\beta_2x^{-13/8}
   (1+O((h_1+h_2)/P)).
\]
The remaining c_d''(G-floor(G)) is O(kP^(-7/8)).
Substituting beta_1 beta_2 approximately 9p x only as values
produces the coefficient -243/128 in (S10).

All curvature errors, including psi and the shifted endpoint mode,
satisfy
\[
|f_{r,s}''-\Lambda_{\ell,N}|\ll_C P^{-3/4}. \tag{S11}
\]
Before inserting the parameter caps, the relevant terms are
\[
\begin{split}
&(|u|+|u'|)P^{-5/4}
 +( |u|h_1^2+|u'|h_2^2 )P^{-7/4}\\
&\quad+k(h_1+h_2)P^{-9/8}
 +K(h_1+h_2)P^{-13/8}
 +kP^{-7/8}+P^{-29/24}+|\psi''|.
\end{split}
\]
Each is O(P^(-3/4)). This bound covers large opposite coefficients
even when their signed sum is zero.

The complete cell partition has local count
O_C(1+LP^(-3/8)). To check this, the original run density is
O((h_1+h_2)P^(-1/2)); within each run, G is monotone with
|G'| comparable to pP^(-3/4), so its floor adds
O(1+pLP^(-3/4)) cuts there. The boundedly many arc-order cuts
and the B_w windows add a constant multiple of the run count
and O(1+LP^(-3/4)) cuts. All these densities are at most
O(P^(-3/8)); intersect with the stipulated partition of psi.
No derivative estimate is extended across a jump.

## 6. Small signed combination

Suppose A<=P^(1/32). There are O(P^(1/32)) N-windows.
On one window and for fixed ell, use (S4) with (S10).
The normalized scale obeys
\[
K P^{-5/8}\ll S\ll P^{-3/16},\qquad
\rho\ll P^{-1/8},\qquad \nu\ll P^{-3/8}.
\]
The upper bound uses |alpha|<=2P^(1/2),
|N|=O(P^(1/4)), and |ell|=O(P^(5/16)).
The four significant terms in (S4) are bounded respectively by
\[
P^{29/32},\quad P^{15/16}\log(2P),\quad
P^{21/32},\quad P^{15/16}.
\]
Thus the weighted sum for one window is
O(P^(15/16) log(P)^C), after summing (S9).
Summing the O(P^(1/32)) windows gives
\[
O(P^{31/32}\log(P)^C). \tag{S12}
\]
This includes alpha=0 and both exact cancellation identities from
the D2 report. The cost of a full ambient-scale estimate is
explicitly paid once for every window in this regime.

## 7. Large signed combination

Suppose A>P^(1/32). By (S8), B_w is monotone and a complete
N-window has length comparable to P/A; endpoint windows may be
shorter. There are O(A) windows.

On one window define
\[
L_N(x)=N+{9\over8}\alpha x^{-1/4}
          +{81\over32}Kx^{-1/8}.
\]
Then
\[
\Lambda_{\ell,N}(x)={3\over4}x^{-1/2}(\ell-L_N(x)).
\]
The image of L_N on the window has bounded length: its derivative
is O(A/P+1/P), and the window length is O(P/A).
Furthermore |L_N(x)| is comparable to A, because
N=(9/4)alpha x^(-1/4)+O(1) there and K P^(-1/8)<=1.

There are O(1) integer ell within a fixed, sufficiently large
distance of this image. Call them the resonant indices. All have
|ell| comparable to A, so (S9) bounds their total coefficient
sup norm by O(log(P)/A). Estimate these terms trivially over
all windows, at total cost
\[
O(P\log(P)/A). \tag{S13}
\]
This counts possible curvature cancellation by frequency and
preserves the coefficient weights.

For every other ell, put
d_ell=distance(ell,L_N(window)), which is bounded below.
Throughout the window, (S11) implies
|f_(r,s)''| comparable to d_ell P^(-1/2) with one sign.
This comparison holds for every pair giving the same ell;
the error O(P^(-3/4)) is smaller than a fixed multiple of P^(-1/2).

If the window has length L and meets C_N refined cells, the
second-derivative estimate gives, before its Fourier weight,
\[
L P^{-1/4}\sqrt{d_\ell}
 + C_N P^{1/4}d_\ell^{-1/2}.
\]
The elementary weighted sums are
\[
\begin{split}
\sum_{\ell\ {\rm nonres.}}{ \sqrt{d_\ell}\over1+|\ell|}
 &\ll P^{5/32}\log(2P),\\
\sum_{\ell\ {\rm nonres.}}{ d_\ell^{-1/2}\over1+|\ell|}
 &\ll A^{-1/2}\log(2P).
\end{split}
\]
For example, split at |ell| comparable to A and at
|ell-L_N| comparable to A. Near L_N the weight is O(1/A);
near zero the distance is comparable to A; in the far tail
the inverse-root summand is O(|ell|^(-3/2)).
The first bound also uses A=O(P^(1/4)) and |ell|=O(P^(5/16)).

Sum over windows. Their lengths sum to P, and their cell counts
sum to O(P^(5/8)); the O(A) window endpoints fit that budget.
Combining (S9) and (S13), the total is
\[
\ll\left(P/A+P^{29/32}+P^{7/8}A^{-1/2}\right)\log(P)^C
 \ll P^{31/32}\log(P)^C. \tag{S14}
\]
This proves (S2), after absorbing the earlier errors and fixed
logarithmic powers into P^epsilon.

## 8. Slow modes and D2 factors

For the extra slow term q Delta_1 Delta_2 Y, replace qF(m) by qG.
The total error is O(|q|pP^(-1/4)) and its added curvature is
O(|q|pP^(-7/4)); both fit the proof. This establishes the extra
term in Section 1.

The same argument allows a fixed number of the D2 factors
specified in the preceding supplement. Its centered reduction
has total error O(P^(15/16) log P), and each retained phase has
second derivative O(P^(-15/16)) in the stated ranges. Its run
density is O(P^(-11/24)) and its coefficient-window density is
O(P^(-17/24)), both within the partition allowance here.
The coefficient norms and variations cost a fixed power of log P.

Apply the weighted version of (S4), and in Section 7 use (S9)
multiplied by that fixed logarithmic mass. The reference phase
(S10) is unchanged, while the D2 terms enter (S11).
The absolute errors are charged before oscillatory estimates.
This proves a bound O_epsilon(P^(31/32+epsilon)) for the family
with any fixed number of those D2 factors.

The conclusion applies only when their parameter, derivative,
and partition conditions hold. It does not automatically include
the historical widened D1 decorations or arbitrary smooth remnants.

## 9. What has and has not been repaired

The maximum-individual-wave dominance inference is no longer
needed for this zero-offset family. The small-A case uses a
quadratic sublevel bound with the anchor coefficient retained.
The large-A case charges the few potentially cancelling
frequencies with their actual Fourier weights.

Centering only B_w is deliberate. Centering the total coefficient
and then substituting the moving center into a global curvature
formula can cancel the anchor term at leading order. In the proof
above N is fixed on each window and the bounded B_a remains in the
Fourier coefficients. No frequency is differentiated as though
its moving center were constant.

The remaining kernel question is now the wave-bearing family
with nonzero total Y frequency, including its widened D1
decorations, coefficient weights, and all partition boundaries.
The nonzero-offset anchor family and the transfer to the OOOEE
mixed modes also remain to be checked. Conditional exponent
arithmetic from the D2 report is not an unconditional kernel
bound.

This pass stops at that assembly requirement. It does not change
the main paper's theorem statements or its publication status.

## 10. Reproducibility and sources

The companion validate_paper_b_signed_waves.py checks the exact
cancellation identities, frozen curvature coefficients, quadratic
coordinate change, compact interpolation identities, coefficient
convolution controls, and exponent budgets. These are finite
algebra and bookkeeping controls, not independent validation of
asymptotic cancellation.

The exact floor identities and centered Fourier estimates used
here are in the [current manuscript](juggler_parity_discrepancy_note.md)
and the [D2 supplement](paper_b_d2_report.md).
The derivative estimate and differencing tools are classical;
see S. W. Graham and G. Kolesnik, Van der Corput's Method of
Exponential Sums, Cambridge University Press, 1991
([publisher excerpt](https://beckassets.blob.core.windows.net/product/readingsample/666252/9780521339278_excerpt_001.pdf)).
No literature-wide priority claim, independent peer review,
Lean formalization, or Zenodo upload is made.

