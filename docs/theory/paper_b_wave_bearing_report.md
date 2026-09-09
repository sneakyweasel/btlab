# Paper B: the wave-bearing family with widened D1 terms

9 September 2026. Research supplement to the 27/32 manuscript.

## Outcome and scope

The family with nonzero total Y frequency has the written estimate
\[
U(P)\ll_{C,M,\varepsilon}P^{31/32+\varepsilon}.
\]
It includes finitely many signed first differences with the widened
coefficient range, piecewise constant coefficients on the specified
coarse partition, and the D2 floor factors from the preceding repair.

The useful simplification is to differentiate each twice-differenced
D1 branch with respect to the floored variable m. Its floor error is
small enough to discard in the sum, even at the widened frequencies.
After this replacement the nonzero main wave controls the curvature
for all but a fixed number of differencing shifts.

Decision: **PROMOTE** this family estimate and the D1 linearization.
This is an AI-assisted written proof, with exact algebra and exponent
controls; it has not received independent mathematical review or
Lean verification. It does not prove the complete kernel, the OOOEE
count, or density 7/8. The 27/32 manuscript and deposit package are unchanged.

## 1. A precise family

Let e(v)=exp(2 pi i v), and put
\[
X(x)=x^{3/2},\quad m(n)=\lfloor X(n)\rfloor,\quad
Y(n)=m(n)^{3/2},\quad \Delta_d f(x)=f(x+d)-f(x).
\]
All functions are defined on [P,3P], with harmless further extension
at its upper endpoint if needed. Constants C and M are fixed.
All estimates concern sufficiently large P depending only on them.
Let t be real and fixed throughout the sum, with
\[
\tfrac12\le |t|\le CP^{1/24}.
\]
There are at most M first-difference terms, with even shifts e_j>=0
and positive integer half-shifts r_j satisfying
\[
e_j\le CP^{1/24},\qquad 1\le r_j\le CP^{1/24},
\qquad |a_j(x)|r_j\le CP^{1/2}. \tag{W1}
\]
The real coefficients a_j are constant separately on the cells of an
interval partition \(\mathcal P\). Any interval of length L meets at
most C(1+L P^(-11/24)) cells of this partition. In particular, its
total cell count is O_C(P^(13/24)). The real function phi is C^3
on each cell and satisfies
\[
|\phi'''(x)|\le CP^{-13/12}. \tag{W2}
\]
No continuity across cell boundaries is required. The complex
amplitude eta satisfies
\[
\|\eta\|_{\infty,I}+\operatorname{TV}_I(\eta)\le C
\]
on each cell I. Endpoint values are assigned consistently; their
possible exceptional contribution is covered by the cell count.

We also allow at most M terms \(-\sigma_\ell c_\ell A_\ell\), where
sigma belongs to {-1,0,1}. These are the fixed-label D2 objects of
the [D2 supplement](paper_b_d2_report.md), with
\[
1\le k_\ell,h_{\ell,1},h_{\ell,2}\le CP^{1/24},
\qquad c_\ell(x)=\tfrac34 k_\ell(x+v_\ell)^{9/8}.
\]
The integers k and h are positive. The base shift s_ell and the
coefficient shift v_ell are nonnegative even integers O_C(P^(1/24)).
To specify the object unambiguously, partition by the integer parts of
\[
X(x+s_\ell+2h_{\ell,i})-X(x+s_\ell),\qquad
X(x+s_\ell+2h_{\ell,1}+2h_{\ell,2})-X(x+s_\ell).
\]
On every such original run choose fixed admissible carry offsets
beta_1,beta_2,beta_12, with beta_i comparable to h_i sqrt(P) and
j=beta_12-beta_1-beta_2 a bounded integer (|j|<=2 suffices). Set
\[
\begin{split}
F_\ell(z)&=(z+\beta_1+\beta_2+j)^{3/2}
 -(z+\beta_1)^{3/2}-(z+\beta_2)^{3/2}+z^{3/2},\\
G_\ell(x)&=F_\ell(X(x+s_\ell)),\\
A_\ell(n)&=\lfloor F_\ell(m(n+s_\ell))\rfloor.
\end{split}
\]
The version \(A_\ell(n)=\lfloor G_\ell(n)\rfloor\) is also allowed.

The partition \(\mathcal P\) refines these original runs. Further
refinement does not change their chosen labels: it cannot introduce
new arbitrary jumps in F_ell or G_ell. All D2 counting errors below
are evaluated on the original runs. These floors are not first
partitioned into their integer level sets.

Under these hypotheses the theorem is
\[
\begin{split}
U(P)=\sum_{\substack{P<n\le2P\\n\ {\rm odd}}}\eta(n)e\Big(
 tY(n)+\sum_j a_j(n)\Delta_{2r_j}Y(n+e_j)
 -\sum_\ell\sigma_\ell c_\ell(n)A_\ell(n)+\phi(n)\Big),\\
|U(P)|\ll_{C,M,\varepsilon}P^{31/32+\varepsilon}. \tag{W3}
\end{split}
\]
The hypotheses on the partition and phi must be verified in any
application; they do not permit arbitrary additional floor factors
or a smooth twist that cancels the main wave.

## 2. The widened D1 linearization

Fix an A-process half-shift \(1\le h\le P^{1/12}\). On an actual
carry branch for z=n+e, put
\[
m(z+2h)=m(z)+\beta_1,\quad
m(z+2r)=m(z)+\beta_2,\quad
m(z+2h+2r)=m(z)+\beta_1+\beta_2+j.
\]
Then
\[
\Delta_{2h}\Delta_{2r}Y(z)=F_j(m(z)),
\]
where F_j has the same four-term form as F_ell above. Uniformly,
beta_1 is comparable to h sqrt(P), beta_2 to r sqrt(P), and |j|<=2.
The latter follows because the corresponding real mixed difference
of X is O(hr P^(-1/2))=o(1).

The exact integral formulas, with the beta values frozen, are
\[
\begin{split}
F_0(v)&=\tfrac34\int_0^{\beta_1}\int_0^{\beta_2}
                    (v+b+c)^{-1/2}\,dc\,db,\\
F_j(v)-F_0(v)&=\tfrac{3j}{2}\int_0^1
                    (v+\beta_1+\beta_2+\tau j)^{1/2}\,d\tau .
\end{split} \tag{W4}
\]
They hold for both signs of j. Differentiating with respect to v gives
\[
|F_j'(v)|\ll |j|P^{-3/4}+hrP^{-5/4},\qquad v\asymp P^{3/2}. \tag{W5}
\]
Since 0<=X(z)-m(z)<1, replacing F_j(m(z)) by F_j(X(z)) in
the exponential costs at most a constant times |a| times (W5).
The error summed over all integers in the dyadic interval is
\[
\ll |a|P^{1/4}+|a|hrP^{-1/4}
\ll_C P^{3/4}/r+hP^{1/4}
\ll_C P^{3/4}. \tag{W6}
\]
This is one global charge; it is not paid again on each branch.

A second differentiation after composition gives
\[
|(F_j\circ X)''|\ll |j|P^{-5/4}+hrP^{-7/4}.
\]
Consequently the retained D1 curvature is at most
\[
C\big(P^{-3/4}/r+hP^{-5/4}\big). \tag{W7}
\]
The leading frozen coefficients provide a useful check:
\[
\begin{array}{c|cc}
 & F_j'(v) & (F_j\circ X)''(x)\\ \hline
\text{offset part} & (3j/4)v^{-1/2} & -(9j/32)x^{-5/4}\\
\text{zero-offset part} & -(3\beta_1\beta_2/8)v^{-3/2}
 & (63\beta_1\beta_2/64)x^{-11/4}.
\end{array}
\]
These are leading terms with uniform smaller remainders, not exact
equalities for finite beta. One must not differentiate the moving
approximation beta_i approximately 3h_i sqrt(x).

The historical D1 argument used a larger floor-error upper bound.
(W5) strengthens that estimate; it does not refute the older
inequality. No large Fourier expansion of this D1 floor error is needed.

## 3. Differencing and the nonzero main wave

Choose \(H=\lfloor P^{1/12}\rfloor\). Apply van der Corput differencing
to the sequence indexed by the odd integers, using shifts 2h:
\[
|U|^2\ll_C P^2/H+(P/H)\sum_{1\le h<H}|V_h|. \tag{W8}
\]
Here V_h is the correlation on the overlap of the original interval
and its translate. At most O_C(h P^(13/24)) starting points cross
a cell boundary of \(\mathcal P\). Their contribution is
O_C(P^(5/8)) for each h. On each remaining stable interval
I intersect (I-2h), all a_j are constant, the product of the two
amplitudes has bounded variation O_C(1), and
\[
|(\Delta_{2h}\phi)''|\le 2h\sup_I|\phi'''|
\ll_C hP^{-13/12}. \tag{W9}
\]
We apply all derivative tests to these intervals, never to a
domain punctured by individual exceptional integers.

Let theta(n)={X(n)}. Taylor's theorem gives
\[
Y(n)=n^{9/4}-\tfrac32\theta(n)n^{3/4}+E(n),
\qquad |E(n)|\ll P^{-3/4}.
\]
On a fixed main carry branch write beta=m(n+2h)-m(n), and put
\[
A_h(x)=\Delta_{2h}(x^{9/4})
          -\tfrac32\Delta_{2h}X(x)(x+2h)^{3/4}.
\]
The exact resulting decomposition is
\[
\Delta_{2h}Y(n)= A_h(n)+\tfrac32\beta(n+2h)^{3/4}
 -\tfrac32\theta(n)\Delta_{2h}(n^{3/4})+\Delta_{2h}E(n). \tag{W10}
\]
The theta term and E term cost, over the full correlation,
\[
O(|t|hP^{3/4}+|t|P^{1/4})=O_C(P^{7/8}). \tag{W11}
\]
Taylor expansion of the smooth A_h, with derivatives, gives
\[
A_h''=O(h^2P^{-7/4}).
\]
On each branch beta=3h sqrt(x)+O(1+h^2P^(-1/2)) as a
comparison of values. Holding beta fixed in differentiation, the
main retained phase therefore has
\[
\left(tA_h+\tfrac{3t}{2}\beta(x+2h)^{3/4}\right)''
 =-\tfrac{27}{32}thx^{-3/4}(1+o(1)). \tag{W12}
\]
The o(1) is uniform for 1<=h<=H and for all admissible branches.

Write \(M_h=|t|hP^{-3/4}\). The ratio of the combined D1 curvature
in (W7) to M_h is
\[
O_{C,M}\big((|t|h)^{-1}+P^{-1/2}/|t|\big).
\]
Choose a sufficiently large constant h_0=h_0(C,M), independent
of P. For h>=h_0 this ratio is smaller than a fixed fraction of
the lower constant in (W12). The twist ratio in (W9) is
O_C(P^(-1/3)/|t|). Thus all these terms preserve the one-signed
main curvature. This argument permits arbitrary signs and mutual
cancellation among the D1 coefficients.

There are only O_{C,M}(1) shifts h<h_0. The trivial bound |V_h|<=C P
for these shifts contributes O_{C,M}(P^2/H) to (W8).
Small values of P for which H<h_0 are covered by the implied constant.

## 4. Insert the D2 reduction on its original runs

Use (D9) of the D2 supplement at this h, with Q=floor(P^(5/16)).
Translations of the base and coefficient by O_C(P^(1/24)) preserve
all derivative comparisons and run counts in that proof. Conjugation
handles sigma=-1, and sigma=0 contributes the constant factor one.

For each factor, outside an error whose sum of absolute values is
O_C(P^(15/16) log P), the retained modes are
\[
e(\Phi_{\ell,q}),\qquad
\Phi_{\ell,q}=(N_\ell+q-B_\ell)G_\ell,\quad
B_\ell=\Delta_{2h}c_\ell,\quad N_\ell=\lfloor B_\ell\rfloor ,
\]
or their conjugates. Here |q|<=Q and on each coefficient window
the total coefficient sup norms plus variations are O(log P).
For a fixed number of factors these become a fixed power of log P.

Every such mode has
\[
|\Phi_{\ell,q}''|\ll_C P^{-15/16}. \tag{W13}
\]
The ratio to M_h is O_C(P^(-3/16)/(|t|h)), and so preserves (W12).
The additional coefficient-window count is
\[
O_C(1+k_\ell hP^{1/8})=O_C(P^{1/4});
\]
the original D2 run count is O_C(P^(13/24)). Both are retained
in the common partition below.

For clarity, the P^(15/16) error includes floor mismatches and
floor-crossing events. Those are compared in absolute value with
unimodular expressions and then replaced on full intervals. Their
counts are taken on the original D2 runs before any extra refinement.
Allowing fresh D2 labels on every added input cell would not be
justified by that count and is explicitly excluded in Section 1.

## 5. Reassemble the actual first-level carries

There are finitely many first-floor evaluations in the main wave
and the D1 terms. All have the form m(n+s), with s an even
nonnegative integer O_C,M(h+P^(1/24)). Use the single variable
theta={X(n)} and
\[
m(n+s)-m(n)=b_s+
 {\bf1}_{\,\theta\ge 1-\delta_s},\qquad
b_s=\lfloor X(n+s)-X(n)\rfloor,\quad
\delta_s=\{X(n+s)-X(n)\}.
\]
The convention when delta_s=0 is that this indicator is zero
for 0<=theta<1.

Partition by all b_s, the stable input cells, and the D2 coefficient
windows. The total number D_h of cells is
\[
D_h\ll_{C,M}(h+P^{1/24})P^{1/2}. \tag{W14}
\]
Indeed each gap has derivative O(s P^(-1/2)), the coarse cells
number O(P^(13/24)), and the extra D2 windows number O(P^(1/4)).
On each gap run each delta_s is monotone and varies by at most one.
Sort their endpoints 1-delta_s; two distinct endpoints cross at most
once on such a run, because the difference of the corresponding
real gaps is monotone. Equal shifts give identical endpoints.
This adds only O_C,M(1) cuts per cell.

A joint carry pattern is now a fixed finite union of intervals of
theta, with endpoints 0,1, or 1-delta_s. Its Fourier expansion
truncated at R=floor(P^(1/4)) has:
- a zero-mode coefficient with sup norm plus variation O_C,M(1);
- endpoint modes with coefficients O_C,M(1/|v|), 0<|v|<=R,
  multiplying e(vX(n+s)) for one of the allowed s (s=0 included);
- an absolute remainder bounded by a constant times the sum of
  E_R(X(n+s)) over these finitely many endpoints, where
  E_R(z)=min(1,1/(R||z||)), with value one at integers.

This is the usual interval Fourier expansion: a moving endpoint
u=1-delta_s supplies e(-v u), and, since b_s is integer,
e(vX(n))e(-v(1-delta_s))=e(vX(n+s)). Thus the moving
endpoint belongs in the phase, not in an unbounded-variation
coefficient. Zero-length intervals and points at endpoints are
covered by the positive remainder.

Here is the global bound needed for that remainder:
\[
\sum_{P<n\le2P}E_R(X(n+s))\ll_{C,M}P^{5/6}\log(2P). \tag{W15}
\]
It holds also over odd integers or a subinterval. To verify it,
the second-derivative test for vX(x+s) gives
O(|v|^(1/2)P^(3/4)+|v|^(-1/2)P^(1/4)).
The interval-discrepancy inequality with auxiliary cutoff
K=floor(P^(1/6)) then gives discrepancy O(P^(5/6)).
Dyadic bands for the distance to an integer give
O(P log(2R)/R+P^(5/6)), which implies (W15).
The remainder is charged once over the common input interval.
It is not multiplied by D_h. Products with the D2 expansions
introduce at most a fixed logarithmic factor.

## 6. Sum every retained mode and every cell

After the preceding replacements, the zero carry mode has
one-signed curvature comparable to M_h, uniformly in the D2 indices.
On a cell of length L the second-derivative test gives
O(L sqrt(M_h)+M_h^(-1/2)), also for any subinterval and the odd lattice.
Partial summation applies to eta and all Fourier coefficients.
Their total sup norms plus variations on each cell are at most
a fixed power of log P. Summing lengths and all D_h endpoints gives
\[
\begin{split}
P\sqrt{M_h}+D_h M_h^{-1/2}
\ll_{C,M}{}&
(|t|h)^{1/2}P^{5/8}\\
&+\left(\sqrt{h/|t|}
       +P^{1/24}(|t|h)^{-1/2}\right)P^{7/8}.
\end{split} \tag{W16}
\]
For h_0<=h<=P^(1/12) and the stated t range this is
O_C,M(P^(11/12)), before logarithmic losses.

For a nonzero carry Fourier mode v, its extra curvature is
vX''(x+s), of size |v|P^(-1/2). All other curvatures together
are O_C,M(M_h), and
\[
\frac{M_h}{|v|P^{-1/2}}
 \ll_{C,M}P^{-1/8}.
\]
Thus these modes also have one-signed curvature of the claimed size.
Summing their 1/|v| weights and all cell endpoints gives
\[
R^{1/2}P^{3/4}+D_h P^{1/4}
\ll_{C,M}P^{7/8}+(h+P^{1/24})P^{3/4}. \tag{W17}
\]
This is O_C,M(P^(7/8)) in the full range. A common reference
curvature and uniform cell count make this bound valid after summing
the coefficient masses of every D2 mode; no factor Q or D_h is
hidden in that mass.

Combining the absolute errors (W6), (W11), (W15), the D2 error,
the coarse-boundary cost, and (W16)--(W17), for every h>=h_0,
\[
|V_h|\ll_{C,M}P^{15/16}(\log(2P))^{B}, \tag{W18}
\]
where B depends only on M. The largest cost is the D2 error.
Substitution in (W8), with the finitely many small shifts treated
as in Section 3, yields
\[
|U|^2\ll_{C,M}
 P^{23/12}+P^{31/16}(\log(2P))^{B}.
\]
Since 23/12<31/16, this proves (W3), absorbing logarithms into
an arbitrarily small positive power of P.

## 7. How far this repairs the historical argument

A finite shifted-wave expression can be written exactly as
\[
\sum_{d\in\mathcal D}q_dY(n+d)
 =tY(n)+\sum_{\substack{d\in\mathcal D\\d\ne0}}
                      q_d\Delta_dY(n),\qquad
t=\sum_{d\in\mathcal D}q_d. \tag{W19}
\]
The identity holds even if 0 was not an original shift. Choosing
base zero avoids an incomplete inventory of pairwise differences.
For even d=O(P^(1/24)) and |q_d|=O(P^(1/24)), the seed
differences satisfy |q_d|(d/2)=O(P^(1/12)), within (W1).
Additional widened terms satisfying |u|h_i<=CP^(1/2) also fit.
Both signs of t are covered when |t|>=1/2.

There is room in (W2) for the natural smooth nonzero-offset pieces:
on a frozen original D2 run,
\[
(cG)'''=O_C(k|j|P^{-9/8}+kh_1h_2P^{-13/8})
       =O_C(P^{-13/12}).
\]
A constant frequency w=O(P^(5/12)) multiplying X likewise
satisfies |(wX)'''|=O(P^(-13/12)). These observations explain
the twist budget; they do not authorize an arbitrary additional
floor partition. In particular, splitting a nonzero-offset A into
its individual integer levels before applying (W3) generally has
too many cells for the hypothesis in Section 1.

The next bounded question is the nonzero-offset anchor family
with zero total Y frequency, including its signed decorations.
After that estimate, a separate audit must verify the whole kernel
decomposition, coefficient weights, carry restrictions, and every
mixed mode required for OOOEE. The conditional outer exponent chain
in the D2 supplement cannot yet be promoted to a kernel theorem.
This pass stops at (W3).

## 8. Validation and references

The accompanying validate_paper_b_wave_bearing.py checks frozen
leading coefficients, exact differencing and shifted-wave identities,
common-carry endpoint identities, and rational exponent budgets.
These checks support the written derivation; finite algebra tests
do not independently establish asymptotic cancellation.

The centered Fourier and interval expansions use the tools stated in
the [current manuscript](juggler_parity_discrepancy_note.md).
The D2 error and coefficient-variation statements are proved in the
[D2 supplement](paper_b_d2_report.md). The
[signed zero-offset supplement](paper_b_signed_waves_report.md)
handles a different family.

Classical differencing, second-derivative tests, and discrepancy
estimates are used in their standard forms; see S. W. Graham and
G. Kolesnik, Van der Corput's Method of Exponential Sums,
Cambridge University Press, 1991
([publisher excerpt](https://beckassets.blob.core.windows.net/product/readingsample/666252/9780521339278_excerpt_001.pdf)).
No literature-wide priority claim, independent review, stronger
certificate density, or Zenodo upload is asserted.

