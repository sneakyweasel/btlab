# Paper B: bounded repair of the D2 expansion

9 September 2026. Research supplement to the 27/32 manuscript.

## Result and scope

The two identified D2 errors admit a repair on fixed carry-label
extensions. The reduction below has total absolute error
O(P^(15/16) log P), uniformly in the historical shift ranges.
Its retained modes have logarithmic coefficient mass on each window,
and their second derivatives are small relative to the undisturbed
differenced-wave curvature. The proof counts every original gap run.

This is a reduction lemma, not a bound for the complete decorated
exponential sum. It does not prove the OOOEE count, the general kernel,
or density 7/8. The published-candidate manuscript and its 27/32
certificate subfamily are unchanged.

A separate issue prevents propagation into an unconditional kernel
theorem: the historical zero-offset classification can select a
"dominant" wave by the maximum of two individual sizes although the
signed waves cancel. Section 8 gives an exact witness and states the
remaining estimate.

Decision: **PROMOTE** the D2 reduction and its error accounting.
The complete kernel remains open.

## 1. Parameters and the branch extension

Write e(t)=exp(2 pi i t). All constants below are absolute, or depend
on fixed constants in comparability bounds. Let P tend to infinity,
with integer parameters
\[
1\le k,h_1,h_2\le P^{1/24},\qquad 1\le h\le P^{1/8}.
\]
Put X(x)=x^(3/2), m(n)=floor(X(n)), and c(x)=3k x^(9/8)/4.
Work on (P,2P], extending the definitions to (P,3P] to accommodate
shifts. All estimates also hold after restriction to odd integers.

Partition by the integer parts of
X(x+2h_1)-X(x), X(x+2h_2)-X(x), and
X(x+2h_1+2h_2)-X(x). There are
\[
D\ll (h_1+h_2)P^{1/2}
\]
runs, and an interval of length L meets
O(1+(h_1+h_2)L P^(-1/2)) runs.

On each run freeze a carry label and its integer offsets
beta_1, beta_2, beta_12. Assume
beta_i is comparable to h_i P^(1/2), for i=1,2, and
j=beta_12-beta_1-beta_2 is a bounded integer, with |j|<=2
for the admissible branches used here. Define, on that run,
\[
\begin{split}
F(t)&=(t+\beta_1+\beta_2+j)^{3/2}
 -(t+\beta_1)^{3/2}-(t+\beta_2)^{3/2}+t^{3/2},\\
G(x)&=F(X(x)),\qquad A(n)=\lfloor F(m(n))\rfloor.
\end{split}
\]
The offsets may change between runs. The theorem treats any such
piecewise extension; no derivative crosses a run boundary.
There are only finitely many carry labels, so bounds for their
positive error terms can be summed. Reassembling oscillatory sums
with the actual carry indicators is a further step, not an assumption
that a branch extension is the physical orbit everywhere.

## 2. A counting lemma for a slow monotone variable

On an interval I of length L, suppose G is C^1 and
a<=|G'|<=C a, with 0<a<=1. Its derivative has constant sign.
For 0<delta<=1/2, the number of integer n in I with
distance(G(n),Z)<=delta is
\[
\ll \delta(L+a^{-1})+aL+1. \tag{D1}
\]
Indeed G(I) meets O(aL+1) integer neighborhoods. Each inverse image
is an interval of length O(delta/a), containing O(delta/a+1)
integers. This includes endpoints and exact integer values.

Let
\[
E_Q(t)=\min(1,(Q\|t\|)^{-1}),\qquad E_Q(t)=1\quad(t\in\mathbb Z).
\]
Splitting the distances to Z into dyadic bands gives
\[
\sum_{n\in I}E_Q(G(n))
 \ll {L+a^{-1}\over Q}\log(2Q)+aL+1. \tag{D2}
\]
The additive lattice-count cost is multiplied by a convergent
geometric sum, not by the number of bands.

Over D disjoint runs with a common comparable derivative scale,
these become
\[
\begin{split}
\#\{\|G(n)\|\le\delta\}
 &\ll \delta(P+D/a)+Pa+D,\\
\sum E_Q(G(n))
 &\ll {(P+D/a)\log(2Q)\over Q}+Pa+D. \tag{D3}
\end{split}
\]
Runs of different offset types are bounded separately. No
equidistribution assumption, random model, or rescaling of a global
exceptional set is used.

## 3. Derivative scales for the actual branch functions

Set p=h_1 h_2. The zero-offset part has the exact integral
representation
\[
F_0(t)={3\over4}\int_0^{\beta_1}\int_0^{\beta_2}
 (t+s+r)^{-1/2}\,dr\,ds.
\]
Consequently, with the beta values fixed when differentiating,
\[
\begin{split}
G_0'(x)&=-{9\over16}\beta_1\beta_2 x^{-7/4}(1+o(1)),\\
G_0''(x)&={63\over64}\beta_1\beta_2 x^{-11/4}(1+o(1)).
\end{split}
\]
The errors are uniform because (beta_1+beta_2)/X=o(1).

The offset contribution is
\[
{3j\over2}\int_0^1
 (t+\beta_1+\beta_2+s j)^{1/2}\,ds.
\]
After composition with X its first derivative is
(9j/8)x^(-1/4)(1+o(1)). For j nonzero it dominates the zero-offset
derivative, since p P^(-1/2)=o(1). Thus, on every run,
\[
|G'|\asymp
\begin{cases}
pP^{-3/4},&j=0,\\
P^{-1/4},&j\ne0,
\end{cases}
\qquad
|G''|\ll |j|P^{-5/4}+pP^{-7/4}. \tag{D4}
\]
Also |G| is O(|j|P^(3/4)+pP^(1/4)).
These are derivatives of frozen-offset functions, not derivatives
of the approximations beta_i approximately 3h_i sqrt(x).

Take Q=floor(P^(5/16)). For j=0, the potentially largest term in
(D3) is
\[
{D\over Qa}\ll {h_1+h_2\over h_1h_2}P^{15/16}
 \ll P^{15/16}.
\]
The other terms are P^(11/16), pP^(1/4), and D.
For j nonzero, (D3) is O(P^(3/4) log P).
It follows that, summed over all runs of either type,
\[
\sum E_Q(G(n))\ll P^{15/16}\log P. \tag{D5}
\]

The replacement of m by X is used only inside the floor, after
counting its exceptional set. The mean value theorem gives
\[
|F(m(n))-G(n)|
 \ll |j|P^{-3/4}+pP^{-5/4}=:\delta.
\]
A floor mismatch requires G(n) to lie within delta of an integer.
For either derivative scale in (D4), delta/a=O(P^(-1/2)).
The first line of (D3) therefore proves
\[
\#\{n:A(n)\ne\lfloor G(n)\rfloor\}\ll P^{3/4}. \tag{D6}
\]
This remains useful when c is large: changing a unit exponential
costs at most two on the exceptional set. A large coefficient is
never multiplied by an uncontrolled pointwise floor error.

## 4. Replace the small-increment carry by floor-crossing counts

Exclude for the moment n whose interval from n to n+2h crosses
an original run boundary. There are O(hD) such integers.

Within a run, G is monotone. If
floor(G(n+2h)) differs from floor(G(n)), this interval contains an
integer-level crossing of G. There are O(aL+1) levels on a run of
length L, and any crossing belongs to at most O(h) such integer
starting intervals. Including the original run boundaries gives
\[
\#\{\hbox{floor change or run crossing}\}
 \ll h(Pa+D)\ll P^{7/8}. \tag{D7}
\]
For zero offset the bound is even smaller; the uniform largest term
is hP^(3/4) from nonzero offsets.

Write B(x)=c(x+2h)-c(x). Using (D6) at both endpoints and then
(D7), we obtain the following statement in the sum of absolute
errors:
\[
e\bigl(-\Delta_{2h}(cA)(n)\bigr)
 =e\bigl(-B(n)\lfloor G(n)\rfloor\bigr)+\mathcal E_n,
\qquad
\sum|\mathcal E_n|\ll P^{7/8}. \tag{D8}
\]
Both expressions in this comparison are unimodular. The second
expression is defined on every run, including the exceptional
starting points; no irregularly punctured domain is passed to a
derivative test.

This repairs the D2(b) carry step directly. For comparison, on
zero-offset runs |Delta G| is O(hpP^(-3/4)); at the historical carry
cutoff J=floor(P^(1/8)), J|Delta G|=o(1). Therefore the distance
majorant E_J(Delta G) equals one for sufficiently large P.
The standard sawtooth Fourier approximation has an order-one
endpoint error there as well. Small drift alone cannot justify the
historical O(P/J) charge for this individual layer. The exact carry
combination may cancel; (D7) preserves that cancellation by counting
the floor change before expansion.

## 5. Center the D2(a) coefficient

The coefficient B is increasing, with
\[
B\asymp khP^{1/8},\quad
B'\asymp khP^{-7/8},\quad
|B''|\ll khP^{-15/8}.
\]
Refine the original runs by N=floor(B), and put beta=B-N.
The extra number of cuts is O(1+khP^(1/8)).
The exact identity
\[
e(B\{G\})=e(NG)e(\beta\{G\})
\]
centers the frequency before truncation.

For 0<=beta<=1 let
\[
a_r(\beta)=\int_0^1 e((\beta-r)t)\,dt.
\]
By the centered Fourier lemma in the current Paper B, or its
complex conjugate,
\[
e(\beta\{G\})
 =\sum_{|r|\le Q}a_r(\beta)e(rG)+O(E_Q(G)).
\]
The integral definition includes the removable singularity.
Both |a_r| and |a_r'| are O(1/(1+|r|)). On each refined interval,
beta is monotone and has variation at most one, so
\[
\sum_{|r|\le Q}
 \left(\|a_r(\beta)\|_\infty+\operatorname{TV}(a_r(\beta))\right)
 \ll\log(2Q).
\]

Combining this expansion with (D5) and (D8) proves the D2 reduction:
\[
\begin{split}
e\bigl(-\Delta_{2h}(cA)(n)\bigr)
 &=\sum_{|r|\le Q}a_r(\beta(n))e(\Phi_r(n))+\mathcal R_n,\\
\Phi_r(x)&=(N+r-B(x))G(x),\\
\sum_{P<n\le2P}|\mathcal R_n|&\ll P^{15/16}\log P. \tag{D9}
\end{split}
\]
N and all offsets are fixed only within the refined interval.
The error sum is charged once on the original runs; it is not
multiplied by the number of frequency windows. This is valid with
any additional weight of modulus at most one. A fixed number of
D2 factors can be expanded by telescoping, at a fixed extra power
of log P and with the same power saving.

This replacement uses the bounded residual beta, so it has no
unaccounted continuous-part tail between Q and P^(1/2).

## 6. Curvature and boundary accounting for the retained modes

Differentiate with N and r fixed:
\[
\Phi_r''=(N+r-B)G''-2B'G'-B''G.
\]
Since N+r-B=r-beta, (D4) yields
\[
|\Phi_r''|\ll
(Q+1)(|j|P^{-5/4}+pP^{-7/4})
+kh(|j|P^{-9/8}+pP^{-13/8}). \tag{D10}
\]
For an undisturbed wave curvature M=uhP^(-3/4), u>=1/2,
the four exponent bounds for this ratio are respectively
\[
P^{-3/16},\quad P^{-29/48},\quad
P^{-1/3},\quad P^{-3/4}.
\]
Thus |Phi_r''|=O(P^(-3/16)M), uniformly.

Where a total phase already has curvature comparable to M, the
extra endpoint cost in the second-derivative estimate is
\[
\begin{split}
(D+1+khP^{1/8})M^{-1/2}
\ll{}&(h_1+h_2)(uh)^{-1/2}P^{7/8}\\
&+k(h/u)^{1/2}P^{1/2}+(uh)^{-1/2}P^{3/8}.
\end{split} \tag{D11}
\]
Its largest uniform exponent is 11/12, below 15/16.
Partial summation uses the logarithmic variation bound in Section 5.

This comparison is not a declaration that an arbitrary sum of
signed waves has curvature comparable to M. At a curvature
cancellation, the reference-function and sublevel hypotheses must
still be verified for the complete phase.

## 7. What the losses would imply if the remaining sums were controlled

There are two useful bookkeeping outcomes.

First, keeping the historical uncentered expansion literally would
require restoring the omitted tail. Its continuous coefficients obey,
for |r| greater than 2|B|,
\[
|b_r|\ll {|B|\over r^2},
\qquad \sum_{|r|>Q}|b_r|\ll {|B|\over Q}.
\]
Since |B|=O(P^(7/24)), the resulting uniform absolute error is
O(P^(47/48)). This is an upper-bound cost, not an assertion that
the actual tail attains that size.

Second, the centered replacement (D9) has the better error exponent
15/16. If all other contributions to the innermost differenced
sum V also obey O(P^(15/16+epsilon)), then the usual van der Corput
inequality, with the historical third shift at least P^(1/12),
gives a wave bound O(P^(31/32+epsilon)).
If the entire doubly differenced kernel T_2 consequently obeys
that bound, the two outer shifts H_2=P^(1/24), H_1=P^(1/48) give
\[
T_2:\ P^{31/32+\varepsilon},\qquad
T_1:\ P^{63/64+\varepsilon},\qquad
K:\ P^{127/128+\varepsilon}. \tag{D12}
\]
All three diagonal terms fit these conditional budgets.
With the literal-tail error instead, the corresponding conditional
chain is 47/48 -> 95/96 -> 191/192 -> 383/384.

These are conditional implications from complete inner-sum bounds,
not newly proved kernel estimates. Finite Fourier support also means
a logarithmic loss in a total wave frequency is acceptable here;
recovering the old frequency-dependent factor is unnecessary for
the stated weaker target. Transfer from a kernel to all mixed modes
needed for OOOEE is another requirement.

## 8. The first remaining assembly obstruction

The historical Theorem 5.3, Step 5(b), classifies the zero-offset
anchor using a scale based on max(|u|h_1,|u'|h_2) for two signed
first-differenced waves
\[
u\,\Delta_{2h_1}Y+u'\,\Delta_{2h_2}Y.
\]
That maximum does not certify the curvature of their sum.

For h_1=h_2=1, u=L and u'=-L, the sum is identically zero.
One can take integer L comparable to P^(1/4), within the historical
continuous Fourier supports and the conditions
|u|h_1,|u'|h_2<=P^(1/2).
For k=1 the quoted individual-wave scale is comparable to P^(-1/2),
while the zero-offset anchor scale is P^(-5/8).
Their ratio tends to infinity, so the printed rule enters the
mode-dominant case even though the full wave contribution vanishes.

This refutes that dominance inference. It does not refute a bound
for the complete exponential sum, and it does not assert that every
such pair has nonzero Fourier weight in every specialized application.

Merging equal shifts fixes this example. Unequal shifts need the
same attention: with h_2=2h_1 and u'=-u/2 for even u,
\[
u\Delta_{2h_1}Y-\tfrac u2\Delta_{4h_1}Y
 =-\tfrac u2\Delta_{2h_1}^{\,2}Y.
\]
The remaining term has a new second-difference shape. Leading
curvature cancellation alone does not make it negligible.

The exact next question is:

Can the zero-offset anchor together with both signed differenced
waves, their carry modes, and all run boundaries be bounded by
O(P^(1-eta)) for some eta>0, after the reduction (D9), uniformly over
the Fourier supports actually retained?

A successful estimate must use the combined signed phase and its
weights, including equal-shift and leading-cancellation cases.
The single-wave collision model in the current manuscript does
not yet supply that result. This is the stopping point of this pass.

## 9. Validation and publication status

The accompanying validate_paper_b_d2.py checks exact centering and
product-difference identities, both signed cancellation identities,
the frozen derivative coefficients, and all displayed exponent
budgets using rational arithmetic. Its finite checks support the
written proof; they do not prove asymptotic cancellation.

No independent peer review, Lean formalization, stronger certificate
density, Zenodo upload, or manuscript release change is claimed.

The centered Fourier tool is Lemma 4.7 of the
[current manuscript](juggler_parity_discrepancy_note.md).
Classical derivative estimates and differencing are used as described
in S. W. Graham and G. Kolesnik, Van der Corput's Method of Exponential
Sums, Cambridge University Press, 1991
([publisher excerpt](https://beckassets.blob.core.windows.net/product/readingsample/666252/9780521339278_excerpt_001.pdf)).
This supplement makes no literature-wide priority claim.

