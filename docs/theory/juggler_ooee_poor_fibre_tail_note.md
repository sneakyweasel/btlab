# A poor-fibre tail for the actual OOEE production

22 September 2026. **EXACT — HUMAN PROOF** in the laboratory's terminology:
an AI-assisted written argument, pending independent mathematical review.
The analytic estimates below are not Lean-verified. Existing Lean identities
cover the linearization remainder and the carry algebra, not this theorem.

Branch: [actual OOEE fibres](../problems/juggler_ooee_poor_fibres.md).
This note resolves that branch's missing poor-target inclusion. It does not
prove growing-depth estimates, termination, or a new contagion exponent.

## 1. Statement and exact objects

For positive integers n put

\[
 O(n)=\lfloor n^{3/2}\rfloor,\quad Q(n)=\lfloor\sqrt n\rfloor,
 \quad a(n)=n+(n\bmod2),\quad
 w(n)=\log\frac{a(n)+1}{a(n)-1}.
\]

Let F_m contain exactly those n for which n and O(n) are odd,
O^2(n) and Q(O^2(n)) are even, and Q^2(O^2(n))=m. Thus F_m is the
actual OOEE predecessor fibre, with all four parity guards. Write

\[
 W_m=\sum_{n\in F_m}w(n),\qquad R_m=W_m/w(m).
\]

**Theorem 1 (poor-fibre tail).** For every fixed 0<eta<1/9,

\[
 \sum_{m\ge U:\ R_m<1/9-\eta}\frac1m
       \ll_\eta U^{-7/9}\qquad(U\ge1).
 \tag{1}
\]

The implied constant and the onset of the estimates may depend on eta.
No numerical onset is asserted. The proof also applies to the set
where |R_m-1/9|>eta. It does not claim uniform convergence at every target.
The exact empty fibres in the branch dossier are consistent with (1).

Set B(a)=ceil(a^(2/3)) and A_m=B(B(m^4)). The formal, unguarded
preimage of m under Q^2 O^2 is exactly

\[
 I_m=[A_m,A_{m+1})\cap\mathbb N.
 \tag{2}
\]

Indeed O(n)>=a iff n^3>=a^2, and Q^2(v)=m iff m^4<=v<(m+1)^4.
The ceilings give

\[
 m^{16/9}\le A_m\le m^{16/9}+2.
\]

Consequently, with P=m^(16/9) and H_m the number of odd integers in I_m,

\[
 |I_m|=\frac{16}{9}m^{7/9}+O(1),\qquad
 H_m=\frac89m^{7/9}+O(1),\qquad I_m\subseteq[P,2P]
 \tag{3}
\]

for all sufficiently large m. Interval length here means the difference
of its real endpoints; integer counts differ by at most a constant.
On odd n in I_m, w(n)=2/P times 1+O(1/m), uniformly. Also
w(m)=2/m times 1+O(1/m). Writing C_m=|F_m| gives

\[
 R_m=\frac89\frac{C_m}{H_m}+O(m^{-7/9}).
 \tag{4}
\]

The larger error m^(-7/9), rather than m^(-1), retains the integer
rounding in H_m. All constants in (2)--(4) are absolute.

## 2. Classical analytic inputs

Write e(t)=exp(2*pi*i*t). We use the following classical forms on arbitrary
real intervals, retaining an absolute endpoint term when necessary:

- If f' is monotone and stays at distance at least lambda from every
  integer, the Kusmin--Landau bound is O(1+lambda^(-1)).
- If lambda<=|f''|<=C lambda, then the second-derivative bound on an
  interval of length L is O_C(1+L sqrt(lambda)+lambda^(-1/2)).
- For N consecutive terms of modulus at most one and integer 1<=D<=N,
  van der Corput differencing bounds the square of their sum by
  O(N^2/D+(N/D) sum_{1<=h<D}|T_h|), with overlap correlations T_h.
- The one- and three-dimensional Erdős--Turán--Koksma inequalities bound
  unnormalized interval or box discrepancy by the count divided by K,
  plus the finite Fourier sums weighted by the product of
  1/max(1,|k_j|), for frequencies at most K.

These are the same tools as in [Paper B, Sections 3--4](juggler_parity_discrepancy_note.md).
For accessible statements and a proof of the differencing inequality, see
[Jammes, Section 2](https://math.univ-cotedazur.fr/~pjammes/publications/diviseurs95.pdf).
The second-derivative bound is also stated as Theorem 10 in
[Bergelson--Richter](https://people.math.osu.edu/bergelson.1/BR_DensityCoprime.pdf).
The discrepancy reference is Kuipers--Niederreiter, *Uniform Distribution
of Sequences*, Chapter 2, already indexed as
`kuipers-niederreiter-1974-uniform-distribution`.
No qualitative Hardy-field or global-count localization is used.

## 3. The short mixed estimate

For real x>=3 define X(x)=x^(3/2), Z(x)=x^(9/8); for integer n put
M(n)=floor(X(n)), Y(n)=M(n)^(3/2).

**Lemma 2 (fixed mixed modes).** Fix constants K,L_0>=1. For every
integer triple (i,j,k) with max(|i|,|j|,|k|)<=K and (i,j)!=(0,0),
and every interval I in [P,2P] of length at most L_0 P^(7/16),

\[
 \sum_{n\in I,\ n\text{ odd}}
 e\left(\tfrac i2 X(n)+\tfrac j2 Y(n)+\tfrac k2 Z(n)\right)
       \ll_{K,L_0} P^{13/32}.
 \tag{5}
\]

K is fixed independently of P. This lemma expressly excludes the pure
slow modes (0,0,k). No estimate uniform in growing K is asserted.

### 3.1 The carry approximation on a short interval

Let b(t)={t}-1/2. For integer R>=2 set

\[
 b_R(t)=-\sum_{1\le|r|\le R}\frac{e(rt)}{2\pi i r},\qquad
 E_R(t)=\min\{1,(R\|t\|)^{-1}\},
\]

with E_R=1 at integers. The ordinary truncated Fourier series satisfies
b=b_R+O(E_R), including at integers; Paper B Lemma 4.3 proves this
pointwise assertion. We re-estimate its total error at the current length.

For any interval J in [P,3P] of length at most L_0 P^(7/16),
the second-derivative test on the odd lattice gives

\[
 \left|\sum_{n\in J,\ n\text{ odd}} e(rX(n))\right|
 \ll_{L_0} P^{3/16}|r|^{1/2}+P^{1/4}|r|^{-1/2}+1.
 \tag{6}
\]

Here x=2t+1 only changes fixed curvature constants. Apply the
one-dimensional discrepancy inequality with R=floor(P^(1/8)). Its
error is at most

\[
 O\left(P^{7/16}/R+P^{3/16}R^{1/2}+P^{1/4}+\log(2R)\right)
       =O(P^{5/16}).
\]

Splitting distances to the nearest integer into dyadic ranges starting
at 1/R therefore gives

\[
 \sum_{n\in J,\ n\text{ odd}} E_R(X(n))
          \ll_{L_0} P^{5/16}\log P.
 \tag{7}
\]

For clarity: at distance at most z there are O(z P^(7/16)+P^(5/16))
points. Each dyadic range contributes O(P^(7/16)/R) from its length,
while the discrepancy contribution forms a geometric sum. This also
counts exact integer values of X. The same bound holds for X(n+2h)
by translation of the odd interval. No dyadic exceptional set has been
multiplied by a short-interval length ratio.

### 3.2 Differencing, with a bounded number of carry cells

Suppose j!=0. Conjugating if necessary, take u=j/2>0; then 1/2<=u<=K/2.
Use odd-lattice shifts 2h with 1<=h<=D=floor(P^(1/16)). The overlap
interval still has length O_{L_0}(P^(7/16)). Write

\[
 \theta=\{X(n)\},\quad \delta(x)=X(x+2h)-X(x),\quad
 g(n)=M(n+2h)-M(n).
\]

The one-signed linearization, proved by factorization in Paper B Lemma 7.1,
is

\[
 Y(n)=\tfrac32 M(n)n^{3/4}-\tfrac12n^{9/4}+E(n),\qquad
 0\le E(n)\ll n^{-3/4}.
\]

It gives the exact identity

\[
 \Delta_hY(n)=A_h(n)+\tfrac32g(n)(n+2h)^{3/4}
       -\tfrac32\theta\Delta_h(n^{3/4})+\Delta_hE(n),
 \tag{8}
\]

where Delta_h f(x)=f(x+2h)-f(x) and

\[
 A_h(x)=\tfrac32x^{3/2}\Delta_h(x^{3/4})
                         -\tfrac12\Delta_h(x^{9/4}).
\]

Removing the last two terms of (8) from the exponential costs at most

\[
 O_K\left(hP^{7/16-1/4}+P^{7/16-3/4}\right)=O_K(P^{1/4}).
 \tag{9}
\]

The function delta is increasing and delta'=O(hP^(-1/2)). Its floor
therefore cuts the overlap interval into

\[
 O_{L_0}(1+hP^{7/16-1/2})=O_{L_0}(1)
 \tag{10}
\]

cells, including the partial endpoint cells. On each cell freeze G=floor(delta)
and let z=delta-G. Then 0<=z<1 is monotone, G is of order h sqrt(P), and

\[
 g=G+\kappa,\qquad
 \kappa=z+b(X(n))-b(X(n+2h))\in\{0,1\}.
 \tag{11}
\]

Define the smooth cell phases

\[
 F_{G,\epsilon}(x)=u A_h(x)+\tfrac{3u}{2}(G+\epsilon)(x+2h)^{3/4}
        +\tfrac i2\delta(x)+\tfrac k2\Delta_hZ(x),\quad \epsilon=0,1.
\]

The exponential remaining after (9) equals, exactly,

\[
 (1-z)e(F_{G,0})+z e(F_{G,1})+
 (b(X(n))-b(X(n+2h)))(e(F_{G,1})-e(F_{G,0})).
 \tag{12}
\]

This follows by substituting (11) into
(1-kappa)e(F_{G,0})+kappa e(F_{G,1}). There is no independence assumption.

### 3.3 Every local error term

The identity A_h(x)=x^(9/4) a(2h/x), with
a(t)=(3/2)((1+t)^(3/4)-1)-(1/2)((1+t)^(9/4)-1), has a(0)=a'(0)=0.
Writing a(t)=t^2 a_2(t), whose first two derivatives are bounded near zero,
shows A_h''=O(h^2 P^(-7/4)). Thus on each fixed cell

\[
 F_{G,\epsilon}''(x)=-\frac9{32}u(G+\epsilon)(x+2h)^{-5/4}
     +O_K(h^2P^{-7/4}+hP^{-3/2}+hP^{-15/8}).
 \tag{13}
\]

Its curvature is comparable to u h P^(-3/4), with a fixed sign and
bounded ratio, uniformly in h<=P^(1/16). The second-derivative estimate
and partial summation for z and 1-z bound the first two terms of (12) by

\[
 O_{K,L_0}\left(P^{7/16}(uh)^{1/2}P^{-3/8}
                         +(uh)^{-1/2}P^{3/8}+1\right)
       =O_{K,L_0}(P^{3/8}).
 \tag{14}
\]

The endpoint term P^(3/8) is retained. There are only O_{L_0}(1) cells.

Replace the two b functions in (12) by b_R. By (7) and
|e(F_1)-e(F_0)|<=2, their total remainder is O(P^(5/16) log P),
even after the partition. Each nonzero Fourier mode now has phase
F_{G,epsilon}+rX(x) or F_{G,epsilon}+rX(x+2h). Its curvature is comparable
to |r|P^(-1/2): the competing curvature divided by that quantity is
O_K(h P^(-1/4)/|r|)=O_K(P^(-3/16)). Hence the modes, summed with their
O(1/|r|) coefficients over 1<=|r|<=R=P^(1/8), cost

\[
 O_{K,L_0}\left(P^{3/16}R^{1/2}+P^{1/4}+\log(2R)\right)
                 =O_{K,L_0}(P^{1/4}).
 \tag{15}
\]

Combining (9), (14), (7), and (15), every overlap correlation obeys
|T_h|=O_{K,L_0}(P^(3/8)). In particular, the carry error is smaller than
this bound; log P is absorbed by the gap 3/8-5/16=1/16.

If the odd count N in I is at least D, differencing gives

\[
 |S|^2\ll_{K,L_0} P^{7/8-1/16}+P^{7/16+3/8}
                     =O_{K,L_0}(P^{13/16}).
 \tag{16}
\]

If N<D the trivial estimate is already stronger. This proves (5) for j!=0.
If j=0 and i!=0, the undifferenced smooth phase has curvature comparable
to |i|P^(-1/2), since the k term has curvature O_K(P^(-7/8)). Its sum
is O_{K,L_0}(P^(1/4)), which also proves (5). This completes Lemma 2.

## 4. The pure slow modes and the actual last guard

Let V(n)=floor(Y(n)). Uniformly for n in [P,2P],

\[
 |\sqrt{V(n)}-n^{9/8}|\ll P^{-3/8}.
 \tag{17}
\]

Indeed replacing sqrt(floor(Y)) by sqrt(Y)=M^(3/4) costs O(P^(-9/8));
replacing M=X-theta by X in the 3/4 power costs O(P^(-3/8)). The mean
value theorem applies on positive intervals bounded below by constant
multiples of the relevant powers. Thus replacing Z by sqrt(V) in a
fixed-frequency exponential sum costs O_K(P^(1/16)), negligible in (5).
We use (17) for exponential sums, not to assert equality of floor parities.

Put alpha_m=(9/8)m^(2/9). In the odd coordinate n=2t+1,
the derivative of (k/2)n^(9/8) is (9k/8)n^(1/8). On I_m it differs
from k alpha_m by at most

\[
 C_0 |k|m^{-7/9}
 \tag{18}
\]

for an absolute C_0. This follows from (3) and the derivative bound
for x^(1/8), since P^(-7/8) P^(7/16)=m^(-7/9). The derivative is monotone.

For fixed integers K>=1 and real C>2 C_0 K, suppose

\[
 \|k\alpha_m\|>C m^{-7/9}\quad(1\le k\le K).
 \tag{19}
\]

For sufficiently large m the derivative of each pure slow phase stays
in one interval between consecutive integers and at distance at least
(C/2)m^(-7/9) from them. Kusmin--Landau gives

\[
 \left|\sum_{n\in I_m,\ n\text{ odd}}e\left(\tfrac k2 Z(n)\right)\right|
       \ll m^{7/9}/C+1\ll H_m/C+1.
 \tag{20}
\]

Negative k follow by conjugation. Equation (17) gives the same bound
with an additional O_K(P^(1/16)) for the actual sqrt(V) phase.

## 5. Joint parity, resonance inclusion, and the tail

Apply three-dimensional box discrepancy to the actual points

\[
 \left(\{X(n)/2\},\{Y(n)/2\},\{\sqrt{V(n)}/2\}\right),
                  \qquad n\in I_m,\ n\text{ odd}.
\]

The box [1/2,1) times [0,1/2) times [0,1/2) specifies exactly the three
remaining OOEE guards. Its volume is 1/8. Half-open boundaries encode
integer-floor parity exactly, including square and cube coincidences.

For fixed K and C as above and m satisfying (19), Lemma 2 controls every
mode with (i,j)!=(0,0), and (20) controls the pure slow modes. Therefore

\[
 \left|C_m/H_m-1/8\right|
   \le A/K+A\log(2K)/C+O_{K,L_0}(P^{-1/32})
                         +O_K(P^{-3/8})+O_K(H_m^{-1}),
 \tag{21}
\]

where A is absolute; fixed logarithmic frequency weights are absorbed in
the indicated constants. For any epsilon>0, first choose K so the first
term is less than epsilon/3; then choose C>2 C_0 K so the second is less
than epsilon/3; finally choose m large so the remaining terms total less
than epsilon/3. This order keeps K and C independent of m.

Together with (4), this proves: for every eta>0 there are fixed
K_eta,C_eta and m_eta such that

\[
 m\ge m_\eta,\ |R_m-1/9|>\eta
 \quad\Longrightarrow\quad
 \exists\,1\le q\le K_\eta:\quad
       \|q\alpha_m\|\le C_\eta m^{-7/9}.
 \tag{22}
\]

For example, take epsilon=eta/4 and enlarge m_eta until the error in (4)
is at most eta/4. Strict poor inequalities R_m<1/9-eta are contained
in this absolute-deviation set.

For fixed q, the derivative of q alpha_m is (q/4)m^(-7/9).
On [M,2M), each window within C_eta M^(-7/9) of an integer has
preimage length at most 8 C_eta 2^(7/9)/q. There are
O(q M^(2/9)+C_eta+1) possible integer levels. Counting integers in
these bounded intervals, then summing over q<=K_eta, gives

\[
 \#\{M\le m<2M:\ m\text{ satisfies the right side of (22)}\}
                \ll_\eta M^{2/9}.
 \tag{23}
\]

The same bound for deficient targets follows beyond m_eta; increasing
its constant absorbs the finite initial set. Division by M and summation
over dyadic blocks starting at U yields (1). This proves Theorem 1.

## 6. What the coefficient now supplies

For any subset A of the positive integers, any finite target cutoff X,
and fixed 0<eta<1/9, Theorem 1 and w(m)<=4/m give

\[
 \sum_{m\in A,\ m\le X} W_m
    \ge (1/9-\eta)\sum_{m\in A,\ m\le X}w(m)-C_\eta.
 \tag{24}
\]

The constant is independent of A and X. Separate the poor targets and
use their bounded total w-mass; all W_m are nonnegative. Fibres for
different targets are disjoint. If A is backward closed under the actual
Juggler map, every source in these fibres also belongs to A.

This is an actual two-consecutive-odd production at any coefficient below
1/9, with a bounded additive loss. A source cutoff still requires the
exact endpoint restriction A_(m+1)<=source_cutoff+1. Combining (24) with
the existing E/OE shell recursion, checking its boundary losses, and
formalizing that assembly were subsequent work for this analytic phase.
The [follow-up assembly](juggler_ooee_contagion_note.md) now gives written
contagion at 5/8 and a sufficient Tao-rate threshold e>3/8. Its Lean
implication retains both actual odd-production inequalities explicitly;
the analytic input of the present note remains a written proof.

## 7. Audit and formalization boundary

The proof does not invoke Paper B's global mixed-sum theorem as a
short-interval estimate. Its new estimate (5) is rederived above. The
earlier unsuccessful localization of longer OOOEE/OOEOE fibres remains
closed: those source lengths are P^(5/32), below the retained P^(3/8)
correlation endpoint cost. Pure slow modes remain excluded from (5).

Existing kernel-checked components are
[PaperBAssembly.lean](../../formal/Problems/Juggler/PaperBAssembly.lean)
(`lemma43_closed_form`, `lemma43_nonneg`, `lemma43_upper`,
`carry_identity`, `carry_mem_zero_one`) and
[GapCells.lean](../../formal/Problems/Juggler/GapCells.lean)
(`carry_eq_fract_add_sub_fract`, `floor_odd_iff_half_le_fract_half`).
They support the exact algebra and parity interpretation. Neither file
contains the analytic short-interval estimate or Theorem 1.

The census is a regression control, not a proof of (1). Independent
review should particularly check (7), the bounded cell count (10), all
endpoint terms in (14)--(16), and the fixed-parameter order in (21)--(22).
Full analytic Lean formalization is deferred; no new assumptions are
introduced into the existing Lean development.
