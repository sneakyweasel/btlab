# Paper B: the OOOEE mixed-mode transfer

9 September 2026. Research supplement to the 27/32 manuscript.

## Outcome and scope

The precise four-coordinate family needed for OOOEE has the following
AI-assisted written bound. Put
\[
X(n)=n^{3/2},\quad m(n)=\lfloor X(n)\rfloor,\quad
Y(n)=m(n)^{3/2},\quad v(n)=\lfloor Y(n)\rfloor,\quad
Z(n)=v(n)^{3/2},\quad w(n)=\lfloor Z(n)\rfloor,\quad U(n)=\sqrt{w(n)}.
\]
For every fixed \(C\ge1\) and every \(\varepsilon>0\), uniformly over
nonzero integer quadruples with
\(\max(|i|,|j|,|k|,|l|)\le CP^{1/24}\),
\[
\left|\sum_{\substack{P<n\le2P\\n\ {\rm odd}}}
 e\left(\frac{iX(n)+jY(n)+kZ(n)+lU(n)}2\right)\right|
 \ll_{C,\varepsilon}P^{127/128+\varepsilon}. \tag{T1}
\]
Here e(x)=exp(2 pi i x). These coordinates form a formal chain for
every odd n; they coincide with the Juggler trajectory on the
specified OOOEE sign class.

As consequences,
\[
\#\{n\le N:\operatorname{word}_5(n)=OOOEE\}
 =\frac N{32}+O_\varepsilon(N^{127/128+\varepsilon}), \tag{T2}
\]
and the class \(\mathcal C_5\) of starts with a power-envelope
contraction certificate of length at most five satisfies
\[
\#(\mathcal C_5\cap[1,N])
 =\frac{7N}{8}+O_\varepsilon(N^{127/128+\varepsilon}). \tag{T3}
\]
This is a certificate-class density, not the exact density of all
starts that happen to descend within five steps.

Decision: **PROMOTE** the stated mixed-mode estimate and its counting
consequences as written research results. Exact algebra and exponent
controls accompany this proof; they do not prove cancellation by
finite computation. Independent mathematical review and Lean
verification remain outstanding. The historical 95/96 kernel target,
arbitrary decorations, short-interval localization, and termination
are not established. The existing 27/32 manuscript and deposit files
are unchanged; consolidation and publication review are a separate step.

## 1. Dependencies and the full phase

We use the [kernel assembly](paper_b_kernel_assembly_report.md),
especially its exact master identity (K7), positive errors (K5),
centered inventory (K8)--(K12), and first-floor carry expansion.
Its nonzero-frequency input is the theorem (W3) in the
[wave-bearing supplement](paper_b_wave_bearing_report.md).
Floor replacements and frozen integral estimates are those in the
[D2](paper_b_d2_report.md),
[signed-wave](paper_b_signed_waves_report.md), and
[offset-anchor](paper_b_offset_anchor_report.md) supplements.
The elementary small-shift proof used below is Lemma 4.4 of the
[current manuscript](juggler_parity_discrepancy_note.md).

The bare kernel bound alone is insufficient. Writing
\(\theta=\{X\}\) and \(\vartheta=\{Y\}\), Taylor's theorem gives
\[
\begin{split}
Z&=m^{9/4}-\tfrac32m^{3/4}\vartheta+O(P^{-9/8}),\\
m^{3/4}&=n^{9/8}+O(P^{-3/8}),\\
U&=m^{9/8}+O(P^{-9/16}). \tag{T4}
\end{split}
\]
For the last assertion,
\(\sqrt{\lfloor Z\rfloor}=v^{3/4}+O(P^{-27/16})\) and
\(v^{3/4}=Y^{3/4}+O(P^{-9/16})\).
All comparisons are uniform for n in [P,3P].

Let \(c(x)=3kx^{9/8}/4\). Replacing the original phase by
\[
F(n)=\tfrac i2X(n)+\tfrac j2Y(n)+\tfrac k2m(n)^{9/4}
       +\tfrac l2m(n)^{9/8}-c(n)\vartheta(n) \tag{T5}
\]
costs in the whole exponential sum at most
\[
O_C\bigl(|k|P^{5/8}+|k|P^{-1/8}+|l|P^{7/16}\bigr)
 =O_C(P^{2/3}). \tag{T6}
\]
We keep both powers of m in (T5) until after differencing. In
particular, the fifth-coordinate term is not expanded initially
into a Fourier series with a growing coefficient.

## 2. The cases k=0, including every zero coordinate

In these cases (T4) leaves the phase
\(iX/2+jY/2+l m^{9/8}/2\), with error already covered by (T6).

If j is nonzero, apply one A-process with
\(H=\lfloor P^{1/12}\rfloor\). On a first-floor gap cell and
carry branch let \(g=m(n+2h)-m(n)\), with g fixed and comparable
to \(h\sqrt P\). For
\[
V_g(z)=(z+g)^{9/8}-z^{9/8}
\]
the exact integral formula gives
\[
|V_g'(X)|\ll hP^{-13/16},\qquad
|(V_g\circ X)''|\ll hP^{-21/16}. \tag{T7}
\]
Replace \(lV_g(m)/2\) by \(lV_g(X)/2\) at the global cost
\(O(|l|hP^{3/16})\le O_C(P^{5/16})\).
In the proof of Lemma 4.4, add this last smooth term separately
to each of the two g branches. No new gap cell or carry is needed.
Its curvature relative to the main one
\(|j|hP^{-3/4}\) is
\[
O(|l/j|P^{-9/16})=O_C(P^{-25/48}).
\]
The exact carry interpolation (4.8), global positive Fourier errors,
and domination of the nonzero first-floor Fourier modes therefore
remain valid. Both signs of j are handled by conjugating the whole
phase. The correlation is
\(O_C(P^{7/8}(1+\sqrt h))\); the A-process gives
\(O_C(P^{23/24})\).

If j=0 and l is nonzero, expand once:
\[
\tfrac l2m^{9/8}
 =\tfrac l2n^{27/16}-B(n)\theta+O(|l|P^{-21/16}),
\quad B(x)=\tfrac{9l}{16}x^{3/16}. \tag{T8}
\]
Set \(N_B=\lfloor B\rfloor\) and expand the bounded residual
\(B-N_B\) at cutoff \(T=\lfloor P^{1/8}\rfloor\).
The retained phases are
\[
f_r(x)=\tfrac l2x^{27/16}+(i/2+r-N_B)x^{3/2},\qquad |r|\le T.
\]
Freeze \(N_B\) when differentiating. Substituting its value only
after differentiation gives
\[
f_r''=\tfrac{81l}{512}x^{-5/16}
       +O((|i|+T+1)P^{-1/2}). \tag{T9}
\]
The coefficient is
\((1/2)(27/16)(11/16)-(9/16)(3/4)=81/512\).
The error relative to the leading term is
\(O_C(P^{-7/48}+P^{-1/16})\).
There are \(O(1+|l|P^{3/16})\) center windows; the Fourier
coefficient mass and variation on each are \(O(\log P)\).
The summed second-derivative bound is
\[
O\left(|l|^{1/2}P^{27/32}
 +(1+|l|P^{3/16})|l|^{-1/2}P^{5/32}\right)\log^C(2P)
 \ll_C P^{83/96}\log^C(2P).
\]
The positive Fourier error totals \(O(P^{7/8}\log P)\).
For example (W15)'s distance-band proof gives
\(O(P\log(2T)/T+P^{5/6}\log(2P))\) at this cutoff.
Thus this case is \(O_C(P^{7/8}\log^C P)\).

Finally j=l=0 forces i nonzero. The smooth phase \(iX/2\)
has curvature comparable to \(|i|P^{-1/2}\) and sum
\(O_C(P^{37/48}+P^{1/4})\). This covers every k=0 mode
without using (T1).

## 3. The twice-differenced inventory when k is nonzero

Conjugate all four frequencies if necessary to assume k>=1.
Use the kernel ranges
\[
H_1=\lfloor P^{1/48}\rfloor,\quad H_2=\lfloor P^{1/24}\rfloor,
\quad 1\le h_a<H_a,\quad d_a=2h_a,\quad
p=h_1h_2,\quad \Pi=kp\ll_C P^{5/48}. \tag{T10}
\]
Write \(\Delta_a f(x)=f(x+d_a)-f(x)\),
\(W_a=\Delta_aY\), \(D=\Delta_1\Delta_2Y\), and
\(c_{11}(x)=c(x+d_1+d_2)\).
The double difference of (T5) is exactly
\[
\tfrac k2\Delta_1\Delta_2(m^{9/4})
+\tfrac l2\Delta_1\Delta_2(m^{9/8})
+\tfrac i2\Delta_1\Delta_2X+\tfrac j2D
-\Delta_1\Delta_2(c\vartheta). \tag{T11}
\]

Apply the conjugate of the master expansion (K7)--(K10) to the
last term, with \(J=\lfloor P^{1/24}\rfloor\). Set
\[
B_2=\Delta_2c(x+d_1),\quad B_1=\Delta_1c(x+d_2),
\quad N_a=\lfloor B_a\rfloor .
\]
The retained modes have phase
\[
\begin{split}
&\tfrac k2\Delta_1\Delta_2(m^{9/4})
 +\tfrac l2\Delta_1\Delta_2(m^{9/8})-c_{11}\{D\}\\
&\hspace{8mm}+tY+a_1W_1+a_2W_2+qD+\psi,\qquad
a_1=-N_2+u,\quad a_2=-N_1+v. \tag{T12}
\end{split}
\]
Here t,u,v are integers of absolute value \(O_C(J)\);
q is a half-integer of absolute value \(O_C(J)\), including
the original j/2. The function \(\psi\) is \(i\Delta_1\Delta_2X/2\)
plus a bounded integer combination of \(B_1,B_2,c_{11}\).
In particular
\[
\begin{split}
|a_1|h_1+|a_2|h_2
 &\ll_C \Pi P^{1/8}+J(h_1+h_2)\ll_C P^{11/48},\\
|\psi''|&\ll_C kP^{-7/8}+|i|pP^{-5/2}. \tag{T13}
\end{split}
\]
All signs of i,j,l,u,v,q are permitted.
The original jY/2 contributes only jD/2 after two differences,
so t remains an integer.

The full coefficient mass is \(O(\log^7(2P))\). Each multi-index
has a fixed harmonic envelope under which its normalized
coefficient has bounded sup norm plus variation on the N_1,N_2
cells. The centers have local density \(O_C(P^{-19/24})\).
These are exactly the centering and five binary-carry operations
in the kernel proof, with signs reversed. The deleted first
master term costs \(O_C(P^{11/48})\), and all positive errors cost
\(O_C(P^{23/24}\log^C P)\). Their arguments are the same Y corners,
W_1,W_2,the shifted W_1, and D. The new factors in (T11) have
modulus one, so the positive bounds (K5) are unchanged. In
particular no OOOEE discrepancy has been assumed to control them.

## 4. Frozen branches and the extra powers

Partition first into the original gap runs determined by the floors
of \(\Delta_1X,\Delta_2X,\Delta_{d_1+d_2}X\).
Their total count is \(O_C(P^{13/24})\), their local count in
length L is \(O_C(1+LP^{-11/24})\), and their lengths are
\(O_C(\sqrt P)\). On a carry pattern let
\[
m(n+d_a)=m(n)+\beta_a,\quad
m(n+d_1+d_2)=m(n)+\beta_1+\beta_2+b .
\]
Then \(-1\le b\le2\), since the real mixed difference of X is
positive and o(1). The beta values and b are fixed on the branch;
\(\beta_a=3h_a\sqrt x+O(1+h_a^2P^{-1/2})\) only as values.

For any exponent a define
\[
F_a(z)=(z+\beta_1+\beta_2+b)^a
 -(z+\beta_1)^a-(z+\beta_2)^a+z^a .
\]
The formulas used for every derivative are
\[
\begin{split}
F_{a,0}(z)&=a(a-1)\int_0^{\beta_1}\int_0^{\beta_2}
                   (z+s+t)^{a-2}\,dt\,ds,\\
F_a(z)-F_{a,0}(z)&=ab\int_0^1
                 (z+\beta_1+\beta_2+\tau b)^{a-1}\,d\tau .
                                                        \tag{T14}
\end{split}
\]
They apply also when b<0. The notation \(F_{a,0}\) means b=0.
Put \(G=F_{3/2}(X)\) and \(A=\lfloor F_{3/2}(m)\rfloor\).
The exact identity \(\Delta_1\Delta_2(m^a)=F_a(m)\)
holds on its actual carry pattern.

The fifth-coordinate term can now be replaced directly by
\(lF_{9/8}(X)/2\). The relevant bounds are
\[
\begin{split}
|F_{9/8}'(X)|&\ll |b|P^{-21/16}+pP^{-29/16},\\
|(F_{9/8}\circ X)''|&\ll |b|P^{-29/16}+pP^{-37/16},\\
|(F_{9/8}\circ X)'''|&\ll |b|P^{-45/16}+pP^{-53/16}.
                                                        \tag{T15}
\end{split}
\]
The total replacement error is
\(O(|l|P^{-5/16}+|l|pP^{-13/16})=O_C(1)\).
Replacing qD by qG costs \(O_C(P^{7/24})\), as in (O5)--(O7);
integrality of q is irrelevant for that comparison.

Combine the two large terms before expanding in theta:
\[
H(z,x)=\tfrac k2F_{9/4}(z)-c_{11}(x)F_{3/2}(z),\qquad
B_{\rm core}(x)=\partial_zH(X(x),x).
\]
Since \(-c_{11}\{D\}=-c_{11}F_{3/2}(m)+c_{11}A\), the
core of (T12) is H(m,x)+c_11 A. Taylor expansion gives
\[
H(m,x)=H(X,x)-B_{\rm core}\theta
 +O_C(k|b|P^{-9/8}+\Pi P^{-13/8}), \tag{T16}
\]
so its total error is bounded. The growing coefficient is
\[
B_{\rm core}
 =\tfrac{27}{32}kb x^{3/8}
 +O_C\bigl(\Pi P^{-1/8}+k(h_1+h_2)P^{-5/8}\bigr). \tag{T17}
\]
The leading coefficient is \(45/32-9/16=27/32\).
The error is bounded in (T10). On each original run its derivative
is bounded by \(O_C(P^{-3/4})\); this follows directly by
differentiating (T14), with the beta values fixed.

All carry patterns are retained. As in (W15), their indicators are
finite unions of arcs in theta. Endpoint-order cuts add only a
fixed multiple of the run count. At cutoff \(R_c=P^{1/4}\),
each nonzero endpoint mode has weight \(O(1/|s|)\) and phase
sX(x+d), for an allowed shift d; the zero coefficient has bounded
variation. Their global positive errors are \(O(P^{5/6}\log P)\).
We use \(R=P^{5/16}\) for the bounded theta coefficients below;
their global errors have the same bound. No error is charged
again on each gap run or frequency window.

## 5. Nonzero total Y frequency

Suppose t is nonzero in (T12). Keep the first differences
\(a_1W_1+a_2W_2\) unexpanded and keep the floor A on its original
fixed-label runs. In particular do not cut into A's integer levels.

Center the growing term (T17) at
\[
N_*=\left\lfloor\tfrac{27}{32}kb x^{3/8}\right\rfloor .
\]
On the intersections of original runs and N_* windows,
\(B_{\rm core}-N_*\) has bounded size and variation.
For b=0 use N_*=0. Expand this bounded residual at R.
After the first-floor carry expansion the smooth part is
\[
\Phi=H(X,x)+\tfrac l2F_{9/8}(X)+qG+\psi
                  +(r-N_*)X+sX(x+d).
\]
Its third derivative satisfies
\[
|\Phi'''|\ll_C
 kP^{-9/8}+\Pi P^{-13/8}
 +(R+|N_*|+R_c)P^{-3/2}
 +|l|(P^{-45/16}+pP^{-53/16})
 \ll_C P^{-13/12}. \tag{T18}
\]
The q and psi terms are smaller; \(|N_*|\ll_C P^{5/12}\).

The common coarse partition consists of original runs, N_1,N_2
windows, N_* windows, and endpoint-order cuts. Its local count
remains \(O_C(1+LP^{-11/24})\), since N_* has local density
\(O_C(kP^{-5/8})=O_C(P^{-7/12})\). Fixed b on each original
run permits this assertion even though b changes between runs.
The assigned D2 labels do not change at extra refinements.
An empty carry pattern is extended using an admissible fixed
label on that original run and zero amplitude there.

Every normalized retained term now satisfies (W3): the nonzero
integer t is in its allowed range; (T13) fits its widened
first-difference budget; (T18) fits its twist budget; and the
single floor term is +c_11 A, namely sigma=-1 in (W3).
The sum of all these weighted terms is
\[
O_{C,\varepsilon}(P^{31/32+\varepsilon}). \tag{T19}
\]
The D2 reduction is invoked inside (W3), after that theorem's
additional A-process, rather than on an arbitrary undifferenced
floor.

## 6. Zero total Y frequency: shared reductions

Now t=0. Replace A by \(J_F=\lfloor G\rfloor\).
The exception count on the original runs is \(O_C(P^{3/4})\)
when b is nonzero, by (O6); it is \(O_C(P^{13/24})\) when b=0,
by (S6). Each changed exponential costs at most two. The
coefficient c_11 is not multiplied by the size of a floor error.

For \(V_a(z)=(z+\beta_a)^{3/2}-z^{3/2}\), expand
\[
a_aV_a(m)=a_aV_a(X)-a_aV_a'(X)\theta
                    +O(|a_a|h_aP^{-7/4}).
\]
By (T13) the global error is \(O_C(P^{-25/48})\).
The smooth part and theta coefficient are consequently
\[
\begin{split}
F_{\rm sm}&=\tfrac k2F_{9/4}(X)-c_{11}(G-J_F)
            +a_1V_1(X)+a_2V_2(X)+\tfrac l2F_{9/8}(X)+qG+\psi,\\
B&=B_{\rm core}+a_1V_1'(X)+a_2V_2'(X). \tag{T20}
\end{split}
\]
The wave contribution to B is bounded:
\[
\left|\sum a_aV_a'(X)\right|
 \ll_C \Pi P^{-1/8}+J(h_1+h_2)P^{-1/4}\ll_C1.
\]
Its derivative on a frozen cell is bounded by
\(O_C(\Pi P^{-9/8}+J(h_1+h_2)P^{-5/4})\).
These facts give the bounded coefficient variation required
below. All integer levels of J_F are now included in the
derivative-test partition.

## 7. Nonzero b: recompute the mixed curvature

For b nonzero, center B at the same N_* as in Section 5;
its bounded residual has bounded variation. Retained phases are
\(f=F_{\rm sm}+(r-N_*)X+sX(x+d)\).

The bare offset-anchor coefficient 81/64 cannot be imported:
the sign of that anchor is reversed and \(kF_{9/4}(X)/2\)
is present. Freeze \(\beta_a,b,J_F,N_*,N_a\) before differentiation.
The three leading contributions, in units of \(kb x^{-1/8}\),
are
\[
\begin{array}{c|c}
\text{term} & \text{coefficient}\\ \hline
(kF_{9/4}(X)/2)'' & 945/512\\
(-c_{11}(G-J_F))'' & -864/512\\
-N_*X'' & -324/512
\end{array}
\]
Their sum is
\[
-\tfrac{243}{512}. \tag{T21}
\]
For the middle row use
\(-2c_{11}'G'-c_{11}G''-c_{11}''(G-J_F)\).
The last factor \(G-J_F\) is bounded, so its curvature term is
only \(O(kP^{-7/8})\). Dropping the integer-floor contribution
would give the wrong leading coefficient.

Uniformly for every retained index,
\[
f''=-\tfrac{243}{512}kb x^{-1/8}+O_C(P^{-3/16}). \tag{T22}
\]
For clarity, the error terms include
\[
\begin{split}
&\Pi P^{-5/8}+k(h_1+h_2)P^{-9/8}+kP^{-7/8}\\
&+(|a_1|h_1+|a_2|h_2)P^{-3/4}
 +(R+R_c+1)P^{-1/2}+R_c(h_1+h_2)P^{-3/2}\\
&+|q|(P^{-5/4}+pP^{-7/4})
 +|l|(P^{-29/16}+pP^{-37/16})+|\psi''|.
\end{split}
\]
Every term fits (T22) under (T10),(T13). Both signs of b are
allowed. The error is smaller than the leading curvature by
\(O_C(P^{-1/16}/k)\).

The full number of intervals is \(O_C(P^{3/4})\).
The G-levels add at most \(O_C(P^{3/4}+P^{13/24})\);
the original gaps, moving centers, and arc-order cuts are smaller.
Summing lengths and every endpoint in the second-derivative
estimate, with coefficient masses and variation, gives
\[
O_C\left(\sqrt{k}P^{15/16}
       +k^{-1/2}P^{13/16}\right)\log^C(2P)
 \ll_C P^{23/24}\log^C(2P). \tag{T23}
\]
The positive errors and floor exceptions are smaller. This
proves the nonzero-offset part for the actual mixed family.

## 8. Zero b: the actual negative moving centers

When b=0, (T20) has \(|B|\ll_C1\) and bounded variation on every
original run intersected with the N_a windows. Expand it directly
at R, without a new theta center. After the carry expansion put
\(\ell_F=r+s\), an integer, and
\(\alpha_0=uh_1+vh_2\).
For fixed \(\ell_F\), the coefficient sup norms plus variations
sum to \(O(\log(2P)/(1+|\ell_F|))\). This is the harmonic
convolution estimate (S9); the phases for different r,s need not
be identical.

The pure \(kF_{9/4}(X)/2\) curvature has leading coefficient
\(-6075/2048\) in units of \(\Pi x^{-5/8}\).
The negative fractional anchor contributes
\(243/128=3888/2048\), so their subtotal is \(-2187/2048\).
The centers in this problem have negative signs:
\[
h_1a_1+h_2a_2
 =-\tfrac{27}{8}\Pi x^{1/8}+\alpha_0
  +O_C(h_1+h_2+\Pi(h_1+h_2)P^{-7/8}). \tag{T24}
\]
The frozen wave curvature is
\(-27(h_1a_1+h_2a_2)x^{-3/4}/32\), up to smaller terms.
It adds \(729/256=5832/2048\) to the subtotal. Thus
\[
f''=-\tfrac{27}{32}\alpha_0x^{-3/4}
    +\tfrac{3645}{2048}\Pi x^{-5/8}
    +\tfrac34\ell_Fx^{-1/2}
    +O_C(\Pi P^{-3/4}). \tag{T25}
\]
This coefficient differs from the undecorated kernel's
\(-1215/256\). It has been recomputed for (T12).

The errors in (T25) include
\[
\begin{split}
&(h_1+h_2)P^{-3/4}
 +( |a_1|+|a_2| )P^{-5/4}
 +( |a_1|h_1^2+|a_2|h_2^2 )P^{-7/4}\\
&+k(h_1+h_2)P^{-9/8}
 +\Pi(h_1+h_2)P^{-13/8}
 +kP^{-7/8}+|q|pP^{-7/4}\\
&+P^{-29/24}+|l|pP^{-37/16}+|\psi''|.
\end{split}
\]
Use \(h_1+h_2\le2p\le2\Pi\), before inserting independent shift
caps, for the leading rounding error. All terms have the claimed
bound. The fifth-coordinate term is particularly small here.

There is a strict frequency gap:
\[
\frac{|\alpha_0|P^{-3/4}}{\Pi P^{-5/8}}
 \ll_C JP^{-1/8}=O_C(P^{-1/12}),\qquad
\frac{\Pi P^{-5/8}}{P^{-1/2}}\ll_C P^{-1/48}. \tag{T26}
\]
Consequently \(\ell_F=0\) has one-signed curvature comparable
to \(\Pi P^{-5/8}\); every nonzero integer \(\ell_F\) has
one-signed curvature comparable to \(|\ell_F|P^{-1/2}\).
No hypothesis on the largest individual signed wave is used.

The common partition has \(O_C(P^{13/24})\) cells, including
\(O_C(pP^{1/4}+P^{13/24})\) zero-offset G-level cuts.
For \(\ell_F=0\), summing all lengths and endpoints costs
\[
O_C\left(\Pi^{1/2}P^{11/16}
        +\Pi^{-1/2}P^{41/48}\right)\log^C(2P).
\]
For nonzero \(\ell_F\), sum the harmonic weights as well:
\[
O_C\left(R^{1/2}P^{3/4}+P^{13/24+1/4}\right)\log^C(2P)
 =O_C(P^{29/32}\log^C(2P)). \tag{T27}
\]
The zero mode and positive errors are smaller. This is a direct
estimate for the moving coefficients in (T12), not an application
of an ambient fixed-coefficient bound separately on every window.

## 9. Assembly and the dyadic count

For the double correlation of (T5), the accounting is:

| Contribution | Exponent, apart from fixed logarithmic powers |
|---|---|
| Deleted master term | 11/48 |
| Positive short-Fourier errors | 23/24 |
| Extra-power Taylor errors and slow D replacement | at most 7/24 |
| Nonzero t, via (W3) | 31/32 |
| t=0, nonzero b | 23/24 |
| t=0, b=0 | 29/32 |

The first-floor Fourier errors and floor mismatches are included
in the last three estimates. Thus the double correlation is
\(O_{C,\varepsilon}(P^{31/32+\varepsilon})\).
Both outer A-processes are precisely (K3), giving
\[
|T_1|^2\ll_C P^{47/24}+P^{63/32+\varepsilon},
\qquad |T_1|\ll_{C,\varepsilon}P^{63/64+\varepsilon},
\]
and
\[
|S_F|^2\ll_C P^{95/48}+P^{127/64+\varepsilon},
\qquad |S_F|\ll_{C,\varepsilon}P^{127/128+\varepsilon}.
\]
Overlap endpoints cost \(O(h_1+h_2)\) and fit these estimates.
Arbitrarily small epsilon losses may be relabeled after each step.
Together with Sections 1--2 this proves (T1).

Apply the four-dimensional Erdős--Turán--Koksma inequality to
\[
(\{X/2\},\{Y/2\},\{Z/2\},\{U/2\})
\]
on the odd integers in a single dyadic block. Use cutoff
\(\lfloor P^{1/24}\rfloor\). Its diagonal error is \(O(P^{23/24})\);
the weighted nonzero modes in (T1) cost
\(O_\varepsilon(P^{127/128+\varepsilon})\), absorbing the
four harmonic sums. All sixteen half-boxes have volume 1/16.
Since there are P/2+O(1) odd inputs, each formal sign class has
count
\[
P/32+O_\varepsilon(P^{127/128+\varepsilon})
\]
on this block. A half-box records exactly the parity of the floor:
even for a coordinate in [0,1/2), odd for one in [1/2,1).

Use this discrepancy argument separately on each dyadic block
in a decomposition of [1,N], with that block's own frequency
cutoff. Then sum the counts and errors. One must not impose
the largest block's cutoff on all smaller blocks. Taking a small
epsilon first, the error series is geometric; the remaining
bounded initial interval contributes O(1). The class with
m,v odd and w,floor(U) even is exactly OOOEE for odd n.
This proves (T2), including endpoint conventions. All fifteen
nonempty products of its four parity signs also have this
error bound, by summing the sixteen sign classes. In the
manuscript's notation, H(OOOEE;delta) follows for every
\(0<\delta<1/128\).

Finally Lemma 5.1 and Theorem 5.3 of the manuscript give the
disjoint union of its 27/32 class and OOOEE. The former error
\(O(N^{47/48})\) is smaller. Their densities add to
\(27/32+1/32=7/8\), proving (T3).
This discharges the specific hypothesis of the existing
Theorem 5.4 at the level of the present written supplements.

## 10. Validation, limits, and next step

The companion validate_paper_b_oooee_transfer.py checks the
negative master identity, signed half-integer frequency accounting,
frozen coefficients derived from rational power differentiation,
Taylor and partition budgets, the two outer diagonal terms,
and the exact formal-chain/OOOEE equivalence on finite integers.
It also reruns the kernel's exact carry inventory controls.
The numerical word census is a finite consistency check, not
evidence sufficient to infer a limiting density.

The proof depends on the stated earlier analytic supplements,
particularly (W3). This pass checks their use in the new family;
it does not supply an independent review of that entire proof chain.
No effective numerical threshold or uniform constant is certified.
The stronger historical kernel exponent, arbitrary decorated
families, localization to rejected short fibers, density-one
termination, and all-depth fair-share statements remain unresolved.

The next bounded step is to consolidate the dependency chain into
a readable manuscript proof, audit it afresh, and regenerate the
Zenodo artifacts only after that review. This branch stops with
(T1)--(T3); it does not publish or silently replace the release.

The classical tools are van der Corput differencing,
second-derivative estimates, and Fourier discrepancy inequalities;
see S. W. Graham and G. Kolesnik, Van der Corput's Method of
Exponential Sums, Cambridge University Press, 1991
([publisher excerpt](https://beckassets.blob.core.windows.net/product/readingsample/666252/9780521339278_excerpt_001.pdf)).
No literature-wide priority claim or independent peer review is asserted.

