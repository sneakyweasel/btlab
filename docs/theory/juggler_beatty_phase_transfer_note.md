# A jump-series formula for the Beatty first-passage profile

23 September 2026. Working mathematical note; not a paper revision.

**Evidence boundary.** Sections 1–7 give a written proof using the classical
Sparre Andersen–Spitzer generating-function identity and uniform Stirling
estimates. The proof is presented for independent review. It is not an
end-to-end Lean proof. The Lean module
[BeattyPhaseTransfer.lean](../../formal/Problems/Juggler/BeattyPhaseTransfer.lean)
checks the phase coordinates, the exact count and jump cancellation identities,
the finite-depth error algebra, the regularity of a summable positive jump
series, and a dominated moving-kernel convergence theorem with explicit
kernel bounds and a vanishing remainder as hypotheses. It does not prove the generating-function identity, Stirling estimate,
or their specialization to the asymptotic below. No termination claim is made.

## 1. Statement and notation

Fix an irrational \(1<\alpha<2\), and put
\[
\beta=\alpha^{-1},\quad q=1-\beta,\quad s=\alpha-1=q/\beta,\quad
v=\beta^{-\beta}q^{-q},\quad \rho=v/2,\quad
B=v^\alpha=\frac{\alpha^\alpha}{(\alpha-1)^{\alpha-1}}.
\]
The application is \(\alpha=\log_2 3\). Let \(N_d\) count binary words for which
every nonempty prefix of length \(j\) has more than \(\beta j\) ones.
Set \(N_0=1\), \(M_d=2N_{d-1}-N_d\),
\[
m_r=\lfloor\alpha r\rfloor,\quad \delta_r=\alpha r-m_r,\quad
c_r=M_{m_r+1},\quad C_r=\binom{m_r-1}{r-1},\quad
R_r^+=\frac{r c_r}{C_r}.
\]
The \(M_d\) in this note always counts first-descent words, not words sitting
on the survivor barrier.

Define the positive weights
\[
\boxed{\quad
w_r=\frac{c_r}{B^r q^{\delta_r}}
    =c_r\beta^r q^{m_r-r},\qquad r\ge1.
\quad}                                                     \tag{1}
\]
The proposed answer, justified below by the written argument, is the
left-continuous function
\[
\boxed{\quad
F(\delta)=1+\sum_{\substack{r\ge1\\\delta_r<\delta}}w_r,
\qquad 0\le\delta<1.
\quad}                                                     \tag{2}
\]
It satisfies
\[
R_r^+=F(\delta_r)+O(r^{-1/2}),\qquad
\sum_{r\ge1}w_r=\frac1{\alpha-1}.                           \tag{3}
\]
In particular
\[
F(0+)=1,\qquad F(1-)=\frac{\alpha}{\alpha-1},\qquad
F(\delta_r+)-F(\delta_r-)=w_r.                              \tag{4}
\]
It is continuous at every other interior point. All interior jumps are upward.
Their locations are dense, so “pure jump” does not mean piecewise constant on
nonempty intervals. In fact \(F\) is strictly increasing: the orbit is dense
and every \(c_r\ge1\), as witnessed by \(r\) ones followed by zeros until the
first crossing. On the circle there is additionally a downward wrap at zero.

For the first atom, \(m_1=c_1=1\); hence
\[
\boxed{\Delta F(\{\alpha\})=\beta=\log_3 2
       =0.630929753571457\ldots.}                           \tag{5}
\]
No fitted amplitude occurs in these formulas.

## 2. Exact comparison of normalizations

At a crossing \(d=m_r+1\), irrationality gives \(0<\delta_r<1\), and
\[
\{m_r\beta\}=1-\beta\delta_r,\qquad
\{(m_r+1)\beta\}=\beta(1-\delta_r).                         \tag{6}
\]
If a bounded survivor profile \(\psi\) gives
\[
N_d=v^d d^{-3/2}\bigl(\psi(\{d\beta\})+o(1)\bigr),          \tag{7}
\]
the certificate identity and the uniform binomial normalization imply
\[
F(\delta)=
\frac{2\sqrt{2\pi(\alpha-1)}}{\alpha}\,
s^{-\beta\delta}
\left[
 \psi(1-\beta\delta)-\rho\,\psi(\beta(1-\delta))
\right],\qquad 0<\delta<1.                                 \tag{8}
\]
Here
\[
C_r=\kappa q^{\delta_r}B^r r^{-1/2}(1+O(r^{-1})),
\qquad \kappa=(2\pi\alpha(\alpha-1))^{-1/2}.
\]
This is Proposition 34 of the public v21 manuscript *Marked Rotations and
Factorization Heights for Dual Beatty Passage Counts*, where the lower
normalized family is denoted \(R_r^G\). The earlier \(R_r^+\) notation is
retained in this laboratory.

For verification, before taking a limit the relevant bracket is
\[
L_m-\rho\left(\frac m{m+1}\right)^{3/2}L_{m+1},
\qquad L_j=j^{3/2}N_j/v^j.
\]
The polynomial ratio tends to one. Boundedness of the profiles controls the
error; positivity of the difference need not be assumed to obtain an additive
\(o(1)\). This avoids subtracting two relative asymptotics without controlling
cancellation.

## 3. The generating-function input and a uniform binomial estimate

Let \(T_n\) count all binary words with a positive endpoint, with no prefix
restriction:
\[
T_n=\sum_{k=\lceil n\beta\rceil}^n\binom nk,\qquad
A_n=T_n/v^n,\quad b_n=A_n/n,\quad u_n=N_n/v^n.
\]
The classical positive-partial-sum identity is
\[
U(z):=\sum_{n\ge0}u_nz^n
=\exp\left(\sum_{n\ge1}b_nz^n\right).                      \tag{9}
\]
One obtains it by applying the Sparre Andersen–Spitzer identity to independent
fair binary increments \(X-\beta\), then rescaling the generating variable.
There are no nonempty zero-sum words because \(\beta\) is irrational.
The positive-partial-sum generating identity is given, for example, in
[Baxter (1960), Example 3](https://msp.org/pjm/1960/10-3/pjm-v10-n3-p01-s.pdf);
it specializes to (9) by extracting the diagonal where all partial sums
are positive. This is a classical input, not a new identity.

Put
\[
a_0=(2\pi\beta q)^{-1/2},\qquad
\Phi(x)=\frac{a_0s^{1-x}}{1-s}\quad(0\le x<1).
\]
Uniform Stirling expansion at \(k=n\beta+h\), \(0<h<1\), gives
\[
\binom n{\lceil n\beta\rceil}/v^n
=a_0n^{-1/2}s^{1-\{n\beta\}}(1+O(n^{-1})).
\]
The successive ratios in the upper binomial tail approach \(s<1\);
summing that geometric tail gives, uniformly in the offset,
\[
\boxed{\sqrt n\,A_n=\Phi(\{n\beta\})+O(n^{-1}).}            \tag{10}
\]
For completeness, the uniformity is not a non-lattice approximation: write
each term relative to the first as a product of successive ratios. These
ratios are bounded above by \(s\). For \(j\le n^{1/4}\), that product is
\(s^j(1+O((j+1)^2/n))\), uniformly in \(h\). Summing its error uses
\(\sum(j+1)^2s^j<\infty\); the remaining tail is exponentially small in
\(n^{1/4}\). This proves the stated \(O(n^{-1})\) relative tail estimate.
Thus \(0\le b_n\le K n^{-3/2}\) and \(L:=\sum b_n<\infty\).

## 4. A coefficient bound without assuming the desired asymptotic

It would be circular to use the conjectured \(n^{-3/2}\) estimate for \(u_n\)
to justify the limiting convolution. The following elementary bound supplies
it directly from (9).

For a \(k\)-tuple of positive integers summing to \(n\), at least one component
is at least \(n/k\). In the coefficient of \(b(z)^k\), sum over the possible
choice of that component and then over the other \(k-1\) components. The
chosen component is fixed by their sum, so
\[
0\le[z^n]b(z)^k
\le K k^{5/2}L^{k-1}n^{-3/2}.
\]
Summing over \(k\ge1\), with the exponential coefficient \(1/k!\), gives
\[
u_n\le K_u n^{-3/2},\qquad
K_u=K\sum_{k\ge1}\frac{k^{5/2}L^{k-1}}{k!}<\infty.          \tag{11}
\]
This also gives
\[
\sum_{j>J}u_j=O(J^{-1/2}),\qquad
\sum_{1\le j\le J}j u_j=O(\sqrt J).
\]
In particular \(U(1)<\infty\). These facts precede, and do not assume, a
phase-only limit.

## 5. Constructing the survivor profile and bounding the remainder

Define
\[
\boxed{\psi(x)=\sum_{j\ge0}u_j\Phi(\{x-j\beta\}).}           \tag{12}
\]
The series converges uniformly and absolutely because \(\Phi\) is bounded and
\(\sum u_j<\infty\). It is bounded above, and bounded below by
\(a_0s/(1-s)>0\), since \(u_0=1\).

Differentiate the formal identity (9) and compare coefficients:
\[
n u_n=\sum_{j=0}^{n-1}A_{n-j}u_j.                          \tag{13}
\]
Let \(x_n=\{n\beta\}\). Multiplying by \(\sqrt n\), split the sum at \(j=n/2\).
For \(j\le n/2\), (10) and
\(\{x_n-j\beta\}=\{(n-j)\beta\}\) give
\[
\sqrt n A_{n-j}
=\sqrt{\frac n{n-j}}\,
\left[\Phi(\{x_n-j\beta\})+O((n-j)^{-1})\right].
\]
Since \(\sqrt{n/(n-j)}=1+O(j/n)\), the error summed against \(u_j\) is
\[
O\left(n^{-1}\sum_{j\le n/2}(j+1)u_j\right)=O(n^{-1/2}).
\]
For \(j>n/2\), put \(k=n-j\). By (10) and (11), the remaining contribution is
\[
\sqrt n\sum_{1\le k<n/2}A_ku_{n-k}
=O\left(n^{-1}\sum_{k<n/2}k^{-1/2}\right)=O(n^{-1/2}).
\]
The omitted tail of (12) is also \(O(n^{-1/2})\). Consequently,
\[
\boxed{n^{3/2}u_n=\psi(\{n\beta\})+O(n^{-1/2}).}            \tag{14}
\]
This proves the asserted phase asymptotic by a coefficient argument.
The abstract Lean moving-kernel theorem applies to the first-half kernel
\(\mathbf1_{j<n,\;2j\le n}\sqrt n A_{n-j}\), the shifted kernel
\(\Phi(\{x_n-j\beta\})\), and the second-half remainder above. Its fixed-index
approximation follows from (10) and \(\sqrt{n/(n-j)}\to1\); its domination
follows from \(n/(n-j)\le2\). Establishing these concrete inputs is part of
this written argument, not yet of its Lean specialization.
It never replaces a moving phase by its limit, and so does not require
continuity at an orbit point or uniform separation from the dense jump set.
The constants depend on the fixed slope; no uniformity as \(\alpha\to2\)
or \(\alpha\to1\) is claimed.

Each summand in (12) has a downward jump of size \(a_0u_j\) at \(\{j\beta\}\).
Dominated convergence permits termwise one-sided limits. Irrationality makes
these points distinct, giving the previously conjectured jump law. Off that
orbit the series is continuous. If desired, its Fourier identity is
\[
\widehat\psi(k)=
\frac{a_0}{\log(1/s)-2\pi i k}\,
U(e^{-2\pi i k\beta}).                                    \tag{15}
\]
The denominator contains \(\log(1/s)\). Replacing it by \(-2\pi i k\)
is only a high-frequency approximation; it loses the continuous part of
the survivor profile.

## 6. Cancellation gives a pure jump profile

For \(0<\delta<1\), set \(x=1-\beta\delta\), \(y=\beta(1-\delta)\).
Since \(y=x+\beta-1\),
absolute convergence of (12) permits reindexing:
\[
\psi(x)-\rho\psi(y)
=\sum_{j\ge0}\frac{M_{j+1}}{2v^j}\Phi(\{x-j\beta\})
 -\rho\Phi(y).                                            \tag{16}
\]
The first-descent support is exactly \(j=0\) and \(j=m_r\), \(r\ge1\).
Indeed a first-descent word ends in a zero, and with \(r\) ones it must satisfy
\(\beta j<r<\beta(j+1)\). At \(j=0\) its count is \(M_1=1\).

For a crossing \(j=m_r\),
\[
\{x-m_r\beta\}=
\begin{cases}
\beta(\delta_r-\delta),&\delta<\delta_r,\\
0,&\delta=\delta_r,\\
1+\beta(\delta_r-\delta),&\delta>\delta_r.
\end{cases}
\]
Multiply (16) by the prefactor \(2s^{-\beta\delta}/a_0\) in (8). The crossing
term becomes \(s w_r/(1-s)\) when \(\delta\le\delta_r\), and
\(w_r/(1-s)\) when \(\delta>\delta_r\). The two remaining terms, from
\(M_1=1\) and \(-\rho\Phi(y)\), add to \(-s/(1-s)\), using
\(v s^{1-\beta}=\alpha\). Thus
\[
F(\delta)=\frac{s}{1-s}\left(\sum_{r\ge1}w_r-1\right)
          +\sum_{\delta_r<\delta}w_r.                      \tag{17}
\]
The next section shows \(\sum w_r=1/s\), reducing the constant to exactly one.
This derives (2), rather than reconstructing a function from its jumps
without excluding an additional continuous component.

At an individual crossing the same cancellation is particularly transparent:
\[
\Delta F(\delta_r)
=\frac{2s^{-\beta\delta_r}}{a_0}
 \left(a_0\frac{N_{m_r}}{v^{m_r}}
       -\rho a_0\frac{N_{m_r+1}}{v^{m_r+1}}\right)
=w_r.
\]
This algebraic cancellation is covered by Lean.

## 7. Total mass by a centered walk

Take independent Bernoulli variables with \(\mathbb P(X=1)=\beta\),
\(\mathbb P(X=0)=q\), and consider the centered walk
\(S_n=\sum_{i=1}^n(X_i-\beta)\).
Its first strictly negative time is almost surely finite.

Here is an elementary justification. Stop upon entering \((-\infty,0)\)
or \([H,\infty)\). In the remaining bounded interval, a fixed sufficiently
long block of zeros forces exit. Such a block has fixed positive probability
in each independent block of that length. The stopping time is therefore
finite almost surely. The stopped walk lies in the bounded interval
\([-\beta,H+1-\beta]\), so bounded stopping and dominated convergence give
\(\mathbb E S_\tau=0\). If \(p_H\) is the probability of upper exit,
\[
0=\mathbb E S_\tau\ge p_H H-(1-p_H)\beta,\qquad
p_H\le\frac{\beta}{H+\beta}.
\]
Survival forever would require upper exit for every \(H\); letting \(H\to\infty\)
proves its probability is zero.

First descent at length one has probability \(q\). Every other first-descent
word has length \(m_r+1\), with \(r\) ones, and there are \(c_r\) such words.
The probability of that event is
\[
c_r\beta^r q^{m_r+1-r}=q w_r.
\]
These events partition the almost sure first descent. Therefore
\[
q+q\sum_{r\ge1}w_r=1,\qquad
\sum_{r\ge1}w_r=\frac{\beta}{q}=\frac1s.
\]
This proves the normalization in (3). Equations (14), (8), and uniform
Stirling now give the error \(O(r^{-1/2})\) asserted there.

## 8. Reproducible finite checks

Runner:

~~~powershell
python tools/lab.py run research.juggler_sequence.beatty_phase_transfer --depth 8000 --coefficient-depth 256
python tools/lab.py test -- tests/research/juggler_sequence/test_beatty_phase_transfer.py -q
~~~

The run computes exact survivor counts to depth 8000 (crossing orders 1–5047)
and independently checks the integer coefficient identity
\[
nN_n=\sum_{k=1}^n T_kN_{n-k}
\]
through \(n=256\). This finite check is not a proof of (9).
The first weights, evaluated with floating-point logarithms, are:

| order | phase | predicted jump |
|---:|---:|---:|
| 1 | 0.584962501 | 0.630929754 |
| 2 | 0.169925001 | 0.146916662 |
| 3 | 0.754887502 | 0.185388186 |
| 4 | 0.339850003 | 0.064753517 |
| 5 | 0.924812504 | 0.095328147 |
| 6 | 0.509775004 | 0.038053482 |
| 7 | 0.094737505 | 0.022152587 |
| 8 | 0.679700006 | 0.039600725 |

These can be compared with the earlier finite-window jump measurements
\(0.633,0.148,0.188,0.066,0.098,0.039,0.023,0.042\).
Window averages include nearby atoms; they should not equal individual jumps.

The partial atomic masses through orders 1261, 2523 and 5047 fall short of
\(1/s\) by approximately \(0.040444,0.028594,0.020219\).
For orders 4548–5047, the observed ratio minus the respective cumulative
partial series lies approximately in
\([0.000031,0.040099]\), \([0.000018,0.028249]\), and
\([0.000011,0.019877]\). These are numerical diagnostics, not interval
certificates for the finite-depth error or evidence replacing the proof.

The output and its actual-run provenance are
[phase_transfer.json](../../data/research/juggler/winkler_phase_collapse/phase_transfer.json)
and
[phase_transfer.research.json](../../data/research/juggler/winkler_phase_collapse/phase_transfer.research.json).

## 9. Review boundary and relation to the existing programme

The exact change of normalization alone is a reparameterization. The added
content is the explicit cumulative series and a written proof of its limit,
including a non-circular coefficient bound and the treatment of dense jumps.
No priority claim is made; the coefficient method uses classical fluctuation
theory. The public Beatty manuscript supplies the same normalization and
envelopes, while this note proposes the whole profile.

Before incorporating the conclusion into Paper B, independent review should
check especially: the positive-partial-sum specialization of (9); the uniform
offset estimate (10); and the coefficient-tail split in Section 5.
The older MeanderShape assumption and the paper's evidence labels are not
retagged by this note. The analytic argument is not covered by the current
Lean module. Formalizing only the algebra does not certify the asymptotic.

Validation on 23 September: the module and the full retained Lean graph compile
(9034 build jobs); eleven principal declarations were audited and use only
the standard logical dependencies propext, Classical.choice and Quot.sound.
The style check reports zero new violations. The probe, previous phase-collapse,
ledger, layer-architecture and documentation-link tests pass. Research metadata
and this run's output hashes pass; the global hash check reports one unrelated
changed-source warning for a concurrently maintained Collatz manifest.
