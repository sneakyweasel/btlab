# Phase Profiles and a Singular Continuous Law for Beatty First-Passage Counts

Philippe Cochin. 23 September 2026. Unpublished working note.

**Abstract.** We study binary survivor and first-passage counts at a Beatty
boundary. At the slope `alpha=log_2 3`, the normalized first-passage counts
admit an explicit positive cumulative jump profile, with exact weights and
total mass. Their complete set of accumulation values is the profile's
envelope with its open jump intervals removed: a nonempty compact perfect
set of Lebesgue measure zero. Their empirical probability measures converge
to the image of uniform phase measure under the profile. This limiting law
is singular continuous. Its continuous distribution function inverts the
profile and has explicit plateaus at the Beatty phases. All these qualitative
results, including the survivor asymptotic supplying the profile, are proved
in Lean for the actual integer counts.

**Main conclusions.** With the notation of Section 1 and `alpha=log_2 3`,
write `E=alpha/(alpha-1)`. The checked statements are

\[
\begin{gathered}
F(t)=1+\sum_{\delta_j<t}w_j,\qquad
R_r^+-F(\delta_r)\longrightarrow0,\qquad
\sum_{j\ge1}w_j=E-1,\\[3pt]
\operatorname{Clust}(R_r^+)
=K=[1,E]\setminus\bigcup_{j\ge1}(F(\delta_j),F(\delta_j)+w_j),\\[3pt]
\frac1N\sum_{0\le r<N}\delta_{R_r^+}
\Longrightarrow\mu=F_*\bigl(\lambda\!\restriction_{(0,1]}\bigr),
\qquad \mu(K)=1,\quad \lambda(K)=0,\quad \mu(\{y\})=0.
\end{gathered}
\]

For the continuous CDF `G(y)=mu((-infinity,y])`,

\[
G(F(t))=t\quad(0\le t\le1),\qquad
G(y)=\delta_j\quad\bigl(F(\delta_j)\le y\le F(\delta_j)+w_j\bigr).
\]

Thus the phase profile has dense jumps, while the distribution of its
values is continuous and singular. Sections 14–15 give the limit-set and
frequency proofs; Sections 12–13 establish their counting and asymptotic
inputs.

**Evidence boundary.** The preceding conclusions are **EXACT — LEAN VERIFIED**
at the concrete logarithmic slope, without unproved counting, binomial,
first-passage or equidistribution inputs. Sections 1–7 also retain a broader
written argument for irrational `1<alpha<2`, including a quantitative
`O(r^(-1/2))` rate. Those stronger statements are explicitly distinguished
from the checked qualitative specialization. This is a standalone working
note supporting Paper B; it does not revise a deposited paper or establish
literature priority or trajectory termination.

The phase-asymptotic interface is
[certificate_phase_asymptotic](../../formal/Problems/Juggler/BeattyCertificateAsymptotic.lean).
The exact series equality is in
[BeattyCertificateIdentification.lean](../../formal/Problems/Juggler/BeattyCertificateIdentification.lean),
with critical mass and concrete atom properties in
[BeattyCertificateMass.lean](../../formal/Problems/Juggler/BeattyCertificateMass.lean)
and [BeattyCertificateSeries.lean](../../formal/Problems/Juggler/BeattyCertificateSeries.lean).
[BeattyEndpointAsymptotic.lean](../../formal/Problems/Juggler/BeattyEndpointAsymptotic.lean)
discharges the finer terminal input and yields the unconditional survivor
`MeanderShape`. These build on the counting, coarse bounds and renewal modules
recorded below. The complete limit-set interface is
[certificateRatio_cluster_iff](../../formal/Problems/Juggler/BeattyCertificateCluster.lean),
and the empirical-law interface is
[certificateRatio_empiricalLaw_tendsto](../../formal/Problems/Juggler/BeattyCertificateDistribution.lean).
The latter module also proves continuity of the CDF, singularity and the
exact threshold and plateau formulas.

## 1. Statement and notation

This section and Sections 2–7 present the broader written argument. The
formal theorem summarized above specializes to \(\alpha=\log_2 3\).
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
The cumulative profile, identified in Lean at the logarithmic slope, is the
left-continuous function
\[
\boxed{\quad
F(\delta)=1+\sum_{\substack{r\ge1\\\delta_r<\delta}}w_r,
\qquad 0\le\delta\le1.
\quad}                                                     \tag{2}
\]
The written argument gives the stronger rate
\[
R_r^+=F(\delta_r)+O(r^{-1/2}),\qquad
\sum_{r\ge1}w_r=\frac1{\alpha-1}.                           \tag{3}
\]
At \(\alpha=\log_2 3\), the total mass and the qualitative error
\(R_r^+-F(\delta_r)=o(1)\) are Lean-checked; the displayed quantitative
rate is a separate written claim.
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
\boxed{\Delta F(\{\alpha\})=\beta\quad\text{and, at }\alpha=\log_2 3,\quad
\beta=\log_3 2
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
follows from \(n/(n-j)\le2\). Sections 12–13 formalize the qualitative
specialization of these inputs at the logarithmic slope. The displayed
quantitative remainder remains part of the written argument.
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
content is the explicit cumulative series, its phase asymptotic, the complete
accumulation set and the singular continuous empirical law. The proof includes
a non-circular coefficient bound and treatment of the dense jumps.
No priority claim is made; the coefficient method uses classical fluctuation
theory. The public Beatty manuscript supplies the same normalization and
envelopes, while this note identifies the whole profile and the distribution
of its values along the actual count sequence.

Before incorporating the conclusion into Paper B, independent review should
check especially: the positive-partial-sum specialization of (9); the uniform
offset estimate (10); and the coefficient-tail split in Section 5.
The paper's evidence labels are not retagged by this note. The analytic
convolution argument is covered by Lean, as described in Section 10.
Sections 12–13 discharge its concrete inputs and establish the complete
certificate-profile identification and unconditional `MeanderShape` at the
logarithmic slope. The quantitative rate and general irrational-slope
statement still require independent review.

Validation on 23 September: the module and the full retained Lean graph compile
(9034 build jobs); eleven principal declarations were audited and use only
the standard logical dependencies propext, Classical.choice and Quot.sound.
The style check reports zero new violations. The probe, previous phase-collapse,
ledger, layer-architecture and documentation-link tests pass. Research metadata
and this run's output hashes pass; the global hash check reports one unrelated
changed-source warning for a concurrently maintained Collatz manifest.

## 10. Lean continuation: from the formal exponential to MeanderShape

The formalization now separates the analytic consequence from the two
classical specialization inputs. This is a stronger result than the earlier
abstract moving-kernel lemma.

For any nonnegative real sequence `A`, define `b_n=A_n/n` (with `b_0=0`)
and let `u_n` be the coefficients of the formal series `exp(sum b_n X^n)`.
The theorem `renewalCoeff_phase_limit` proves:

~~~text
Phi is bounded,
sqrt(n) A_n - Phi(n beta) -> 0
    implies
n sqrt(n) u_n - sum_j u_j Phi((n-j) beta) -> 0.
~~~

The hypotheses impose no continuity on `Phi`. Lean derives all of the
following within the proof:

1. The terminal asymptotic gives a global square-root bound, including the
   finite initial segment. Hence `sum |b_n|` converges by the three-halves test.
2. Coefficient extraction from formal exponential substitution gives a sum
   of convolution powers divided by factorials. Their total masses form an
   ordinary exponential series, proving `sum u_n < infinity` without using
   a desired survivor asymptotic.
3. The formal chain rule proves the exact recurrence
   `n u_n = sum_{j<n} A_(n-j) u_j`.
4. The recurrence itself gives `u_n <= U/(n sqrt(n))`. For the near half the
   normalized sum is at most `2 K sum u_j`; assuming the bound at smaller
   indices, the far half is at most
   `4 U (sum_{k=1}^n |A_k|)/n`. The latter Cesaro mean tends to zero. Beyond
   a fixed cutoff its multiplier is at most `1/2`; a single constant covering
   the finite initial segment closes strong induction. This is a second,
   fully formalized non-circular proof of coefficient decay.
5. At each fixed lag the square-root ratio tends to one. Dominated convergence
   handles the near half, and the concrete Cesaro estimate removes the far
   half. All phases are evaluated exactly; no limit crosses an uncontrolled
   jump.

For the laboratory's actual slope `PaperBThreshold.beta`,
`BeattySurvivorProfile.lean` defines the terminal binomial count directly,
uses the existing `neverNegCount`, and sets `survivorBase=2*rateBase`.
Its proposed profile is exactly
`survivorPhase(x)=sum_j (N_j/v^j) terminalPhase(x-j beta)`.
The terminal phase is periodic and lies between
`a_0 s/(1-s)` and `a_0/(1-s)`. The zeroth survivor coefficient equals one,
so the survivor profile is bounded away from zero. This makes the additive
phase limit equivalent to the relative normalization in Paper B.

The final public statement is:

~~~lean
theorem meanderShape_survivorPhase
    (hcount : SurvivorExponentialIdentity)
    (hterminal : EndpointPhaseAsymptotic) :
    PaperBSurvivorAsymptotic.MeanderShape survivorPhase
~~~

`SurvivorExponentialIdentity` and `EndpointPhaseAsymptotic` are definitions
of propositions passed as theorem arguments. They are not axioms, and this
file contains no proofs of them. The later `BeattyCounting.lean` proves
the first, and `BeattyEndpointAsymptotic.lean` proves the second. They mean,
respectively, equality of the
actual normalized survivor coefficients with the formal exponential, and
convergence of the actual normalized terminal binomial counts to the explicit
bounded phase kernel.

| Statement | Current formal status |
|---|---|
| Formal exponential recurrence, summability, coefficient decay, moving limit | Lean proved |
| Actual `MeanderShape` for the explicit survivor profile | Lean proved unconditionally after Sections 12–13 discharge the inputs |
| Positive-partial-sum identity for the actual counts | Lean proved in `BeattyCounting.lean` |
| Actual sharp three-halves order, without a phase profile | Lean proved in `BeattyBinomialBounds.lean` |
| Uniform terminal binomial asymptotic | Lean proved at the logarithmic slope in Section 13 |
| Survivor-to-certificate series identification and total mass | Lean proved in Section 13 |
| Complete compact perfect null accumulation set and exact gaps | Lean proved in Section 14 |
| Uniform phase law, singular continuous empirical law and exact threshold frequencies | Lean proved in Section 15 |
| Quantitative `O(r^(-1/2))` error | Written proof; this continuation proves `o(1)` only |

These distinctions must be preserved in any communication about the result.
A kernel-checked implication with named hypotheses does not discharge those
hypotheses or settle the whole Beatty-passage question.

Continuation validation on 23 September: all three modules and the full
retained Lean graph compile (9037 build jobs). An executed dependency audit
of thirteen principal declarations, including the final `MeanderShape`
theorem, lists only `propext`, `Classical.choice` and `Quot.sound`. There are
no proof placeholders or added axioms. The style check reports zero new
violations, and the research metadata check reports zero errors and warnings.

## 11. Extracted partial theorems and corollaries

The first continuation yielded results with weaker hypotheses than the full
moving-phase asymptotic. Section 12 discharges the counting and coarse-bound
premises of the sharp-order result below.

**A purely integer formulation of the counting obligation.** The recurrence
`n u_n = sum_{j<n} A_(n-j) u_j`, together with `u_0=1`, uniquely determines
the formal exponential coefficients. This requires neither positivity nor
convergence. For the actual counts, cancellation of the exponential
normalization gives the Lean equivalence

~~~text
SurvivorExponentialIdentity
    iff
for every n, n N_n = sum_{j<n} T_(n-j) N_j.
~~~

The right side uses only natural-number counts and finite sums; `T_n` is
the strict positive-endpoint binomial count in `endpointCount`.
`survivorExponentialIdentity_iff_count_recurrence` proves this equivalence.
It does not by itself prove the recurrence. The separate theorem
`survivor_count_recurrence` now proves it at every degree; the older check
through degree 256 remains a finite regression check.

**Sharp polynomial order without a phase limit.** For nonnegative terminal
coefficients, Lean proves `A_n/n <= u_n` for the formal exponential
coefficients. If, for every positive `n`,

~~~text
a/sqrt(n) <= A_n <= K/sqrt(n),
~~~

then there is a finite `U >= 0` such that

~~~text
a/(n sqrt(n)) <= u_n <= U/(n sqrt(n)).
~~~

With `a>0` this is `u_n = Theta(n^(-3/2))`, without assuming a limiting
phase profile. The upper estimate requires only the upper terminal bound.
Theorems `exists_renewalCoeff_three_halves_bound` and
`renewalCoeff_three_halves_bounds` state these results. Their specialization
`survivor_three_halves_bounds_of_terminal_bounds` applies to the actual
survivor counts **assuming** the counting identity and the displayed coarse
bounds. Section 12 proves those premises and supplies an unconditional
actual-count theorem, without completing the finer profile.

**Uniform finite approximation, including the jumps.** If the actual
normalized survivor coefficients are summable, then for every real `x`,

~~~text
|psi(x) - sum_{j<N} u_j Phi(x-j beta)|
    <= (a0/(1-s)) sum_{j>=N} u_j.
~~~

The bound has no dependence on the phase or its distance from a jump.
`survivorPhase_truncation_bound` proves it, and
`survivorPhase_uniform_approximation` proves that for each positive tolerance
one cutoff works simultaneously for every real phase. This is a useful
approximation theorem despite the dense discontinuities. It is not yet a
numerical error certificate: an explicit computable tail bound is needed
to choose a certified cutoff. Section 12 now proves summability for the
actual counts unconditionally, so this approximation theorem no longer
requires a phase-asymptotic input when applied to these counts.

These intermediate theorems retain their displayed hypotheses. Section 13
now discharges them and completes the qualitative profile specialization.

The ten additional declarations compile in the full retained graph (9037
build jobs). Their executed dependency audit again lists only `propext`,
`Classical.choice` and `Quot.sound`; the style check has zero new violations.

## 12. Unconditional integer recurrence and sharp order

**EXACT — LEAN VERIFIED.** At `beta=log 2/log 3`, the new modules prove

~~~text
for every n >= 0,  n N_n = sum_{j<n} T_(n-j) N_j;
there exist a,U > 0 such that, for every n >= 1,
  a/(n sqrt(n)) <= N_n/v^n <= U/(n sqrt(n)).
~~~

There is no counting, binomial-estimate or phase-limit hypothesis in these
statements. The public interfaces are `survivor_count_recurrence`,
`survivor_exponential_identity`, `endpointNormalized_sqrt_bounds`,
`survivor_three_halves_bounds`, and `survivorDensity_isTheta_model`.
The last theorem states exactly
`survivorDensity =Theta[atTop] model` for the existing Paper B definitions.
The constants are existential; no numerical value for the survivor upper
constant or effective profile cutoff is claimed.

**Counting proof.** Retain an odd-letter variable `x`. Let `U_n(x)` be the
survivor polynomial and `D_n(x)` the first-descent polynomial. The existing
last-letter partition gives
`U_(n+1)+D_(n+1)=(1+x)U_n`, hence the formal-series factorization
`1-D(z,x)=(1-z(1+x))U(z,x)`. Survivor monomials have positive endpoint
weight `k-beta*n`, and first-descent monomials have negative weight.
Both closed support half-planes are preserved by products and formal
inversion at constant coefficient one. Euler differentiation preserves
them too. The difference of the two logarithmic derivatives is
`z(1+x)/(1-z(1+x))`. Its positive-weight coefficients are precisely the
terminal binomial coefficients. Evaluation at `x=1` gives the integer
recurrence. The proof also checks the strict convention: a positive power
of two cannot equal a power of three. No cycle-lemma assumption is used.

**Coarse terminal bounds.** Put `k=floor(n*beta)+1`. The binomial-ratio
identity and `beta>5/8` give consecutive-tail ratio at most `3/5`. Thus

~~~text
binom(n,k) <= T_n <= (5/2) binom(n,k).
~~~

Mathlib's global Stirling-sequence bounds give
`0 <= log(n!)-((n+1/2)log n-n) <= 1` for positive `n`.
For `n>=6`, both `k/n` and `(n-k)/n` are at least `1/6`. The elementary
logarithm inequalities bound the entropy correction uniformly. In particular,
with `q=1-beta`, Lean checks

~~~text
log(q/beta)-1/beta-2
  <= log(sqrt(n) binom(n,k)/v^n)
  <= 1+log 6.
~~~

Exponentiation and the finite positive initial segment yield positive
two-sided square-root bounds for `T_n/v^n` at every positive depth.
The previously checked renewal theorem then proves the sharp survivor order.

**Further consequence and remaining boundary.**
`summable_survivorNormalized_unconditional` proves `sum N_n/v^n < infinity`.
The explicit candidate profile is therefore absolutely convergent, bounded
above and away from zero, and has the previously proved uniform truncation
estimate, without assuming the fine phase limit. At this intermediate stage, identifying the candidate as the survivor
profile required `EndpointPhaseAsymptotic`; Section 13 now proves it and the
certificate identification and total mass. The quantitative rate remains open. This sharp-order theorem concerns
binary parity words and makes no assertion about integer-trajectory termination
or priority over the cited prior work. **PROMOTE** this completed intermediate
theorem within the existing branch.

Validation: the full retained Lean graph passes (9039 jobs), and a separate
consumer file checks the recurrence, all-positive-depth bounds, the exact
`Theta` statement, the phase theorem with only its terminal input, and
uniform profile approximation using the unconditional summability theorem.
All seven new principal declarations depend only on `propext`,
`Classical.choice` and `Quot.sound`. The style check has zero new violations;
the targeted combinatorial, layer, ledger and documentation-link tests pass,
as do ledger rendering, branch-index and research metadata checks (zero
errors and warnings).

## 13. Finer phase limit and complete certificate identification

**EXACT — LEAN VERIFIED, at `beta=log 2/log 3`.** The following results now
have no unproved mathematical inputs:

- `endpoint_phase_asymptotic`: `sqrt(n) T_n/v^n - Phi(n beta) -> 0`.
- `survivor_phase_limit_unconditional` and
  `meanderShape_survivorPhase_unconditional`: the actual survivor counts
  have the explicit convolution profile, additively and relatively.
- `certificateCriticalMass_hasSum`: first descent has total probability one
  for the critical Bernoulli weights.
- `certificate_jump_weights_hasSum`: `sum_{r>=1} w_r=1/s` for the actual
  counts, with `w_r=c_r beta^r q^(m_r-r)`.
- `certificateProfile_eq_transfer`: throughout `0<delta<1`, the consecutive
  survivor transfer equals `1+sum_{delta_r<delta} w_r`, including at atoms.
- `certificate_phase_asymptotic`:
  `r M_(m_r+1)/binom(m_r-1,r-1) - F(delta_r) -> 0`.

**The terminal refinement.** For `k=floor(n beta)+1` and `l=n-k`, the
relative entropy remainder satisfies

~~~text
0 <= k log(k/(n beta)) + l log(l/(n q)) <= 1/(n beta q), n >= 6.
~~~

Stirling's limiting constant and `k/n -> beta`, `l/n -> q` therefore give
`sqrt(n) binom(n,k)/v^n - a0 s^(1-fract(n beta)) -> 0`. For each fixed
lag, the binomial term divided by its first term tends to `s^j`; the already
proved `(3/5)^j` majorant justifies summing over all lags. The tail ratio
converges to `1/(1-s)`. No passage through a discontinuous phase is used.

**Critical total mass without optional stopping.** Let `P_n` be the total
critical weight of surviving words and `E_n` their weighted centered endpoint
height. The finite last-letter partition preserves probability and the
centered first moment. Certificate heights lie in `[-beta,0)`, so induction
gives `E_n+beta P_n <= beta`. For every `H>0`, splitting survivors at height
`H` gives

~~~text
P_n <= exp(H log(beta/q)) (N_n/v^n) + beta/H.
~~~

The normalized survivor counts tend to zero by proved summability. First
let `n` tend to infinity, then let `H` increase: `P_n -> 0`. Telescoping the
finite probability identity proves total first-descent mass one. Reindexing
by the unique certificate window gives `q + q sum_{r>=1} w_r=1`.

**Identification, not just jump matching.** Absolute convergence permits
reindexing the complete consecutive-survivor difference by the actual
certificate lengths. The scaled kernel is exactly
`s w_r/(1-s) + 1_{delta_r<delta} w_r`. Including the immediate descent as an
auxiliary zeroth atom makes the constant cancellation exact. The total-mass
theorem then leaves the claimed cumulative series. This excludes an
undetermined continuous component or additive constant.

**Original normalization.** At a positive crossing `m=m_r`, Lean proves
`endpointCutoff m=r` and the exact binomial identity
`r/binom(m-1,r-1)=m/binom(m,r)`. The preceding first-term Stirling limit
therefore suffices; no second unproved binomial normalization is inserted.
The factor `m sqrt(m)/((m+1)sqrt(m+1))` is retained until its limit is taken.
A moving quotient estimate is valid because the phase denominator is
uniformly bounded away from zero.

**Formal corollaries.** All positive-index weights are strictly positive;
distinct indices have distinct phases; `w_1=beta`; `F` is nondecreasing;
`1<=F<=1+1/s`; its traces are `F(0+)=1` and `F(1-)=1+1/s`; and each
right-minus-left jump is precisely its weight. The generic trace results
also identify continuity away from the listed atoms. No quantitative
`O(r^(-1/2))` remainder or effective numerical truncation constant is claimed.
The arbitrary-irrational-slope generalization remains a separate theorem.
**PROMOTE** the completed qualitative specialization within this branch.

Validation of Section 13: the complete retained Lean graph passes (9044
jobs). The separate consumer audit in `.build/beatty-phase/Audit.lean`
expands the final profile and weights into the original integer counts
and Bernoulli powers, and checks the terminal limit, `MeanderShape`,
first-passage mass and jump mass without extra hypotheses. All twenty
principal declarations list only `propext`, `Classical.choice` and
`Quot.sound`; there are no proof placeholders or added axioms. Lean style
has zero new violations. The targeted Beatty, layer, ledger and documentation
link tests pass, as do ledger rendering, branch-index and research metadata
checks (zero errors and warnings).

## 14. The complete certificate accumulation set

**EXACT — LEAN VERIFIED, at `alpha=log_2 3`.** Write
`E=alpha/(alpha-1)=1+1/s`. The complete set of real subsequential limits is

\[
\boxed{\quad
\operatorname{Clust}(R_r^+)=K
=[1,E]\setminus\bigcup_{j\ge1}
  \bigl(F(\delta_j),F(\delta_j)+w_j\bigr).
\quad}                                                     \tag{18}
\]

The set `K` is nonempty, compact and perfect, with Lebesgue measure zero
and empty interior. Thus the envelope contains a Cantor set of accumulation
values with explicitly identified complementary gaps. Both endpoints of
every listed gap are actual subsequential limits. The first gap has length
`w_1=beta`. This is a qualitative description of the complete limit set;
it does not assert a rate of approach. Section 15 proves the limiting frequency law.

The public interface
[certificateRatio_cluster_iff](../../formal/Problems/Juggler/BeattyCertificateCluster.lean)
uses `MapClusterPt y atTop certificateRatio`, which for real sequences is
equivalent to convergence along a strictly increasing subsequence. Its
right-hand side is membership in the explicitly defined `certificateClusterSet`.
The original integer counts and binomial denominator are retained in
`certificateRatio`; no fitted or independently assumed phase model replaces them.

**Range geometry.** The generic module
[BeattyProfileGeometry.lean](../../formal/Problems/Juggler/BeattyProfileGeometry.lean)
proves that the closure of a summable nonnegative cumulative jump profile's
range is precisely its envelope minus its open jump intervals. The atoms
must be distinct and lie in `(0,1)`; density is unnecessary for this first
statement. For the reverse inclusion, a supremum cut locates any omitted
value between the two traces at one phase. If the traces differ, that phase
is an atom, and the omitted value lies in its listed gap. This rules out
unlisted gaps as well as an unaccounted continuous component.

Monotonicity makes the open gaps pairwise disjoint. Each has Lebesgue measure
equal to its weight, and their total measure equals `sum w_j=E-1`. Subtracting
them from the envelope leaves measure zero. Dense strictly positive atoms
make `F` strictly increasing on `[0,1]`. Its left traces, and its right trace
at zero, approximate every range value by distinct range values. The closure
is consequently perfect. These statements are proved for the generic series
before specializing to the certificate weights.

**Actual subsequences.** The new certificate module proves recurrence of the
exact phase sequence in every open subinterval of `[0,1]`, arbitrarily far
along the sequence. Positivity of every nonzero certificate phase first
proves irrationality of `1/beta`. Mathlib's density and recurrence theorems
for a compact additive circle then apply. Sampling the one-sided continuous
profile along these recurrent phases gives exactly its range closure as
the set of subsequential limits. A separate general lemma proves that an
additive error tending to zero preserves every real subsequential limit in
both directions. Applying the existing `certificate_phase_asymptotic` proves
(18) without a new analytic premise.

**A precise finite-depth consequence.** For every listed gap and every
closed interval `[a,b]` strictly inside it, there is a depth beyond which
`R_r^+` never belongs to `[a,b]`. This is
`certificateRatio_eventually_avoids_gap`. Individual finite-depth values may
still enter a gap near its endpoints. The formal theorem does not claim that
all sufficiently large values lie exactly in `K`.

**Boundary and decision.** The geometry of a positive pure jump series is
a general consequence, not a novelty claim. The application here specifies
every certificate accumulation value and every interior gap beyond the
earlier extremal envelopes. Section 15 now proves empirical weak convergence
to the law of `F(U)` for uniform `U`, and singular continuity of that law.
Those results use additional modules beyond the cluster-set proof. Quantitative errors,
effective constants and arbitrary irrational slopes remain separate as well.
**PROMOTE** this completed accumulation-set theorem within the existing dossier.

Validation: the complete retained Lean graph passes (9046 jobs). The executed
consumer audit in `.build/beatty-cluster/Audit.lean` expands the count ratio and
the gap set, and checks compactness, perfectness, null measure, empty interior,
nonemptiness and the two endpoint limits. All seventeen audited principal
declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.
There are no proof placeholders or added assumptions. Lean style reports zero
new violations; the targeted Beatty, layer, ledger and documentation-link tests
pass. Registry lint, ledger rendering, branch-index validation and research
metadata checks pass, with zero metadata errors or warnings.

## 15. The singular continuous empirical certificate law

**EXACT — LEAN VERIFIED, at `alpha=log_2 3`.** Let `U` be uniform on
`(0,1]`, and let `mu` be the probability law of `F(U)`. For the actual
normalized integer counts, the empirical measures converge weakly:

\[
\boxed{\qquad
\frac1N\sum_{0\le r<N}\delta_{R_r^+}\ \Longrightarrow\
\mu=F_*\bigl(\lambda\!\restriction_{(0,1]}\bigr).
\qquad}                                                     \tag{19}
\]

Equivalently, for every bounded continuous real function `g`,

\[
\frac1N\sum_{0\le r<N}g(R_r^+)
\longrightarrow \int_0^1 g(F(t))\,dt.                         \tag{20}
\]

Lean defines the harmless zeroth ratio by its total natural-number formula.
The empirical probability object uses `N+1` samples to avoid an empty
probability measure; the test-function theorem (20) uses the first `N`
samples. Changing finitely many initial samples leaves the limit unchanged.

The public declarations are
`certificateRatio_empiricalLaw_tendsto` and `certificateRatio_average_tendsto`
in [BeattyCertificateDistribution.lean](../../formal/Problems/Juggler/BeattyCertificateDistribution.lean).
The limit uses the exact profile from Section 13, with the actual integer
certificate counts in its weights. No phase distribution hypothesis remains.

**Proof of convergence.** The reciprocal slope `1/beta` is irrational.
For each nonzero integer frequency, the associated geometric exponential
sum is uniformly bounded in its length. The existing Weyl criterion
therefore proves Haar equidistribution on the circle. Choosing the `(0,1]`
representative preserves measure and is continuous except at one point.
[BeattyPhaseEquidistribution.lean](../../formal/Problems/Juggler/BeattyPhaseEquidistribution.lean)
concludes that the exact certificate phases have uniform empirical law;
the exceptional zeroth representative does not affect the limit.

The profile is monotone, so its discontinuity set is countable. A proved
almost-everywhere continuous mapping theorem passes phase equidistribution
through `F`, even though every positive sample phase is itself a jump point.
Finally `R_r^+-F(delta_r)->0` transfers the same law to the actual counts.
The generic tools in
[BeattyWeakConvergence.lean](../../formal/Problems/Juggler/BeattyWeakConvergence.lean)
prove the mapping step by the open-set Portmanteau criterion, and the error
transfer using bounded Lipschitz tests and Cesaro convergence.

**Singular continuity.** Lean proves all of the following:

- `mu({y})=0` for every real `y`, since strict increase of `F` on `[0,1]`
  makes each restricted level set contain at most one phase.
- `mu(K)=1` and `mu(K^c)=0`, where `K` is the explicit compact perfect
  accumulation set of Section 14.
- `mu` and Lebesgue measure are mutually singular, since `lambda(K)=0`.
- The distribution function `G(y)=mu((-infinity,y])` is continuous everywhere.

Thus a discontinuous pure jump phase profile produces a **singular continuous
probability law** for the normalized counts. The statement concerns the
limiting measure; it does not assert that the finite-depth ratios lie in `K`
or that their frequency of exact membership in `K` tends to one. Weak
convergence alone would not justify that assertion, because `K` has full
limiting boundary mass.

**Exact frequency and plateau corollaries.** For every `t` in `[0,1]`,

\[
G(F(t))=t,\qquad
\frac{\#\{0\le r<N:R_r^+\le F(t)\}}{N}\longrightarrow t.       \tag{21}
\]

More generally the frequency below every real threshold `y` tends to `G(y)`;
there are no exceptional thresholds because the limiting law has no atoms.
Each jump interval gives an exactly identified flat segment:

\[
G(y)=\delta_j\quad\text{for every}\quad
y\in[F(\delta_j),F(\delta_j)+w_j],\qquad j\ge1.                \tag{22}
\]

Every such closed interval has zero limiting mass, including its endpoints,
although both endpoints are subsequential limits of the counts. The exact
interfaces are `certificateLaw_Iic_profile`, `certificateRatio_threshold_frequency`,
`certificateRatio_profile_threshold_frequency`, `certificateLaw_closed_gap`
and `certificateLaw_Iic_gap`.

**Boundary and decision.** These are qualitative frequency results for the
concrete logarithmic slope. No discrepancy rate, effective truncation error,
arbitrary-slope certificate theorem, or literature priority claim is added.
The generic measure arguments are standard; the specialization identifies
the empirical law of the original certificate counts explicitly.
**PROMOTE** this completed empirical-law theorem within the existing dossier.

Validation: the complete retained Lean graph passes (9049 jobs). The executed
consumer audit in `.build/beatty-distribution/Audit.lean` expands the averages
into the original integer counts, natural floors and Bernoulli jump weights.
It also checks weak convergence, atomlessness, continuous CDF, singularity,
full limiting mass on `K` and exact threshold frequencies. All seventeen
audited principal declarations depend only on `propext`, `Classical.choice`
and `Quot.sound`, with no proof placeholders or added axioms. Lean style
has zero new violations. The targeted Beatty, layer, ledger and documentation
link tests pass, along with registry lint, ledger rendering, branch-index
validation and research metadata checks (zero errors and warnings).

## References

1. G. Baxter, *An analytic problem whose solution follows from a simple
   algebraic identity*, Pacific Journal of Mathematics **10** (1960),
   731–742, Example 3. [doi:10.2140/pjm.1960.10.731](https://doi.org/10.2140/pjm.1960.10.731).
2. M. Winkler, *Marked Rotations and Factorization Heights for Dual Beatty
   Passage Counts*, preprint, v21, 13 September 2026, Proposition 34.
   [doi:10.13140/RG.2.2.22015.57761](https://doi.org/10.13140/RG.2.2.22015.57761).
3. M. Winkler, *Admissible qx+1 Sequences, Semiconvergents, and Rational
   Catalan Numbers*, preprint, 14 September 2026, Corollary 12.
   [arXiv:2609.22303v1](https://arxiv.org/abs/2609.22303v1).
