# The live mass of odd starts: the frontier statement, priced and machine-checked

Status: **export**. Not a laboratory branch and not a new
formulation. This page states the one open quantity of the Juggler
termination programme in the language an analytic number theorist
would use, gives the exact price of every route the laboratory has
closed around it (7 September 2026), and names the parts of the
reduction that are now kernel-checked. It supersedes nothing; it
collects. Sources: Paper C
([juggler_fate_almost_all_note.md](juggler_fate_almost_all_note.md)
§§8–10), the Tao note
([juggler_tao_reduction_note.md](juggler_tao_reduction_note.md)
§§10–11), and the branch dossiers named below.

## The object

Let \(J(n)=\lfloor\sqrt n\rfloor\) for even \(n\) and
\(J(n)=\lfloor n^{3/2}\rfloor\) for odd \(n\). Fix the certified floor
\(N_0=3.5\cdot10^8\) (every start \(\le N_0\) reaches \(1\)). For
\(n\in(y,2y]\) let \(\tau(n)\) be the first time the orbit enters
\([1,N_0]\), let \(o_t(n)\) count the odd letters among the first \(t\)
iterates, and let \(L=\log_2(\log 2y/\log N_0)\). The quantity is

\[
\Lambda(y,d)=\frac{\#\{n\ \mathrm{odd}\in(y,2y]:\ \tau(n)>d\}}{y/2},
\qquad d=d(y)=\lceil CL\rceil .
\]

**What suffices.** If \(\Lambda(y,d(y))\le(\log y)^{-e}\) for all large
\(y\) with \(e>e_*=1-\lambda^{**}=0.5074\), the conjecture holds
(`J-tao-rate-implies-conjecture`, via the contagion theorem: every
backward-closed set has \(\sum_{n\le x}1/n\gg(\log x)^{\lambda}\) for
all \(\lambda<\lambda^{**}=0.4926\)).

## The frontier hypothesis

Write \(p_C=(1-1/C)\log2/\log3\), take \(q<p_C\), and the tilt
\(\theta=\log\bigl(p_C(1-q)/(q(1-p_C))\bigr)\). Let \(\mu_{\theta,t}\)
be the probability measure on the starts live at depth \(t\) with
density \(\propto e^{\theta o_t(n)}\), and

\[
s_\theta(t)=\mu_{\theta,t}\bigl(J^t(n)\ \text{odd}\bigr)
\]

the *tilted odd share*: the probability that the next letter is odd
when odd-heavy live prefixes are up-weighted exponentially.

**Hypothesis \(\mathrm M_{\theta,q}(C)\), no momentum.**
\(\sum_{t<d(y)}\bigl(s_\theta(t)-q\bigr)^+=o(d(y))\) for all large
\(y\).

**Theorem (kernel-checked reduction, `TiltedShare.lean`).** For any
nonnegative word weight whose two children never exceed their parent
(the live counts), with \(x=e^\theta\), \(a_q=1+(x-1)q\),
\(c_q=(x-1)/a_q\):
\[
\#\{o_d\ge k\}\ \le\ \frac{Z_0\,a_q^{\,d}}{x^{k}}\,
\exp\Bigl(c_q\sum_{t<d}(s_\theta(t)-q)^+\Bigr)
\qquad(\texttt{count\_le\_pressure}).
\]
The hypothesis itself is the Lean proposition `NoMomentum μ x q δ d`
(\(\sum_{t<d}(s_t-q)^+\le\delta d\)), and `count_le_of_noMomentum`
gives the count \(\le Z_0a_q^d e^{c_q\delta d}/x^k\) under it;
`tilt_exponent_eq_kl` identifies the per-step exponent at the
re-centring tilt with \(D(p_C\|q)\). At \(k=p_Cd\) the exponent is
\(-d\,D(p_C\|q)\) plus the excess term, so
\(\mathrm M_{\theta,q}(C)\) gives \(\Lambda\le(\log y)^{-CD(p_C\|q)/\ln2+o(1)}\),
which exceeds \(e_*\) exactly from the least \(C\):
\(C\ge19,\,41,\,214,\,1496\) at \(q=0.5,\,0.55,\,0.6,\,0.62\)
(`least_C_pressure`). The live counts are such a weight
(`liveWeight_weightSplit`, `LiveCountWeight.lean`), so
`juggler_count_le_of_noMomentum` states the count directly: for starts in
\([1,N]\) that stay above \(N_0\) for \(d\) steps with at least \(k\)
odd letters, \(\#\le N a_q^d e^{c_q\delta d}/x^k\) under `NoMomentum` of
the live count.

**What it does not need** (Paper C §9.3). Any \(o(\log\log y)\)
initial depths; any individual cylinder to split fairly (only the
tilted average over the \(\approx2^{0.97d}\) typical cylinders); towers
\(O^t\) biased below \(0.836\). **What it cannot be replaced by**
(§9.3(e)): any bounded-depth cylinder statement, since the measure that
is fair to depth \(k\) and all-odd afterwards satisfies every one of
them and keeps a positive live mass for ever.

## The price of failure

If the conjecture is false, then for every \(C\) and \(q\), infinitely
often in \(y\) (`J-failure-margin`):
\[
\frac1d\sum_{t<d}\bigl(s_\theta(t)-q\bigr)^+\ \ge\
m(C,q)=\frac{D(p_C\|q)-e_*\ln2/C}{c_q}-o(1).
\]

```text
  q      C=20    C=30    C=50    C=100   C=230   C->inf
  0.50   0.58%   2.87%   4.49%   5.59%   6.18%   6.62%
  0.55   0       0       0.91%   2.62%   3.48%   4.11%
  0.60   0       0       0       0       0.12%   1.56%
```

The margin is zero below the least \(C\) and saturates at \(6.6\%\) for
\(q=\tfrac12\): the conjecture's failure would force the tilted odd
share to exceed \(\tfrac12\) by \(6.6\%\) per step on average, at every
large \(C\), infinitely often. The existing pressure census (depth
\(40\), \(\pm0.06\)) sits at \(C=15.6\) and \(11.3\) at \(10^{50}\) and
\(10^{100}\) — below the least \(C\), where the margin is zero — and so
cannot bear on \(\mathrm M_{\theta,q}\) in principle.

## What is exact about the words

- **Tower absorption** (`TowerAbsorption.lean`, kernel-checked).
  \(\lfloor\sqrt{\lfloor x\rfloor}\rfloor=\lfloor\sqrt x\rfloor\): an
  odd step followed by \(j\) even steps is the single floor
  \(\lfloor n^{3/2^{j+1}}\rfloor\). An orbit value after any word is a
  nested tower with one level per **odd** letter and exponents
  \(3/2^{j_r+1}\) fixed by the even runs. The tower height is the odd
  count, not the depth; the tilt selects words of height
  \(\approx0.6\,d\).
- **The first letter is exact** (`J-depth-one-main-term`).
  \(\sum_{M\le X}e(\tfrac12M^{3/2})=0.27217\,X^{3/4}(1+o(1))\): the
  van der Corput dual of \(x^{3/2}\) is a rational cubic, so the
  second-derivative bound is attained, and the parity of
  \(\lfloor M^{3/2}\rfloor\) is biased toward even by \(0.425X^{3/4}\)
  — entirely on even \(M\), which Juggler sends to \(\lfloor\sqrt M\rfloor\).
  Over odd \(M\) every harmonic's main term cancels (the half-integer
  dual shift fixes the mod-\(27k^2\) cubic sums), so
  \(\#\{n\le X\ \text{odd}:\lfloor n^{3/2}\rfloor\ \text{odd}\}=X/4+O(X^{1/2+\varepsilon})\),
  measured near \(X^{1/4}\). Tower levels \(\ge2\) show only
  \(\sqrt N\)-order imbalance: the structure is special to the
  exponent \(3/2\).
- **Certified splits.** Every word class of depth \(\le4\) has its
  Bernoulli density with a power saving (Paper B Cor. 4.9); depth
  five is \(7/8\) certified, the open split being \(O^4\to O^5\)
  (Conjecture 7.3), where the level-3 floor difference
  \(\Delta_hz\asymp hn^{5/4}\) has derivative \(\gg1\) and the
  branch-run decomposition (\(e<2\)) that Theorem 5.3 rests on has no
  analogue.

## The routes and their exact prices

| route | what it needs | price | dossier |
|---|---|---|---|
| reset of \(s_\theta\) at the last even step | the complement to be Paper B | high-walk images are sparse; the complement is \(\mathrm H_q\) at unbounded depth | `juggler_pressure_direct` |
| reset only at *good bases* (even step at walk height \(u\le0\), fibres \(\ge y^{1/2}\)) | tolerance on the uncontrolled towers | tolerance \(\beta_*=p_C+O(1/d)\) at every scale: the split is \(\mathrm H_{p_C}\) on the towers; the fair-coin room is the \(\beta=\tfrac12\)/\(\beta=1\) inconsistency | `juggler_effective_tower_height` |
| Walsh expansion of the tilted moment | two-sided control of the tail | the tail is \(e^{\Theta(d)}\); two-sided is \(\mathrm H(C,A)\) | `juggler_pressure_direct` |
| low-order moments / large sieve | Walsh sums of order \(\propto d\) | a single character at depth \(t\) is already a height-\(0.6t\) tower | (this page) |
| forward \(S\)-sampling | \(S\)-fairness of the live set | the free term of the exact map | `J-tao-free-term-is-live-mass` |
| Weyl differencing | per-depth loss \(<2^{1/C}=1.037\) | differencing loses \(\ge2\) | Paper C Prop. 10.3 |
| rate-free density one (a different theorem) | qualitative equidistribution of the tower at every fixed depth, or node-wise even share \(\ge0.369\) | external: Hardy-of-floor composition, or the pair \(\tfrac54p+q<\tfrac23\) for \(cm^{9/4}-jm^{2/3}\) (hull \(95/112\)) | `exponent_pair_two_monomial` |

## What would count

An averaging theorem: for the tilted measure at depth
\(t\asymp\log\log y\), the odd share of the next letter is at most
\(q+o(1)\) on average over \(t\), for some \(q<0.6309\). It may fail on
any \(o(\log\log y)\) depths and on any family of cylinders of small
tilted weight; it is one-sided; it is a mean over the characters of a
nested-floor parity sequence, not a supremum. Everything the
laboratory can do at fixed depth has been run against it and missed;
the wall is the height-\(\ge4\) tower over a sparse base, in either
coordinate (the bracket in \(n\), the sub-density in the top variable).

## Appendix: what is machine-checked

`FateContagion.lean` (the exact layer of contagion),
`RateFreeDensity.lean` (Proposition J, the biased-split domination,
`weight_markov`), `TowerAbsorption.lean` (absorption),
`TiltedShare.lean` (Proposition 9.3, the Markov join, the hypothesis
`NoMomentum` with its count, and the identity
\(\theta p-\ln a_{\theta,q}=D(p\|q)\)), `LiveCountWeight.lean` (the live
count of starts is such a weight, and the Tao-type count on Juggler
itineraries follows from `NoMomentum` on it). Prose: the contagion rate
theorem and Paper B's estimates.
