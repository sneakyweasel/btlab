# A sharper concentration inequality does not move Paper C's constants

Killed claim: `tao_reduction.azuma_exponent` is lossy, so replacing
Azuma-Hoeffding by the sharp Chernoff-KL bound lowers the depth constants
\(C\), \(C(0.5)\), \(C(0.55)\); or the endpoint Chernoff bound wastes the
first-passage saving that the exact DP already computes, so the true rate
is better than \(e(C)\) and least \(C\) drops below \(19\).

Kill: both are real defects and neither has a consumer. Azuma uses only
the increment range \(\log_2 3\), while the increments are two-valued and
therefore admit Chernoff-KL — which the unbiased path in the same module
already uses via `kl_bernoulli`. It is genuinely weaker (at \(C=19\),
\(q=1/2\): \(0.523541\) against KL's \(0.526927\)) and the integers do not
move: least \(C=19\) at \(q=0.5\) and \(41\) at \(q=0.55\) under both
inequalities. Only \(q=0.6\) moves, \(223\to214\), and nothing consumes
\(q=0.6\). For the second: the exact first-passage exponent exceeds
\(e(C)\) at every finite depth, and the excess shrinks — \(0.2205\),
\(0.1231\), \(0.0673\) at \(L=20,40,80\) for \(C=18\) — while
\(\text{excess}\times L\) *grows* (\(4.41,4.92,5.38\)), which is an
\(O(\log L/L)\) correction and not \(O(1/L)\). A negative-drift walk
conditioned to stay above a level pays the same exponential cost as one
merely ending above it, so Chernoff already carries the true rate. The
hypothesis must hold as \(L\to\infty\), so the finite-depth surplus is
worth nothing.

Do not reopen as a Bernstein / Freedman / Bennett variance refinement, a
martingale bound with better constants, a first-passage or ballot
refinement of the bad-word count, or an exact-DP replacement of \(e(C)\).
The \(V_k\) ladder ceiling already recorded that any constant that moves
needs \(\lambda\) to move by \(0.0174\); this records that the other
input to those constants — the inequality — is also exhausted. What
remains is outside both: the \(r\ge2\) rungs, exported to Paper B.
Kind: `MEASUREMENT` / `METHOD_OBSTRUCTION`.
Branch: [juggler_external_input_audit](../problems/juggler_external_input_audit.md).

**Complement (PROMOTE).** The same audit assembled the transcendence
chain into one identity: the closure-threshold exponent of
[juggler_cycle_wuwang_reduction](../problems/juggler_cycle_wuwang_reduction.md)
*is* the provable irrationality measure \(\mu\) of \(\log2/\log3\), since
\(\lvert\Lambda\rvert=L\log3\lvert\alpha-o/L\rvert\ge cL^{1-\mu}\) feeds
\(n\log n\le(2/c)L^{\mu}\). That is why Dirichlet's \(\mu\ge2\) floors the
cycle target at \(L^{2}\). It also found that Paper A cites Rhin p. 160
equation (7) and prints \(14.3\), while equation (8) of the same
Proposition is reported in the literature as \(\mu\le8.616\) — which
would be a sharper statement one equation further down the same citation.
That row is **UNVERIFIED and DISPUTED** and load-bearing on nothing.
The report (Spiegelhofer, not Spiegelhofer–Wallner: the paper is
single-authored) was checked at the source and is transcribed correctly,
but Zudilin's survey (arXiv:math/0404523, §3.4 Theorem 3) attributes the
same \(8.616\) to the irrationality exponent of any nonzero
\(\theta\in\mathbb{Q}\log2+\mathbb{Q}\log3\) — a set containing
\(\log3\) but **not** the ratio \(\log3/\log2\). Only one reading can be
equation (8); under Zudilin's there is no sharper statement in Paper A's
citation at all. Nobody here has read Rhin p. 160. Wu-Wang's
\(5.1163051\) is sharper still either way and is what the laboratory
uses.

