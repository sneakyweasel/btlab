# Fixed positive Pell domains cannot preserve an actual OOE return

Recorded 22 September 2026. The
[Pell invariant-domain attempt](../problems/juggler_pell_invariant_domain.md)
proves an unconditional bracket. For \(X_0=1,X_1=m\ge2\),
\(X_{k+1}=2mX_k-X_{k-1}\), and prescribed \(A=E\circ O\circ O\),
\[
X_{\lceil9k/8\rceil-1}<A(X_k)<X_{\lceil9k/8\rceil}\qquad(k\ge2).
\]
The quadratic-unit formula has leading coefficient \(1/2\); the ratio
\(X_k^9/X_l^8\) jumps across the entire return window when the integer
\(9k-8l\) changes from nonpositive to positive. Exact OOE root bounds
control the remaining error. This uses neither abc nor a logarithmic
linear-form estimate.

For k=1 and m>=5 the endpoint is between X_1 and X_2. The formal small
returns at 1, 2, 3 and 4 all fail OOE source guards. Consequently no
actual OOE block starts and ends in the x-coordinate set of one fixed
equation \(x^2-Dy^2=1\), and no nonempty sparse subset of that set can
be an OOE invariant domain. The actual nonsquare example
\(97\to955\to29512\to171\) leaves the D=3 Pell family.

The fixed-Pell route is **CLOSE**. This does not cover longer branch
words, switching equations, right side other than 1, or general escape.
Allowing arbitrary new D is vacuous since every n>=2 solves
\(n^2-(n^2-1)\cdot1^2=1\). No invariant nonsquare seed was constructed.
Member: J-pell-ooe-interlacing-obstruction.
