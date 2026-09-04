# A two-monomial exponent-pair question

Status: **external mathematics**. Not a laboratory branch, not a
Juggler construction, and not a Phase-0. Phase 42 (2 September
2026) reconfirmed that asking this leftover as a harvest /
termination successor is a wrap, not a door. The objects are a clean
two-monomial exponential sum and the classical exponent-pair hull.
4 September 2026 adds the barrier half of the answer (§ *What is now
settled*): the \(A\)/\(B\) process route is closed unconditionally, the
hull minimum \(95/112\) is certified rather than recorded, and any pair
below the line is a subconvexity result past \(1/12\). The question
itself stays open and stays external.

## The question

Let \(c\neq 0\) and \(1\le\lvert j\rvert\le M^{2/5}\). Write

\[
f(m)=c\,m^{9/4}-j\,m^{2/3},\qquad
T_j(M)=\sum_{m\le M}e\bigl(f(m)\bigr).
\]

An exponent pair \((p,q)\) is *applicable* to \(f\) when the standard
derivative hypotheses of the pair hold on the relevant dyadic blocks
(Graham–Kolesnik / van der Corput: the first derivative of \(f\) is
monotonic of size \(\asymp M^{5/4}\)). Any such pair yields the block
bound \(T_j\ll M^{(5/4)p+q}\).

\[
\boxed{\text{Can one prove }\tfrac54 p+q<\tfrac23
\text{ for an exponent pair applicable to }cm^{9/4}-jm^{2/3}?}
\]

Equivalently: produce any applicable pair below that line, or any
specialized two-monomial bound of the same strength. Either would give
the sub-density estimate \(T_j=o(M^{2/3})\).

On those blocks the \(9/4\)-term dominates every derivative uniformly
in \(\lvert j\rvert\le M^{2/5}\) once the block length is
\(\gg M^{0.27}\); smaller blocks are already below \(M^{2/3}\). The
first-derivative scale is \(T\asymp M^{9/4}\), so
\(\alpha=\log M/\log T=4/9\).

## Known values

The functional \(\phi(p,q)=\tfrac54 p+q\) on recorded pairs and
ceilings (exact arithmetic):

| Source | Pair or bound | \(\phi\) |
|---|---|---|
| van der Corput derivative tests | \((1/6,2/3)\), \((1/14,11/14)\); \(k=3,4,5\) tests | \(7/8\) |
| Huxley 2005 | \((32/205,269/410)\) | \(349/410\approx 0.851\) |
| Bourgain 2017 | \((13/84,55/84)\) | \(95/112\approx 0.848\) |
| Bombieri–Iwaniec dream ceiling | \(p=3/20\) on \(q=p+\tfrac12\) | \(67/80=0.8375\) |
| Needed for \(T_j=o(M^{2/3})\) | — | \(<2/3\) |
| Exponent-pair conjecture | \((0,1/2)\) | \(1/2\) |

Theorem 4 below upgrades this table: \(95/112\) is not merely the
recorded minimum but the exact minimum of \(\phi\) over the entire
\(A\)/\(B\)/convex closure of these pairs.

Literature: `bourgain-2017-exponent-pair`, `huxley-2005-zeta-v`,
`huxley-1996-area-lattice-points`,
`kuipers-niederreiter-1974-uniform-distribution`.

## What is already settled

**Generic hull pairs miss (KNOWN).** The recorded minimum of
\(\phi\) on the known exponent-pair hull is Bourgain's
\(95/112\approx 0.848\), above \(2/3\). Huxley's pre-decoupling pair
is slightly worse. Van der Corput tests land at \(7/8\).

**Bombieri–Iwaniec cannot reach the line, even conjecturally within
the method (KNOWN).** BI-type pairs sit on the half-line
\(q=p+\tfrac12\). There \(\phi=(9/4)p+\tfrac12\), and
\(\phi=2/3\) at exactly \(p=2/27\). In the zeta normalization a
half-line pair gives \(\zeta(\tfrac12+it)\ll t^{\theta}\) with
\(\theta=p\). Even a complete resolution of both spacing problems
cannot get the zeta exponent below \(3/20\) (Huxley; Encyclopedia of
Mathematics, “Bombieri–Iwaniec method”). Hence no BI-producible pair
has \(p<3/20\), and

\[
\frac{3/20}{2/27}=\frac{81}{40}=2.025.
\]

The dream-ceiling functional is \(67/80=0.8375\), still far above
\(2/3\). Bourgain's \(13/84\) already resolves the first spacing
problem optimally; the remaining within-method slack is the second
spacing problem, and zeroing it cannot reach \(2/27\).

The \(B\)-process fixes the half-line pointwise. The \(A\)-process
worsens \(\phi\) precisely when \(p<1/6\) (exact root of
\(9p^2+\tfrac92 p-1\)), which covers every historical BI pair. No
\(A\)/\(B\) transform escapes. The regime \(\alpha=4/9\) sits in the
method's middle range \((2/5,1/2)\): there is no boundary loophole.

**The secondary monomial is inert (KNOWN).** On the blocks that
matter, \(-jm^{2/3}\) is lower order in every derivative and does not
change the resonance geometry. A native run of the method on
\((T,M)=(M^{9/4},M)\) is subject to the same ceiling.

## What is now settled (4 September 2026)

Five exact facts, all rational arithmetic; the verification is
[`tests/research/juggler_sequence/test_exponent_pair_hull.py`](../../tests/research/juggler_sequence/test_exponent_pair_hull.py).
Throughout an exponent pair carries the standard normalisation
\(0\le p\le\frac12\le q\le 1\), the processes are

\[
A(p,q)=\Bigl(\frac{p}{2p+2},\ \frac{p+q+1}{2p+2}\Bigr),\qquad
B(p,q)=\Bigl(q-\tfrac12,\ p+\tfrac12\Bigr),\quad B^2=\mathrm{id},
\]

and convex combinations of exponent pairs are exponent pairs, so the
linear \(\phi\) is minimised over a hull at a generating point.

**Theorem 1 (the \(A\)-process can never approach the line).** For every
exponent pair \((p,q)\),

\[
\phi\bigl(A(p,q)\bigr)=\frac{9p+4q+4}{8(p+1)}\ \ge\ \frac34,
\]

with equality only at \((p,q)=(0,\tfrac12)\).
*Proof.* \(\partial_q\) of the middle term is \(1/(2(p+1))>0\), so the
minimum over \(q\ge\frac12\) is at \(q=\frac12\), where
\(\phi(A)-\frac34=3p/(8(p+1))\ge0\). \(\square\)
Equivalently, in deficiency form,
\(1-\phi(A(p,q))=\bigl[(1-q)-\tfrac p4\bigr]/(2p+2)\le(1-q)/2\le\tfrac14\).

**Theorem 2 (nor \(A\) followed by \(B\)).**
\(\phi\bigl(B(A(p,q))\bigr)=\dfrac{8p+5q+4}{8(p+1)}\ge\dfrac{13}{16}\),
equality only at \((0,\tfrac12)\). *Proof.* \(\partial_q=5/(8(p+1))>0\);
at \(q=\frac12\) the excess over \(13/16\) is \(3p/(16(p+1))\ge0\).
\(\square\)

Both floors are attained exactly at the exponent-pair conjecture point,
which is not an exponent pair; on every actual pair they are strict. Both
sit **above** the density line \(2/3\).

**Corollary 3 (any solution is primitive).** Let \((p,q)\) be an exponent
pair with \(\tfrac54p+q<\tfrac34\) — in particular any pair answering the
boxed question. Then neither \((p,q)\) nor \(B(p,q)\) is the \(A\)-image
of an exponent pair: in any derivation from seeds, no \(A\) may occur as
the outermost or second-outermost letter. *Proof.* \((p,q)=A(x)\)
contradicts Theorem 1; \(B(p,q)=A(y)\) gives
\((p,q)=B(B(p,q))=B(A(y))\), contradicting Theorem 2. \(\square\)

So the pair cannot be manufactured by processing known pairs at all — it
must be produced directly. This supersedes the half-line observation
recorded above (\(A\) worsens \(\phi\) precisely when \(p<1/6\)): the
\(A\)-image floor is unconditional and independent of where its argument
sits.

**Theorem 4 (the known hull bottoms out at exactly \(95/112\)).** Let
\(H\) be the closure of \(\{(0,1)\}\) together with BI 1986, Huxley 1993,
Huxley 2005 and Bourgain 2017 under \(A\), \(B\) and convex combination.
Then \(\min_H\phi=95/112\), attained only at \((13/84,55/84)\).
*Proof.* \(A\) is the projective map
\([x:y:w]\mapsto[x:x+y+w:2x+2w]\), whose denominator \(2(p+1)w\) is
positive on the region, and \(B\) is affine; both therefore carry a
polytope to the polytope spanned by the images of its vertices. The
\(29\)-vertex rational polytope \(P\) built in the verification — the
convex hull of the depth-\(14\) closure together with the corners of the
exactly \(A\)-invariant tail box \([0,10^{-4}]\times[1-10^{-4},1]\) and of
its \(B\)-image — satisfies \(A(v),B(v)\in P\) for each of its \(29\)
vertices and contains all five seeds, so \(H\subseteq P\). As \(\phi\) is
linear, \(\min_P\phi=95/112\) at the vertex \((13/84,55/84)\), which lies
in \(H\). \(\square\)

This closes the "perhaps some long \(A\)/\(B\) word does better" question
that the recorded minimum left open: no word of any length, applied to
any exponent pair whatever, reaches \(\phi<3/4\) (Theorem 1), and inside
the published hull nothing goes below \(95/112\).

**Theorem 5 (the price of the line in the zeta normalisation).** Every
exponent pair satisfies \(\mu(\tfrac12)\le(p+q-\tfrac12)/2\), where
\(\zeta(\tfrac12+it)\ll t^{\mu(1/2)+\varepsilon}\). Hence

\[
\tfrac54p+q<\tfrac34\ \Longrightarrow\ \mu(\tfrac12)<\tfrac18,
\qquad
\tfrac54p+q<\tfrac23\ \Longrightarrow\
\mu(\tfrac12)<\tfrac1{12}-\tfrac p8\le\tfrac1{12}.
\]

*Proof.* For a pair with \(q\ge p+\frac12\) this is the classical
deduction: dyadic blocks \(N\le t^{1/2}\) in the approximate functional
equation give
\(\zeta(\tfrac12+it)\ll\log t\cdot\max_{N\le t^{1/2}}t^pN^{q-p-1/2}
=t^{(p+q-1/2)/2}\log t\). For a pair with \(q<p+\frac12\), apply that to
\(B(p,q)\), which is an exponent pair with
\(q'-p'-\tfrac12=p-q+\tfrac12>0\) and \(p'+q'=p+q\); the bound is
\(B\)-invariant, so it holds universally. For the consequences,
\(\phi<c\) and \(p\ge0\) give \(p+q<c-\tfrac p4\). \(\square\)

The boxed question is therefore not merely unreached — it is strictly
stronger than the subconvexity record:

| \(\mu(1/2)\) | value | factor over \(1/12\) |
|---|---|---|
| Bourgain 2017 (record) | \(13/84=0.15476\) | \(13/7=1.857\) |
| BI method ceiling | \(3/20=0.15\) | \(1.8\) |
| implied by \(\phi<3/4\) (the process floor) | \(<1/8=0.125\) | \(1.5\) |
| implied by \(\phi<2/3\) (the line) | \(<1/12=0.08333\) | \(1\) |

Even \(\phi<3/4\) — merely what Theorem 1 forbids the \(A\)-process from
reaching — would already break the record.

**Modern derivative tests do not help (exact).** On this phase
\(\lambda_k\asymp M^{9/4-k}\). The classical van der Corput \(k\)-th
derivative test gives block exponent
\(\max\bigl(1+\frac{9/4-k}{2^k-2},\,1-2^{2-k}-\frac{9/4-k}{2^k-2}\bigr)\),
minimised at \(7/8\) for \(k=3,4\). Heath-Brown's Vinogradov-based
\(k\)-th derivative test gives \(7/8\) at \(k=3\) and is worse at every
\(k\ge4\) (\(11/12\), \(191/200\), \(39/40,\dots\)): it is built for the
small-\(\alpha\) regime, and here \(\alpha=4/9\). Post-1990 \(k\)-th
derivative technology buys this phase nothing.

## What would count as a solution

Any one of the following:

- a new exponent pair \((p,q)\) applicable to \(f\) with
  \(\tfrac54 p+q<\tfrac23\);
- a specialized bound for this two-monomial phase (not necessarily
  packaged as a generic pair) giving \(T_j=o(M^{2/3})\).

The exponent-pair conjecture point \((0,1/2)\) would clear the line
with a power saving. No currently published pair or BI-refinement
does.

Theorems 1–5 pin down the *shape* either object must have.

- A new pair cannot be a processed one (Corollary 3): it has to come
  from a method that produces exponent pairs directly. And if it is an
  exponent pair at all, it is by Theorem 5 a subconvexity result past
  \(1/12\) — past both the decoupling record \(13/84\) and the
  Bombieri–Iwaniec ceiling \(3/20\). The line is not a technical gap in
  the hull; it is a strictly stronger statement than anything known
  about \(\zeta(\tfrac12+it)\).
- A specialized bound escapes Theorem 5 only by not being an exponent
  pair. Since a bound depending solely on the derivative sizes
  \(\lambda_k\asymp M^{9/4-k}\) is a statement about the whole class of
  phases carrying those sizes, such a bound must use something specific
  to the exponent pair \((9/4,2/3)\) or to \(c\). It would be a
  single-\(\alpha\) statement at \(\alpha=4/9\) rather than a full pair,
  which is a formally weaker object — but it is exactly what van der
  Corput / BI / decoupling theory computes at that \(\alpha\), and
  \(7/8\) (derivative tests) and \(95/112\) (Theorem 4) are its state of
  the art.

Not claimed: that \(T_j=o(M^{2/3})\) is false. The sum is expected
to sit at square-root scale; the missing object is a proof past the
known hull.

This is a question in the theory of exponent pairs. It is not a
dynamical construction, and it should not be rewritten as one.

## Appendix: laboratory origin

The phase \(f(m)=cm^{9/4}-jm^{2/3}\) is the Vaaler fluctuation of a
Piatetski–Shapiro inversion
\(S_c(N)=\sum_{m\le\lfloor N^{3/2}\rfloor}r(m)\,e(cm^{9/4})\),
\(r\in\{0,1\}\). The laboratory records of that reduction and of the
BI-ceiling comparison are
[juggler_ps_inversion_barrier.md](../problems/juggler_ps_inversion_barrier.md)
and
[juggler_bi_resonance_limit.md](../problems/juggler_bi_resonance_limit.md).
Both branches are **CLOSE**. This page is the export of the remaining
external question; it is not a successor research phase.
