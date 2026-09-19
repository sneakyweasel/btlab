# The poor-fiber tail, and the OE share on an arbitrary set

**Laboratory extract.** Status: **EXACT — HUMAN PROOF**. Not Lean. Not a
halt theorem, not a cycle exclusion, and not a strengthening of any
statement about the Juggler map itself: everything here is about the
parity of \(\lfloor n^{3/2}\rfloor\) on \(OE\) fibers, and its only
consequence is the coefficient of one production in the contagion
recursion.

Branch: [juggler_oe_rest_average](../problems/juggler_oe_rest_average.md).
Parent results: [Paper C](juggler_fate_almost_all_note.md) Lemmas 3.2,
4.2, 4.3 and 4.5. Probe:
`research.juggler_sequence.oe_rest_average`.

## What this closes

Paper C bounds the \(OE\) parity share \(\sigma_m=G_m/H_m\) from below in
two ways: pointwise, by \(\tfrac13-O(1/H_m)\) on every good fiber
(Lemma 4.2, from the monotone pairing Lemma 4.1'), and on average over an
even block of \(m\), by \(\tfrac12-o(1)\) (Proposition 4.4, from Vaaler's
approximation and two exponential-sum bounds). The first is sharp
pointwise — the \(\tfrac13\) is attained, not approached
(`J-oe-fiber-pairing-third-is-attained`) — and the second applies only to
the \(E\)-produced part of \(A\), because that is the part that arrives in
blocks. The rest of \(A\) got the pointwise bound, hence the coefficient
\(\tfrac29=(\tfrac23)(\tfrac13)\) in the production inequality (5.2).

The question this note answers is whether an adversarial backward-closed
\(A\) can concentrate on the fibers where the pointwise bound is the
truth. It cannot, and for a reason that needs nothing about \(A\): the
fibers with share bounded away from \(\tfrac12\) are so sparse that their
total \(1/m\)-weighted mass beyond \(U\) is \(O(U^{-1/3})\). There is
nothing to concentrate on.

The decay was measured before it was proved
(`oe_fiber_constant.poor_fiber_decay`, exponents \(0.32\) to \(0.40\)
across the thresholds tested); the exponent proved below is \(\tfrac13\).

## Notation

Fix \(m\ge 10^6\). As in Paper C §3, \(\Phi(m)\) is the set of odd \(n\)
with \(\lfloor n^{3/4}\rfloor=m\), \(H_m=\#\Phi(m)\),
\[
G_m=\#\{n\in\Phi(m):\lfloor n^{3/2}\rfloor\ \text{even}\},
\qquad \sigma_m=G_m/H_m .
\]
Write \(n_1<\dots<n_{H_m}\) for the members of \(\Phi(m)\),
\(x_j=n_j^{3/2}/2\), so \(\lfloor n_j^{3/2}\rfloor\) is even iff
\(\{x_j\}<\tfrac12\). Put
\[
A_m=\tfrac32m^{2/3},\qquad \alpha_m=\{A_m\},\qquad \eta_m=B_m-A_m,
\]
with \(B_m\) the upper step bound of Lemma 4.2. We use three facts from
Paper C, all of them Lean:

* **(F1)** every step \(\delta_j=x_{j+1}-x_j\) lies in \([A_m,B_m]\), and
  \(\eta_m\le 1.02\,m^{-1/3}\) (Lemma 4.2's proof; the Lean form
  `FiberParity.xval_step` gives the sharper \(\eta_m\le m^{-1/3}\));
* **(F2)** \(\tfrac23m^{1/3}-1\le H_m\le\tfrac23(m+1)^{1/3}+1\)
  (Lemma 3.2);
* **(F3)** hence \(\eta_mH_m\le
  1.02\bigl(\tfrac23(1+1/m)^{1/3}+m^{-1/3}\bigr)\le 0.6903\) for
  \(m\ge 10^6\), the expression being decreasing in \(m\).

\(\|z\|\) is the distance from \(z\) to the nearest integer. Note that
\(\alpha_m\) is **not** the fiber's own first step: the two differ by up
to \(\eta_m\), which is the same order as the resonance window below, so
they are not interchangeable (`oe_rest_average.alpha_star` against
`fate_contagion.fiber_alpha`).

## 1. The block lock

Everything rests on one inequality, and it is elementary. It says that a
fiber can be unbalanced only by locking onto a rational step of small
denominator.

**Lemma 1 (block lock).** Let \(m\ge10^6\) and let \(q\ge1\) be a
denominator of a convergent of \(\alpha_m\). Then
\[
\Bigl|\sigma_m-\tfrac12\Bigr|\ \le\
4\,\|q\alpha_m\|\ +\ \frac{5}{2q}\ +\ \frac{3.77\,q}{H_m}.
\tag{1.1}
\]

*Proof.* Put \(N=\lfloor A_m\rfloor\) and \(y_j=x_j-jN\). Then \(N\) is an
integer, so \(\{y_j\}=\{x_j\}\) and the good count is unchanged, and by
(F1) the steps of \(y\) lie in \([\alpha_m,\alpha_m+\eta_m]\). Write
\(\alpha=\alpha_m\), \(\eta=\eta_m\), \(H=H_m\).

Let \(p/q\) be the convergent, so \(\gcd(p,q)=1\) and
\(|\alpha-p/q|=\|q\alpha\|/q\). Cut \(1,\dots,H\) into
\(\lfloor H/q\rfloor\) consecutive blocks of length \(q\) and a remainder
of fewer than \(q\) indices. Inside one block, with \(j_0\) its first
index and \(0\le i<q\),
\[
y_{j_0+i}-y_{j_0}=\sum_{l=0}^{i-1}\bigl(\alpha+(\text{step}-\alpha)\bigr)
= i\alpha+r_i,\qquad 0\le r_i\le i\eta\le q\eta,
\]
and \(i\alpha=ip/q+i(\alpha-p/q)\) with
\(|i(\alpha-p/q)|\le\|q\alpha\|\). Hence, modulo \(1\),
\[
y_{j_0+i}\equiv y_{j_0}+\frac{ip}{q}+e_i,\qquad
|e_i|\le\varepsilon:=\|q\alpha\|+q\eta .
\tag{1.2}
\]
Because \(\gcd(p,q)=1\), the points \(\{y_{j_0}+ip/q\}\), \(0\le i<q\),
are exactly the \(q\) points of a translate of the \(1/q\)-grid. Two
elementary counts for such a translate:

* an arc of length \(\tfrac12\) contains \(\lfloor q/2\rfloor\) or
  \(\lceil q/2\rceil\) of them, so the count in \([0,\tfrac12)\) is within
  \(\tfrac12\) of \(q/2\);
* at most \(2\varepsilon q+1\) of them lie within \(\varepsilon\) of a
  fixed point of the circle.

A perturbation of size at most \(\varepsilon\) changes the indicator
\(\mathbf 1[\{\cdot\}<\tfrac12]\) only at points within \(\varepsilon\) of
\(0\) or of \(\tfrac12\), so by the second count it changes at most
\(4\varepsilon q+2\) of the indicators in the block. With the first count,
the good count of the block differs from \(q/2\) by at most
\(4\varepsilon q+\tfrac52\). The remainder block has fewer than \(q\) indices, so it contributes
at most \(q\) to \(|G_m-H/2|\); the sharper \(q/2\) is not needed.
Summing,
\[
\Bigl|G_m-\frac H2\Bigr|\ \le\ \frac Hq\Bigl(4\varepsilon q+\frac52\Bigr)+q
= 4\varepsilon H+\frac{5H}{2q}+q .
\]
Divide by \(H\) and substitute \(\varepsilon=\|q\alpha\|+q\eta\), using
\(\eta H\le0.6903\) from (F3):
\[
\Bigl|\sigma_m-\tfrac12\Bigr|\le
4\|q\alpha\|+\frac{5}{2q}+\frac qH\bigl(1+4\eta H\bigr)
\le 4\|q\alpha\|+\frac{5}{2q}+\frac{3.77\,q}{H}. \qquad\square
\]

Three remarks on what the proof does and does not use. It never assumes
the steps are monotone, and never assumes \(\alpha_m\le\tfrac12\), so
unlike Lemma 4.2 it needs no case split and no goodness hypothesis; it
applies to every fiber. It is a statement about one fiber, with no
averaging over \(m\). And it is sharp in form: the \(5/(2q)\) term is
real, since a fiber locked at \(q=3\) genuinely has share near
\(\tfrac13\) — those are the attaining witnesses of
`J-oe-fiber-pairing-third-is-attained`.

## 2. The lock lemma

**Lemma 2 (lock).** Let \(\eta_0\in(0,\tfrac12]\) and let \(m\ge10^6\)
satisfy \(H_m\ge 1280/\eta_0^2\). If
\(|\sigma_m-\tfrac12|\ge\eta_0\) then there is an integer \(q\) with
\[
1\le q\le \frac{3.77}{\eta_0}
\qquad\text{and}\qquad
\|q\alpha_m\|\ \le\ \frac{32}{\eta_0H_m}.
\]

*Proof.* Put \(\theta=\eta_0/16\) and \(H_0=\lfloor\theta H_m\rfloor\).
Since \(H_m\ge1280/\eta_0^2\ge 32/\eta_0\) we have \(\theta H_m\ge2\) and
so \(H_0\ge\theta H_m/2\). By **Dirichlet's approximation theorem** there is
\(q\) with \(1\le q\le H_0\) and \(\|q\alpha_m\|\le 1/(H_0+1)<1/H_0\).
Replacing \(p/q\) by its lowest terms \(p'/q'\) only decreases both \(q\)
and \(\|q\alpha_m\|\), since \(q'\alpha_m-p'=(q\alpha_m-p)/d\) with
\(d=\gcd(p,q)\), so we may assume \(\gcd(p,q)=1\), which is what (1.1)
requires. Apply (1.1) to this \(q\):
\[
\eta_0\ \le\ \frac{4}{H_0}+\frac{5}{2q}+\frac{3.77H_0}{H_m}
\ \le\ \frac{8}{\theta H_m}+\frac5{2q}+3.77\,\theta .
\]
Now \(3.77\theta=0.2356\,\eta_0\), and
\(8/(\theta H_m)=128/(\eta_0H_m)\le 0.1\,\eta_0\) because
\(H_m\ge1280/\eta_0^2\). Hence \(5/(2q)\ge 0.6644\,\eta_0\), i.e.
\(q\le 3.763/\eta_0\). Finally
\(\|q\alpha_m\|<1/H_0\le 2/(\theta H_m)=32/(\eta_0H_m)\). \(\square\)

An earlier version of this proof took \(q\) to be the largest continued-fraction
convergent denominator below \(H_0\), using \(\|q_k\alpha\|<1/q_{k+1}\).
That works, but it is more than the argument needs and it would drag continued
fractions into the formalization: the proof uses only \(q\le H_0\) and
\(\|q\alpha_m\|<1/H_0\), which is precisely Dirichlet's conclusion.
Mathlib has it as `Real.exists_nat_abs_mul_sub_round_le`, in the `round` form
that matches the resonance predicate exactly.

The hypothesis \(H_m\ge1280/\eta_0^2\) is the price of stating the lemma
for all \(\eta_0\) at once, and it is severe: at the \(\eta_0\) that
matters for §5 it puts \(m\) past \(10^{36}\). Nothing below is affected,
because the conclusion is asymptotic in \(x\); but it does mean the
lemma's own constants cannot be tested by enumeration, only the
inequality (1.1) behind them can. See §6.

## 3. The arc count

**Lemma 3 (arc count).** For \(u\ge10^6\), \(Q\ge1\) and
\(\delta\in(0,\tfrac12)\),
\[
\#\Bigl\{m\in(u,2u]:\ \exists\,q\le Q,\ \|q\alpha_m\|\le\delta\Bigr\}
\ \le\ \bigl(0.882\,u^{2/3}+2\bigr)
\Bigl(2Q\delta\,(2u)^{1/3}+\tfrac{Q(Q+1)}2\Bigr).
\]

*Proof.* This is Lemma 4.3 with its two goodness arcs replaced by a
general finite union, and the proof is the same.

Take one \(q\) at a time, and apply the arc count to \(\varphi_q(m)=q\cdot
\tfrac32m^{2/3}\) rather than to \(\tfrac32m^{2/3}\). Then
\(\|q\alpha_m\|\le\delta\) is membership in the **single** arc
\([0,2\delta)\) after the shift \(\varphi_q+\delta\), which is exactly the
shift `bad_mem_arc` uses to turn a wrap-around arc into one arc. The price is
the step bound: \(\varphi_q(m+1)-\varphi_q(m)\ge q\,(m+1)^{-1/3}\), so
\(d_q=q\,d\); and the gain is the window count, which rises to
\(q\cdot0.882u^{2/3}+2\). The \(q\) cancels between them:
\[
\bigl(0.882\,q\,u^{2/3}+2\bigr)\Bigl(\frac{2\delta}{qd}+1\Bigr)
= 0.882\,u^{2/3}\cdot\frac{2\delta}{d}\;+\;0.882\,q\,u^{2/3}\;+\;O(\delta/(qd)).
\]
Summing over \(q\le Q\) gives \(2Q\delta/d\) in the first term and
\(\sum_{q\le Q}q=\tfrac{Q(Q+1)}2\) in the second, which is the stated
bound. The underlying facts about \(\varphi\) are Lemma 4.3's:
\(\varphi(m+1)-\varphi(m)=\int_m^{m+1}t^{-1/3}\,dt\in
[(m+1)^{-1/3},m^{-1/3}]\), total increase
\(\tfrac32u^{2/3}(2^{2/3}-1)<0.882\,u^{2/3}\) over \((u,2u]\), and at most
\(w/d+1\) points of an arc of width \(w\) per integer window. \(\square\)

*Revision, on formalizing.* The first version of this proof covered
\(\|q\alpha_m\|\le\delta\) by the \(q\) arcs of half-width \(\delta/q\)
around the points \(p/q\), \(0\le p<q\), giving
\(\tfrac{Q(Q+1)}2\) arcs of total length \(2Q\delta\). That is correct and
gives the same bound, but it drags in which \(p\) are coprime to \(q\) and
makes the Lean an induction over a double union. Scaling the sequence instead of
subdividing the circle removes all of it: one arc per \(q\), no coprimality,
one application of the existing `arc_count_le` per \(q\). Lean:
`FiberParity.resonance_count_one` and `resonance_count_le` in
`Problems/Juggler/FateResonanceCount.lean`.

Lean: `FiberParity.arc_count_le` in `Problems/Juggler/FateThinFibers.lean`
is the per-window count \(w/d+1\), and `FiberParity.bad_count_le` is this
lemma for the two arcs of Lemma 4.2's goodness. The generalization needs
no new Lean idea, only the union bound over \(q\le Q\).

## 4. The theorem

**Theorem 4 (poor-fiber tail).** Let \(\eta_0\in(0,\tfrac12]\) and put
\[
P_{\eta_0}=\bigl\{m:\ |\sigma_m-\tfrac12|\ge\eta_0\bigr\},
\qquad
u_0(\eta_0)=\max\Bigl(10^6,\ \bigl(1950/\eta_0^2\bigr)^3\Bigr).
\]
Then for every \(u\ge u_0(\eta_0)\),
\[
\#\bigl(P_{\eta_0}\cap(u,2u]\bigr)\ \le\ \frac{420}{\eta_0^{2}}\,u^{2/3},
\tag{4.1}
\]
and for every \(U\ge u_0(\eta_0)\),
\[
\sum_{m\in P_{\eta_0},\ m>U}\frac1m\ \le\ \frac{2040}{\eta_0^{2}}\,U^{-1/3}.
\tag{4.2}
\]

*Proof.* For \(m>u\ge10^6\), (F2) gives
\(H_m\ge\tfrac23u^{1/3}-1\ge0.6566\,u^{1/3}\), and
\(u\ge(1950/\eta_0^2)^3\) makes \(H_m\ge1280/\eta_0^2\), so Lemma 2
applies to every \(m\in(u,2u]\) with \(Q=3.77/\eta_0\) and
\(\delta=32/(\eta_0H_m)\le 48.74\,u^{-1/3}/\eta_0\). Feed these into
Lemma 3:
\[
2Q\delta(2u)^{1/3}\le
2\cdot\frac{3.77}{\eta_0}\cdot\frac{48.74}{\eta_0}\cdot 2^{1/3}\cdot1.0001
=\frac{463.1}{\eta_0^2},
\qquad
\frac{Q(Q+1)}2\le\frac{8.99}{\eta_0^2},
\]
the second using \(\eta_0\le1\). Their sum is at most
\(472.1/\eta_0^2\), and \(0.882u^{2/3}+2\le0.8825\,u^{2/3}\) for
\(u\ge10^6\); the product is below \(420\,u^{2/3}/\eta_0^2\), which is
(4.1). Summing (4.1) over the dyadic blocks above \(U\),
\[
\sum_{m\in P_{\eta_0},\,m>U}\frac1m
\le\sum_{i\ge0}\frac{420}{\eta_0^2}\frac{(2^iU)^{2/3}}{2^iU}
=\frac{420}{\eta_0^2}U^{-1/3}\sum_{i\ge0}2^{-i/3}
\le\frac{2040}{\eta_0^2}U^{-1/3}. \qquad\square
\]

The constants are crude and the exponent is not. \(420\) and \(2040\)
carry the whole slack of Lemmas 1 to 3; the census finds the true density
of the fibers with \(\sigma_m\le0.40\) between \(1.4\,u^{-1/3}\) and
\(2.1\,u^{-1/3}\) over \(u\in[10^5,10^8]\), drifting slightly downward
(`oe_rest_average.poor_block_scaling`, `lock_census`). What matters is
that the exponent \(\tfrac13\) makes (4.2) summable: the poor set is not
merely thin, it has **finite total logarithmic mass**, so it cannot
support an adversary at every scale.

Nothing downstream is sensitive to the value \(\tfrac13\). Corollary 5
and §5 need only that the tail vanishes as \(V\to\infty\), so any
positive exponent would carry them; \(\tfrac13\) sets the rate at which
the recursion's error terms die and hence \(t_1\), not whether the
argument runs. The downward drift in the measured density is consistent
with the true exponent being slightly above \(\tfrac13\), which is the
direction that costs nothing.

**Corollary 5 (the share on an arbitrary set).** Let
\(\eta_0\in(0,\tfrac12]\) and \(V\ge u_0(\eta_0)\). For *every* set
\(S\subseteq(V,\infty)\) of integers — no backward closure, no structure
of any kind —
\[
\sum_{m\in S}\frac{\sigma_m}{m}\ \ge\
\Bigl(\frac12-\eta_0\Bigr)\sum_{m\in S}\frac1m\ -\
\frac{1020}{\eta_0^2}\,V^{-1/3}.
\]

*Proof.* On \(S\setminus P_{\eta_0}\) the integrand obeys
\(\sigma_m\ge\tfrac12-\eta_0\) pointwise. On \(S\cap P_{\eta_0}\) use
\(\sigma_m\ge0\) and discard at most \((\tfrac12-\eta_0)/m\le 1/(2m)\)
per term; (4.2) bounds that sum by
\(\tfrac12\cdot 2040\,V^{-1/3}/\eta_0^2\). \(\square\)

## 5. What it does to the recursion

This is the payoff the branch was reopened for, and it is a change of
proof economy rather than of the headline number.

In Paper C §5.1 the three families are the \(E\)-images, the \(OE\)-images
of the \(E\)-blocks, and the \(OE\)-images of the *rest*. The middle
family exists only because the block average of Proposition 4.4 needs its
members to arrive in even blocks, and the rest was split off from it to
keep the two disjoint. With Corollary 5 that split has no purpose: the
\(OE\) family may be taken over all of \(A\cap(x^{3/8},x^{3/4}]\) at once,
and it stays disjoint from the \(E\)-images for the reason it always did,
namely that one family is even and the other odd.

Fix \(\eta_0\) and let \(x\to\infty\). For
\(m\in A\cap(x^{3/8},x^{3/4}-1]\) the fiber \(\Phi(m)\) lies in
\((\sqrt x,x]\), the fibers are disjoint, each \(n\in\Phi(m)\) has
\(1/n>(m+1)^{-4/3}\), and
\(H_m(m+1)^{-4/3}\ge\tfrac2{3m}\bigl(1-\tfrac32m^{-1/3}\bigr)
\bigl(1-\tfrac4{3m}\bigr)\) by (F2). Corollary 5 with \(V=x^{3/8}\),
whose error \(V^{-1/3}=x^{-1/8}\) is the same shape as the error Lemma
4.3 already contributes, gives item 3 a log-mass at least
\[
\frac23\Bigl(\frac12-\eta_0\Bigr)\bigl(1-O(x^{-1/8})\bigr)\,g_A(3t/4)
\ -\ \frac{680}{\eta_0^2}\,x^{-1/8},
\]
and with item 1 unchanged the functional inequality becomes a
**two-production** one:
\[
g_A(t)\ \ge\ (1-\varepsilon_1(t))\,g_A(t/2)
+\Bigl(\tfrac13-\tfrac23\eta_0-\varepsilon_7(t)\Bigr)g_A(3t/4)
-\varepsilon_8(t),
\tag{5.1}
\]
with \(\varepsilon_7,\varepsilon_8\to0\) for each fixed \(\eta_0\).
Lemma 5.1 then gives \(g_A(t)\gg t^\lambda\) for every \(\lambda\) with
\(2^{-\lambda}+\bigl(\tfrac13-\tfrac23\eta_0\bigr)(3/4)^{\lambda}>1\).

Letting \(\eta_0\downarrow0\), the supremum of the attainable exponents is
the root of
\[
2^{-\lambda}+\tfrac13(3/4)^{\lambda}=1,
\qquad \lambda_{\rm ideal}=0.4926579801\ldots,
\]
which Paper C already names as the depth-two ceiling. It exceeds the
published \(\lambda^{**}=0.4925715447\ldots\); the two agree to
\(8.6\times10^{-5}\), and the break-even is \(\eta_0=8.60\times10^{-5}\)
(`oe_rest_average.averaging_theorem`).

So the value of this is not the exponent. It is that (5.1) uses **only**
Lemma 3.1, Lemma 3.2 and Theorem 4, and therefore:

* **Proposition 4.4 leaves the critical path.** Its two exponential-sum
  bounds — Vaaler's approximation, the second-derivative test,
  Kusmin–Landau — are Paper C's largest unformalized gap and the reason
  Theorem 5.3 is not Lean end to end. Nothing in §1–4 above uses an
  exponential sum, an approximation to the parity wave, or any tool
  beyond continued fractions and counting.
* **The six-word ladder and Appendix D leave it too**, since two
  productions now reach past where six took the exponent.
* **Lemmas 4.1, 4.1' and 4.2 leave it as well** --- their *statements* do.
  Theorem 4 needs no goodness hypothesis and no pointwise floor: fibers
  that would have been called bad are simply members of \(P_{\eta_0}\)
  and are discarded with the rest of it. What is retained is one step of
  Lemma 4.2's *proof*, the step interval (F1)
  (`FiberParity.xval_step`, Lean), which is where \(\alpha_m\) and
  \(\eta_m\) come from. The sweep lemmas themselves --- 4.1, its
  monotone form 4.1', and the \(H/3-2\) floor they produce --- are not
  used anywhere above.

Two things it does **not** do. It does not attain
\(\lambda_{\rm ideal}\), because \(\eta_0\) is fixed before \(x\) — the
published statement has the same shape. And it does not move any standing
question: the exponent is still below \(1\), Theorem 7.2 is still
conditional, no cycle is excluded and no orbit is shown to reach \(1\).
A ceiling on a method is not a statement about the map.

The threshold is honest about its size. At
\(\eta_0=4.3\times10^{-5}\), half the break-even,
\(u_0=1.2\times10^{36}\) and the recursion starts at
\(x_0=u_0^{8/3}\approx10^{96}\), so \(t_1\approx221\) and the implied
constant \(K=c_0t_1^{-\lambda}\) is small. The constants of Lemmas 1–3
are certainly improvable by a large factor; the exponent \(\tfrac13\) is
the part that would have to be wrong for the argument to fail.

## 6. What was checked, and how it could fail

Lemma 2's constants cannot be tested by enumeration — they bind only past
\(m\approx10^{36}\). Lemma 1 can, and it is the whole proof, so it is
what the probe attacks.

* **(1.1) at every convergent denominator \(q\le H_m\)**, over four
  windows at \(10^6,10^7,10^8,10^9\). A single negative slack refutes the
  note. `oe_rest_average.lock_census`.
* **(F3)**, the bound \(\eta_mH_m\le0.6903\) that fixes the constant
  \(3.77\), measured against the fibers' actual sizes.
* **Lemma 3** against its own bound at nine \((u,Q,\delta)\) combinations.
  `oe_rest_average.arc_count`.
* **The mechanism**: every fiber with \(\sigma_m\le0.40\) is locked, and
  at which \(q\). At \(10^7\) the locks are \(q\in\{1,3\}\) — \(q=1\) the
  fibers Corollary 4.6 calls extreme, \(q=3\) the attaining witnesses of
  the pairing third.
* **The exponent**, as the density of \(P\) times \(u^{1/3}\) across three
  scales: if that drifts upward the corollary is false, whatever (4.1)
  says. `oe_rest_average.poor_block_scaling`.

The falsifier that would have killed this: a low-share fiber with no
small-\(q\) resonance. None exists, and Lemma 1 says why none can.

## Formalization

**Lemma 1 is done and kernel-checked.**
`Problems/Juggler/FateBlockLock.lean`, `BlockLock.block_lock`, in the
un-divided form
\(|G-\tfrac H2|\le 4\varepsilon H+\tfrac{5H}{2q}+q\) with
\(\varepsilon=\rho+q\eta\); `lake env lean` exits clean and
`#print axioms` gives `[propext, Classical.choice, Quot.sound]`, the three
standard ones. The two grid counts of §1 are `grid_half_count` and
`grid_near_count`; `gridRes_mul_inj` and `grid_reindex` are where
\(\gcd(p,q)=1\) earns its place, by making the \(q\) points a full
\(1/q\)-grid; `span_bounds` is the telescoping; `block_count`,
`block_chain` and `block_lock` assemble them. It is a statement about an
arbitrary real sequence and imports nothing from the Juggler stack.

Remaining, in order. **Lemma 3** is `FateResonanceCount.lean`, written and
awaiting its dependency chain; it is `bad_count_le` with the two arcs
replaced by a union, and carries no new idea. **Lemma 2** is now a short
bridge rather than a project: Dirichlet
(`Real.exists_nat_abs_mul_sub_round_le`) supplies the \(q\), the
lowest-terms reduction supplies the coprimality `block_lock` wants, and the
rest is the \(\theta=\eta_0/16\) arithmetic, a real-number inequality of
the kind `FateProduction` already carries. **Theorem 4** is then the
composition, and (4.2) the dyadic sum that `bad_logMass_le` already does.
Nothing here needs `native_decide`.
