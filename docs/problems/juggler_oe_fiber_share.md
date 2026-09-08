# Juggler: the OE-fiber share is a quadratic sweep, exact on cubes

## Problem

Paper C's productions count, for each target \(m\), the odd \(n\) in the \(OE\)
fiber \(\Phi(m)=\{n\ \text{odd}: m^4\le n^3<(m+1)^4\}\) whose odd-step image
\(\lfloor n^{3/2}\rfloor\) is even. Some fibers are empty: \(99969\) has
\(G_m=0\), while \(10^6\) has \(G_m=H_m\). Why, how often, and what does it do to
the argument?

## Exact statement

Let \(H_m=|\Phi(m)|\), \(G_m\) the even-image count, \(\alpha_m\) the fractional
part of \(\tfrac32m^{2/3}\) taken in \((-\tfrac12,\tfrac12]\),
\(\beta_m=\alpha_mH_m\), and \(\theta_m=\{n_1^{3/2}/2\}\) with \(n_1=\min\Phi(m)\).

**Share law.** \(G_m/H_m=S(\beta_m,\theta_m)+O(H_m^{-1})\), where
\[
S(\beta,\theta)=\bigl|\{s\in[0,1]:\ \{\theta+\beta s+s^2/3\}<\tfrac12\}\bigr|.
\]

**Phase average.** \(\int_0^1S(\beta,\theta)\,d\theta=\tfrac12\) for every \(\beta\).

**Extreme window.** \(S\in\{0,1\}\) is possible iff \(\beta\in[-\tfrac56,\tfrac16]\).

**Empty measure.** \(\int\bigl|\{\theta:S(\beta,\theta)=0\}\bigr|\,d\beta=\tfrac{25}{108}\).

**Cubes.** For \(m=k^3\) and every \(n=k^4+t\in\Phi(k^3)\),
\(\lfloor n^{3/2}\rfloor=k^6+\tfrac32k^2t\) exactly, since \(3t\le4k\) on the fiber.
Hence the fiber of an even cube is full and the fiber of an odd cube alternates
exactly.

## Current literature

`independent`; internal to Paper C. Its Lemma 4.2 defines the same \(\alpha_m\),
calls \(m\) bad when \(\|\alpha_m\|<22m^{-1/3}\) or \(\|\alpha_m-\tfrac12\|<2m^{-1/3}\),
proves \(G_m\ge H_m/3-2\) on good \(m\) by the monotone sweep Lemma 4.1', and bounds
the bad set in Lemma 4.3. Proposition 4.4 averages over even blocks by Vaaler and van
der Corput and needs no per-fiber bound. Section 11 there records the mean share
\(\tfrac12\) and a minimum near \(\tfrac13\) on good fibers. The quadratic phase is the
same object as the curvature of [juggler_parity_complexity](juggler_parity_complexity.md)
at a different scale, and the exact cube identity is a one-interval strengthening of
the record's "floor is a no-op iff the state is a square"
([juggler_exact_floor_impact](juggler_exact_floor_impact.md)).

## Branch budget

- **Target:** explain the empty and full \(OE\) fibers and price their effect on
  Paper C.
- **Novelty hypothesis:** the share is a deterministic function of two phases, not a
  coin; at cubes it is exact.
- **Falsifier:** a fiber whose share is far from \(S(\beta_m,\theta_m)\) outside the
  \(O(1/H)\) error, or an extreme fiber outside the drift window, or a cube fiber that
  is neither full nor alternating.
- **Already killed by?:** none. Not a cycle claim, not a construction of
  \(e(uw^{3/2})\), not a local attack; it is the anatomy of a fiber Paper C already
  treats.
- **Existing machinery:** Paper C's Lemma 3.2 fiber, exact integer cube roots,
  `Nat.eq_sqrt` in Lean.
- **Maximum Phase-0 scope:** the law, its three corollaries, the cube identity in Lean,
  a census to \(10^6\).
- **Promotion criterion:** an exact theorem plus a sharpening Paper C can adopt.
- **Stop criterion:** the law fails the window fit.

## Balanced-ternary formulation

None. The objects are integer fibers of a floor-power map.

## Why BT may be relevant

It is not; recorded for the template.

## Candidate operations / invariants

- the cube identity and its range: **EXACT — LEAN VERIFIED**;
- the share law and the phase average: **EXACT — HUMAN PROOF**;
- the extreme window and the \(25/108\): **EXACT — HUMAN PROOF** as properties of
  \(S\); the resulting empty-fiber density: **OBSERVATION**, since it assumes
  \((\beta_m,\theta_m)\) equidistribute;
- the census and the window fit: **COMPUTATIONALLY VERIFIED**.

## Experiments

`python -m research.juggler_sequence.oe_fiber_share` writes
`data/research/juggler/oe_fiber_share/summary.json` in about five seconds: cube checks
for \(k\le120\), the exact \(25/108\), phase averages, density scans at three scales, and
the window fit near \(10^6\).

Window fit near \(10^6\), fiber length 67: 432 fibers with \(|\beta_m|\le1.2\), mean
absolute error \(0.0195\) against \(1/H=0.015\), maximum \(0.26\) at one tangency.
All 105 extreme fibers found have \(\beta_m\in[-0.788,0.143]\subset[-\tfrac56,\tfrac16]\).

| scale | \(H\) | mean share | predicted empty | empty | full |
|---|---|---|---|---|---|
| \(10^4\) | 14.9 | 0.4995 | 1.56% | 2.00% | 2.10% |
| \(10^5\) | 31.1 | 0.4996 | 0.75% | 1.05% | 0.85% |
| \(10^6\) | 66.9 | 0.4991 | 0.35% | 0.58% | 0.33% |

The observed empty density runs 1.3 to 1.7 times the asymptotic prediction. Two
candidate reasons, neither tested: the count \(G_m=0\) includes fibers whose model
share is below \(1/2H\), and \(\beta_m\) and \(\theta_m\) may be correlated, both being
functions of \(m^{2/3}\). The prediction is therefore an observation, not a claim.

Cubes, \(2\le k\le120\): every even \(k\) full, every odd \(k\) alternating, the
identity holding on every fiber element, and \(3t_{\max}=4k\) attained, so the Lean
hypothesis is the fiber's own bound. The identity itself outlives the fiber, holding
to \(t<1.63k\) and failing at \(t=2k\).

## Conjectures

None registered.

## Counterexamples

None to the law. To the fair-coin picture of a fiber: \(m=k^3\) for every even \(k\)
is a full fiber and for every odd \(k\) an alternating one, deterministically.

## Formalization

`formal/Problems/Juggler/CubeFiber.lean`, registered in `Problems.Juggler` and in
`lean_paths.LAYERS`: `cube_fiber_range` (\(3t\le4k\) on the fiber, by contradiction from
\((3k^4+4k+1)^3\ge27(k^3+1)^4\)), `cube_fiber_sqrt_even` and `cube_fiber_sqrt_odd` (the
identity by `Nat.eq_sqrt` and `nlinarith`), `cube_fiber_even_image`,
`cube_fiber_alternating`, and the fiber-level `even_cube_fiber_full` and
`odd_cube_fiber_alternating`. Mathlib's three axioms only. The share law is not
formalized: it is real analysis with an \(O(1/H)\) error.

## Results

**1 (EXACT — LEAN VERIFIED).** For \(a\ge1\) and every \(n\) with \((2a)^4\le n\) and
\(n^3<((2a)^3+1)^4\), \(\lfloor n^{3/2}\rfloor\) is even. For every odd \(n\) with
\((2a+1)^4\le n\) and \(n^3<((2a+1)^3+1)^4\), \(\lfloor n^{3/2}\rfloor+(n-(2a+1)^4)/2\)
is odd. Mechanism: \(n^{3/2}=k^6(1+t/k^4)^{3/2}=k^6+\tfrac32k^2t+\tfrac38t^2/k^2-\dots\),
and \(\tfrac38t^2/k^2<1\) exactly while \(t^2<\tfrac83k^2\); the parity of
\(k^6+\tfrac32k^2t\) is \(0\) for even \(k\) and \(1+t/2\) for odd \(k\).

**2 (EXACT — HUMAN PROOF).** The share law. Consecutive odd \(n\) advance
\(x=n^{3/2}/2\) by \(\tfrac32\sqrt{n_j+1}\), and \(\sqrt{n_1+2(j-1)}=\sqrt{n_1}+(j-1)/\sqrt{n_1}+O(j^2n_1^{-3/2})\),
so \(x_j=x_1+A(j-1)+\tfrac34(j-1)^2/\sqrt{n_1}+O(j^3n_1^{-3/2})\) with
\(A=\tfrac32\sqrt{n_1}\). With \(\sqrt{n_1}=m^{2/3}(1+O(m^{-4/3}))\) and
\(H=\tfrac23m^{1/3}+O(1)\), the quadratic coefficient times \(H^2\) is
\(\tfrac13+O(1/H)\), the cubic term is \(O(1/H)\) over the fiber, and
\(\{A\}=\alpha_m+O(m^{-4/3})\). Counting \(j\) with \(\{x_j\}<\tfrac12\) against the
measure of \(s\) with \(\{\theta+\beta s+s^2/3\}<\tfrac12\) costs one point per boundary
crossing, of which there are \(O(1+|\beta|)\), hence \(O(1/H)\) in share.

**3 (EXACT — HUMAN PROOF).** \(\int_0^1S(\beta,\theta)d\theta=\tfrac12\): by Fubini
the inner integral over \(\theta\) of the indicator is \(\tfrac12\) for each \(s\),
whatever the phase function. The extreme window: for \(\beta\ge0\) the phase increases
by \(\beta+\tfrac13\) over the fiber; for \(-\tfrac23\le\beta<0\) it falls by
\(\tfrac34\beta^2\) then rises to \(\max(0,\beta+\tfrac13)\); for \(\beta<-\tfrac23\) it
falls by \(-\beta-\tfrac13\). An extreme needs total range \(\le\tfrac12\), which is
\(\beta\in[-\tfrac56,\tfrac16]\). The \(\theta\)-measure of the empty set is \(\tfrac12\)
minus the range, and its integral over the four pieces is
\(\tfrac1{72}+\tfrac{11}{108}+\tfrac{11}{108}+\tfrac1{72}=\tfrac{25}{108}\).

**4 (COMPUTATIONALLY VERIFIED, OBSERVATION).** The table and the window fit above;
the density corollary as an observation with the stated excess.

**5 (Impact on Paper C).** Three items.

*The exceptional set is about 29 times wider than it needs to be.* Lemma 4.2's
symmetric window \(\|\alpha_m\|<22m^{-1/3}\) has width \(44m^{-1/3}\); the extremes
live in \(\alpha_m\in[-1.25,0.25]\,m^{-1/3}\), width \(1.5m^{-1/3}\), asymmetric
because the curvature is one-signed. Lemma 4.3's constants \(63\) and \(306\) shrink
with it. Harmless slack, since the term is \(o(1)\) either way; the sharp figure
replaces a guess.

*The parked remainder lift is a named hypothesis.* The remainder-set production runs
at coefficient \(\tfrac29\) where the ideal is \(\tfrac13\), and the record parks the
lift. Since the \(\theta\)-average of \(S\) is \(\tfrac12\) for every \(\beta\), the lift
holds if and only if the landing phase \(\theta_m\) equidistributes along the remainder
set conditionally on \(\beta_m\). That is a depth-two fairness statement on a
backward-closed set, of the kind already priced at the frontier; no fiber-local lemma
can supply it, and the empty fibers do not obstruct it. Lemma 4.1' is essentially
sharp as printed, its \(\tfrac13\) coming from the resonance \(\alpha_m\approx\tfrac13\),
which has positive density and cannot be discarded.

*The cube family is a standing caution.* Any construction selecting targets from a
thin arithmetic set must not treat the fiber as a coin.

Paper C's manuscript is not edited here. The edits it would take are one constant in
Lemma 4.2 and one sentence at the remainder lift.

## Open questions

- The systematic excess of observed empty fibers over \(25/108\) per fiber length:
  discreteness at \(1/2H\), or correlation between \(\beta_m\) and \(\theta_m\)?
- Equidistribution of \(\theta_m\) along the remainder set, which is the lift.
- The general even-square version: above every even perfect square \(s^2\) the nested
  floor is \(s^3+\tfrac32st\) for \(t<1.63\sqrt s\), a monochrome run longer than a
  fiber; the fiber is fully covered only when \(s^{3/2}\) is nearly an integer from
  above, which is what makes cubes exact. Whether that gives a second exact family is
  not examined.

## Decision

**PROMOTE.** An exact theorem in Lean, a share law that explains the whole phenomenon
with three corollaries, a 29-fold sharpening of a printed exceptional set, and a
parked item converted into a named hypothesis. It belongs in Paper C as a constant
and a remark, which is the Paper C owner's edit.

Best next question: does \(\theta_m\) equidistribute along the remainder set, or can
the remainder set be shown to carry no correlation with the landing phase at all?

## Publication assessment

Status: `THEOREM`. The cube theorem is a clean, self-contained elementary result and
would sit naturally as a lemma in Paper C's Section 4, next to Lemma 4.2, with the
share law as the remark that explains why the block average of Proposition 4.4 is
exactly a half. Not a paper on its own.
