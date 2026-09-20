# Juggler OE rest average: \(1/3\) versus \(1/2\) on \(A^{\mathrm{rest}}\)

Status: **PROMOTE** (unparked 19 September 2026: the missing lemma is
proved, and the averaging question is answered for every \(A\) at once)

Proof:
[juggler_oe_poor_fiber_tail_note.md](../theory/juggler_oe_poor_fiber_tail_note.md).

Child of [juggler_oe_fiber_constant.md](juggler_oe_fiber_constant.md)
and [juggler_fate_contagion.md](juggler_fate_contagion.md). Not a new
production, not a halt theorem, and it does not touch \(\psi_F\).


> **Superseded in approach, 2026-09-20.** The branch
> `claude/latest-progress-summary-s011un` answers this question by a route
> needing almost none of the machinery below. Its observation: \(P\) has
> **finite total logarithmic mass** (verified here — density \(\sim m^{-1/3}\),
> sum \(\approx 1.3\)), so there is nothing to plant, the fraction vanishes for
> *every* set of integers, and no backward closure is required. Its decay proof
> is one inequality at every convergent denominator,
> \(|G_m/H_m-\tfrac12|\le 4\|q\alpha_m\|+\tfrac5{2q}+3.77q/H_m\), with no
> exponential sum. The measurements below stand; the framing and the assembled
> chain answer a question that dissolves. Merging is Philippe's call and takes
> the whole branch or none.

## Problem

Pairing gives a uniform per-fiber even-share \(\ge 1/3-O(1/H)\), hence
\(\lambda^{**}=0.4480\). The depth-two ceiling \(0.4927\) is the
ideal-fiber equation, which needs even-share \(1/2\) on
\(A^{\mathrm{rest}}\). Can that average be forced for every
backward-closed \(A\)?

## Exact statement

**Observation (COMPUTATIONALLY VERIFIED).** Let \(P\) be the set of
\(m\) with exact even-share \(G_m/H_m\le 0.40\). Then:

1. \(P\) has log-mass fraction \(\ge 0.059\) on every dyadic block
   checked in \([2^8,2^{16}]\). **Corrected 2026-09-19:** the original
   parenthetical here read "(not \(O(U^{-1/3})\))", and that is an
   artifact of stopping at \(2^{16}\), where \(H_m\le 27\) and
   binomial noise alone predicts about \(14\%\). Carried four more
   octaves the \(1/m\)-weighted fraction falls \(0.0508\to 0.0072\)
   from \(2^{16}\) to \(2^{24}\), a factor \(7.1\) against the
   cube-root prediction \(6.35\)
   (`oe_fiber_constant.poor_fiber_decay`). The decay is consistent with
   \(O(U^{-1/3})\). This does **not** unpark the branch: the PARK rests
   on observations (2)-(4), and the quantity Theorem 5.3 needs is
   poor-set mass relative to \(A\), not to all integers, so an
   adversarial backward-closed \(A\) is untouched.
2. The \(E{+}OE\) closure of a *capped* \(P\cap[1,3000]\) has odd
   members above the cap with weighted even-share \(0.515\) (low-even
   fraction \(0.06\)): a fixed seed set mixes.
3. The \(E{+}OE\) closure of *all* of \(P\) up to \(8\cdot 10^4\) has
   odd-member even-share rising \(0.25\to 0.41\) from \(2^8\) to
   \(2^{16}\), with low-even fraction falling \(1.00\to 0.37\):
   infinite planting drowns slowly and has no closed coefficient.
4. The thick control (closure of \([1,260]\)) has rest even-share
   \(0.44\)–\(0.50\).

There is no pairing-style lemma that writes \(1/2\) into (4.2)
uniformly in \(A\). The ideal root is not a theorem of the same kind.

**Interpretation.** The gap \(0.448\to 0.4927\) is no longer a
pointwise fiber problem (pairing closed that door at \(1/3\), and
\(\alpha_m\) is dense at \(1/3\)). If it is attacked at all, it is
by a dynamical averaging theorem for the low-even set \(P\): the
\(E{+}OE\) orbit of \(P\) has even-share \(1/2-o(1)\). That is not
opened here.

**Superseded 19 September 2026.** The dynamical theorem is not needed,
because \(P\) is too small to require one. See the next section.

## The theorem that unparks this

**Theorem (poor-fiber tail; EXACT — HUMAN PROOF).** For
\(\eta_0\in(0,\tfrac12]\) put
\(P_{\eta_0}=\{m:|G_m/H_m-\tfrac12|\ge\eta_0\}\). There is
\(u_0(\eta_0)=\max(10^6,(1950/\eta_0^2)^3)\) with
\[
\#\bigl(P_{\eta_0}\cap(u,2u]\bigr)\le\frac{430}{\eta_0^2}u^{2/3}
\quad(u\ge u_0),
\qquad
\sum_{m\in P_{\eta_0},\,m>U}\frac1m\le\frac{2100}{\eta_0^2}U^{-1/3}
\quad(U\ge u_0).
\]

Three steps, all elementary, none using an exponential sum:

1. **Block lock.** For every convergent denominator \(q\) of
   \(\alpha_m=\{\tfrac32m^{2/3}\}\),
   \(|G_m/H_m-\tfrac12|\le 4\|q\alpha_m\|+\tfrac5{2q}+3.77q/H_m\).
   Cut the fiber into blocks of \(q\) consecutive members; each is a
   translate of the \(1/q\)-grid perturbed by
   \(\|q\alpha_m\|+q\eta_m\), and a \(1/q\)-grid splits a
   half-circle within \(\tfrac12\) of evenly.
2. **Lock.** Contrapositive at the largest convergent denominator below
   \(\eta_0H_m/16\): a deviation \(\ge\eta_0\) forces
   \(q\le3.77/\eta_0\) with \(\|q\alpha_m\|\le32/(\eta_0H_m)\).
3. **Arc count.** Lemma 4.3 with its two goodness arcs replaced by the
   \(\tfrac{Q(Q+1)}2\) arcs of total length \(2Q\delta\); the count
   over \((u,2u]\) is \((0.882u^{2/3}+2)(2Q\delta(2u)^{1/3}+\tfrac{Q(Q+1)}2)\).

**Corollary.** For every set \(S\subseteq(V,\infty)\) whatever --- no
backward closure, no structure ---
\(\sum_{m\in S}\tfrac1m\tfrac{G_m}{H_m}\ge(\tfrac12-\eta_0)\sum_{m\in S}\tfrac1m-1050\eta_0^{-2}V^{-1/3}\).

**Why this kills the obstruction rather than dodging it.** The PARK
rested on the poor set's mass *relative to \(A\)*, which observations
(2)--(4) could not control. The theorem makes that quantity irrelevant:
\(P_{\eta_0}\) has finite total logarithmic mass, so there is nothing
for an adversary to concentrate on, whatever \(A\) is. Observations
(2)--(4) stand as measurements and were never wrong; they were taken at
\(2^{16}\), where the density of \(P\) is still \(\approx0.37\)
because \(420\eta_0^{-2}u^{-1/3}\) has not begun to bite.

## Current literature

- Pairing \(H/3-2\) (`extended` as the uniform floor; this branch is
  the leftover average).
- Prop. 3.4 block average \(1/2\) (`known`): applies to even blocks,
  not to an arbitrary rest.
- Paper C §5.6 (`reproduced`): the ceiling \(0.4927\) needs uniform
  \(c=1/2\).

## Branch budget

```text
Mathematical target     For every backward-closed A, is the 1/m-weighted
                        even-share on A^rest equal to 1/2 − o(1)?
Novelty hypothesis      E-trees of poor seeds inject block-average 1/2
                        into later rest and drown a one-sided P.
Falsifier               Closure of all low-even m keeps rest even-share
                        ≤ 1/3+δ at definite log-mass.
Existing machinery      certified_closure, fiber_stats, pairing, Prop. 3.4.
Maximum Phase-0 scope   Poor-set log-mass, closure-of-P, capped-seed
                        descendants, thick control. No Paper C rewrite.
Promotion criterion     Human-proof 1/2−o(1) uniformly in A; root moves.
Stop criterion          Intermediate coefficient, or a constant hunt.
```

Reopened 19 September 2026, against the corrected pricing:

```text
Mathematical target     For every fixed eta>0, is #{m in (u,2u] :
                        |G_m/H_m - 1/2| >= eta} << u^{2/3}?
Novelty hypothesis      Low share forces a small-denominator resonance in
                        alpha_m at width O(1/H_m); Lemma 4.3 already counts
                        exactly that, for q <= 2 only.
Falsifier               A low-share fibre with no resonance q <= Q(eta)
                        inside C(eta)/H_m; or the block-lock inequality
                        failing at any convergent denominator.
Already killed by?      No. negative_knowledge.md kills averaging as a route
                        to bounded-m CYCLE exclusion, an extreme-value
                        problem; this is the contagion recursion's fibre
                        share, an average problem. Different target.
Existing machinery      Lemma 4.1', 4.2, 4.3 and FiberParity.arc_count_le;
                        Lemma 4.5 share law; alpha_star; fiber_stats.
Maximum Phase-0 scope   Prove the three lemmas, verify each as a falsifier,
                        derive the tail and the two-production root. No
                        Paper C rewrite -- that manuscript is claimed.
Promotion criterion     The tail bound, uniform in A, with a two-production
                        root above 0.492572.
Stop criterion          The lock lemma needing Erdos-Turan or any
                        exponential sum: then it is a wash, because
                        Proposition 4.4 is back on the critical path.
```

The stop criterion did not bind. The lock lemma is continued fractions
and counting; no exponential sum appears anywhere in the note.

## Balanced-ternary formulation

None. The objects are odd members of a backward-closed set and the
even-share of \(\lfloor n^{3/2}\rfloor\) on their OE fibers.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Block lock (1.1), the inequality carrying the whole proof —
  **EXACT — HUMAN PROOF**.
- Poor-fiber tail \(O(U^{-1/3})\), uniform in \(A\) —
  **EXACT — HUMAN PROOF**.
- Arc count past \(q=2\) — **EXACT — HUMAN PROOF** (Lemma 4.3 generalized).
- Poor-set density \(\asymp u^{-1/3}\) from below —
  **COMPUTATIONALLY VERIFIED** (\(1.4\) to \(2.1\) times \(u^{-1/3}\)
  over \([10^5,10^8]\)).
- One-sided low-even set \(P\) — **COMPUTATIONALLY VERIFIED**.
- Capped-seed mixing to \(1/2\) — **COMPUTATIONALLY VERIFIED**.
- Infinite-planting even-share \(0.25\to 0.41\) — **OBSERVATION**
  (pre-asymptotic, now explained).
- Ideal root \(0.4927\) — **KNOWN**, and now the supremum of what two
  productions reach.

## Experiments

- Probe: `research.juggler_sequence.oe_rest_average`.
- Artifact: `data/research/juggler/oe_rest_average/summary.json`.
- Tests: `tests/research/juggler_sequence/test_oe_rest_average.py`.

## Conjectures

None opened.

## Counterexamples

The \(E{+}OE\) closure of all \(m\) with \(G_m/H_m\le 0.40\) is a
backward-closed set whose rest even-share is \(0.41\) at \(2^{16}\),
not \(1/2\). A finite check is not an asymptotic refutation of
drowning; it kills a pairing-style uniform rewrite of (4.2).

## Formalization

**Done and kernel-checked, standard axioms throughout**: Lemma 1
(`BlockLock.block_lock`), Lemma 2 (`FiberParity.fiber_lock`), Lemma 3
(`FiberParity.resonance_count_le'`), Theorem 4 both halves
(`poor_count_le'`, `poor_logMass_le`), and §5's family bound
(`family_OE_averaged`). Five modules: `FateBlockLock`, `FateFiberLock`,
`FateResonanceCount`, `FatePoorTail`, `FatePoorProduction`.

**And the recursion, at an exponent above the published one.**
`production_two_averaged` is the production inequality at
\((2/3)(1/2-\eta_0)\), with `production_two`'s shell geometry inlined and
one new hypothesis \(hT:3(1280/\eta_0^2+1)\le e^{t/8}\) --- Lemma 2's two
block conditions rewritten at \(U=\lfloor e^{3t/8}\rfloor\), which is the
whole cost of averaging and shows up only as \(t_1\approx250\).
`contagion_averaged` runs `recursion_lemma`, which was already generic, so
Lemma 5.1 is not restated; it is parametric in \(\lambda\) and
\(\eta_0\) with \(\zeta>0\) as a hypothesis, which is the shape the
mathematics has. `zeta2avg_pos` is a separate arithmetic certificate at
\(\lambda=100/203=0.4926108\), \(\eta_0=10^{-5}\), chosen for margin
rather than minimality: \(67/136\) also lies in
\((\lambda^{**},\lambda_{\rm ideal})\) with the smaller denominator but a
fifth of the \(\zeta\)-slack, which `exponent_certificate` re-derives in
exact arithmetic. So `logMass_contagion_averaged` is Theorem 5.3 above
\(\lambda^{**}\), unconditionally, and
`conjecture_of_tao_rate_averaged` puts the unconditional Tao threshold at
\(e>103/203=0.50739\), below Paper C's *conditional* \(0.51\).

`FateProduction.lean` is not edited: it is pinned by Paper C's release
manifest, and its \(2/9\) chain is what the manuscript cites. An earlier
pass stopped here, declining to inline `production_two`'s geometry on
anti-duplication grounds. **That was overstated**, and the correction is
worth keeping: formalpedia's habit exists to stop two *named declarations*
stating one fact, because that splits a citation; inlined proof steps inside
one proof cost maintenance and create no ambiguous citation target. The two
are different defects and only the first justifies a recorded gap.

## Results

- Classification `OE_REST_AVERAGE_PROVED` (the closure census keeps its
  own `OE_REST_AVERAGE_MIXED` under `closure_classification`; both are
  true and they answer different questions).
- Block lock verified at every convergent denominator \(q\le H_m\) over
  four windows at \(10^6,10^7,10^8,10^9\); least slack \(0.233\), and
  \(\eta_mH_m\le0.6834\) against the \(0.6903\) the constant
  \(3.77\) is built on.
- Every fiber with share \(\le0.40\) locks: \(q\in\{1,3,5\}\) at
  \(10^6\), \(\{1,3\}\) at \(10^7\), \(\{1\}\) at \(10^8\),
  with resonance \(\|q\alpha_m\|H_m\le1.99\) throughout. \(q=1\) is
  the extreme family of Corollary 4.6, \(q=3\) the attaining witnesses
  of the pairing third.
- Arc count holds at nine \((u,Q,\delta)\) combinations, ratio at most
  \(0.882\) --- tight at \(Q=1\), as the leading term predicts.
- Two productions reach every \(\lambda<0.4926580\); the break-even
  against the published \(\lambda^{**}=0.4925715\) is
  \(\eta_0=8.60\times10^{-5}\).
- Child-phase \(\{(3/2)m^{8/9}\}\) on low-even parents is uniform
  (total variation \(0.046\) on \([3000,8000]\)).
- Not a halt theorem. No floor moves, no cycle is excluded.

## Open questions

A dynamical averaging theorem for \(P\) is **no longer wanted**: the
theorem makes \(P\) too small for the dynamics to matter. What is open,
in descending order of value:

1. **Constants, and what they cost.** Done: Theorem 5.3 is Lean end to end
   at \(\lambda=100/203>\lambda^{**}\), which it had never been. What is
   left is that \(430\) and \(2100\) are crude, so see (2).
2. **Sharpening.** \(430\) and \(2100\) are crude by a large factor, and
   \(u_0(\eta_0)=(1950/\eta_0^2)^3\) is what makes \(t_1\approx221\)
   at the \(\eta_0\) that matters. Sharpening \(\theta\) in Lemma 2
   and the grid-boundary count in Lemma 1 is routine and would bring
   \(u_0\) down by many orders.
3. **Depth three.** The two-production ceiling is now reached, so the
   ceiling on the *method* is what binds, exactly as
   `J-paper-c-ladder-recovers-the-depth-two-ceiling` says. Going past
   \(0.4927\) needs a third production, not a better constant.

Another pointwise fiber bound is still the wrong door. Two-way closed
fate classes are a different question and are not opened.

## The averaging chain, assembled

Written 2026-09-19. Both halves of the bootstrap now stand at once for the
first time, so the chain is set out here in one place with each link's status
rather than spread across eight commit messages. **This does not unpark the
branch** -- see the soft spots below, and the PARK is a judgement for Philippe.

**The claim.** For every nonempty backward-closed \(A\) and every fixed
\(\delta>0\), the fraction of \(A\)'s \(1/m\)-weight at scale \(x\) carried by
fibres with \(\lvert\sigma_m-\tfrac12\rvert\ge\delta\) is
\(O_\delta(x^{-1/3})\).

| # | link | status |
|---|---|---|
| 1 | \(A\) backward-closed \(\Rightarrow\) \(A\) is a union of COMPLETE fibres over its own elements | Paper C Lemma 2.1, **Lean** |
| 2 | low share \(\Rightarrow\) resonant at order \(\le K(\delta)\) | \(\delta\ge 1/6\): Paper C Lemma 4.2, **Lean**. \(\delta<1/6\): `J-low-share-forces-a-small-order-resonance`, **proved but vacuous below \(m\sim 10^{15}\)** |
| 3 | the resonant set at order \(\le K\) has measure \(O_\delta(m^{-1/3})\) | proved; the interval count is \(\Theta(K^2)\) not \(O(K)\), which the exponent survives |
| 4 | every production fibre equidistributes \(\alpha\) | proved: \(\theta_w=2^{a+b+1}/3^{b+1}\) is never an integer, because \(3\nmid 2^k\) |
| 5 | the two routes' rates combine | **both provably marginal** at \(x^{-1/3}\), which suffices. E route by an elementary crossing count, OE route by van der Corput |

**End to end, on the hardest \(A\) available** -- the closure of the
*non-resonant* seeds, built specifically to avoid resonance. Low-share weight
fraction at \(\delta=0.10\), times \(x^{1/3}\):

| block | \(\lvert A\cap\text{blk}\rvert\) | low-share wt frac | \(\times x^{1/3}\) |
|---|---|---|---|
| \(2^{13}\) | 287 | 0.17587 | 4.058 |
| \(2^{14}\) | 560 | 0.13811 | 4.015 |
| \(2^{17}\) | 646 | 0.06304 | 3.665 |
| \(2^{18}\) | 352 | 0.05997 | 3.929 |

Flat. The low-share fraction is bounded by the resonant fraction at every
block, as link 2 requires.

**The soft spots, which are why this is not a closed branch.**

1. Link 2 is *vacuous* at every reachable \(m\). Its numerical support
   confirms a sharper constant-free phenomenon that the theorem does not
   reach. A Selberg--Vaaler majorant would buy about \(60\times\); not done.
2. Link 5's E-route rate is measured, not proved. The OE route is proved and
   marginal, and marginal suffices -- but the *combination* has not been
   written with one set of constants.
3. Nothing here is Lean beyond links 1 and 2's easy half.
4. The bootstrap this feeds also needs the contagion exponent it improves.
   That circularity is benign in the strong sense -- the input is a polylog
   lower bound on \(A\)'s weight and the output a polynomial separation, so
   any positive \(\lambda_0\) serves, there is no fixed point and no
   iteration. **But the crossover is at \(y\sim 3.5\times10^{10}\):** at
   \(y=2^{14},2^{16},2^{18}\) the capacity \(12y^{-1/6}\) is 2.38, 1.89,
   1.50 against \(A\)'s weight 0.175, 0.202, 0.206, so the comparison runs
   the wrong way by 7 to 14 times at every reachable scale.
5. **Every link has that character.** The assembly's crossovers sit between
   \(10^{10}\) and \(10^{20}\), so none of the chain can be corroborated
   numerically. What the measurements confirm throughout is a sharper,
   constant-free phenomenon that the proofs do not reach. That is the
   honest summary of its status, and the reason the PARK is defensible even
   with both halves standing.

**What it would buy, unchanged since the pricing.** Two productions at the mean
share reach \(\lambda^{**}\), taking Proposition 4.4's two exponential-sum
bounds off Paper C's critical path -- the largest unformalized gap in the
paper. Not a better exponent; the same one with the analytic core removed.

**The assembled constant, written once.** All at the element scale \(x\),
with \(K=\lceil 2C_{ET}/\delta\rceil\) and \(\gamma H^2\to 1/3\),
\(H=\tfrac23 x^{1/3}\):

\[
\text{low-share fraction}\;\le\;
\Bigl(\underbrace{\pi C_{ET}K^2\log(eK)/\delta}_{\text{resonant measure}}
\;+\;\underbrace{0.27\cdot(3/\pi^2)K^2}_{\text{OE discrepancy}}\Bigr)x^{-1/3}.
\]

| \(C_{ET}\) | \(\delta\) | \(K\) | constant | bound \(<1\) from |
|---|---|---|---|---|
| 1 | 0.100 | 20 | \(5.0\times10^{4}\) | \(x=1.3\times10^{14}\) |
| 1 | 1/6 | 12 | \(9.5\times10^{3}\) | \(x=8.5\times10^{11}\) |
| 4 | 0.100 | 80 | \(4.3\times10^{6}\) | \(x=8.1\times10^{19}\) |
| 4 | 1/6 | 48 | \(8.5\times10^{5}\) | \(x=6.1\times10^{17}\) |

Measured constant on the adversarial \(A\) at \(\delta=0.10\): about \(3.9\).
So the bound is loose by \(10^{6}\), and the crossover range \(10^{12}\) to
\(10^{20}\) is exactly the span quoted above.

**One thing this settles.** The Erdős--Turán term is \(99.988\%\) of the
constant and the OE discrepancy term is \(0.012\%\) -- a ratio of \(8241\) to
\(1\) at \(C_{ET}=4,\ \delta=0.10\). So the marginality of the OE route, which
looked like the binding difficulty, contributes one part in eight thousand.
Sharpening the discrepancy buys nothing; only the Erdős--Turán constant is
worth attacking, and Selberg--Vaaler is the way (it removes \(C_{ET}\) from
\(K\), so it enters the constant cubed).

**Selberg--Vaaler, computed rather than left as a note.** Since \(C_{ET}\)
enters cubed it is the only lever worth pulling, and the Vaaler majorant for a
single fixed interval carries an explicit coefficient \(1\) on \(1/(K+1)\), so
\(K=\lceil 2/\delta\rceil-1\) with no \(C_{ET}\) in it:

| \(\delta\) | route | \(K\) | constant | crossover |
|---|---|---|---|---|
| 0.100 | Erdős--Turán, \(C_{ET}=4\) | 80 | \(4.4\times10^{6}\) | \(8.7\times10^{19}\) |
| 0.100 | **Selberg--Vaaler** | 19 | \(5.2\times10^{4}\) | \(1.4\times10^{14}\) |
| 1/6 | Erdős--Turán, \(C_{ET}=4\) | 48 | \(8.8\times10^{5}\) | \(6.8\times10^{17}\) |
| 1/6 | **Selberg--Vaaler** | 11 | \(1.0\times10^{4}\) | \(1.0\times10^{12}\) |

**\(85\times\) on the constant, \(6\times10^{5}\) on the crossover** at the
standard \(C_{ET}=4\). But at \(C_{ET}=1\) the Erdős--Turán route is already
within \(1.1\times\), so what Selberg--Vaaler actually buys is *not having to
know \(C_{ET}\)* -- it is not intrinsically sharper. Anyone who pins a citation
giving \(C_{ET}=1\) gets the same thing without changing the argument.

Two caveats kept with it. The Vaaler form used here is the one the adversarial
pass reported and is **not verified against a source**; it needs a citation
with a page number before the constant is quoted anywhere else. And
\(\delta\ge 1/6\) is Paper C Lemma 4.2 already, in Lean and \(37\times\)
sharper, so the only range where any of this is the best available is
\(\delta<1/6\), where the crossover is \(\ge 1.4\times10^{14}\).

**Link 5 no longer needs a measurement.** It was recorded as "E route error
\(\ll\) density (measured), OE route marginal (proved)". Both are provably
marginal by arguments of the same shape, and marginal suffices.

Within the E-block of \(m\) the phase \(\alpha(n)=\{\tfrac32 n^{2/3}\}\) is
monotone with increment \(\sim m^{-2/3}\), sweeping \(T=2m^{1/3}\) turns over
\(N\approx m\) even points. For a target that is a union of \(K\) intervals,
each of the \(2K\) boundaries is crossed \(T\) times and each crossing
miscounts at most one point, so

\[
\bigl|\,\#\{n:\alpha(n)\in S\}-N|S|\,\bigr|\;\le\;2KT,
\qquad\text{relative error}\;\le\;\frac{2KT}{N}=4Km^{-2/3}.
\]

Against a resonant density of about \(9m^{-2/3}\) that is a ratio of
\(4K/9=1.33\) at \(K=3\): marginal, exactly like the OE route, and by the same
reasoning harmless. Checked at \(m=300,10^3,3\cdot10^3,10^4\), where the bound
\(0.268, 0.120, 0.058, 0.026\) holds against measured errors
\(9.5\times10^{-4}, 3.2\times10^{-4}, 4.9\times10^{-5}, 4.3\times10^{-5}\).

The measured \(m^{-0.6}\) relative error on the E side is real and much better
than the bound, but it is now a bonus rather than a load-bearing input. Link 5
rests on two elementary arguments and nothing measured.

**The crossover is not one number — it is \(\delta^{-9}\), and that changes
what the route is worth.** The chain proves \(O_\delta(x^{-1/3})\) for FIXED
\(\delta\), with constant \(\sim\pi K^2\log(eK)/\delta\) and \(K\sim 2/\delta\),
so the constant goes like \(\delta^{-3}\) and the crossover like
\(\delta^{-9}\). But the bootstrap needs \(\delta\to 0\) to push the effective
share to \(1/2\). Pricing the two together:

| target two-production root | needed share | \(\delta\) | crossover \(x\) |
|---|---|---|---|
| \(0.326121\) (today, unconditional) | \(0.3333\) | \(1.7\times10^{-1}\) | \(1.0\times10^{12}\) |
| \(0.400\) | \(0.4075\) | \(9.3\times10^{-2}\) | \(3.3\times10^{14}\) |
| \(0.450\) | \(0.4575\) | \(4.3\times10^{-2}\) | \(5.4\times10^{17}\) |
| \(0.4926=\lambda^{**}\) | \(0.499942\) | \(5.8\times10^{-5}\) | \(2.0\times10^{44}\) |
| \(0.492658=\lambda_{\text{ideal}}\) | \(1/2\) | \(0\) | **unreachable at any \(x\)** |

Fitted, \(x\approx 10^{5}\delta^{-9}\).

**This deflates the headline claim, including as this dossier has repeatedly
stated it.** "Two productions at the mean share reach \(\lambda^{**}\), taking
Proposition 4.4's exponential sums off the critical path" is true as a
statement about coefficients and false as a statement about anything
achievable: it needs \(x\sim10^{44}\). The crossover of \(1.4\times10^{14}\)
quoted earlier corresponds to buying a root of about \(0.40\) — real, and well
short of \(\lambda^{**}\). And the ideal root is not approached slowly, it is
not attained at all, because it requires \(\delta=0\) exactly.

What the route honestly buys is an asymptotic: for every \(\theta<1/2\) the
effective share exceeds \(\theta\) eventually, with "eventually" growing like
\((1/2-\theta)^{-9}\). That is a genuine theorem and it is not a route to
\(\lambda^{**}\) at any scale a person or a computer will meet.

## Decision

**PROMOTE.** The averaging question is answered, and not by averaging.
The obstruction the PARK recorded --- "an intermediate coefficient with
no lemma" --- turned out to be an artifact of asking for the wrong
theorem: nobody needs to show that \(A\)'s orbit mixes, because the set
it would have to mix away has finite total logarithmic mass. Three
elementary lemmas, no exponential sum, and the conclusion holds for every
set of integers whatever.

What this is worth, priced as the reopening budget required: the
two-production inequality now reaches every \(\lambda<0.4926580\),
above the published \(\lambda^{**}=0.4925715\). The gain in the number
is \(8.6\times10^{-5}\) and is not the point. The point is which
machinery the number stops needing:

- **Proposition 4.4 leaves the critical path**, with its two
  exponential-sum bounds --- Vaaler, the second-derivative test,
  Kusmin--Landau --- which are Paper C's largest unformalized gap.
- **The six-word ladder and Appendix D leave it**, since two productions
  now pass where six stopped.
- **Lemmas 4.1, 4.1' and 4.2 leave it too**, as statements: the new
  argument needs no goodness hypothesis and no pointwise floor, because a
  fiber that would have been called bad is just a member of
  \(P_{\eta_0}\). One step of Lemma 4.2's proof is retained --- the step
  interval \([A_m,B_m]\), which is where \(\alpha_m\) and \(\eta_m\)
  come from --- but the sweep lemmas themselves are not used.

Three things this is not. It is not a better exponent in any sense that
matters (\(8.6\times10^{-5}\)). It is not a halt theorem, and Theorem
7.2 stays conditional. And it does not attain \(0.4926580\): \(\eta_0\)
is fixed before \(x\), so the supremum is approached, which is the shape
the published statement already has.

The earlier re-pricing on this line stands as written and was the reason
to reopen: the prize was never a better number, it was the same number
with the analytic core removed. That is what was collected.

**Paper C is not edited here.** The manuscript is claimed by another
session; this branch records the theorem and the consequence, and the
rewrite of §5.1--5.2 is theirs to take or leave.

## Publication assessment

Status: `PUBLISHABLE` as a section of the fate note, replacing §5.1
item 2 and simplifying §5.2, at the holding session's discretion. The
census remains a remark. Not a halt theorem.
