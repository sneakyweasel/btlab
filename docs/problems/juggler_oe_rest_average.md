# Juggler OE rest average: \(1/3\) versus \(1/2\) on \(A^{\mathrm{rest}}\)

Status: **PROMOTE** (unparked 19 September 2026: the missing lemma is
proved, and the averaging question is answered for every \(A\) at once)

Proof:
[juggler_oe_poor_fiber_tail_note.md](../theory/juggler_oe_poor_fiber_tail_note.md).

Child of [juggler_oe_fiber_constant.md](juggler_oe_fiber_constant.md)
and [juggler_fate_contagion.md](juggler_fate_contagion.md). Not a new
production, not a halt theorem, and it does not touch \(\psi_F\).

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

**Not done**: the recursion. `recursion_lemma` is generic and needs
nothing; `production_two` is stated against the literal `2/9`. Its
geometry half is coefficient-free and should be factored out and shared,
but `FateProduction.lean` is pinned by Paper C's release manifest, so
adding even a lemma to it needs a manuscript rebuild this container
cannot do. Copying the geometry instead was declined: it would give the
same facts two names in one layer. The gap is environmental, and the
note's Formalization section says what a session with a Paper C build
should do.

Superseded planning text follows.

None yet, and the note names the order: the arc count first
(`FiberParity.bad_count_le` with a union over \(q\le Q\) in place of the
two goodness arcs, no new idea), then the block lock, which is the only
genuinely new Lean work, then the tail as arithmetic. Nothing needs
`native_decide`. `FateContagion.lean` stays the exact layer. No `sorry`.

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

1. **Lean.** The three lemmas, in the order the note gives. The arc count
   is a generalization of an existing Lean proof; the block lock is new.
   This is the item that would let Theorem 5.3 be Lean end to end at an
   exponent above \(0.4926\), which it has never been.
2. **Constants.** \(430\) and \(2100\) are crude by a large factor, and
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
