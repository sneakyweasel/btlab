# Juggler OE rest average: \(1/3\) versus \(1/2\) on \(A^{\mathrm{rest}}\)

Status: **PARK** (drowning is real for a fixed seed; infinite planting
has no clean coefficient)

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

## Balanced-ternary formulation

None. The objects are odd members of a backward-closed set and the
even-share of \(\lfloor n^{3/2}\rfloor\) on their OE fibers.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- One-sided low-even set \(P\) — **COMPUTATIONALLY VERIFIED**.
- Capped-seed mixing to \(1/2\) — **COMPUTATIONALLY VERIFIED**.
- Infinite-planting even-share \(0.25\to 0.41\) — **OBSERVATION**.
- Ideal root \(0.4927\) — **KNOWN** (not reached).

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

None. `FateContagion.lean` stays the exact layer. No `sorry`.

## Results

- Classification `OE_REST_AVERAGE_MIXED`.
- Child-phase \(\{(3/2)m^{8/9}\}\) on low-even parents is uniform
  (total variation \(0.046\) on \([3000,8000]\)).
- \(\lambda^{**}\) stays \(0.4480\). Not a halt theorem.

## Open questions

A dynamical averaging theorem for \(P\) (even-share \(1/2-o(1)\) along
the \(E{+}OE\) orbit). Not opened. Another pointwise fiber bound is
the wrong door. Two-way closed fate classes are a different question
and are not opened.

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
| 5 | the two routes' rates combine | E route error \(\ll\) density (measured \(\sim m^{-0.6}\) relative); OE route marginal at \(x^{-1/3}\), which suffices |

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

## Decision

**PARK.** A fixed seed set mixes to \(1/2\); planting low-even
\(m\) at every scale leaves an intermediate coefficient with no lemma.
The gap \(0.448\to 0.4927\) is now read as a dynamical averaging
problem for \(P\), not as a missing pointwise fiber bound.

**Re-priced 2026-09-19; the PARK stands but "none on this line" is now
arguable.** The park was weighed against the prize "a better exponent",
and on that measure it was right --
`J-paper-c-ladder-recovers-the-depth-two-ceiling` shows the ladder has
already banked all but \(8.6\times10^{-5}\) of it, and
`J-oe-fiber-pairing-third-is-attained` shows the pointwise \(1/3\) cannot
be improved. But the two-production inequality is the whole
unconditional chain and its root moves steeply in the OE coefficient
(`oe_rest_average.averaging_payoff`):

| \(c\) | share | two-production root |
|---|---|---|
| \(2/9=0.222222\) | \(1/3\) | \(0.326121\) (pointwise-sharp) |
| \(0.300000\) | \(0.450\) | \(0.442499\) |
| \(0.320000\) | \(0.480\) | \(0.472576\) |
| \(1/3=0.333333\) | \(1/2\) | \(0.492658\) |

The coefficient matching \(\lambda^{**}=0.492572\) on two productions
alone is \(0.3332760\), a share of \(0.4999140\) -- essentially the mean.
So an averaged argument delivering the mean would reach the headline
exponent with two productions, making the block-average family and the
six-word ladder unnecessary for it, and taking **Proposition 4.4's two
exponential-sum bounds off the critical path**. Those are Paper C's
analytic core, absent from `formal/`, and its largest unformalized gap.
The prize is therefore not a better number but the same number with the
analytic core removed -- a different kind of prize from the one weighed
here.

**What still vindicates the PARK: the target is narrow.** Break-even
against the three-production base \(0.448017\), which the block average
already gives, is \(c=0.3036722\), a share of \(0.4555\). An averaged
argument landing below that share is a *regression*, not progress, and it
must reach \(0.4999\) to match \(\lambda^{**}\). Recovering "better than
the worst case" is worth nothing here; only "essentially the mean" pays,
and that is exactly what observation (3)'s slow drowning fails to give.

Quantification contributed by a peer session; reproduced and guarded in
`test_oe_rest_average.py`.

## Publication assessment

Status: `EXPLORATORY`. The census belongs in a remark of the fate
note, not as a new theorem. Not a halt theorem.
