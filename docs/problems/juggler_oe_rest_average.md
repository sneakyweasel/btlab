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
