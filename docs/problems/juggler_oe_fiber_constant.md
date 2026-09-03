# Juggler OE-fiber constant: monotone pairing \(1/7\to 1/3\)

Status: **PROMOTE** (Lemma 3.1′; \(\lambda^{**}=0.4480\))

Child of [juggler_fate_contagion.md](juggler_fate_contagion.md). Not a new
production, not Appendix C, not a halt theorem, and it does not touch
\(\psi_F\).

## Problem

Replace the adversarial sweep constant \(1/7\) on a good OE fiber by a
constant near \(1/3\), the observed floor at \(\alpha_m\approx\tfrac13\).

## Exact statement

**Lemma 3.1′ (EXACT — HUMAN PROOF).** If \(x_1<\dots<x_H\) have monotone
steps in \([a,b]\), \(0<a\le b\le\tfrac12\), \(b\le\tfrac{21}{20}a\),
and \((H-1)a\ge 12\), then both half-interval counts are at least
\(H/3-2\).

**Lemma 3.2 (updated).** On a good fiber \(m\ge 10^6\),
\(G_m\ge\tfrac13 H_m-2\) and \(H_m-G_m\ge\tfrac13 H_m-2\).

**Theorem 4.2 (updated).** \(\lambda^{**}=0.4480\ldots\) is the root of
\(2^{-\lambda}+\tfrac19(\tfrac38)^\lambda+\tfrac29(\tfrac34)^\lambda=1\).

The abstract Lemma 3.1 stays at \(1/7\): a non-monotone \(3+1\) lock
near \(a=\tfrac14\) has scarcer share \(\approx\tfrac14\).

## Current literature

- Fate note Lemmas 3.1–3.2 (`extended`): the cell-product \(10/69\) is
  replaced on monotone fibers only.
- Paper C §5.6 predicted \(0.405\to 0.448\) (`reproduced` as the root).
- Kernel localization (`refuted` as a method) is a different door.

## Branch budget

```text
Mathematical target     Can every good OE fiber carry ≥ (1/3)(1−ε(m))
                        of each parity of floor(n^{3/2}), ε(m)→0?
Novelty hypothesis      Pairing plus monotonicity makes the worst
                        revolution the 1+2 split at α=1/3.
Falsifier               A monotone step sequence (or a good m) with
                        scarcer share ≤ 1/3−δ for a fixed δ>0 as H→∞.
Existing machinery      Lemmas 3.1–3.3, fiber_stats, lambda_root.
Maximum Phase-0 scope   Pairing lemma plus a tiny synthetic / α-binned
                        check. No closure, no Lean, no new production.
Promotion criterion     Human-proof 1/3(1−ε) and the root moves.
Stop criterion          Structural gap below 1/3, or a constant hunt.
```

## Balanced-ternary formulation

None. The objects are run lengths of a monotone walk on \(\mathbb R/\mathbb Z\).

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Adversarial sweep \(H/7\) — **EXACT — HUMAN PROOF** (Lemma 3.1, kept).
- Monotone pairing \(H/3-2\) — **EXACT — HUMAN PROOF** (Lemma 3.1′).
- Fiber transfer — **EXACT — HUMAN PROOF** (Lemma 3.2, steps monotone).
- \(\lambda^{**}=0.4480\) — **EXACT — HUMAN PROOF** (`J-fate-log-density`).
- Adversarial \(3+1\) lock \(\approx 1/4\) — **COMPUTATIONALLY VERIFIED**.
- Census min \(0.328\) at \(\alpha_m\approx\tfrac13\) — **COMPUTATIONALLY VERIFIED**.

## Experiments

- Probe: `research.juggler_sequence.oe_fiber_constant`.
- Artifact: `data/research/juggler/oe_fiber_constant/summary.json`.
- Tests: `tests/research/juggler_sequence/test_oe_fiber_constant.py`.
- No closure rerun.

## Conjectures

None opened.

## Counterexamples

The adversarial \(3+1\) lock (steps in \([0.242,0.252]\), scarcer
\(\approx 0.247\)) kills an abstract rewrite of Lemma 3.1 as \(1/3\).
It is not monotone and is not a fiber.

## Formalization

None. `FateContagion.lean` stays the exact layer. No `sorry`.

## Results

- Lemma 3.1′, Lemma 3.2, Theorem 4.2 with \(\lambda^{**}=0.4480\).
- Classification `OE_FIBER_PAIRING_CONSISTENT`.
- Tao rate threshold \(0.552\); least \(C=20\). Appendix C consistency
  root \(\lambda^{***}=0.5392\) (no new production).

## Open questions

The remaining depth-two gap \(0.448\to 0.4927\) is a dynamical
averaging problem for the low-even set \(P\), not another pointwise
fiber bound. The average-on-rest attack is PARK
([juggler_oe_rest_average.md](juggler_oe_rest_average.md)). The
free term \(\psi_F\) is untouched.

## Decision

**PROMOTE.** Monotone pairing is a human proof, the characteristic
root moves, and the census floor at \(\alpha_m\approx\tfrac13\) is the
named obstruction. Best next question: none on this line; the
\(1/3\) versus \(1/2\) gap is not opened here.

## Publication assessment

Status: `THEOREM`. The pairing is elementary and belongs in Paper C
Theorem 1. Not a halt theorem.
