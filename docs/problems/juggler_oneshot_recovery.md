# Juggler recovery after the one-shot `OOEOOOEOOEE` loop

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the residual of the
promoted pre/post refinement of the coarse scale loop.

## Problem

After one pass of \(L(n)=T_{\mathtt{OOEOOOEOOEE}}(n)\) on the
inherited even-even second-`OO` corridor, what exact resource
was spent, and can \(t=L(n)\) recreate the same entrance
without first dropping below \(n\)?

## Exact statement

Let \(n\) follow `OOEOOOEOOEE` through the inherited even-even
second-`OO` corridor, and write \(t=L(n)\). The Phase-0
questions are:

1. the strongest exact inequality for \(t\), and which
   suffixes \(W\) compose with \(t^{2048}\le n^{2187}\) to
   force \(T_W(t)<n\);
2. whether \(t\) can satisfy the same pre-\(L\) entrance
   (start `OOE`, pay a first `OOO`, finish even-even);
3. whether the observed recoveries of \(501\) and \(6187\)
   are instances of a common structural split.

## Current literature

- Even-even \(C_2\to C_4\to C_2\to C_1\) is `OOEOOOEOOEE`;
  \(C_1^{\mathrm{pre}}=C_1^{\mathrm{post}}\) iff \(t=n\) —
  **EXACT — HUMAN PROOF** (`J-cyclemin-scale-loop-oneshot`).
- The exact loop signature repeats —
  **REFUTED** (`J-cyclemin-scale-loop-signature-repeats`).
- \(t^{2048}\le n^{2187}\) —
  **EXACT — HUMAN PROOF**. This does not force \(t<n\)
  (\(2187>2048\)).
- Inherited second-`OO` envelope —
  **EXACT — HUMAN PROOF**.
- Bunched-short / front overshoot / \(2\)-adic hidden state —
  **PARK** / **REFUTED**. Frozen. Not reopened.

Project relationship: **extended**. The designated next
question of the promoted scale-loop hidden-state branch.

## Branch budget

```text
Mathematical target     post-L entrance exclusion / recovery
Novelty hypothesis      E or OE after L drops below n
Falsifier               t re-enters L; only the old envelope;
                        recovery is an arbitrary suffix
Existing machinery      t^{2048} <= n^{2187}; 501 / 6187
Maximum Phase-0 scope   compose 2187/2048 through E, OE;
                        named OO residual; no Lean
Promotion criterion     post-L cannot meet the pre-L entrance,
                        or a bounded recovery
Stop criterion          only the old envelope; suffix chaos;
                        Z5 / length-11 / four-even / p-adic
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- If \(t^{2048}\le n^{2187}\) and \(t\) follows \(W\), then
  \(T_W(t)<n\) whenever
  \(2187\cdot 3^{\#O(W)}<2048\cdot 2^{|W|}\) —
  **EXACT — HUMAN PROOF**.
- Even \(t\) drops: \(W=\mathtt{E}\) gives \(2187<4096\) —
  **EXACT — HUMAN PROOF**. Witness \(11233\to 21154\to 145\).
- \(t\) following `OE` drops: \(6561<8192\) —
  **EXACT — HUMAN PROOF**. Witnesses \(6187\to 1087\) and
  \(11853\to 1831\).
- Therefore a post-\(L\) state that does not start `OO`
  has FiniteProgress and cannot start `OOE`, hence cannot
  meet the pre-\(L\) entrance —
  **EXACT — HUMAN PROOF**.
- `OOE` after \(t\) compose-drops —
  **REFUTED**. \(2187\cdot 9>2048\cdot 8\).
- A second \(L\) compose-drops —
  **REFUTED**. \(2187\cdot 2187>2048\cdot 2048\).
- Every post-\(L\) recovery is `OE` —
  **REFUTED**. \(11233\) is `E`; \(501\) is `OO`.
- Final even remainder is a Lyapunov /
  finite-progress certificate —
  **REFUTED**. \(\varepsilon(s)\) is \(747\), \(7719\),
  \(9186\), \(27853\) on the four named loops.
- \(t\) re-enters \(L\) or `second_oo(t)` —
  **REFUTED** on the inherited sample \(n<12001\)
  (four loops). \(763\) still starts `OOE` but never
  pays a first `OOO`.
- The `OO` residual is closed —
  not claimed. \(501\) recovers by `OOEOOEOOEOEE`
  (\(2187\cdot 2187<2048\cdot 4096\)), one sample.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.oneshot_recovery`
- Records: [juggler_oneshot_recovery.md](../research/juggler_oneshot_recovery.md),
  [juggler_oneshot_recovery.json](../research/juggler_oneshot_recovery.json)
- Tests: `tests/research/juggler_sequence/test_oneshot_recovery.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that every post-\(L\) recovery is `OE` is
**REFUTED**.

\[
11233\xrightarrow{\mathtt{OOEOOOEOOEE}}21154
\xrightarrow{\mathtt{E}}145.
\]

\[
501\xrightarrow{\mathtt{OOEOOOEOOEE}}763
\xrightarrow{\mathtt{OOEOOEOOEOEE}}34.
\]

The hypothesis that \(t\) re-enters the pre-\(L\) entrance
is **REFUTED** on the inherited even-even sample below
\(12001\):

\[
6187\to 11189\xrightarrow{\mathtt{OE}}1087,
\qquad
11853\to 22403\xrightarrow{\mathtt{OE}}1831.
\]

None of the four images follows `OOEOOOEOOEE`. None has
`second_oo(t)`. None pays a first `OOO` from \(t\).

No \(L^k(n)=n\) approach was found.

## Formalization

None. Existing `Envelope.lean` `power_bound_word` and
`power_bound_contracts` are cited, not rewritten. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`.
No `no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **ONESHOT_RECOVERY_GREEN**.

If \(t=L(n)\) and \(t^{2048}\le n^{2187}\), then any
followed word \(W\) with
\(2187\cdot 3^{\#O(W)}<2048\cdot 2^{|W|}\) lands below
\(n\). In particular

\[
t\text{ even}\Rightarrow T(t)<n,
\qquad
t\text{ follows }\mathtt{OE}\Rightarrow T_{\mathtt{OE}}(t)<n.
\]

Those two cases are FiniteProgress and lie outside the
`OOE` entrance of \(L\). The remaining case is an odd
\(t\) that starts `OO`. The only inherited example below
\(12001\) is \(501\to 763\), which does not re-enter \(L\)
and recovers by a compose-contracting itinerary.

The resource consumed by one \(L\) pass, on the non-`OO`
branch, is the ability to start `OOE` without immediately
dropping. That is an exact entrance exclusion, not a
residue.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package \(2187<4096\) and \(6561<8192\) after
`OOEOOOEOOEE`. The residual is the `OO` post-\(L\) branch,
now the separate branch
[juggler_post_l_ooe.md](juggler_post_l_ooe.md).
Do not reopen bunched-short cells. Do not write \(Z_5\).
Do not assemble `no_cycle_itinerary_length_eleven`. Do not
build a \(p\)-adic system.

## Decision

**PROMOTE**. After \(L\), even \(t\) or `OE` is FiniteProgress
by composed exponents, and those states cannot meet the
pre-\(L\) `OOE` entrance. The apparent scale loop is
arithmetically one-shot on that branch. The `OO` residual
is not closed.

Best next question: after \(L\), if \(t\) starts `OO`, is a
compose-contracting recovery still forced, or can \(t\) pay
a later first `OOO` relative to the same \(n\)?

## Publication assessment

Status: `THEOREM`.

A named exact post-\(L\) composition theorem for `E` and
`OE`. Not a Juggler totality result and not a claim that
the `OO` residual cannot re-expand.
