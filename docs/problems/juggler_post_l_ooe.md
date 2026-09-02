# Juggler post-`L` `OOE` residual

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the residual of the
promoted post-\(L\) `E`/`OE` FiniteProgress theorem: the odd \(t\)
that starts `OOE`.

## Problem

After \(t=L(n)\) begins `OOE`, can that episode regenerate the
original \(L\)-entrance, or is it a strictly different expansion
with an inherited envelope?

## Exact statement

Let \(n\) follow `OOEOOOEOOEE` through the inherited even-even
second-`OO` corridor, write \(t=L(n)\), and assume \(t\) starts
`OOE`. Let \(s=T_{\mathtt{OOE}}(t)\) and
\(M=\mathtt{OOEOOOEOOEEOOE}\). The Phase-0 questions are:

1. the strongest exact envelope for \(s=T_M(n)\) relative to
   \(n\), not a generic `OOE` from \(t\);
2. whether \(s\) even or \(s\) following `OE` forces
   FiniteProgress;
3. whether \(t\) or \(s\) can meet the original \(L\)-entrance.

## Current literature

- Post-\(L\) even \(t\) or `OE` is FiniteProgress —
  **EXACT — HUMAN PROOF** (`J-cyclemin-oneshot-oe-drop`).
- \(t\) re-enters \(L\) / every recovery is `OE` —
  **REFUTED** (`J-cyclemin-oneshot-reenters`).
- \(t^{2048}\le n^{2187}\) —
  **EXACT — HUMAN PROOF**.
- Even-even \(C_2\to C_4\to C_2\to C_1\) is `OOEOOOEOOEE` —
  **EXACT — HUMAN PROOF**.
- Bunched-short / \(2\)-adic hidden state / terminal cells —
  **PARK** / **REFUTED**. Frozen. Not reopened.

Project relationship: **extended**. The designated next
question of the promoted oneshot-recovery branch.

## Branch budget

```text
Mathematical target     post-L OOE: new L-entrance or not
Novelty hypothesis      M+E / M+OE drop; M has a square cell
Falsifier               generic OOE only; second L-entrance;
                        no inherited n-relative bound
Existing machinery      2187/2048; 501 OO residual
Maximum Phase-0 scope   M envelope; E/OE after one OOE;
                        501 / 17245; no Lean
Promotion criterion     FP or a strictly different episode
Stop criterion          generic OOE; arbitrary recovery;
                        Z5 / length-11 / four-even / p-adic
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(T_M(n)^{16384}\le n^{19683}\) and \(19683<32768\),
  hence \(s<n^2\) —
  **EXACT — HUMAN PROOF**. This uses \(t^{2048}\le n^{2187}\)
  through one `OOE` (\(s^8\le t^9\)).
- \(M\) contracts versus \(n\) —
  **REFUTED**. \(19683>16384\).
- After \(M\), even \(s\) drops: `M+E` contracts
  (\(19683<32768\)) —
  **EXACT — HUMAN PROOF**.
- After \(M\), \(s\) following `OE` drops: `M+OE`
  contracts (\(59049<65536\)) —
  **EXACT — HUMAN PROOF**. Witness
  \(17245\to 33435\to 122949\xrightarrow{\mathtt{OE}}6565\).
- Therefore a post-\(L\) `OOE` landing that does not start
  `OO` is FiniteProgress and cannot meet the \(L\)-entrance —
  **EXACT — HUMAN PROOF**.
- `OOE` from \(t\) compose-drops versus \(n\) —
  **REFUTED**. \(2187\cdot 9>2048\cdot 8\).
- A second post-\(L\) `OOE` then `OE` contracts versus
  \(n\) —
  **REFUTED**. \(3^{12}>2^{19}\).
- Post-\(L\) `OOE` always dies immediately —
  **REFUTED**. \(501\to 763\to 1749\) starts `OO`.
- \(t\) or \(s\) re-enters \(L\) —
  **REFUTED** on the inherited sample. `walk_language(763)`
  exits by drop; `second_oo(763)` is missing; neither
  \(763\) nor \(1749\) follows `OOEOOOEOOEE`.
- Every new episode has a strictly larger CycleMin
  anchor —
  not claimed. \(501\) later drops to \(34\).
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.post_l_ooe`
- Records: [juggler_post_l_ooe.md](../research/juggler_post_l_ooe.md),
  [juggler_post_l_ooe.json](../research/juggler_post_l_ooe.json)
- Tests: `tests/research/juggler_sequence/test_post_l_ooe.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that post-\(L\) `OOE` immediately dies is
**REFUTED**.

\[
501\xrightarrow{\mathtt{OOEOOOEOOEE}}763
\xrightarrow{\mathtt{OOE}}1749,
\]

and \(1749\) starts `OO`. The orbit never pays a first
`OOO` relative to \(763\) and recovers by
`OOEOOEOOEOEE` to \(34\).

The hypothesis that every post-\(L\) `OOE` continues `OO`
is **REFUTED**.

\[
17245\xrightarrow{\mathtt{OOEOOOEOOEE}}33435
\xrightarrow{\mathtt{OOE}}122949
\xrightarrow{\mathtt{OE}}6565<17245.
\]

No inherited post-\(L\) `OOE` residual with \(n<20001\)
follows a second `OOEOOOEOOEE`.

## Formalization

None. Existing `Envelope.lean` `power_bound_word` and
`power_bound_contracts` are cited, not rewritten. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`.
No `no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **POST_L_OOE_GREEN**.

If \(t=L(n)\) starts `OOE` and \(s=T_{\mathtt{OOE}}(t)\),
then

\[
s^{16384}\le n^{19683}<n^{32768}=(n^2)^{16384},
\]

so \(n\le s<n^2\) on the inherited corridor. Moreover

\[
s\text{ even}\Rightarrow T(s)<n,
\qquad
s\text{ follows }\mathtt{OE}\Rightarrow T_{\mathtt{OE}}(s)<n.
\]

Those landings cannot recreate the \(L\)-entrance. The only
surviving residual is a landing that starts `OO` — a second
post-\(L\) `OOE`, not an \(L\)-episode. That second `OOE`
then `OE` does not contract versus \(n\).

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package \(19683<32768\) and \(59049<65536\) after
`OOEOOOEOOEEOOE`. The residual is a second post-\(L\)
`OOE` (\(501\to 1749\)), now the separate branch
[juggler_second_post_l_ooe.md](juggler_second_post_l_ooe.md).
Do not reopen bunched-short cells. Do not write \(Z_5\).
Do not assemble `no_cycle_itinerary_length_eleven`. Do not
build a \(p\)-adic system.

## Decision

**PROMOTE**. One post-\(L\) `OOE` is a different episode
from \(L\): it occupies a square cell relative to \(n\), and
if the landing does not start `OO` it is FiniteProgress.
The \(L\)-entrance is not recreated. The second `OOE` after
\(L\) is not closed.

Best next question: after \(L+\mathtt{OOE}\), if \(s\)
starts `OO`, does that second `OOE` still admit an exact
\(n\)-relative split, or is that the first post-\(L\) block
that no longer contracts on `OE`?

## Publication assessment

Status: `THEOREM`.

A named exact \(M\)-envelope and `M+E`/`M+OE` drop. Not a
Juggler totality result and not an episode-anchor induction.
