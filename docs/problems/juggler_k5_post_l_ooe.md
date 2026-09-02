# Juggler \(k=5\) post-\(L\) `OOE` escape

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the designated
next question of the promoted second post-\(L\) `OOE` branch: the
first square-cell failure of \(M(\mathtt{OOE})^k\).

Notation is the implemented one. \(L=\mathtt{OOEOOOEOOEE}\) and

\[
M=L+\mathtt{OOE}=\mathtt{OOEOOOEOOEEOOE}
\]

(length 14, 9 odds). The square-cell budget
\(2^{15+3k}>3^{9+2k}\) is for this \(M\), not for \(L\) itself.

## Problem

When \(k=5\) loses the \(n^2\) cell, what exact \(n\)-relative
corridor replaces it, and what does parity do next?

## Exact statement

Let \(W_5=M(\mathtt{OOE})^5\) and \(x_5=T_{W_5}(n)\) whenever
\(n\) follows \(W_5\). The Phase-0 questions are:

1. the sharpest exact envelope \(x_5^A\le n^B\) and the smallest
   integer \(m\) with \(x_5<n^m\);
2. whether the \(k=5\) failure is a small leak or a new scale
   regime;
3. the even and odd next-step corridors;
4. whether an even landing resets to a previously controlled
   corridor, and whether \(x_5\) can restart \(L\).

The lower bound \(x_5\ge n^2\) is **not** an axiom of the
square-cell failure.

## Current literature

- \(M(\mathtt{OOE})^k\) has a square cell iff \(k\le 4\) —
  **EXACT — HUMAN PROOF** (`J-cyclemin-second-post-l-ooe-square`).
- First post-\(L\) \(M\)-envelope \(s<n^2\) —
  **EXACT — HUMAN PROOF**.
- \(t^{2048}\le n^{2187}\) —
  **EXACT — HUMAN PROOF**.
- First-`OO` language \((\mathtt{OOE})^k\) has a square cell
  iff \(k\le 5\) —
  **EXACT — HUMAN PROOF**.
- Bunched-short / \(Z_5\) / terminal cells —
  **PARK**. Frozen. Not reopened.

Project relationship: **extended**. The designated next
question of the promoted second post-\(L\) `OOE` branch.

## Branch budget

```text
Mathematical target     k=5 replacement corridor / parity split
Novelty hypothesis      cube cell; 9/8 leak; even resets to n^{3/2}
Falsifier               no bound below n^4; even opens a new
                        hierarchy; only a generic 3/2 bound
Existing machinery      M(OOE)^k square max 4; power_bound_word
Maximum Phase-0 scope   W_5 gaps; even reset; odd n^4; 501; no Lean
Promotion criterion     exact replacement corridor plus a
                        parity-conditioned transition
Stop criterion          generic 3/2 only; suffix automaton;
                        Z5 / length-11 / four-even / p-adic
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(W_5\) has length 29 and 19 odds, so
  \(x_5^{2^{29}}\le n^{3^{19}}\) —
  **EXACT — HUMAN PROOF**.
- The square cell fails:
  \(2^{30}=1073741824<1162261467=3^{19}\) —
  **EXACT — HUMAN PROOF**.
- The cube cell holds:
  \(3^{19}<3\cdot 2^{29}=1610612736\), hence
  \(x_5<n^{3^{19}/2^{29}}<n^3\) —
  **EXACT — HUMAN PROOF**. The first integer threshold
  replacing \(n^2\) is \(n^3\).
- \(x_5\ge n^2\) is forced by the square failure —
  **REFUTED** as a deduction. Losing a ceiling does not
  create a floor.
- The \(k=4\) ceiling lies below 2
  (\(3^{17}<2^{27}\)); the \(k=5\) ceiling lies above 2
  (\(3^{19}>2^{30}\)). The exponent ratios differ by
  exactly \(9/8\) —
  **EXACT — HUMAN PROOF**. This is a near-square leak,
  not a jump to \(n^4\).
- Even \(x_5\) is FiniteProgress —
  **REFUTED**. \(3^{19}>2^{30}\).
- Even \(x_5\) resets:
  \(T(x_5)^{2^{30}}\le n^{3^{19}}\) and
  \(3^{19}<3\cdot 2^{29}\) give \(T(x_5)<n^{3/2}<n^2\) —
  **EXACT — HUMAN PROOF**. Same comparison as the cube
  cell. This is the known \(C_1\)-type corridor, not a
  new hierarchy. Even \(x_5\) cannot start \(L\)
  (\(L\) begins with `O`).
- Odd \(x_5\) has next-`O` image below \(n^3\) —
  **REFUTED**. \(3^{20}>3\cdot 2^{30}\).
- Odd \(x_5\) has next-`O` image below \(n^4\):
  \(3^{20}<4\cdot 2^{30}\) —
  **EXACT — HUMAN PROOF**.
- Therefore
  \[
  k=5
  \Rightarrow
  \begin{cases}
  \text{even: known }C_1\text{ corridor }T<n^{3/2},\\
  \text{odd: controlled next-}O\text{ below }n^4.
  \end{cases}
  \]
  **EXACT — HUMAN PROOF**.
- \(501\) realizes \(W_5\) —
  **REFUTED**. Max consecutive post-\(M\) `OOE` is \(k=2\);
  landing \(12707\) starts `OE`.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed
- \(k=5\) is contradictory — not claimed

## Experiments

- Probe: `research.juggler_sequence.k5_post_l_ooe`
- Records: [juggler_k5_post_l_ooe.md](../research/juggler_k5_post_l_ooe.md),
  [juggler_k5_post_l_ooe.json](../research/juggler_k5_post_l_ooe.json)
- Tests: `tests/research/juggler_sequence/test_k5_post_l_ooe.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that \(k=5\) has no useful bound below
\(n^4\), or that the even branch opens a new scale
hierarchy, is **REFUTED** by

\[
3^{19}<3\cdot 2^{29}.
\]

The hypothesis that even \(x_5\) drops below \(n\) is
**REFUTED** by \(3^{19}>2^{30}\).

The hypothesis that \(501\) pays the \(k=5\) escape is
**REFUTED**:

\[
1749\xrightarrow{\mathtt{OOE}}4447\xrightarrow{\mathtt{OOE}}12707,
\]

and \(12707\) starts `OE`. No \(W_5\) follower occurs in
the Phase-0 window \(12\le n<801\).

## Formalization

None. Existing `Envelope.lean` `power_bound_word` and
`power_bound_contracts` are cited, not rewritten. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`.
No `no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **K5_POST_L_OOE_GREEN**.

If \(n\ge 2\) follows \(W_5\), then

\[
x_5^{536870912}\le n^{1162261467}<n^{1610612736}=(n^3)^{536870912},
\]

so

\[
x_5<n^{3^{19}/2^{29}}<n^3.
\]

The square cell is unavailable. The first integer
replacement is the cube. The exact rational class is
strictly above \(2\) for the first time in this residual
family, by the factor \(9/8\) over the \(k=4\) ratio.

Even \(x_5\) returns to a previously controlled corridor:

\[
x_5\text{ even}\Rightarrow T(x_5)<n^{3/2}<n^2,
\]

and cannot restart \(L\). It is not FiniteProgress.

Odd \(x_5\) has a controlled next-`O` envelope below
\(n^4\), which may enter \(C_3\). That is the leftover.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package \(3^{19}<3\cdot 2^{29}\) and the even
\(n^{3/2}\) reset. The odd \(k=5\) next-`O` residual is
the separate branch
[juggler_odd_k5_leak.md](juggler_odd_k5_leak.md).
Do not reopen bunched-short cells. Do not write \(Z_5\).
Do not assemble `no_cycle_itinerary_length_eleven`. Do not
build a \(p\)-adic system.

## Decision

**PROMOTE**. The first post-\(L\) square-cell failure is a
near-square cube corridor, not a contradiction and not a
new unbounded hierarchy. Even landings reset to the known
\(C_1\)-type band below \(n^{3/2}\). Odd landings are a
controlled fourth-power residual.

Best next question: if \(x_5\) is odd, does the next `O`
stay below \(n^3\) under an inherited constraint, or is
the first post-\(L\) \(C_3\) landing the leftover?

## Publication assessment

Status: `THEOREM`.

A named exact cube replacement of the \(k=5\) square
failure and an even-reset theorem. Not a Juggler totality
result and not a claim that every residual dies at \(k=5\).
