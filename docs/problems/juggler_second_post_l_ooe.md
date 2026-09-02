# Juggler second post-`L` `OOE` residual

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the residual of
the promoted first post-\(L\) `OOE` theorem: the landing \(s\)
that starts `OO`.

## Problem

After \(s=T_M(n)\) starts `OO`, does the next completed `OOE`
still occupy an \(n\)-relative square cell, and for how many
consecutive post-\(L\) `OOE` blocks does that cell survive?

## Exact statement

Let \(M=\mathtt{OOEOOOEOOEEOOE}\) and assume \(s=T_M(n)\) is
odd and starts `OO`. Write \(r=T_{\mathtt{OOE}}(s)\). The
Phase-0 questions are:

1. whether \(r=T_{M+\mathtt{OOE}}(n)\) satisfies \(n\le r<n^2\);
2. the largest \(k\) such that \(M(\mathtt{OOE})^k\) still
   has the square-cell gap \(2^{15+3k}>3^{9+2k}\);
3. whether even \(r\) or an `OE` after \(r\) is FiniteProgress.

## Current literature

- First post-\(L\) `OOE`: \(s^{16384}\le n^{19683}\) and
  \(s<n^2\); `M+E`/`M+OE` contract —
  **EXACT — HUMAN PROOF** (`J-cyclemin-post-l-ooe-me-drop`).
- Post-\(L\) `OOE` re-enters \(L\) —
  **REFUTED**.
- \(t^{2048}\le n^{2187}\) —
  **EXACT — HUMAN PROOF**.
- First-`OO` language \((\mathtt{OOE})^k\) has a square
  cell iff \(k\le 5\) —
  **EXACT — HUMAN PROOF**.
- Bunched-short / \(Z_5\) / terminal cells —
  **PARK**. Frozen. Not reopened.

Project relationship: **extended**. The designated next
question of the promoted post-\(L\) `OOE` branch.

## Branch budget

```text
Mathematical target     second post-L OOE square cell / k-max
Novelty hypothesis      M+OOE still < n^2; k<=4; even r drops
Falsifier               square fails at k=1; k unbounded;
                        generic OOE only; OE after M2 drops
Existing machinery      M square cell; 501 -> 1749
Maximum Phase-0 scope   M+(OOE)^k gaps; 501 r=4447; no Lean
Promotion criterion     square for a nontrivial k-range,
                        plus a parity split
Stop criterion          no finite k; generic OOE;
                        Z5 / length-11 / four-even / p-adic
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(M+\mathtt{OOE}\) has length 17 and 11 odds, so
  \(r^{131072}\le n^{177147}\) and \(2^{18}>3^{11}\),
  hence \(n\le r<n^2\) —
  **EXACT — HUMAN PROOF**.
- Even \(r\) drops: \(3^{11}<2^{18}\) —
  **EXACT — HUMAN PROOF**.
- \(M(\mathtt{OOE})^k\) has the square gap
  \(2^{15+3k}>3^{9+2k}\) iff \(k\le 4\) —
  **EXACT — HUMAN PROOF**. The cell is lost at
  \(k=5\) (\(2^{30}<3^{19}\)). This is a corridor
  budget, not a halt bound.
- `OE` after the second `OOE` is FiniteProgress —
  **REFUTED**. \(3^{12}>2^{19}\) (\(531441>524288\)).
  The itinerary still has a square cell (\(3^{12}<2^{20}\)).
  If that landing is even, `M+OOEOEE` contracts.
- Therefore
  \(\operatorname{CycleMin}(n,M\,\mathtt{OOE}\,v)\)
  implies FiniteProgress or \(v\) starts with `O` —
  **EXACT — HUMAN PROOF**. `OE` is not itself a drop.
- Repeated \(k\) is unbounded in the square cell —
  **REFUTED**. First failure at \(k=5\).
- The second `OOE` is a generic `OOE` from \(s\)
  with no \(n\)-relative cell —
  **REFUTED**. The cell is \(r^{131072}\le n^{177147}\).
- \(501\to 4447\) re-enters \(L\) —
  **REFUTED**. `walk_language(1749)` exits by drop;
  `second_oo(1749)` is missing.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.second_post_l_ooe`
- Records: [juggler_second_post_l_ooe.md](../research/juggler_second_post_l_ooe.md),
  [juggler_second_post_l_ooe.json](../research/juggler_second_post_l_ooe.json)
- Tests: `tests/research/juggler_sequence/test_second_post_l_ooe.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that `OE` after the second post-\(L\)
`OOE` drops below \(n\) is **REFUTED** by the exponent
comparison \(531441>524288\).

The hypothesis that the square cell persists for all
\(k\) is **REFUTED**:

\[
k=5:\qquad 2^{30}=1073741824<1162261467=3^{19}.
\]

The \(501\) residual continues `OO` at the second
landing:

\[
1749\xrightarrow{\mathtt{OOE}}4447,
\qquad 4447<501^{2},\qquad 4447\text{ starts }\mathtt{OO}.
\]

It later leaves by a third `OOE` then `OE` to \(34\),
never paying a first `OOO` from \(1749\).

## Formalization

None. Existing `Envelope.lean` `power_bound_word` and
`power_bound_contracts` are cited, not rewritten. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`.
No `no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **SECOND_POST_L_OOE_GREEN**.

If \(s=T_M(n)\) starts `OO` and \(r=T_{\mathtt{OOE}}(s)\),
then

\[
r^{131072}\le n^{177147}<n^{262144}=(n^2)^{131072},
\]

so \(n\le r<n^2\). Even \(r\) is FiniteProgress. An `OE`
after \(r\) is not. The repeated residual

\[
M(\mathtt{OOE})^k
\]

stays in the square cell for every \(k\le 4\) and leaves
it at \(k=5\). That is a finite algebraic budget on
consecutive post-\(L\) `OOE` blocks, not a proof that
every orbit dies before \(k=5\).

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package \(2^{18}>3^{11}\) and the \(k\le 4\) gap.
The first \(k=5\) square failure is the separate branch
[juggler_k5_post_l_ooe.md](juggler_k5_post_l_ooe.md).
The residual after a second `OO` landing (\(501\to 4447\))
that dies at \(k=2\) is not that escape. Do not
reopen bunched-short cells. Do not write \(Z_5\). Do not
assemble `no_cycle_itinerary_length_eleven`. Do not build a
\(p\)-adic system.

## Decision

**PROMOTE**. The second post-\(L\) `OOE` still occupies
\([n,n^2)\), even landings drop, and consecutive copies
have a finite square-cell budget \(k\le 4\). `OE` after
the second block is not FiniteProgress. The \(k=5\)
failure is not a contradiction.

Best next question: at \(k=5\), when
\(2^{15+3k}>3^{9+2k}\) fails, what exact corridor
replaces the square cell?

## Publication assessment

Status: `THEOREM`.

A named exact second-post-\(L\) square cell and a finite
\(k\)-budget. Not a Juggler totality result and not a
claim that every residual dies at \(k=5\).
