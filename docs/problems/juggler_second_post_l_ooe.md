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

## Envelope scope

A failed exponent comparison means that the inherited upper envelope does
not certify the proposed descent or cell bound. It gives no lower bound on
an actual orbit and does not prove absence of `FiniteProgress`. Negative
claims labelled REFUTED below concern deductions from this envelope test;
separate explicit orbit counterexamples retain their stated finite scope.

## Problem

After \(s=T_M(n)\) starts `OO`, does the next completed `OOE`
still occupy an \(n\)-relative square cell, and for how many
consecutive post-\(L\) `OOE` blocks does that cell survive?

## Exact statement

Let \(M=\mathtt{OOEOOOEOOEEOOE}\) and assume \(s=T_M(n)\) is
odd and follows the completed word `OOE`. Write \(r=T_{\mathtt{OOE}}(s)\). The
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
  hence \(r<n^2\) (and \(n\le r\) only under a separate cycle-minimum assumption) —
  **EXACT — HUMAN PROOF**.
- Even \(r\) drops: \(3^{11}<2^{18}\) —
  **EXACT — HUMAN PROOF**.
- \(M(\mathtt{OOE})^k\) has the square gap
  \(2^{15+3k}>3^{9+2k}\) iff \(k\le 4\) —
  **EXACT — HUMAN PROOF**. The square-envelope certificate fails at
  \(k=5\) (\(2^{30}<3^{19}\)). This is a corridor
  budget, not a halt bound.
- The exponent test certifies `OE` after the second `OOE` as FiniteProgress —
  **REFUTED**. \(3^{12}>2^{19}\) (\(531441>524288\)).
  The itinerary still has a square cell (\(3^{12}<2^{20}\)).
  If that landing is even, `M+OOEOEE` contracts.
- Therefore
  \(\operatorname{CycleMin}(n,M\,\mathtt{OOE}\,v)\)
  implies FiniteProgress or \(v\) starts with `O` —
  **EXACT — HUMAN PROOF**. The inherited exponent test does not
  certify a drop for `OE` itself.
- This square-envelope test succeeds for arbitrarily large \(k\) —
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
- The envelope core is in `CycleMinEnvelopes.lean`; see Formalization. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The claim that the inherited exponent test certifies descent for
`OE` after the second post-\(L\) `OOE` is **REFUTED** by
\(531441>524288\). This does not refute actual descent.

The claim that this exponent test certifies the square cell for all
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

The envelope core is formalized in
[CycleMinEnvelopes.lean](../../formal/Problems/Juggler/CycleMinEnvelopes.lean).
The canonical ledger rows `J-cyclemin-second-post-l-ooe-square`
name the matching declarations. Negative declarations with
`exponent_not_lt` in their names prove only failure of the exponent
test. They do not prove non-descent or non-termination.

## Results

Classification **SECOND_POST_L_OOE_GREEN**.

If \(n\ge2\) follows \(M\,\mathtt{OOE}\), with
\(s=T_M(n)\) and \(r=T_{\mathtt{OOE}}(s)\),
then

\[
r^{131072}\le n^{177147}<n^{262144}=(n^2)^{131072},
\]

so \(r<n^2\). The lower bound \(n\le r\) requires the separate
cycle-minimum hypothesis. Even \(r\) gives FiniteProgress; the
inherited exponent test does not certify it for `OE` after \(r\).
The repeated residual

\[
M(\mathtt{OOE})^k
\]

has a certified square upper bound for every \(k\le 4\); this
exponent certificate first fails at \(k=5\). That is a budget for the test on
consecutive post-\(L\) `OOE` blocks, not a proof that
every orbit dies before \(k=5\).

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The square bound and \(k\le4\) exponent gap are formalized
in `m_ooe_lt_sq` and `m_ooePow_gap_iff`.
The first \(k=5\) square failure is the separate branch
[juggler_k5_post_l_ooe.md](juggler_k5_post_l_ooe.md).
The residual after a second `OO` landing (\(501\to 4447\))
that dies at \(k=2\) is not that escape. Do not
reopen bunched-short cells. Do not write \(Z_5\). Do not
assemble `no_cycle_itinerary_length_eleven`. Do not build a
\(p\)-adic system.

## Decision

**PROMOTE**. The second post-\(L\) `OOE` stays below \(n^2\),
and even landings drop below \(n\). Under a cycle-minimum assumption,
the intermediate landing also lies above or at \(n\). The square
envelope test succeeds for consecutive copies exactly when \(k\le4\).
For `OE` after the second copy, the test does not certify descent.
Its failure at \(k=5\) is not an orbit contradiction.

Best next question: at \(k=5\), when
\(2^{15+3k}>3^{9+2k}\) fails, what exact corridor
replaces the square cell?

## Publication assessment

Status: `THEOREM`.

A named exact second-post-\(L\) square cell and a finite
\(k\)-budget. Not a Juggler totality result and not a
claim that every residual dies at \(k=5\).
