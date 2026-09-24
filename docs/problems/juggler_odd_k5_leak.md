# Juggler odd \(k=5\) leak

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the designated
next question of the promoted \(k=5\) cube-corridor branch: the
odd residual after \(W_5\).

## Envelope scope

A failed exponent comparison means that the inherited upper envelope does
not certify the proposed descent or cell bound. It gives no lower bound on
an actual orbit and does not prove absence of `FiniteProgress`. Negative
claims labelled REFUTED below concern deductions from this envelope test;
separate explicit orbit counterexamples retain their stated finite scope.

## Problem

If \(x_5=T_{W_5}(n)\) is odd, does the next `O` remain in a
controlled \(n\)-relative corridor, and what does parity do
to that image?

## Exact statement

Assume \(n\ge 2\) follows \(W_5=M(\mathtt{OOE})^5\) with
\(M=\mathtt{OOEOOOEOOEEOOE}\), and that \(x_5\) is odd. Write
\(y=T(x_5)\). The Phase-0 questions are:

1. the sharpest inherited envelope of \(y\), not the generic
   \(y<n^{9/2}\);
2. whether \(y\) can exceed \(n^3\);
3. the even-\(y\) and odd-\(y\) next-step corridors;
4. the shortest structurally plausible recovery words from
   \(x_5\).

## Current literature

- \(W_5\) cube cell \(x_5\le n^{3^{19}/2^{29}}<n^3\); even
  \(x_5\) resets to \(T<n^{3/2}\) —
  **EXACT — HUMAN PROOF** (`J-cyclemin-k5-post-l-cube`).
- \(M(\mathtt{OOE})^k\) has a square cell iff \(k\le 4\) —
  **EXACT — HUMAN PROOF**.
- First post-\(L\) \(M\)-envelope \(s<n^2\) —
  **EXACT — HUMAN PROOF**.
- Bunched-short / \(Z_5\) / terminal cells —
  **PARK**. Frozen. Not reopened.

Project relationship: **extended**. The designated next
question of the promoted \(k=5\) branch.

## Branch budget

```text
Mathematical target     odd x_5 next-O corridor / parity split
Novelty hypothesis      y \le  n^{3^{20}/2^{30}} < n^4; even y to C_1
Falsifier               only generic 9/2; y stays in C_3; even
                        opens a new hierarchy
Existing machinery      W_5 cube cell; power_bound_word
Maximum Phase-0 scope   y gaps; OEE recovery; second-O fifth;
                        501; no Lean
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

- \(W_5+\mathtt{O}\) has length 30 and 20 odds, so
  \(y^{2^{30}}\le n^{3^{20}}\) —
  **EXACT — HUMAN PROOF**.
- The cube cell fails:
  \(3^{20}=3486784401>3221225472=3\cdot 2^{30}\) —
  **EXACT — HUMAN PROOF**. The envelope does not exclude crossing
  \(n^3\); no orbit realizing such a crossing is asserted.
- The fourth-power cell holds:
  \(3^{20}<4\cdot 2^{30}\), hence
  \(y\le n^{3^{20}/2^{30}}<n^4\) —
  **EXACT — HUMAN PROOF**.
- The inherited ceiling is below the generic \(9/2\):
  \(3^{20}<9\cdot 2^{29}\) —
  **EXACT — HUMAN PROOF**.
- \(y\) stays in \(C_3=[n^2,n^3)\) —
  **REFUTED** as a deduction from the envelope. The cube
  gap fails. \(y\ge n^2\) is also not forced.
- The inherited envelope certifies a drop below \(n\) after even \(y\) —
  **REFUTED**. \(3^{20}>2^{31}\).
- The envelope certifies an even-\(y\) return below \(n^{3/2}\) —
  **REFUTED**. Same comparison as the failed cube cell.
- Even \(y\) resets:
  \(z=T(y)\) satisfies \(z^{2^{31}}\le n^{3^{20}}\) and
  \(3^{20}<2^{32}\), hence \(z\le n^{3^{20}/2^{31}}<n^2\) —
  **EXACT — HUMAN PROOF**. This is the known \(C_1\)
  corridor. Even \(y\) cannot start \(L\).
- From \(x_5\), the itineraries `E`, `OE`, `OOE`, `OOOE` contract
  versus \(n\) by the inherited exponent test —
  **REFUTED**.
- `OEE` contracts:
  \(3^{20}<2^{32}\) —
  **EXACT — HUMAN PROOF**. If \(y\) and \(T(y)\) are both
  even, the odd leak is FiniteProgress.
- The envelope certifies a second `O` from odd \(y\) below \(n^4\) —
  **REFUTED**. \(3^{21}>4\cdot 2^{31}\).
- A second `O` stays below \(n^5\):
  \(3^{21}<5\cdot 2^{31}\) —
  **EXACT — HUMAN PROOF**. An even landing after that
  second `O` returns below \(n^3\).
- \(501\) realizes the odd leak —
  **REFUTED**. Max consecutive post-\(M\) `OOE` is \(k=2\).
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed
- a recurrent \(k=5\) episode exists — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_k5_leak`
- Records: [juggler_odd_k5_leak.md](../research/juggler_odd_k5_leak.md),
  [juggler_odd_k5_leak.json](../research/juggler_odd_k5_leak.json)
- Tests: `tests/research/juggler_sequence/test_odd_k5_leak.py`
- The envelope core is in `CycleMinEnvelopes.lean`; see Formalization. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The envelope does not certify that the next `O` stays in \(C_3\).
The claim that only the generic \(9/2\) bound survives is **REFUTED** by

\[
3^{20}>3\cdot 2^{30},\qquad 3^{20}<4\cdot 2^{30},\qquad
3^{20}<9\cdot 2^{29}.
\]

The hypothesis that even \(y\) opens a new hierarchy is
**REFUTED**: \(3^{20}<2^{32}\) returns \(z\) to \(C_1\).

The inherited exponent tests for `E`/`OE`/`OOE`/`OOOE` from
\(x_5\) fail. Among these short candidates, `OEE` certifies recovery;
this does not exclude actual recovery along a word whose test fails.

`501` never follows \(W_5\). No \(W_5\) follower occurs in
the Phase-0 window \(12\le n<801\).

## Formalization

The envelope core is formalized in
[CycleMinEnvelopes.lean](../../formal/Problems/Juggler/CycleMinEnvelopes.lean).
The canonical ledger rows `J-cyclemin-odd-k5-y-fourth`
name the matching declarations. Negative declarations with
`exponent_not_lt` in their names prove only failure of the exponent
test. They do not prove non-descent or non-termination.

## Results

Classification **ODD_K5_LEAK_GREEN**.

If \(x_5\) is odd, then

\[
y^{1073741824}\le n^{3486784401}<n^{4294967296}=(n^4)^{1073741824},
\]

so

\[
y\le n^{3^{20}/2^{30}}<n^4.
\]

The cube cell is unavailable. The first integer replacement
is \(n^4\). The exact rational class lies strictly between
\(3\) and \(4\), and strictly below \(9/2\). This is a mild
enlargement, not a new unbounded regime.

Even \(y\) returns to a previously controlled corridor:

\[
y\text{ even}\Rightarrow T(y)<n^{2},
\]

and cannot restart \(L\). If the next image is also even,
`OEE` is FiniteProgress.

Odd \(y\) starts a second `OO` below \(n^5\). That is the
leftover. An even landing after that second `O` returns
below \(n^3\).

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The \(y<n^4\) bound and even-\(y\) square reset are
formalized in `w5_odd_lt_fourth` and `y_even`. The odd-\(y\) second-`OO` residual is the
separate branch
[juggler_w5_second_oo.md](juggler_w5_second_oo.md).
Do not reopen bunched-short cells. Do not write \(Z_5\).
Do not assemble `no_cycle_itinerary_length_eleven`. Do not
build a \(p\)-adic system.

## Decision

**PROMOTE**. The odd \(k=5\) leak is not a generic
\(n^{9/2}\) excursion. Its envelope does not certify a return
to \(C_3\); it supplies a
near-cube fourth-power corridor. Even images reset to
\(C_1\); `OEE` is FiniteProgress. The leftover is an odd
\(y\) that starts a second `OO`.

Best next question: if \(y\) is odd, does the second `O`
stay below \(n^4\) under an inherited constraint, or is
the first post-\(L\) fifth-power landing the leftover?

## Publication assessment

Status: `THEOREM`.

A named exact inherited next-`O` envelope and an even-\(y\)
reset. Not a Juggler totality result and not a claim that
every residual dies after one more `O`.
