# Juggler first `OOO` after controlled `OOE`

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the first-`OOO`
residual of the promoted odd-landing dichotomy after `OOEOOE`.

## Problem

After the first internal `OO`, can a CycleMin trajectory remain in
`OOE\cdot\{OE,OOE\}^*` indefinitely, or what constraint does the first
later odd run of length at least \(3\) satisfy?

## Exact statement

Let \(n\ge 12\) follow `OOE`, and write the subsequent blocks from the
language \(\{OE,OOE\}\) until the first `OOO` or a drop below \(n\).
Let \(x_{\mathrm{pre3}}\) be the state immediately before that first
`OOO`, when it occurs. The Phase-0 questions are:

1. whether \(\{OE,OOE\}^*\) has a common envelope strong enough to
   bound the number of `OOE` blocks;
2. whether every such trajectory must reach a first `OOO`;
3. whether
   \[
   x_{\mathrm{pre3}}\ge n
   \;\Rightarrow\;
   T^2(x_{\mathrm{pre3}})\ge n^2.
   \]

## Current literature

- \(T_{\mathtt{OOEOOE}}(n)<n^2\), even landing drops —
  **EXACT — HUMAN PROOF** (`J-cyclemin-ooeooe-square-preimage`).
- Forced next `O` after an odd `OOEOOE` landing stays below \(n^2\) —
  **EXACT — HUMAN PROOF** (`J-cyclemin-ooeooe-next-o`).
- Isolated-`OE` comparison \(R(2)=0\), so `OOE OE` cannot stay
  CycleMin — **EXACT — LEAN VERIFIED**
  (`no_cycleMin_prefix_ooe_oe`).
- Complete words `OOEOOE` and `OOEOOOE` —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_ooeooe`,
  `no_cycleMin_ooeoooe`).
- `ooo_suffix_threshold` —
  **EXACT — LEAN VERIFIED**. Not reopened as a tail table.
- Bunched-short / front overshoot / isolated-odd fibre —
  **PARK**. Frozen.

Project relationship: **extended**. The designated next question of
the promoted odd-landing branch.

## Branch budget

```text
Mathematical target     first OOO entrance after OOE.{OE,OOE}*
Novelty hypothesis      a narrow pre-OOO corridor C_3(n)
Falsifier               unbounded no-OOO survival; first OOO
                        from a generic scale; late OE always drops
Existing machinery      OOEOOE square cell; (OOE)^k gap;
                        no_cycleMin_prefix_ooe_oe; cube lemma
Maximum Phase-0 scope   language envelope; first-OOO event;
                        no Lean; no terminal-cell reopen
Promotion criterion     language bound, first-OOO inevitability,
                        or a sharp entrance corridor
Stop criterion          generic envelope only; uncontrolled
                        entrance; residue automaton;
                        Z5 / length-11 / four-even
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \((OOE)^k\) has the square-cell gap iff \(k\le 5\) —
  **EXACT — HUMAN PROOF**. \(2^{3k+1}>3^{2k}\).
- The next-`O` refinement \(3\cdot(9/8)^k<4\) holds iff
  \(k\le 2\) — **EXACT — HUMAN PROOF**.
- \(\{OE,OOE\}^*\) has no common sub-\(n^2\) envelope —
  **EXACT — HUMAN PROOF**. Six `OOE` blocks need at least
  one `OE` to restore the gap.
- `OOEO` has the gap \(32>27\), so the first `OE` after one
  `OOE` drops — **EXACT — HUMAN PROOF**. This is the
  square-cell mechanism of `no_cycleMin_prefix_ooe_oe`.
- `OOEOOO` loses the \(n^2\) gap; completed `OOEOOOE`
  restores it — **EXACT — HUMAN PROOF**.
- \(\lfloor n^{3/2}\rfloor^3\ge n^4\) for \(n\ge 3\) —
  **EXACT — HUMAN PROOF**. Hence if \(x\ge n\) follows
  `OO`, then \(T^2(x)\ge n^2\).
- first `OOO` is inevitable on the no-`OOO` language —
  **REFUTED**. \(365\) does \((OOE)^4\) then a late `OE`
  and drops.
- every later `OE` drops — **REFUTED**. After \(k\ge 3\),
  the even intermediate can already lie above \(n^2\).
  Witnesses: \(429\), \(365\).
- a bounded `OOE`-count — not claimed. The exponent
  \(9/8>1\) gives no \(r\)-bound analogue.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.first_ooo_escape`
- Records: [juggler_first_ooo_escape.md](../research/juggler_first_ooo_escape.md),
  [juggler_first_ooo_escape.json](../research/juggler_first_ooo_escape.json)
- Tests: `tests/research/juggler_sequence/test_first_ooo_escape.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that every no-`OOO` continuation must reach
`OOO` is **REFUTED**. Witness:

\[
365\xrightarrow{(OOE)^4}\;12707\xrightarrow{OE}\;1196\xrightarrow{E}\;34.
\]

The even intermediate of that late `OE` is \(1432400\ge 365^2\),
so the even-below-\(n^2\) trap no longer applies to the `O` of
`OE`. The subsequent even landing \(1196<365^2\) then drops.

The hypothesis that every `OE` after completed `OOE` blocks
drops immediately is **REFUTED**. Witnesses: \(365\) (\(k=4\))
and \(429\) (\(k=3\)).

The first-`OOO` escape witness remains

\[
565\xrightarrow{(OOE)^2}\;3039\xrightarrow{OOO}\;T^2(3039)=68571361\ge 565^2.
\]

The entrance \(3039\) still lies in \([565,565^2)\). The second
odd letter is the escape.

## Formalization

None. Existing `Envelope.lean`, `CycleCore.lean`,
`FirstInternalOO.lean`, and `Scale.lean` lemmas are cited, not
rewritten. No `no_cycleMin_prefix_ooeooo`. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`. No
`no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **FIRST_OOO_GREEN**.

If \(n\ge 3\) and \(x\ge n\) follows `OO`, then
\(T^2(x)\ge n^2\). Therefore

\[
\text{first post-first-OO }\mathtt{OOO}\text{ at }x\ge n
\;\Rightarrow\;
T^2(x)\ge n^2.
\]

The square-cell ceiling is lost at the second odd letter of
that `OOO`, not by repeated `OOE` itself. For \(k\le 5\),
\(T_{(OOE)^k}(n)<n^2\), so a first `OOO` after at most five
controlled `OOE` blocks enters from

\[
C_3(n)=[n,n^2)\cap(2\mathbb{Z}+1).
\]

The language \(\{OE,OOE\}^*\) does not force `OOO`, and it
has no common sub-\(n^2\) envelope. A bounded `OOE`-count is
not a theorem.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package \(\lfloor n^{3/2}\rfloor^3\ge n^4\) and the
second-odd escape. The residual after a first `OOO` from
\(C_3(n)\) — completed `OOOE` versus a longer odd run — is
the separate branch
[juggler_post_ooo_crossing.md](juggler_post_ooo_crossing.md).
Do not reopen bunched-short cells. Do not write \(Z_5\). Do
not assemble `no_cycle_itinerary_length_eleven`.

## Decision

**PROMOTE**. The first `OOO` after the controlled `OOE`
language, when it occurs, enters from \([n,n^2)\) and loses
the square ceiling at the second odd letter. First `OOO` is
not inevitable, and late `OE` after \(k\ge 3\) can survive
one step. A bounded no-`OOO` lifetime is not claimed.

Best next question: after a first `OOO` entered from
\(C_3(n)\), does the completed `OOOE` still force finite
progress or an existing obstruction, or is a longer odd run
the only residual?

## Publication assessment

Status: `THEOREM`.

A named exact second-odd square escape from the integer cube
comparison. Not a Juggler totality result and not an
inevitability theorem for `OOO`.
