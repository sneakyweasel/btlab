# Juggler minimal first-`OO` corridor `OOEOOE`

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the \(a_0=2\),
\(r=0\), \(b=2\) cut of the first-internal-`OO` program.

## Problem

After \(R(2)=0\), does the weakest remaining \(a_0=2\) prefix
`OOEOOE` force finite progress or an already-known obstruction,
using only that prefix plus general CycleMin properties?

## Exact statement

Let \(C=T_{OOE}\) and write
\[
n\xrightarrow{O}x_1\xrightarrow{O}x_2\xrightarrow{E}x_3
\xrightarrow{O}x_4\xrightarrow{O}x_5\xrightarrow{E}x_6,
\]
so \(x_3=C(n)\) and \(x_6=C(x_3)\) whenever \(n\) follows `OOEOOE`.
The Phase-0 questions are:

1. the strongest exact relation between \(x_6\) and \(n\);
2. whether
   \[
   \operatorname{CycleMin}(n,\;OOEOOE\,v)
   \Rightarrow
   \texttt{FiniteProgress}(n)
   \;\lor\;
   \texttt{ExistingObstruction}(n,v)
   \]
   holds for arbitrary \(v\).

The empty itinerary \(v=\varepsilon\) is already excluded
(`no_cycleMin_ooeooe`). Isolated `OE` after the first even is already
excluded (`no_cycleMin_prefix_ooe_oe`). Neither is reopened.

## Current literature

- Isolated-`OE` comparison \(r\le R(a_0)\), and \(R(2)=0\) —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-first-oo-r-bound`,
  `isolated_oe_r_max_two`, `no_cycleMin_prefix_ooe_oe`).
- `OOEOOE` as a complete CycleMin word —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_ooeooe`). Internal-`E`
  next-square threshold. Not a prefix theorem.
- First-even overshoot; second-`OO` transport —
  **EXACT — LEAN VERIFIED**.
- `power_bound_word` —
  **EXACT — LEAN VERIFIED**.
- Last two-even leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**. Not reopened as a suffix table.
- Bunched-short / front overshoot / isolated-odd fibre —
  **PARK**. Frozen.

Project relationship: **extended**. The designated next question of
the promoted first-internal-`OO` branch.

## Branch budget

```text
Mathematical target     CycleMin(n, OOEOOE v) =>
                        FiniteProgress or existing obstruction
Novelty hypothesis      two minimal OOE blocks from the
                        CycleMin minimum create a new constraint
Falsifier               OOEOOE v stays >= n with no stronger
                        restriction than a generic OO; or the
                        second OOE resets the first surplus
Existing machinery      power_bound_word; no_cycleMin_ooeooe;
                        R(2)=0; first-even overshoot
Maximum Phase-0 scope   OOEOOE scale chain; square cell;
                        even/odd landing; no Lean;
                        no terminal-cell reopen
Promotion criterion     FiniteProgress from the prefix, or a
                        reusable two-OOE constraint
Stop criterion          generic square only; leftover table;
                        Z5 / length-11 / four-even;
                        finite census as the theorem
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(T_{OOEOOE}(n)<n^2\) whenever the itinerary follows —
  **EXACT — HUMAN PROOF**. `power_bound_word` gives
  \(x_6^{64}\le n^{81}\). Then \(n^2\le x_6\) implies
  \(n^{128}\le n^{81}\), impossible for \(n\ge 2\). The same
  comparison holds for `OOEOOOE` (\(256>243\)) and fails for
  \(b\ge 4\).
- even \(x_6\) forces \(T(x_6)<n\) —
  **EXACT — HUMAN PROOF**. \(x_6\le n^2-1\), so
  \(\lfloor\sqrt{x_6}\rfloor\le n-1\).
- \(\operatorname{CycleMin}(n,OOEOOE\,v)\) implies \(v\) begins
  with `O` —
  **EXACT — HUMAN PROOF**. Empty \(v\) is `no_cycleMin_ooeooe`.
  An even landing plus a next `E` drops below \(n\).
- \(\operatorname{CycleMin}(n,OOEOOE\,v)\Rightarrow
  \texttt{FiniteProgress}(n)\) —
  **REFUTED**. Odd landings exist: \(89\mapsto 291\),
  \(111\mapsto 385\).
- the second `OOE` is a strictly stronger increment than the
  first —
  **OBSERVATION** on \(13\le n<801\) (\(d_2>d_1\) on every
  follower; no reset). The *provable* floor remains
  \(x_6\ge x_3+1\).
- two generic `OO` squares already give the same ceiling —
  **REFUTED** as the named mechanism. The ceiling is the
  length-\(6\) envelope \(81<128\), not
  \((x_3+1)^2\) applied twice.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.minimal_ooe_corridor`
- Records: [juggler_minimal_ooe_corridor.md](../research/juggler_minimal_ooe_corridor.md),
  [juggler_minimal_ooe_corridor.json](../research/juggler_minimal_ooe_corridor.json)
- Tests: `tests/research/juggler_sequence/test_minimal_ooe_corridor.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that every `OOEOOE` prefix forces finite progress
is **REFUTED**. Permanent odd-landing witnesses:

\[
89\xrightarrow{\mathtt{OOEOOE}}291,
\qquad
111\xrightarrow{\mathtt{OOEOOE}}385.
\]

Both landings are odd and lie in \([n,n^2)\). The next letter is
`O`.

The hypothesis that the second `OOE` can reset the first surplus
is **REFUTED** in the scanned window: \(d_2>d_1\) on every
follower.

The stronger claims that remain false or unproved:

- “`OOEOOE` is an impossible CycleMin prefix” — false; odd
  landings continue.
- “\(b\ge 3\) is the same theorem” — only \(b=3\) inherits the
  square-cell gap; \(b\ge 4\) does not.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

None. Existing `Envelope.lean`, `CycleCore.lean`, and
`FirstInternalOO.lean` lemmas are cited, not rewritten. No
`no_cycleMin_prefix_ooeooe`. No `no_cycleMin_four_even`. No
`no_cycle_itinerary_length_eleven`. No `no_juggler_cycle`. Paper A is
unchanged.

## Results

Classification **MINIMAL_OOE_GREEN**.

If \(n\ge 2\) follows `OOEOOE`, then
\[
T_{OOEOOE}(n)<n^2.
\]
If that landing is even, the next even step is strictly below
\(n\). Therefore
\[
\operatorname{CycleMin}(n,\;OOEOOE\,v)
\;\Rightarrow\;
v\text{ begins with }O
\]
(after the already-excluded empty itinerary). The new constraint
created by the second `OOE` is not “the number is too large”.
It is the opposite: two minimal blocks still cannot reach the
even-contraction cell \(n^2\), so a safe even letter is
impossible and a CycleMin must continue with another odd.

On odd \(13\le n<801\): \(12\) followers, all below \(n^2\);
\(4\) even landings, all drop on the next `E`; \(8\) odd
landings. That window is not the theorem.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The odd-landing residual is treated in
[juggler_odd_ooe_landing.md](juggler_odd_ooe_landing.md).
Lean-package the square-cell ceiling. Do not reopen bunched-short
cells. Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`.

## Decision

**PROMOTE**. The square-cell ceiling is a parameterized theorem
about the minimal first-`OO` prefix, independent of the terminal
cluster. The strong FiniteProgress claim for every \(v\) is
false and is not claimed.

Best next question: after an odd `OOEOOE` landing, does the
forced next `O` produce finite progress or another `OOE`?

## Publication assessment

Status: `THEOREM`.

A named exact ceiling from `power_bound_word` on the length-\(6\)
word. Not a Juggler totality result and not a prefix-halt
theorem.
