# Juggler isolated-odd prefixes versus the exact short-tail fibre

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
leftover-suffix path table, not a raise-above invariant, not a
preimage enumerator, not a \(Z_5\) family, not a length-11
assembler, not a four-even leftover cell, and not a claim that
every positive integer reaches 1.

## Problem

After exact short-cluster closure is the \((\varepsilon,\eta)\)
`EE` fibre (and the last-odd layer for \(c=1\)), can an
isolated-odd `CycleMin` prefix — no `OO` between the first even
and the last cluster — land in that fibre while staying
\(\ge n\)?

## Exact statement

Write a bunched-short word as
\[
O^{a_0}EO^{a_1}\cdots EO^{a_{e-3}}EO^bEO^cE
\]
with \(a_0\ge 2\), \(e\ge 5\), \((b,c)\in S\), and
\(a_{e-3}<a_{\min}(b,c)\). The prefix is isolated-odd when
\[
a_i\in\{0,1\}\qquad\text{for }1\le i\le e-3.
\]
Let \(y\) be the state at the last-cluster entrance. The
Phase-0 question is whether
\[
T_{O^bEO^cE}(y)=n
\]
can hold on a path that stays \(\ge n\).

The \(e=4\) isolated-odd remainder is the parked four-even
short-gap cell and is not reopened.

## Current literature

- `EE` closure identity —
  **EXACT — HUMAN PROOF** (`J-cyclemin-short-ee-compose`).
- Defect obstruction —
  **REFUTED** (`J-cyclemin-short-defect-obstruction`).
- Isolated-odd prefixes with no `OO` at all —
  **REPARAMETERIZATION** / **CLOSE**
  (`J-cyclemin-iso-odd-return`). This branch is the leftover
  \(a_0\ge 2\) case.
- Isolated-odd bunched-short shapes exist at \(e=5,6\) —
  **EXACT — HUMAN PROOF** on the expanding window.
- First-even overshoot; `OE` contracts —
  **EXACT — LEAN VERIFIED**.
- Four-even short-gap —
  **PARK**. Not reopened.
- Front overshoot plus later `OO` —
  **PARK**. Not reopened.

Project relationship: **extended**. The designated next
question of the parked defect branch.

## Branch budget

```text
Mathematical target     Can an isolated-odd CycleMin prefix
                        land in the exact short-tail fibre?
Novelty hypothesis      isolated-odd transport cannot hit
                        the fibre while staying >= n
Falsifier               one isolated-odd CycleMin-shaped
                        word with exact short-tail return
Existing machinery      EE identity; first-even overshoot;
                        oe_block_contracts
Maximum Phase-0 scope   e=5,6 isolated-odd words; exact
                        tail return; no Lean
Promotion criterion     Lean CycleMin + isolated-odd +
                        short tail => bot
Stop criterion          four-even; named words; leftover
                        cell; Z5; length-11
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- isolated-odd \(e\ge 5\) prefixes land in the exact fibre
  while staying \(\ge n\) —
  **REFUTED** on \(13\le n<151\) (0 fibre hits, 0
  `CycleMin` returns)
- those prefixes can follow without dropping below \(n\) —
  **REFUTED** in the same window (34 follows, all
  \(\mathrm{path\_min}<n\))
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.isolated_odd_fibre`
- Records: [juggler_isolated_odd_fibre.md](../research/juggler_isolated_odd_fibre.md),
  [juggler_isolated_odd_fibre.json](../research/juggler_isolated_odd_fibre.json)
- Tests: `tests/research/juggler_sequence/test_isolated_odd_fibre.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that an isolated-odd prefix can stay in the
`CycleMin` region through a short tail is **REFUTED** in the
scanned window. The 34 follows all contract below \(n\) after
the first-even overshoot. Samples:

\[
25\xrightarrow{\mathtt{OOOEEOEOEE}}\text{min }2,
\qquad
81\xrightarrow{\mathtt{OOOEOEEEE}}\text{min }2.
\]

The second extends the parked leftover-suffix return
\(81\to 16\) on \(\mathtt{OOOEOEE}\) and then drops further.
Neither is a `CycleMin`.

The stronger claims that remain false or unproved:

- “every isolated-odd \(e\ge 5\) word follows” — false; only
  \(a_0\in\{2,3,5\}\) followed.
- “every last-cluster class is now excluded” — false; the
  window is finite and \(e=4\) is parked.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

None. `oe_block_contracts` is cited, not rewritten. No
`no_cycleMin_isolated_odd`. No `no_cycleMin_four_even`. No
`no_cycle_itinerary_length_eleven`. No `no_juggler_cycle`. Paper A
is unchanged.

## Results

Classification **ISO_FIBRE_PARK**.

588 isolated-odd bunched-short words with \(e\in\{5,6\}\) and
\(2\le a_0\le 8\). On odd \(13\le n<151\): 34 follows, 0
paths stay \(\ge n\), 0 exact fibre landings, 0 `CycleMin`
returns. Follows occur only at \(a_0\in\{2,3,5\}\). After the
first-even overshoot the isolated `OE`/`EE` middle collapses
below \(n\), so the entrance is far below the `EE` fibre. The
\(e=4\) case remains the parked four-even cell.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The bunched-short residual is now parked in every named
subattack. Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`. Do not reopen four-even cells.

## Decision

**PARK**. The isolated-odd fibre is empty in a finite window,
and every follow drops below \(n\). That is not a Lean
transport theorem. Do not claim that every cycle itinerary is
impossible.

Best next question: none on this line. The \(e=4\) isolated-odd
remainder is the parked four-even cell. Do not open it.

## Publication assessment

Status: `EXPLORATORY`.

A named empty window plus contraction diagnostics. Not a
paper candidate and not a Juggler totality result.
