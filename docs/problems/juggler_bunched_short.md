# Juggler bunched-short last-cluster residual

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a \(Z_5\)
family, not a length-11 assembler, not a four-even leftover cell,
and not a claim that every positive integer reaches 1.

## Problem

After the last two-even leftover and the last three-even bunched
leftover are excluded after an arbitrary prefix, does the same
leftover-suffix path table exclude the bunched-short residual
\(a<a_{\min}\)?

## Exact statement

A bunched-short leftover is \(O^a\) plus one of the seven mixed
tails EEE, EOEE, EOOEE, EOOOEE, EEOE, EOEOE, EOOEOE, with
\(a<a_{\min}\) for that tail. Write \(y\) for a leftover start.
The leftover-suffix method asks whether any \(y\) follows the
short leftover and lands in \([12,y]\).

It does. Witnesses below \(256\) include

\[
129\xrightarrow{\mathrm{OOOOOEEE}}100,\qquad
81\xrightarrow{\mathrm{OOOEOEE}}16.
\]

There are \(18\) such returns for \(2\le y<256\), and none of
those short leftovers overshoot \(y\). Isolated-odd bunched-short
shapes with \(e\ge 5\) exist in the expanding window
\(e=5,6\), \(o=7..14\).

A return \(y\to n\) is not a `CycleMin`. It only kills the
leftover-suffix seal. The \(e=4\) short-first-gap remainder is
already **PARK** as a four-even cell. This branch does not reopen
it, does not write \(Z_5\), and does not assemble length 11.

## Current literature

- Last-cluster split —
  **EXACT — HUMAN PROOF** (`J-cyclemin-last-cluster`). Class 4
  is the bunched-short residual.
- Last two-even leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**.
- Last three-even bunched leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**. Those theorems start at
  \(a\ge a_{\min}\).
- First-E at \(e=4\) —
  **REPARAMETERIZATION** / **CLOSE**. Not reopened.
- Four-even short-first-gap cells —
  **PARK**. Not reopened as \(Z_5\).
- Necklace slack —
  **REFUTED**. Not pinned here.

Project relationship: **extended**. The residual named by the
last-cluster split, tested as a leftover-suffix.

## Branch budget

```text
Mathematical target     Does the leftover-suffix path table
                        seal CycleMin n (u ++ short leftover)?
Novelty hypothesis      short leftovers never return into [12,y]
Falsifier               a return 12 <= n <= y
Existing machinery      prefix bunched; last-cluster split;
                        CycleMin n>=12
Maximum Phase-0 scope   path census; window split; no Lean,
                        no Z5, no length-11
Promotion criterion     Lean exclusion or a new exact inequality
                        that is not a leftover cell
Stop criterion          hits at n>=12; leftover method fails;
                        no new cell
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- leftover-suffix path table seals \(a<a_{\min}\) —
  **REFUTED** (18 returns with \(12\le n\le y<256\))
- short leftovers overshoot \(y\) below \(256\) —
  **REFUTED** (0 overshoots)
- isolated-odd bunched-short shapes with \(e\ge 5\) exist —
  **EXACT — HUMAN PROOF** on the expanding window
- \(e=4\) short-first-gap is a four-even cell —
  already **PARK**; not reopened
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.bunched_short`
- Records: [juggler_bunched_short.md](../research/juggler_bunched_short.md),
  [juggler_bunched_short.json](../research/juggler_bunched_short.json)
- Tests: `tests/research/juggler_sequence/test_bunched_short.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The leftover-suffix seal for bunched-short is **REFUTED**.
Permanent witnesses:

- `OOOOOEEE`: \(129\to 100\), \(209\to 159\)
- `OOOEOEE`: \(81\to 16\), \(87\to 16\)
- `OOEOOEE`: \(69\to 14\), \(109\to 19\)

The stronger claims that remain false or unproved:

- “short leftovers behave like expanding leftovers” — false;
  they return, they do not overshoot.
- “every bunched-short \(e\ge 5\) word has an internal `OO`” —
  false; 96 isolated-odd shapes at \(e=5\) in the expanding
  window.
- “every last-cluster class is now excluded” — false.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

None. `PrefixBunched.lean` is not rewritten to short \(a\).
No `no_cycleMin_four_even`. No `no_cycleMin_five_even`. No
`no_cycle_itinerary_length_eleven`. No `no_juggler_cycle`. Paper A
is unchanged.

## Results

Classification **BUNCHED_SHORT_PARK**.

The leftover-suffix method that excluded last-cluster classes
2 and 3 does not exclude class 4. Short leftovers return into
\([12,y]\). Isolated-odd \(e\ge 5\) shapes exist. The \(e=4\)
remainder stays the parked four-even cell. This is not \(Z_5\),
not a length-11 census, and not a halt theorem.

## Open questions

The front / predecessor-cell attack is a separate parked
branch
([juggler_bunched_short_front.md](juggler_bunched_short_front.md)).
The first-even-overshoot plus later-`OO` attack is also parked
([juggler_front_overshoot.md](juggler_front_overshoot.md)).
The exact-return attack \(S_{b,c}(y)=n\) is also parked
([juggler_bunched_short_return.md](juggler_bunched_short_return.md)).
The isolated-odd prefix attack is **CLOSE**
([juggler_isolated_odd_return.md](juggler_isolated_odd_return.md)).
Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`. Do not reopen four-even cells.

## Decision

**PARK**. The leftover-suffix path table is the wrong tool for
the residual. The residual remains bunched-short last cluster,
now with an explicit return family. Do not claim that every
cycle itinerary is impossible.

Best next question: answered in
[juggler_bunched_short_front.md](juggler_bunched_short_front.md),
[juggler_front_overshoot.md](juggler_front_overshoot.md),
[juggler_bunched_short_return.md](juggler_bunched_short_return.md),
and [juggler_isolated_odd_return.md](juggler_isolated_odd_return.md).

## Publication assessment

Status: `EXPLORATORY`.

A named residual plus a refuted method. Not a paper candidate
and not a Juggler totality result.
