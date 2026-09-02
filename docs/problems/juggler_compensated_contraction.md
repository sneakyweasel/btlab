# Juggler defect-compensated contraction

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can a non-monochrome realized itinerary with formal drift \(3^o>2^k\) still
contract because its floor-envelope deficit exceeds the formal gap
\(n^{3^o}-n^{2^k}\)?

## Exact statement

For a realized itinerary \(w\) of length \(k\) with \(o=\#O(w)\), write

\[
\Delta_w(n)=n^{3^o}-T_w(n)^{2^k},\qquad
G_w(n)=n^{3^o}-n^{2^k}.
\]

If \(3^o>2^k\), does \(\Delta_w(n)>G_w(n)\) ever occur, and does that
force \(T_w(n)<n\)? In particular, for the shortest mixed
positive-drift words \(OOE\), \(OEO\), and \(EOO\), which starts
contract?

This is a local arithmetic question. It is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Phase-17 (`juggler_power_itineraries`): weak envelope
  \(T_w(n)^{2^k}\le n^{3^o}\) **EXACT — LEAN VERIFIED**. Formal
  contraction uses only \(3^o<2^k\).
- Phase-19 (`juggler_envelope_defect`): first-defect bound
  \(\Delta\ge\delta_j\) **EXACT — LEAN VERIFIED**.
- Phase-20 (`juggler_defect_sharpness`): \(\Delta=\delta_j\) iff an
  exact even suffix **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The one-sided envelope does not
decide direction when the formal exponent points upward.

## Branch budget

```text
Mathematical target     Can a mixed itinerary with 3^o > 2^k still
                        contract because floor defect overcomes
                        the formal gap?
Novelty hypothesis      A shortest mixed positive-drift family
                        contracts, or that family is obstructed
Falsifier               No contraction and no obstruction; or a
                        first-defect-only certificate that never
                        fires and is treated as a theorem
Existing machinery      PowerBound, powerDeficit, localDefect,
                        first-defect sharpness
Maximum Phase-0 scope   Search OOE/OEO/EOO; first-defect vs G;
                        Lean certificate or EOO classification
Promotion criterion     A verified compensated-contraction family
                        or a sharp obstruction for the shortest
                        mixed positive-drift words
Stop criterion          Lower-envelope theory; PowerHeight;
                        recursive defect datatype; engine edits;
                        termination claim; parked OE^s unless
                        forced
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Compensated-contraction certificate
  \(\Delta>G\Rightarrow T_w(n)<n\) —
  **EXACT — LEAN VERIFIED**
- `EOO` contracts iff \(n\in\{2,12,14\}\) —
  **EXACT — LEAN VERIFIED**
- First local defect never exceeds \(G\) for \((k,o)=(3,2)\) —
  **EXACT — LEAN VERIFIED**
- First-defect-only compensation — **REFUTED** on every realized
  `EOO` start (\(n=2\): \(\delta_E=1<256=G\))
- `OOE` / `OEO` never contract — **COMPUTATIONALLY VERIFIED** on
  the scanned window; not a Lean obstruction
- Lower power envelope — not added
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.compensated_contraction`
- Records: [juggler_compensated_contraction.md](../research/juggler_compensated_contraction.md),
  [juggler_compensated_contraction.json](../research/juggler_compensated_contraction.json)
- Tests: `tests/research/juggler_sequence/test_compensated_contraction.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- First-defect sufficiency \(\delta_j>G_w(n)\) fails at every
  `EOO` witness: \(n=2\), \(\delta_E=1\), \(G=256\); \(n=12\),
  \(\delta_E=3\); \(n=14\), \(\delta_E=5\).
- `EOO` at \(n=10\) realizes the same word and expands
  (\(T^3(10)=11\)).

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `power_bound_compensated_contracts` /
  `power_bound_compensated_contracts_follows`
- `itineraryEOO` / `wordOOE` / `wordOEO` and `follows` wrappers
- `floorPower_eoo_contracts_iff`
- `floorPower_eoo_two_contracts` / `_twelve_` / `_fourteen_`
- `eoo_first_defect_lt_formal_gap`
- `floorPower_eoo_two_deficit_gt_gap`

No `PowerHeight`. No `sorry`. No `mixed_word_power_lt`. No ledger
row. Existing `PowerBound` and first-defect theorems are unchanged.

## Results

Classification **COMPENSATED_CONTRACTION_FOUND**.

`EOO` is a formally expanding mixed itinerary (\(9>8\)) that nevertheless
contracts, and only at \(n\in\{2,12,14\}\). The reusable certificate
says that any deficit larger than the formal gap forces contraction.
The first local defect never supplies that margin for
\((k,o)=(3,2)\): compensation uses later odd steps, not
\(\Delta=\delta_j\).

`OOE` and `OEO` produced no contraction on the scanned odd window.
That is not a Lean obstruction.

This is not a termination theorem and not a lower-envelope theory.

## Open questions

Do `OOE` and `OEO` never contract, or is there a large odd start?
Is there an infinite mixed positive-drift family that contracts?

## Decision

**PROMOTE** the certificate and the finite `EOO` classification.
Record `COMPENSATED_CONTRACTION_FOUND`. Do not register an attack.
Do not claim termination. Do not open a lower-envelope theory. Do
not reopen the parked odd-start \(OE^s\) question.

Best next question: do `OOE` and `OEO` never contract, or is there
an infinite mixed positive-drift contraction family?

## Publication assessment

Status: `EXPLORATORY`. A local finite-itinerary direction lemma, not a
paper candidate and not a Juggler totality result.
