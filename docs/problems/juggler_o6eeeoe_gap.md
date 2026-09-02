# Juggler \(O^6\mathrm{EEEOE}\) +1-chain gap

Status: **THEOREM**

Standalone application phase on the unique \((3,1)\) even-run leftover
`OOOOOOEEEOE`. It is **not** a Research Engine control-layer
experiment, not a length-11 census, not a \(Z_5\) family, and not a
claim that every positive integer reaches 1.

## Problem

Does every six-odd image sit at or above the `EEEOE` inverse cell of
\(n\), so that `OOOOOOEEEOE` is excluded by the same \(+1\)-chain
that killed \(O^7\mathrm{EEEE}\), rather than by leftover \(N_0=4.38\cdot 10^8\)?

## Exact statement

If \(n\ge 2\) follows \(O^6\), write \(z=T^6(n)\). The inverse of
\(n\) under `EEEOE` is contained in

\[
z<(v+1)^8,\qquad v^3<(n+1)^4.
\]

Then \(z\) lies outside that cell, so `OOOOOOEEEOE` is not a cycle
word. Lean independently has `no_cycle_itinerary_ooooooeeeoe` via
the CycleMin-fudge unique-rotation upgrade. The \(T^6\) versus
EEEOE cell inequalities remain human.

## Current literature

- \(O^7\mathrm{EEEE}\) +1-chain —
  **EXACT — LEAN VERIFIED**
  (`o7_image_ge_succ_pow16`, `no_cycle_itinerary_oooooooeeee`).
- Four-even short-first-gap \(Z_4\) —
  **PARK**. This shape first fires at \(437\,599\,552\).
- Amplify versus surplus —
  **REFUTED** / **CLOSE**.
- Length-11 rotation / internal-E —
  **REFUTED** / **CLOSE**.
- The five `(1,3)` leftovers —
  not opened here.

Project relationship: **extended**. One even-run signature, one
word.

## Branch budget

```text
Mathematical target     Does the O^7 +1-chain kill the unique
                        (3,1) leftover OOOOOOEEEOE?
Novelty hypothesis      T^6 sits above the EEEOE cell at the
                        first O^6 start, not at leftover N0
Falsifier               an O^6 image inside the EEEOE cell, or
                        the chain still needs n ~ 10^8
Existing machinery      (T+1)^2 > x^3; cycle_trailing_evens;
                        O^7 +1-chain; 30-word list
Maximum Phase-0 scope   one word OOOOOOEEEOE; CycleMin Lean
                        corollary; no (1,3) family, no
                        29-word scan
Promotion criterion     a proof covering every O^6 start
Stop criterion          the bound still needs a huge pin;
                        a 29-word scan; Z5; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- no six-odd run below \(163\) —
  **COMPUTATIONALLY VERIFIED**
- \(n^{1995}<(n+1)^{1266}(T^6(n)+1)^{64}\) on an \(O^6\) run —
  **EXACT — HUMAN PROOF**
- \(n^{1995}>(n+1)^{1970}\) for every \(n\ge 25\) —
  **EXACT — HUMAN PROOF**
- \((v_{\max}+1)^8<(n+1)^{11}\) for every \(n\ge 16\), and
  \(898^8<164^{11}\) at the first \(O^6\) start —
  **EXACT — HUMAN PROOF**
- \(T^6(n)\ge(v_{\max}+1)^8\) on every \(O^6\) start —
  **EXACT — HUMAN PROOF**
- `OOOOOOEEEOE` is not a cycle itinerary —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_ooooooeeeoe`);
  the \(T^6\) versus EEEOE cell argument is
  **EXACT — HUMAN PROOF**
- leftover cell for this shape fires at \(437\,599\,552\) —
  **COMPUTATIONALLY VERIFIED**
- no cycle of length 11 — not claimed
- the five `(1,3)` words die — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.o6eeeoe_gap`
- Records: [juggler_o6eeeoe_gap.md](../research/juggler_o6eeeoe_gap.md),
  [juggler_o6eeeoe_gap.json](../research/juggler_o6eeeoe_gap.json)
- Tests: `tests/research/juggler_sequence/test_o6eeeoe_gap.py`
- Finite checks: first \(O^6\) at \(163\); \(170\) starts with
  \(n<10^4\), all above the cell, closest ratio \(37.3\); leftover
  \(N_0=437\,599\,552\).
- Lean cycle-itinerary corollary: `no_cycle_itinerary_ooooooeeeoe` in
  `CycleMinFudge.lean`. The cell inequalities are not Lean.
  Paper A is unchanged.

## Conjectures

None opened.

## Counterexamples

None to the gap. The stronger claims that fail:

- “this shape needs leftover \(N_0\sim 4\cdot 10^8\)” — the exact
  successor cell fires at the first \(O^6\) start.
- “this is a length-11 census” — one word.
- “the five `(1,3)` words are included” — they are not.

## Formalization

`no_cycle_itinerary_ooooooeeeoe` and `no_cycleMin_ooooooeeeoe` live
in `Problems/Juggler/CycleMinFudge.lean`. The specialised
\(T^6\) versus EEEOE cell inequalities are not Lean.
`SmallCycleCensus.lean` still assembles only through length
seven. No `no_cycle_itinerary_length_eleven`. No `sorry`. No halt
theorem. Paper A is unchanged.

## Results

Classification **O6EEEOE_GAP_PROVED**.

On an \(O^6\) run the exact cells \(x_k^3<(x_{k+1}+1)^2\) and
\(x_k\ge n\) compose to
\(n^{1995}<(n+1)^{1266}(T^6(n)+1)^{64}\). The `EEEOE` inverse is
\(z<(v+1)^8\) with \(v^3<(n+1)^4\). For \(n\ge 25\),
\(n^{1995}>(n+1)^{1970}\) and \((v_{\max}+1)^8<(n+1)^{11}\), so
\(T^6(n)\) lies above the cell. No \(n<163\) follows \(O^6\).

The leftover envelope first fires at \(437\,599\,552\). It is not
used.

## Open questions

The five `(1,3)` leftovers were taken up by
[juggler_one_three_eee_gap](juggler_one_three_eee_gap.md).
Do not scan the remaining twenty-three automatically. Do not
write \(Z_5\).

## Decision

**PROMOTE** the one-word \(+1\)-chain. The leftover \(4\)-fudge was
again the threshold obstruction. This is not a halt result and not
an exclusion of the other twenty-eight words.

Best next question: the \(a_0\ge 8\) tails, not a length-11
census.

## Publication assessment

Status: `THEOREM`. A one-word exact exclusion by an elementary
\(+1\)-chain, not a paper candidate and not a Juggler totality
result.
