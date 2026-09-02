# Juggler next letter after odd `OE`

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a length-11
cycle census, not an expanding-grammar reopen, not Paper B, not
escape-margin \(M\), and not a claim that every positive integer
reaches 1.

This is the leftover of
[juggler_escaped_even.md](juggler_escaped_even.md): after the odd
`OE` landing \(1517\to 2493\), is the next image odd (another
`OO`) or another escaped even?

## Problem

On a CE-shaped odd `OE` landing in \([n,n^{2})\), the next letter
is `O`. Does that image stay below \(n^{2}\)? If it is even, it
drops. If it is odd, another `OO` starts.

## Exact statement

If \(\operatorname{MinimalNonTerm}(n)\) and \(n\) follows
`OOEOOEOOEOE`, then \(n\) follows `OOEOOEOOEOEO`. Phase 0 asks:

1. whether \(T_{\mathtt{OOEOOEOOEOEO}}(n)<n^{2}\) from \(6561<8192\);
2. whether an even image of that next `O` is descent on a CE;
3. whether another escaped even (\(q\ge n^{2}\) even) can occur on
   this step.

Do not prove \(\neg\operatorname{EscapesToInfinity}\). Do not open
a length-11 cycle census. Do not reopen the first-`OOO` language
envelope.

## Current literature

- CE `OE` landing after a third `OOE` is odd and below \(n^{2}\) —
  **EXACT — LEAN VERIFIED** (`J-ce-escaped-even-oe-preimage`).
- Every escaped even drops —
  **REFUTED** (`J-escaped-even-always-drops`; witness \(1517\)).
- \(429\) dies by even `OE` landing —
  **COMPUTATIONALLY VERIFIED**.

Project relationship: **extended**. The CE trap is continued one
`O` past the odd `OE` leftover. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     After 1517 -> 2493, is the next image
                        odd (another OO) or another escaped even?
Novelty hypothesis      6561 < 8192 keeps the next O below n^2,
                        so another escaped even is impossible
Falsifier               a next image >= n^2; or only the previous
                        OE trap restated
Existing machinery      OE square cell; power_bound_word;
                        even_floorPower_lt_iff
Maximum Phase-0 scope   Lean 12-letter square + CE even-trap;
                        1517/7653 scan
Promotion criterion     a new CE-capable envelope that forbids
                        another escaped even on this step
Stop criterion          length-11 assembler; first-OOO language;
                        expanding-grammar; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- on a CE, `OOEOOEOOEOE` implies `follows OOEOOEOOEOEO` —
  **EXACT — LEAN VERIFIED**
- \(T_{\mathtt{OOEOOEOOEOEO}}(n)<n^{2}\) because \(6561<8192\) —
  **EXACT — LEAN VERIFIED**
- a CE next image after the odd `OE` is odd —
  **EXACT — LEAN VERIFIED**
- another escaped even occurs on this step —
  **REFUTED** (square gap forbids \(q\ge n^{2}\))
- no trajectory escapes — not claimed
- length-11 cycle itineraries are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.oe_next_oo`
- Records: [juggler_oe_next_oo.md](../research/juggler_oe_next_oo.md),
  [juggler_oe_next_oo.json](../research/juggler_oe_next_oo.json)
- Tests: `tests/research/juggler_sequence/test_oe_next_oo.py`
- Lean: `OOEOOEOOEOEO` square cell and CE even-trap in
  `Escape.lean`. Laboratory barrel only. No `sorry`. No halt
  theorem. No length-11 census.

## Conjectures

None opened.

## Counterexamples

Another escaped even on this step is **REFUTED** by the square
gap \(6561<8192\). No scanned odd-`OE` start has next image
\(\ge n^{2}\).

\(1517\) realizes another `OO`:

\[
1517\xrightarrow{\mathtt{OOEOOEOOEOEO}}124475,
\]

with \(2493\le 124475<1517^{2}\) and \(124475\) odd.

\(7653\) is the even-image drop, not a CE leftover:

\[
7653\xrightarrow{\mathtt{OOEOOEOOEOEO}}1663784
\xrightarrow{\mathtt{E}}\lfloor\sqrt{1663784}\rfloor<7653.
\]

## Formalization

`Escape.lean` adds `wordOOEOOEOOEOEO`, the square envelope,
`minimal_ooeooeooeoe_follows_o`, and
`minimal_ooeooeooeoeo_not_even`. `FloorPower` and
`MinimalNonTerm` are not rewritten. No `sorry`. No
`no_juggler_escape`. No `no_cycle_itinerary_length_eleven`. Paper A
is unchanged.

## Results

Classification **OE_NEXT_OO_GREEN**.

A CE that follows an odd `OE` after a third `OOE` follows the
next `O`, and that image is odd and below \(n^{2}\) —
**EXACT — LEAN VERIFIED** (`J-ce-oe-next-oo`). Another escaped
even is impossible on this step — **REFUTED**
(`J-oe-next-escaped-even`). \(1517\) starts another `OO`.
\(7653\) drops on an even image.

This is not a halt theorem and not a length-11 cycle census.

## Open questions

Answered in
[juggler_second_o_lost_sq.md](juggler_second_o_lost_sq.md): the
second `O` loses the square cell and \(1517\) lands odd in
\([n^{2},n^{3})\). Do not open a length-11 assembler.

## Decision

**PROMOTE** the CE next-`O` square trap. **REFUTE** another
escaped even on this step. Do not claim that escape is
impossible.

Best next question: answered in
[juggler_second_o_lost_sq.md](juggler_second_o_lost_sq.md).

## Publication assessment

Status: `EXPLORATORY`.

One more transferred envelope that closes a named leftover.
Not a paper candidate and not a Juggler totality result.
