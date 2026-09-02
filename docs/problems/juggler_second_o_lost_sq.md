# Juggler second `O` loses the square cell

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a length-11
cycle census, not an expanding-grammar reopen, not Paper B, not
escape-margin \(M\), and not a claim that every positive integer
reaches 1.

This is the leftover of
[juggler_oe_next_oo.md](juggler_oe_next_oo.md): after
\(1517\to 124475\), does the second `O` of the new `OO` still lie
below \(n^{2}\)?

## Problem

The CE spine has kept a square-cell gap through the third `OOE`,
the escaped-even `OE`, and the first `O` of a new `OO`. Does that
gap survive the second `O`?

## Exact statement

If \(\operatorname{MinimalNonTerm}(n)\) and \(n\) follows
`OOEOOEOOEOE`, then \(n\) follows `OOEOOEOOEOEOO`. Phase 0 asks:

1. whether \(T_{\mathtt{OOEOOEOOEOEOO}}(n)<n^{2}\) from a square
   gap — it does not, because \(19683>16384\);
2. whether \(T_{\mathtt{OOEOOEOOEOEOO}}(n)<n^{3}\) from
   \(19683<24576\);
3. whether \(1517\) realizes an odd landing in \([n^{2},n^{3})\).

Do not continue the letter-by-letter square chain. Do not prove
\(\neg\operatorname{EscapesToInfinity}\). Do not open a length-11
cycle census.

## Current literature

- CE next `O` after odd `OE` is odd and below \(n^{2}\) —
  **EXACT — LEAN VERIFIED** (`J-ce-oe-next-oo`).
- Another escaped even on that step —
  **REFUTED** (`J-oe-next-escaped-even`).
- Lost square / kept cube after `OOEOOOEO` —
  **EXACT — HUMAN PROOF** (`J-cyclemin-odd-oooe-next-o`), a
  different word.

Project relationship: **extended**. The CE square-cell chain
ends. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     After 1517 -> 124475, does the second
                        O still lie below n^2?
Novelty hypothesis      19683 > 16384 is the first lost square
                        on this spine; the cube survives
Falsifier               a square gap; or 1517 stays below n^2
                        with no cube statement
Existing machinery      next-O square; power_bound_word
Maximum Phase-0 scope   lost-square decide; cube envelope;
                        1517 corridor; stop the letter chain
Promotion criterion     a new exact cube envelope plus a
                        realized [n^2, n^3) landing
Stop criterion          another same-trap square transfer;
                        length-11 assembler; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- on a CE, `OOEOOEOOEOE` implies `follows OOEOOEOOEOEOO` —
  **EXACT — LEAN VERIFIED**
- the 13-letter word loses the square cell (\(19683>16384\)) —
  **EXACT — LEAN VERIFIED**
- \(T_{\mathtt{OOEOOEOOEOEOO}}(n)<n^{3}\) because \(19683<24576\) —
  **EXACT — LEAN VERIFIED**
- the second `O` still lies below \(n^{2}\) —
  **REFUTED** (\(1517\to 43916043\))
- no trajectory escapes — not claimed
- length-11 cycle itineraries are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.second_o_lost_sq`
- Records:
  [juggler_second_o_lost_sq.md](../research/juggler_second_o_lost_sq.md),
  [juggler_second_o_lost_sq.json](../research/juggler_second_o_lost_sq.json)
- Tests: `tests/research/juggler_sequence/test_second_o_lost_sq.py`
- Lean: lost-square decide and cube envelope in `Escape.lean`.
  Laboratory barrel only. No `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The second `O` stays below \(n^{2}\) is **REFUTED**:

\[
1517\xrightarrow{\mathtt{OOEOOEOOEOEOO}}43916043,
\]

with \(1517^{2}=2301289\le 43916043<1517^{3}\) and \(43916043\)
odd. The square gap is already absent: \(19683>16384\).

A following `E` would restore a square cell (\(19683<32768\)),
but \(1517\) does not take that `E`.

## Formalization

`Escape.lean` adds `wordOOEOOEOOEOEOO`,
`ooeooeooeoeoo_loses_square`,
`follows_ooeooeooeoeoo_image_lt_cube`, and
`minimal_ooeooeooeoeo_follows_o`. `FloorPower` and
`MinimalNonTerm` are not rewritten. No `sorry`. No
`no_juggler_escape`. Paper A is unchanged.

## Results

Classification **SECOND_O_LOST_SQ_GREEN**.

The second `O` is the first lost square-cell letter on this CE
spine. The cube envelope survives —
**EXACT — LEAN VERIFIED** (`J-ce-second-o-cube`). \(1517\)
realizes an odd landing in \([n^{2},n^{3})\) — **REFUTED** as
“still below \(n^{2}\)” (`J-second-o-below-square`).

This is not a halt theorem and not a length-11 cycle census.

## Open questions

After an odd landing in \([n^{2},n^{3})\), is there a CE-capable
constraint on the next letter other than another one-step
envelope? Do not resume the letter-by-letter square chain.

## Decision

**PROMOTE** the lost-square / cube split and the \(1517\)
corridor. **REFUTE** that the second `O` stays below \(n^{2}\).
Stop the square-cell letter chain. Do not claim that escape is
impossible.

Best next question: after an odd cube-corridor landing such as
\(1517\to 43916043\), is there a unifying CE-capable invariant,
or only another one-step envelope?

## Publication assessment

Status: `EXPLORATORY`.

The square-cell chain ends with a cube leftover. Not a paper
candidate and not a Juggler totality result.
