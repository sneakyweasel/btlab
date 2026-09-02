# Juggler escaped even after third `OOE`

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a length-11
cycle census, not an expanding-grammar reopen, not Paper B, not
escape-margin \(M\), and not a claim that every positive integer
reaches 1.

This is the leftover of
[juggler_third_residual.md](juggler_third_residual.md): after a
third-`OOE` landing such as \(429\to 5595\) with even
\(T(y)\ge n^{2}\), is there a CE-capable constraint on that
escaped even?

## Problem

On a CE-shaped completed third `OOE`, the next letter is `O`. If
that image is even and already \(\ge n^{2}\), does the following
`OE` landing still drop, or can it survive?

## Exact statement

If \(\operatorname{MinimalNonTerm}(n)\) and \(n\) follows
`OOEOOEOOE`, then \(n\) follows `OOEOOEOOEO`. Phase 0 asks:

1. whether \(T_{\mathtt{OOEOOEOOEOE}}(n)<n^{2}\) from \(2187<4096\);
2. whether an even landing of that `OE` is descent on a CE;
3. whether every escaped even therefore drops, or an odd `OE`
   landing can stay in \([n,n^{2})\).

Do not prove \(\neg\operatorname{EscapesToInfinity}\). Do not open
a length-11 cycle census. Do not reopen
`EXPANDING_GRAMMAR_IS_PERSISTENCE` or the first-`OOO` language
envelope.

## Current literature

- CE third `OOE` landing is odd and below \(n^{2}\) —
  **EXACT — LEAN VERIFIED** (`J-ce-third-residual-preimages`).
- Late `OE` after \(k\ge 3\) `OOE` blocks need not drop on the
  first even — **REFUTED** as a CycleMin claim
  (`J-cyclemin-ooo-inevitable`; witnesses \(365\), \(429\)).
- `OOEOOEOOEOEE` contracts —
  **EXACT — HUMAN PROOF** (\(2187<4096\)), already used as a
  recovery word on a different corridor.
- Infinite PE concatenation is the CE leftover —
  **REPARAMETERIZATION** (`J-expanding-concat-is-ce`).

Project relationship: **extended**. The CE trap is continued one
`OE` past the escaped even. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     After a 429-type third OOE with even
                        T(y) >= n^2, is there a CE-capable
                        constraint on that escaped even?
Novelty hypothesis      the OE landing stays below n^2, so even
                        w is descent; odd w may survive
Falsifier               an OE landing >= n^2; or only the
                        first_ooo late-OE observation restated
Existing machinery      third-OOE square; power_bound_word;
                        even_floorPower_lt_iff
Maximum Phase-0 scope   Lean 11-letter square + CE even-trap;
                        429/1517 scan; no length-11 census
Promotion criterion     a new CE-capable envelope on the escaped
                        even, plus a decided leftover
Stop criterion          length-11 assembler; first-OOO language
                        reopen; expanding-grammar; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- on a CE, `OOEOOEOOE` implies `follows OOEOOEOOEO` —
  **EXACT — LEAN VERIFIED**
- \(T_{\mathtt{OOEOOEOOEOE}}(n)<n^{2}\) because \(2187<4096\) —
  **EXACT — LEAN VERIFIED**
- a CE `OE` landing after a third `OOE` is odd —
  **EXACT — LEAN VERIFIED**
- every escaped even drops —
  **REFUTED** (\(1517\))
- `OOEOOEOOEOEE` is contracting —
  **EXACT — HUMAN PROOF**
- no trajectory escapes — not claimed
- length-11 cycle itineraries are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.escaped_even`
- Records: [juggler_escaped_even.md](../research/juggler_escaped_even.md),
  [juggler_escaped_even.json](../research/juggler_escaped_even.json)
- Tests: `tests/research/juggler_sequence/test_escaped_even.py`
- Lean: `OOEOOEOOEOE` square cell and CE even-trap in
  `Escape.lean`. Laboratory barrel only. No `sorry`. No halt
  theorem. No length-11 census.

## Conjectures

None opened.

## Counterexamples

The escaped even of \(429\) is **not** a CE leftover. It dies by
the even-`OE` trap:

\[
429\xrightarrow{\mathtt{OOEOOEOOEOE}}646
\xrightarrow{\mathtt{E}}25.
\]

Here \(T(5595)=418504\ge 429^{2}\) is the escaped even, but
\(646<429^{2}\) is even, so the next `E` drops. The same word
`OOEOOEOOEOEE` is formally contracting.

Uniform drop of every escaped even is **REFUTED**:

\[
1517\xrightarrow{\mathtt{OOEOOEOOEOE}}2493.
\]

Here \(T(33811)=6217088\ge 1517^{2}\) is even, but the `OE`
landing \(2493\) is odd and lies in \([1517,1517^{2})\).

\(365\) is not this branch: its third-`OOE` landing \(4447\) is
odd-odd, so the next image is odd.

## Formalization

`Escape.lean` adds `wordOOEOOEOOEO` / `wordOOEOOEOOEOE`, the
square envelope, `minimal_ooeooeooe_follows_o`, and
`minimal_ooeooeooeoe_not_even_landing`. `FloorPower` and
`MinimalNonTerm` are not rewritten. No `sorry`. No
`no_juggler_escape`. No `no_cycle_itinerary_length_eleven`. Paper A
is unchanged.

## Results

Classification **ESCAPED_EVEN_GREEN**.

A CE that follows a third `OOE` follows the next `O`. The
escaped-even `OE` lands below \(n^{2}\); an even landing is
descent — **EXACT — LEAN VERIFIED** (`J-ce-escaped-even-oe-preimage`).
So on a CE an escaped even forces an odd landing in
\([n,n^{2})\). That leftover is realized by \(1517\). The
witness \(429\) is the even-landing drop, not a CE survivor.
Uniform drop of every escaped even is **REFUTED**
(`J-escaped-even-always-drops`).

This is not a halt theorem and not a length-11 cycle census.

## Open questions

Answered in [juggler_oe_next_oo.md](juggler_oe_next_oo.md): the
next `O` stays below \(n^{2}\); another escaped even is
impossible; \(1517\) starts another `OO`. Do not open a
length-11 assembler. Do not reopen the first-`OOO` language
envelope.

## Decision

**PROMOTE** the CE `OE` square trap on the escaped even.
**REFUTE** that every escaped even drops. Do not claim that
escape is impossible. Do not claim a length-11 census.

Best next question: answered in
[juggler_oe_next_oo.md](juggler_oe_next_oo.md).

## Publication assessment

Status: `EXPLORATORY`.

One more transferred envelope plus a decided leftover. Not a
paper candidate and not a Juggler totality result.
