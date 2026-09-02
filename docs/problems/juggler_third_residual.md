# Juggler third residual after forced `OO`

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not an
expanding-grammar reopen, not Paper B, not escape-margin \(M\), and
not a claim that every positive integer reaches 1.

This is the leftover of
[juggler_expanding_residual_concat.md](juggler_expanding_residual_concat.md)
and [juggler_non_escape.md](juggler_non_escape.md): after the CE
`OOEOOE` trap forces `OOEOOEOO`, does the completed third residual
drop below \(n\) or remain a persistent expanding block?

## Problem

On a CE-shaped `OOEOOE` follower, classify the residual that starts
at \(x=T_{\mathtt{OOEOOE}}(n)\) after the forced extra `OO`.

## Exact statement

If \(\operatorname{MinimalNonTerm}(n)\) and \(n\) follows `OOEOOE`,
then \(n\) follows `OOEOOEOO`. Phase 0 asks:

1. whether \(T_{\mathtt{OOEOOEOO}}(n)<n^{3}\) from \(729<768\);
2. whether a completed third `OOE` satisfies
   \(T_{\mathtt{OOEOOEOOE}}(n)<n^{2}\) from \(729<1024\), so an even
   landing is descent on a CE;
3. whether every such completed residual drops below \(n\), or
   every such residual is PE, or neither.

Do not prove \(\neg\operatorname{EscapesToInfinity}\). Do not claim
that the third residual is always `OOE`. Do not reopen
`EXPANDING_GRAMMAR_IS_PERSISTENCE`.

## Current literature

- CE `OOEOOE` forces another `OO` —
  **EXACT — LEAN VERIFIED** (`J-minimal-ooeooe-escape-trap`).
- `OOEOOEOOE` square-cell gap on the CycleMin corridor —
  **EXACT — HUMAN PROOF** (`juggler_odd_ooe_landing`).
- \(365\to 4447\) via `OOEOOEOOE` —
  **COMPUTATIONALLY VERIFIED**.
- \(565\) later odd run escapes \(n^{2}\) —
  **REFUTED** as “every later odd run stays below \(n^{2}\)”.
- Infinite PE concatenation is the CE leftover —
  **REPARAMETERIZATION** (`J-expanding-concat-is-ce`).

Project relationship: **extended**. The CE trap is continued one
residual further. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     After the CE OOEOOE trap forces OOEOOEOO,
                        does the completed third residual drop
                        below n or remain PE?
Novelty hypothesis      the cube/square envelopes survive without
                        CycleMin return, and both uniforms fail
Falsifier               an expanding drop; or only restated
                        odd_ooe_landing with no CE transfer
Existing machinery      minimal_ooeooe_forces_oo; power_bound_word;
                        even_floorPower_lt_iff; residual_excursion
Maximum Phase-0 scope   Lean cube and third-OOE square on Escape;
                        CE even-landing trap; window scan
Promotion criterion     a new CE-capable envelope that is not the
                        CycleMin corridor restated, plus a decided
                        dichotomy
Stop criterion          expanding-grammar reopen; halt; length-11;
                        a residue automaton
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- on a CE, `OOEOOE` implies `follows OOEOOEOO` —
  **EXACT — LEAN VERIFIED**
- \(T_{\mathtt{OOEOOEOO}}(n)<n^{3}\) because \(729<768\) —
  **EXACT — LEAN VERIFIED**
- \(T_{\mathtt{OOEOOEOOE}}(n)<n^{2}\) because \(729<1024\) —
  **EXACT — LEAN VERIFIED**
- a CE third-`OOE` landing is odd —
  **EXACT — LEAN VERIFIED**
- the third residual is always PE —
  **REFUTED** (\(429\), \(565\))
- the third residual always drops below \(n\) —
  **REFUTED** (\(365\))
- scanned drops are formally contracting —
  **COMPUTATIONALLY VERIFIED**
- no trajectory escapes — not claimed
- the third residual is always `OOE` — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.third_residual`
- Records: [juggler_third_residual.md](../research/juggler_third_residual.md),
  [juggler_third_residual.json](../research/juggler_third_residual.json)
- Tests: `tests/research/juggler_sequence/test_third_residual.py`
- Lean: cube and third-`OOE` square cells in `Escape.lean`.
  Laboratory barrel only. No `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

Uniform drop is **REFUTED**:

\[
365\xrightarrow{\mathtt{OOEOOEOOE}}4447,
\]

and \(4447>1749>365\) is PE.

Uniform PE is **REFUTED** already among completed `OOE` thirds:

\[
429\xrightarrow{\mathtt{OOEOOEOOE}}5595.
\]

Here \(5595>2145\) is odd, but \(T(5595)=418504\) is even and
\(418504>429^{2}\), so the landing is not odd-odd and the next
even escapes the square cell.

A longer third residual also fails to be PE:

\[
565\xrightarrow{\mathtt{OOEOOEOOOOOOOOOEEE}}\text{above }n^{2}.
\]

Drops in the window \(n<4001\) are contracting
(\(2177\), \(2185\), \(3565\)) and so are impossible on a CE.

No scanned third residual lands in \([n,x]\).

## Formalization

`Escape.lean` adds `wordOOEOOEOO` / `wordOOEOOEOOE`, the cube and
square envelopes, `minimal_ooeooe_follows_ooeooeoo`, and
`minimal_ooeooeooe_not_even_landing`. `FloorPower` and
`MinimalNonTerm` are not rewritten. No `sorry`. No
`no_juggler_escape`. Paper A is unchanged.

## Results

Classification **THIRD_RESIDUAL_GREEN**.

A CE that follows `OOEOOE` follows `OOEOOEOO`, and that image is
below \(n^{3}\). A completed third `OOE` is below \(n^{2}\); an
even landing is descent —
**EXACT — LEAN VERIFIED** (`J-ce-third-residual-preimages`).
The completed third residual is not uniformly a drop and not
uniformly PE — **REFUTED** (`J-third-residual-drop-or-pe`).

This is not a halt theorem and not a finite PE-run bound.

## Open questions

Answered in [juggler_escaped_even.md](juggler_escaped_even.md):
the escaped-even `OE` still lands below \(n^{2}\); even \(w\) drops
(\(429\)); odd \(w\) survives (\(1517\)). Do not reopen the
expanding-grammar obstruction. Do not claim a uniform PE-run bound.

## Decision

**PROMOTE** the CE cube/square transfer and the third-`OOE` even
trap. **REFUTE** both uniforms. Do not claim that escape is
impossible. Do not claim that every third residual is `OOE`.

Best next question: answered in
[juggler_escaped_even.md](juggler_escaped_even.md).

## Publication assessment

Status: `EXPLORATORY`.

One more transferred envelope plus a decided dichotomy. Not a
paper candidate and not a Juggler totality result.
