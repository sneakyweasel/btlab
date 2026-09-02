# Juggler odd landing after `OOEOOE`

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the odd-landing
residual of the promoted `OOEOOE` square-cell theorem.

## Problem

After an odd `OOEOOE` landing \(x\in[n,n^2)\), what does the forced
next `O` do? Does it drop below \(n\), or start another structured
`OO`?

## Exact statement

Let \(x=T_{\mathtt{OOEOOE}}(n)\) with \(n\le x<n^2\) and \(x\) odd,
and let \(z=\lfloor x^{3/2}\rfloor\). The Phase-0 questions are:

1. whether \(z<n^2\) follows from the exact envelope
   \(x^{64}\le n^{81}\);
2. whether
   \[
   \operatorname{CycleMin}(n,\;\mathtt{OOEOOE}\,O\,v)
   \Rightarrow
   \texttt{FiniteProgress}(n)
   \;\lor\;
   \text{\(v\) begins with \(O\)}.
   \]

## Current literature

- \(T_{\mathtt{OOEOOE}}(n)<n^2\), even landing drops —
  **EXACT — HUMAN PROOF** (`J-cyclemin-ooeooe-square-preimage`).
- `CycleMin` cannot end in `O` —
  **EXACT — LEAN VERIFIED** (`cycleMin_not_end_odd`).
- Isolated-`OE` comparison \(R(2)=0\) —
  **EXACT — LEAN VERIFIED**.
- `power_bound_word` —
  **EXACT — LEAN VERIFIED**.
- `OOEOOE` as a complete CycleMin —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_ooeooe`).
- Bunched-short / front overshoot / isolated-odd fibre —
  **PARK**. Frozen.

Project relationship: **extended**. The designated next question of
the promoted `OOEOOE` corridor.

## Branch budget

```text
Mathematical target     CycleMin(n, OOEOOE O v) =>
                        FiniteProgress or another OO
Novelty hypothesis      the next O is a controlled dichotomy
                        under the exact 81/64 envelope
Falsifier               z >= n^2; even z with T(z) >= n;
                        a long stay without another OO
Existing machinery      OOEOOE square cell; power_bound_word;
                        cycleMin_not_end_odd
Maximum Phase-0 scope   next-O envelope; Case A/B events;
                        no Lean; no terminal-cell reopen
Promotion criterion     FiniteProgress or FirstOO again
Stop criterion          generic bound only; uncontrolled
                        odd families; residue automaton;
                        Z5 / length-11 / four-even
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(x^{64}\le n^{81}\) implies \(x^3<n^4\) for \(n\ge 2\) —
  **EXACT — HUMAN PROOF**. Raise to the third power:
  \(x^{192}\le n^{243}\). Then \(n^{243}<n^{256}=(n^4)^{64}\).
- \(z=\lfloor x^{3/2}\rfloor<n^2\) —
  **EXACT — HUMAN PROOF**. \(z^2\le x^3<n^4\).
- even \(z\) forces \(T(z)<n\) —
  **EXACT — HUMAN PROOF**. The even-state trap under \(n^2\).
- odd \(z\) forces another `OO` —
  **EXACT — HUMAN PROOF**. Parity plus
  `cycleMin_not_end_odd`.
- \(\operatorname{CycleMin}(n,\mathtt{OOEOOE}Ov)\Rightarrow
  \texttt{FiniteProgress}\) for every \(v\) —
  **REFUTED**. Case B exists: \(365\) starts a second `OOE`.
- every post-`OO` odd run stays below \(n^2\) —
  **REFUTED**. \(565\) follows `OOEOOEO` by a long odd run
  and escapes \(n^2\).
- a second completed `OOE` stays below \(n^2\) —
  **EXACT — HUMAN PROOF** on the itinerary `OOEOOEOOE`
  (\(1024>729\)), and **COMPUTATIONALLY VERIFIED** on the
  scanned followers.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_ooe_landing`
- Records: [juggler_odd_ooe_landing.md](../research/juggler_odd_ooe_landing.md),
  [juggler_odd_ooe_landing.json](../research/juggler_odd_ooe_landing.json)
- Tests: `tests/research/juggler_sequence/test_odd_ooe_landing.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that the forced next `O` always drops is
**REFUTED**. Witness:

\[
365\xrightarrow{\mathtt{OOEOOEOOE}}4447.
\]

The landing \(z=73145\) is odd, so another `OO` starts. The
completed second `OOE` stays below \(365^2\).

The hypothesis that every later odd run stays below \(n^2\) is
**REFUTED**. Witness:

\[
565\xrightarrow{\mathtt{OOEOOEOOOOOOOO}\cdots}\text{above }n^2.
\]

The even-below-\(n^2\) trap has no counterexample. An even
\(m<n^2\) cannot satisfy \(T(m)\ge n\).

The previously named odd landings \(89\to 291\) and
\(111\to 385\) are Case A: the next image is even and the
following `E` drops (\(70\) and \(86\)).

## Formalization

None. Existing `Envelope.lean` and `CycleCore.lean` lemmas are
cited, not rewritten. No `no_cycleMin_prefix_ooeooeo`. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`. No
`no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **ODD_OOE_GREEN**.

If \(x=T_{\mathtt{OOEOOE}}(n)\) is odd and the prefix follows,
then \(x^3<n^4\) and \(z=\lfloor x^{3/2}\rfloor<n^2\). Therefore

\[
\operatorname{CycleMin}(n,\;\mathtt{OOEOOE}\,O\,v)
\;\Rightarrow\;
\begin{cases}
\texttt{FiniteProgress}(n) & \text{if }z\text{ is even},\\
v\text{ begins with }O & \text{if }z\text{ is odd}.
\end{cases}
\]

The new constraint is the exponent ladder \(81/64\to 243/128<2\),
not a residue automaton. A later `OOO` run can escape \(n^2\);
indefinite odd survival under the ceiling is not a theorem.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package the next-`O` envelope \(243<256\). The Case B
residual — first later `OOO` after the controlled `OOE`
language — is the separate branch
[juggler_first_ooo_escape.md](juggler_first_ooo_escape.md).
Do not reopen bunched-short cells. Do not write \(Z_5\). Do not
assemble `no_cycle_itinerary_length_eleven`.

## Decision

**PROMOTE**. The next `O` is a finite-transition dichotomy:
even image drops, odd image starts another `OO`. The strong
claim that odd survival below \(n^2\) cannot continue is false
for long odd runs and is not claimed.

Best next question: after Case B starts another `OO`, does a
second completed `OOE` repeat the same even/odd trap, or is
the `OOO` escape the only remaining residual?

## Publication assessment

Status: `THEOREM`.

A named exact next-`O` envelope from `power_bound_word`. Not a
Juggler totality result and not an indefinite-parity theorem.
