# Juggler next `O` after an odd `OOOE` landing

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the odd-landing
residual of the promoted post-`OOO` `OOOE` dichotomy.

## Problem

After an odd `OOEOOOE` landing \(w\in[n,n^2)\), does the forced next
`O` again produce a finite transition dichotomy?

## Exact statement

Let \(w=T_{\mathtt{OOEOOOE}}(n)\) be odd with \(n\le w<n^2\), and
let \(q=T(w)\). The Phase-0 questions are:

1. whether the inherited envelope \(w^{128}\le n^{243}\) forces a
   bound on \(q\) stronger than the generic \(w^{3/2}\) estimate;
2. whether even \(q\) gives FiniteProgress or a smaller corridor;
3. what exact corridor an odd \(q\) occupies.

## Current literature

- Completed `OOOE` after one `OOE` lands in \([n,n^2)\) —
  **EXACT — HUMAN PROOF** (`J-cyclemin-post-ooo-oooe`).
- Even `OOOE` landing drops; odd landing forces `O` —
  **EXACT — HUMAN PROOF**.
- Second `OOO` is not a stronger entrance —
  **REFUTED** (`J-cyclemin-post-ooo-always-drop`).
- \(T^2(x)\ge n^2\) on a first `OOO` —
  **EXACT — HUMAN PROOF**.
- `ooo_residual_ge_cube`, `no_cycleMin_ooeoooe` —
  **EXACT — LEAN VERIFIED**.
- Bunched-short / front overshoot / isolated-odd fibre —
  **PARK**. Frozen.

Project relationship: **extended**. The designated next question of
the promoted post-`OOO` branch.

## Branch budget

```text
Mathematical target     next O after odd OOEOOOE landing
Novelty hypothesis      q in [n^2, n^3); even q shrinks
Falsifier               generic 3/2 bound only;
                        483/491 unconstrained;
                        no shrinking on any branch
Existing machinery      OOEOOOE envelope 243/128;
                        cube lemma; 243 < 256
Maximum Phase-0 scope   inherited envelope; Case split;
                        no Lean; no terminal-cell reopen
Promotion criterion     FiniteProgress or a new exact
                        corridor for q
Stop criterion          generic bound only; residue
                        automaton; Z5 / length-11 / four-even
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `OOEOOOEO` loses the square-cell gap (\(512<729\)) —
  **EXACT — HUMAN PROOF**. This is the first
  ceiling-breaking extension after `OOEOOOE`.
- The next-`O` square refinement \(3\cdot 243<4\cdot 128\)
  fails — **EXACT — HUMAN PROOF**. So \(q<n^2\) is not
  inherited.
- \(q^{256}\le n^{729}<n^{768}=(n^3)^{256}\), hence
  \(q<n^3\) — **EXACT — HUMAN PROOF**.
- \(q\ge n^2\) — **EXACT — HUMAN PROOF**.
  \(w\ge\lfloor(n+1)^{3/2}\rfloor\) and
  \(\lfloor(n+1)^{3/2}\rfloor^3\ge(n+1)^4>n^4\).
- even \(q\) returns to \(r\in[n,n^{3/2})\) —
  **EXACT — HUMAN PROOF**. Even \(r\) drops:
  `OOEOOOEOEE` contracts (\(729<1024\)).
- even \(q\) always gives FiniteProgress —
  **REFUTED**. \(483\) has \(r=6623\) odd.
- every later corridor shrinks —
  **REFUTED**. Odd \(q\) starts a second `OO` from
  \([n^2,n^3)\). Witness \(491\).
- \(483/491\) are separated by cell position —
  **REFUTED**. Both have \(w/n^2\approx 0.533\). The split
  is the parity of \(q\).
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_oooe_next`
- Records: [juggler_odd_oooe_next.md](../research/juggler_odd_oooe_next.md),
  [juggler_odd_oooe_next.json](../research/juggler_odd_oooe_next.json)
- Tests: `tests/research/juggler_sequence/test_odd_oooe_next.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that even \(q\) immediately drops is
**REFUTED**. Witness:

\[
483:\quad w=124381,\quad q=43866306\text{ even},\quad r=6623\text{ odd}.
\]

The landing \(r\) still lies in \([483,483^{3/2})\). A second
`OOO` then starts at \(6623\).

The hypothesis that every surviving branch shrinks is
**REFUTED**. Witness:

\[
491:\quad w=128423,\quad q=46021865\text{ odd }\in[491^2,491^3).
\]

The second `OO` starts above \(n^2\). Both \(483\) and \(491\)
have \(w/n^2\approx 0.533\); the split is parity, not cell
location.

The even–even drop is

\[
319\xrightarrow{\mathtt{OOEOOOEOEE}}60.
\]

An odd \(q\) need not be an immediate second `OOO`: \(501\)
continues by `OOE` and later drops.

## Formalization

None. Existing `Envelope.lean`, `Preimages.lean`, and
`CycleCore.lean` lemmas are cited, not rewritten. No
`no_cycleMin_prefix_ooeoooee`. No `no_cycleMin_four_even`.
No `no_cycle_itinerary_length_eleven`. No `no_juggler_cycle`.
Paper A is unchanged.

## Results

Classification **ODD_OOOE_GREEN**.

If \(w=T_{\mathtt{OOEOOOE}}(n)\) is odd, then
\(q=T(w)\) satisfies

\[
n^2\le q<n^3.
\]

Therefore

\[
\operatorname{CycleMin}(n,\;\mathtt{OOEOOOE}\,O\,v)
\;\Rightarrow\;
\begin{cases}
r\in[n,n^{3/2}) & \text{if }q\text{ is even},\\
\text{a second }\mathtt{OO}\text{ from }[n^2,n^3)
  & \text{if }q\text{ is odd}.
\end{cases}
\]

If \(q\) and \(r=T(q)\) are both even, FiniteProgress. The
square-cell ceiling is lost at `OOEOOOEO`; the cube ceiling
is not. A uniform descending cell hierarchy \(C_{j+1}\subset C_j\)
fails on the odd-\(q\) branch.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package \(729<768\) and `OOEOOOEOEE` contraction.
The residual after odd \(q\) is the second `OO` from
\([n^2,n^3)\), now the separate branch
[juggler_second_oo_cube.md](juggler_second_oo_cube.md).
Do not reopen bunched-short cells. Do not write \(Z_5\).
Do not assemble `no_cycle_itinerary_length_eleven`.

## Decision

**PROMOTE**. The forced next `O` after an odd `OOOE`
landing is a three-way finite transition under the inherited
envelope: even–even drop, even–odd shrink to \(n^{3/2}\), or
odd \(q\) leaving the square cell into \([n^2,n^3)\). A
uniform shrinking hierarchy is not a theorem.

Best next question: after odd \(q\in[n^2,n^3)\), does the
second `OO` still carry an exact cube-relative envelope, or
is that the first uncontrolled post-`OOO` branch?

## Publication assessment

Status: `THEOREM`.

A named exact cube corridor for the next odd image from the
`OOEOOOE` envelope. Not a Juggler totality result and not a
descending-cell theorem for every branch.
