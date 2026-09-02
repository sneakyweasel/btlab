# Juggler post-`OOO` square-ceiling crossing

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the post-`OOO`
residual of the promoted first-`OOO` entrance theorem.

## Problem

After a first `OOO` from \(x\in[n,n^2)\), where does the completed
`OOOE` landing lie, and can CycleMin recover?

## Exact statement

Let \(x\) be the state immediately before the first post-first-`OO`
`OOO`, with \(n\le x<n^2\) and \(x\) odd, and write
\[
y=T(x),\qquad z=T(y),\qquad u=T(z),\qquad w=T_{\mathtt{OOOE}}(x)
\]
whenever the third odd image \(u\) is even. The Phase-0 questions
are:

1. exact bounds for \(u\) and \(w\) under the first-`OOO` history;
2. whether an even \(w\) forces FiniteProgress;
3. whether an odd \(w\) remains in a controlled corridor.

## Current literature

- First `OOO` from a CycleMin state has \(T^2(x)\ge n^2\) —
  **EXACT — HUMAN PROOF** (`J-cyclemin-ooo-second-step-square`).
- \(\lfloor n^{3/2}\rfloor^3\ge n^4\) —
  **EXACT — HUMAN PROOF**.
- `oo_suffix_threshold`, `ooo_residual_ge_cube` —
  **EXACT — LEAN VERIFIED**. Applied at \(x\), not at \(n\).
- `OOEOOOE` as a complete CycleMin —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_ooeoooe`).
- `floorPower_oooee_five_step_lt` —
  **EXACT — LEAN VERIFIED**. Contracts versus the start of
  `OOOEE`, not versus the CycleMin minimum.
- `OOEOOE` square cell; next-`O` envelope \(243<256\) —
  **EXACT — HUMAN PROOF**.
- Bunched-short / front overshoot / isolated-odd fibre —
  **PARK**. Frozen.

Project relationship: **extended**. The designated next question of
the promoted first-`OOO` branch.

## Branch budget

```text
Mathematical target     post-OOO OOOE corridor from C_3(n)
Novelty hypothesis      even OOOE drops; odd OOOE stays in C_3
Falsifier               even w < n^2 with T(w) >= n;
                        generic post-OOO suffix;
                        second OOO always stronger
Existing machinery      second-odd escape; OOEOOOE gap;
                        ooo_residual_ge_cube; OOOEE contracts
Maximum Phase-0 scope   k=1 OOOE envelope; Case A/B/C;
                        no Lean; no terminal-cell reopen
Promotion criterion     FiniteProgress or a finite post-OOO
                        corridor
Stop criterion          generic bound only; uncontrolled
                        landing; residue automaton;
                        Z5 / length-11 / four-even
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- After one `OOE`, \(x^8\le n^9\) and \(u^8\le x^{27}\) give
  \(u^{64}\le n^{243}<n^{256}=(n^4)^{64}\), hence
  \(T^3(x)<n^4\) — **EXACT — HUMAN PROOF**. The same
  \(243<256\) comparison as the next-`O` envelope.
- Completed `OOOE` then has \(n\le w<n^2\) —
  **EXACT — HUMAN PROOF**. Lower bound from
  \(u\ge(x+1)^3>(n+1)^3>n^2\). Upper bound from \(u<n^4\).
  The itinerary `OOEOOOE` has the square-cell gap \(256>243\).
- even \(w\) forces FiniteProgress —
  **EXACT — HUMAN PROOF**. `OOEOOOEE` contracts versus
  \(n\) because \(243<256\), and \(w<n^2\) even implies
  \(T(w)\le n-1\).
- odd \(w\) stays in \(C_3(n)\) and forces a next `O` —
  **EXACT — HUMAN PROOF**.
- every post-`OOO` recovery is FiniteProgress —
  **REFUTED**. Odd `OOOE` landings continue; \(483\)
  produces a second `OOO`. A longer odd run is a separate
  residual (\(173\), \(565\)).
- two consecutive `OOO` events require a strictly stronger
  entrance constraint — **REFUTED**. \(483\) re-enters
  \(C_3(n)\); \(491\) re-enters above \(n^2\).
- `OOO` is fatal — not claimed
- first `OOO` is the unique visit to a state \(\ge n^2\) —
  **REFUTED** as a state statement. An `OOE` block already
  crosses \(n^2\) at its second odd image, then returns by
  `E`. `OOO` is the unique *odd* \(T^2\) crossing, which
  refuses that return.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.post_ooo_crossing`
- Records: [juggler_post_ooo_crossing.md](../research/juggler_post_ooo_crossing.md),
  [juggler_post_ooo_crossing.json](../research/juggler_post_ooo_crossing.json)
- Tests: `tests/research/juggler_sequence/test_post_ooo_crossing.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that every post-`OOO` continuation drops is
**REFUTED**. Witness:

\[
483\xrightarrow{\mathtt{OOEOOOE}}124381
\]

with \(124381\) odd in \([483,483^2)\). The next `O` leads to
a second `OOO` at \(6623\), still in \(C_3(483)\), then a drop.

The hypothesis that a second `OOO` is a strictly stronger
entrance is **REFUTED**. Witness:

\[
491\xrightarrow{\text{second OOO}}558757\ge 491^2.
\]

The even-below-\(n^2\) trap has no counterexample. An even
\(m<n^2\) cannot satisfy \(T(m)\ge n\).

The named even recovery is

\[
105\xrightarrow{\mathtt{OOEOOOEE}}82<105.
\]

The long-odd residual remains \(565\) (\(O^9\) after two `OOE`)
and \(173\) (\(O^8\) after one `OOE`).

## Formalization

None. Existing `Envelope.lean`, `Preimages.lean`, and
`CycleCore.lean` lemmas are cited, not rewritten. No
`no_cycleMin_prefix_ooeoooee`. No `no_cycleMin_four_even`.
No `no_cycle_itinerary_length_eleven`. No `no_juggler_cycle`.
Paper A is unchanged.

## Results

Classification **POST_OOO_GREEN**.

If the first `OOO` follows a single `OOE` from \(n\ge 2\),
then \(T^3(x)<n^4\). Whenever that run completes as `OOOE`,

\[
n\le w<n^2,
\]

and

\[
\operatorname{CycleMin}(n,\;\mathtt{OOEOOOE}\,v)
\;\Rightarrow\;
\begin{cases}
\texttt{FiniteProgress}(n) & \text{if }w\text{ is even},\\
v\text{ begins with }O\text{ and }w\in C_3(n) & \text{if }w\text{ is odd}.
\end{cases}
\]

A later odd run of length at least \(4\) is a residual, not
the dichotomy. A second `OOO` has no monotone constraint.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package the \(243<256\) third-odd envelope and
`OOEOOOEE` contraction versus \(n\). The residual after an
odd `OOOE` landing — the forced next `O` — is the separate
branch [juggler_odd_oooe_next.md](juggler_odd_oooe_next.md).
Do not reopen bunched-short cells. Do not write \(Z_5\). Do
not assemble `no_cycle_itinerary_length_eleven`.

## Decision

**PROMOTE**. After a first `OOO` following one `OOE`, a
completed `OOOE` landing is a finite-transition dichotomy:
even drops, odd stays in \(C_3(n)\). `OOO` is not fatal, and
a second `OOO` is not a stronger entrance theorem.

Best next question: after an odd `OOOE` landing in \(C_3(n)\),
does the forced next `O` repeat the even/odd trap, or is a
longer odd run the only residual that leaves the corridor?

## Publication assessment

Status: `THEOREM`.

A named exact post-`OOO` envelope from `power_bound_word` on
`OOE` then `OOO`. Not a Juggler totality result and not an
`OOO`-fatality theorem.
