# Juggler hidden state of the coarse scale loop

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the residual of the
promoted second-`OO` scale graph: the apparent
\(C_2\to C_4\to C_2\to C_1\) cycle.

## Problem

The coarse scale graph after an inherited odd cube-corridor \(q\)
contains a directed cycle. Which exact arithmetic state did that
graph forget, and does the forgotten state drift or close?

## Exact statement

Let \(w=T_{\mathtt{OOEOOOE}}(n)\) be odd in \([n,n^2)\) and
\(q=T(w)\) odd in \([n^2,n^3)\), with \(u=T(q)\) even and
\(s=\lfloor\sqrt{u}\rfloor\) even. Write \(t=\lfloor\sqrt{s}\rfloor\).
The Phase-0 questions are:

1. whether \(C_2\to C_4\to C_2\to C_1\) is a repeating signature
   or a one-shot word;
2. the smallest refinement of \((C_k,\mathrm{parity})\) that
   separates the CycleMin start from the return \(t\);
3. whether defects, even remainders, or \(2\)-adic digits are
   that refinement.

## Current literature

- Inherited second `OO` envelope \(n^3\le T(q)<n^{2187/512}\) —
  **EXACT — HUMAN PROOF** (`J-cyclemin-second-oo-envelope`).
- The scale graph is acyclic / \(T^2(q)\in C_2\cup C_3\) —
  **REFUTED** (`J-cyclemin-second-oo-scale-acyclic`).
  Witness \(501\to 763\).
- Odd `OOEOOOE` landing forces \(n^2\le q<n^3\) —
  **EXACT — HUMAN PROOF**.
- Global defect accumulation as a halt mechanism —
  parked. Not reopened.
- Bunched-short / front overshoot / isolated-odd fibre —
  **PARK**. Frozen.

Project relationship: **extended**. The designated next question
of the promoted second-`OO` cube-corridor branch.

## Branch budget

```text
Mathematical target     refine C2-C4-C2-C1 so it cannot recur
Novelty hypothesis      a hidden carry/defect/pre-post state drifts
Falsifier               H repeats; no finite predictor;
                        only another exponent envelope
Existing machinery      second-OO envelopes; 501 -> 763;
                        OOEOOOEOOEE does not contract
Maximum Phase-0 scope   two inherited even-even loops;
                        C1 collision; p-adic control; no Lean
Promotion criterion     H' != H with a definite direction,
                        or a refined acyclic graph
Stop criterion          chaotic defects; modulus census;
                        Z5 / length-11 / four-even
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Even-even \(C_2\to C_4\to C_2\to C_1\) is the itinerary
  `OEE` on \(q\), equivalently `OOEOOOEOOEE` on \(n\) —
  **EXACT — HUMAN PROOF**.
- The return satisfies \(t^{2048}\le n^{2187}\) —
  **EXACT — HUMAN PROOF**. This does not force
  \(t<n\) (\(2187>2048\)).
- Refined states \(C_1^{\mathrm{pre}}\) (CycleMin start,
  first `OOO` unpaid) and \(C_1^{\mathrm{post}}\)
  (image of `OOEOOOEOOEE`) coincide iff \(t=n\) —
  **EXACT — HUMAN PROOF**.
- The exact loop signature repeats in one orbit —
  **REFUTED**. \(501\) and \(6187\) each have one
  coarse hit, then drop (\(34\) and \(1087\)).
- Scale + parity determines the future —
  **REFUTED**. \(501\) and \(763\) are both \(C_1\)
  odd relative to \(501\); \(501\) enters first `OOO`,
  \(763\) follows \((\mathtt{OOE})^3\mathtt{OE}\,E\).
- The hidden state is \(2\)-adic —
  **REFUTED** as a distinguished structure. On the
  inherited odd-\(q\) sample, moduli \(2^e,3^e,5^e,7^e\)
  all eventually separate the four futures. No \(2\)-adic
  compression.
- Consecutive defects obey a narrow one-way \(\Phi\) —
  **REFUTED** as a Phase-0 invariant. Each orbit has
  only one loop, so there is no second \(\delta\) to
  compare; \(\delta_0/(2q)\) was already wide.
- \(t=n\) is impossible — not claimed. That would be
  exact CycleMin closure of `OOEOOOEOOEE`, not a
  length-11 assembler.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.scale_loop_hidden`
- Records: [juggler_scale_loop_hidden.md](../research/juggler_scale_loop_hidden.md),
  [juggler_scale_loop_hidden.json](../research/juggler_scale_loop_hidden.json)
- Tests: `tests/research/juggler_sequence/test_scale_loop_hidden.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that the coarse loop is a repeating exact
signature is **REFUTED**.

\[
501\xrightarrow{\mathtt{OOEOOOEOOEE}}763,
\quad
\varepsilon(u)=278026,\quad\varepsilon(s)=747.
\]

The orbit has one \(C_2\to C_4\to C_2\to C_1\) hit, then
\((\mathtt{OOE})^3\mathtt{OE}\,E\) to \(34\).

\[
6187\xrightarrow{\mathtt{OOEOOOEOOEE}}11189
\xrightarrow{\mathtt{OE}}1087<6187.
\]

Again one hit. The return starts `OE`, not a second
first-`OOO`.

The hypothesis that \((C_1,\mathrm{odd})\) is a Markov
state is **REFUTED** by the pair \(501\) versus \(763\).

No refined-state periodic orbit with \(H'=H\) was found.
No exact integer closure \(t=n\) was found.

## Formalization

None. Existing `Envelope.lean`, `Preimages.lean`, and
`CycleCore.lean` lemmas are cited, not rewritten. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`.
No `no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **SCALE_LOOP_GREEN**.

The apparent scale cycle is a projection of a one-shot
word. In the refined state

\[
\bigl(C_k,\;\text{parity},\;
\text{pre- versus post-}\mathtt{OOEOOOEOOEE}\bigr)
\]

the transition is

\[
C_1^{\mathrm{pre}}
\longrightarrow
C_2\longrightarrow C_4\longrightarrow C_2
\longrightarrow
C_1^{\mathrm{post}},
\]

and \(C_1^{\mathrm{post}}=C_1^{\mathrm{pre}}\) if and only
if \(t=n\). The two inherited even-even orbits then leave
the first-`OOO` language and drop. Defects and \(2\)-adic
digits are not the missing state.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package the identification of even-even
\(C_2\to C_4\to C_2\to C_1\) with `OOEOOOEOOEE`.
The residual after \(C_1^{\mathrm{post}}\) is the
post-\(L\) recovery
[juggler_oneshot_recovery.md](juggler_oneshot_recovery.md).
Do not reopen bunched-short cells. Do not write \(Z_5\).
Do not assemble `no_cycle_itinerary_length_eleven`. Do not
build a \(p\)-adic dynamical system.

## Decision

**PROMOTE**. Scale recurrence is a projection artifact.
The hidden state is the pre/post bit of the one-shot word
`OOEOOOEOOEE`, not a \(2\)-adic carry and not a defect
\(\Phi\). Both named orbits then drop; the exact signature
does not repeat.

Best next question: after \(C_1^{\mathrm{post}}\), does the
inherited \(2187/2048\) envelope force the `OE` drop of
\(6187\), or can a \(501\)-type `OOE` continuation still
pay a later first `OOO` relative to the same \(n\)?

## Publication assessment

Status: `THEOREM`.

A named exact refinement of the second-`OO` scale graph.
Not a Juggler totality result and not a claim that
`OOEOOOEOOEE` cannot close.
