# Juggler second `OO` from the cube corridor

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the residual of the
promoted odd-`OOOE` next-`O` cube corridor.

## Problem

After an odd `OOEOOOE` landing produces odd \(q\in[n^2,n^3)\),
does the next `OO` still carry a non-generic constraint from the
inherited envelope \(q^{256}\le n^{729}\)?

## Exact statement

Let \(w=T_{\mathtt{OOEOOOE}}(n)\) be odd with \(n\le w<n^2\), and
let \(q=T(w)\) be odd. Write \(u=T(q)\) and, if \(u\) is odd,
\(v=T(u)\). The Phase-0 questions are:

1. the strongest exact power envelope for \(u\) and \(v\) obtained
   by raising \(q^{256}\le n^{729}\), not the generic \(3/2\) map;
2. the even/odd split after \(u\), and whether an even pullback
   returns to a CycleMin-compatible band;
3. whether the observed scale/parity graph is acyclic.

## Current literature

- Odd `OOEOOOE` landing forces \(n^2\le q<n^3\) —
  **EXACT — HUMAN PROOF** (`J-cyclemin-odd-oooe-next-o`).
- Even \(q\) always drops / every branch shrinks —
  **REFUTED** (`J-cyclemin-odd-oooe-even-q-drops`).
- Completed `OOOE` after one `OOE` lands in \([n,n^2)\) —
  **EXACT — HUMAN PROOF**.
- \(T^2(x)\ge n^2\) on a first `OOO` —
  **EXACT — HUMAN PROOF**.
- `ooo_residual_ge_cube`, `no_cycleMin_ooeoooe` —
  **EXACT — LEAN VERIFIED**.
- Bunched-short / front overshoot / isolated-odd fibre —
  **PARK**. Frozen.

Project relationship: **extended**. The designated next question of
the promoted odd-`OOOE` next-`O` branch.

## Branch budget

```text
Mathematical target     second OO from odd q in [n^2, n^3)
Novelty hypothesis      inherited 729/256 beats generic 3/2
Falsifier               generic 3/2 only; unrestricted defects;
                        featureless scale graph; residue automaton
Existing machinery      odd OOEOOOE cube corridor;
                        q^{256} <= n^{729}; 729 < 768
Maximum Phase-0 scope   raise 729/256 through OO;
                        parity split; named family; no Lean
Promotion criterion     sharper-than-generic envelope, or
                        a finite exact scale/parity theorem
Stop criterion          generic bound only; residue
                        automaton; Z5 / length-11 / four-even
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(u^{512}\le n^{2187}\), hence
  \(n^3\le u<n^{2187/512}\) —
  **EXACT — HUMAN PROOF**. Sharper than generic
  \(u<n^{9/2}\) because \(2187<2304\). The integer
  threshold \(u<n^4\) fails (\(2187>2048\)); \(u<n^5\)
  holds (\(2187<2560\)).
- If \(u\) is odd, \(v^{1024}\le n^{6561}\), hence
  \(n^{9/2}\le v<n^{6561/1024}\) —
  **EXACT — HUMAN PROOF**. Sharper than generic
  \(v<n^{27/4}\) because \(6561<6912\). The integer
  threshold \(v<n^6\) fails (\(6561>6144\)); \(v<n^7\)
  holds (\(6561<7168\)).
- Even \(u\) lands at \(s\) with
  \(n^{3/2}\le s<n^{2187/1024}\) —
  **EXACT — HUMAN PROOF**. \(s<n^2\) is not forced
  (\(2187>2048\)).
- `OOEOOOEOOEE` contracts versus \(n\) —
  **REFUTED**. \(3^7=2187>2048=2^{11}\). This is an
  exponent comparison for one itinerary, not a length-11
  assembler.
- \(T^2(q)\) always lies in \(C_2\cup C_3\) —
  **REFUTED**. Even \(u\) can land in \(C_2\)
  (\(491\), \(s=558757\)); odd \(u\) reaches \(C_6\)
  (\(1181\)).
- The scale/parity graph is acyclic —
  **REFUTED**. \(501\) realizes
  \(C_2\to C_4\to C_2\to C_1\) with
  \(t=763\ge 501\).
- Consecutive odd defects obey a narrow \(\Phi\) —
  **REFUTED**. In the inherited window,
  \(\delta_0/(2q)\) ranges through \((0.04,0.75)\).
- \(q\) is a generic odd integer in \([n^2,n^3)\) —
  **REFUTED**. The inherited state satisfies
  \(q^{256}\le n^{729}\), so \(q<n^{729/256}\).
  A generic odd near \(n^2\) can send \(T(q)\) into
  \(C_3\); the named inherited \(q\)'s land in \(C_4\).
- entering \([n^2,n^3)\) is itself dangerous —
  not claimed. \(501\) continues after the \(C_1\)
  return.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.second_oo_cube`
- Records: [juggler_second_oo_cube.md](../research/juggler_second_oo_cube.md),
  [juggler_second_oo_cube.json](../research/juggler_second_oo_cube.json)
- Tests: `tests/research/juggler_sequence/test_second_oo_cube.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that the second `OO` stays in \(C_2\cup C_3\)
is **REFUTED**. Witnesses:

\[
491:\quad u=312209649122\in C_4,\quad s=558757\in C_2\text{ odd}.
\]

\[
1181:\quad u=13268056096991\text{ odd}\in C_4,\quad
v=48329349373548636613\in C_6.
\]

The hypothesis that the scale graph is acyclic is
**REFUTED**. Witness:

\[
501:\quad u=339791341082\text{ even},\quad s=582916\text{ even},
\quad t=763\in C_1,\quad t\ge 501.
\]

The even-\(q\) contrast \(483\) is a different edge
(\(C_2\) even \(\to C_1\) odd \(r=6623\)), not a second
`OO` from odd \(q\).

States such as \(3989\) with \(w\ge n^2\) are outside the
inherited first-`OOOE` corridor and are excluded.

## Formalization

None. Existing `Envelope.lean`, `Preimages.lean`, and
`CycleCore.lean` lemmas are cited, not rewritten. No
`no_cycleMin_prefix_ooeoooee`. No `no_cycleMin_four_even`.
No `no_cycle_itinerary_length_eleven`. No `no_juggler_cycle`.
Paper A is unchanged.

## Results

Classification **SECOND_OO_GREEN**.

If \(w=T_{\mathtt{OOEOOOE}}(n)\) is odd and \(q=T(w)\) is
odd, then \(q^{256}\le n^{729}\) raises through the next
`OO`:

\[
n^3\le u=T(q)<n^{2187/512},
\]

and if \(u\) is odd,

\[
n^{9/2}\le v=T(u)<n^{6561/1024}.
\]

Therefore

\[
\operatorname{CycleMin}(n,\;\mathtt{OOEOOOE}\,O\,v)
\;\Rightarrow\;
\begin{cases}
s\in[n^{3/2},n^{2187/1024}) & \text{if }u\text{ is even},\\
v^{1024}\le n^{6561} & \text{if }u\text{ is odd}.
\end{cases}
\]

Both envelopes are strictly sharper than the generic
\(3/2\) iteration from \(q<n^3\). The integer cells
\(C_2\cup C_3\) do not capture \(T^2(q)\). The scale
graph contains a \(C_1\) return and is not a proof of
eventual finite progress.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Lean-package \(2187<2560\) and \(6561<7168\). The residual
after the apparent \(C_2\to C_4\to C_2\to C_1\) return is
the hidden-state refinement
[juggler_scale_loop_hidden.md](juggler_scale_loop_hidden.md).
Do not reopen bunched-short cells. Do not write \(Z_5\).
Do not assemble `no_cycle_itinerary_length_eleven`. Do not
treat the \(501\) scale return as a numerical cycle.

## Decision

**PROMOTE**. An odd cube-corridor \(q\) is not a generic
odd integer in \([n^2,n^3)\). The inherited
\(q^{256}\le n^{729}\) gives exact second-`OO` envelopes
sharper than generic power growth. The scale automaton is
not acyclic, and the two-step defect chain is not a useful
constraint.

Best next question: after even \(u=T(q)\), does the landing
\(s\in[n^{3/2},n^{2187/1024})\) still give a finite even/odd
trap under that envelope, or can the realized
\(C_2\to C_4\to C_2\to C_1\) return repeat?

## Publication assessment

Status: `THEOREM`.

A named exact second-`OO` envelope from the `OOEOOOE`
cube corridor. Not a Juggler totality result, not an
acyclic scale-automaton theorem, and not a descending-cell
theorem for every branch.
