# Juggler parity persistence

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. Integer-cell continuation
is not resumed. This is the designated next question of the
promoted odd-\(u\) branch: whether inherited history forces an
even landing before \(\alpha_k\) multiplies by \(3/2\) again.

## Problem

On an inherited post-\(L\) landing, can the trajectory remain
odd for arbitrarily many steps, or is there a finite
odd-run budget?

## Exact statement

Let \(t=T_L(n)\) for \(n\) that follows \(L=\mathtt{OOEOOOEOOEE}\).
Write \(k\) for the number of consecutive odd states starting
at \(t\). The Phase-0 questions are:

1. whether the inherited source forces \(T(t)\) even;
2. whether \(k\le K\) for a finite \(K\) depending only on the
   entrance data;
3. whether odd-to-odd continuation shrinks the residue set
   modulo \(8\).

Do not search generic odd integers. Do not open a \(2\)-adic
system. Do not add another integer power cell.

## Current literature

- Iterated odd-landing sets \(\mathcal P_r\) stay at half and
  occupy every odd class modulo \(8,16,32\) —
  **CLOSE** (`ODD_LANDING_SETS_ARE_FORWARD_ORBITS`).
- Landing valuation is \(y\bmod 8\) and is not changed by PE
  history —
  **CLOSE**.
- \(2\)-adic / BT bridge splits at the second letter —
  **CLOSE**.
- Odd \(u\) next-`O` envelope \(v<n^{11}\); even \(v\) resets
  below \(n^6\) —
  **EXACT — HUMAN PROOF**.
- Post-\(L\) even/\(\mathtt{OE}\) landings drop; \(\mathtt{OOE}\)
  does not —
  **EXACT — HUMAN PROOF**.
- Bunched-short / \(Z_5\) / terminal cells —
  **PARK**. Frozen. Not reopened.

Project relationship: **extended**. The designated next
question of the promoted odd-\(u\) branch, tested on the
actual post-\(L\) family because no \(W_5\) follower occurs
below \(50000\).

## Branch budget

```text
Mathematical target     finite odd-run budget on inherited L
Novelty hypothesis      history forces even within finite K
Falsifier               inherited family with long odd runs;
                        stay ~ 1/2; residues do not shrink
Existing machinery      L-image split; odd_landing_sets CLOSE
Maximum Phase-0 scope   named L-window; 33391 run 5; no Lean
Promotion criterion     finite K or exact even-forcing transfer
Stop criterion          parity statistically broad; no K;
                        modulus census; another power bound
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Inherited post-\(L\) state forces \(T(t)\) even —
  **REFUTED**. \(501\to 763\) starts \(\mathtt{OO}\).
- Odd persistence after \(L\) is at most \(k=2\)
  (\(\mathtt{OOE}\) only) —
  **REFUTED**. \(29371\to 59041\) has run \(3\);
  \(28367\to 56889\) has run \(4\);
  \(33391\to 67709\) has run \(5\) (\(\mathtt{OOOOOE}\)).
- A finite odd-run budget \(K\) depending only on the
  \(L\)-entrance —
  **REFUTED** as a Phase-0 theorem. The observed maximum is
  \(5\) and increases with the window. Stay among odd
  landings is \(8/17\).
- Odd-to-odd continuation shrinks the class modulo \(8\) —
  **REFUTED**. Every odd class modulo \(8\) both continues
  and exits. The \(2\)-adic line is abandoned here, as
  prescribed. No \(p\)-adic system.
- \(W_5\) is realized below \(50000\) —
  **REFUTED**. The deepest \(\alpha_k\) chain is not
  computationally present.
- \(\theta\)-phase contraction — not reopened
  (**CLOSE** as `LANDING_THETA_UNRESTRICTED`).
- Episode automaton / finite exponent-state set — not built.
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed
- unbounded odd runs for all large \(n\) — not claimed

## Experiments

- Probe: `research.juggler_sequence.parity_persist`
- Records: [juggler_parity_persist.md](../research/juggler_parity_persist.md),
  [juggler_parity_persist.json](../research/juggler_parity_persist.json)
- Tests: `tests/research/juggler_sequence/test_parity_persist.py`
- Fixed witness list: the \(23\) starts that follow \(L\)
  in \(12\le n<50000\). Not a residue automaton.
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that inherited history forces an even output,
or at most two consecutive odds, is **REFUTED** by

\[
33391\xrightarrow{L}67709
\xrightarrow{\mathtt{OOOOOE}}
T^5(67709)\text{ even}.
\]

The hypothesis that odd-to-odd continuation occupies a
proper subclass modulo \(8\) is **REFUTED**: all four odd
classes both stay and exit.

No \(W_5\) follower occurs among those \(23\) starts.

## Formalization

None. Existing `odd_preimage_unique`, `power_bound_word`, and
`power_bound_contracts` are cited, not rewritten. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`.
No `no_juggler_cycle`. Paper A is unchanged. The closed
odd-landing-set and landing-valuation modules are not
reopened.

## Results

Classification **PARITY_PERSIST_PARK**.

On the actual post-\(L\) family below \(50000\):

- \(17\) of \(23\) landings are odd;
- immediate odd-to-odd stay is \(8/17\);
- odd-run lengths from \(t\) are
  \(1^{9}\,2^{4}\,3^{2}\,4^{1}\,5^{1}\);
- the maximum is \(5\), at \(33391\);
- every odd class modulo \(8\) both continues and exits;
- \(W_5\) is absent.

Parity persistence is not forced to deteriorate. The
inherited envelope does not supply an even-forcing
transfer. A finite \(K\) was not obtained. The \(2\)-adic
diagnostic is the same unrestricted split already closed
for generic \(\mathcal P_r\).

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Whether \(k\) is unbounded as \(n\to\infty\) on \(L\)-followers
is the separate branch
[juggler_l_odd_run_cap.md](juggler_l_odd_run_cap.md).
Do not reopen \(\theta\), valuation, or predecessor
cylinders. Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`. Do not build a \(p\)-adic
system.

## Decision

**PARK**. Inherited post-\(L\) history does not force an even
landing and does not yield a finite odd-run budget. Stay is
comparable to the closed generic half-stay. Residues modulo
\(8\) do not shrink. The \(W_5\) chain is computationally
absent. Do not continue the integer-cell ladder. Do not open
an episode automaton.

Best next question: is there a Diophantine obstruction to
arbitrarily long odd runs from \(T_L(n)\), or is \(k\)
unbounded on the \(L\)-family?

## Publication assessment

Status: `EXPLORATORY`.

A named computational refutation of even-forcing on the
inherited \(L\)-family. Not a finite-\(K\) theorem and not a
Juggler totality result.
