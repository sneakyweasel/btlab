# Juggler \(L\)-odd-run cap

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. Integer-cell continuation
is not resumed. This is the designated next question of the parked
parity-persistence branch: whether a Diophantine obstruction caps
odd runs from \(t=T_L(n)\).

## Problem

Does the inherited envelope \(t^{2048}\le n^{2187}\) forbid
arbitrarily long odd runs from \(t\), or must any finite
\(K\) come from non-realization of \(L+\mathtt{O}^k\)?

## Exact statement

Assume \(n\ge 2\) follows \(L=\mathtt{OOEOOOEOOEE}\) and
\(t=T_L(n)\) satisfies \(t^{2048}\le n^{2187}\). If \(t\)
follows \(\mathtt{O}^k\), does the compose test

\[
2187\cdot 3^{k}<2048\cdot 2^{k}
\]

force \(T_{\mathtt{O}^k}(t)<n\)? If not, is there another
exact obstruction to all large \(k\)?

Do not open an \(L+\mathtt{O}^k\) itinerary census. Do not reopen
\(\theta\), valuation, or predecessor cylinders.

## Current literature

- \(t^{2048}\le n^{2187}\); `E` and `OE` from \(t\) drop;
  `OOE` does not —
  **EXACT — HUMAN PROOF**.
- \(33391\to 67709\) has odd-run length \(5\) —
  **COMPUTATIONALLY VERIFIED**.
- Inherited history forces even / \(K=2\) —
  **REFUTED**.
- `odd_run_suffix_threshold` / `no_cycle_odd_run_append_even`
  forbid `CycleItinerary` \(\mathtt{O}^a\mathrm{E}\) for \(a\ge 3\) —
  **EXACT — LEAN VERIFIED**.
- Iterated odd-landing sets stay at half —
  **CLOSE**.
- Bunched-short / \(Z_5\) / terminal cells —
  **PARK**. Frozen. Not reopened.

Project relationship: **extended**. The designated next
question of the parked parity-persistence branch.

## Branch budget

```text
Mathematical target     L-envelope vs long odd runs from t
Novelty hypothesis      2187/2048 supplies a finite K
Falsifier               compose never drops; k=5 realized
Existing machinery      compose_below_anchor; 33391 run 5
Maximum Phase-0 scope   compose test; 33391; no itinerary census
Promotion criterion     finite K theorem, or unboundedness
Stop criterion          only a larger computational max;
                        L+O^k census; p-adic; another cell
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- If \(t^{2048}\le n^{2187}\) and \(t\) follows \(\mathtt{O}^k\),
  then \(T_{\mathtt{O}^k}(t)<n\) —
  **REFUTED**. \(2187>2048\) and \(3^{k}\ge 2^{k}\), so
  \(2187\cdot 3^{k}>2048\cdot 2^{k}\) for every \(k\ge 0\).
  Slack at \(k=0\) is \(139\) and increases.
- Therefore the \(L\)-envelope supplies a finite odd-run
  budget \(K\) —
  **REFUTED**.
- `no_cycle_odd_run_append_even` caps path-length from
  \(t\) —
  **REFUTED** as a deduction. That theorem is a
  `CycleItinerary` obstruction, not a path obstruction.
  \(33391\) realizes \(k=5\).
- Realization of \(L+\mathtt{O}^k\) for all \(k\) —
  not claimed. Not a census.
- \(k\) is unbounded on the \(L\)-family —
  not claimed. A one-shot search of odd \(n<150001\)
  found no \(k=6\) (**OBSERVATION**, not re-run in the
  probe).
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.l_odd_run_cap`
- Records: [juggler_l_odd_run_cap.md](../research/juggler_l_odd_run_cap.md),
  [juggler_l_odd_run_cap.json](../research/juggler_l_odd_run_cap.json)
- Tests: `tests/research/juggler_sequence/test_l_odd_run_cap.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem. No \(L+\mathtt{O}^k\) census.

## Conjectures

None opened.

## Counterexamples

The hypothesis that \(t^{2048}\le n^{2187}\) forbids long
odd runs from \(t\) is **REFUTED** by

\[
2187\cdot 3^{k}>2048\cdot 2^{k}\qquad(k\ge 0)
\]

and by the realized run \(33391\xrightarrow{L}67709\) of
length \(5\).

## Formalization

None. Existing `power_bound_contracts`,
`odd_run_suffix_threshold`, and
`no_cycle_odd_run_append_even` are cited, not rewritten.
No `no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`.
No `no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **L_ODD_RUN_CAP_PARK**.

If \(t^{2048}\le n^{2187}\) and \(t\) follows \(\mathtt{O}^k\),
the compose test does **not** force a drop below \(n\). Any
finite \(K\) must come from non-existence of an \(n\) that
follows \(L+\mathtt{O}^k\). That realization question is
open. The cycle-suffix theorems do not answer it.
\(k=5\) is realized. \(k=6\) was not seen for odd
\(n<150001\).

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

Does \(L+\mathtt{O}^k\) fail to be realized for all large
\(k\), or does some sequence of \(L\)-followers realize
arbitrarily large \(k\)? That is a preimage/realization
question. Do not open an itinerary census here. Do not reopen
\(\theta\), valuation, or predecessor cylinders. Do not
write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`. Do not build a \(p\)-adic
system. Do not resume the integer-cell ladder.

## Decision

**PARK**. The inherited \(L\)-envelope is not a cap on odd
runs from \(t\). Boundedness is therefore not an exponent
question. Realization of \(L+\mathtt{O}^k\) remains open.
Do not census words. Do not claim that \(k\) is unbounded.

Best next question: is there a preimage obstruction to
\(L+\mathtt{O}^k\) for large \(k\), other than a search for
more followers?

## Publication assessment

Status: `THEOREM`.

A named exact non-contraction for every odd continuation
of an \(L\)-image. Not a finite-\(K\) theorem, not an
unboundedness theorem, and not a Juggler totality result.
