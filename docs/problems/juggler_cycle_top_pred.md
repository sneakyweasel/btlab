# Juggler maximum predecessors

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Once the maximum \(M\) is reached from its odd predecessor \(x\), does
the combination of the odd inverse cell at \(x\) and the iterated
square-root cell \(M\to p\) leave enough arithmetic room for a cycle?

## Exact statement

For a `CycleMax n w` with \(n\ge 2\), write \(M=n\) and let \(x\) be
the cycle predecessor \(T^{|w|-1}(M)\). Then \(x\) is odd,
\(T(x)=M\), and

\[
M^2\le x^3<(M+1)^2.
\]

The top normal form supplies an odd landing \(p=T^r(M)\) with
\(r\ge 1\) and

\[
p^{2^r}\le M<(p+1)^{2^r}.
\]

The odd-to-even two-step law gives \(T(M)<x\). Even descent along the
top run gives \(p\le T(M)\). Therefore the strict three-level relation

\[
p<x<M
\]

is forced. Direct return \(x=p\) is excluded. \(T(M)=p\) only when
\(r=1\).

The nested lower cells imply the exact scale bounds

\[
x^3\ge p^{2^{r+1}},\qquad M<x^2,\qquad p^{2^{r-1}}<x.
\]

The crude comparison of \(x^3\ge p^{2^{r+1}}\) with
\(x<M<(p+1)^{2^r}\) does not empty the region for every \(p\) and
every \(r\ge 1\). In particular \(x\ge p^2\) is not forced.

This says nothing about totality. Do not prove that every cycle itinerary
is impossible.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Top even-run window \(p^{2^r}\le M<(p+1)^{2^r}\) —
  **EXACT — LEAN VERIFIED**.
- Odd-to-even two-step \(T^2(n)<n\) —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The maximum predecessor is
normalized independently of the ascent word. Totality remains
unclaimed.

## Branch budget

```text
Mathematical target     odd predecessor of M plus top window gives a nested-cell restriction
Novelty hypothesis      T^2(x)<x forces p<x<M; nested cells constrain (p,x,M,r)
Falsifier               a cycle-legal even predecessor; or nested cells empty for some r
Existing machinery      cycleMax_top_normal_form, even_iter_*, odd-even two-step, odd cube cell
Maximum Phase-0 scope   predecessor odd; p<x<M; nested cells; x^3≥p^{2^{r+1}}; transient preds
Promotion criterion     reusable three-level top structure, or a genuine p–x scale gap
Stop criterion          cycle engine; itinerary census; FloorPower rewrite; r-census; log/cube-root in Lean
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- predecessor of a cycle maximum is odd —
  **EXACT — LEAN VERIFIED**
- three-level top \(p<x<M\) —
  **EXACT — LEAN VERIFIED**
- nested cells \(p^{2^r}\le M<(p+1)^{2^r}\) and
  \(M^2\le x^3<(M+1)^2\) —
  **EXACT — LEAN VERIFIED**
- scale \(x^3\ge p^{2^{r+1}}\) and \(M<x^2\) —
  **EXACT — LEAN VERIFIED**
- nested cells empty for all \(r\ge 1\) — not claimed
- a class of top-run lengths is impossible — not claimed
- \(x\ge p^2\) — **REFUTED** as a forced relation (transient \(9\), \(77\))
- \(x=p\) — excluded on cycles
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_top_pred`
- Records: [juggler_cycle_top_pred.md](../research/juggler_cycle_top_pred.md),
  [juggler_cycle_top_pred.json](../research/juggler_cycle_top_pred.json)
- Tests: `tests/research/juggler_sequence/test_cycle_top_pred.py`
- The Research Engine control layer is not modified.
- Finite-orbit maxima only. No cycle-state search.

## Conjectures

None opened.

## Counterexamples

None to the three-level relation or the nested cells. The stronger
claims that fail:

- “\(x=p\) is typical or possible on a cycle” — the two-step law
  forces \(p<x\).
- “\(x\ge p^2\)” — start \(9\) has \(p=11\), \(x=27\); start \(77\)
  has \(p=1523\), \(x=17537\).
- “no odd \(x<M\) can map into the top window” — every calibrated
  transient realises the nested cell.
- “\(T(M)=p\) for every top run” — only when \(r=1\).

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, a small extension. Added:

- `cycleMax_predecessor_odd` / `cycleMax_predecessor_lt`
- `cycle_top_predecessor_cell`
- `cycle_top_three_level`
- `cycle_top_nested_cell`
- `cycle_top_scale_constraint` / `cycle_top_pred_scale`
- `cycle_top_max_lt_pred_sq` / `cycle_top_pred_gt_pow`

`FloorPower` and `Progress` are not rewritten. No `sorry`. No halt
theorem. No `no_juggler_cycle`. No `CycleSearch`. No length
classification. No top-run obstruction theorem. No `PowerBoundEq`
attack. No `PowerHeight`.

## Results

Classification **TOP_NESTED_CELL_GREEN**, with secondary
**TOP_SCALE_GAP_GREEN** and **TOP_NESTED_CELL_SURVIVES**.

The three-level top is reusable and word-independent. The nested
cells constrain \(x\) but do not empty any top-run length.

## Open questions

Answered in [juggler_cycle_peak_descent.md](juggler_cycle_peak_descent.md):
the nested triple is not squeezed further. The maximum determines a
canonical contracting peak block \(OE^r\), and financing it recovers
the existing ascent scale. Do not start a first-cell census. Do not
reopen length 7.

## Decision

**PROMOTE** the odd predecessor, the three-level top, and the nested
cells. Do not claim that a top-run length is impossible. Do not claim
that \(x\ge p^2\). Do not claim termination.

Best next question: answered in
[juggler_cycle_peak_descent.md](juggler_cycle_peak_descent.md).

## Publication assessment

Status: `EXPLORATORY`. A maximum-predecessor lemma, not a paper
candidate and not a Juggler totality result.
