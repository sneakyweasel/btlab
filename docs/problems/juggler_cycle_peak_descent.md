# Juggler canonical peak descent

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Every nontrivial cycle has a canonical contracting peak block
\(x\xrightarrow{OE^r}p<x\). Can the ascent from the landing \(p\) back
to the predecessor \(x\) finance that collapse more strongly than the
ordinary top-ascent envelope?

## Exact statement

For a `CycleMax n w` with \(n\ge 2\), write \(M=n\), let \(x\) be the
cycle predecessor of \(M\), and let \(p=T^r(M)\) be the odd landing
after the maximal even run. Then

\[
x\xrightarrow{OE^r}p,\qquad p<x.
\]

The block \(OE^r\) is formally contracting:

\[
3=3^{\#O(OE^r)}<2^{|OE^r|}=2^{r+1}.
\]

Write \(v\) for the finite path from \(p\) to \(x\). The peak lower
cell and the ascent envelope combine to

\[
p^{2^{r+1}}\le x^3,\qquad
x^{2^{|v|}}\le p^{3^{\#O(v)}},
\]

hence

\[
3^{\#O(v)+1}\ge 2^{|v|+r+1}.
\]

After appending the final odd letter this is exactly the existing
top-ascent law

\[
3^{\#O(vO)}\ge 2^{|vO|+r}.
\]

The peak-finance identity is therefore a **reparameterization** of
`top_ascent_superquadratic`, not a stronger cycle-scale gap.

This says nothing about totality. Do not prove that every cycle itinerary
is impossible. Do not build an odd-milestone graph.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Three-level top \(p<x<M\) —
  **EXACT — LEAN VERIFIED**.
- Formally contracting \(O^aE^b\) blocks contract the entry —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The peak block is named as a
canonical subword of every cycle. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     canonical OE^r descent plus finance vs existing ascent scale
Novelty hypothesis      every cycle has a determined contracting peak block
Falsifier               peak image misses p; or finance stronger than top-ascent
Existing machinery      cycle_top_three_level, oddEvenBlock, power_bound_word
Maximum Phase-0 scope   peak descent; contracting; finance=ascent; transient peaks
Promotion criterion     reusable canonical peak descent
Stop criterion          cycle engine; milestone graph; FloorPower rewrite; r-census
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- canonical peak descent \(T_{OE^r}(x)=p<x\) —
  **EXACT — LEAN VERIFIED**
- \(OE^r\) is formally contracting —
  **EXACT — LEAN VERIFIED**
- peak-ascent finance \(3^{o+1}\ge 2^{k+r+1}\) —
  **EXACT — LEAN VERIFIED**, and **REPARAMETERIZATION** of the top
  ascent
- a stronger scale gap than the top ascent — not claimed
- odd-milestone residual cycle — not built
- \(p=m\) — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_peak_descent`
- Records: [juggler_cycle_peak_descent.md](../research/juggler_cycle_peak_descent.md),
  [juggler_cycle_peak_descent.json](../research/juggler_cycle_peak_descent.json)
- Tests: `tests/research/juggler_sequence/test_cycle_peak_descent.py`
- The Research Engine control layer is not modified.
- Finite-orbit peak blocks only. No cycle-state search.

## Conjectures

None opened.

## Counterexamples

None to the peak descent. The stronger claims that fail:

- “peak finance is stronger than the top-ascent envelope” — it is the
  same inequality after appending the final \(O\).
- “transients close an ascent from \(p\) to \(x\)” — they realise the
  descent only; \(p\) is visited after \(M\).
- “\(T(p)\) has a single parity” — both parities appear among
  calibrated transients.

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, a small extension. Added:

- `peak_block_formally_contracting` / `peak_block_contracts`
- `cycle_peak_descent`
- `peak_ascent_scale` / `cycle_peak_finance`

`FloorPower` and `Progress` are not rewritten. No `sorry`. No halt
theorem. No `no_juggler_cycle`. No `CycleSearch`. No odd-milestone
type. No `PowerBoundEq` attack. No `PowerHeight`.

## Results

Classification **PEAK_DESCENT_GREEN**, with secondary
**MILESTONE_REPACKAGING**.

Every nontrivial cycle has a canonical contracting peak block. The
ascent that finances it is the existing top-ascent law, rewritten at
the predecessor.

## Open questions

Answered in
[juggler_cycle_extremal_composition.md](juggler_cycle_extremal_composition.md):
composing the existing min / first-even / top-cell / peak constraints
is envelope repackaging. Do not open an odd-landing graph.

## Decision

**PROMOTE** the canonical peak descent and the finance identity. Do
not claim a stronger scale gap. Do not build an odd-milestone engine.
Do not claim termination.

Best next question: answered in
[juggler_cycle_extremal_composition.md](juggler_cycle_extremal_composition.md).

## Publication assessment

Status: `EXPLORATORY`. A peak-block lemma, not a paper candidate and
not a Juggler totality result.
