# Juggler extremal composition

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can the existing local mechanisms be composed around one complete
cycle to obtain information that the ordinary finite-itinerary envelope
cannot see?

## Exact statement

A nontrivial cycle has distinguished states

\[
m=\min C,\qquad
z=\text{first even after }m,\qquad
x=\text{predecessor of }M,\qquad
M=\max C,\qquad
M\xrightarrow{E^r}p.
\]

Existing theorems already give

\[
m\text{ odd},\quad
M\text{ even},\quad
M>m^2,\quad
p<x<M,\quad
p^{2^r}\le M<(p+1)^{2^r},\quad
M^2\le x^3<(M+1)^2,
\]

the peak descent \(T_{OE^r}(x)=p<x\), and the square-scale prefix law
\(3^{\#O(w)}\ge 2^{|w|+1}\). The composition attempt packages the
cycle-only order

\[
m\le p<x<M
\]

together with the strict top window

\[
p^{2^r}<M
\]

forced by parity (\(p^{2^r}\) is odd). The derived comparison
\(m^4<x^3\) is \(M>m^2\) plus the cube cell, not a new scale gap.

Every attempted stronger scale law — first-even versus top collapse,
minimum-to-maximum split at \(z\), closing path from \(p\) to \(m\),
peak finance, defect on the ascent — reduces to
`power_bound_word` or an existing extremal theorem.

This says nothing about totality. Do not prove that every cycle itinerary
is impossible. Do not introduce odd landings, a residual graph, or a
new energy.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Cycle extrema \(M>m^2\) —
  **EXACT — LEAN VERIFIED**.
- Top nested cell and peak descent —
  **EXACT — LEAN VERIFIED**.
- Peak finance is the top-ascent envelope —
  **REPARAMETERIZATION**.

Project relationship: **extended**. The distinguished order is
recorded. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     compose min + first-even + top cell + peak; seek a non-envelope inequality
Novelty hypothesis      distinguished locations interact more strongly than 2^K < 3^O
Falsifier               every composition reduces to an existing envelope or extremal theorem
Existing machinery      CycleMin/Max, square_scale_*, cycle_top_*, cycle_peak_*
Maximum Phase-0 scope   distinguished order; strict window; first-even vs top; stop on repackaging
Promotion criterion     a location-sensitive constraint that is not an envelope, or a cycle contradiction
Stop criterion          COMPOSITION_REPACKAGING; odd-landings; residual graph; defect object; energy
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- distinguished order \(m\le p<x<M\) —
  **EXACT — LEAN VERIFIED**
- strict top window \(p^{2^r}<M\) —
  **EXACT — LEAN VERIFIED**
- derived \(m^4<x^3\) —
  **EXACT — LEAN VERIFIED**, and a **REPARAMETERIZATION** of
  \(M>m^2\) plus the cube cell
- first-even versus top scale gap — not claimed
- \(p=m\), \(z<p\), \(z>x\) — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_extremal_composition`
- Records: [juggler_cycle_extremal_composition.md](../research/juggler_cycle_extremal_composition.md),
  [juggler_cycle_extremal_composition.json](../research/juggler_cycle_extremal_composition.json)
- Tests: `tests/research/juggler_sequence/test_cycle_extremal_composition.py`
- The Research Engine control layer is not modified.
- Finite-orbit distinguished points only. No cycle-state search.

## Conjectures

None opened.

## Counterexamples

None to the packaged cycle order. The stronger claims that fail as
universal statements, already on transients:

- “\(p=m\)” — start 7 has \(p=1<7\).
- “\(z=M\)” — start 37 has a first even strictly below the maximum.
- “\(z>x\)” — start 37 has \(z<x\).
- “\(z<x\)” — start 21 has \(z>x\).
- “\(z\ge m^2\)” — start 21 has first even \(96<21^2\). This bound is
  cycle-minimum only.
- “\(x\ge p^2\)” — already refuted at starts 9 and 77.

A transient that realises every local cell does **not** refute a
cycle-only theorem.

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, a small extension. Added:

- `exists_first_even_iterate`
- `cycle_top_window_strict`
- `cycleMax_iterate_le`
- `cycleMax_not_cycleMin`
- `cycleMax_min_sq_lt`
- `cycle_distinguished_order`

Not added: `cycle_first_even_to_max_scale`,
`cycle_max_to_min_scale`, `cycle_peak_vs_first_even`,
`cycle_distinguished_scale_composition`, `cycle_extremal_defect`,
`OddLanding`, `MilestoneGraph`, `CycleEngine`, `PowerHeight`,
`Energy`.

`FloorPower` and `Progress` are not rewritten. No `sorry`. No halt
theorem. No `no_juggler_cycle`. No `CycleSearch`.

## Results

Classification **COMPOSITION_REPACKAGING**.

The strongest compatible normal form is

\[
m\le p<x<M,\qquad
p^{2^r}<M<(p+1)^{2^r},\qquad
M^2\le x^3<(M+1)^2,\qquad
m^4<x^3.
\]

Scale compositions retain only total odd/even counts.

## Open questions

Answered in
[juggler_cycle_rounding.md](juggler_cycle_rounding.md): cyclic
return of the exact floor remainders is a non-envelope identity, not
an exponent-budget composition. Do not reopen scale composition.

## Decision

**CLOSE** the compose-for-contradiction branch. Record the compatible
normal form. Do not claim an itinerary-independent cycle obstruction. Do
not claim termination.

Best next question: answered in
[juggler_cycle_rounding.md](juggler_cycle_rounding.md).

## Publication assessment

Status: `EXPLORATORY`. A negative composition result, not a paper
candidate and not a Juggler totality result.
