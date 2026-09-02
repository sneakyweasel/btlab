# Juggler cyclic rounding

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

The exponent envelope throws away every local floor remainder. Can
those remainders be made to close incompatibly around a nontrivial
cycle?

## Exact statement

For a realized branch, write \(x'=T(x)\). The exact local remainder is

\[
x^{e}=x'^{2}+\rho,\qquad
0\le\rho<2x'+1,
\]

with \(e=1\) on an even branch and \(e=3\) on an odd branch. This is
the existing `localDefect`, not a new dynamics object.

On a `CycleItinerary n w` every index satisfies that identity, and cyclic
return gives the balance

\[
\sum\rho+\sum_{\mathrm{even}}x(x-1)
=
\sum_{\mathrm{odd}}x^{2}(x-1).
\]

Dropping every \(\rho\ge 0\) recovers `power_bound_word`. For
\(n\ge 2\) the all-zero remainder pattern is impossible: it would
force a monochrome equality tower, and those itineraries cannot return.
At a cycle maximum the odd predecessor remainder is strictly
positive, equivalently \(M^{2}<x^{3}\), because \(x\) is odd and
\(M\) is even.

This says nothing about totality. Do not prove that every cycle itinerary
is impossible. Do not introduce remainder dynamics or an energy.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Local defects and first-defect sharpness —
  **EXACT — LEAN VERIFIED**.
- Extremal composition of scale laws —
  **REPARAMETERIZATION** of the envelope.

Project relationship: **extended**. Remainders refine the envelope.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     exact local remainders plus cyclic closure, not an exponent budget
Novelty hypothesis      keeping ρ around a cycle sees something the envelope drops
Falsifier               every remainder identity reduces to power_bound_word or a known cell
Existing machinery      localDefect, cube/square cells, CycleItinerary, equality rigidity
Maximum Phase-0 scope   remainder API; cycle balance; all-zero rigidity; peak ρ_O>0; transients
Promotion criterion     a remainder-location constraint that is not an envelope, or a cycle contradiction
Stop criterion          CYCLE_ROUNDING_REPACKAGING; RemainderDynamics; energy; cycle census
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- local remainder window \(0\le\rho<2T(x)+1\) —
  **EXACT — LEAN VERIFIED**
- cyclic remainder balance —
  **EXACT — LEAN VERIFIED**
- all-zero remainders impossible for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- peak odd remainder \(\rho_O\ge 1\) —
  **EXACT — LEAN VERIFIED**
- remainder amplification \(\rho_j>0\Rightarrow\rho_{j+1}>\rho_j\) —
  **REFUTED** at start 9
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_rounding`
- Records: [juggler_cycle_rounding.md](../research/juggler_cycle_rounding.md),
  [juggler_cycle_rounding.json](../research/juggler_cycle_rounding.json)
- Tests: `tests/research/juggler_sequence/test_cycle_rounding.py`
- The Research Engine control layer is not modified.
- Finite-orbit remainders only. No cycle-state search.

## Conjectures

None opened.

## Counterexamples

None to the local remainder equations or the cycle balance. The
stronger claim that fails as a universal statement:

- “a positive remainder forces the next remainder to grow” — start 9
  has remainders \(0,83,19\).

A transient that realises every local remainder does **not** refute a
cycle-only theorem. Off-cycle, the balance fails by the correction
\(x_0^{2}-x_k^{2}\).

## Formalization

`formal/Problems/Engine/FloorPower.lean` gained only the local
remainder lemmas that belong there:

- `localDefectEven_lt_succ` / `localDefectOdd_lt_succ`
- `branchDefect` / `branchExp` / `branchDefect_add` / `branchDefect_lt`

`formal/Problems/Engine/CycleItinerary.lean` gained the cycle system:

- `cycle_remainder_eq` / `cycle_remainder_lt`
- `cycle_remainder_balance`
- `cycle_remainders_project_to_envelope`
- `cycle_not_localsTight` / `cycle_exists_pos_remainder`
- `cycleMax_pred_cube_strict` / `cycle_peak_odd_remainder_pos`

Not added: `RemainderDynamics`, `Energy`, `OddLanding`,
`MilestoneGraph`, `CycleEngine`, `PowerHeight`. No `sorry`. No halt
theorem. No `no_juggler_cycle`. No `PowerBoundEq` in `CycleItinerary`.

## Results

Classification **CYCLIC_ROUNDING_GREEN**, with secondary
**CYCLIC_ROUNDING_NEW_CONSTRAINT** and
**CYCLE_REMAINDER_RIGIDITY_GREEN**.

The remainders refine the envelope. They do not yet produce a
word-independent cycle obstruction. Universal remainder
amplification is false.

## Open questions

Answered in
[juggler_cycle_diophantine.md](juggler_cycle_diophantine.md): the
sequential peak identity exists and is the envelope slack
\(x^3-p^{2^{r+1}}=2\varepsilon p^{2^r}+\varepsilon^2+\delta\). Do not
open a remainder-dynamics object.

## Decision

**PROMOTE** the remainder API, the cyclic balance, and the all-zero
rigidity. Do not claim a cycle obstruction. Do not build remainder
dynamics. Do not claim termination.

Best next question: answered in
[juggler_cycle_diophantine.md](juggler_cycle_diophantine.md).

## Publication assessment

Status: `EXPLORATORY`. A remainder-refinement lemma, not a paper
candidate and not a Juggler totality result.
