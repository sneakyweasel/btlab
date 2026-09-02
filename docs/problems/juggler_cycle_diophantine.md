# Juggler cycle Diophantine defects

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

The cyclic-rounding open question asked for a sequential, non-sum
remainder identity that uses \(T_w(n)=n\). Do the peak odd defect
\(\delta\) and the top even-run defect \(\varepsilon\) impose a
congruence or residual-class restriction that the existing power
envelope cannot see?

## Exact statement

For a `CycleMax n w` with \(n\ge 2\), write \(M=n\), let \(x\) be the
odd predecessor, and let \(p=T^r(M)\) be the odd landing after the
maximal even run. Existing cells already give

\[
x^3=M^2+\delta,\qquad 0\le\delta<2M+1,
\]

\[
M=p^{2^r}+\varepsilon,\qquad
0<\varepsilon<(p+1)^{2^r}-p^{2^r}.
\]

The sequential composition is

\[
x^3=\bigl(p^{2^r}+\varepsilon\bigr)^2+\delta,
\]

equivalently the exact slack of the known lower cell

\[
x^3-p^{2^{r+1}}=2\varepsilon\,p^{2^r}+\varepsilon^2+\delta.
\]

Parity already forces \(\delta>0\), \(\varepsilon>0\), and both odd.
The residual class \(R=\{1,\ldots,11\}\) is `ReachesOne`. A
nontrivial cycle therefore cannot visit \(R\), so \(p\ge 13\).

This says nothing about totality. Do not prove that every cycle itinerary
is impossible. Do not introduce remainder dynamics, a Mordell solver,
or a cycle engine.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Local defects and cyclic remainder balance —
  **EXACT — LEAN VERIFIED**.
- Nested top cells and peak scale \(x^3\ge p^{2^{r+1}}\) —
  **EXACT — LEAN VERIFIED**.
- Extremal composition of scale laws —
  **REPARAMETERIZATION** of the envelope.

Project relationship: **extended**. The sequential peak identity is
named. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does the peak pair (δ, ε) impose a congruence
                        or residual-class restriction that the existing
                        scale envelope cannot see?
Novelty hypothesis      x^3 = (p^{2^r}+ε)^2+δ is sequential, not a sum,
                        and (p,ε,δ) may be modularly rigid; R={1..11}
                        may force p≥13 on a nontrivial cycle.
Falsifier               The composition is only the known slack
                        x^3 − p^{2^{r+1}} = 2εp^{2^r}+ε^2+δ, and every
                        residue law is odd/odd or a known cell.
Existing machinery      localDefectOdd, cycle_top_window_strict,
                        cycle_top_nested_cell, cycle_peak_odd_remainder_pos,
                        cycle_remainder_balance, reachesOne_of_lt_twelve
Maximum Phase-0 scope   Named δ/ε wrappers; composition identity;
                        cheap residue census on transients; at most one
                        new congruence; R-avoidance of cycle states.
Promotion criterion     A cycle-forced congruence or residual restriction
                        that still-allowed scale inequalities do not imply.
Stop criterion          DIOPHANTINE_REPACKAGING: composition = envelope
                        slack + existing parity. No RemainderDynamics,
                        no Mordell solver, no itinerary census, no halt.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- peak odd defect \(\delta=x^3-M^2\) in the successor window —
  **EXACT — LEAN VERIFIED** (wrapper of `localDefectOdd`)
- top even-run defect \(\varepsilon=M-p^{2^r}\) with the existing
  strict window —
  **EXACT — LEAN VERIFIED** (wrapper of `cycle_top_window_strict`)
- \(\delta\) and \(\varepsilon\) odd —
  **EXACT — LEAN VERIFIED**, and a **REPARAMETERIZATION** of the
  existing peak/top parity
- sequential composition
  \(x^3=(p^{2^r}+\varepsilon)^2+\delta\) —
  **EXACT — LEAN VERIFIED**, and a **REPARAMETERIZATION** of the
  nested cells
- slack identity
  \(x^3-p^{2^{r+1}}=2\varepsilon p^{2^r}+\varepsilon^2+\delta\) —
  **EXACT — LEAN VERIFIED**, and a **REPARAMETERIZATION** of
  `cycle_top_pred_scale`
- cycle states avoid \(R=\{1,\ldots,11\}\), hence \(p\ge 13\) —
  **EXACT — LEAN VERIFIED**, a named corollary of
  `reachesOne_of_lt_twelve` plus cyclic return
- a modular restriction stronger than odd/odd — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_diophantine`
- Records: [juggler_cycle_diophantine.md](../research/juggler_cycle_diophantine.md),
  [juggler_cycle_diophantine.json](../research/juggler_cycle_diophantine.json)
- Tests: `tests/research/juggler_sequence/test_cycle_diophantine.py`
- The Research Engine control layer is not modified.
- Finite-orbit peak cells only. No cycle-state search.

## Conjectures

None opened.

## Counterexamples

None to the composition or the slack identity. The stronger claims
that fail:

- “the sequential identity is not the envelope slack” — it is
  exactly \(x^3-p^{2^{r+1}}=2\varepsilon p^{2^r}+\varepsilon^2+\delta\).
- “\((\delta,\varepsilon)\) is modularly rigid beyond odd/odd” —
  transient peaks realise several residues mod \(8\) and \(16\).
- “\(R\) forbids a residue class of \(p\) on transients” —
  starts \(3\), \(7\), and \(9\) land in \(R\). The \(p\ge 13\)
  bound is cycle-only and only upgrades \(2\le p\).

A transient that realises the two peak cells does **not** refute a
cycle-only theorem.

## Formalization

`formal/Problems/Engine/CycleDiophantine.lean`, imported from
`formal/Problems.lean`. Wrappers and the sequential identity only.
`CycleItinerary.lean` and `FloorPower.lean` are not rewritten.

Added:

- `peakOddDefect` / `topEvenDefect`
- `peakOddDefect_add` / `_lt` / `_odd` / `_pos`
- `topEvenDefect_add` / `_pos` / `_lt` / `_odd`
- `peak_diophantine_compose` / `peak_diophantine_slack`
- `cycle_peak_diophantine` / `cycle_peak_diophantine_slack`
- `cycle_top_landing_ge_thirteen`
- `cycleItinerary_not_reachesOne` / `cycleItinerary_iterate_not_lt_twelve`
  (cycle facts; live in `CycleCore.lean`)

Not added: a modular lemma beyond odd/odd, `RemainderDynamics`,
`Energy`, `OddLanding`, `MilestoneGraph`, `CycleEngine`,
`PowerHeight`, a Mordell solver. No `sorry`. No halt theorem. No
`no_juggler_cycle`. No ledger row.

## Results

Classification **DIOPHANTINE_REPACKAGING**, with secondary
**CYCLE_R_AVOIDANCE_GREEN**.

The sequential peak identity exists and uses the two cells rather
than a path-sum. Its arithmetic content is the known slack of
`cycle_top_pred_scale` plus the existing odd/odd parity. The residual
class \(R\) only upgrades \(2\le p\) to \(13\le p\).

## Open questions

The peak pair \((\delta,\varepsilon)\) is envelope slack. Do not
reopen defect composition, another modulus, or a remainder-dynamics
object. Answered in
[juggler_odd_odd_residual.md](juggler_odd_odd_residual.md):
non-extremal odd-odd continuation is
`ODD_ODD_RESIDUAL_COMPLEX`.

## Decision

**CLOSE** the Diophantine peak-pair branch as
`DIOPHANTINE_REPACKAGING`. Record the named defects, the sequential
identity, and the cycle \(R\)-avoidance corollary. Do not claim a
word-independent cycle obstruction. Do not claim termination.

Best next question: answered in
[juggler_odd_odd_residual.md](juggler_odd_odd_residual.md).

## Publication assessment

Status: `EXPLORATORY`. A negative sequential-identity result, not a
paper candidate and not a Juggler totality result.
