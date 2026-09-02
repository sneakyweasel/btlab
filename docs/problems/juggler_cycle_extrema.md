# Juggler cycle extrema

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can the existing power, parity, and cell machinery impose incompatible
constraints on the excursion from a cycle minimum \(m\) to a cycle
maximum \(M\) and back, without enumerating cycle itineraries?

## Exact statement

For a nontrivial `CycleItinerary` with \(n\ge 2\), write \(m\) for a
minimum state and \(M\) for a maximum state. Then:

- \(m\) is odd,
- \(M\) is even,
- \(M>m^2\),
- \(M\ge(m+1)^2\).

The first scale inequality is strict because \(m^2\) is odd.
Equivalently, \(T(M)=\lfloor\sqrt M\rfloor\ge m\), so \(M\ge m^2\),
and parity forbids equality. First-even overshoot on a `CycleMin`
then places the first even residual at or above \((m+1)^2\), so the
maximum satisfies \(M\ge(m+1)^2\) and \(T(M)>m\).

Any realized finite itinerary from a start \(n\ge 2\) to a state at least
\(n^2\) is superquadratic:

\[
3^{\#O(w)}\ge 2^{|w|+1}.
\]

In particular, on a cycle minimum the path to any later even state —
including the maximum — is superquadratic. This is stronger than the
full-cycle envelope \(3^{\#O}>2^{|w|}\): the prefix `OOE` is expanding
(\(9>8\)) but not superquadratic (\(9<16\)), so it cannot carry \(m\)
to square scale.

The maximum return cell is the ordinary even branch:

\[
T(M)=q=\lfloor\sqrt M\rfloor,\qquad
M\in[q^2,(q+1)^2),\qquad q\ge m.
\]

This does not force \(q=m\). The first-cell family
\(M\in(m^2,(m+1)^2)\) is excluded: \(M\ge(m+1)^2\). The landing
satisfies \(q>m\).

This says nothing about cycles ending in a particular letter. Do not
prove that every cycle itinerary is impossible. Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Cycle minimum is odd —
  **EXACT — LEAN VERIFIED**.
- Finite-itinerary power envelope —
  **EXACT — LEAN VERIFIED**.
- Internal-E bootstrap —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. Extrema are packaged independently
of itinerary length. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     extrema force M ≥ (m+1)^2 and a superquadratic min-to-even path
Novelty hypothesis      first-even overshoot excludes first-cell maxima
Falsifier               a CycleMin whose max sits below (m+1)^2
Existing machinery      CycleMin, cycleMin_first_even_overshoots, cycleMin_max_gt_sq
Maximum Phase-0 scope   CycleMax; M ≥ (m+1)^2; square-scale superquadratic; transient calibration
Promotion criterion     reusable extrema package, or a genuine prefix law
Stop criterion          cycle engine; itinerary census; FloorPower rewrite; first-cell census
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- cycle maximum is even —
  **EXACT — LEAN VERIFIED**
- \(M>m^2\) on a cycle minimum —
  **EXACT — LEAN VERIFIED**
- \(M\ge(m+1)^2\) on a cycle minimum, equivalently first-cell
  maxima are impossible —
  **EXACT — LEAN VERIFIED**
  (`cycleMin_max_ge_succ_sq`, `cycleMax_min_succ_sq_le`)
- \(T(M)>m\) —
  **EXACT — LEAN VERIFIED** (`cycleMax_landing_gt_min`)
- square-scale image implies superquadratic word —
  **EXACT — LEAN VERIFIED**
- min-to-even (hence min-to-max) prefixes are superquadratic —
  **EXACT — LEAN VERIFIED**
- growth and collapse cannot coexist — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_extrema`
- Records: [juggler_cycle_extrema.md](../research/juggler_cycle_extrema.md),
  [juggler_cycle_extrema.json](../research/juggler_cycle_extrema.json)
- Tests: `tests/research/juggler_sequence/test_cycle_extrema.py`
- The Research Engine control layer is not modified.
- Stay-above-min transient calibration only. No cycle-state search.
- No evaluation of huge eventual \(Q_0\).

## Conjectures

None opened.

## Counterexamples

None to the extrema package. The stronger claims that fail:

- “every odd start hits \(m^2\) before dropping” — `7` walks
  `O` then `E` and falls to `4`.
- “the cycle envelope already forces the prefix law” — `OOE` is
  expanding and not superquadratic.
- “\(M=m^2\) is possible” — \(m\) odd makes \(m^2\) odd.
- “the maximum must collapse to the minimum” — the return cell
  permits \(q>m\); first-even overshoot now forces \(q>m\).
- “first-cell maxima survive” — \(M\ge(m+1)^2\).

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, a small extension. Added:

- `CycleMax` / `exists_cycle_max_even` / `cycleMax_start_even`
- `cycleMin_max_gt_sq` / `cycleMax_return_preimage`
- later, in `EvenCountThree.lean`: `cycleMin_max_ge_succ_sq` /
  `cycleMax_min_succ_sq_le` / `cycleMax_landing_gt_min` /
  `cycleMax_exists_min_succ_sq` / `cycle_distinguished_order_succ_sq`
- `square_scale_superquadratic`
- `cycleMin_to_even_superquadratic` / `cycleMin_to_max_superquadratic`

`FloorPower` and `Progress` are not rewritten. No `sorry`. No halt
theorem. No `no_juggler_cycle`. No `CycleSearch`. No length
classification. No first-cell census. No `PowerBoundEq` attack. No
`PowerHeight`.

## Results

Classification **CYCLE_EXTREMES_GREEN**, with secondary
**ASCENDING_SUPERQUADRATIC_GREEN**.

The package is reusable and word-independent. It is not a
growth-versus-collapse obstruction. Ordinary transients often drop
before square scale, so the cycle demand \(M\ge(m+1)^2\) is not
vacuous. First-cell maxima are excluded by first-even overshoot,
not by a cell census.

## Open questions

Answered in [juggler_cycle_top_excursion.md](juggler_cycle_top_excursion.md)
and [juggler_cycle_top_pred.md](juggler_cycle_top_pred.md): the
maximum begins a finite even run onto an odd landing, then is
reached from a strict odd predecessor inside nested cells. The cells
survive. Do not start a first-cell census. Do not reopen length 7.

## Decision

**PROMOTE** the extrema package, the square-scale prefix law, and
the first-cell exclusion \(M\ge(m+1)^2\). Do not claim that growth
and collapse cannot coexist. Do not claim termination. Do not start
a first-cell census.

Best next question: answered in
[juggler_cycle_top_excursion.md](juggler_cycle_top_excursion.md).

## Publication assessment

Status: `EXPLORATORY`. An extrema-and-prefix lemma, not a paper
candidate and not a Juggler totality result.
