# Juggler internal-E scale barriers

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can an internal even step, together with the cycle-minimum scale
barrier, bootstrap an existing next-square suffix threshold strongly
enough to exclude the first mixed E-terminating cycle itineraries?

## Exact statement

If `CycleMin n (u ++ [E] ++ v ++ [E])` and

\[
\forall m\ge N,\qquad
\bigl(\mathrm{follows}(m,v)\Rightarrow T_v(m)\ge(m+1)^2\bigr),
\]

then there is no such cycle minimum at any \(n\ge N\).

The reason is cycle-internal, not an orbit-minimality hypothesis. The
minimum state \(n\) is odd. Any later even cycle state \(z\) satisfies
\(z\ge n^2\), because \(T(z)\) is also a cycle state and the even branch
is a square root. Hence \(y=T(z)\ge n\). A next-square threshold at
\(y\) gives

\[
T_v(y)\ge(y+1)^2\ge(n+1)^2,
\]

which contradicts the last-even cell \(T_v(y)<(n+1)^2\).

The inequality \(y>n\) is not required. If \(n^2<z<(n+1)^2\), then
\(y=n\), and that is already enough.

Applied to the normalized expanding length-6 E-words:

- `OOOOOE` is already excluded by the inherited `OOOO` threshold.
- `OEOOOE` is impossible as a cycle minimum, by bootstrap with suffix
  `OOO`.
- `OOEOOE` is impossible as a `CycleItinerary`: every rotation is a cycle
  minimum that either starts `E`, starts `OE`, or is `OOEOOE` itself.
- `OOOEOE` has suffix `O` after the internal `E`. There is no
  next-square `O` threshold, so bootstrap does not apply.
- `OOOOEE` is not free from `OOOOE`: \(T_{OOOO}\ge(n+1)^2\) does not
  imply \(T_{OOOOE}\ge(n+1)^2\).

This says nothing about cycles ending in `O`. It does not exclude every
length-6 E-terminating word. Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Last-even cycle cell —
  **EXACT — LEAN VERIFIED**.
- `OO` / `OOO` suffix thresholds —
  **EXACT — LEAN VERIFIED**.
- No length-4 or length-5 E-terminating cycle —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The cycle-minimum scale barrier
transports an existing threshold across an internal even step. Totality
remains unclaimed.

## Branch budget

```text
Mathematical target     can an internal E plus cycle-min scale bootstrap an existing next-square suffix?
Novelty hypothesis      even cycle states satisfy z ≥ n_min², so T(z) ≥ n_min and a known suffix threshold fires
Falsifier               y < n still lands in the last-even cell; or z ≥ n² is false for a cycle min
Existing machinery      exists_cycle_min_odd, oo/ooo thresholds, no_cycle_append_even_of_suffix_threshold
Maximum Phase-0 scope   CycleMin even-barrier; generic bootstrap; OOEOOE / OEOOOE; record OOOEOE
Promotion criterion     reusable bootstrap, or OOEOOE / OEOOOE excluded
Stop criterion          cycle engine; 2^6 census; FloorPower rewrite; O-terminating programme
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- cycle minimum even-scale barrier \(z\ge n^2\) —
  **EXACT — LEAN VERIFIED**
- a cycle minimum cannot start `OE` —
  **EXACT — LEAN VERIFIED**
- internal-E bootstrap of a next-square suffix —
  **EXACT — LEAN VERIFIED**
- no `CycleMin` for `OEOOOE` or `OOEOOE` —
  **EXACT — LEAN VERIFIED**
- no `CycleItinerary` for `OOEOOE` —
  **EXACT — LEAN VERIFIED**
- no length-6 E-terminating cycle — not claimed
- `OOOEOE` is impossible — not claimed
- `OOOOEE` is impossible — not claimed
- cycles ending in `O` are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_internal_e`
- Records: [juggler_cycle_internal_e.md](../research/juggler_cycle_internal_e.md),
  [juggler_cycle_internal_e.json](../research/juggler_cycle_internal_e.json)
- Tests: `tests/research/juggler_sequence/test_cycle_internal_e.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No evaluation of the huge eventual \(Q_0\).

## Conjectures

None opened.

## Counterexamples

None to the bootstrap. The stronger claims that fail:

- “\(y>n\) is required” — \(y\ge n\) already overshoots the last-even
  cell.
- “`OOOOEE` dies through the `OOOOE` threshold” —
  \(T_{OOOO}\ge(n+1)^2\) does not lift across the extra `E`.
- “every mixed length-6 E-word is excluded” — `OOOEOE` has suffix `O`.
- “`¬CycleMin` is `¬CycleItinerary`” — `OEOOOE` rotates onto `OOOEOE`.

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, a small extension. Added:

- `CycleMin` / `cycleMin_even_ge_sq` / `cycleMin_not_odd_even`
- `no_cycleMin_internal_even_threshold`
- `no_cycleMin_oeoooe` / `no_cycleMin_ooeooe`
- `no_cycle_itinerary_ooeooe`

`FloorPower`, `Progress`, and the orbit-minimum module are not
rewritten. No `sorry`. No halt theorem. No `no_juggler_cycle`. No
`CycleSearch`. No length-6 classification theorem. No `PowerBoundEq`
attack. No `PowerHeight`.

## Results

Classification **INTERNAL_E_BOOTSTRAP_GREEN**, with secondary
**OOOEOE_EXCEPTION**.

The generic theorem is the reusable result. `OOEOOE` is fully excluded.
`OEOOOE` is excluded as a cycle minimum. `OOOEOE` and `OOOOEE` remain
as leftovers of this bootstrap. A later branch,
[juggler_leftover_cycles](juggler_leftover_cycles.md), excludes both
as `CycleItinerary`. That is not this branch's next-square-suffix argument;
the `PROMOTE` here is unchanged.

## Open questions

The itinerary-length programme is stopped. The next opened branch is
[juggler_cycle_extrema.md](juggler_cycle_extrema.md). The parked
word-specific question remains: what exact extra scale does the prefix
`OOO` give before the internal `E` of `OOOEOE`? Do not open length 7.

## Decision

**PROMOTE** the cycle-minimum even barrier and the internal-E bootstrap.
Do not claim that all length-6 E-terminating cycles are impossible. Do
not claim termination. Do not treat cycles ending in `O`.

Best next question: answered by a pivot to
[juggler_cycle_extrema.md](juggler_cycle_extrema.md). The parked
`OOOEOE` scale question is not reopened here.

## Publication assessment

Status: `EXPLORATORY`. A threshold-transport lemma, not a paper
candidate and not a Juggler totality result.
