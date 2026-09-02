# Juggler top excursions

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can the global maximum of a nontrivial cycle be turned into a
word-independent turning-point constraint: a finite even run from
\(M\) onto an odd landing \(p\), with a two-sided scale window for
the ascent \(p\to M\)?

## Exact statement

For a `CycleMax n w` with \(n\ge 2\), there exists \(r\ge 1\) such
that the first \(r\) iterates are even and the next state \(p\) is
odd. Then

\[
p^{2^r}\le n<(p+1)^{2^r}.
\]

The cycle rotates to the top normal form

\[
p\xrightarrow{u}n\xrightarrow{E^r}p,
\]

with \(T_u(p)=n\) and

\[
3^{\#O(u)}\ge 2^{|u|+r}.
\]

The last inequality is the general scale law: any realized itinerary from
a start \(q\ge 2\) to a state at least \(q^{2^s}\) satisfies
\(3^{\#O}\ge 2^{k+s}\).

The integer window is nonempty. This does not force \(p\) to be the
cycle minimum and does not force \(r=1\). It does not prove that the
ascent cannot land in the window.

This says nothing about totality. Do not prove that every cycle itinerary
is impossible.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Cycle extrema \(m\) odd, \(M\) even, \(M>m^2\) —
  **EXACT — LEAN VERIFIED**.
- Square-scale prefixes are superquadratic —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The maximum is normalized as an
even run. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     max begins E^r onto odd p with a two-sided scale window
Novelty hypothesis      iterated isqrt cells plus PowerBound give a top normal form
Falsifier               a cycle max with no odd landing; or M outside [p^{2^r}, (p+1)^{2^r})
Existing machinery      CycleMax, square_scale_superquadratic, power_bound_word
Maximum Phase-0 scope   even-run bounds; top normal form; scale-superquadratic; transient tops
Promotion criterion     reusable top normal form, or a sharp two-sided window
Stop criterion          cycle engine; itinerary census; FloorPower rewrite; ascent-contradiction claim without proof
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- even-run lower scale \(T^r(x)^{2^r}\le x\) —
  **EXACT — LEAN VERIFIED**
- even-run upper cell \(x<(T^r(x)+1)^{2^r}\) —
  **EXACT — LEAN VERIFIED**
- scale-superquadratic prefixes —
  **EXACT — LEAN VERIFIED**
- top normal form \(p\to M\to E^r\to p\) —
  **EXACT — LEAN VERIFIED**
- the ascent cannot fit the window — not claimed
- \(T(M)=m\) — not claimed
- \(r=1\) always — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_top_excursion`
- Records: [juggler_cycle_top_excursion.md](../research/juggler_cycle_top_excursion.md),
  [juggler_cycle_top_excursion.json](../research/juggler_cycle_top_excursion.json)
- Tests: `tests/research/juggler_sequence/test_cycle_top_excursion.py`
- The Research Engine control layer is not modified.
- Finite-orbit maxima only. No cycle-state search.

## Conjectures

None opened.

## Counterexamples

None to the window or the normal form. The stronger claims that fail:

- “the top window is empty” — it is a nonempty integer interval.
- “every top run has length 1” — transients exhibit \(r\ge 2\).
- “\(T(M)\) is the cycle minimum” — the landing may sit strictly
  above the minimum.
- “ordinary overshoots close a top excursion” — 37 and 77 collapse
  through the window without returning to the landing.

## Formalization

`formal/Problems/Engine/CycleItinerary.lean`, a small extension. Added:

- `even_iter_pow_le` / `even_iter_lt_succ_pow`
- `power_scale_superquadratic` / `top_ascent_superquadratic`
- `cycleMax_top_even_run` / `cycleMax_top_normal_form`

`FloorPower` and `Progress` are not rewritten. No `sorry`. No halt
theorem. No `no_juggler_cycle`. No `CycleSearch`. No length
classification. No ascent-contradiction theorem. No `PowerBoundEq`
attack. No `PowerHeight`.

## Results

Classification **TOP_EXCURSION_GREEN**, with secondary
**TOP_SCALE_WINDOW_GREEN** and **TOP_WINDOW_SURVIVES**.

The maximum is a reusable turning point. The two-sided window is
sharp and nonempty. The ascent is not shown to overshoot it.

## Open questions

Answered in [juggler_cycle_top_pred.md](juggler_cycle_top_pred.md):
the maximum is reached from an odd predecessor \(x\) with
\(p<x<M\) and nested cells. The cells survive; they do not empty a
top-run length. Do not start a first-cell census. Do not reopen
length 7.

## Decision

**PROMOTE** the top even-run, the two-sided window, and the landing
normal form. Do not claim that the ascent is impossible. Do not claim
that \(T(M)=m\). Do not claim termination.

Best next question: answered in
[juggler_cycle_top_pred.md](juggler_cycle_top_pred.md).

## Publication assessment

Status: `EXPLORATORY`. A maximum-normalization lemma, not a paper
candidate and not a Juggler totality result.
