# Juggler length-84 leftover at \(m\ge 3\)

Status: **ARCHIVED**

Compiled leftover written as
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).

Follow-up to
[position-dependent finance](juggler_cycle_position_finance.md).
It asks whether leftover length \(84\) with at least three odd-runs
dies at the live residual floor \(261\). It is not a floor raise,
not a `PositionFinance` layer, and not a halt theorem.

## Problem

Height finance already excludes length \(84\) at \(m\le 2\) at
floor \(261\). The laboratory leftover is therefore period \(84\)
with \(m\ge 3\), or length \(\ge 85\). Does any cheap refinement
kill the remaining \(m\) at the same floor?

## Exact statement

Write \(\theta=1-2^{84}/3^{53}\approx 0.002086\). At \(n=261\),
\(o=53\), \(m=3\):

- Height packing, constant \(1\): RHS \(\approx 0.002193>\theta\).
- Height packing, constant \(6/5\): RHS \(\approx 0.002631>\theta\).
- Joint-minima, constant \(1\): RHS \(\approx 0.003527>\theta\).
- Lean inv-sum (valleys \(1/n\), climbs \(1/\tau_j\), evens
  \(1/n^2\)) versus \(\theta\cdot 61/11\):
  \(S\approx 0.012672>0.011568\).
- Singleton start (\(T(261)=4216\) is even, so the CycleMin
  odd-run has length \(1\)) plus other valleys at \(n+2\):
  RHS \(\approx 0.002179>\theta\).

None excludes \(m=3\). Larger \(m\) is worse. Height first kills
\(m=3\) at floor \(273\) and every \(m\) at \(1981\). Those
raises stay **PARK**.

Equal-valleys \(n+2\) is already **REFUTED**
([juggler_cycle_equal_valleys.md](juggler_cycle_equal_valleys.md)).

No cycle of any length — not claimed.

## Current literature

- Lean leftover is period \(84\) with \(m\ge 3\) or \(\ge 85\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`)
- Height packing kills \(m=1,2\) at \(261\), \(m=3\) at \(273\),
  all \(m\) at \(1981\) —
  **COMPUTATIONALLY VERIFIED** (`l84_floors.json`)
- \(n+2\) valleys —
  **REFUTED** as a leftover killer
- Residual-floor factory to \(1981\) / \(4756\) — **PARK**
- Every start reaches 1 — not claimed

Project relationship: **refuted** slogan; leftover unchanged.

## Branch budget

```text
Mathematical target     Does any argument at residual floor 261
                        exclude every length-84 CycleMin with
                        m≥3, so the leftover becomes L≥85?
Novelty hypothesis      pigeonhole on 53 odds in ≥3 runs, or a
                        tighter inv-sum than the two-level cap,
                        yields a contradiction that height packing
                        and n+2 valleys do not
Falsifier               every cheap refinement still has S≥θ log n
                        (or θ≤RHS) for some m≥3 at n=261
Existing machinery      cycleMin_finance_inv_sum, oddRunHeight,
                        position_rhs, joint-minima, unique visit,
                        l84_exclusion_floors (m=3 at 273)
Maximum Phase-0 scope   exact slack table at n=261 for m=3
                        under Lean inv-sum, full-height packing,
                        and singleton-start + n+2; no Lean, no
                        floor raise, no PositionFinance layer
Promotion criterion     a new inequality or obstruction that kills
                        every m≥3 at 261
Stop criterion          all refinements miss some m≥3
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Height packing at floor \(261\) excludes \(m\ge 3\) —
  **REFUTED** (`juggler_l84_m_ge_three_floor_261`)
- Lean inv-sum full-height cap excludes \(m=3\) at \(261\) —
  **REFUTED**
- Singleton start plus \(n+2\) excludes \(m=3\) —
  **REFUTED**
- \(n+2\) valleys — already **REFUTED**
- Residual floor \(273\) / \(1981\) — **PARK**
- No cycle of any length — not claimed

## Experiments

- Probe helper: `research.juggler_sequence.cycle_position_finance.l84_m_ge_three_at_floor`
- Tests: `tests/research/juggler_sequence/test_cycle_l84_m3.py`
- No CLI. No new Lean. Paper A is unchanged.

## Conjectures

`juggler_l84_m_ge_three_floor_261` — **REFUTED**.

## Counterexamples

\(L=84\), \(o=53\), \(m=3\), \(n=261\), \(\theta\approx 0.002086\):
height constant \(1\) RHS \(\approx 0.002193\); Lean inv-sum
\(S\approx 0.012672>0.011568\); singleton-start plus \(n+2\)
RHS \(\approx 0.002179\).

## Formalization

None added. `CycleHeightFinance.lean` is unchanged. Not added:
`CyclePositionFinance.lean`, `cycle_height_finance`. No `sorry`.
Paper A is unchanged. Not a halt theorem.

## Results

Classification **CLOSED**. The slogan is false at floor \(261\).

- Every tested refinement misses \(m=3\). Larger \(m\) is worse.
- \(T(261)\) even forces a singleton start run; that plus \(n+2\)
  still misses (same order as the equal-valleys height-split).
- Pigeonhole (\(k\ge 18\) odds in some run) does not starve the
  even budget: \(11\) square-roots return to scale \(n\), and
  \(31-(3-1)=29\) evens are available.
- Height packing first kills \(m=3\) at \(273\) and every \(m\)
  at \(1981\). Those campaigns stay **PARK**.

## Open questions

Stop. The laboratory leftover remains period \(84\) with
\(m\ge 3\), or \(\ge 85\). A second-valley bound \(\ge 281\) was
attacked and **REFUTED**
([juggler_cycle_second_valley.md](juggler_cycle_second_valley.md)).
The upper cell \((p+1)^{2^r}\) was attacked and **REFUTED** as a
leftover-killer
([juggler_cycle_ceiling_finance.md](juggler_cycle_ceiling_finance.md)).

## Decision

**CLOSE**. The target is false: no cheap refinement excludes
length \(84\) at \(m\ge 3\) at floor \(261\). This is not a reason
to raise the floor. Not a halt theorem.

Best next question: answered in
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).

## Publication assessment

Status: `ARCHIVED`. Negative knowledge. Not a paper candidate.
