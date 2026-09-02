# Juggler cycle equal valleys

Status: **ARCHIVED**

Compiled leftover written as
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).

Standalone application phase on the Juggler floor-power map, on the
**cycle half** of the `cycles_or_escapes` split. It asks whether a
cycle can have every local minimum equal to the global minimum, and
whether forbidding that coincidence excludes leftover \((L,m)\). It
is not a leftover-length census, not a floor raise, not a
formalization of the height law, and not a halt theorem.

## Problem

Joint-minima finance charges every valley at the CycleMin start
\(n\). That is the worst case. Can it actually happen? If all \(m\)
valleys equal \(n\) is impossible, the next odd \(n+2\) might
tighten the leftover pair \(L=84\), \(m\ge 3\) at the live residual
floor \(261\).

## Exact statement

A **local minimum** is a cyclic even-to-odd landing. An
**\(m\)-cycle** has \(m\) blocks \(O^{k_i}E^{\ell_i}\). `CycleItinerary n w`
is a realized return \(T_w(n)=n\). `CycleMin` adds that every
interior state is \(\ge n\).

**Unique visit (REPARAMETERIZATION of prefix return).**
If `CycleItinerary n w` and \(0<k<L\) satisfy \(T^k(n)=n\), then
`follows_take` and `image_take_of_le` give `CycleItinerary n (w.take k)`.
On a leftover length — currently \(L=84\) or \(\ge 85\), with every
shorter length already excluded — there is no such \(k\). Hence \(n\)
occurs once per period. The CycleMin start is that unique occurrence
and is a local minimum. For \(m\ge 2\), every other valley is a
different odd state, so \(\ge n+2\).

For \(m=1\) the single valley is \(n\) tautologically. Height law
already excludes \(L=84\) as a 1-cycle at floor \(261\).

**Equal-valleys leftover-killer (REFUTED).**
Charging one valley at \(n\) and the other \(m-1\) at \(n+2\)
excludes leftover \(L=84\) at \(m\ge 3\) at floor \(261\).

Counterexample: \(L=84\), \(o=53\), \(m=3\), \(n=261\),
\(\theta\approx 0.002086\). Lean constant \(1\):

- all valleys at \(n\): RHS \(\approx 0.003527\)
- split \(n\) and \(n+2\): RHS \(\approx 0.003515\)
- height law, all valleys at \(n\): RHS \(\approx 0.002193\)
- height law plus split \(n+2\): RHS \(\approx 0.002180\)

None is below \(\theta\). Joint-style split never kills: the fifty
climb interiors charged at \(T(261)=4216\) already exceed the
gap. Height-split would need the other valleys \(\ge 281\), which
\(n+2=263\) does not give.

No cycle of any length — not claimed.

## Current literature

- Cycle finance leftover is period \(84\) with \(m\ge 3\) or
  \(\ge 85\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`,
  [juggler_cycle_finance.md](juggler_cycle_finance.md))
- Prefix itinerary: `follows_take`, `image_take_of_le` —
  **EXACT — LEAN VERIFIED** (`Itinerary.lean`)
- Joint-minima finance —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_m_finance.md](juggler_cycle_m_finance.md))
- Odd-run height law; \(L=84\) at \(m=1,2\) dies at floor \(261\) —
  **EXACT — LEAN VERIFIED**
  ([juggler_cycle_position_finance.md](juggler_cycle_position_finance.md))
- Residual-floor campaign to \(4756\) / \(1981\) —
  **PARK** / **REFUTED** as the cheapest kill of \(L=84\)
  (`juggler_cycle_finance_l84_floor_4756`)
- First-return excursions —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_first_return_excursions.md](juggler_first_return_excursions.md))
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover killer; unique visit
is **known** first-return.

## Branch budget

```text
Mathematical target     Can all m valleys equal the CycleMin start n,
                        and if not, does the next odd n+2 exclude
                        leftover (L, m) at floor 261?
Novelty hypothesis      forbidding a repeated global minimum is a
                        new valley-height law, not first-return
Falsifier               unique visit is prefix return; n+2 does not
                        move any leftover pair below θ
Existing machinery      CycleItinerary, follows_take, image_take_of_le,
                        leftover 84 or ≥85, joint-minima, height law
Maximum Phase-0 scope   prefix-return uniqueness; split-valley
                        arithmetic at L=84, m=3, floor 261.
                        No Lean, no floor raise, no height-law file
Promotion criterion     a valley-separation law that is not
                        first-return and that excludes a leftover pair
Stop criterion          REPARAMETERIZATION plus n+2 fails to kill
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Intermediate return \(T^k(n)=n\) is a shorter `CycleItinerary` —
  **REPARAMETERIZATION** of `follows_take` / `image_take_of_le`
- On leftover \(L\), \(n\) occurs once; \(m\ge 2\) forces a valley
  \(\ge n+2\) —
  **EXACT — HUMAN PROOF**
- Split-valley finance at \(n+2\) excludes \(L=84\), \(m\ge 3\) —
  **REFUTED** (`juggler_equal_valleys_leftover_killer`)
- Height plus \(n+2\) excludes \(L=84\), \(m=3\) —
  **REFUTED** at floor \(261\); would need the other valleys
  \(\ge 281\)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_equal_valleys`
- Records: [juggler_cycle_equal_valleys.md](../research/juggler_cycle_equal_valleys.md),
  [juggler_cycle_equal_valleys.json](../research/juggler_cycle_equal_valleys.json)
- Dataset: `data/research/juggler/cycle_equal_valleys/`
- Tests: `tests/research/juggler_sequence/test_cycle_equal_valleys.py`

Science window: leftover \(L=84\) at floor \(261\), \(m=3,4,31\),
constants \(1\) and \(6/5\). No CLI. No new Lean. Paper A is
unchanged.

## Conjectures

`juggler_cycle_all_valleys_equal` — **REFUTED**.

`juggler_equal_valleys_leftover_killer` — **REFUTED**.

## Counterexamples

- A leftover-length \(m\)-cycle with all valleys equal to \(n\)
  would be a shorter `CycleItinerary` at the first repeated visit.
- \(L=84\), \(m=3\), \(n=261\): split RHS \(0.003515>\theta\);
  height plus \(n+2\) is \(0.002180>\theta\).

## Formalization

None added. `follows_take` and `image_take_of_le` already exist.
Not added: `CycleEqualValleys.lean`, `UniqueValley.lean`,
`SecondValley`. No `sorry`. Paper A is unchanged. Not a halt
theorem.

## Results

Classification **EQUAL_VALLEYS_CLOSED**. Regenerate with
`python -m research.juggler_sequence.cycle_equal_valleys`.

- All \(m\) valleys equal \(n\) is impossible for \(m\ge 2\) on a
  leftover length. That is prefix return, not a new scale law.
- The next odd \(n+2\) changes the \(m=3\) joint RHS by about
  \(0.3\%\). Climbs charged at \(T(n)\) dominate the slack.
- Stacking uniqueness on the height law still misses \(L=84\) at
  \(m=3\); the other valleys would have to reach \(281\).
- No leftover pair dies. No floor is raised.

## Open questions

Stop on equal valleys as a leftover killer. Do not raise the
residual floor. A second-valley bound \(\ge 281\) was opened and
**CLOSE** / **REFUTED**
([juggler_cycle_second_valley.md](juggler_cycle_second_valley.md)).

## Decision

**CLOSE**. The literal question has a first-return answer: impossible
for \(m\ge 2\) on leftover lengths. The only novel reading — that
\(n+2\) excludes a leftover pair — is false at the live pair
\((84,3)\). This is not a halt theorem and not a reason to raise
the floor.

Best next question: answered in
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).
The height leftover is Lean; excluding \(m\ge 3\) at floor
\(261\) is **REFUTED**
([juggler_cycle_l84_m3.md](juggler_cycle_l84_m3.md)).

## Publication assessment

Status: `ARCHIVED`.

A negative compression: unique visit of the CycleMin start is
classical first-return, and \(n+2\) is not a leftover-killing
height. Not a paper candidate and not a Juggler totality result.
