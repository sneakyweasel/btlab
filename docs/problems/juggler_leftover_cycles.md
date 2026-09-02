# Juggler leftover length-six cycle orientations

Status: **THEOREM**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It does not reopen the closed
uniform-from-\(3\) extra-scale branch.

## Problem

Are the leftover legal `CycleMin` orientations `OOOEOE` and `OOOOEE`
impossible as `CycleItinerary` for every \(n\ge 2\)?

## Exact statement

For every \(n\ge 2\),
\[
\neg\mathrm{CycleItinerary}(n,OOOEOE)
\qquad\text{and}\qquad
\neg\mathrm{CycleItinerary}(n,OOOOEE).
\]
The argument is an exhaustive evaluation for \(n<256\) together with
the last-even cell against the coarse lower envelope
\(n^{81}>2^{130}(n+1)^{64}\) for \(n\ge256\).

This branch proves those two exclusions only. A later consolidation
(`J-small-cycle-census`) assembles them with existing machinery into
the exclusion of every cycle itinerary of length at most six. Neither is a
halt theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Cycle exponent and extrema —
  **EXACT — LEAN VERIFIED**.
- Internal-E bootstrap —
  **EXACT — LEAN VERIFIED**. `OOOEOE` and `OOOOEE` were the leftovers.
- Prefix-OOO extra scale from \(n=3\) —
  **REFUTED**; first forced `OOO` overshoot at \(n=109\). That `CLOSE`
  is not reopened.

Project relationship: **extended**. The parked leftover of
`juggler_cycle_internal_e` and `juggler_cycle_ooo_scale`. Totality
remains unclaimed.

## Branch budget

```text
Mathematical target     Are CycleItinerary n OOOEOE and CycleItinerary n OOOOEE
                        impossible for all n≥2?
Novelty hypothesis      Finite eval below 256 plus n≥256 LowerPowerBound
                        / last-even comparison
Falsifier               A realizing n exists, or the tail is only a
                        rewrite of closed OOO identities
Existing machinery      LowerPowerBound, last-even cells, CycleItinerary,
                        ooo_suffix_threshold
Maximum Phase-0 scope   These two words only; no length-7; no halt
Promotion criterion     Lean exclusion of both CycleItineraries
Stop criterion          Tail fails to formalize or is reparameterization
                        without exclusion
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `CycleItinerary` on `OOOEOE` is impossible —
  **EXACT — LEAN VERIFIED**
- `CycleItinerary` on `OOOOEE` is impossible —
  **EXACT — LEAN VERIFIED**
- every cycle itinerary of length at most six is impossible —
  **EXACT — LEAN VERIFIED** (later consolidation `J-small-cycle-census`,
  `no_cycle_itinerary_length_le_six`; assembly of existing exclusions)
- cycles of length seven or more are impossible — not claimed
- global halt — not claimed

## Experiments

- Lean: `formal/Problems/Juggler/LeftoverEval.lean`,
  `formal/Problems/Juggler/LeftoverCycles.lean`
- Tests: `tests/research/juggler_sequence/test_cycle_leftover_itineraries.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length 7. No O-terminating programme.

## Conjectures

None opened.

## Counterexamples

None to the two exclusions. The stronger claims that remain false:

- “`LowerPowerBound` on `OOO` forces last-even overshoot from \(n=3\)”
  — still fails at \(n=3\) and \(n=5\); this branch uses cutoff \(256\).
- “every length-six word is excluded” — not claimed.

## Formalization

`formal/Problems/Juggler/LeftoverEval.lean` isolates `native_decide`
facts. `formal/Problems/Juggler/LeftoverCycles.lean` proves

- `no_cycle_itinerary_oooeoe`
- `no_cycle_itinerary_ooooee`

`FloorPower`, `Progress`, and `Minimal` are not rewritten. No `sorry`.
No halt theorem. No `no_juggler_cycle`. No `CycleSearch`. No
`PowerBoundEq` attack. No `PowerHeight`. The length-six leftover
file later also hosts the length-seven leftovers
`no_cycle_itinerary_ooooeoe` and `no_cycle_itinerary_oooooee`.

A later consolidation, `formal/Problems/Juggler/SmallCycleCensus.lean`,
assembles the two exclusions with rotation invariance, the all-odd
ascent argument, the expanding filter, and the existing threshold
theorems into `no_cycle_itinerary_length_le_six`: no cycle itinerary of length at
most six at any \(n\ge2\). The assembly adds no new `native_decide`
table. A subsequent length-7 branch added `no_cycle_itinerary_ooooeoe` and
`no_cycle_itinerary_oooooee` to the same leftover file and assembled
`no_cycle_itinerary_length_le_seven`.

## Results

Both leftover orientations are impossible as cycle itineraries
(**EXACT — LEAN VERIFIED**). The math note records this as Lemma 3.5,
the key leftover lemma of the small-cycle census (Theorem 3.6,
`no_cycle_itinerary_length_le_six`, ledger row `J-small-cycle-census`): no
nontrivial Juggler cycle has length at most six.

## Open questions

Whether almost every odd-to-odd start has a finite descent certificate.
Length 7 was taken up by a later branch. Do not start an
O-terminating `CycleItinerary` programme.

## Decision

**PROMOTE**. Finite evaluation below \(256\) plus the last-even cell
against `LowerPowerBound` excludes both leftover `CycleItinerary`s, and the
later census consolidation promotes the result to: no cycle itinerary of
length at most six. This is not the closed uniform-from-\(3\)
extra-scale attack and not a halt theorem. Length seven was later
closed by the length-7 leftover branch.

Best next question: do almost all odd-to-odd starts have a finite
descent certificate?

## Publication assessment

Status: `THEOREM`.

Named exclusion of two leftover orientations; recorded in the math
note as Lemma 3.5 and consolidated into the small-cycle census
(Theorem 3.6). Not a Juggler totality result.
