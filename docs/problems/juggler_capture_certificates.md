# Juggler descent and capture certificates

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can finite Juggler blocks be certified as either a strict descent or a
capture into a finite already-controlled basin?

## Exact statement

With certified basin \(S=\{1\}\), a realized itinerary \(w\) at \(n\) is

- a **capture** if \(T_w(n)=1\);
- a **descent** if \(T_w(n)<n\).

Prove that capture composes, that the known changing-family collapses
are captures, and that a hypothetical minimal \(n\) that never reaches
\(1\) admits neither certificate. Do not prove that every start has
such a block.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Changing-family collapses onto \(1\) —
  **EXACT — LEAN VERIFIED**.
- Compensated contraction certificate —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The collapse loophole is rewritten
as a capture certificate. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Capture into {1} plus descent, with composition
Novelty hypothesis      Changing-family collapses are basin captures
Falsifier               Large changing-family T not in {1} and no descent
Existing machinery      image_append, even_tower_to_one, nested 2500
Maximum Phase-0 scope   Capture/Descent; append; normalize families;
                        minimal-avoidance lemma
Promotion criterion     Known collapses are capture; composition proved
Stop criterion          Halt theorem; generic tactic; enlarge S without need
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `Capture` / `Descent` / `ReachesOne` — **EXACT — LEAN VERIFIED**
- Capture composition `capture_of_suffix` / `capture_append` —
  **EXACT — LEAN VERIFIED**
- \(E^kO^{3k}\) and `OEEE` / `q=2500` as capture —
  **EXACT — LEAN VERIFIED**
- First-even cell capture when \(T_v(q)=1\) —
  **EXACT — LEAN VERIFIED**
- Minimal \(n\) avoiding `ReachesOne` admits neither certificate —
  **EXACT — LEAN VERIFIED**
- `EOO` at \(12,14\) is descent to \(11\), not capture —
  **COMPUTATIONALLY VERIFIED** / already classified
- Basin larger than \(\{1\}\) — not needed
- Global halt — not claimed
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.capture_certificates`
- Records: [juggler_capture_certificates.md](../research/juggler_capture_certificates.md),
  [juggler_capture_certificates.json](../research/juggler_capture_certificates.json)
- Tests: `tests/research/juggler_sequence/test_capture_certificates.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the capture normalization of the large changing families.
Short `EOO` at \(n=12,14\) is descent, which the framework already
allows.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `InertBasin` / `Capture` / `Descent` / `ReachesOne`
- `capture_of_suffix` / `capture_append`
- `even_tower_capture` / `even_tower_odd_tail_capture`
- `odd_even_tower_seven_capture` / `nested_even_collapse_2500_capture`
- `first_even_cell_capture`
- `descent_of_below` / `minimal_avoids_progress`

Unchanged: `LowerPowerBound`, `power_bound_compensated_contracts`,
`eventually_no_first_even_contraction`. No `sorry`. No halt theorem.
No `PowerHeight`.

## Results

Classification **DESCENT_CAPTURE_FRAMEWORK_GREEN**, with
**CAPTURE_BASIN_ONE_GREEN**.

The known large collapse families are capture into \(\{1\}\). Capture
composes through an arbitrary prefix. On a first-even cell, \(T_v(q)=1\)
is cell capture. Small is not inert: \(3\to5\to11\to36\).

A hypothetical minimal \(n\) that never reaches \(1\) cannot carry a
descent block or a capture block. That is the global obstruction
vocabulary, not a totality proof.

## Open questions

Answered in [juggler_no_progress_paths.md](juggler_no_progress_paths.md):
a hypothetical minimal non-1 orbit avoids every `ReachesOne` state;
even prefixes at \(n\ge 2\) are descent; landing at \(2,4,6,8\) is
already fatal. The remaining question lives there.

## Decision

**PROMOTE** the descent/capture calculus and the capture normalization
of the changing-family collapses. Keep \(S=\{1\}\). Do not claim that
every trajectory contains such a block. Do not claim termination.

Best next question: what structural constraints would an infinite
`NO_CERTIFICATE` path have to satisfy?

## Publication assessment

Status: `EXPLORATORY`. A local certificate calculus, not a paper
candidate and not a Juggler totality result.
