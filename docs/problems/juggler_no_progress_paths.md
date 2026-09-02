# Juggler no-progress path structure

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

What necessary structure must a long `NO_CERTIFICATE` prefix of a
hypothetical minimal non-1 start satisfy?

## Exact statement

Phase A is already `minimal_avoids_progress`: a minimal \(n\) with
\(\neg\mathrm{ReachesOne}\,n\) has neither `Descent` nor `Capture`.
Do not add a coinductive path type.

Prove the stronger necessary constraint \(C\):

- \(\mathrm{ReachesOne}\) is closed backward along realized images, so
  a non-1 \(n\) cannot visit any certified `ReachesOne` state, not only
  \([1,n)\);
- \(2,4,6,8\) are `ReachesOne`, so an image in that set is already
  fatal (this does not enlarge the capture basin \(S=\{1\}\));
- a nonempty even prefix at \(n\ge 2\) is `Descent`;
- a minimal non-1 \(n\ge 3\) is odd.

Scan realized prefixes for collapse-without-capture
\(x\xrightarrow{E^r}y\) with \(y>1\), and for an integer-deficit reset
to \(0\) after a first positive defect. Do not prove that every integer
terminates.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Descent/capture calculus and `minimal_avoids_progress` —
  **EXACT — LEAN VERIFIED**.
- `even_itinerary_contracts`, `reachesOne_of_iterate`, `floorPower_two` —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The obstruction is stronger than
“no descent and no capture”. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     What necessary structure C must a long NO_CERTIFICATE prefix of a minimal non-1 n satisfy?
Novelty hypothesis      Collapse-without-capture to m>1 is either already ReachesOne (e.g. 2) or forces a later descent; defect cannot reset
Falsifier               A large even collapse to m>1 whose whole prefix from n is neither Descent nor Capture nor ReachesOne-implied
Existing machinery      minimal_avoids_progress, Capture/Descent/ReachesOne, even_itinerary_contracts, reachesOne_of_iterate, floorPower_two
Maximum Phase-0 scope   ReachesOne closure of small even residuals; collapse-without-capture scan; defect-reset scan; one necessary C in Lean
Promotion criterion     A proved necessary C beyond “no descent and no capture”, or a minimized COLLAPSE_WITHOUT_CAPTURE / DEFECT_RESET witness
Stop criterion          Coinductive orbits; PowerHeight; residual automaton; enlarged capture basin; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Backward closure `reachesOne_of_image` —
  **EXACT — LEAN VERIFIED**
- Cheap certificates `two_reachesOne` / `four_reachesOne` /
  `six_reachesOne` / `eight_reachesOne` —
  **EXACT — LEAN VERIFIED**
- `minimal_avoids_reachesOne_image` —
  **EXACT — LEAN VERIFIED**
- `even_word_descent` / `minimal_odd_start` —
  **EXACT — LEAN VERIFIED**
- `OOOE` at \(3\) and `OOE` at \(5\) land at \(6\ge n\), so they are
  not descent and not capture, but they are `ReachesOne`-implied —
  **COMPUTATIONALLY VERIFIED**
- `OOE` at \(9\) lands at \(11\) (uncertified \(y\ge n\)); later
  `OOEOE` descends to \(6\) — **COMPUTATIONALLY VERIFIED**
- Integer deficit does not return to \(0\) after a first positive
  defect on \(n\le 80\) — **OBSERVATION**
- Collapse basin larger than \(\{1\}\) — not needed
- Global halt — not claimed
- `PowerHeight` / `no_progress_prefix` datatype — not added

## Experiments

- Probe: `research.juggler_sequence.no_progress_paths`
- Records: [juggler_no_progress_paths.md](../research/juggler_no_progress_paths.md),
  [juggler_no_progress_paths.json](../research/juggler_no_progress_paths.json)
- Tests: `tests/research/juggler_sequence/test_no_progress_paths.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to \(C\). Collapse-without-capture to an uncertified \(y\ge n\)
exists (`OOE` at \(9\) lands at \(11\); `OOOOE` at \(37\) lands at
\(9317\); a later even run on the same start sends
\(24906114455136\) to \(2233\)). Those prefixes are not descent and
not capture, which is exactly why \(C\) is stronger than Phase A:
they are forbidden only once the image itself is a certified
`ReachesOne` state. A delayed later descent on the same orbit is an
observation, not a halt theorem. No defect-reset witness on the scan.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `two_reachesOne` / `four_reachesOne` / `six_reachesOne` /
  `eight_reachesOne`
- `reachesOne_of_image` / `image_two_reachesOne` (and \(4,6,8\))
- `minimal_avoids_reachesOne_image`
- `even_word_descent` / `minimal_odd_start`

Unchanged: `minimal_avoids_progress`,
`power_bound_compensated_contracts`, `first_even_freeze`,
`eventually_no_first_even_contraction`,
`changing_suffix_unbounded_contraction`. Basin remains \(\{1\}\).
No `sorry`. No halt theorem. No `PowerHeight`. No new path type.

## Results

Classification **NO_PROGRESS_STRUCTURE_GREEN**.

Necessary \(C\): a hypothetical non-1 orbit avoids every `ReachesOne`
state; even residuals \(2,4,6,8\) are forbidden even when the image is
at least \(n\); a nonempty even prefix at \(n\ge 2\) is descent; a
minimal non-1 \(n\ge 3\) starts odd.

On annotated odd starts \(3,7,13,41\), the realized itinerary is an odd
expansion staying \(\ge n\), then an even residual that is either
\(<n\) or cheap `ReachesOne`. This is finite-prefix annotation, not
empirical totality.

## Open questions

Answered in [juggler_residual_progress.md](juggler_residual_progress.md):
every residual in \(\{1,\ldots,11\}\) is `ReachesOne`, so \(9\to 11\)
is already fatal, and even residuals below \(144\) follow. The
remaining question lives there.

## Decision

**PROMOTE** the extra constraint \(C\). It is not a restatement of
`minimal_avoids_progress`: `OOE` at \(5\) lands at \(6\), which is
neither descent nor capture, and is still fatal by `ReachesOne`. Keep
\(S=\{1\}\). Do not claim that every uncertified collapse is followed
by a bounded descent. Do not claim termination.

Best next question: after an uncertified collapse to \(y\ge n\), must
a later residual become descent, capture, or cheap-`ReachesOne`
implied, with any bound depending only on \(y\)?

## Publication assessment

Status: `EXPLORATORY`. A local obstruction refinement, not a paper
candidate and not a Juggler totality result.
