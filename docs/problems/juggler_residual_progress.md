# Juggler residual progress

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

After an uncertified collapse \(n\to y\) with \(y\ge n\), what must the
residual state \(y\) do if the original trajectory is a hypothetical
minimal non-terminating path?

## Exact statement

Do not attempt a theorem for every residual. Identify a useful class
\(R\) such that

\[
y\in R
\Longrightarrow
\text{a bounded realized prefix from }y
\text{ is Descent or }ReachesOne.
\]

Keep local descent below \(y\) separate from global descent below the
original \(n\). Keep `Capture` as image \(1\). Do not add an
infinite-path type. Do not prove totality.

The smallest useful \(R\) is the initial segment that swallows the
minimized uncertified residual \(11\).

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- `ReachesOne` backward closure and cheap certificates \(2,4,6,8\) —
  **EXACT — LEAN VERIFIED**.
- Uncertified collapse \(9\xrightarrow{\texttt{OOE}}11\) —
  **COMPUTATIONALLY VERIFIED** in the previous phase.

Project relationship: **extended**. The cheap `ReachesOne` set grows
from \(\{1,2,4,6,8\}\) to a proved initial segment. Totality remains
unclaimed.

## Branch budget

```text
Mathematical target     Useful R with ProgressWithin; residuals from known collapses
Novelty hypothesis      All 1≤y<12 are ReachesOne; even y<144 follow; known residuals descend from y
Falsifier               Some y<12 is not ReachesOne, or a calibration residual escapes
Existing machinery      ReachesOne, reachesOne_of_image, floorPower_pos, no_progress_paths
Maximum Phase-0 scope   ProgressWithin census; small-M scan; renewal search; Lean interval <12 and even <144
Promotion criterion     Proved R beyond {2,4,6,8}, or a minimized escape
Stop criterion          Halt; PowerHeight; infinite streams; FloorPower rewrite; cycle/dichotomy programme
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `ProgressWithin(y,L)` / `DescendsWithin` / `ReachesOneWithin` —
  **COMPUTATIONALLY VERIFIED** (Python predicates)
- \(1\le y<12\implies ReachesOne(y)\) —
  **EXACT — LEAN VERIFIED**
- even \(1\le y<144\implies ReachesOne(y)\) —
  **EXACT — LEAN VERIFIED**
- image in \(\{1,\ldots,11\}\) is fatal —
  **EXACT — LEAN VERIFIED**
- a positive non-`ReachesOne` value is at least \(12\) —
  **EXACT — LEAN VERIFIED**
- `11` and `9317` locally descend from \(y\); `T^2(11)=6<9` —
  **COMPUTATIONALLY VERIFIED**
- no renewal counterexample \(T^r(y)\ge n\) on \(n\le 80\) —
  **OBSERVATION**
- no uniform \(L\) for all of \(\mathbb{N}\) (`193` first hits \(R\) at step \(70\)) —
  **OBSERVATION**
- `Capture` enlarged beyond \(\{1\}\) — not done
- global halt — not claimed
- `PowerHeight` / `ResidualState` / `MinimalNonTerm` — not added

## Experiments

- Probe: `research.juggler_sequence.residual_progress`
- Records: [juggler_residual_progress.md](../research/juggler_residual_progress.md),
  [juggler_residual_progress.json](../research/juggler_residual_progress.json)
- Tests: `tests/research/juggler_sequence/test_residual_progress.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the class \(R=\{1,\ldots,11\}\). The claim that some uniform
\(L\) gives `ProgressWithin(y,L)` for every positive \(y\) is false:
\(193\) first hits \(R\) at step \(70\). That kills “\(R=\mathbb{N}\) with
a uniform bound”, not the initial-segment class.

No residual from the \(n\le 80\) uncertified-collapse list evaded
`ProgressWithin` on the scan horizon. No defect of
\(T^r(y)<n\) on that list; that is not a renewal theorem.

## Formalization

Source locations below follow the current Lean layout. Development notes
retain this branch's original scope; subsequent results and open directions
are tracked in the [Juggler guide](../../attacks/juggler/AGENT.md).

`formal/Problems/Juggler/Termination.lean` and
`formal/Problems/Juggler/Itinerary.lean`. Added wrappers only:

- `three_reachesOne` … `eleven_reachesOne`
- `image_pos`
- `reachesOne_of_lt_twelve` / `image_lt_twelve_reachesOne`
- `non_reachesOne_ge_twelve`
- `even_lt_sq_twelve_reachesOne`

No new module. No `sorry`. No halt theorem. No `PowerHeight`. Basin
remains \(\{1\}\). Unchanged:
`minimal_avoids_progress`, `two_reachesOne`,
`power_bound_compensated_contracts`, `first_even_freeze`,
`eventually_no_first_even_contraction`,
`changing_suffix_unbounded_contraction`.

## Results

Classification **RESIDUAL_PROGRESS_GREEN**.

The useful class is \(R=\{1,\ldots,11\}\): every such residual is
`ReachesOne`. Consequently any realized image in that interval is
fatal, and a positive hypothetical non-1 value is at least \(12\).
One even step extends this to every even residual strictly below
\(144=12^2\).

The minimized uncertified collapse \(9\to 11\) is therefore
`ReachesOne`-implied. Calibration residuals `11` and `9317` locally
descend from \(y\) itself. Capture is still image \(1\).

## Open questions

Answered in [juggler_even_scale_barrier.md](juggler_even_scale_barrier.md):
an even residual on a minimal non-1 orbit must lie at scale
\(\ge n_*^2\), and an \(E^r\) run must start at \(\ge n_*^{2^r}\). The
orbit is not forced to be all-odd. The remaining question lives there.

## Decision

**PROMOTE** the finite residual class \(R=\{1,\ldots,11\}\) and the
even-below-\(144\) corollary. This is not a restatement of cheap
\(\{2,4,6,8\}\): \(11\) was the minimized uncertified residual, and
it is now certified. Keep \(S=\{1\}\). Do not claim a uniform
progress bound for every \(y\). Do not claim termination.

Best next question: must a residual \(y\ge 144\) eventually land in
an even state below \(144\), with any bound depending only on \(y\)?

## Publication assessment

Status: `EXPLORATORY`. A finite residual-class certificate, not a
paper candidate and not a Juggler totality result.
