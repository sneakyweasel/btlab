# Juggler hug-flow depth-2 conditional mixing

Status: **ARCHIVED** (Phase 0 decided)

Follow-up to the depth-\(1\) window lemma. It is **not** a
\(C_L\ne\emptyset\) theorem, not an application of
`J-hug-flow-window-depth-one` to \(y=\lfloor x^{3/2}\rfloor\), not
a \(K_3\) attack, not a reopen of mechanical lift, and not a halt
theorem.

## Problem

Does a depth-\(1\) admissible block keep enough interval structure,
after conditioning on the first parity, for a second-stage
Erdős–Turán estimate? Concretely: is every sufficiently large
depth-\(1\) window's cylinder \(\mathcal A_1\) a union of
consecutive-\(y\) blocks above the second-stage working window?

## Exact statement

Let \(W(X)=\bigl\lfloor\tfrac23 X^{1/3}\bigr\rfloor\) and let \(I\)
be a window of \(W(X)\) consecutive odd integers in \([X,2X]\). Write
\[
V(I)=\bigl\{\lfloor x^{3/2}\rfloor:x\in I\bigr\}
\]
and \(\mathcal A_1(\varepsilon)=\{x\in I:\lfloor x^{3/2}\rfloor\equiv\varepsilon\pmod 2\}\).
The depth-\(1\) lemma already says both \(\varepsilon\) occur. Phase 0
asks whether \(V(I)\) (or the image of either \(\mathcal A_1\)
piece) contains a consecutive integer interval of length
\(\gg\tfrac23 Y^{1/3}\) at \(Y\asymp X^{3/2}\), so that interval
Erdős–Turán could mix
\(\lfloor y^{3/2}\rfloor\).

The trap, named before the census: the *span* of \(V(I)\) is
\(\asymp X^{5/6}\), which is a long interval at scale \(Y\). The
occupants are not that interval.

## Current literature

- Depth-\(1\) working-window both-parities —
  **EXACT — HUMAN PROOF** (`J-hug-flow-window-depth-one`).
- Long-interval nested parity to depth \(\le 4\) —
  **EXACT — HUMAN PROOF** (Paper B). Ambient, not a sparse-image
  transfer (Paper B Corollary 4.2 remark).
- Hug-cylinder construction freedom flow —
  **OBSERVATION** / **PARK**
  ([juggler_hug_cylinder_construction.md](juggler_hug_cylinder_construction.md)).
- Mechanical-lift empty `OOE` — **CLOSE** (single-cell inverses,
  not counting).
- Prefix realization to depth \(28\) —
  **COMPUTATIONALLY VERIFIED** / **CLOSE**. Finite \(C_2\ne\emptyset\)
  is already known and is not the target.

Project relationship: **independent** geometry of the first-stage
cylinder. The increment identity is KNOWN calculus; the
PROJECT-SPECIFIC content is that the gap is larger than the
second-stage working window, so interval ET does not iterate.

## Branch budget

```text
Mathematical target     does A_1 inside a W(X)-window keep interval
                        structure for a second-stage ET estimate?
Novelty hypothesis      the first-parity filter might leave long
                        consecutive y-blocks above the Y^{1/3} window
Falsifier               V(I) gaps >= the second-stage working window
                        Y^{1/3}=X^{1/2}, or A_1 pieces <= X^{1/4}
Existing machinery      J-hug-flow-window-depth-one; increment
                        (x+2)^{3/2}-x^{3/2}; flow census runs
Maximum Phase-0 scope   exact image-gap identity + W(X)-window
                        geometry census; no C_L, no sparse-AP ET
Promotion criterion     quantitative mixing inside every large A_1
                        block (J-hug-flow-window-depth-two)
Stop criterion          image fragments at/below the remainder scale,
                        or conditioning destroys interval ET
```

## Balanced-ternary formulation

Not BT-specific; the gap is ordinary floor-power increment
arithmetic.

## Why BT may be relevant

Only through the shared \(2\)–\(3\) scale. No representation claim.

## Candidate operations / invariants

- **Image gap** \(\lfloor(x+2)^{3/2}\rfloor-\lfloor x^{3/2}\rfloor\)
  versus \(3\lfloor\sqrt x\rfloor\) (**EXACT — HUMAN PROOF** below).
- **Second-stage window** \(\tfrac23 Y^{1/3}=\tfrac23 X^{1/2}\)
  (**KNOWN** depth-\(1\) window at the image scale).
- **\(\mathcal A_1\) run lengths** in \(x\)-space
  (**OBSERVATION**).

## Experiments

Runner: `python -m research.juggler_sequence.hug_flow_depth_two`
(probe `src/research/juggler_sequence/hug_flow_depth_two.py`).
Artifact: `data/research/juggler/hug_flow_depth_two/summary.json`.
Fast suite:
`tests/research/juggler_sequence/test_hug_flow_depth_two.py`.

Exact integer census of \(W(X)\)-windows at scales
\(2^{12}\)–\(2^{28}\) (generic, mid-block, near-square starts):
image gaps, gap versus \(3\lfloor\sqrt x\rfloor\), gap versus the
second-stage window, and \(\mathcal A_1\) run lengths. No
second-stage exponential sum.

## Conjectures

None new. `juggler_hug_flow_window` stays ACTIVE for a possible
sparse-set depth-\(2\) statement; the interval-iteration reading
is closed here.

## Counterexamples

- “\(V(I)\) is a consecutive interval of length \(\asymp X^{5/6}\)
  at scale \(X^{3/2}\).” False: consecutive odd \(x\) have
  image gap \(\ge 3\lfloor\sqrt x\rfloor\), larger than
  \(\tfrac23 Y^{1/3}\).
- “Apply `J-hug-flow-window-depth-one` to
  \(y=\lfloor x^{3/2}\rfloor\).” False target: those \(y\) are not
  a consecutive interval of odd integers.

## Formalization

`HugFlowImageGap.lean` (24 September 2026) proves the image gap for every
`x`, not only odd `x >= 3` (`sqrt_cube_add_two_ge`, `floorPower_add_two_ge`),
the separation of odd images (`no_odd_image_in_gap`), the window comparison
(`window_le_sqrt`, `window_lt_gap`) and the ratio
`3 floor(sqrt x) / ((2/3) sqrt x) -> 9/2` (`gap_window_ratio_tendsto`).
Kernel-checked with the standard axioms only; not imported by the paper
roots. `J-hug-flow-image-gap` is **EXACT — LEAN VERIFIED**. The remark that
an interval Erdős–Turán bound does not apply directly is methodological,
not a theorem. No `sorry`. Paper A and Paper B are unchanged.

## Results

- **Image gap (`J-hug-flow-image-gap`, EXACT — HUMAN PROOF).**
  For every odd integer \(x\ge 3\),
  \[
  \lfloor(x+2)^{3/2}\rfloor-\lfloor x^{3/2}\rfloor
  \ge 3\lfloor\sqrt x\rfloor.
  \]
  *Proof.* Both sides of
  \((x+2)^{3/2}>x^{3/2}+3\sqrt x\) are positive, and the
  inequality is equivalent to
  \((x+2)^3>(x^{3/2}+3\sqrt x)^2\). Expanding,
  \[
  (x+2)^3=x^3+6x^2+12x+8,
  \qquad
  (x^{3/2}+3\sqrt x)^2=x^3+6x^2+9x,
  \]
  so the difference is \(3x+8>0\). Therefore
  \(\lfloor(x+2)^{3/2}\rfloor
  \ge\lfloor x^{3/2}+3\sqrt x\rfloor
  \ge\lfloor x^{3/2}\rfloor+\lfloor 3\sqrt x\rfloor\).
  Since \(3\sqrt x\ge 3\lfloor\sqrt x\rfloor\), the last floor is
  at least \(3\lfloor\sqrt x\rfloor\). \(\square\)

  At image scale \(Y=\lfloor x^{3/2}\rfloor\le x^{3/2}\) one has
  \(Y^{1/3}\le\sqrt x<\lfloor\sqrt x\rfloor+1\), so the depth-\(1\)
  working window at that scale satisfies
  \(\tfrac23 Y^{1/3}<\tfrac23(\lfloor\sqrt x\rfloor+1)\). For
  \(s=\lfloor\sqrt x\rfloor\ge 1\),
  \(3s>\tfrac23(s+1)\). Hence every consecutive odd pair has
  image gap strictly larger than the entire second-stage working
  window. The ratio tends to \(9/2\).

- **Census (COMPUTATIONALLY VERIFIED, classification
  `IMAGE_FRAGMENTED`):** every measured \(W(X)\)-window at
  \(2^{12}\)–\(2^{28}\) has `gap_ge_3sqrt` and
  `min_gap_gt_y_window`. Ratios sit at \(4.50\) (predicted
  \(9/2\)). At \(2^{28}\), a generic window of \(430\) odd \(x\)
  has min image gap \(49152\) against second-stage window
  \(10922\); \(\mathcal A_1\) even-runs have min/median/max
  \(12/18/105\) and odd-runs \(13/17.5/43\), all at or below
  the depth-\(1\) remainder \(\tfrac23 X^{1/4}\approx 85\) except
  one even-run of \(105\). Conditioning thins \(x\)-runs; it
  does not close \(y\)-gaps.

- **Interval ET does not iterate.** The first-parity filter
  preserves a \(3\sqrt X\)-separated packing, not an interval.
  The construction dossier's “image span \(\asymp X^{5/6}\), then
  Paper B on that interval” is the named trap. Sparse-AP
  discrepancy of \(\lfloor y^{3/2}\rfloor\) on difference
  \(\asymp 3\sqrt X\) is a different problem and is not opened.

## Open questions

None from this branch. A sparse-set depth-\(2\) statement would
be a new Phase-0, not an interval-ET corollary. The existence
claim \(C_L\ne\emptyset\) is not a theorem.

## Decision

**CLOSE.** The falsifier fired: \(V(I)\) is
\(3\lfloor\sqrt x\rfloor\)-separated, and that gap exceeds the
second-stage working window \(\tfrac23 Y^{1/3}\) at every odd
\(x\ge 3\). Depth-\(1\) mixing therefore does not survive
conditioning as an interval problem. The promotion target
`J-hug-flow-window-depth-two` (quantitative conditional mixing
inside every large \(\mathcal A_1\) block) is not met. The
obstruction lemma is recorded as `J-hug-flow-image-gap`. No
\(C_L\) induction, no sparse-AP campaign, no Paper edit.

Best next question: none from this branch — the construction
branch stays PARK; its remaining depth-\(2\) hope is not
interval ET.

## Publication assessment

Status: **ARCHIVED**. Negative knowledge: the depth-\(1\) window
lemma does not iterate by treating the image span as an interval.
A paragraph of context for the parked construction dossier, not
a paper candidate.
