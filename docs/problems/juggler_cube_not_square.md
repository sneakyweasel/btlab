# Juggler cube-not-square cell

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a W_5
reopen, not a next-letter envelope on \(1517\), not Paper A, and
not a claim that every positive integer reaches 1.

The envelope spine left a generic hole:
\(\operatorname{AboveAnchor}(n,w)\) with
\(T_w(n)<n^{3}\) and not \(T_w(n)<n^{2}\). This phase names the
certificate.

## Problem

What certificate, if any, follows from an anchor-relative state
in the cube-not-square cell \([n^{2},n^{3})\)?

## Exact statement

Let \(n\ge 2\) and \(n^{2}\le x<n^{3}\). Then:

- if \(x\) is even, \(n\le T(x)<n^{2}\); if also \(T(x)\) is even,
  two even letters are `FiniteProgress`;
- if \(x\) is odd, \(n^{3}\le T(x)\).

On `MinimalNonTerm`, an even cube-cell landing has odd next
image. This is not a halt theorem.

## Current literature

- `envelope_lt_pow` / `power_bound_lt_pow` —
  **EXACT — LEAN VERIFIED** (`J-envelope-lt-pow`)
- `even_below_anchor_pow` / `even_below_fourth` —
  **EXACT — LEAN VERIFIED** (`J-above-anchor`)
- `OOEOOEOOEOEOO` has cube and not square —
  **EXACT — LEAN VERIFIED** (`J-ce-second-o-cube`)
- \(1517\) lands odd in \([n^{2},n^{3})\) —
  **COMPUTATIONALLY VERIFIED**; “still below \(n^{2}\)” —
  **REFUTED** (`J-second-o-below-square`)
- `odd_ge_succ_sq_floorPower_ge_cube` uses floor \((n+1)^{2}\),
  not \(n^{2}\)
- even landing is immediately descent —
  **REFUTED** (already; cube even is not `FiniteProgress`)
- Every start reaches 1 — not claimed

Project relationship: **extended**. The designated next question
of the envelope-spine consolidation.

## Branch budget

```text
Mathematical target     Does AboveAnchor + n^2 ≤ image < n^3
                        force a certificate?
Novelty hypothesis      even resets to [n, n^2); odd lifts to
                        ≥ n^3; EE after even cube is
                        FiniteProgress
Falsifier               even cube-not-square stays ≥ n^2;
                        odd x ≥ n^2 has T(x) < n^3
Existing machinery      even_below_fourth;
                        even_below_square_iff;
                        odd_ge_succ_sq_floorPower_ge_cube;
                        envelope_lt_pow; 1517 odd landing
Maximum Phase-0 scope   generic Lean dichotomy + EE→FP +
                        1517 lift check; no next-letter
                        envelope; no W_5
Promotion criterion     named Lean dichotomy with a CE
                        consumer
Stop criterion          restates even_below_fourth only;
                        letter chain; W_5 reopen
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- even \(x<n^{3}\) gives \(T(x)<n^{2}\) —
  **EXACT — LEAN VERIFIED**
- even \(n^{2}\le x<n^{3}\) gives \(n\le T(x)<n^{2}\) —
  **EXACT — LEAN VERIFIED**
- odd \(n^{2}\le x\) gives \(T(x)\ge n^{3}\) —
  **EXACT — LEAN VERIFIED**
- cube-cell even then even is `FiniteProgress` —
  **EXACT — LEAN VERIFIED**
- cube-cell even is already `FiniteProgress` —
  false
- next letter after \(1517\to 43916043\) — not asked

## Experiments

- Probe: `research.juggler_sequence.cube_not_square`
- Records: [juggler_cube_not_square.md](../research/juggler_cube_not_square.md),
  [juggler_cube_not_square.json](../research/juggler_cube_not_square.json)
- Tests: `tests/research/juggler_sequence/test_cube_not_square.py`
- Lean: `formal/Problems/Juggler/MinimumRelative.lean`, laboratory
  barrel only. Not imported by `Problems.JugglerPaper`. No `sorry`.

## Conjectures

None opened.

## Counterexamples

“Cube-cell even landing is `FiniteProgress`” is false: \(n=3\),
\(x=16\) lies in \([9,27)\), \(T(16)=4\ge 3\). The second even
then drops: \(T(4)=2<3\).

\(1517\) takes the odd branch: \(43916043\) is odd in
\([1517^{2},1517^{3})\) and \(T(43916043)\ge 1517^{3}\).

## Formalization

`Corridor.lean` already has `even_below_cube_preimage`.
`CubeCorridor.lean` adds `even_cube_not_square` and
`odd_ge_sq_floor_ge_cube`. `Progress.lean` adds
`finiteProgress_of_cube_even_even`. `Minimal.lean` adds
`minimal_cube_even_forces_odd_image`. Paper A is unchanged. No
`sorry`. No halt theorem.

## Results

Classification **CUBE_NOT_SQUARE_GREEN**.

The cube-not-square cell is a parity-split certificate, not a
drop by itself. Even landings reset into the square cell; a
second even is `FiniteProgress`. Odd landings lift to at least
\(n^{3}\). The leftover corridor \(1517\) occupies the odd
branch.

This is not a halt theorem and not a next-letter envelope.

## Open questions

The leftover is still an odd lift from \([n^{2},n^{3})\) with no
drop. Do not resume the letter-by-letter square chain. Do not
reopen W_5.

## Decision

**PROMOTE** the parity-split certificate and the EE
`FiniteProgress` bridge. CycleMin and MinimalNonTerm consume the
same geometry. Do not claim termination.

Best next question: after an odd lift \(T(x)\ge n^{3}\) from a
cube-not-square odd landing, is there a shared cell other than
another one-step envelope?

## Publication assessment

Status: `EXPLORATORY`.

A small exact dichotomy that makes the envelope leftover a
named certificate. Not a paper candidate and not a Juggler
totality result.
