# Shortcut Collatz finite descent residual

Status: **ARCHIVED**

This module does **not** claim a proof or disproof of the Collatz conjecture.

The map under study is the **shortcut** map, not hailstone `3n+1` and not
the parked odd-only `T` of [collatz.md](collatz.md):

```text
C(n) = n/2           if n is even
C(n) = (3n+1)/2      if n is odd
```

Code name: `shortcut_step`. Terminal convention: the exact cycle `{1,2}`.

## Problem

Can a finite residual together with bounded affine blocks certify strict
descent for every sufficiently large positive integer, or is there an
exact obstruction in a natural finite-state class?

## Exact statement

Does there exist a finite set `S`, a residual `R : N → S`, a bound `L`,
and a policy `P : S → {E,O}^{≤L}` such that for every `n > N0`

```text
C^{|P(R(n))|}(n) < n
```

with `P(R(n))` legal for every integer in the class `R^{-1}(s)`? If not,
is there an exact obstruction for residuals of the form `n mod 2^L` with
block length at most `L`?

Claim ladder: A = some descent trajectory exists (weak). B = bounded
block determined by a finite residual. C = that plus induction would
terminate every positive integer. This phase reached **neither B nor C**.

## Current literature

The witness `n = 2^L - 1` has `L` initial odd shortcut steps and
`C^L(n) = 3^L - 1 > n`. Unbounded stopping time is `KNOWN` (elementary;
Terras-type density of contracting `k`-blocks is not the target). Tao's
logarithmic-density theorem is context, not a computational target.
The parked application [collatz.md](collatz.md) studies odd-only `T`,
not this map.

## Branch budget

- **Target:** finite residual + bounded blocks, or an exact obstruction
  in a stated finite-state class.
- **Novelty hypothesis:** the engine might find a hidden finite local
  structure of BT-residual type, or a precise obstruction that is not a
  census.
- **Falsifier:** short-block search plus 2-adic residuals produce only
  stopping-time statistics, or only the elementary `2^L-1` word.
- **Existing machinery:** `ProblemSpec`, `AttackPlanner`, EXACT vs
  BOUNDED closure, reverse closure, `LinearFunctional`, experiment YAML,
  Lean `Problems/Collatz`.
- **Maximum Phase-0 scope:** shortcut adapter; blocks of length `≤ 12`;
  residuals `n mod 2^k` and their behavioral quotient; reverse from
  `{1,2}` with a depth cap; one perturbation `C_{5,1}`; Lean of the
  strongest local theorem.
- **Promotion criterion:** a genuine descent certificate, a residual not
  equivalent to 2-adic legality, or a non-elementary obstruction.
- **Stop criterion:** the only exact statement is `KNOWN` unbounded
  stopping time. Then `CLOSE`.

## Balanced-ternary formulation

None. The stress test is a two-control piecewise-affine integer map.
BT coordinates of the parked `T`-application are not used.

## Why BT may be relevant

It is not required. The laboratory question is whether the
constrained-dynamics engine, which found finite residuals in BT
normalization, finds the same kind of structure here.

## Candidate operations / invariants

- Shortcut `C` with state-determined parity. **EXACT — LEAN VERIFIED**
  (`shortcutC`, `{1,2}` cycle).
- Block `C^k(n) = (a_w n + b_w)/2^k` on the unique residue of `w`.
  **EXACT — HUMAN PROOF** in the adapter; one-letter odd block
  **EXACT — LEAN VERIFIED**.
- `V(n)=n` decreases on every step. **REFUTED** (`n=1`, every odd `n`).
- Uniform `L`-block policy from `n mod 2^L`. **REFUTED** / obstruction
  **EXACT — LEAN VERIFIED**: `C^L(2^L-1) > 2^L-1`.
- Integer `n` as a finite residual. Integer-state BFS from 27 hits the
  cap (`INCONCLUSIVE`). Forward closure from 1 is the terminal cycle
  `{1,2}` (`EXACT`, not a descent residual of `N`).

## Experiments

- `btlab research analyze|attack|reproduce|report collatz`
  (alias `collatz_finite_descent`). `--remaining` is the short-block
  bound `L`, default 4 in the CLI, 12 in the mathematical bound.
- Adapter tests: `tests/research/collatz_finite_descent/test_finite_descent.py`
- Records: `data/research/collatz/finite_descent/`
- Perturbation: `C_{5,1}` via `plan_perturbation_5_1`. The `O^L` word of
  `2^L-1` is `(3,1)`-specific for `L≥2`; uniform `L`-descent on
  `n mod 2^L` still fails because odd residues expand on the first step.

## Conjectures

None opened.

## Counterexamples

- One-step Lyapunov `V(n)=n`: `n=1` (`C(1)=2`).
- Uniform finite 2-adic descent: `n=2^L-1` for every `L≥1`.
- Behavioral residual of length-`≤4` tests is a proper quotient of
  `Z/2^4` (colliding residues exist); it is still a function of
  `n mod 2^L`, not a new invariant.

## Formalization

`formal/Problems/Collatz/Shortcut.lean`. No `sorry`. Does not embed the
Python search. Does not retag `C-T-*` rows of the parked `T` module.

## Results

- Controls are state-determined. `AffineSystem` is inapplicable
  (different rational slopes). Modular/spectral stay skipped.
- Integer-state closure from 27: bounded search hit the cap.
  Reverse from `{1,2}` with depth cap 6: `BOUNDED`, not global coverage.
- Escape set `E_L` contains the class `-1 mod 2^L` for the `(3,1)` map.
  `|E_L|/2^L` is the fraction of length-`L` words with `3^{odd count} > 2^L`.
  That density is not a descent theorem.
- Claim level actually reached: not A-as-success, not B, not C.

## Open questions

None opened by this phase. Do not auto-start a second Collatz phase.

## Decision

`CLOSE`. The engine reused the generic attack stack and produced an
exact obstruction: no residual of the form `n mod 2^L` with blocks of
length at most `L` certifies strict descent, because `n=2^L-1` realises
the all-odd word and expands. That statement is `KNOWN` elementary
unbounded stopping time, not a new Collatz theorem. A branch whose
surviving statements are `KNOWN` is a `CLOSE`. The `C_{5,1}` comparison
shows the obstruction is not an artefact of hiding the `(3,1)` constants
in the residual, even though the specific all-odd word of `2^L-1` is
`(3,1)`-specific for `L≥2`.

Best next question: none from this branch. The parked odd-only `T`
application remains PARK; do not reopen it from this CLOSE.

## Publication assessment

Status: `ARCHIVED`. Not a `PAPER_CANDIDATE`. The Lean obstruction is
exact and independently checkable; its novelty is `KNOWN`.
