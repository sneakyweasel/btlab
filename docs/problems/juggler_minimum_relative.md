# Juggler minimum-relative consolidation

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a new isolated
obstruction theorem, not Paper A, and not a claim that every positive
integer reaches 1.

This phase extracts the common minimum-relative trajectory geometry
already used by `CycleMin` and `MinimalNonTerm`, then makes both
programs consume the same Lean primitives.

## Problem

CycleMin proofs and termination proofs have been restating the same
finite-prefix constraint under different names. What is the shared
predicate, and how much of the no-cycle program already produces
`FiniteProgress` on a minimal non-1 start?

## Exact statement

Define

\[
\operatorname{AboveAnchor}(n,w)
:\Leftrightarrow
\operatorname{follows}(n,w)
\;\wedge\;
\forall i\le |w|,\; T^{i}(n)\ge n.
\]

Then

\[
\operatorname{CycleMin}(n,w)\Rightarrow\operatorname{AboveAnchor}(n,w),
\]

and every finite prefix realized from a `MinimalNonTerm` start is
`AboveAnchor`. A realized drop `T_w(n)<n` is the existing
`FiniteProgress` certificate. An even image below \(n^{2}\) is that
certificate via the shared square trap. An isolated prefix
`O^a E (OE)^r` that stays at least \(n\) forces
\(2^{a+2r+1}\le 3^{a+r}\); in particular \(a=2\) forces \(r=0\).
If every nontrivial cycle word is impossible, then a start that never
reaches 1 must escape. This last implication is not a no-cycle
theorem.

## Current literature

- Isolated-`OE` survival \(r\le R(a_0)\) —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-first-oo-r-bound`).
- `OOEOOE` square cell without cycle return —
  **EXACT — LEAN VERIFIED** (`J-minimal-ooeooe-escape-trap`).
- Cycle-or-escape split —
  **EXACT — LEAN VERIFIED** (`J-trajectory-cycle-or-escape`).
- `MinimalNonTerm` orbits stay \(\ge n\) —
  **EXACT — LEAN VERIFIED**.
- Every start reaches 1 — not claimed.
- Every cycle is impossible — not claimed.

Project relationship: **extended**. The existing Type B lemmas are
re-homed; totality remains unclaimed.

## Branch budget

```text
Mathematical target     Can CycleMin and MinimalNonTerm share one
                        minimum-relative predicate and produce
                        FiniteProgress from the same prefix facts?
Novelty hypothesis      several CycleMin lemmas use only x_i ≥ n,
                        not T_w(n)=n, so they already constrain CEs
Falsifier               a candidate “shared” lemma still needs
                        closure; or AboveAnchor is only a rename
Existing machinery      CycleMin; MinimalNonTerm iterate_ge;
                        isolated_oe_ge_implies_exponent;
                        even_floorPower_lt_iff; FiniteProgress;
                        ReturnBelow; cycles_or_escapes
Maximum Phase-0 scope   MinimumRelative.lean + connectors + one
                        FP certificate + no-cycle ⇒ no bounded
                        nonterm; wrappers; dossier; no halt claim
Promotion criterion     Criteria A–E: shared predicate, several
                        Type-B lemmas, one FP bridge, clean
                        consumers, leftover class named
Stop criterion          abstraction without reuse; Paper A edits;
                        new isolated obstruction theorem
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `AboveAnchor` is implied by `CycleMin` and by every
  `MinimalNonTerm` prefix —
  **EXACT — LEAN VERIFIED**
- even \(x<n^{2}\) gives \(T(x)<n\), and \(x<n^{2k}\) gives
  \(T(x)<n^{k}\) —
  **EXACT — LEAN VERIFIED**
- \(x^{A}\le n^{B}\) and \(B<kA\) give \(x<n^{k}\); Escape
  square/cube cells are instances —
  **EXACT — LEAN VERIFIED** (`J-envelope-lt-pow`)
- isolated-`OE` survival is an anchor theorem, not a cycle theorem —
  **EXACT — LEAN VERIFIED**
- `OOE OE` and even `OOEOOE` landings are `FiniteProgress` —
  **EXACT — LEAN VERIFIED**
- no nontrivial cycle \(\Rightarrow\) no bounded nontermination —
  **EXACT — LEAN VERIFIED**
- no-cycle proves termination — not claimed
- `AboveAnchor` is cycle closure — false; it is a prefix lower bound

## Experiments

- Probe: `research.juggler_sequence.minimum_relative`
- Records: [juggler_minimum_relative.md](../research/juggler_minimum_relative.md),
  [juggler_minimum_relative.json](../research/juggler_minimum_relative.json)
- Tests: `tests/research/juggler_sequence/test_minimum_relative.py`
- Lean: `formal/Problems/Juggler/MinimumRelative.lean`, laboratory
  barrel only. Not imported by `Problems.JugglerPaper`. No `sorry`.

## Conjectures

None opened.

## Counterexamples

None to the shared-layer implications. The stronger claims that fail:

- “`follows` alone implies isolated-`OE` survival” — `9` follows
  `OOEOE` and drops; `AboveAnchor` is false.
- “the leftover classes coincide” — odd-landing escape corridors
  stay `AboveAnchor` on long prefixes without hitting a shared
  even-trap.
- “no-cycle proves halt” — unbounded escape remains.

## Formalization

`formal/Problems/Juggler/MinimumRelative.lean` imports `Corridor` +
`FirstInternalOO`, not `Scale` / `Minimal` / `CycleCore`. `CycleMin`
and `MinimalNonTerm` consume `AboveAnchor` downward (`CycleCore`,
`Minimal.lean`). Isolated-prefix envelopes live in
`FirstInternalOO`; cube geometry lives in `CubeCorridor`. Added:

- `AboveAnchor` / `aboveAnchor_of_minimalNonTerm` /
  `aboveAnchor_of_cycleMin` / `aboveAnchor_not_lt`
- `even_below_square_iff` / `even_below_anchor_pow` /
  `even_below_fourth` / `even_below_cube` /
  `finiteProgress_of_even_below_square`
- `isolatedOddSurvival_bound` / `aboveAnchor_isolated_two` /
  `finiteProgress_of_ooe_oe`
- `finiteProgress_of_aboveAnchor_returnBelow`
- `no_nontrivial_cycle_no_bounded_nonterm`

Word algebra in `Envelope.lean`: `EnvelopeState`, `envelope_lt_pow`,
`power_bound_lt_pow` (`EnvelopeState.of_follows.lt_pow`).
Escape square/cube cells are instances. `power_bound_contracts`
is the `k = 1` case of that theorem. Isolated CycleMin wrappers
stay in `CycleObstructions`. CE wrappers stay in `Minimal.lean`.
`FiniteProgress` is not redefined. Paper A is unchanged. No `sorry`.
No halt theorem. Spine: [juggler_lean_spine.md](../architecture/juggler_lean_spine.md).

## Results

Classification **MINIMUM_RELATIVE_GREEN**.

`CycleMin` and `MinimalNonTerm` are consumers of `AboveAnchor`.
The isolated-`OE` bound and the `OOEOOE` even-trap are prefix
theorems that emit `FiniteProgress` when the image drops. A future
no-cycle theorem would kill only bounded nontermination.

The leftover termination class is **odd-landing corridors** that
remain `AboveAnchor` on every finite prefix, never land even below
\(n^{2}\), may sit in a cube cell \(T_w(n)<n^{3}\) without a square
cell, never realize a scale-gap isolated prefix, and do not
eventually cycle. The word `OOEOOEOOEOEOO` is the named instance:
\(3^{9}<3\cdot 2^{13}\) and \(\neg(3^{9}<2\cdot 2^{13})\). A
cube-cell even landing is not `FiniteProgress`.

This is not a halt theorem and not a cycle-exclusion theorem.

## Open questions

The leftover class is the true termination target. First-kill
classification is closed in
[juggler_above_anchor_first_fail.md](juggler_above_anchor_first_fail.md).
The envelope spine still makes the hole one missing cell:

\[
\operatorname{AboveAnchor}(n,w)\land\operatorname{image}<n^{3}
\land\neg(\operatorname{image}<n^{2})
\;\Rightarrow\;
{?}
\]

Do not continue proving CycleMin-only lemmas that do not import as
shared obstructions. Do not claim that no-cycle proves halt. Do not
reopen bunched-short cells, escape-margin \(M\), or a length-11
census.

## Decision

**PROMOTE** the shared `AboveAnchor` layer, the `EnvelopeState` /
`envelope_lt_pow` spine, and the FiniteProgress bridge. CycleMin
remains about closure. MinimalNonTerm remains about refusing
descent. Do not claim termination.

Best next question: taken up and closed in
[juggler_above_anchor_first_fail.md](juggler_above_anchor_first_fail.md).
The residual hole is a cube cell without a square cell.

## Publication assessment

Status: `EXPLORATORY`.

An architectural consolidation of already-proved geometry. Not a
paper candidate and not a Juggler totality result.
