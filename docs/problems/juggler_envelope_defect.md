# Juggler finite-itinerary envelope defect and strictness

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

For a realized non-monochrome finite itinerary, how far below the one-sided
floor-power envelope must the image lie, and can that gap be traced to
the first non-exact branch?

## Exact statement

Write

\[
\Delta_w(n)=n^{3^{\#O(w)}}-T_w(n)^{2^{|w|}}.
\]

If \(w\) is realized and not an extremal equality tower, is
\(\Delta_w(n)\ge 1\)? Does a positive local defect

\[
\delta_E(x)=x-T(x)^2,\qquad
\delta_O(x)=x^3-T(x)^2
\]

persist through an arbitrary suffix, and is there a useful lower bound
in \(\delta\), the defect state, and the suffix length?

This is a local arithmetic question. It is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Phase-15 (`juggler_equality_rigidity`): mixed-word *local* strictness
  **REFUTED** at word `O`, \(n=9\). That forbids
  `mixed_word_power_lt` / a universal `T(n)^2<n^3`. **extended** here
  by a *composite* strict envelope, which is the complement of the
  extremal equality theorem.
- Phase-18 (`juggler_equality_language`): equality language
  **EXACT — LEAN VERIFIED**.

## Branch budget

```text
Mathematical target     Can the first non-exact branch produce a
                        compositional lower bound on Δ_w(n)?
Novelty hypothesis      A local defect δ>0 persists through suffix
                        power maps and yields a reusable strict bound.
Falsifier               DEFECT_NO_SIMPLE_BOUND
Existing machinery      PowerBound, PowerBoundEq, extremal iff,
                        local even/odd square inequalities, local tightness
Maximum Phase-0 scope   Local defects; StrictPowerBound + append;
                        non-monochrome ⇒ strict; first-defect probe
                        without huge powers. No PowerHeight, no engine edits.
Promotion criterion     Lean proves compositional strictness, or a
                        quantitative propagation law, or a minimized
                        obstruction to simple first-defect bounds
Stop criterion          PowerHeight; equality census; termination claim;
                        generic tactic; engine control edits
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Local defects \(\delta_E,\delta_O\) —
  **EXACT — LEAN VERIFIED**
- `StrictPowerBound` append / suffix persistence —
  **EXACT — LEAN VERIFIED**
- Non-monochrome realized itinerary \(\Rightarrow\Delta\ge 1\) —
  **EXACT — LEAN VERIFIED**
- First local defect \(\Rightarrow\Delta\ge\delta_j\) through any suffix —
  **EXACT — LEAN VERIFIED**
- Universal local mixed strictness / `mixed_word_power_lt` — remains
  **REFUTED**
- Suffix-amplified \(F(\delta_j,x_j,|v|)\) growing in \(|v|\) — not
  proved; monotonicity in \(\Delta\) is the quantitative law
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.envelope_defect`
- First-defect scan via local tightness; global \(\Delta\) only on a
  tiny bit budget
- Records: [juggler_envelope_defect.md](../research/juggler_envelope_defect.md),
  [juggler_envelope_defect.json](../research/juggler_envelope_defect.json)
- Tests: `tests/research/juggler_sequence/test_envelope_defect.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- Mixed-word local strictness remains refuted at word `O`, \(n=9\).
- Candidate \(\Delta_w(n)\ge\delta_j\) was not falsified on the searched
  domain and is now a theorem.
- Same-count word permutations do not obey a first-defect-position
  order. The bound uses \(\delta_j\), not letter counts.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `localDefectEven` / `localDefectOdd`
- `StrictPowerBound`
- `strict_power_bound_append_even` / `_odd` / `strict_power_bound_from`
- `power_bound_word_strict` / `power_bound_defect_ge_one`
- `powerDeficit`
- `power_deficit_append_even` / `_odd` / `power_deficit_from`
- `local_defect_even_le_suffix_deficit` /
  `local_defect_odd_le_suffix_deficit`

No `PowerHeight`. No `sorry`. No `mixed_word_power_lt`. No
`PowerBoundStrict`. No ledger row. Existing weak `PowerBound` theorems
are unchanged.

## Results

Classification **DEFECT_QUANTITATIVE_GREEN**.

A realized itinerary that leaves an extremal tower at the first non-exact
branch \(j\) satisfies

\[
\Delta_w(n)\ge\delta_j>0.
\]

The mechanism is compositional: the empty prefix is an equality; the
first inexact even or odd branch produces a gap at least \(\delta_j\);
every later branch is monotone in `powerDeficit`, so the suffix cannot
restore equality or shrink the certified lower bound below \(\delta_j\).
Non-monochrome words are the special case already excluded from the
extremal families, and give \(\Delta_w(n)\ge 1\).

This is not a suffix-length amplification law and not a contraction
margin. It is not a termination theorem.

## Open questions

Is there an exact recursive \(\mathcal{D}(x,\mathrm{branch},v)\) that
improves on \(\delta_j\) by using the suffix letters, or is
\(\Delta\ge\delta_j\) the sharp uniform compositional statement?

## Decision

**PROMOTE** the local-defect calculus, `StrictPowerBound` composition,
and the first-defect lower bound \(\Delta\ge\delta_j\). Record
`DEFECT_QUANTITATIVE_GREEN`. Do not register an attack. Do not claim
termination. Do not add a suffix-length closed form or a contraction
margin in this phase.

Best next question: is there an exact recursive suffix defect
\(\mathcal{D}(x,\mathrm{branch},v)\) strictly stronger than \(\delta_j\)?

## Publication assessment

Status: `EXPLORATORY`. A local defect lemma, not a paper candidate and
not a Juggler totality result.
