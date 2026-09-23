# Juggler first-defect bound sharpness

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Is the first-defect lower bound \(\Delta_w(n)\ge\delta_j\) sharp for a
nonempty suffix, or does every later branch strictly amplify the
deficit?

## Exact statement

Write \(w=ubv\) with \(u\) locally exact, \(b\) the first inexact
branch, and local defect \(\delta_j>0\). When is

\[
\Delta_w(n)=\delta_j,
\]

and in particular can this happen for \(|v|>0\)?

This is a local arithmetic question. It is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Phase-18 (`juggler_equality_language`): extremal families
  **EXACT — LEAN VERIFIED**.
- Phase-19 (`juggler_envelope_defect`): first-defect bound
  \(\Delta\ge\delta_j\) **EXACT — LEAN VERIFIED**. **extended** here by
  asking whether that bound is sharp.

## Branch budget

```text
Mathematical target     Can a nonempty suffix keep Δ_w(n)=δ_j, or does
                        every later branch strictly amplify?
Novelty hypothesis      Either every |v|>0 is strict, or equality is a
                        rigid exact-even suffix on T(n)
Falsifier               DEFECT_SUFFIX_COUNTEREXAMPLE to a proposed
                        universal amplification law; or no structural
                        equality
Existing machinery      localDefect, powerDeficit, append monotonicity,
                        HasPowTwoDepth, exact even towers
Maximum Phase-0 scope   Cheap Δ=δ_j search; trivial vs nontrivial;
                        one-step algebra; Lean only for the equality
                        law that survives
Promotion criterion     Sharpness characterization, or |v|>0 ⇒ Δ>δ_j,
                        or a minimized counterexample to amplification
Stop criterion          Recursive defect hierarchy; PowerHeight;
                        contraction margin; engine edits; termination
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Empty-prefix first step \(\Delta=\delta\) —
  **EXACT — LEAN VERIFIED**
- Exact even suffix preserves \(\Delta\) —
  **EXACT — LEAN VERIFIED**
- Any odd letter after a defect strictly increases \(\Delta\) —
  **EXACT — LEAN VERIFIED**
- Nonempty exact prefix already forces \(\Delta>\delta_j\) —
  **EXACT — LEAN VERIFIED**
- Universal \(|v|>0\Rightarrow\Delta>\delta_j\) — **REFUTED** at
  word `OE`, \(n=11\), and word `EE`, \(n=18\)
- Recursive suffix-defect object — not added
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.defect_sharpness`
- First-defect scan via local tightness; global \(\Delta\) only on a
  tiny bit budget
- Records: [juggler_defect_sharpness.md](../research/juggler_defect_sharpness.md),
  [juggler_defect_sharpness.json](../research/juggler_defect_sharpness.json)
- Tests: `tests/research/juggler_sequence/test_defect_sharpness.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- Universal nonempty-suffix amplification is refuted at \(n=11\),
  word `OE` (\(\Delta=\delta_O=35\)) and \(n=18\), word `EE`
  (\(\Delta=\delta_E=2\)).
- Empty suffix is not automatically sharp: word `OO` at \(n=9\) has
  \(|v|=0\) but \(\Delta>\delta_j\) because the first letter is exact.
- Mixed-word local strictness remains refuted at word `O`, \(n=9\).

## Formalization

Source locations below follow the current Lean layout. Development notes
retain this branch's original scope; subsequent results and open directions
are tracked in the [Juggler guide](../../attacks/juggler/AGENT.md).

`formal/Problems/Juggler/Defect.lean`. Added:

- `powerDeficit_even_first` / `powerDeficit_odd_first`
- `pow_sub_pow_gt_sub`
- `even_defect_gap_gt_of_pos_prefix` / `odd_defect_gap_gt_of_pos_prefix`
- `power_deficit_append_even_eq` / `power_deficit_append_even_of_defect`
- `power_deficit_append_odd_of_strict`
- `suffix_deficit_eq_of_exact_even` / `suffix_eq_of_deficit_eq`
- `power_deficit_eq_local_even_iff` / `power_deficit_eq_local_odd_iff`

No `PowerHeight`. No `sorry`. No `mixed_word_power_lt`. No
`PowerBoundStrict`. No ledger row. Existing `PowerBound` and first-defect
theorems are unchanged.

## Results

Classification **DEFECT_SHARP_GREEN**.

After a first defect at the start,

\[
\Delta_w(n)=\delta_j
\]

if and only if the remaining word is an exact even tower on \(T(n)\).
An odd continuation, or an inexact even continuation, strictly
increases the deficit. A nonempty exact prefix already forces
\(\Delta>\delta_j\).

So the first-defect bound is optimal: it is attained for arbitrarily
long exact-even suffixes (even monochrome towers such as
\(258\xrightarrow{EEE}2\)), and also for a mixed one-step suffix
(\(11\xrightarrow{OE}6\)). Universal amplification after one step is
false. No recursive suffix-defect object was added.

This is not a contraction margin and not a termination theorem.

## Open questions

Does an odd start admit arbitrarily long exact-even sharp suffixes
\(OE^s\), or is the unbounded sharp family only the even monochrome
towers?

## Decision

**PROMOTE** the sharpness characterization. Record
`DEFECT_SHARP_GREEN`. Do not register an attack. Do not claim
termination. Do not add a recursive suffix-defect calculus.

Best next question: does an odd start admit arbitrarily long
exact-even sharp suffixes, or only the even monochrome family?

## Publication assessment

Status: `EXPLORATORY`. A local sharpness lemma, not a paper candidate
and not a Juggler totality result.
