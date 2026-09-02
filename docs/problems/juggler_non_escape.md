# Juggler non-escape spine

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a Paper B
reopen, not an escape-margin \(M\) revival, not an expanding-grammar
attack, not a bunched-short reopen, not a length-11 census, and not a
claim that every positive integer reaches 1.

This is the unbounded leftover named in
[juggler_residual_path.md](juggler_residual_path.md): a bounded orbit
repeats, so the only remaining non-1 possibility on a minimal
counterexample is escape. Phase 0 packages that split and transfers
the `OOEOOE` even-trap from `CycleMin` onto `MinimalNonTerm`.

## Problem

On a hypothetical minimal non-1 start, is the orbit a nontrivial
cycle or unbounded? Does the `OOEOOE` even-trap force the escape
branch onto another `OO`, without a cycle-return hypothesis?

## Exact statement

Define

\[
\operatorname{EscapesToInfinity}(n)
:=\forall B.\;\exists k.\; B<T^{k}(n),
\qquad
\operatorname{EventuallyCycles}(n)
:=\exists i<j.\; T^{i}(n)=T^{j}(n).
\]

Every \(n\in\mathbb{N}\) satisfies

\[
\operatorname{EventuallyCycles}(n)
\lor
\operatorname{EscapesToInfinity}(n).
\]

If \(\operatorname{MinimalNonTerm}(n)\), then a cycle value stays
\(\ge n\) (hence is not the \(1\)-cycle), or the orbit escapes.

If \(\operatorname{MinimalNonTerm}(n)\) and \(n\) follows `OOEOOE`,
then the landing is odd, the forced next letter is `O`, and the image
after that `O` is again odd. An even landing, or an even next image
below \(n^{2}\), is `FiniteProgress` and is impossible on a CE.

This is **not** a halt theorem. It does **not** prove
\(\forall n,\;\neg\operatorname{EscapesToInfinity}(n)\). It does
**not** prove that all cycles are impossible.

## Current literature

- Bounded residual prefix \(\Rightarrow\) repeat \(\Rightarrow\) cycle
  — **EXACT — LEAN VERIFIED** (`bounded_prefix_not_nodup`,
  `trajectory_repeat_cycle`).
- `MinimalNonTerm` orbits stay \(\ge n\); first `O^a E` overshoots
  — **EXACT — LEAN VERIFIED**.
- \(T_{\mathtt{OOEOOE}}(n)<n^{2}\); even landing drops —
  **EXACT — HUMAN PROOF** (`J-cyclemin-ooeooe-square-preimage`).
- Next-`O` dichotomy on `CycleMin` —
  **EXACT — HUMAN PROOF** (`J-cyclemin-ooeooe-next-o`).
- Escape-state margin \(M\) —
  **CLOSE** (`ESCAPE_STATE_COMPLEX`).
- `FiniteCoeffStopConjecture` — isolated `def`, not a theorem.
- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**.
  Totality is not claimed.

Project relationship: **extended**. The residual-path unbounded
branch is named and given an escape-capable `OOEOOE` constraint.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     On a hypothetical minimal non-1 start, is the
                        orbit a nontrivial cycle or unbounded — and
                        does the OOEOOE even-trap force the escape
                        branch onto another OO (not a CycleMin return)?
Novelty hypothesis      CycleMin corridor lemmas survive after dropping
                        the return hypothesis, so they constrain
                        escapers, not only cyclers
Falsifier               the transfer needs image = n; or the only new
                        Lean is pigeonhole already in Residuals.lean
Existing machinery      ReachesOne / FiniteProgress spine; MinimalNonTerm;
                        bounded_prefix_not_nodup; trajectory_repeat_cycle;
                        minimal_first_even_overshoots; wordOOEOOE;
                        even_floorPower_lt_iff; human 81/64 and 243/256
Maximum Phase-0 scope   Lean Escape module + one MinimalNonTerm OOEOOE
                        dichotomy; dossier/journal/tests; no halt claim
Promotion criterion     a new exact escape-capable constraint, or a
                        clean Lean cycle-or-escape reduction that is
                        not a restatement of residual_path
Stop criterion          FiniteCoeffStopConjecture; Paper B reopen;
                        escape-margin M; expanding-grammar; bunched-short;
                        length-11 census; CLI / visualization
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- every orbit eventually cycles or escapes —
  **EXACT — LEAN VERIFIED**
- a bounded orbit eventually cycles —
  **EXACT — LEAN VERIFIED**
- `ReachesOne` is the \(1\)-cycle case of `EventuallyCycles` —
  **EXACT — LEAN VERIFIED**
- `MinimalNonTerm` \(\Rightarrow\) cycle with values \(\ge n\), or escape —
  **EXACT — LEAN VERIFIED**
- `follows n OOEOOE` \(\Rightarrow\) \(T_{\mathtt{OOEOOE}}(n)<n^{2}\) —
  **EXACT — LEAN VERIFIED**
- `follows n OOEOOEO` \(\Rightarrow\) image \(<n^{2}\) —
  **EXACT — LEAN VERIFIED**
- on `MinimalNonTerm`, an `OOEOOE` landing is odd and the next
  completed letter after the forced `O` is again `O` —
  **EXACT — LEAN VERIFIED**
- growing residual prefixes such as \(365\to 763\to 1749\to 4447\)
  are finite escape prefixes, not unbounded orbits —
  **COMPUTATIONALLY VERIFIED**
- no trajectory escapes to infinity — not claimed
- all cycles are impossible — not claimed
- global halt — not claimed
- `FiniteCoeffStopConjecture` — not claimed

## Experiments

- Probe: `research.juggler_sequence.non_escape`
- Records: [juggler_non_escape.md](../research/juggler_non_escape.md),
  [juggler_non_escape.json](../research/juggler_non_escape.json)
- Tests: `tests/research/juggler_sequence/test_non_escape.py`
- Lean: `formal/Problems/Juggler/Escape.lean`, laboratory barrel only.
  Not imported by `Problems.JugglerPaper`. No `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

None to the cycle-or-escape split or to the `MinimalNonTerm` `OOEOOE`
trap. The stronger claims that fail or stay closed:

- “the transfer needs a cycle return `image = n`” — the even trap
  uses only `image < n^{2}` and `even_floorPower_lt_iff`.
- “\(M=T^{2^{k}}-n^{2^{k}}\) is a progress law on escape prefixes”
  — already **CLOSE** as `ESCAPE_STATE_COMPLEX`.
- “every residual chain is bounded” — not claimed; \(365\to 4447\)
  is a growing finite prefix.
- “no trajectory escapes” — not claimed.

## Formalization

`formal/Problems/Juggler/Escape.lean`, above `Residuals`, `Minimal`,
`Envelope`, and `CycleCore`. Added:

- `EscapesToInfinity` / `EventuallyCycles`
- `not_escapes_iff_bounded` / `bounded_trajectory_eventually_cycles`
- `cycles_or_escapes` / `reachesOne_implies_eventually_cycles`
- `minimal_nonterm_cycles_or_escapes` /
  `minimal_nonterm_cycle_values_ge`
- `follows_ooeooe_image_lt_sq` / `follows_ooeooeo_image_lt_sq`
- `minimal_ooeooe_not_even_landing` / `minimal_ooeooe_forces_oo`

`FloorPower`, `Progress`, and `MinimalNonTerm` are not rewritten.
No `sorry`. No `no_juggler_escape`. No `FiniteCoeffStopConjecture`
theorem. No coinductive infinite-path type. No `PowerHeight`.
Paper A is unchanged.

## Results

Classification **NON_ESCAPE_SPINE_GREEN**.

Every orbit eventually cycles or escapes. On `MinimalNonTerm n`, a
cycle stays \(\ge n\) or the orbit is unbounded. If that \(n\)
follows `OOEOOE`, the landing is odd and the forced next `O` is
followed by another `O`. Even landings drop; even next images below
\(n^{2}\) drop. Both are `FiniteProgress`, hence impossible on a CE.

The square-cell comparisons \(64/81\) and \(128/243\) are the same
envelope already used for `CycleMin`. The new point is that they
do not need a return `image = n`.

This is not a halt theorem, not a cycle-exclusion theorem, and not
`FiniteCoeffStopConjecture`.

## Open questions

Answered in
[juggler_expanding_residual_concat.md](juggler_expanding_residual_concat.md)
and [juggler_third_residual.md](juggler_third_residual.md):
infinite PE concatenation is not a stricter class; after the CE
trap forces `OOEOOEOO`, the third residual is not uniformly a drop
and not uniformly PE. Do not reopen Paper B, bunched-short cells,
escape-margin \(M\), or a length-11 census.

## Decision

**PROMOTE** the Lean cycle-or-escape split and the escape-capable
`OOEOOE` trap. The trap does not use `CycleMin` return. Do not
claim that escape is impossible. Do not claim that all cycles are
impossible. Do not claim termination.

Best next question: answered in
[juggler_third_residual.md](juggler_third_residual.md).

## Publication assessment

Status: `EXPLORATORY`.

An organizing spine plus one transferred prefix theorem. Not a
paper candidate and not a Juggler totality result.
