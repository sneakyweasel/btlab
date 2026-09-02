# Juggler expanding-residual concatenation

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not an
expanding-grammar reopen, not Paper B, not escape-margin \(M\), and
not a claim that every positive integer reaches 1.

This is the leftover of [juggler_non_escape.md](juggler_non_escape.md):
can a `MinimalNonTerm` itinerary concatenate infinitely many expanding
residual blocks without a contracting itinerary?

## Problem

Is “infinite expanding-residual concatenation without a contracting
word” a strictly smaller class than a minimal non-1 start, or is it
the same leftover?

## Exact statement

An itinerary is expanding when \(2^{|w|}<3^{\#O(w)}\) and contracting when
\(3^{\#O(w)}<2^{|w|}\). Phase 0 asks:

1. whether expanding itineraries are closed under concatenation;
2. whether a `MinimalNonTerm` start can realize any contracting itinerary;
3. whether those two facts identify the leftover with the unbounded
   `MinimalNonTerm` branch already named in
   [juggler_non_escape.md](juggler_non_escape.md).

Do not prove that a PE chain is finite. Do not prove
\(\neg\operatorname{EscapesToInfinity}\). Do not reopen
`EXPANDING_GRAMMAR_IS_PERSISTENCE`.

## Current literature

- `exponentExpanding` / `exponentGap` —
  **EXACT — LEAN VERIFIED**.
- Persistence equals expansion on \(n\ge 2\) —
  **CLOSE** (`EXPANDING_GRAMMAR_IS_PERSISTENCE`).
- Two, three, and four consecutive PE blocks exist
  (\(365\to 763\to 1749\to 4447\); length-5 run at \(2183\)) —
  **REFUTED** as a two-block prohibition.
- `power_bound_contracts` and `minimal_nonterm_no_descent` —
  **EXACT — LEAN VERIFIED**.
- Cycle-or-escape and the CE `OOEOOE` trap —
  **EXACT — LEAN VERIFIED** (`J-trajectory-cycle-or-escape`,
  `J-minimal-ooeooe-escape-trap`).

Project relationship: **extended**. The non-escape leftover is
identified, not solved.

## Branch budget

```text
Mathematical target     Is infinite PE concatenation without a
                        contracting itinerary a stricter class than
                        MinimalNonTerm?
Novelty hypothesis      either a CE realizes a contracting
                        concatenation, or the leftover is the
                        same unbounded CE branch
Falsifier               a CE-shaped contracting itinerary; or the
                        identification is already written
Existing machinery      exponentExpanding; power_bound_contracts;
                        minimal_nonterm_no_descent; residual_chain
Maximum Phase-0 scope   expanding_append; CE prefix-NC; chain
                        scan; no halt; no grammar reopen
Promotion criterion     a new exact lemma that is not the
                        envelope contraposed, and a genuine
                        smaller subclass
Stop criterion          REPARAMETERIZATION of MinimalNonTerm;
                        EXPANDING_GRAMMAR_IS_PERSISTENCE; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- expanding itineraries are closed under concatenation —
  **EXACT — LEAN VERIFIED**
- a CE never realizes an exponent-gap word —
  **EXACT — LEAN VERIFIED**
- every realized prefix of a CE is prefix-noncontracting —
  **EXACT — LEAN VERIFIED**
- scanned persistent residual blocks (\(y>x\)) are expanding, and
  their concatenations stay expanding —
  **COMPUTATIONALLY VERIFIED**
- a later residual may stay \(\ge\) the original start while
  contracting versus its own \(x\) — that is not a PE block —
  **OBSERVATION**
- infinite PE concatenation is a strictly smaller class than
  `MinimalNonTerm` —
  **REPARAMETERIZATION**
- PE chains are finite — not claimed
- no trajectory escapes — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.expanding_residual_concat`
- Records:
  [juggler_expanding_residual_concat.md](../research/juggler_expanding_residual_concat.md),
  [juggler_expanding_residual_concat.json](../research/juggler_expanding_residual_concat.json)
- Tests: `tests/research/juggler_sequence/test_expanding_residual_concat.py`
- Lean: `exponentExpanding_append` in `ItineraryStats.lean`;
  `minimal_nonterm_not_exponentGap` and
  `minimal_nonterm_prefix_noncontracting` in `Escape.lean`.
  Laboratory barrel only. No `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

None to concatenation closure or to CE prefix-NC. The stronger
claims that fail:

- “two consecutive PE blocks are impossible” — already refuted by
  \(365\to 763\to 1749\).
- “the leftover is a stricter combinatorial class” — a CE cannot
  realize a contracting itinerary, so PE concatenation without a
  contracting itinerary is the CE leftover rewritten.
- “formal contraction kills a PE concatenation” — concatenation of
  expanding itineraries stays expanding.

## Formalization

`ItineraryStats.lean` adds `exponentExpanding_append`. `Escape.lean` adds
the CE prefix-NC pair. `FloorPower` and `MinimalNonTerm` are not
rewritten. No `sorry`. No `no_juggler_escape`. No infinite-path
type. Paper A is unchanged.

## Results

Classification **EXPANDING_CONCAT_CE_CLOSE**.

Expanding itineraries are closed under concatenation —
**EXACT — LEAN VERIFIED** (`J-exponent-expanding-append`). A
`MinimalNonTerm` start never realizes an exponent-gap itinerary, so
every realized prefix is prefix-noncontracting —
**EXACT — LEAN VERIFIED** (`J-minimal-prefix-noncontracting`).
Therefore an infinite PE concatenation without a contracting itinerary
is not a smaller class: it is the unbounded CE branch already
isolated by the non-escape spine —
**REPARAMETERIZATION** (`J-expanding-concat-is-ce`). Window
\(n<801\): \(87/87\) persistent blocks expand; \(83\) later
residuals stay above the original start while contracting versus
their own \(x\).

This is not a halt theorem and not a finite-run bound.

## Open questions

Answered in
[juggler_third_residual.md](juggler_third_residual.md): the
completed third residual is not uniformly a drop and not uniformly
PE. Do not reopen the expanding-grammar obstruction. Do not claim
a uniform PE-run bound.

## Decision

**CLOSE** the leftover as a reparameterization of `MinimalNonTerm`.
The new exact facts are concatenation closure and CE prefix-NC; they
identify the class, they do not shrink it. Do not claim that PE
chains are finite. Do not claim that escape is impossible.

Best next question: answered in
[juggler_third_residual.md](juggler_third_residual.md).

## Publication assessment

Status: `EXPLORATORY`.

A leftover identification, not a paper candidate and not a Juggler
totality result.
