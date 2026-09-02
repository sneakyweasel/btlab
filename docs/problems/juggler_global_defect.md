# Juggler global accumulated defect

Status: **STRUCTURAL**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Can the local floor remainders of a realized Juggler itinerary be
assembled into one exact, compositional global defect?

## Exact statement

For a realized itinerary \(w\) of length \(k\) with \(o\) odd letters,

\[
n^{3^o}
=
T_w(n)^{2^k}
+
\Delta_w(n),
\qquad
\Delta_w(n)\ge 0.
\]

The object \(\Delta_w(n)\) is defined by a recursive lift of the local
remainders \(\rho_i\), not as an informal sum and not as a prior
subtraction of the envelope.

## Current literature

- Local remainders and the weak envelope `PowerBound` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Defect` /
  `Envelope`.
- Numeric slack `powerDeficit` — the envelope difference after the
  weak bound is known. **extended** here by a constructive recurrence
  that implies the envelope.
- Naive path sum `pathDefectSum` — additive, not the exponent
  envelope. Distinct.
- OEIS A007320: step counts to 1. **known**. Totality is not claimed.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Can local floor defects be assembled into an
                        exact compositional Δ_w(n) with
                        n^{3^o} = T_w(n)^{2^k} + Δ_w(n)?
Novelty hypothesis      The missing object is the recursively weighted
                        accumulation, not the envelope slack and not
                        the naive path sum.
Falsifier               The recurrence fails to match the slack, or
                        Δ=0 does not recover local tightness.
Existing machinery      branchDefect, PowerBound, PowerBoundEq,
                        localsTight, powerDeficit, ResidualStep
Maximum Phase-0 scope   Recurrence + Lean identity/positivity/envelope
                        corollary/equality/composition; small word
                        census; ResidualStep certificate; CE inequality
                        only as far as the identity supports
Promotion criterion     Exact identity, composition law, and
                        Δ=0 ↔ local tightness, sorry-free
Stop criterion          Δ is only a rename of powerDeficit with no
                        new law; halt claim; another prefix hunt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `powGap a ρ e = (a+ρ)^e - a^e` — **EXACT — LEAN VERIFIED**
- Even step `D ↦ D + powGap(T^2, ρ, 2^k)` —
  **EXACT — LEAN VERIFIED**
- Odd step `D ↦ powGap(T^2, ρ, 2^k) + powGap(x^{2^k}, D, 3)` —
  **EXACT — LEAN VERIFIED**
- `global_defect_identity` — **EXACT — LEAN VERIFIED**
- `global_defect_append` — **EXACT — LEAN VERIFIED**
- `Δ = 0 ↔` all local remainders vanish `↔ localsTight ↔ PowerBoundEq`
  — **EXACT — LEAN VERIFIED**
- Mixed realized itinerary `⇒ Δ > 0` — **EXACT — LEAN VERIFIED**
- First-defect bound `ρ_i^{2^i} ≤ Δ` — **EXACT — LEAN VERIFIED**
- Residual step carries the identity — **EXACT — LEAN VERIFIED**
- On a CE, `Δ + n^{2^k} ≤ n^{3^o}` — **EXACT — LEAN VERIFIED**
- `Δ` exceeds the formal surplus on expanding mixed CE prefixes —
  **REFUTED** (equivalent to `T_w(n) < n`)

## Experiments

Short realized itineraries, `n ≤ 80`, length `≤ 5`: recurrence matches the
envelope slack exactly; mixed itineraries have `Δ > 0`; composition matches
the two-lift formula. Prefix scan of `OOE`, `OOEO`, `OOOE` on odd
`n ∈ [12, 400]`: no witness with `Δ` larger than the formal surplus.

Tests: `tests/research/juggler_sequence/test_global_defect.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

`Δ > n^{3^o} - n^{2^k}` on a realized expanding mixed prefix of a
hypothetical minimal non-1 start. None exist: that inequality is
`T_w(n) < n`.

## Formalization

`formal/Problems/Juggler/GlobalDefect.lean`. Residual wrapper in
`Residuals.lean`. CE surplus inequality in `Minimal.lean`. No `sorry`.
No halt theorem.

## Results

- Exact identity `n^{3^o} = T_w(n)^{2^k} + Δ_w(n)`.
- Envelope is the corollary `Δ ≥ 0`.
- Equality is `Δ = 0`, equivalent to vanishing local remainders and to
  the existing rigid monochrome towers.
- Composition is the two-term lift
  `powGap(mid^{2^{|u|}}, Δ_u, 3^{#O(v)}) + powGap(T_v^{2^{|v|}}, Δ_v, 2^{|u|})`.
- The identity does not forbid `OOE` / `OOEO` / `OOOE` on a CE.

## Open questions

Taken up by `docs/problems/juggler_defect_lower_bound.md`. A
first-defect Amplify bound exists and does not beat the formal
surplus on expanding `OOE`.

## Decision

**PROMOTE** the global defect layer. The recurrence is a new exact
object; it is not a rename of `powerDeficit`. Do not claim
termination.

Best next question: can a quantitative lower bound on `Δ` beat the
formal surplus on some mixed expanding class?

## Publication assessment

Status: `STRUCTURAL`. Exact identity and composition law. Not a
Juggler totality result.
