# Juggler accelerated odd-to-odd map

Status: **EXPLORATORY**

Standalone application phase on the first-return-to-odd Juggler map.
It is **not** a Research Engine control-layer experiment, not a second
acceleration, and not a claim that every positive integer reaches 1.

## Problem

Does the odd-to-odd first-return map \(A\), with exact branch label
\((a,b)\), have a simpler exact transition, inverse, contraction, or
repeated-branch law than one-step \(J\) or the existing `ResidualStep`?

## Exact statement

For odd \(n>1\), when the minimum exists,

\[
r(n)=\min\{r\ge 1:J^r(n)\text{ is odd}\},\qquad
A(n)=J^{r(n)}(n).
\]

The first letter from an odd start is always O, so the realized branch
is \((1,0)\) or \((1,b)\). ResidualStep is the comparison object: it
consumes a full odd run before an even tail with \(b\ge 1\). Phase 0
asks whether any identity of \(A\) fails to rewrite immediately as a
theorem about the original word \(w\). This is not a totality theorem.

## Current literature

- One-step floor-power map and \(T_w\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Itinerary`.
- `ResidualStep` / `oddEvenBlock` / `residualStep_global_defect` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Residuals`.
- \(T_w\) monotone on realizers —
  **EXACT — LEAN VERIFIED** (`image_monotone_of_follows`).
- Global defect identity —
  **EXACT — LEAN VERIFIED** (`J-global-defect-identity`).
- Floor cells / odd-cell uniqueness —
  **EXACT — LEAN VERIFIED**; inverse graph **CLOSE** as
  `BACKWARD_COMPLEX`.
- First-return-below —
  **CLOSE** as `EXCURSION_COMPLEX`.
- PE grammar / residual future / sum-rho / realization geometry /
  information complexity —
  **CLOSE**. Do not reopen.

Project relationship: **extended**. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does first-return-to-odd A have a simpler
                        exact law than one-step J or ResidualStep?
Novelty hypothesis      Even-tail collapse exposes a new odd-to-odd law
Falsifier               every identity is T_w / ResidualStep / cells
Existing machinery      floor_power, residual_excursion, globalDefect,
                        image_monotone_of_follows, floor cells
Maximum Phase-0 scope   odd n<=4000; algebraic comparison; decide
Promotion criterion     one exact statement that is not an itinerary theorem
Stop criterion          ACCELERATION_REPACKAGING or ACCELERATION_COMPLEX
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(A\) is first-return-to-odd with \(a\equiv 1\) —
  **COMPUTATIONALLY VERIFIED**
- \(J(n)\) odd \(\Rightarrow A(n)=J(n)\); \(J(n)\) even \(\Rightarrow\)
  \(A\) is ResidualStep with \(a=1\) —
  **COMPUTATIONALLY VERIFIED**, novelty **REPARAMETERIZATION**
- \(\Delta_{a,b}=\) `global_defect` —
  **REPARAMETERIZATION**
- Monotonicity on a fixed \((a,b)\) —
  **REPARAMETERIZATION** of `image_monotone_of_follows`
- \(A(n)<n\) iff \(J(n)\) is even —
  **EXACT — HUMAN PROOF**, novelty **REPARAMETERIZATION**
- \(\beta(a,b)\) is the finite-itinerary exponent —
  **REPARAMETERIZATION**
- \(A_{1,b}^{-1}\) is nested floor cells —
  **REPARAMETERIZATION**
- First \(J\)-return below \(n\) can occur on an even state before
  \(A(n)\) —
  **EXACT — HUMAN PROOF** (witness \(n=63\))
- Macro word removes irrelevant complexity —
  **REFUTED** as a mathematical discovery; it is a shorter encoding

## Experiments

- Probe: `research.juggler_sequence.accelerated`
- Diagnostic: odd \(n\le 4000\), plus hard / PE / first-return records
- Records: [juggler_accelerated.md](../research/juggler_accelerated.md)
- Data: `data/research/juggler/accelerated/`
- Tests: `tests/research/juggler_sequence/test_accelerated.py`

No GPU. No new Lean file. No generic \(n\le 10^8\) census.

## Conjectures

None opened.

## Counterexamples

- “\(A\) is ResidualStep”: \(n=3\), \(A(3)=5\), ResidualStep lands at
  \(1\) after `OOOEEE`.
- “\(A\) is a new transition law”: whenever \(J(n)\) is odd, \(A=J\).
- “Macro contraction is stronger than the envelope”: it is the envelope
  on `O` / `OE^b`.
- “Fixed \((a,b)\) inverse is cleaner than the cells”: it is the cells.
- “Every first \(J\)-return is an \(A\)-state”: smallest witness
  \(n=7\) returns at even \(4\) before \(A(7)=1\). Also \(n=63\)
  at even \(22\) before \(A(63)=1\).

## Formalization

None added. Existing lemmas `floorPower_odd_ge`,
`power_bound_contracts`, `image_monotone_of_follows`,
`global_defect_identity`, `residualStep_global_defect`,
`odd_preimage_unique`, and `image_eq_iterate` already cover the identities.
No `sorry`. No halt theorem.

## Results

Phase 0 is recorded in
[juggler_accelerated.md](../research/juggler_accelerated.md).
Classification **ACCELERATION_COMPLEX**, secondary
**ACCELERATION_REPACKAGING**.

On odd \(n\le 4000\), every start has a next odd landing and \(a=1\).
\(A\) is the odd subsequence of \(J\): one-step \(J\) when the image
is odd, and the \(a=1\) ResidualStep landing when the image is even.
Defect, monotonicity, contraction, \(\beta\), inverse, and consecutive
branches rewrite as existing word / floor-power / cell theorems.
Acceleration removes only even tails. The first-return problems of
\(J\) and \(A\) are not identical.

## Open questions

None from this branch. Do not replace \(J\) by \(A\). Do not infer
that every odd integer has a next odd landing outside the window.

## Decision

**CLOSE**. Acceleration is a shorter encoding of the same
state-dependent dynamics. Algebraic identities are repackaged word
theorems. Do not invent a second acceleration. Do not launch CUDA
Phase 2. Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A negative coordinate-change result, not a
paper candidate and not a Juggler totality result.
