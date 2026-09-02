# Juggler first-passage layer architecture

Status: **EXPLORATORY**

Standalone architectural rewrite of the Juggler formalization. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can the Juggler Lean stack be rewritten as one-way layers so that the
only unproved global arrow is finite coefficient stopping time?

## Exact statement

Separate

\[
\text{orbit}\neq\text{parity itinerary}\neq\text{word envelope}
\neq\text{stopping time}\neq\text{descent certificate}
\]

and delete the fused `Problems.Engine.FloorPower` stack. After the
rewrite, the isolated research target is

\[
\forall n\ge 2,\qquad \tau_G(n)<\infty
\]

where \(\tau_G(n)=\min\{k:G(\operatorname{word}(n,k))>0\}\) when the
minimum exists. Do not prove that statement. Prove only the already
known arrows that turn a finite \(\tau_G\) into a strict smaller
iterate and a contradiction to minimality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Terras stopping-time residue trees (`terras-1976-stopping-time`) are
  **methodological guidance only**. No Collatz density theorem is
  imported.
- Finite-itinerary envelope, equality, first-defect, compensated
  contraction, descent/capture, finite-progress coverage, and
  minimal-nontermination constraints — **EXACT — LEAN VERIFIED** in
  the previous fused stack. This branch re-homes those proofs.
- Drift-crossing and nested first-passage probes —
  **COMPUTATIONALLY VERIFIED** on stated windows; they are not this
  rewrite.

Project relationship: **extended**. Architecture of an existing local
theory, not a new Juggler identity.

## Branch budget

```text
Mathematical target     Can the Juggler formalization isolate a single
                        unproved implication
                        (n>1 ⇒ τ_G(n)<∞)
                        such that every later proposed theorem either
                        reduces to an existing layer or introduces a
                        new ingredient?
Novelty hypothesis      The missing object is not another itinerary identity.
                        It is a clean first-passage / certificate
                        separation. Recent CLOSE loops happened because
                        those layers were fused inside FloorPower.
Falsifier               The “new” objects cannot be stated without
                        mixing layers, or HasFiniteCoeffStop is already
                        proved for all n≥2 (it is not).
Existing machinery      floorPower, iterate, follows, PowerBound,
                        power_bound_contracts, Descent/Capture,
                        FiniteProgress, MinimalNonTerm, cycle/residual
                        satellites, Python τ₊ in drift_crossing
Maximum Phase-0 scope   Full rewrite of every Juggler Lean file into
                        Problems.Juggler with one-way imports. Delete
                        the Engine copies. Retarget Python paths.
                        No new τ_G hunt. No halt theorem. No ledger row.
Promotion criterion     Engine Juggler files are gone; each module has
                        one job; the missing implication is a first-class
                        Lean statement.
Stop criterion          leftover FloorPower or Engine export shim;
                        sorry; halt claim; dual namespaces; a new
                        computational hunt inside this branch.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `itinerary n k` and `follows n w ↔ itinerary n |w| = w` —
  **EXACT — LEAN VERIFIED** (reparameterization of `follows`)
- Word drift \(G(w)=2^{|w|}-3^{\#O(w)}\) — **EXACT — LEAN VERIFIED**
  (reparameterization of the exponent gap)
- `HasFiniteCoeffStop n → HasFiniteStop n` —
  **EXACT — LEAN VERIFIED** (wraps `power_bound_contracts`)
- `DescentCertificate` as the only certificate type —
  **EXACT — LEAN VERIFIED** (reparameterization of Descent/Capture)
- `MinimalNonTerm n → HasFiniteCoeffStop n` — **CONJECTURE** as a
  Prop; not proved
- `∀ n ≥ 2, HasFiniteCoeffStop n` — **CONJECTURE**; not proved
- Global halt — not claimed

## Experiments

- Formalization only. No new computational hunt.
- Existing probes keep their recorded windows. They are retargeted at
  `research.juggler_sequence.lean_paths`.
- Tests: `tests/research/juggler_sequence/test_layer_architecture.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened in `conjectures/`. The isolated statement
`∀ n ≥ 2, HasFiniteCoeffStop n` is recorded here as the leftover
research target, not as a new named conjecture file.

## Counterexamples

None. Finite windows with a realized \(\tau_G\) are not a proof that
every start has one.

## Formalization

`formal/Problems/Juggler/` with one-way imports. Barrel
`formal/Problems/Juggler.lean`. Deleted Engine copies:

- `FloorPower.lean`, `Progress.lean`, `MinimalNonTerm.lean`
- `RepeatedOE.lean`, `OddRunFinancing.lean`, `RepeatedBlock.lean`
- `OddOddFrontier.lean`, `ResidualChain.lean`, `ResidualPath.lean`
- `CycleItinerary.lean`, `CycleDiophantine.lean`

No `sorry`. No halt theorem. No ledger row.

## Results

- Engine Juggler files are gone. Live Lean is `formal/Problems/Juggler/` with one-way imports and barrel `formal/Problems/Juggler.lean`.
- `follows n w ↔ itinerary n |w| = w` is proved in Itinerary.
- `HasFiniteCoeffStop n → HasFiniteStop n` is proved; `∀ n ≥ 2, HasFiniteCoeffStop n` is the unproved `FiniteCoeffStopConjecture`.
- `DescentCertificate` is the only certificate type. `FiniteProgress n` is that type. Capture and Descent are not standalone defs.
- `HasFiniteCoeffStop n → ¬MinimalNonTerm n` is proved. `MinimalNonTerm n → HasFiniteCoeffStop n` is the unproved `MinimalImpliesCoeffStop`.
- Python probes resolve Lean names through `research.juggler_sequence.lean_paths`. No new hunt. No ledger row.

## Open questions

Does every \(n\ge 2\) have finite coefficient / drift stopping time?
Everything required to turn a yes into a strict smaller iterate is
already proved.

Residual-state sufficiency (object A) is recorded in
[juggler_residual_state.md](juggler_residual_state.md).

## Decision

**PROMOTE** the layered architecture. Engine Juggler files are gone,
imports are one-way, and the missing implication is a first-class Lean
statement. Do not claim termination.

Best next question: does every \(n\ge 2\) have finite coefficient /
drift stopping time?

## Publication assessment

Status: `EXPLORATORY`. Laboratory architecture, not a paper candidate
and not a Juggler totality result.
