# Paper E: Juggler and the signed Collatz maps

## Problem

Consolidate the completed comparison into a living publication with reproducible
proof data and explicit review boundaries.

## Exact statement

No new mathematical statement is introduced by this packaging branch.
The [manuscript](../theory/juggler_signed_collatz_note.md) states the global
orbit code, preservation of actual periods, modular-return counterfamily,
signed ancestor exponent 21/25, and the fixed-grid ceiling below 99/100.

## Current literature

Classical inputs: terras-1976-stopping-time,
bernstein-lagarias-1996-conjugacy-map,
krasikov-lagarias-2003-difference-inequalities,
boshernitzan-1994-hardy-fields, and the attributed M. Sharpe grid method.
The paper distinguishes these inputs from the signed adaptation and isolated
obstructions. Specialist priority review remains pending.

## Branch budget

- **Target:** a complete first manuscript and publication package.
- **Novelty hypothesis:** a coherent comparative presentation of completed results.
- **Falsifier:** a headline exceeding its proof or duplicating prior work.
- **Already killed by?:** coding alone as an arithmetic attack is closed;
  this publication documents that limitation and opens no replacement attack.
- **Existing machinery:** Papers A-D, existing Lean proofs, exact certificate.
- **Maximum Phase-0 scope:** manuscript, proof map, audit, typesetting, release kit.
- **Promotion criterion:** proofs mapped, local checks and visual review pass.
- **Stop criterion:** list outstanding independent review; do not open a branch.

## Balanced-ternary formulation

Not used. The comparison concerns parity coding and ordinary height.

## Why BT may be relevant

The laboratory hosts the work; no representation advantage is asserted.

## Candidate operations / invariants

The existing code, period, divisibility, capped ancestor counts, and reciprocal mass.
No theorem-ledger claim is duplicated merely because it enters a manuscript.

## Experiments

tools/check_paper_e.py checks the exact table, grid, small-orbit barrier,
rational code examples, and modular-return witnesses.
tools/build_paper_e.py builds and hashes the publication package.

## Conjectures

No new conjecture. Integer realization, growing-depth distribution, and fate-class
harmonic mass retain the open status stated in their source dossiers.

## Counterexamples

The manuscript includes H(3)=83/27, H(4)=H(6), the signed height-budget
counterexample, modular returns, the backward ray, and stopped moment loss.

## Formalization

Problems.JugglerCollatzPaper imports the existing modules.
AxiomCheckJugglerCollatzPaper audits 28 selected declarations.
PaperECompletion identifies the odd-time series with the residue-limit code,
proves the limiting-frequency and real-exponent statements, and proves both
finite full-tree identities and direct sums over minimal stopping words.
Theorem 4.1's written equidistribution proof is not formalized.

## Results

Version 0.2.0 has a canonical manuscript, full proof narrative, bibliography,
author metadata, AI disclosure, formalization map, reviewer packet, version
policy, exact validation report, PDF/TeX build, and local deposit kit with
source-and-certificate archive.

The formal completion phase adds six audited statements with no new
mathematical conjecture. The series proof includes finite or empty odd-time
sets; the direct stopping-word sums are regrouped only after proving
summability. Local comparison confirms the target and cutoff quantifiers of
the signed ancestor theorem. Theorem 4.1 remains a separate analytic
formalization project: no applicable equidistribution theorem was found in
the installed Mathlib.

## Open questions

Independent statement coverage, written-proof review, and literature priority.
Publication venue and deposit remain author decisions.

## Decision

**PROMOTE** the living paper and its reproducible publication package.
The notation-completion phase is also **PROMOTE**; it closes the four
smaller coverage categories and records the remaining analytic boundary.
Best next question: does specialist review confirm the signed theorem's
precise literature distinction? No new arithmetic branch is opened.

## Publication assessment

**PAPER_CANDIDATE.** First complete preprint prepared locally, not deposited.
See the [build guide](../theory/PAPER_E_BUILD.md) and
[review record](../theory/paper_e_review.md).
