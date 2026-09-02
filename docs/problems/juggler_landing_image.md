# Juggler landing-image geometry

Status: **EXPLORATORY**

Standalone arithmetic layer on the parked word atlas. It is **not** a
Research Engine control-layer experiment, not a reopening of PE-factor,
residual-future, or summed-rho branches, and not a claim that every
positive integer reaches 1.

## Problem

Can the landing image \(Y_w=T_w(R_w)\) be described by a
low-complexity exact geometric structure that is stronger than the
parity support of the image?

## Exact statement

For a finite itinerary \(w\) and a bound \(N\),

\[
Y_w(N)=T_w\bigl(R_w(N)\bigr),\qquad
R_w(N)=\{n\le N:\operatorname{follows}(n,w)\}.
\]

The child split is the parity support of \(Y_w\). That identity is
the definition of \(d(w)\), not a theorem. The question is whether
\(Y_w\) is an interval, a small cell union, a monotone image of
\(R_w\), or recursively \(\Phi_E/\Phi_O\) of a closed class of
sets.

Absence under a scan bound is not global emptiness.

This says nothing about totality.

## Current literature

- `follows` / `image` / `floorPower` —
  **EXACT — LEAN VERIFIED**.
- Inverse-floor cells —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Preimages`.
- Realization-set geometry —
  **PARK**; \(d(w)\) is landing-parity monochromicity.
- Word-language / PE-factor —
  **CLOSE**. Do not reopen.
- Residual-future quotient / summed-rho —
  **CLOSE**. Do not reopen.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Is Y_w a low-complexity exact image object?
Novelty hypothesis      monotone / cell / Phi calculus stronger than
                        elementwise landing parity
Falsifier               inversions; Y_wb != Phi_b(Y_w); only tautologies
Existing machinery      image_after, floor_power, collect_realizing,
                        even_preimage
Maximum Phase-0 scope   N<=4000 prefixes k<=12; selected confirm N<=1e5
Promotion criterion     an exact image theorem that is not d(w)
Stop criterion          generic fragmentation; one cell per start;
                        halt / PE / residual reopen
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(T_w\) monotone on \(R_w\) —
  **EXACT — LEAN VERIFIED** as `image_monotone_of_follows`
- \(Y_{wb}=\Phi_b(Y_w)\) —
  **EXACT — HUMAN PROOF** from `image` composition plus the
  one-step parity filter (`COMPUTATIONALLY VERIFIED` on the
  diagnostic window)
- \(Y_E\) a single interval —
  **COMPUTATIONALLY VERIFIED** on the diagnostic window
- Mixed \(Y_w\) an interval —
  **REFUTED** for pure odd prefixes
- Atlas schema for LANDING_IMAGE —
  not added; infrastructure waits on a branching theorem, not a
  restatement of one-step monotonicity

## Experiments

- Probe: `research.juggler_sequence.landing_image`
- Diagnostic: \(n\le 4000\), \(k\le 12\)
- Confirm: selected words, \(n\le 10^5\)
- Records: [juggler_landing_image.md](../research/juggler_landing_image.md)
- Tests: `tests/research/juggler_sequence/test_landing_image.py`

## Conjectures

None opened in `conjectures/`.

## Counterexamples

Recorded by the probe. Expected: mixed-word images that are
`FRAGMENTED`; no \(T_w\) inversion if monotonicity holds.

## Formalization

`floorPower_even_mono` / `floorPower_odd_mono` in
`Problems.Juggler.Dynamics` and `image_monotone_of_follows` in
`Problems.Juggler.Itinerary`. Sorry-free. No ledger row: the lemma
is one-step monotonicity on a parity class, not a new branching
calculus.

## Results

On \(N\le 4000\), \(k\le 12\) (1836 prefixes) and selected confirm
at \(N\le 10^5\): zero inversions; endpoints of \(R_w\) control the
hull of \(Y_w\); \(Y_{wb}=\Phi_b(Y_w)\) on 1834 checks. Mixed
images are often `FRAGMENTED` (248 rows). Pure \(O^r\) is one
component per realizer. `IMAGE_CELL_GREEN`,
`IMAGE_BRANCHING_GREEN`, `IMAGE_THAW_GREEN`, and
`IMAGE_SCALE_GREEN` were not promoted. Record:
[juggler_landing_image.md](../research/juggler_landing_image.md).

## Open questions

The leftover atlas question is unchanged: is there any arithmetic,
other than the integer \(y\) itself, that decides whether a
persistent residual landing stays odd-to-odd?

## Decision

**PARK**. The exact facts that survive — monotonicity on realizers
and \(\Phi_E/\Phi_O\) composition — are consequences of `floorPower`
being monotone on each parity class. Mixed images fragment. Do not
promote a restatement of the one-step map. Do not add an atlas image
schema. Do not reopen closed branches.

Best next question: is there any arithmetic, other than the integer
\(y\) itself, that decides whether a persistent residual landing
stays odd-to-odd?

## Publication assessment

Status: `EXPLORATORY`. An image-geometry reading, not a paper
candidate and not a Juggler totality result.
