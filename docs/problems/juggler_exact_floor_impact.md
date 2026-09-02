# Juggler exact-floor impact

Status: **EXPLORATORY**

Standalone first-descent census of steps where the Juggler floor is
a no-op because the real power is already an integer. It is **not**
a Research Engine control-layer experiment, not an itinerary-atlas
recensus, not a reopen of floor-boundary, and not a claim that
every positive integer reaches 1.

## Problem

On first-descent walks, do isolated exact-floor steps (perfect
squares that are not a continuing equality tower) bias
first-descent class or PE continuation beyond the known local
package: exact iff square, crumb 0, next letter equals the current
letter, tower iff the image is a square?

## Exact statement

Write \(T\) for the Juggler map. A state \(x\) is *exact* when
\(\lfloor\sqrt x\rfloor=\sqrt x\) (\(x\) even) or
\(\lfloor x\sqrt x\rfloor=x^{3/2}\) (\(x\) odd). Both are
equivalent to \(x\) being a perfect square
(`localDefect*_eq_zero_iff`). An exact step is *isolated* when
\(T(x)\) is not a square. Phase 0 tags every exact step on the
first-descent path of each start \(2\le n\le 10^5\) and asks
whether the tagged events change first-descent class
\(\{E,OE,OOEE,\mathrm{leftover}\}\) or PE continuation by any law
that is not the local package above. This says nothing about
totality.

## Current literature

- Exact iff square —
  **EXACT — LEAN VERIFIED**
  (`floorPower_even_sq_eq_iff_square`,
  `floorPower_odd_sq_eq_cube_iff_square`,
  `localDefectEven_eq_zero_iff`,
  `localDefectOdd_eq_zero_iff`).
- Envelope equality forces monochrome towers —
  **EXACT — LEAN VERIFIED**
  (`power_bound_eq_implies_monochrome`).
- Floor-boundary next-gap census —
  **CLOSE** ([juggler_floor_boundary.md](juggler_floor_boundary.md)).
  Do not reopen \(e=0\Rightarrow\) small next gap.
- Even-square walk increment is exactly \(-1\) —
  **EXACT — HUMAN PROOF** on the coboundary branch.
- Word atlas —
  **PARK**. This branch does not recensus it.

Project relationship: **reproduced** the local package;
**refuted** as a new first-descent or PE impact.

## Branch budget

```text
Mathematical target     On first-descent walks, do isolated exact-floor
                        steps (perfect squares that are not a continuing
                        equality tower) bias first-descent class or PE
                        continuation beyond the known local package
                        (exact iff square; crumb 0; next letter = current
                        letter; tower iff image is square)?
Novelty hypothesis      Isolated exact landings concentrate on first-
                        descent E or PE odd-squares at a rate invisible
                        from square density and the monochrome letter law
Falsifier               Exact-event rate matches square density in the
                        visited parity class; first-descent class is the
                        parity itinerary; PE exact hits are exactly the odd
                        squares that appear, with no extra continuation
Existing machinery      local_tight / is_square (power_algebra.py),
                        local_defect, saturation_prefix,
                        first-descent walk, leading_drift,
                        classify_step / residual_excursion
Maximum Phase-0 scope   Python scan of starts n<=1e5 to first descent
                        (step_cap 40); PE subsample odd n<=4000; persist
                        event tags + impact summary; decide
Promotion criterion     An exact implication that is not local_tight,
                        monochrome towers, or the CLOSED floor-boundary
                        next-gap census
Stop criterion          All aggregates are KNOWN / REPARAMETERIZATION;
                        any GPU atlas recensus, Paper A edit, N0 raise,
                        or new Lean file
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exact iff square —
  **EXACT — LEAN VERIFIED** (existing)
- Isolated exact step forces next letter to match —
  **EXACT — LEAN VERIFIED** (monochrome one-step); **COMPUTATIONALLY VERIFIED**
  on the Phase-0 grid (0 letter-force failures)
- Exact crumb is 0 —
  **EXACT — LEAN VERIFIED**; **COMPUTATIONALLY VERIFIED** (0 mismatches)
- Isolated exact steps bias first-descent class beyond word length —
  **REFUTED** on the Phase-0 grid (E mid-rate is 0; OE rate
  \(3.2\cdot 10^{-4}\) sits below OOEE / leftover; leftover is
  longer than OOEE and slightly sparser because the states are
  larger)
- Exact PE hits have a continuation other than the integer cube / root —
  **REFUTED** (8 hits, all squares, image equals the cube or root)
- Exact E-certificate share differs from even-square density among
  even starts —
  **REFUTED** (158/50000, ratio 1 against the combinatorial baseline)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.exact_floor_impact`
- Artifact:
  `data/research/juggler/exact_floor_impact/summary.json`
- Note: [juggler_exact_floor_impact.md](../research/juggler_exact_floor_impact.md)
- Tests:
  `tests/research/juggler_sequence/test_exact_floor_impact.py`

First-descent starts \(n\le 10^5\), step cap 40. PE subsample
odd-odd \(n\le 4000\). No GPU. No atlas recensus. No Lean. No
\(N_0\) raise. No companion edit.

## Conjectures

None opened. Computational observations are not conjectures.

## Counterexamples

- “Floor is a no-op at a non-square” — 0 mismatches on 374 exact
  events and on every inexact step of the scan.
- “Exact step can flip the next letter” — 0 failures. Canonical
  witnesses: \(9\to 27\) (O then O), \(36\to 6\) on the orbit of 3
  (E then E).
- “Isolated exact steps create a new first-descent class” — mid-path
  isolated hits are 8 OE + 16 OOEE + 29 leftover. Class E never
  appears (word length 1, start not a square). That is occupancy
  of a longer itinerary, not a new certificate.
- “PE exact continuation is extra” — image is \(m^3\) on odd
  squares and \(m\) on even squares. Eight PE hits, zero extras.

## Formalization

None new. The square and monochrome lemmas stay in `Equality.lean`
and `Defect.lean`. No `ExactFloorImpact.lean`. Paper A is
unchanged. No `sorry`.

## Results

Classification **EXACT_FLOOR_IMPACT_KNOWN**.

- Identity: 0 mismatches, 0 letter-force failures, 0 even-square
  walk-increment failures. 374 exact events (356 isolated, 18
  tower). 607 starts uncapped at step 40.
- Density: per-state \(1/\sqrt x\) baseline on unique visited
  states; every magnitude bin matches (ratios \(0.32\)–\(4.15\);
  Poisson-consistent on sparse large bins).
- E-certificates: \(50000\) even starts, \(158\) exact descending
  evens, ratio \(1\) against even-square density.
- Mid-isolated rates: E \(0\) (mean length 1), OE
  \(3.20\cdot 10^{-4}\) (length 2), OOEE \(2.59\cdot 10^{-3}\)
  (length 4), leftover \(1.59\cdot 10^{-3}\) (mean length
  \(10.4\)). Leftover is slightly below OOEE because leftover
  states are larger, not because exactness selects a class.
- PE: 275 PE starts, 8 exact hits, 0 non-squares, 0 extra
  continuations.

## Open questions

None from exact-floor impact. Do not recensus the itinerary atlas, do
not reopen floor-boundary next-gap, do not raise \(N_0\), and do
not add a companion mark from this branch.

## Decision

**CLOSE.** Floor is a no-op exactly on perfect squares. The tagged
impact of those steps is the existing local package: crumb 0,
monochrome next letter, tower iff the image is a square. Isolated
exact landings do not create a first-descent class and do not
alter PE continuation. Every Phase-0 statement is `KNOWN` or
`REPARAMETERIZATION`. That is the stop criterion. Best next
question: none from this door; do not start another exact-step
census.

## Publication assessment

Status: `EXPLORATORY`. A negative impact census of already-integer
floor steps. Not a paper candidate. No Paper A/B edit.
