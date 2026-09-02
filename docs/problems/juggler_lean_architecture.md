# Juggler Lean architecture

Status: **STRUCTURAL**

Lean-only spine for the Juggler laboratory: upper `EnvelopeState`,
lower `AboveAnchor`, and the two-sided `PowerCorridor`. This is
**not** a termination attack, not Paper A, and not a claim that
every positive integer reaches 1.

## Problem

Does the existing envelope / anchor pair yield a reusable two-sided
corridor, even-run lower barrier, and a Residuals-free `CycleCore`,
without new Juggler dynamics?

## Exact statement

For integers \(n \ge 2\) and a realized finite itinerary \(w\):

- an `EnvelopeState` is a one-sided bound \(x^A \le n^B\);
- `AboveAnchor n w` is `follows n w` and \(n \le T^i(n)\) for all
  \(i \le |w|\);
- a `PowerCorridor` is the two-sided cell \(n^L \le x < n^U\).

The six corollaries of this packaging are:

| Id | Statement |
|----|-----------|
| A | \(n^L \le x\), \(x^A \le n^B\), \(B < LA\) \(\Rightarrow \bot\) |
| B | \(x < n^{2k}\), \(x\) even \(\Rightarrow T(x) < n^k\) |
| C | \(x < n^4\), \(x,T(x)\) even \(\Rightarrow T^2(x) < n\) |
| D | an envelope drop of a continuation forbids `AboveAnchor` |
| E | `AboveAnchor` plus \(r\) evens \(\Rightarrow n^{2^r} \le x\) |
| F | \(2^{a+2r+1} \le 3^{a+r}\) independent of cycle closure |

No new floor-power identity is claimed.

## Current literature

Project relationship: **reparameterization** of existing Lean
theorems (`J-envelope-lt-pow`, `J-above-anchor`,
`J-cube-not-square-split`, isolated-OE survival). Paper A
(`Problems.JugglerPaper`) is unchanged. Prior spine audit:
[juggler_lean_spine.md](../architecture/juggler_lean_spine.md).

## Branch budget

```text
Mathematical target     Does upper EnvelopeState + lower AboveAnchor
                        yield a reusable corridor obstruction / reset,
                        without new Juggler dynamics?
Novelty hypothesis      The missing object is the two-sided collision
                        (Corollary A) and the generic even-run lower
                        barrier, not another named word.
Falsifier               Cube-band or isolated-OE still needs a bespoke
                        exponent proof after the shared lemmas exist.
Existing machinery      EnvelopeState, envelope_lt_pow, AboveAnchor,
                        even_below_anchor_pow, finiteProgress_of_imageLt
Maximum Phase-0 scope   Composition API + corridor lemmas + even-run
                        extract + CycleCore Residuals cut. No new attack.
Promotion criterion     The six corollaries compile as shared lemmas;
                        lake build Problems.Juggler is green; architecture
                        doc matches the live import graph.
Stop criterion          A proof only compiles after weakening a shared
                        theorem, or a new research module is required.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The laboratory host is balanced ternary; the
Juggler map is independent of trit encoding.

## Candidate operations / invariants

- `EnvelopeState.map_word` — fold `.even` / `.odd` on a realized itinerary.
  **REPARAMETERIZATION**
- `PowerCorridor` / `envelope_corridor_contradiction` — two-sided
  collision. **REPARAMETERIZATION**
- `even_below_anchor_pow` / `two_even_below_fourth` — even reset.
  **REPARAMETERIZATION**
- `AboveAnchor` + `aboveAnchor_even_run_ge_pow` — lower even-run
  barrier. **REPARAMETERIZATION**
- `HasFiniteStop` bridges from image drop / `k=1` envelope.
  **REPARAMETERIZATION**

No Collatz-solution language. No halt theorem.

## Experiments

None. Formal packaging only. Regression is `lake build
Problems.Juggler`, `lake build Problems.JugglerPaper`, and the
fast tests `test_problem_dossiers.py`, `test_minimum_relative.py`,
`test_layer_architecture.py`.

## Conjectures

None opened. `FiniteCoeffStopConjecture` remains the isolated
laboratory target and is not a claim of this branch.

## Counterexamples

None new. Existing leftover odd-landing corridors (365, 501, 6187)
are unchanged.

## Formalization

Lean modules, no `sorry`:

- `formal/Problems/Juggler/Envelope.lean` — `EnvelopeState`,
  `map_word`, `of_follows`, cycle-envelope family
- `formal/Problems/Juggler/Corridor.lean` — `PowerCorridor`,
  Corollaries A–C, even-reset family
- `formal/Problems/Juggler/CubeCorridor.lean` — cube-band
  arithmetic; no `AboveAnchor`
- `formal/Problems/Juggler/Progress.lean` — `FiniteProgress` and
  geometric descent bridges
- `formal/Problems/Juggler/FirstInternalOO.lean` — isolated-prefix
  syntax and Corollary F
- `formal/Problems/Juggler/MinimumRelative.lean` — `AboveAnchor`,
  Corollaries D–E
- `formal/Problems/Juggler/CycleCore.lean` — cycle foundations;
  imports `Envelope` + `Cells` + `MinimumRelative`, not `Residuals`
- `formal/Problems/Juggler/CycleObstructions.lean` — named-word
  exclusions and isolated CycleMin wrappers
- `formal/Problems/Juggler/FirstPassage.lean` —
  `hasFiniteStop_of_imageLt`, `hasFiniteStop_of_power_bound_lt_pow`
- `formal/Problems/Juggler/Minimal.lean` — CE wrappers of the
  generic even-run barrier; no `GlobalDefect` import

Paper A comments are not edited.

## Results

Live Lean imports (not slogans):

```text
Dynamics → Iteration → Termination → Itinerary → ItineraryStats
                                              ↓
                                           Envelope
                                              ↓
                                           Corridor
                                              ↓
                                         CubeCorridor
                                              ↓
                                           Progress
                                              ↓
                                        FirstInternalOO
                                              ↓
                                        MinimumRelative
                                    ↓                 ↓
                                 Minimal          CycleCore
                                    ↓                 ↓
                                 Scale            CycleObstructions
                                    ↓                 ↓
                              Residuals          CycleExtrema / leftover
```

`CycleCore` imports `Envelope` + `Cells` + `MinimumRelative`, not
`Residuals`. `Cycles.lean` re-exports `CycleCore` +
`CycleObstructions` + `CycleExtrema`.

Canonical primitives:

| Kind | Object | Home |
|------|--------|------|
| Primitive | `floorPower` / `follows` / words | Dynamics, Itinerary, ItineraryStats |
| Primitive | `EnvelopeState` / `map_word` / `envelope_lt_pow` | Envelope |
| Primitive | `PowerCorridor` | Corridor |
| Primitive | cube-band geometry | CubeCorridor |
| Primitive | `AboveAnchor` | MinimumRelative |
| Primitive | isolated-prefix envelope | FirstInternalOO |
| Primitive | `HasFiniteStop` | FirstPassage |
| Primitive | `DescentCertificate` / `FiniteProgress` | Certificates, Progress |
| Derived | `PowerBound` as \(A=2^{\|w\|}\), \(B=3^{\#O}\) | Envelope |
| Derived | `even_below_anchor_pow` / `two_even_below_fourth` | Corridor |
| Consumer | `CycleMin` / `aboveAnchor_of_cycleMin` | CycleCore |
| Consumer | `MinimalNonTerm` / `aboveAnchor_of_minimalNonTerm` | Minimal |
| Consumer | named `no_cycle_itinerary_*` / isolated CycleMin wrappers | CycleObstructions |
| Legacy aliases | `power_bound_word`, `power_bound_contracts`, `unresolved_is_odd_odd`, `finiteProgress_of_descent`, `isolated_oe_ge_implies_exponent`, `floorPower_odd_lt_sq` | keep; do not use in new proofs |

Envelope / anchor / progress APIs:

- `EnvelopeState.refl` / `.map_letter` / `.map_word` /
  `.of_follows` → `envelope_lt_pow` → `power_bound_lt_pow`
- `AboveAnchor` is the unique prefix predicate;
  `aboveAnchor_of_cycleMin` and `aboveAnchor_of_minimalNonTerm`
  are thin
- `finiteProgress_of_imageLt` / `finiteProgress_of_prefix_drop`
  stay in Progress; `hasFiniteStop_of_imageLt` /
  `hasFiniteStop_of_power_bound_lt_pow` (`k=1`) sit in
  FirstPassage. `coeffStop_implies_stop` remains a wrapper of
  `power_bound_contracts`. Do not merge `HasFiniteStop` with
  `FiniteProgress`

Extracted corollaries:

| Id | Lean name | Home |
|----|-----------|------|
| A | `envelope_corridor_contradiction` | Corridor |
| B | `even_below_anchor_pow` | Corridor |
| C | `two_even_below_fourth`; cube is `two_even_below_cube` via \(n^3<n^4\) | Corridor |
| D | `aboveAnchor_not_envelope_drop` | MinimumRelative |
| E | `aboveAnchor_even_run_ge_pow` | MinimumRelative |
| F | `isolatedOddSurvival_bound` | FirstInternalOO |

Compatibility layer:

- `power_bound_from` / `power_bound_append_even` /
  `power_bound_append_odd` stay for Defect; they are thin
  wrappers of `.even` / `.odd`, not a second floor arithmetic
- Short CycleItinerary exclusions (`no_cycle_itinerary_odd` / `oo` /
  `eoo` / `ooe` / `oeo` / `oooe`, length-4/5) stay in
  `CycleCore`. The named tail (`wordOOEOOE` and after) lives in
  `CycleObstructions`
- Python `lean_api_present` string-scans. `CYCLE` kernel text is
  Core + Obstructions + Extrema. New corridor / even-run names
  are listed in `minimum_relative.LEAN_THEOREMS`
- `JugglerPaper.lean` comments do not mention `EnvelopeState`
- After the Residuals cut, consumers that used the old re-export
  take one extra import: `CycleExtrema` imports `Scale`, and
  `Escape` / `EvenCountThree` / `LandingValuation` import
  `Residuals`. Isolated CycleMin wrappers live in
  `CycleObstructions`; the CE wrapper `minimal_isolated_two`
  lives in `Minimal`. `SequentialMordell` imports `GlobalDefect`
  directly.

Research exclusions (do not reopen from this dossier):

terminal clusters, four-even cells, \(Z_5\), length-11 assemblers,
p-adic, episode-rank, generic predecessor enumeration, Cells split,
Defect / Equality / CycleExtrema proof rewrite, a giant generic
Juggler framework, new conjectures, Paper A edits, the next
termination attack.

## Open questions

None from this packaging. Do not resume an odd-lift letter chain
from an architecture note.

## Decision

**PROMOTE** the architecture as the live Juggler Lean spine.
**CLOSE** as a research attack: every new statement is a
`REPARAMETERIZATION` of existing local lemmas, and the branch
produced no new Juggler dynamics.

Best next question: none from this packaging. A later research
branch must name its own mathematical target.

## Publication assessment

Status: `STRUCTURAL`.

The six corollaries are packaging of already-proved local lemmas.
This is not a `PAPER_CANDIDATE` and not a halt theorem.
