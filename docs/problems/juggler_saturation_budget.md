# Juggler exact perfect-power dynamics and saturation budget

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

How much 2-adic perfect-power structure must a starting value possess
to sustain exact equality in the finite-itinerary floor-power envelope for
\(k\) consecutive steps?

## Exact statement

Write \(HasPowTwoDepth(n,r)\) for \(\exists a,\ n=a^{2^r}\). If a
realized itinerary \(w\) of length \(k\) attains

\[
T_w(n)^{2^{k}}=n^{3^{\#O(w)}},
\]

does \(HasPowTwoDepth(n,k)\) hold? Equivalently: does each exact
branch consume one factor of \(2\) from the perfect-power exponent?

This is a local arithmetic question. It is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Phase-14 (`juggler_power_composition`): one-sided envelope
  **EXACT — LEAN VERIFIED**.
- Phase-16 (`juggler_power_algebra`): equality rigidity
  **EXACT — LEAN VERIFIED**. Mixed-word strictness remains
  **REFUTED**. **extended** here by asking for the 2-adic budget of
  exact saturation.

## Branch budget

```text
Mathematical target     Does k consecutive exact envelope branches require
                        the start to be a 2^k-th power?
Novelty hypothesis      Each exact E/O step consumes one unit of 2-adic
                        perfect-power depth; equality cannot persist for
                        arbitrary length without arbitrarily deep 2-powers.
Falsifier               POWER_TWO_DEPTH_COUNTEREXAMPLE: a saturated word of
                        length k from a state whose repeated-square depth
                        is < k.
Existing machinery      PowerBoundEq, power_bound_eq_implies_square,
                        floorPower_of_even_sq / floorPower_of_odd_sq,
                        isSquare_pow_three_iff.
Maximum Phase-0 scope   Exact a^(2^r) transitions; HasPowTwoDepth drop
                        lemmas; budget theorem if it holds; square-depth
                        probe without cmp_pow or PowerHeight.
Promotion criterion     Lean proves the depth-drop rules and either the
                        budget theorem or a minimized counterexample.
Stop criterion          A PowerHeight hierarchy; an equality-itinerary census;
                        a termination claim; engine control edits.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exact even transition \(a^{2^r}\mapsto a^{2^{r-1}}\) —
  **EXACT — LEAN VERIFIED**
- Exact odd transition \(a^{2^r}\mapsto a^{3\cdot 2^{r-1}}\) —
  **EXACT — LEAN VERIFIED**
- \(HasPowTwoDepth(n,r)\) drops by one on each exact branch —
  **EXACT — LEAN VERIFIED**
- Envelope equality of length \(k\) implies \(HasPowTwoDepth(n,k)\) —
  **EXACT — LEAN VERIFIED**
- `PowerHeight` / equality-itinerary census — not added

## Experiments

- Probe: `research.juggler_sequence.saturation_budget`
- Equality via local tightness and repeated `isqrt` depth; no `cmp_pow`
  on \(n^{3^o}\)
- Records: [juggler_saturation_budget.md](../research/juggler_saturation_budget.md),
  [juggler_saturation_budget.json](../research/juggler_saturation_budget.json)
- Tests: `tests/research/juggler_sequence/test_saturation_budget.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened. The budget is a theorem. A classification of all equality
words remains out of scope.

## Counterexamples

- Mixed-word strictness remains refuted at word `O`, \(n=9\).
- No `POWER_TWO_DEPTH_COUNTEREXAMPLE` on the searched domain.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `HasPowTwoDepth`
- `floorPower_of_pow_two_depth_even`
- `floorPower_of_pow_two_depth_odd`
- `hasPowTwoDepth_even_exact`
- `hasPowTwoDepth_odd_exact`
- `hasPowTwoDepth_of_cube`
- `hasPowTwoDepth_ge_two_image_square`
- `localsTight_implies_power_bound_eq`
- `power_bound_eq_implies_pow_two_depth`
- `power_bound_eq_contracts_pow_two_lb`

No `PowerHeight`. No `sorry`. No ledger row. Existing `PowerBound` and
contraction theorems are unchanged.

## Results

Classification **SATURATION_BUDGET_GREEN**, depth status
**POWER_TWO_DEPTH_GREEN**.

Each exact branch consumes one unit of 2-adic perfect-power depth.
A realized equality itinerary of length \(k\) forces the start to be a
\(2^k\)-th power. For \(n\ge 2\) this implies \(2^{2^k}\le n\).
All-even equality is formally contracting and meets that lower bound
at the towers \(2^{2^k}\). Exact steps preserve parity, so mixed itineraries
cannot saturate.

Computational search (\(n\le 10^4\), depth 8; prescribed words to
length 6; square towers with bases \(2..30\) and depth \(\le 4\)):
0 `POWER_TWO_DEPTH_COUNTEREXAMPLE`, 99 saturating starts, 0 mixed
saturations, 6 prescribed words realized in bound (`E`, `O`, `EE`,
`OO`, `EEE`, `OOO`). This is not a termination theorem.

## Open questions

How do the induced exponent maps \(e\mapsto e/2\) and \(e\mapsto 3e/2\)
constrain which words can saturate, once every pre-branch exponent is
required to stay even? Do not census equality words in this phase.

## Decision

**PROMOTE** the exact perfect-power transitions and the finite
saturation-budget theorem. Record `SATURATION_BUDGET_GREEN`. Do not
register an attack. Do not claim termination.

Best next question: which words can appear as traces of the even
exponent maps \(e\mapsto e/2\) and \(e\mapsto 3e/2\)?

## Publication assessment

Status: `EXPLORATORY`. A local exact budget lemma, not a paper
candidate and not a Juggler totality result.
