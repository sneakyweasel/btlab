# Juggler collapse normalization

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can a finite itinerary be split into an initial even-run collapse and a
residual suffix, and does a bound on that initial run restore
family-level first-even non-contraction?

## Exact statement

Prove the normalization

\[
T_{E^r u}(a^{2^r})=T_u(a)
\]

for even \(a\) that realize \(u\), and the decomposition
\(v=E^{r(v)}u(v)\) with \(u(v)\) empty or odd-starting.

Then prove or refute: there exists \(Q(R)\) such that every
superquadratic \(v\) with initial even-run length \(\le R\) satisfies
\(T_v(q)\ge(q+1)^2\) for all realized \(q\ge Q(R)\).

Do not reopen the false \(\varepsilon\)-only theorem. Do not replace
the fixed-itinerary lower-growth theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Fixed-word eventual non-contraction — **EXACT — LEAN VERIFIED**.
- Changing family \(E^kO^{3k}\) at \(q=2^{2^{k-1}}\) —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The changing-suffix counterexample
is rewritten as residual evaluation at \(1\). Bounded initial even-run
is refuted as a family bound.

## Branch budget

```text
Mathematical target     T_{E^r u}(a^{2^r})=T_u(a); does bounded r restore Q?
Novelty hypothesis      Collapse depth is the missing changing-family variable
Falsifier               Bounded initial even-run with unbounded contracting q
Existing machinery      floorPower_iterate_even_pow_two_eq, image_append,
                        even_tower_to_one
Maximum Phase-0 scope   Decomposition; residual identity; bounded-r scan;
                        one internal-collapse witness
Promotion criterion     Clean normalization and a decide on bounded r
Stop criterion          Collapse algebra; PowerHeight; lower-envelope;
                        halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(T_{E^r}(a^{2^r})=a\) for even \(a\) — **EXACT — LEAN VERIFIED**
- \(v=E^{r(v)}u(v)\) — **EXACT — LEAN VERIFIED**
- \(T_{E^r u}(q)=T_u(T_{E^r}(q))\) — **EXACT — LEAN VERIFIED**
- Exact-tower contraction iff \(T_u(a)+1<(a^{2^r}+1)^2\) —
  **EXACT — LEAN VERIFIED**
- \(E^kO^{3k}\) at \(q_k=2^{2^{k-1}}\) is \(O^{3k}\) on residual \(1\) —
  **EXACT — LEAN VERIFIED**
- Bounded initial even-run restores \(Q(R)\) — **REFUTED**
- \(q=7\) follows `OEEE` plus nine odds, lands on \(1\) —
  **EXACT — LEAN VERIFIED**
- Longest even run anywhere, as the extra scale parameter —
  **OBSERVATION**
- Generic collapse algebra — not added
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.collapse_normalization`
- Records: [juggler_collapse_normalization.md](../research/juggler_collapse_normalization.md),
  [juggler_collapse_normalization.json](../research/juggler_collapse_normalization.json)
- Tests: `tests/research/juggler_sequence/test_collapse_normalization.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

Initial even-run length \(0\) is not a bound. The itineraries

\[
v_k=OE^kO^{3k}
\]

are superquadratic and start with `O`. Odd starts whose odd-image
falls into the even basin of \(1\) then stay at \(1\):

- \(k=3\), \(q=7\), \(7\to18\to4\to2\to1\) — **EXACT — LEAN VERIFIED**
- \(k=4\), \(q\le345\) on the scan — **COMPUTATIONALLY VERIFIED**
- \(k=5\), \(q\le19955\) on the scan — **COMPUTATIONALLY VERIFIED**

Scanned \(q_{\max}\) grows with the *internal* even-run length \(k\),
not with the initial even-run length.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `initialEvenRun` / `stripInitialEven` / `initial_even_decomposition`
- `iterate_even_pow_two_eq` (alias)
- `collapse_residual_identity` / `collapse_on_pow_two` /
  `collapse_tower_contracts_iff`
- `even_tower_collapse_residual` / `odd_then_even_collapse`
- `wordOEEE9` / `odd_even_tower_seven`

Unchanged: `LowerPowerBound`, `eventually_no_first_even_contraction`,
`changing_suffix_unbounded_contraction`, `first_even_freeze`,
`power_bound_compensated_contracts`. No `sorry`. No
`bounded_collapse_eventual_noncontraction`. No `PowerHeight`.

## Results

Classification **COLLAPSE_DEPTH_TOO_WEAK**, with the normalization
layer **COLLAPSE_NORMALIZATION_GREEN**.

\[
T_{E^r u}(a^{2^r})=T_u(a)
\]

holds, and first-even contraction on that exact tower cell is
\(T_u(a)+1<(a^{2^r}+1)^2\). The changing family \(E^kO^{3k}\) is the
case \(a\)-after-collapse \(=1\).

A bound on the *initial* even-run length does not restore a family
threshold. The additional scale information is the longest even run
anywhere in the itinerary, together with the residual state after that run.

This is not a termination theorem. It does not claim that a bound on
the longest even run is sufficient; that is the next question.

## Open questions

Answered in [juggler_internal_collapse.md](juggler_internal_collapse.md):
a bound on the longest even run is not a useful family threshold.
Nested `E^3 O` blocks with `maxEvenRun=3` still collapse onto \(1\) at
\(q=2500\) and larger.

## Decision

**PROMOTE** the collapse residual identity and the refutation of
initial even-run as a sufficient collapse complexity.
`COLLAPSE_DEPTH_TOO_WEAK`. Keep the fixed-itinerary theorem and the
\(E^kO^{3k}\) family. Do not add a collapse algebra. Do not claim
termination.

Best next question: does a bound on the longest even run restore
family-level first-even non-contraction for superquadratic suffixes?

## Publication assessment

Status: `EXPLORATORY`. A local normalization and a family obstruction,
not a paper candidate and not a Juggler totality result.
