# Juggler internal even-run collapse

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can large first-even contraction cells in changing families be
explained by internal even-run scale collapse, and does bounding every
even-run length restore a useful family-level bound?

## Exact statement

For a realized decomposition \(w=uE^rv\), prove

\[
T_w(x)=T_v(T_{E^r}(T_u(x))).
\]

Then prove or refute: there exists a useful \(Q(R)\) such that every
superquadratic \(v\) with \(\mathrm{maxEvenRun}(v)\le R\) satisfies
\(T_v(q)\ge(q+1)^2\) for all realized \(q\ge Q(R)\).

“Useful” means a bound that stays comparable to the exact short-word
thresholds, not a tower in \(R\) or a nest of even-preimages.

Do not reopen the false \(\varepsilon\)-only theorem. Do not replace
the fixed-itinerary lower-growth theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Initial-run normalization \(T_{E^ru}(a^{2^r})=T_u(a)\) —
  **EXACT — LEAN VERIFIED**.
- Initial even-run length is not a family bound —
  **EXACT — LEAN VERIFIED** (`q=7`).

Project relationship: **extended**. Internal runs are the same residual
evaluation. Syntactic `maxEvenRun` fails as a useful family bound.

## Branch budget

```text
Mathematical target     Does bounding internal even runs restore a family bound?
Novelty hypothesis      Numeric collapse to a small basin is the obstruction
Falsifier               maxEvenRun ≤ R with arbitrarily large contracting q
Existing machinery      image_append, collapse_on_pow_two, odd_even_tower_seven
Maximum Phase-0 scope   Run census; nested R=3 family; Lean residual identity
Promotion criterion     A residual-run identity and a decide on bounded R
Stop criterion          Collapse trees; residual automaton; PowerHeight;
                        halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Medial identity \(T_{uE^rv}(x)=T_v(T_{E^r}(T_u(x)))\) —
  **EXACT — LEAN VERIFIED**
- Inert basin: \(T_{O^s}(1)=1\) — **EXACT — LEAN VERIFIED**
- `maxEvenRun` — **EXACT — LEAN VERIFIED** (definition)
- Bounded `maxEvenRun` gives a useful \(Q(R)\) — **REFUTED**
- Nested witness \(q=2500\), `maxEvenRun=3`, lands on \(1\) —
  **EXACT — LEAN VERIFIED**
- Further nests \(q=6250000\) and a 121-bit \(q\) —
  **COMPUTATIONALLY VERIFIED**
- The only short superquadratic contraction with \(T>1\) is `OO` at
  \(q=3\), \(T=11\) — **COMPUTATIONALLY VERIFIED**
- Collapse algebra / residual automaton — not added
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.internal_collapse`
- Records: [juggler_internal_collapse.md](../research/juggler_internal_collapse.md),
  [juggler_internal_collapse.json](../research/juggler_internal_collapse.json)
- Tests: `tests/research/juggler_sequence/test_internal_collapse.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened. Whether \(Q(R)\) exists as an enormous tower in \(R\) is
left unclaimed.

## Counterexamples

The nested family with \(\mathrm{maxEvenRun}=3\):

| word | \(q\) | \(T\) |
|------|-------|-------|
| `OEEE` + `O^9` | 7 | 1 |
| `EE` + `OEEE` + `O^{12}` | 2500 | 1 |
| `EEE` + `OEEE` + `O^{12}` | 6250000 | 1 |
| `(E^3 O)^3` + `O^{16}` | 121-bit | 1 |

Each extra even run before an odd letter that feeds the basin of `1`
lifts \(q\) by about a \(2^r\)-power. All four words are
superquadratic. The first two are Lean-certified; the last two are
exact integer checks.

On short words, `maxEvenRun=0,1,2` only produced \(q_{\max}\in\{3,2,8\}\).
Those small values are not a family theorem: they fail as soon as a
second even run is stacked in front of `OEEE`.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `maxEvenRun` / `internal_even_collapse` / `collapse_basin_one`
- `wordEE_OEEE12` / `nested_even_collapse_2500` /
  `nested_even_collapse_2500_superquadratic`

Unchanged: `LowerPowerBound`, `eventually_no_first_even_contraction`,
`changing_suffix_unbounded_contraction`, `collapse_on_pow_two`,
`first_even_freeze`, `power_bound_compensated_contracts`. No `sorry`.
No residual automaton. No `PowerHeight`.

## Results

Classification **BOUNDED_RUN_COUNTEREXAMPLE**, with mechanism
**COLLAPSE_COMPRESSION_GREEN**.

Internal even runs are residual evaluation at the exit state. The
inert residual is \(1\) under an odd tail. Large changing-family
contraction cells on the scanned domain are collapse-to-\(1\) events;
the only short \(T>1\) case is the exact `OO` cell at \(q=3\).

Bounding the *length* of every even run does not restore a useful
family threshold. The numerical quantity is the entry/exit ratio of a
run that lands in the basin of \(1\).

This is not a termination theorem. It does not claim that \(Q(R)\) is
infinite, only that it cannot be a small function of \(R\).

## Open questions

The large collapse witnesses are capture into \(\{1\}\); see
[juggler_capture_certificates.md](juggler_capture_certificates.md).
What remains is the structure of a hypothetical path that avoids both
descent and capture.

## Decision

**PROMOTE** the internal-run residual identity and the nested
`maxEvenRun=3` family as a refutation of useful bounded-run
uniformity. `BOUNDED_RUN_COUNTEREXAMPLE`. Keep the fixed-itinerary theorem.
Do not add a collapse tree or residual automaton. Do not claim
termination.

Best next question: must every large superquadratic first-even
contraction contain an even run that lands in an inert basin with
unbounded entry/exit ratio?

## Publication assessment

Status: `EXPLORATORY`. A local collapse mechanism and a family
obstruction, not a paper candidate and not a Juggler totality result.
