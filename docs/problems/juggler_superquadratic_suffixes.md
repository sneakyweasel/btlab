# Juggler superquadratic suffixes

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

For each fixed suffix \(v\) with formal exponent \(\alpha_v>2\), is the
first-even contraction set \(Q_v\) finite?

## Exact statement

Write \(\alpha_v=3^{\#O(v)}/2^{|v|}\). The itinerary \(Ev\) is formally
expanding iff \(\alpha_v>2\), i.e. \(3^{\#O(v)}>2^{|v|+1}\). Prove or
refute: for every such fixed \(v\) there exists \(Q_0(v)\) such that

\[
q\ge Q_0(v)\ \text{and}\ \mathrm{follows}(q,v)
\Longrightarrow
T_v(q)\ge(q+1)^2.
\]

The one-sided power envelope cannot prove this, because it is an upper
bound. The threshold may depend on \(v\). This is not a uniform-in-\(v\)
statement and not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Upper envelope \(T_w(n)^{2^k}\le n^{3^o}\) —
  **EXACT — LEAN VERIFIED**.
- Exact short thresholds \(Q_{OO}=\{1,3\}\), \(Q_{OOO}=\{1\}\) —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The short thresholds remain; a
coarse lower-growth argument covers every fixed superquadratic word.

## Branch budget

```text
Mathematical target     For each fixed v with α_v>2, is Q_v finite?
Novelty hypothesis      Coarse 4T^2 bounds compose, then the gap
                        3^o > 2^{r+1} beats (q+1)^2
Falsifier               A fixed superquadratic v with arbitrarily
                        large contracting q
Existing machinery      first_even_freeze, PowerBound (upper only),
                        oo/ooo_suffix_threshold
Maximum Phase-0 scope   Computational falsifier; LowerPowerBound;
                        eventually_no_first_even_contraction
Promotion criterion     FIRST_E_EVENTUAL_NONCONTRACTION_GREEN
Stop criterion          Generic lower-envelope theory; real α_v;
                        uniform-in-v bound; PowerHeight; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(n<4\cdot n.\mathrm{sqrt}^2\) for \(n\ge1\) —
  **EXACT — LEAN VERIFIED**
- `LowerPowerBound`: \(q^{3^o}\le D_v T_v(q)^{2^r}\) —
  **EXACT — LEAN VERIFIED**
- Eventual non-contraction for each fixed superquadratic \(v\) —
  **EXACT — LEAN VERIFIED**
- No finite itinerary has \(\alpha_v=2\) —
  **EXACT — LEAN VERIFIED**
- Exact \(Q_{OO}\), \(Q_{OOO}\) classifications — retained
- Uniform threshold over all superquadratic \(v\) — not claimed
- Generic lower-envelope structure — not added
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.superquadratic_suffixes`
- Records: [juggler_superquadratic_suffixes.md](../research/juggler_superquadratic_suffixes.md),
  [juggler_superquadratic_suffixes.json](../research/juggler_superquadratic_suffixes.json)
- Tests: `tests/research/juggler_sequence/test_superquadratic_suffixes.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None found. Scanned superquadratic itineraries of length \(\le5\) have
\(Q_v\subseteq\{1,2,3\}\).

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `LowerPowerBound` / `lowerDenom` / `lower_growth_word`
- `four_mul_floorPower_even_sq` / `four_mul_floorPower_odd_sq`
- `eventually_no_first_even_contraction`
- `alpha_ne_two`
- `oo_lower_growth_eventual`

Unchanged: `PowerBound`, `oo_suffix_threshold`,
`ooo_suffix_threshold`, `first_even_freeze`,
`power_bound_compensated_contracts`. No `sorry`. No ledger row. No
cell tree. No `PowerHeight`.

## Results

Classification **FIRST_E_EVENTUAL_NONCONTRACTION_GREEN**.

For every fixed suffix \(v\) with \(3^{\#O(v)}>2^{|v|+1}\),

\[
q^{3^o}\le D_v\,T_v(q)^{2^r}
\]

and therefore \(T_v(q)\ge(q+1)^2\) for all sufficiently large realized
\(q\). The constant \(D_v\) and the threshold \(Q_0(v)\) depend on
\(v\). The existing exact bounds for `OO` and `OOO` remain sharper.

No finite itinerary satisfies \(\alpha_v=2\), because \(3^o\) is odd and
\(2^{r+1}\) is even.

This is not a termination theorem. It does not rule out infinite
families that change the suffix.

## Open questions

Answered in [juggler_uniform_thresholds.md](juggler_uniform_thresholds.md):
a uniform \(Q(\varepsilon)\) does not exist. The even-tower family
\(E^kO^{3k}\) produces arbitrarily large first-even contraction cells.

## Decision

**PROMOTE** the fixed-itinerary lower-growth theorem and the eventual
non-contraction corollary `FIRST_E_EVENTUAL_NONCONTRACTION_GREEN`.
Keep the exact short-word classifications. Do not open a generic
lower-envelope theory. Do not claim a uniform-in-\(v\) bound. Do not
claim termination.

Best next question: can changing superquadratic suffixes still produce
infinitely many first-even contraction cells, or is there a uniform
threshold for \(\alpha_v\ge 2+\varepsilon\)?

## Publication assessment

Status: `EXPLORATORY`. A local fixed-itinerary threshold theorem, not a
paper candidate and not a Juggler totality result.
