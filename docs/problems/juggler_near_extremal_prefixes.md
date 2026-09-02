# Juggler near-extremal non-contracting prefixes

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can a realized non-monochrome prefix stay on the non-contracting side
of the finite-itinerary exponent test, with accumulated defect too small
to force contraction, for arbitrarily long prefixes?

## Exact statement

For a realized itinerary \(w\) of length \(k\) with \(o=\#O(w)\), write

\[
G(w)=2^k-3^o,\qquad
\Delta_w(n)=n^{3^o}-T_w(n)^{2^k}.
\]

A prefix is *prefix-noncontracting* when every initial segment has
\(G_j\le 0\). Restrict to non-monochrome prefixes. Does

\[
\Delta_w(n)>n^{3^o}-n^{2^k}
\]

ever hold on that set, and are the realized lengths bounded?

This is a finite-prefix question. It is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Weak envelope and formal contraction \(3^o<2^k\Rightarrow T_w(n)<n\)
  — **EXACT — LEAN VERIFIED**.
- Defect-compensated contraction
  \(\Delta>n^{3^o}-n^{2^k}\Rightarrow T_w(n)<n\) —
  **EXACT — LEAN VERIFIED** (`juggler_compensated_contraction`).
- \(2^{a+1}\le 3^a\) iff \(a\ge 2\) —
  **EXACT — LEAN VERIFIED** (`two_pow_succ_le_three_pow_iff`).
- Equality only on monochrome extremals —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The new object is a prefix with
every \(G_j\le 0\), not a single mixed block such as `EOO`.

## Branch budget

```text
Mathematical target     realized non-extremal prefixes with G≤0
                        and Δ too small to force T^k(n)<n
Novelty hypothesis      a language obstruction or a defect bound
Falsifier               NEAR_EXTREMAL_COUNTEREXAMPLE / BAD_PREFIX_ARBITRARY
Existing machinery      PowerBound, compensated contraction, O^a E
Maximum Phase-0 scope   combinatorial prefix-NC tree; realized scan
Promotion criterion     DEFECT_DRIVEN_CONTRACTION_GREEN on this set,
                        or BAD_PREFIX_BOUNDED_GREEN
Stop criterion          machinery gravity; Control-layer edits;
                        termination claim; PowerHeight
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exponent gap \(G=2^k-3^o\) — exact integer
- Prefix-noncontracting itineraries start with \(O\); length \(\ge 2\)
  starts with \(OO\) — **OBSERVATION**, follows from \(G(E)=1\) and
  \(G(OE)=1\)
- Mixed family \(O^k E\) for \(k\ge 2\) is prefix-NC —
  **EXACT — LEAN VERIFIED** as \(2^{k+1}\le 3^k\)
- Other mixed prefix-NC patterns (`OOEO`, `OOOOEOOOEE`, …) —
  **OBSERVATION**
- Defect-driven contraction on this set — did not fire in range;
  the implication itself remains **EXACT — LEAN VERIFIED**
- `PowerHeight` — not added
- `DefectContracts` structure — not added

## Experiments

- Probe: `research.juggler_sequence.near_extremal_prefixes`
- Records: [juggler_near_extremal_prefixes.md](../research/juggler_near_extremal_prefixes.md),
  [juggler_near_extremal_prefixes.json](../research/juggler_near_extremal_prefixes.json)
- Tests: `tests/research/juggler_sequence/test_near_extremal_prefixes.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- `EOO` is not a prefix-noncontracting itinerary: \(\tau=1\). Compensated
  contraction of the *block* `EOO` is a different object.
- `n=3` realizes `OOOE`, not `OOE`. Image \(6>3\).
- Realized mixed prefix-NC itineraries of length \(10\) expand
  (`n=37`, `OOOOEOOOEE`; `n=173`, `OOEOOOOOOO`). A horizon hit is
  not an infinite family.

## Formalization

No new Lean. Reused:

- `power_bound_contracts`
- `power_bound_compensated_contracts`
- `two_pow_succ_le_three_pow_iff`
- `power_bound_eq_iff_extremal`

No `sorry`. No ledger row: the new statements are the combinatorial
language and a finite scan, not the English claim that bad prefixes
are bounded.

## Results

Classification **NEAR_EXTREMAL_STRUCTURE_GREEN**. Decision **PARK**.

The prefix-NC language is nonempty, starts odd, and is strictly
larger than \(\{O^k\}\cup\{O^k E:k\ge 2\}\). On
\(2\le n\le 2000\) and \(k\le 10\) there were \(1541\) mixed
prefix-NC rows, \(0\) defect-driven certificates, and mixed itineraries
that remain prefix-NC through the horizon while expanding. Closest
computed \(\Delta\) versus \(n^{3^o}-n^{2^k}\) occurs on short
`OOE` starts and is still far below the formal gap.

This is not `BAD_PREFIX_BOUNDED_GREEN` and not a halt theorem.

## Open questions

Answered in
[juggler_prefix_nc_admissibility.md](juggler_prefix_nc_admissibility.md)
as arithmetic pullback: the constraints are the existing floor
cells, and every mixed prefix-NC itinerary of length \(\le 8\) is
realized. An explicit infinite family, or a defect that exceeds
the formal gap, remains open and is not started there.

## Decision

**PARK**. Record the prefix-NC language and the scan. Do not claim
that horizon-length examples are an infinite family. Do not add a
second compensated-contraction lemma. Do not start a global
automaton. Do not claim termination.

Best next question: answered in
[juggler_prefix_nc_admissibility.md](juggler_prefix_nc_admissibility.md).

## Publication assessment

Status: `EXPLORATORY`. A prefix-language census plus a finite scan,
not a paper candidate and not a Juggler totality result.
