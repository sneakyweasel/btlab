# Juggler two-sided minimal-counterexample corridor

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

On a realized stay-above prefix of a Juggler orbit, do the two-sided
envelope inequalities at a pivot \(x=T^j(n)\) constrain \(x\) beyond
the concatenated-word test \(2^{r+s}\le 3^{o+q}\)?

## Exact statement

Write \(x=T^j(n)\) and let the prefix \(n\to x\) have length \(r\)
and odd count \(o\). For a realized suffix of length \(s\) with odd
count \(q\), the exact corridor is

\[
x^{2^r}\le n^{3^o}
\qquad\text{and}\qquad
n^{2^s}\le x^{3^q}.
\]

The second inequality is available only when \(T^s(x)\ge n\). Phase 0
asks whether this pair, on first-return paths for \(2\le n\le 2000\)
together with the hard and tall starts, yields a restriction on \(x\)
that is not implied by `power_bound_word` plus stay-above. The
composition \(2^{r+s}\le 3^{o+q}\) is the concatenated-word
non-contraction test and is not counted as new.

This is not a halt theorem. A finite stay-above prefix is not a
minimal counterexample. A search-horizon miss is not a bound \(L\).
This object is not the REFUTED two-sided exponent-only law.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Finite-itinerary envelope, equality rigidity, first-defect, and
  compensated contraction — **EXACT — LEAN VERIFIED**.
- `minimal_nonterm_image_ge` — **EXACT — LEAN VERIFIED**. A
  `MinimalNonTerm` already satisfies \(T^j(n)\ge n\).
- Peak-suffix \(P^{3^q}<n^{2^s}\) on completed first returns —
  **COMPUTATIONALLY VERIFIED** on \(n=2..2000\); it never beat the
  exponent gap. Parked as `EXCURSION_ENVELOPE_GREEN`.
- Two-sided exponent-only law — **REFUTED**
  (`POWER_WORD_COUNTEREXAMPLE`). A different object.
- Escape-state margin — closed as `ESCAPE_STATE_COMPLEX`.
- Odd-odd residual scalars — closed as `ODD_ODD_RESIDUAL_COMPLEX`.
- Prefix-NC arithmetic admissibility — closed as
  `PREFIX_NC_ARITHMETIC_COMPLEX`.
- Cycle Diophantine peak identities — closed as
  `DIOPHANTIC_REPACKAGING`.

Project relationship: **extended**. The new object is a pivot
corridor on a stay-above prefix, not another local rewrite of
\(T\ge n\). Totality remains unclaimed.

## Branch budget

```text
Mathematical target     On stay-above prefixes, does a pivot corridor
                        constrain x beyond 2^{r+s} <= 3^{o+q}?
Novelty hypothesis      prefix defect or closure forces extremality
                        or a contraction the full word misses
Falsifier               every exact predicate is power_bound_word + image>=n
Existing machinery      power_bound_*, first-defect, cmp_pow,
                        minimal_nonterm_image_ge, excursion corpus
Maximum Phase-0 scope   one probe; stay-above + first-return census;
                        classify; no Lean; no engine
Promotion criterion     a pivot constraint not implied by the
                        concatenated itinerary, or a new rigidity/defect law
Stop criterion          algebraic collapse; machinery gravity; halt
                        claim; ResidualStep / CycleDiophantine / prefix-NC
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Forward \(x^{2^r}\le n^{3^o}\) — existing **EXACT — LEAN VERIFIED**
  (`power_bound_word`)
- Reverse \(n^{2^s}\le x^{3^q}\) on stay-above — existing envelope
  plus \(T^s(x)\ge n\); **COMPUTATIONALLY VERIFIED** whenever
  `cmp_pow` is available
- Compat \(2^{r+s}\le 3^{o+q}\) — **REPARAMETERIZATION** of
  contraposed `power_bound_contracts` on the concatenated word
- Mixed-word envelope equality — none in the window;
  consistent with **EXACT — LEAN VERIFIED**
  `power_bound_eq_iff_extremal`
- Reverse-without-fullword — none in the window; **OBSERVATION**
- First-defect over concatenated formal gap on stay-above —
  none in the window; **OBSERVATION**
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.corridor`
- Records: [juggler_corridor.md](../research/juggler_corridor.md),
  [juggler_corridor.json](../research/juggler_corridor.json)
- Dataset: `data/research/juggler/corridor/`
- Tests: `tests/research/juggler_sequence/test_corridor.py`
- The Research Engine control layer is not modified.
- `ResidualStep` is not extended. `CycleDiophantine` is not reopened.
- No `PowerHeight`. No corridor automaton. No Lean file.

## Conjectures

None opened.

## Counterexamples

- “The corridor is a new two-sided exponent law”: that law remains
  **REFUTED**; the corridor is a different pair of inequalities.
- “Reverse can fire on a stay-above segment while
  \(3^{o+q}\ge 2^{r+s}\)”: none in \(n=2..2000\).
- “A mixed prefix or suffix saturates”: none in the window.
- Even \(n\) has a stay-above corridor of length \(\ge 1\): none;
  even starts return by \(E\).

## Formalization

None added. Envelope, equality, compensated contraction, and
`minimal_nonterm_image_ge` already live in
`formal/Problems/Engine/FloorPower.lean` and
`formal/Problems/Engine/MinimalNonTerm.lean`. No
`Corridor.lean`. `ResidualChain.lean` is not rewritten. The
composition identity is a trivial lemma composition and is not
packaged. No `sorry`. No ledger row.

## Results

Classification **CORRIDOR_REPACKAGING**.

On \(2\le n\le 2000\), all 1999 starts return before the horizon.
The census produced 45948 corridors: 39137 stay-above and 6811
first-return suffixes. Among available exact comparisons, every
stay-above corridor satisfies forward, reverse, and compat.
Reverse never fired unless the concatenated word was formally
contracting, including at the actual return. Mixed equality and
simultaneous two-sided saturation did not occur. The 150 equality
hits are monochrome extremal prefixes, already classified by
`power_bound_eq_iff_extremal`. Closest stay-above slack is the
trivial gap \(3-2=1\) of a single odd letter. Even starts
contribute no stay-above corridor. Some comparisons are
bit-budget unavailable; those rows are not identity failures.

No Lean file. No halt theorem.

## Open questions

The missing theorem is unchanged: does every \(n\ge 2\) realize a
finite prefix with \(3^o<2^k\)? If yes, `FiniteProgress` follows
from `power_bound_contracts`. An infinite itinerary that stays
prefix-noncontracting would be a non-terminator. Do not reopen
the corridor, ResidualStep, escape-state margins, or peak
Diophantine identities.

Answered in [juggler_drift_crossing.md](juggler_drift_crossing.md):
actual prefix-NC endpoints do not form a shrinking arithmetic
class. Closed as `DRIFT_ENDPOINT_COMPLEX`.

## Decision

**CLOSE** the corridor branch as `CORRIDOR_REPACKAGING`. On
stay-above segments the two-sided inequalities are the existing
finite-itinerary envelope plus \(T^s(x)\ge n\). Their composition is
the concatenated-word test. No pivot-specific contraction,
rigidity, or descent appeared. Do not add Lean. Do not claim
termination.

Best next question: prove or refute that every \(n\ge 2\)
realizes a finite prefix with \(3^o<2^k\).

## Publication assessment

Status: `EXPLORATORY`. A negative corridor result, not a paper
candidate and not a Juggler totality result.
