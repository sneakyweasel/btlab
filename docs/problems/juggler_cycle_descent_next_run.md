# Juggler cheap-band descent next-run type

Status: **ARCHIVED**

Refinement of
[juggler_cycle_finance.md](juggler_cycle_finance.md) and
[juggler_cycle_valley_coupling.md](juggler_cycle_valley_coupling.md),
not a new paper. After return-cost coupling closed, this phase asks
the remaining local slogan of the Section 5 program: whether a
descending even run onto the cheap band \([n,19n]\) is forbidden
from starting \(a=2\). Not a halt theorem, not a leftover-itinerary
census, not a floor raise, and not a reopen of
\((5,3)\) envelope accounting.

## Problem

Theorem 4.7 still charges \(N_{\mathrm{cheap}}=o-e\) valleys near
\(n\). A lift of those valleys to \(19n\), or a proof that
\(N_{\mathrm{cheap}}=O(1)\), would kill \(L=25781\) at floor
\(10^6\). Does CycleMin geometry force every cheap-band descent
to start \(a=1\) (`OE`, already priced at \(n^{4/3}\))?

## Exact statement

Write \(n=10^6+1\) and the cheap band \([n,19n]\).

**One-even descent (COMPUTATIONALLY VERIFIED).**
The first \(a=2\) start \(p=1000057\) lies in the band. Its
even-cell peak \(p^2=1000114003249\) satisfies \(p^2\ge n^2\).
One even step lands at \(p\) with \(a(p)=2\).

**Post-`OOE` descent (COMPUTATIONALLY VERIFIED).**
On \([n,n+20000)\) there are \(2448\) starts with \(a=2\).
Of those, \(1210\) have `OOE` landing in the cheap band
(\(1238\) first landings are even and then even-iterate).
Next-run counts on those landings:

\[
a=1:631,\quad a=2:297,\quad a=3:120,\quad a\ge 4:162.
\]

The first pair is
\(1000057\xrightarrow{\mathrm{OOE}}5623773\) with
\(a(5623773)=2\) and peak \(31626832356906\ge n^2\).
The landing sits at scale \(n^{9/8}\approx 5.6n\), inside
the band that would have to be forbidden.

**Named \(6187\) descent (COMPUTATIONALLY VERIFIED /
not a falsifier).**
The ordered-excursion path \(11189\xrightarrow{Q}1087
\xrightarrow{Q}189\) is real, both landings have \(a=1\),
and both sit below \(6187\). It is an open-orbit drop, not
a `CycleMin` cheap-band return.

**Leftover-killer (REFUTED).**
Descent onto \([n,19n]\) can start \(a=2\). The coupling
that would force \(N_{\mathrm{cheap}}=O(1)\) is false.

No cycle of any length — not claimed.

## Current literature

- Run-type packing, \(N_{\mathrm{cheap}}=o-e\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md));
  cyclic adjacency leftover-killer **REFUTED**
- Return-cost coupling, \((5,3)\) descent, \(O^{53}E^{31}\) —
  **CLOSE**
  ([juggler_cycle_valley_coupling.md](juggler_cycle_valley_coupling.md));
  leftover-killer **REFUTED**
- Ordered pairs: \((2,2)\) and \((2,2,2)\) near \(n\) —
  **COMPUTATIONALLY VERIFIED** /
  leftover-killer **REFUTED**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- `cycleMin_even_ge_sq` —
  **EXACT — LEAN VERIFIED**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-killer; the
post-`OOE` pair is the existing \((2,2)\) geometry, now
measured against the \(19n\) finance lift.

## Branch budget

```text
Mathematical target     After a descending even-run landing p in
                        [n, 19n], is a(p)=2 possible on a CycleMin,
                        or only a=1?
Novelty hypothesis      Near-n a=2 starts exist only inside the
                        initial climb from the global min; descents
                        land as OE. Then N_cheap = O(1), not o-e.
Falsifier               A CycleMin-legal descent from a peak ≥ n^2
                        onto an odd p in [n, 19n] with a(p)=2
Existing machinery      F_a, even cell, oe_start_min,
                        ordered_excursion (2,2) census,
                        valley_coupling CLOSE
Maximum Phase-0 scope   One-even witness; post-OOE census on
                        [n, n+20000); 6187 Q-path. No Lean,
                        no leftover slogan until N_cheap moves
Promotion criterion     A reusable law: descent onto the cheap
                        band forces a=1, dropping 25781
Stop criterion          a=2 after descent occurs, or the law is
                        the even cell / OOE envelope again
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Cheap band \([n,19n]\) —
  **OBSERVATION**; the factor-\(23\) lift at \(L=25781\)
- One-even descent from \(p^2\) —
  **REPARAMETERIZATION** of the even cell
- Post-`OOE` landing in the band with \(a=2\) —
  **COMPUTATIONALLY VERIFIED**; existing \((2,2)\)
- \(6187\) Q-descent —
  **COMPUTATIONALLY VERIFIED**; not `CycleMin`
- Leftover-killer —
  **REFUTED** (`juggler_cycle_descent_next_run`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_descent_next_run`
- Dataset: `data/research/juggler/cycle_finance/descent_next_run/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_descent_next_run.py`
- Window: \(n=10^6+1\); `OOE` starts on \([n,n+20000)\);
  spotlight \(6187\). Fast suite does not rerun the window.
  No CLI. No Lean.

## Conjectures

`juggler_cycle_descent_next_run` — **REFUTED**.

## Counterexamples

- \(p=1000057\), peak \(p^2\ge n^2\), \(a(p)=2\). One-even
  falsifier.
- \(1000057\xrightarrow{\mathrm{OOE}}5623773\),
  \(a(5623773)=2\), \(5623773\in[n,19n]\). Post-`OOE`
  falsifier. \(297\) further witnesses in the window.

## Formalization

None. No `CycleDescentNextRun.lean`. Paper A is unchanged.
Do not formalize the census.

## Results

- **One-even \(a=2\)** — **COMPUTATIONALLY VERIFIED**.
- **Post-`OOE` \(a=2\)** — **COMPUTATIONALLY VERIFIED**
  (`descent_next_run/summary.json`): \(297/1210\) cheap-band
  landings start \(a=2\).
- **No leftover dies.** \(N_{\mathrm{cheap}}=o-e\) remains
  admissible. The factor-\(23\) gap at \(L=25781\) is
  unchanged.

## Open questions

None from next-run type after a cheap-band descent. A global
cluster count that is not this local law is the closed
return-cost branch. A relative tax on \(\Delta\) is not opened.

## Decision

**CLOSE**. A descent onto \([n,19n]\) can start \(a=2\). The
one-even witness is the even cell. The post-`OOE` witness is
the existing \((2,2)\) pair, now checked against the finance
lift \(19n\). The \(6187\) path is an open-orbit drop and is
not a `CycleMin` return. No Paper A edit, no ledger row, no
Lean.

Best next question: none from cheap-band next-run type. The
Section 5 program stays **PARK**.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on the
Section 5 program; not a second manuscript and not a
Paper A edit.
