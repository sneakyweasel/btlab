# Juggler finance-extremal word versus exact terminal cells

Status: **ARCHIVED**

Refinement of
[juggler_cycle_almost_search.md](juggler_cycle_almost_search.md) and
[juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md),
not a new paper. After the \(L=25781\) almost-cycle search closed,
this phase asks whether the early empty-`OOE` failure of the
canonical finance-optimal word is a hybrid theorem

\[
\text{finance extremality}\;\Rightarrow\;\text{exact-cell incompatibility}
\]

that can be stated without the \(25781\)-letter string.
Not a halt theorem, not Phase 2 at \(L=55293\), and not a
floor raise.

## Problem

The finance-optimal word is uniquely determined and is not a
long realized itinerary. Does its ordered `OOE`/`OE` structure
force an empty exact predecessor cell for a reason that is not
the existing \(F_2\) envelope or the known \((2,2,1)\) comparison
\(243<256\)?

## Exact statement

**Three constructions coincide (COMPUTATIONALLY VERIFIED /
KNOWN mechanical combinatorics).**
On the record leftovers \(L\in\{19,84,1054,25781\}\) the
extremal path \(o_k=r(k)\), the ceiling Christoffel word of
slope \(o_{\min}/L\), and the packed `OOE`/`OE` Beatty word
are the same string. `OE` is isolated (Sturmian majority
`OOE`). The itinerary ends `OOE OE`. This is Beatty plus the
standard `OOE`/`OE` Sturmian morphism, not a new cycle law.

**Last circuit cannot be `OOE` (COMPUTATIONALLY VERIFIED).**
On every \(a=2\) start in \([3,20000]\), \(F_2(v)>v\). A
`CycleMin` landing at \(n\) therefore cannot have last circuit
`OOE`. Combined with isolated `OE`, the terminal pair of a
two-type finance-optimal word is forced to be \((2,1)\). The
suffix of \(L=25781\) is in fact `AAB` \(=\) `(2,2,1)` from
the end.

**Terminal \((2,1)\) is not empty (COMPUTATIONALLY VERIFIED).**
At \(n=10^6+1\), \(u=12915515\xrightarrow{\mathrm{OOE}}
v=100000159\xrightarrow{\mathrm{OE}}n\). In a stride-\(20\)
sample near the floor, \(19/41\) of the \(n\) with an `OE`
preimage also have a \((2,1)\) preimage; near \(2\cdot10^6\)
the rate is \(16/41\). The hoped empty-`OOE` law is false.

**Follow death is not mechanical-specific (COMPUTATIONALLY
VERIFIED).**
The canonical word and the bunched `OOE`\(\cdots\)`OE` word
share the prefix `OOEOOEOOE` and have identical follow
statistics on \([10^6+1,10^6+2001]\) (max \(6\), mean
\(2.02\)). Failure occurs inside the shared `OOE` prefix,
before the first mechanical `OE` insertion.

**Terminal \((2,2,1)\) (OBSERVATION / REPARAMETERIZATION).**
No \((2,2,1)\) preimage of \(n\) appeared in either sample
(\(0/19\) and \(0/16\)). That is the dual of the existing
two-block persistence \(243<256\): a landing at \(n\) needs
\(u_0^{243}\ge n^{256}\), and the envelope is tight. Not a
new cell.

No cycle of any length — not claimed.

## Current literature

- Almost-cycle search, empty `OOE` after \(\le 2\) blocks —
  **CLOSE**
  ([juggler_cycle_almost_search.md](juggler_cycle_almost_search.md))
- `OOE` cell \(w^8\le v^9\); \((2,1)\) at a CycleMin start;
  two-block persistence \(243<256\) —
  **EXACT — HUMAN PROOF** /
  leftover-killer **REFUTED**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Extremal path and ceiling Christoffel are both
  prefix-admissible —
  **EXACT — HUMAN PROOF** /
  leftover-killer **REFUTED**
  ([juggler_cycle_prefix_feasibility.md](juggler_cycle_prefix_feasibility.md))
- Run-type packing, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a hybrid leftover-killer;
the three-word collapse is **KNOWN** mechanical combinatorics;
empty \((2,2,1)\) is the existing \(243<256\).

## Branch budget

```text
Mathematical target     Can the early empty-OOE failure of the
                        L=25781 finance-optimal word be stated
                        without the 25781-letter string, as
                        finance-extremality => exact-cell empty?
Novelty hypothesis      The collapse extremal=Christoffel=packed
                        plus last blocks (2,1) into the CycleMin
                        forces an empty F_2 cell that is not the
                        old envelope
Falsifier               Random/bunched two-type words fail the
                        same way; (2,1) into n is realized;
                        or the law is ooe_blocks_oe / 243<256
Existing machinery      ooe_cell; ooe_blocks_oe;
                        two_ooe_still_blocks_oe; run_preimages;
                        excursion_map; almost_search CLOSE;
                        ordered excursion CLOSE
Maximum Phase-0 scope   Last-block classification; (2,1) and
                        (2,2,1) landing census; follow-depth
                        versus bunched; three-word coincidence
                        on small leftovers. No Phase 2, no
                        floor raise, no Lean
Promotion criterion     A reusable statement: two-type CycleMin
                        ending (2,1) is exact-cell empty, or
                        finance-optimal packing forces a
                        forbidden local transition beyond 243<256
Stop criterion          Same failure on non-extremal two-type;
                        (2,1) landings exist; or the law is
                        the old envelope rewritten
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Extremal \(=\) Christoffel \(=\) packed Beatty on the
  record leftovers —
  **COMPUTATIONALLY VERIFIED** / **KNOWN** Sturmian morphism
- Isolated `OE` plus expanding last `OOE` forces terminal
  \((2,1)\) —
  **EXACT — HUMAN PROOF** (Sturmian) /
  **COMPUTATIONALLY VERIFIED** (\(F_2(v)>v\))
- Terminal \((2,1)\) empty —
  **REFUTED** (`n=1000001`)
- Terminal \((2,2,1)\) empty —
  **REPARAMETERIZATION** of \(243<256\)
- Finance-to-cell leftover-killer —
  **REFUTED** (`juggler_cycle_finance_cell_bridge`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_finance_cell_bridge`
- Dataset: `data/research/juggler/cycle_finance/finance_cell_bridge/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_finance_cell_bridge.py`
- Windows: \(F_2\) scan \([3,20000]\); terminal census stride
  \(20\) on \([10^6+1,10^6+801]\) and
  \([2\cdot10^6+1,2\cdot10^6+801]\); follow on
  \([10^6+1,10^6+2001]\). Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_finance_cell_bridge` — **REFUTED**.

## Counterexamples

- \(n=1000001\) has a \((2,1)\) preimage
  \(12915515\to 100000159\to n\). Falsifier of empty
  terminal `OOE`.
- Canonical and bunched-`OOE` follow histograms are
  identical. Falsifier of a mechanical-specific early death.
- \(0/19\) and \(0/16\) \((2,2,1)\) hits are the existing
  \(243<256\) dual, not a new cell.

## Formalization

None. No `FinanceCellBridge.lean`. Paper A is unchanged.
Do not formalize the sample census.

## Results

- **Three-word collapse** — **COMPUTATIONALLY VERIFIED** on
  \(L=19,84,1054,25781\).
- **Terminal \((2,1)\) forced, not empty** —
  **COMPUTATIONALLY VERIFIED**
  (`finance_cell_bridge/summary.json`): `ends_21=true`,
  `n_21=19` of `41` near the floor.
- **Follow** — identical to bunched `OOE` (max \(6\)).
- **No hybrid leftover-killer.**

## Open questions

None from the finance-to-cell bridge. Phase 2 at \(L=55293\)
is not opened. The \(7481\) high-peak seeds stay with the
parked floor campaign.

## Decision

**CLOSE**. Finance extremality does determine a unique
two-type itinerary, and Sturmian isolation plus an expanding last
`OOE` forces the terminal pair \((2,1)\). That pair is
commonly realized. The backward search died one block later,
at \((2,2,1)\), which is the closed ordered-excursion
comparison \(243<256\). Follow depth \(O(1)\) is the shared
`OOE` prefix, not a property of the mechanical interleaving.
No Paper A edit, no ledger row, no Lean.

Best next question: none from the finance-to-cell bridge.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
finance refinement; not a second manuscript and not a
Paper A edit.
