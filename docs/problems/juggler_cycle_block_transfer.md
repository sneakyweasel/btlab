# Juggler cyclic block transfer

Status: **ARCHIVED**

Directed follow-up of
[juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md),
[juggler_cycle_closure.md](juggler_cycle_closure.md),
[juggler_cycle_e_block.md](juggler_cycle_e_block.md),
and [juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md),
not a reopen of those branches and not a new paper. After the
exponent budget closed as \(3^o/2^L\), this phase asks whether
composing exact \(O^a E^r\) interval maps around a CycleMin
necklace produces a cyclic obstruction that those branches did
not already name.

Not a halt theorem, not a run-length automaton, not a leftover
census, not a finance reopen, and not a claim that every cycle
word is impossible.

## Problem

For each block \(B(a,r)=O^a E^r\), write an interval transfer
\(I_{i+1}=F_{a,r}(I_i)\), impose \(n\le V_i\) and \(P_i>V_i\),
and compose \(I_1\to\cdots\to I_1\). Does outcome A (global
expansion), B (global contraction), or C (empty run-type
digraph) fire for a reason that is not an archived cell?

## Exact statement

**\(F_{a,r}\) is the archived hull
(KNOWN / REPARAMETERIZATION).**
The odd climb is \(w^{2^a}\le v^{3^a}\) (`power_bound_word`).
The even descent is \(v^{2^r}\le p<(v+1)^{2^r}\)
(`cycle_trailing_evens_lt` / `even_tower_bounds`). The composite
outer cell is
\[
V_{\mathrm{next}}^{2^{a+r}}\le V^{3^a}<(V_{\mathrm{next}}+1)^{2^{a+r}}.
\]
At \((a,r)=(1,1)\) this is the \(\mathtt{OE}\) corridor
\(z^4\le x^3<(z+1)^4\). At \((2,1)\) it is the OOE cell
\(w^8\le v^9\). The \(r=1\) point map agrees with
`excursion_map`.

**Formal \(F_{\mathrm{cycle}}\) is \(x\mapsto x^{3^o/2^L}\)
(KNOWN / REPARAMETERIZATION).**
The leading-scale composition is the exponent-budget product.
Outcome A at this scale is \(3^o>2^L\), which every nonempty
cycle itinerary already needs (`cycle_itinerary_formally_expanding`).
Outcome B is a contracting itinerary, already impossible. Leftover
\((L,o)=(19,12)\) and \((84,53)\) are formally expanding, so A
does not contradict. Floors on the leftover gap are
`cycleMin_finance`.

**Two-block hulls are \(\mu\) products
(KNOWN / REPARAMETERIZATION).**
\((2,1)\circ(2,1)\) is \(81/64\), and \(81/64<4/3\) is
\(243<256\), the archived ordered-excursion \((2,2,1)\)
comparison. \((2,1)\circ(1,1)\) is \(27/32\). No third block.

**Outcome C is the closed run-length split
(KNOWN / REFUTED as a grammar).**
The prefix \((2,2,2)\) has next run \(2\) at \(365\) and \(1\)
at \(1517\). Later pairs are unrestricted
([juggler_odd_run_itinerary.md](juggler_odd_run_itinerary.md)).
The next \(a\) is the landing’s arithmetic state, not a
function of \((a,r)\). Do not build a run-length automaton.

CycleMin \(n\le V_i\) and \(P_i>V_i\) are
`cycleMin_even_ge_sq` / `even_run_scale_barrier`, already in
the first-block test \(2^{a_0+r}\le 3^{a_0}\).

No cycle of any length — not claimed.

## Current literature

- Point map \(F_a=T^{a+1}\) —
  **REPARAMETERIZATION** of `excursion_map`
- OOE cell \(w^8\le v^9\); \((2,2,1)\) is \(243<256\) —
  **EXACT — HUMAN PROOF** /
  **REPARAMETERIZATION**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Pair-level OE cell \(z^4\le x^3<(z+1)^4\) —
  **CLOSE**
  ([juggler_cycle_closure.md](juggler_cycle_closure.md))
- \(E^r\) tower —
  **REPARAMETERIZATION**
  ([juggler_cycle_e_block.md](juggler_cycle_e_block.md))
- Block product \(3^o/2^L\) —
  **CLOSE**
  ([juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md))
- Run-length grammar —
  **REFUTED** / **PARK**
  ([juggler_odd_run_itinerary.md](juggler_odd_run_itinerary.md),
  [juggler_block_map_q.md](juggler_block_map_q.md))
- Formal expansion \(2^L<3^o\) —
  **EXACT — LEAN VERIFIED**
- Cycle finance —
  **EXACT — LEAN VERIFIED**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new cyclic transfer;
every layer is an archived cell, \(3^o/2^L\), or the closed
run-length graph.

## Branch budget

```text
Mathematical target     Does composing exact O^a E^r interval
                        maps around a CycleMin necklace produce
                        a cyclic obstruction (A/B/C) that is
                        not power_bound_word / excursion_map /
                        cycle_closure hulls / 3^o/2^L / the
                        closed run-length graph?
Novelty hypothesis      interval transfer plus general r plus
                        cyclic return of I_1 makes A or B fire,
                        or C forbids a directed cycle of run
                        types
Falsifier               F_{a,r} is the archived cell; formal
                        F_cycle is x^{3^o/2^L}; C is 365 vs 1517
Existing machinery      excursion_map; even_tower_bounds;
                        power_bound_word;
                        cycle_itinerary_formally_expanding;
                        ordered excursion; pair closure;
                        odd-run itinerary
Maximum Phase-0 scope   write F_{a,r} as the existing cell;
                        compose 1–2 blocks and the formal
                        cycle map; check A/B against 3^o ? 2^L;
                        record C as the closed split. No
                        automaton, no leftover census, no
                        finance reopen
Promotion criterion     an interval image that is not the
                        exponent cell, or A/B that is not
                        formal expansion/contraction
Stop criterion          F_{a,r} and F_cycle are archived cells
                        / 3^o/2^L; C is the closed grammar
```

## Closed-bridge gates

Do not reopen ordered excursion, pair-level closure, the
exponent budget, or the run-length itinerary. Do not build a
run automaton.

- **CLOSE** if \(F_{a,r}\) is the archived exponent cell plus
  even tower.
- **CLOSE** if formal \(F_{\mathrm{cycle}}\) is \(x^{3^o/2^L}\),
  so A is required expansion and B is a contracting itinerary.
- **CLOSE** if two-block hulls are \(\mu\) products
  (\(243<256\)).
- **CLOSE** if C is the \(365/1517\) split.
- **PROMOTE** only if an interval image appears that is not
  the exponent cell.

Do **not** raise \(N_0\). Do **not** open \(L=25781\). Do
**not** reintroduce finance. Do **not** edit Paper A. Do
**not** add Lean. Do **not** enumerate a run-type adjacency
matrix.

## Explicitly out of Phase-0

A \(k\)-block necklace solver, a directed-graph search over
\((a,r)\) types, leftover-killer on \(L=25781\) or \(55293\),
finance reopen, Lean `BlockTransfer.lean`, CLI, Paper A edit.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(F_{a,r}\) outer cell —
  **REPARAMETERIZATION** of `power_bound_word` plus the even
  tower
- \(r=1\) point map —
  **KNOWN** (`excursion_map`)
- Formal \(F_{\mathrm{cycle}}\) —
  **REPARAMETERIZATION** of \(3^o/2^L\)
- Two-block \(\mu\) product —
  **REPARAMETERIZATION** of ordered excursion
- Outcome C —
  **KNOWN** (\(365\) vs \(1517\))
- Cyclic transfer leftover-killer —
  **REFUTED** (`juggler_cycle_block_transfer`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_block_transfer`
- Dataset: `data/research/juggler/cycle_finance/block_transfer/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_block_transfer.py`
- Window: OE/OOE cells; \(r=1\) agreement at \(365\) and
  \(1000057\); formal leftovers \(19\) and \(84\); two-block
  pairs \((2,1)^2\) and \((2,1)\circ(1,1)\); first four runs
  of \(365\) and \(1517\). Fast suite only. No CLI. No new
  Lean. No run-type matrix.

## Conjectures

`juggler_cycle_block_transfer` — **REFUTED**.

## Counterexamples

- \((1,1)\) is \(z^4\le x^3<(z+1)^4\). Falsifier of a new OE
  interval.
- \((2,1)\) is \(w^8\le v^9\). Falsifier of a new OOE interval.
- Formal leftovers \(19\) and \(84\) have outcome A and do not
  contradict a cycle. Falsifier of global-expansion kill.
- \((2,1)^2\) is \(81/64\) and \(243<256\). Falsifier of a new
  two-block hull.
- \(365=(2,2,2,2)\) and \(1517=(2,2,2,1)\). Falsifier of an
  empty run-type digraph.

## Formalization

None added. The cells are already `power_bound_word` and
`cycle_trailing_evens_lt`. The point map is already
`excursion_map`. Paper A is unchanged. Do not add
`BlockTransfer.lean`.

## Results

- **\(F_{a,r}\)** — **REPARAMETERIZATION**
  (`block_transfer/summary.json`).
- **Formal A/B** — **KNOWN**: A required, B forbidden.
- **Two-block** — **REPARAMETERIZATION** of \(243<256\).
- **C** — **COMPUTATIONALLY VERIFIED**: \(365\) vs \(1517\).
- **No new cyclic obstruction.**

## Open questions

None from the cyclic transfer architecture. Do not open a
run-length automaton. Do not reopen ordered excursion, pair
closure, or the exponent budget.

## Decision

**CLOSE**. Interval transfer plus general \(r\) plus cyclic
return does not produce a new map. \(F_{a,r}\) is the archived
exponent cell. Formal composition is \(3^o/2^L\), so A is the
expanding-word lemma and B is a contracting itinerary. Two-block
hulls are \(\mu\) products. Outcome C is the standing
\(365/1517\) split: the next run is not a function of the
run-type word. No Paper A edit, no ledger row, no new Lean,
no \(N_0\) raise, no finance reopen, no run automaton.

Best next question: none from the cyclic block transfer.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
transfer-graph rewrite of archived cells; not a second
manuscript and not a Paper A edit.
