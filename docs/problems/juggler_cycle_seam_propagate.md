# Juggler adjacent-seam incompatibility propagation

Status: **ARCHIVED**

Directed follow-up of the closed seam stack
([juggler_cycle_e_block.md](juggler_cycle_e_block.md),
[juggler_cycle_seam_sliding.md](juggler_cycle_seam_sliding.md),
[juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md),
[juggler_cyclic_feasibility.md](juggler_cyclic_feasibility.md),
[juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md)),
not a reopen of those branches and not a new paper. Local seams
check types independently. This phase asks whether a feasible
block \(O^{a}E^{r}\) produces an output interval that constrains
the next type \((a',r')\).

Not a halt theorem, not a leftover-killer, not a finance reopen,
not a \(Q\)-state law, and not a claim that every positive integer
reaches 1.

## Problem

Independent prefix tests and letter-level cyclic cells already
exist. Does composing the archived peak/valley cell of
\(O^{a}E^{r}\) empty a successor \((a',r')\) that both factors
allow, or is the finite type graph a DAG?

## Exact statement

**The increment is adjacent, not local
(KNOWN).**
A single block \(O^{a}E^{r}\) is CycleMin-possible only if
\(2^{a+r}\le 3^{a}\) (`prefix_allows_first_run`). That test does
not mention the next seam. Letter-level `propagate_cycle` takes
a complete word. The scalar product \(\prod\rho_i=3^o/2^L\)
ignores order. Adjacent propagation is the leftover claim:
the output interval \(C_{i+1}\) of seam \(i\) is an input
constraint on seam \(i+1\).

**Cheap \(\mathtt{OOE}\) already blocks \(\mathtt{OE}\) at
\(v=n\) (KNOWN / EXACT — HUMAN PROOF).**
If \(a(v)=2\) and \(v^{27}<n^{32}\), then the next valley lies
below `oe_start_min(n)`. Two cheap \(\mathtt{OOE}\) blocks still
block \(\mathtt{OE}\) at a CycleMin start (\(243<256\)). Those
are the archived ordered-excursion lemmas, not new cells.

**Prefix pairs \((2,2)\) and \((3,2)\) fail independently
(KNOWN / REPARAMETERIZATION).**
\(2^{a+r}\le 3^{a}\) already forbids those first blocks. A
composed emptiness that is only this test is not adjacent
incompatibility.

**Phase-0 question.**
Write \(C_{i+1}=\mathrm{block\_image}(C_i,a,r)\). Does
\(C_{i+1}\) make some independently allowed \((a',r')\) empty,
other than the archived cheap-\(\mathtt{OOE}\) adjacency? If
every bounded type is a node and a realized or hull-feasible
successor is an edge, is that directed graph acyclic?

No cycle of any length — not claimed. A DAG would be a
type-graph obstruction, not a totality theorem.

## Current literature

- First-block expanding test \(2^{a+r}\le 3^{a}\) —
  **REPARAMETERIZATION**
  ([juggler_cycle_e_block.md](juggler_cycle_e_block.md))
- Trailing-evens / even tower —
  **EXACT — LEAN VERIFIED**
  (`cycle_trailing_evens_lt`)
- Cheap \(\mathtt{OOE}\) cannot feed \(\mathtt{OE}\) at \(v=n\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Two-block \((2,2,1)\) at \(v=n\) —
  **EXACT — HUMAN PROOF** / **REPARAMETERIZATION** of
  \(81/64<4/3\)
- Letter-level cyclic interval propagation —
  **CLOSE**
  ([juggler_cyclic_feasibility.md](juggler_cyclic_feasibility.md))
- Block exponent product \(\prod\rho_i=3^o/2^L\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md))
- Run-length state law \((a_i)\mapsto(a_{i+1})\) —
  **REFUTED**
  ([juggler_block_map_q.md](juggler_block_map_q.md); \(365\) vs
  \(1517\))
- Cyclic seam / \(E^r\) block / seam sliding —
  **CLOSE**
- Cyclic block transfer —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_block_transfer.md](juggler_cycle_block_transfer.md))
- Peak–valley interval composition —
  **CLOSE**
  ([juggler_cycle_peak_valley_composition.md](juggler_cycle_peak_valley_composition.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as an adjacent leftover
obstruction; composed hulls and the type graph are
**REPARAMETERIZATION**s of the archived prefix test, cheap
\(\mathtt{OOE}\) adjacency, \(\rho\), and `propagate_cycle`.

## Branch budget

```text
Mathematical target     Does the output interval of a feasible
                        block O^a E^r restrict the next type
                        (a',r') beyond the independent prefix
                        test 2^{a'+r'} <= 3^{a'} and the archived
                        cheap-OOE adjacency?
Novelty hypothesis      seam_i implies a genuine constraint on
                        seam_{i+1}: a composed cell empties a
                        transition both factors allow, or the
                        finite type graph on bounded (a,r) is a DAG
Falsifier               every empty composed edge is prefix-
                        expansion or the archived (2,1)/(2,2,1)
                        at v=n; the realized graph has a directed
                        cycle; interval shrink equals rho;
                        block-level cyclic closure matches
                        propagate_cycle
Existing machinery      even_tower_bounds, prefix_allows_first_run
                        (cycle_e_block); excursion_map, ooe_blocks_oe
                        (cycle_ordered_excursion); Bound /
                        forward_image / propagate_cycle
                        (cyclic_feasibility); rho (cycle_exponent_budget);
                        a_of / 365 vs 1517 (block_map_q)
Maximum Phase-0 scope   exact two-block image; small (a,r) table;
                        realized transition graph on [13,2001);
                        recover archived (2,1) at v=n; compare
                        C_{k+1}=C_1 to letter-level propagate_cycle
                        on a few short words. No Lean, no finance,
                        no leftover L, no CLI, no Paper A
Promotion criterion     a composed emptiness that both independent
                        prefix tests allow and that is not the
                        archived cheap-OOE adjacency; or a CycleMin-
                        legal type graph with no directed cycle
Stop criterion          composed emptiness = archived tests;
                        realized graph is cyclic and multi-valued;
                        log-width shrink = rho; block propagate
                        = letter propagate
```

## Closed-bridge gates

Do not reopen the entry corridor, the cyclic seam, the
first-intersection taxonomy, the \(E^r\) block, seam sliding,
ordered excursion, cyclic feasibility, the exponent budget,
cyclic block transfer, or the \(Q\)-state law. Do not reopen
\(r=4\) pullback.

- **CLOSE** if every `composed_empty and independent_ok` row
  is the archived cheap-\(\mathtt{OOE}\) adjacency or a
  prefix-test failure.
- **CLOSE** if the realized type graph has a directed cycle.
- **CLOSE** if log-width shrink matches \(\rho\).
- **CLOSE** if block-level cyclic closure matches
  `propagate_cycle`.
- **PROMOTE** only if a composed cell empties a transition
  both prefix tests allow and that emptiness is not
  \((2,1)\) / \((2,2,1)\) at \(v=n\), or the CycleMin-legal
  bounded type graph is acyclic.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do
**not** reintroduce finance. Do **not** edit Paper A. Do
**not** claim termination. Do **not** add Lean.

## Explicitly out of Phase-0

A \(K=11\) proof, defect amplification, Fourier / residues /
\(Q\)-sections, a branch-and-bound engine, ledger row, new Lean,
CLI, visualization, Paper A edit, a leftover-killer census, a
halt theorem.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Block image \(C\mapsto T^{O^{a}E^{r}}(C)\) —
  **REPARAMETERIZATION** of `forward_image`
- Independent prefix test —
  **KNOWN** (`prefix_allows_first_run`)
- Cheap \(\mathtt{OOE}\) adjacency at \(v=n\) —
  **KNOWN** (`ooe_blocks_oe`, `two_ooe_still_blocks_oe`)
- Log-width shrink versus \(\rho\) —
  **REPARAMETERIZATION** of the closed exponent budget
- Block-level \(C_{k+1}=C_1\) —
  **REPARAMETERIZATION** of `propagate_cycle` if they agree
- Type-graph DAG —
  **REFUTED** (OOE self-loop; CycleMin-shaped subgraph cyclic)
- Deterministic \((a,r)\mapsto(a',r')\) —
  **REFUTED** (`J-block-map-q-state`)
- Adjacent-seam leftover-killer —
  **REFUTED** (`juggler_cycle_seam_propagate`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_seam_propagate`
- Dataset: `data/research/juggler/cycle_finance/seam_propagate/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_seam_propagate.py`
- Window: prefix table \(a,a'\le 6\), \(r,r'\le 4\); CycleMin
  tube at \(n=10^6+1\); realized transitions on odds in
  \([13,2001)\); shrink check on a short odd interval; cyclic
  closure on three short expanding itineraries. Fast suite only.
  No CLI. No new Lean. No \(N_0\) raise.

## Conjectures

`juggler_cycle_seam_propagate` — **REFUTED**.

## Counterexamples

- Eighty-one independently allowed pairs on the wide hull
  \([3,10^6+1]\), the CycleMin tube \([10^6+1,10^6+4001]\),
  and the middle \(a\ge 1\) table: `n_new_empty=0`. Falsifier
  of a new composed emptiness.
- First \(\mathtt{OOE}\) start \(1000057\) lands at
  \(5623773<\mathtt{oe\_start\_min}(10^6+1)=100000135\). Two
  \(\mathtt{OOE}\) land at \(39244721\). That is
  `ooe_blocks_oe` / `two_ooe_still_blocks_oe`.
- \((2,2)\) and \((3,2)\) fail \(2^{a+r}\le 3^{a}\)
  independently.
- Realized type graph on \([13,2001)\): \(48\) nodes, \(214\)
  edges, \(\mathtt{OOE}\) self-loop, max out-degree \(30\).
  CycleMin-shaped subgraph: \(17\) nodes, \(41\) edges, also
  cyclic. Falsifier of a DAG.
- \(365=(2,1)^4\) then \((1,3)\) versus \(1517=(2,1)^3\) then
  \((1,1)\). Falsifier of a deterministic successor. This is
  `J-block-map-q-state`.
- Log-width ratio of `block_image` equals \(\rho\) (\(9/8\),
  \(3/4\)). Falsifier of a new shrink law.
- Block-level \(C_{k+1}=C_1\) is not strictly stronger than
  `propagate_cycle` on \(\mathtt{OOOOEE}\),
  \(\mathtt{OOOOOOEEE}\), \(\mathtt{OOEOOEOOEOE}\).

## Formalization

None added. Floor cells are already `forward_image`. The
prefix test is already `power_bound_word` plus
`even_run_scale_barrier`. Cheap \(\mathtt{OOE}\) adjacency is
already the ordered-excursion cell. Paper A is unchanged.
Do not add `SeamPropagate.lean`.

## Results

- **Archived adjacency** — **KNOWN**: first \(\mathtt{OOE}\)
  at \(1000057\) lands below `oe_start_min`; two \(\mathtt{OOE}\)
  still do. Prefix pairs \((2,2)\) and \((3,2)\) fail the
  expanding test (`seam_propagate/summary.json`).
- **Composed pairs** — **COMPUTATIONALLY VERIFIED**:
  `n_new_empty=0` on all three tables (\(81\) independently
  allowed pairs each).
- **Type graph** — **COMPUTATIONALLY VERIFIED**: cyclic and
  multi-valued, including the CycleMin-shaped subgraph. DAG
  implies termination is false as a type-level statement.
- **Shrink** — **REPARAMETERIZATION** of \(\rho\).
- **Cyclic closure** — **REPARAMETERIZATION** of
  `propagate_cycle`: the block coarsening is not strictly
  stronger.
- **No new cyclic obstruction.**

## Open questions

None from adjacent-seam incompatibility propagation. Do not
reopen ordered excursion, cyclic feasibility, the exponent
budget, or the \(Q\)-state law. Do not build a transition-graph
engine. Do not claim termination.

## Decision

**CLOSE**. Adjacent propagation does not outrun the archived
tests. Independently allowed successors stay hull-feasible.
The only emptied cheap adjacency is \(\mathtt{OOE}\to\mathtt{OE}\)
at a CycleMin start, already `ooe_blocks_oe`. The realized
type graph has an \(\mathtt{OOE}\) self-loop, so it is not a
DAG and cannot prove termination. Interval shrink is \(\rho\).
Block-level \(C_{k+1}=C_1\) is letter-level feasibility
coarsened to valleys. That is useful negative knowledge; it
is not a new invariant. No Paper A edit, no ledger row, no
new Lean, no \(N_0\) raise, no finance reopen.

Best next question: none from adjacent-seam incompatibility
propagation.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on
constraint propagation of adjacent \(O^{a}E^{r}\) seams; not
a second manuscript and not a Paper A edit.
