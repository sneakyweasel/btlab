# Juggler seam ancestry graph

Status: **ARCHIVED**

Directed follow-up of the closed
[seam propagate](juggler_cycle_seam_propagate.md) type graph and
the closed
[intersection taxonomy](juggler_cycle_intersection_taxonomy.md),
not a reopen of those branches and not a new paper. The
archived graph \(G_{\mathrm{run}}\) has nodes \((a,r)\). This
phase asks whether first-collision parent-type/phase nodes with
run-labeled edges are a new obstruction.

Not a halt theorem, not a leftover-killer, not a finance reopen,
not a \(Q\)-state law, and not a claim that every positive
integer reaches 1.

## Problem

Nodes of \(G_{\mathrm{run}}\) are run types. Nodes of the
intersection table are parent types \(\{EE,EO,OE,OO\}\) or
phases \(\{V,O_{\mathrm{int}},P,E_{\mathrm{int}}\}\). Does the
product graph whose nodes remember how a seam was first reached,
and whose edges are legal \(O^{a}E^{r}\) runs, empty a
transition or become a DAG for a reason that is not either
archive?

## Exact statement

**Nodes are not \((a,r)\) (KNOWN).**
An ancestry node is \((\pi,\varphi,\mathrm{tag})\). The run
\((a,r)\) sits on the edge. Putting \((a,r)\) on the node is
\(G_{\mathrm{run}}\), already cyclic
(`realized_transition_graph`).

**First \(\mathtt{OO}\) is empty
(KNOWN / EXACT — LEAN VERIFIED).**
Two odd last letters at \(x\) share the unique odd parent
(`odd_preimage_unique`). Occupancy on \([13,2001)\) has
`n_first_oo=0`.

**One-step \(EE\) and \(EO\) are archived
(KNOWN / REPARAMETERIZATION).**
Even parents are the even cell (count, not a list). The
odd-plus-even channel is the unique odd parent plus that cell.
The CycleMin \(2{+}2\) window stays
\(\{\mathtt{OE}\mid\mathtt{OO},\mathtt{EE}\mid\mathtt{OO}\}\).
The two-step EE count is \(n(n^{2}+n+1)\).

**MULTI is empty on the window (COMPUTATIONALLY VERIFIED).**
A length-\(\ge 2\) foreign word that first meets an orbit at
\(x\) still ends on a one-step parent of \(x\). `n_multi=0`.

**Forgetful projection is \(G_{\mathrm{run}}\)
(COMPUTATIONALLY VERIFIED).**
Drop \((\pi,\varphi)\). The \((a,r)\to(a',r')\) graph on
\([13,2001)\) has \(48\) nodes, \(214\) edges, an
\(\mathtt{OOE}\) self-loop, and a cyclic CycleMin-shaped
subgraph. That is the archived type graph.

**Valley provenance is idle
(COMPUTATIONALLY VERIFIED).**
Every valley node is \(\mathtt{ARCHIVED\_EE}\) or
\(\mathtt{ARCHIVED\_EO}\) at phase \(V\). \(G_{\mathrm{anc}}\)
has three nodes and is cyclic.

**The phase necklace is run form
(COMPUTATIONALLY VERIFIED).**
Letter-level phase edges are exactly
\(V\to O_{\mathrm{int}}\to P\to E_{\mathrm{int}}\to V\),
including the \(a=1\) skip \(V\to P\) and the \(r=1\) skip
\(P\to V\).

**\(365/1517\) keep the same ancestry
(COMPUTATIONALLY VERIFIED / REPARAMETERIZATION).**
Both controls are \(\mathtt{EE}|V|\mathtt{ARCHIVED\_EE}\) on
the shared \((2,1)^{3}\) prefix, then split. That is
`J-block-map-q-state`.

No cycle of any length — not claimed.

## Current literature

- Unique odd cell —
  **EXACT — LEAN VERIFIED**
  (`odd_preimage_unique`, `oddLanding_preimage_unique`)
- \(2{+}2\) window \(\{\mathtt{OE}\mid\mathtt{OO},\mathtt{EE}\mid\mathtt{OO}\}\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_cyclic_seam.md](juggler_cycle_cyclic_seam.md))
- Trailing \(\mathtt{EE}\) count \(n(n^{2}+n+1)\) —
  **CLOSE**
  ([juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md))
- First-intersection taxonomy —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md))
- Realized \((a,r)\) type graph, \(\mathtt{OOE}\) self-loop —
  **CLOSE** / **REFUTED** as a DAG
  ([juggler_cycle_seam_propagate.md](juggler_cycle_seam_propagate.md))
- Run-length state law —
  **REFUTED**
  ([juggler_block_map_q.md](juggler_block_map_q.md); \(365\) vs
  \(1517\))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a lifted type-graph
obstruction; the product graph is a **REPARAMETERIZATION** of
\(G_{\mathrm{run}}\) plus the four-position taxonomy.

## Branch budget

```text
Mathematical target     Does the directed graph whose nodes are
                        first-collision parent-type/phase states
                        and whose edges are legal O^a E^r runs
                        empty a transition or become a DAG for a
                        reason that is not the archived (a,r)
                        graph and not the four-position taxonomy?
Novelty hypothesis      remembering how a seam was first reached
                        (parent-type / phase) splits the OOE
                        self-loop or 365/1517, or forbids an
                        edge both (a,r) types still allow
Falsifier               forgetful projection recovers G_run and
                        G_anc is also cyclic; (pi,phi) is idle
                        decoration; every valley is archived
                        one-step EE/EO; the phase necklace is
                        the closed four-position table; OO
                        first-collisions are odd_preimage_unique
Existing machinery      walk_blocks / realized_transition_graph
                        (cycle_seam_propagate); floor_power
                        (power_itineraries); odd_preimage
                        (cycle_almost_search); even_preimage_count
                        (bunched_short_return); first_oe_block /
                        prefix_allows_first_run (cycle_e_block);
                        LEGAL_22 / ee_entry_count;
                        J-block-map-q-state (365 vs 1517)
Maximum Phase-0 scope   define AncestryState = (pi, phi, tag);
                        build G_anc on odds in [13,2001);
                        project to G_run; recover OO empty and
                        one-step EE/EO as archived; test 365/1517.
                        No Lean, no finance, no leftover L, no
                        CLI, no Paper A
Promotion criterion     a lifted emptiness both (a,r) types
                        allow that is not cheap-OOE / prefix
                        failure; or G_anc is a DAG while G_run
                        is cyclic; or provenance splits 365/1517
Stop criterion          G_anc forgets to G_run or to the
                        four-position necklace; provenance is
                        idle; only archived one-step collisions
```

## Closed-bridge gates

Do not reopen seam propagate, the intersection taxonomy, the
cyclic seam, the entry corridor, the \(E^r\) block, block
transfer, or the \(Q\)-state law.

- **CLOSE** if the forgetful projection recovers \(G_{\mathrm{run}}\)
  and \(G_{\mathrm{anc}}\) is also cyclic.
- **CLOSE** if every valley is `ARCHIVED_EE` or `ARCHIVED_EO`
  at phase \(V\).
- **CLOSE** if the phase necklace is run form.
- **CLOSE** if first \(\mathtt{OO}\) is `odd_preimage_unique` and
  MULTI is empty.
- **CLOSE** if \(365/1517\) keep the same ancestry on the
  shared prefix.
- **PROMOTE** only if a provenance-conditioned emptiness, a
  DAG while \(G_{\mathrm{run}}\) is cyclic, or an ancestry
  split of \(365/1517\) survives those filters.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do
**not** reintroduce finance. Do **not** edit Paper A. Do
**not** claim termination. Do **not** add Lean. Do **not**
put \((a,r)\) on nodes. Do **not** treat one-step even-cell
multiplicity as new provenance.

## Explicitly out of Phase-0

A full \(T_u(n)=T_v(m)\) cell classification, an itinerary-order
invariant, a \(K=11\) proof, defect amplification, Fourier /
residues / \(Q\)-sections, a branch-and-bound engine, ledger
theorem row, new Lean, CLI, visualization, Paper A edit, a
leftover-killer census, a halt theorem.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Ancestry node \((\pi,\varphi,\mathrm{tag})\) —
  **REPARAMETERIZATION** of one-step parents plus run form
- First \(\mathtt{OO}\) —
  **KNOWN** empty (`odd_preimage_unique`)
- One-step \(EE\) / \(EO\) —
  **KNOWN** (`even_preimage_count`, `odd_preimage`,
  `ee_entry_count`)
- Forgetful projection —
  **REPARAMETERIZATION** of `realized_transition_graph`
- Phase necklace —
  **REPARAMETERIZATION** of \(O^{a}E^{r}\) run form
- Type-graph DAG after the lift —
  **REFUTED** (\(G_{\mathrm{anc}}\) cyclic; three idle
  valley nodes)
- Provenance split of \(365/1517\) —
  **REFUTED** (`J-block-map-q-state`)
- Ancestry leftover-killer —
  **REFUTED** (`juggler_cycle_seam_ancestry`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_seam_ancestry`
- Dataset: `data/research/juggler/cycle_finance/seam_ancestry/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_seam_ancestry.py`
- Window: occupancy and \(G_{\mathrm{anc}}\) on odds in
  \([13,2001)\), letter cap \(80\); CycleMin \(2{+}2\) and
  EE count at \(n=10^{6}+1\); controls \(365\), \(1517\).
  Fast suite only. No CLI. No new Lean. No \(N_0\) raise.

## Conjectures

`juggler_cycle_seam_ancestry` — **REFUTED**.

## Counterexamples

- First-collision \(\mathtt{OO}\) count \(0\) on
  \([13,2001)\). Falsifier of a new odd-odd first meeting.
- MULTI count \(0\). Every length-\(\ge 2\) occupancy hit
  reduces to a one-step parent of \(x\).
- Forgetful projection: \(48\) nodes, \(214\) edges,
  \(\mathtt{OOE}\) self-loop. Falsifier of a walk that is
  not \(G_{\mathrm{run}}\).
- Valley nodes
  \(\{\mathtt{EE}|V|\mathtt{ARCHIVED\_EE},\mathtt{EO}|V|\mathtt{ARCHIVED\_EO},\mathtt{OE}|V|\mathtt{ARCHIVED\_EO}\}\).
  \(G_{\mathrm{anc}}\) has \(3\) nodes, \(4\) edges, and a
  directed cycle. Falsifier of a DAG lift and of non-idle
  provenance.
- Phase edges are the eight-run-form necklace. Falsifier of
  a new phase invariant.
- \(365=(2,1)^{4}\) then \((1,3)\) versus \(1517=(2,1)^{3}\)
  then \((1,1)\), both
  \(\mathtt{EE}|V|\mathtt{ARCHIVED\_EE}\) on the shared
  prefix. Falsifier of a provenance split.

## Formalization

None added. The uniqueness lemma is already
`odd_preimage_unique` / `oddLanding_preimage_unique`. The type
graph is already `realized_transition_graph`. Paper A is
unchanged. Do not add `SeamAncestry.lean`.

## Results

- **First \(\mathtt{OO}\)** — **KNOWN**: empty
  (`seam_ancestry/summary.json`).
- **One-step tags** — **COMPUTATIONALLY VERIFIED**:
  \(4386\) `ARCHIVED_EE`, \(3140\) `ARCHIVED_EO`; MULTI
  empty. The \(308\) `ARCHIVED_OO` labels are one-step odd
  arrivals, not first-collisions.
- **Forgetful projection** — **COMPUTATIONALLY VERIFIED**:
  matches \(G_{\mathrm{run}}\) (\(48\) nodes, \(214\)
  edges, \(\mathtt{OOE}\) self-loop).
- **\(G_{\mathrm{anc}}\)** — **COMPUTATIONALLY VERIFIED**:
  cyclic; idle valleys; \(n_{\mathrm{new\_empty}}=0\).
- **Phase necklace** — **REPARAMETERIZATION** of run form.
- **Controls** — **REPARAMETERIZATION** of
  `J-block-map-q-state`.
- **No new cyclic obstruction.**

## Open questions

None from the seam ancestry graph. Do not reopen seam
propagate, the intersection taxonomy, or the \(Q\)-state
law. Do not build a transition-graph engine. Do not claim
termination.

## Decision

**CLOSE**. Decorating seams by first-collision parent type
and phase does not outrun the archived graphs. The forgetful
projection is \(G_{\mathrm{run}}\), which is cyclic. Every
valley is an archived one-step \(EE\) or \(EO\) at phase
\(V\), so provenance is idle decoration. The phase necklace
is \(O^{a}E^{r}\) run form. First \(\mathtt{OO}\) is
`odd_preimage_unique`. MULTI is empty. \(365\) and \(1517\) keep
the same ancestry on the shared prefix and still split.
That is useful negative knowledge; it is not a new
invariant. No Paper A edit, no ledger row, no new Lean, no
\(N_0\) raise, no finance reopen.

Best next question: none from the seam ancestry graph.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
parent-type/phase lift of the run-type graph; not a second
manuscript and not a Paper A edit.
