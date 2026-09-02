# Juggler global cyclic itinerary feasibility

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a reopen of
terminal cells, \(Z_5\), length-11 assembly, four-even leftovers,
p-adic systems, escape-language density, survival-set occupancy, or
generic inverse search, not a new atlas language tag, not Paper A,
and not a claim that every positive integer reaches 1.

Open trajectories have repeatedly looked generic. This phase asks
whether the extra equality \(T^k(n)=n\) on a closed itinerary
produces an itinerary-independent arithmetic mismatch.

## Problem

For a finite cyclic parity itinerary \(w\), do the exact floor-cell
equations around the loop become inconsistent once closure is
imposed, independently of the particular leftover spelling?

## Exact statement

\(\operatorname{CycReal}(w)\) means there exists \(n\ge 2\) whose
first \(k=|w|\) steps realise \(w\) and satisfy \(T^k(n)=n\).
`CycleMin` is not imposed at the filter stage. Phase 0 enumerates
primitive necklaces, applies the exponent envelope, the unweighted
cell product, interval propagation of all rotations, a plus-one
weight bound that uses only \(x_i\ge 2\), and a bounded exact
scan. It then compares the residue to the existing CycleItinerary
layer.

A finite empty window is `NOT OBSERVED WITHIN SEARCH BOUND`.
This is not a halt theorem and not a no-cycle theorem.

## Current literature

- Formally expanding cycle itineraries —
  **EXACT — LEAN VERIFIED** (`cycle_itinerary_formally_expanding`)
- Neutral exponent \(3^o=2^k\) —
  **EXACT — LEAN VERIFIED** (`two_pow_ne_three_pow`)
- Contracting words —
  **EXACT — LEAN VERIFIED** (`power_bound_contracts`)
- All-odd words expand for \(n\ge 3\) —
  **EXACT — LEAN VERIFIED** (`odd_word_expands`)
- At most three evens —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_even_count_le_three`)
- Period at least eleven —
  **EXACT — LEAN VERIFIED** (`cycle_itinerary_length_ge_eleven`)
- CycleMin \((n+1)/n\) fudge on the thirty first-expanding
  leftovers — **EXACT — LEAN VERIFIED**; not reopened
- Length \(\le 8\) census — **EXACT — LEAN VERIFIED**
- OEIS A007320 (`oeis-A007320`) — **known**. Totality is not
  claimed

Project relationship: **extended**, then **reparameterization**.

## Branch budget

```text
Mathematical target     Do the exact floor-cell equations around a
                        closed itinerary become inconsistent once
                        T^k(n)=n is imposed, in a way that is not
                        a single-word envelope or a CycleMin leftover?
Novelty hypothesis      Joint closure (rotated cells + product of
                        +1 widths) yields an itinerary-independent sign
                        that open trajectories never see.
Falsifier               Expanding mixed necklaces stay interval-
                        feasible; every new filter is CycleMin
                        (n+1)/n fudge or an existing census.
Existing machinery      PowerBound, odd_word_expands,
                        power_bound_contracts, two_pow_ne_three_pow,
                        CycleMin fudge, floor cells, length-8 census,
                        even-count <= 3, length >= 11
Maximum Phase-0 scope   Primitive necklaces; exponent + interval +
                        phi-product + plus-one weight; bounded exact
                        solve; near-cycles. No Lean, no leftover
                        reopen, no inverse-mass reopen.
Promotion criterion     A uniform closure mismatch, or a small
                        parametric surviving family that is not a
                        known leftover list.
Stop criterion          Filters reproduce CycleMin / envelope;
                        systems stay unconstrained; or a genuine
                        integer cycle (then stop and verify).
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\operatorname{CycReal}(w)\) —
  **REPARAMETERIZATION** of `CycleItinerary`
- Exponent filter \(2^k\le 3^o\) —
  **EXACT — LEAN VERIFIED** (`cycle_itinerary_formally_expanding`);
  not counted as new
- All-even descent / all-odd expansion —
  **EXACT — LEAN VERIFIED**
- Unweighted cell product
  \(\prod_O x^3/(x+1)^2\cdot\prod_E x/(x+1)^2<1\) —
  **OBSERVATION**: necessary on any integer cycle; fires on
  all-odd states \(\ge 3\), already covered by
  `odd_word_expands`; does not fire on mixed leftover hulls
- Rotation-consistent interval propagation —
  **OBSERVATION**: no collision on leftover-shaped words
  inside the search cap
- Plus-one weight \(n^\mu<(3/2)^W\) —
  **REPARAMETERIZATION** of the CycleMin \((n+1)/n\) machine
  with the weaker uniform \(m=2\)
- Word-independent strict closure mismatch —
  **REFUTED** as a Phase-0 statement: after the existing
  CycleItinerary layer the residue is exactly \(e\ge 4\),
  \(k\ge 11\)
- Global halt / no nontrivial cycle — not claimed

## Experiments

- Probe: `research.juggler_sequence.cyclic_feasibility`
- Records: [juggler_cyclic_feasibility.md](../research/juggler_cyclic_feasibility.md),
  [juggler_cyclic_feasibility.json](../research/juggler_cyclic_feasibility.json)
- Dataset: `data/research/juggler/cyclic_feasibility/`
- Tests: `tests/research/juggler_sequence/test_cyclic_feasibility.py`

Science window: primitive necklaces \(k\le 16\); \((k,o)\) pairs
to \(48\); direct orbits \(n\le 2\cdot 10^4\); plus-one / interval
scan cap \(8\cdot 10^3\). Tests use \(k\le 8\), \(n\le 160\).
No CLI. No Lean.

## Conjectures

None opened.

## Counterexamples

- “Every cyclic itinerary has a net strict sign from a new
  joint inequality.” False: interval hulls and the unweighted
  \(\varphi\)-product stay feasible on the \(e\ge 4\) residue.
- “Closed-path potentials \(\log x\), \(x^a-y^b\), or local
  defects telescope to a definite cycle sign.” False on open
  edges they are one-sided cell tautologies; they do not
  produce a new closed-path contradiction for mixed itineraries.
- “A genuine integer cycle exists below the direct window.”
  False for \(2\le n\le 2\cdot 10^4\)
  (`NOT OBSERVED WITHIN SEARCH BOUND`).

## Formalization

None added. Existing `CycleItinerary`, `cycle_itinerary_formally_expanding`,
`odd_word_expands`, `no_cycle_itinerary_even_count_le_three`, and
`cycle_itinerary_length_ge_eleven` already contain the cheap layer.
No `CyclicFeasibility.lean`. No `sorry`. Paper A is unchanged.

## Results

Classification **CYCLIC_FEASIBILITY_CLOSED**.

The cheap cyclic filters are the existing CycleItinerary layer.
Joint interval / \(\varphi\)-product constraints never fire on
the leftover residue. Direct search finds no cycle in the
window. See the research record for the census table.

## Open questions

None from generic cyclic feasibility at this scope. Do not
assemble a length-16 census. Do not reopen the four-even
leftover cells. The no-cycle machinery remains
word/structure dependent.

## Decision

**CLOSE**. Cyclic closure, after quotienting by the existing
envelope / all-odd / even-count theorems, is the leftover
family \(e\ge 4\), \(k\ge 11\) already under CycleMin attack.
The new joint constraints add no itinerary-independent mismatch.
A branch whose new statements are `KNOWN` or
`REPARAMETERIZATION` is a close.

Best next question: none from generic cyclic itinerary
feasibility. The leftover hole is still a cube cell without
a square cell.

## Publication assessment

Status: `EXPLORATORY`. A negative structural check, not a
paper candidate and not a Juggler totality result.
