# Juggler inverse-tube realizability

Status: **ARCHIVED**

Refinement of
[juggler_cycle_almost_search.md](juggler_cycle_almost_search.md),
[juggler_cycle_finance_cell_bridge.md](juggler_cycle_finance_cell_bridge.md),
and [juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md),
not a new paper. After the finance-extremizer discrepancy closed,
this phase asks whether the *ordered* inverse tube of a
near-convergent word loses integer occupancy for a reason that
is not an archived floor cell.

Not a halt theorem, not a finance reopen, not a floor raise, not
Phase 2 at \(L=55293\), and not a claim that one packed necklace
is the obstruction.

## Problem

Symbolic two-type words at \((L,o)=(25781,16266)\) are
finance-admissible, but an integer must realize the letters in
order. Does the inverse interval

\[
\mathcal P_k(y)=F_{a_0}^{-1}\cdots F_{a_{k-1}}^{-1}(y)
\]

become empty because repeated floor constraints make the tube
thinner than the integer lattice, uniformly for every
sufficiently balanced word?

## Exact statement

**Occupied thin hulls (COMPUTATIONALLY VERIFIED).**
The real \(OOE\)-hull of a singleton can have width \(<1\) and
still contain an integer. Witness: \(9\xrightarrow{\mathrm{OOE}}11\),
last-step real width \(0.221\). Width contraction does not decide
emptiness.

**Near-convergent inverse death is the terminal \(OOE\) cell
(COMPUTATIONALLY VERIFIED).**
On complete end-\(E\) prefixes of the Beatty packed itinerary, the
bunched \((OOE)^6\), \(OE\)-front, interleaved, and extra-odd
front words, every endpoint \(y\in\{101,1001,10^4+1,10^5+1,10^6+1\}\)
has empty exact occupancy after the first inverted \(OOE\)
(`death_k=3`, tag `empty_ooe`). Zero unarchived deaths. At the
toy scale \(y=11\) the first \(OOE\) is occupied and the next
block dies, still on an archived cell.

**Forward lifespan does not grow with scale (COMPUTATIONALLY
VERIFIED).**
On \(80\) odds at each of \(10^2,\ldots,10^6\), max \(R_W\) is
flat (\(6\)--\(8\) on the packed/bunched prefixes; mean
\(\approx 2\)). Changing the prescribed order moves the maximum
by \(O(1)\). The named chain \(365\) realizes \(13\) letters of
\((OOE)^*\); that is the known PE spine, not a scale law.

**Contracting controls explode (COMPUTATIONALLY VERIFIED).**
Pure \(E\) and long \(OE\) inverses are hulled at scale
\(2\cdot 10^6\); they do not empty. Pure \(O\) dies at
`empty_odd_cell`. Losing occupancy is an expanding-block
phenomenon, not a generic inverse-width law.

No cycle of any length — not claimed.

## Current literature

- Almost-cycle search, prescribed-word follow \(\le 11\),
  backward empty \(OOE\) after \(\le 2\) blocks —
  **CLOSE**
  ([juggler_cycle_almost_search.md](juggler_cycle_almost_search.md))
- Finance-to-cell bridge; terminal \((2,1)\) realized; empty
  \((2,2,1)\) is \(243<256\) —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_finance_cell_bridge.md](juggler_cycle_finance_cell_bridge.md))
- \(OOE\) cell \(w^8\le v^9\); two-block persistence
  \(243<256\) —
  **EXACT — HUMAN PROOF** /
  leftover-killer **REFUTED**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Inverse hull versus exact fibre —
  **CLOSE** as `BACKWARD_COMPLEX`
  ([juggler_backward_geometry.md](juggler_backward_geometry.md))
- Nested realizing sets \(R_w\) —
  **CLOSE** as `REALIZATION_GEOMETRY_COMPLEX`
  ([juggler_realization_geometry.md](juggler_realization_geometry.md))
- Finance-extremizer discrepancy —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_extremizer_discrepancy.md](juggler_cycle_extremizer_discrepancy.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new emptiness mechanism;
the inverse tube is a reparameterization of the archived \(OOE\)
cell.

## Branch budget

```text
Mathematical target     Does the inverse tube of a near-convergent
                        word empty for a reason other than archived
                        cells, uniformly across finance-admissible
                        orderings?
Novelty hypothesis      lattice occupancy of a shrinking inverse
                        tube, not finance / (L,o,e) / one packed word
Falsifier               every emptiness is an archived cell; hull
                        width < 1 while occupied; some balanced
                        orderings stay occupied past that barrier
Existing machinery      odd_preimage, compatible_oe_preimages,
                        follow_depth, ooe_cell / 243<256, two-type
                        prefixes
Maximum Phase-0 scope   exact inverse occupancy on prefixes ≤ 18;
                        R_W scale sweep; no Lean, no Paper A, no N0
Promotion criterion     emptiness not tagged archived, or a uniform
                        K that is not the known two-block OOE death
Stop criterion          death is cells; width is a hull relaxation;
                        no new uniform law
```

## Closed-bridge gates

Classify emptiness before any follow-up. Do not reopen the boxed
hybrid already **REFUTED** as `juggler_cycle_finance_cell_bridge`,
and do not reopen `BACKWARD_COMPLEX` interval-hull relaxations.

- **CLOSE** if every near-convergent emptiness is `empty_ooe` /
  `empty_oe` / `empty_odd_cell` / \(243<256\), or if a hull of
  width \(<1\) remains occupied.
- **CLOSE** if \(R_W\) is flat in scale and order changes move
  it by \(O(1)\).
- **PROMOTE** only if an inverse emptiness occurs while every
  archived cell of the endpoints is nonempty.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do **not**
edit Paper A.

## Explicitly out of Phase-0

A Level-4 near-convergent theorem, a \(K=11\) proof, the
\(1054k\) family, Fourier / residues / \(Q\)-sections, ledger
row, Lean, CLI, visualization.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exact inverse occupancy of a prescribed word —
  **COMPUTATIONALLY VERIFIED**; dies at the first inverted
  \(OOE\) for every tested near-convergent prefix at
  \(y\ge 101\)
- Real inverse hull width —
  **REPARAMETERIZATION** of the floor cells; width \(<1\) does
  not imply empty
- Order-blind exponent hull \(y^{2^k/3^{o_k}}\) —
  **REPARAMETERIZATION** of `power_bound_word`; it does not
  decide occupancy on this grid
- Forward \(R_W(n)\) versus scale —
  **COMPUTATIONALLY VERIFIED**; flat on \(10^2\)--\(10^6\)
- Uniform bounded lifespan \(R_W\le 20\) for every \(n\) —
  **OBSERVATION** on the scanned windows and named labs
  (max \(13\) at \(365\)); not a theorem
- Inverse-width leftover-killer —
  **REFUTED** (`juggler_cycle_inverse_width`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_inverse_width`
- Dataset: `data/research/juggler/cycle_finance/inverse_width/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_inverse_width.py`
- Window: complete end-\(E\) prefixes of length \(\le 18\);
  inverse endpoints \(\{11,101,10^3+1,10^4+1,10^5+1,10^6+1\}\);
  forward \(80\) odds at each of \(10^2,\ldots,10^6\);
  calibration \(\{365,11681,14237,15343,27623,1000057\}\).
  Fast suite only. No CLI. No Lean. No \(N_0\) raise.

## Conjectures

`juggler_cycle_inverse_width` — **REFUTED**.

## Counterexamples

- \(9\xrightarrow{\mathrm{OOE}}11\) occupies a real hull of
  width \(0.221<1\). Falsifier of “width \(\to 0\) empties the
  tube.”
- Beatty packed, bunched \((OOE)^6\), \(OE\)-front, interleave,
  and extra-odd prefixes all die at `empty_ooe` / \(k=3\) on
  \(y=10^6+1\). Falsifier of a width law that is not the
  archived cell.
- Max \(R_W\) on the packed/bunched prefixes is \(7\) at both
  \(n\sim 10^2\) and \(n\sim 10^6\). Falsifier of
  \(R_W\le C\log n\) growth in this window.

## Formalization

None. No `InverseWidth.lean`. Paper A is unchanged.
Do not formalize the sample table.

## Results

- **Thin occupied hull** — **COMPUTATIONALLY VERIFIED**
  (`inverse_width/summary.json`): `occupied_thin=true`.
- **Archived inverse death** — **COMPUTATIONALLY VERIFIED**.
  `unarchived_deaths=0`; modal tag `empty_ooe`;
  `same_ooe_prefix_death_span=0` at \(y=10^6+1\).
- **No scale law** — **COMPUTATIONALLY VERIFIED**.
  `scale_growth=false`.
- **No leftover-killer.**

## Open questions

None from inverse-width. Do not open a Level-4 near-convergent
theorem, a \(K=11\) proof, or \(L=55293\). The slogan
“symbolic admissibility \(\not\Rightarrow\) integer
realizability” remains true and is already the archived
\(OOE\) cell.

## Decision

**CLOSE**. The inverse tube of a near-convergent two-type
prefix is the existing \(OOE\) predecessor cell, composed.
A real hull thinner than one can still hold an integer, so
width is a relaxation of the fibre already recorded as
`odd_preimage_unique` / `ooe_cell` / \(243<256\). Every tested
finance-admissible ordering dies at that same archived tag;
contracting controls do not empty; \(R_W\) is flat in scale.
No Paper A edit, no ledger row, no Lean, no \(N_0\) raise.

Best next question: none from inverse-width.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on an
inverse-width refinement; not a second manuscript and not a
Paper A edit.
