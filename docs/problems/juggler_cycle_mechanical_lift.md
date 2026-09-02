# Juggler exact mechanical-lift obstruction

Status: **ARCHIVED** (Phase 0 decided)

Successor of the completed walk-finance programme
([juggler_cycle_walk_fan_minimum.md](juggler_cycle_walk_fan_minimum.md)).
It asks whether the information discarded by the exponent-walk
relaxation — the exact position of the integer state inside its
floor-power cell — induces a Juggler-specific cyclic obstruction
on survivor-quality hug / IET words. Not a halt theorem, not a
floor raise, not a finance reopen, and not a Paper A edit.

## Problem

The greedy mechanical word is feasible as an exponent walk
(\(u_k\ge 0\)). Isolated cell positions are unrestricted, and
one-step floor cells are already classified. Does the exact
Juggler map still force a transported law on the within-cell
coordinate \(\xi\) whose cyclic closure \(\xi_L=\xi_0\) fails
for sufficiently good survivor itineraries?

## Exact statement

Write \(\xi=\rho/(2T+1)\in[0,1)\) for the existing normalized
cell position (`cell_record`). Pair it with the hug / IET height
\(u_k=\alpha a_k-k\), \(\alpha=\log_2(3/2)\).

**Relaxed mechanical feasibility (COMPUTATIONALLY VERIFIED).**
The IET hug equals `hug_word` at \(L=19,84,1054\). Streamed
through \(L=16785921\) (fan B) it stays in
\([0,1+\alpha)\) and factors as \(\mathtt{OOE}/\mathtt{OE}\)
only (\(n_{\mathrm{other}}=0\)). This is the already-identified
walk maximizer, not a new finance identity.

**No scale-stable \(\xi\)-cocycle (COMPUTATIONALLY VERIFIED).**
On \(1223\) exact \(\mathtt{OOE}\) realizers and \(2529\)
\(\mathtt{OE}\) realizers in \([13,8001)\cup[10^6+1,10^6+2001)\),

\[
\mathrm{corr}(\xi_{\mathrm{in}},\xi_{\mathrm{out}})
\in\{0.019,0.021\},
\qquad
\frac{\mathrm{Var}_{\mathrm{bin}}(\xi_{\mathrm{out}})}
{\mathrm{Var}(\xi_{\mathrm{out}})}
\approx 0.995,
\]

and same-\(\xi_{\mathrm{in}}\) buckets have
\(\xi_{\mathrm{out}}\)-range \(\approx 1\). Nearby starts
\(1000001,1000003\) share the \(\mathtt{OE}\) landing \(31622\):
\(\xi_{\mathrm{out}}\) is a function of the image integer, not
of \((u,\xi_{\mathrm{in}})\). Composition of \(\Phi_{\mathtt{OOE}}\)
and \(\Phi_{\mathtt{OE}}\) was skipped: there is no scale-stable
\(\Phi\).

**Even \(\xi\) is inert; odd \(\xi\) is not free
(COMPUTATIONALLY VERIFIED / archived).**
All even occupants of \([q^2,(q+1)^2)\) map to \(q\)
(\(q=10,20,100\)). Odd cells through \(m=200\) have at most one
integer (\(166\) empty, \(35\) singleton). These are
`preimage_same_next_state` and `odd_preimage_unique`.

**Hug concatenations are SCALE_HUG, not a \(\xi\) law
(COMPUTATIONALLY VERIFIED / archived).**
Hug(\(19\)) is `OOEOOEOOEOEOOEOOEOE` and contains \(\mathtt{OOEOE}\).
After \(\mathtt{OOE}\) the landings \(365\to 763<2609\),
\(1517\to 3789<17431\), \(1000057\to 5623773<100007601\) sit
below `oe_start_min`. That is the cyclic-valley fact
\(n^{9/8}<n^{4/3}\), not a cell-position obstruction.

**Three classes.**

- Relaxed walk: feasible at every tested length, including both
  survivor fans.
- Actual integer lifts: max follow depth \(13\) on hug(\(19\))
  and hug(\(84\)) (mean \(\approx 2\)); zero complete followers.
  Controls \(365,1517,1000057,1016445\) follow \(10,13,7,3\)
  letters. Numerical absence is not a theorem.
- Cell-feasible inverse hulls: hug(\(19\)) dies at `empty_ooe`
  (\(k=5\) on \(y=11,101,1001\)); the length-\(18\) hug(\(84\))
  prefix dies at `empty_odd_cell` / `empty_oe`. Tagged
  `LOCAL_CELL`.

**Better approximation does not shrink the \(\xi\)-set
(COMPUTATIONALLY VERIFIED).**
Slope gaps at \(L=19,84,1054\) are
\(6.5\cdot 10^{-4}\), \(2.3\cdot 10^{-5}\), \(3.8\cdot 10^{-8}\);
max follow depths are \(13,13,10\). Inverse death remains the
archived one-step cells. Hypothesis 3 fails.

No cycle of any length — not claimed.

## Current literature

- Fan-minimum / walk-finance terminal reduction —
  **PROMOTE** / **CONJECTURE**
  ([juggler_cycle_walk_fan_minimum.md](juggler_cycle_walk_fan_minimum.md))
- Hug = IET prefix, unique prefix-min walk —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_greedy.md](juggler_cycle_walk_greedy.md),
  [juggler_cycle_walk_exchange.md](juggler_cycle_walk_exchange.md))
- Interleaved \(\mathtt{OOE}/\mathtt{OE}\) is CycleMin-illegal
  at the floor (\(9/8<4/3\)) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_cyclic_valley.md](juggler_cycle_cyclic_valley.md))
- Isolated cell position unrestricted; even-cell position inert —
  **COMPUTATIONALLY VERIFIED** /
  **REPARAMETERIZATION**
  ([juggler_cycle_remainder_finance.md](juggler_cycle_remainder_finance.md),
  [juggler_floor_boundary.md](juggler_floor_boundary.md))
- Inverse death is the archived empty \(\mathtt{OOE}\) cell —
  **REFUTED** as a new leftover-killer
  ([juggler_cycle_inverse_width.md](juggler_cycle_inverse_width.md),
  [juggler_cycle_almost_search.md](juggler_cycle_almost_search.md))
- Transported remainders unroll to \(\Delta_w\) —
  **REPARAMETERIZATION**
  ([juggler_cycle_error_transport.md](juggler_cycle_error_transport.md),
  [juggler_cycle_defect_congruence.md](juggler_cycle_defect_congruence.md))
- `odd_preimage_unique` / `preimage_same_next_state` —
  **EXACT — LEAN VERIFIED**
- Every start reaches 1 — not claimed

Project relationship: **independent** (tests the discarded
within-cell coordinate; does not reopen finance). The surviving
statements are archived reparameterizations.

## Branch budget

```text
Mathematical target     Does the greedy mechanical word induce a
                        scale-stable transported law on the exact
                        within-cell coordinate ξ such that cyclic
                        ξ-closure fails, using information not
                        already in (L,o), 3^o/2^L, Δ_w, finance,
                        one-step cells, IET charge, or DK/Ostrowski?
Novelty hypothesis      The integer Juggler map is a skew product
                        (u,ξ)↦(u',Ξ_σ(u,ξ)) whose cheap-excursion
                        maps Φ_OOE, Φ_OE have no periodic lift on
                        sufficiently good survivor itineraries
Falsifier               Ξ is not a function of (u,ξ); or Φ has a
                        cyclic fixed point / nonempty invariant
                        interval; or every emptiness is LOCAL_CELL,
                        INERT_EVEN, SCALE_HUG, or DEFECT_REPARAM
Existing machinery      hug_word, o_min_and_theta, cell_record pos
                        (already ξ=ρ/(2T+1)), follows_itinerary,
                        excursion_map, inverse_walk, controls
                        365/1517/1000057/1016445; cyclic_valley
                        (OE after OOE at 9/8<4/3); remainder_finance
                        (isolated pos unrestricted); inverse_width
                        (death is empty OOE); error_transport (Δ_w)
Maximum Phase-0 scope   One probe, one dossier, one conjecture, one
                        artifact, fast tests. No DP, no floor, no
                        Paper A, no Lean, no CLI, no ledger row
Promotion criterion     A Juggler-specific multi-seam ξ law that
                        survives large CF quotients, is not finance
                        or one-cell residue, and contradicts
                        ξ_L=ξ_0. Numerical absence of integer
                        followers is not enough
Stop criterion          ξ constraints independently satisfiable;
                        cocycle has a fixed point; repeated cheap
                        excursions close; or the finding reduces
                        to an archived identity
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers; \(\xi\)
is the existing floor-cell coordinate.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exact \(\xi=\rho/(2T+1)\) —
  **REPARAMETERIZATION** of `local_defect` / `cell_record`
- Hug / IET walk \(u\in[0,1+\alpha)\) —
  **COMPUTATIONALLY VERIFIED** (already the walk maximizer)
- Scale-stable \(\Xi_\sigma(u,\xi)\) —
  **REFUTED** (uncorrelated scatter)
- CycleMin lift of hug concatenations —
  **REPARAMETERIZATION** of cyclic-valley SCALE_HUG
- Inverse emptiness of hug itineraries —
  **REPARAMETERIZATION** of `empty_ooe` / `odd_preimage_unique`
- Better \(o/L\) \(\Rightarrow\) smaller admissible \(\xi\)-set —
  **REFUTED** (follow depths flat)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_mechanical_lift`
- Artifacts: `data/research/juggler/cycle_mechanical_lift/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_mechanical_lift.py`

No CLI. No new Lean. Paper A is unchanged. The walk-charge DP
is not edited. \(\Phi\)-composition on \(L\ge 1054\) was not
run: Hypothesis 1 produced no scale-stable map.

## Conjectures

`juggler_mechanical_lift_obstruction` — **REFUTED**. The optimal
mechanical exponent word has no exact integer lift for a reason
that is a new \(\xi\)-cocycle / cyclic cell-position law. False:
every obstruction in the census is `INERT_EVEN`, `UNIQUE_ODD`,
`UNCORRELATED`, `SCALE_HUG`, or `LOCAL_CELL`.

## Counterexamples

- \(\mathtt{OE}\) starts \(1000001,1000003\) have
  \(\xi_{\mathrm{in}}\in\{0.00037,0.00337\}\) and the same
  landing \(31622\): \(\xi_{\mathrm{out}}\) ignores \(\xi_{\mathrm{in}}\).
- Even cell \(q=10\): eleven even occupants, one image, \(\xi\)
  ranges over \([0,0.95]\).
- \(365\xrightarrow{\mathtt{OOE}}763<2609=\mathtt{oe\_start\_min}(365)\).
- Hug(\(19\)) inverse at \(y=101\) dies at `empty_ooe`, \(k=5\).

## Formalization

None. No `MechanicalLift.lean`, no `sorry`. Paper A is unchanged.
Not a halt theorem. No ledger row: the statements are archived
reparameterizations.

## Results

Classification **MECHANICAL_LIFT_CLOSED**.

- IET hug \(=\) `hug_word` at \(19,84,1054\)
- Walk feasible on both fans; \(L=16785921\) is
  \(4395553\) \(\mathtt{OOE}\) \(+\) \(1799631\) \(\mathtt{OE}\)
- \(\xi\)-cocycle uncorrelated; \(\Phi\) composition skipped
- Max integer follow depth \(13\); zero complete lifts
  (observation, not a theorem)
- Inverse death is `LOCAL_CELL`
- Hypothesis 3 fails
- Tags: `INERT_EVEN`, `UNIQUE_ODD`, `UNCORRELATED`,
  `SCALE_HUG`, `LOCAL_CELL`

The boxed distinction stands:

- relaxed mechanical feasibility: yes
- exact integer liftability: no new cyclic-\(\xi\) obstruction

## Open questions

None on this coordinate. \(\xi\) is not a dynamical input of
the exact map. Do not reopen finance, Baker, DK sharpness,
Christoffel leftover-cells, seam propagation, or floor campaigns
from this CLOSE.

## Decision

**CLOSE.** The Phase-0 falsifier fired: there is no scale-stable
skew product on \((u,\xi)\), repeated cheap excursions do not
induce a well-defined \(\Phi_{\mathcal E}\), and every exact
emptiness in the census is an archived identity (inert even
cell, unique odd cell, cyclic-valley scale, empty \(\mathtt{OOE}\)
cell). Isolated \(\xi\) remains independently satisfiable.
Numerical absence of hug(\(19\)) followers is not promoted.
The walk-finance programme stays closed; this branch does not
reopen it.

Best next question: none in laboratory scope on the cell-position
coordinate — the exact map's fibres remain parity plus interval.

## Publication assessment

Status: `ARCHIVED`.

A finite, tagged elimination of the exact-lift slogan for the
mechanical word. The useful output is the distinction between
relaxed hug / IET feasibility and exact integer liftability,
together with the observation that \(\xi\) does not transport.
Not a paper candidate and not a halt theorem.
