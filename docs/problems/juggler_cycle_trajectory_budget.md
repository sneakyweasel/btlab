# Juggler global orbit-budget coupling

Status: **ARCHIVED**

Refinement of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md)
and the named Section 5 state-distribution program in
[juggler_cycle_finance.md](juggler_cycle_finance.md),
not a new paper. After realizable-prefix finance closed, this
phase asks whether *one closed integer orbit* forces a strict
integrality gap

\[
C_{\max}(L,n)
<
\texttt{budget_rhs}
\]

because the cheap/expensive valley multiset of the \(6/5\)
extremizer must be realized together.

Not a prefix tax, not a return-cost coupling, not an
inverse-width reopen, not a \(K\le 20\) proof, not CUDA, not
a floor raise, and not a halt theorem.

## Problem

Theorem 4.7 maximises \(\sum 1/(x_i\log x_i)\) over an
adversarial bag of individually legal valleys:
\(o-e\) cheap `OOE` starts at \(n\) and \(2e-o\) expensive
`OE` starts at \(n^{4/3}\). A genuine cycle is one integer
orbit. Can that orbit simultaneously realize the whole
multiset while returning to \(n\)?

## Exact statement

Write \(C_{\mathrm{relax}}=\texttt{budget_rhs}\) and

\[
C_{\max}(L,n)
=
\max\{\,C:\text{globally joined integer valley itinerary
at }(L,o_{\min},n)\,\}.
\]

A node is \((v,a,o_{\mathrm{left}},e_{\mathrm{left}},C,
\text{closure hull})\). The next landing is the realized
`excursion_map`, not an independent height draw. Optimistic
remainder is the Theorem 4.7 packing of the leftover counts
at CycleMin \(n\) (later valleys may return to \(n\)-scale).

**Small-circuit oracle (COMPUTATIONALLY VERIFIED).**
On odds in \([11,79]\) with \(e\le 4\), the B&B maximum
matches the brute \(F_a\)-chain maximum. No closed chain.

**Calibration is not a falsifier (COMPUTATIONALLY
VERIFIED).**
After the realized cheap heads, \(C_{\mathrm{used}}+C_{\mathrm{remain}}\ge\theta\):
\(365\) completes four `OOE`; \(1000057\) completes two.
Local cheap chains do not spend the packed-to-\(\theta\)
slack, as already recorded by realizable-prefix finance.

**No complete itinerary at the leftover
(COMPUTATIONALLY VERIFIED).**
At \((L,o,n)=(25781,16266,10^6+1)\) the bounded search
visits \(15\) `OO`-legal starts, \(24\) nodes, maximum
\(1\) circuit, and zero returns. \(C_{\max}^{\mathrm{ub}}\)
equals `budget_rhs` \(\approx 5.89\cdot 10^{-4}\).
\(\theta\approx 2.55\cdot 10^{-5}\). Partial finance is
tiny because the orbit dies; that is follow depth, not a
new price.

**Deaths are archived cells (COMPUTATIONALLY VERIFIED).**
Prune tags are `empty_ooe`, `cyclemin`, and
`shared_ooe_prefix`, plus a remainder-contracting tail
after a deep first odd run. Backward \(a=1,2\) preimages
of \(n\) sit below CycleMin or empty the `OOE` fibre.
This is almost-search / ordered-excursion / unique visit,
not a global joining law.

**Leftover-killer (REFUTED).**
\(C_{\max}(25781,10^6+1)<\theta\) as a new orbit-budget
gap is false. The admissible upper bound is the packed
RHS. Reading \(C_{\mathrm{partial}}<\theta\) as a kill
rewrites follow depth.

No cycle of any length — not claimed.

## Current literature

- Run-type packing, \(N_{\mathrm{cheap}}=o-e\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md));
  cyclic leftover-killer **REFUTED**
- Realizable-prefix finance —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_realizable_finance.md](juggler_cycle_realizable_finance.md))
- Return-cost coupling, \(N_{\mathrm{sep}}=2324\) —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_valley_coupling.md](juggler_cycle_valley_coupling.md))
- Finance-conditioned closure, lose \(6532\) cheap starts —
  **CLOSE**
  ([juggler_cycle_conditioned_closure.md](juggler_cycle_conditioned_closure.md))
- Pair-level hulls; backward empty `OOE`; follow \(\le 11\) —
  **CLOSE**
  ([juggler_cycle_closure.md](juggler_cycle_closure.md),
  [juggler_cycle_almost_search.md](juggler_cycle_almost_search.md))
- Finance-extremizer discrepancy; inverse-width —
  **CLOSE** / **REFUTED**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-killer; the
search is a reparameterization of archived first-block
cells plus the Theorem 4.7 remainder.

## Branch budget

```text
Mathematical target     Does one closed integer orbit force
                        C_max(L,n) < budget_rhs, strictly, because
                        the 6/5 cheap/expensive valley multiset must
                        be realized together? Decisive test:
                        C_max(25781, 10^6+1) ?< θ.
Novelty hypothesis      The finance extremizer is an adversarial
                        bag of individually legal valleys. A genuine
                        cycle is one T-orbit. That domain change
                        produces an integrality/closure gap δ(L,n),
                        not another local cell tax.
Falsifier               C_max ≥ θ at the floor; or the “polytope”
                        is Theorem 4.7 / valley_coupling / closure
                        / empty-OOE / follow-depth rewritten; or
                        365 and 1000057 already realize the
                        extremal multiset at this scale (they do
                        not: 4+1 and 2 OOE are local).
Existing machinery      budget_rhs, run_type_counts, oe_start_min,
                        inv_log; o_min_and_theta; excursion_map;
                        first_last_cells / word_independent_hull;
                        follow_word; f_coarse; deficit_row
                        (k_lose=6532, P/θ≈23.12); odd_preimage
Maximum Phase-0 scope   Define C vs C_relax; certify B&B on small
                        circuit counts; one bounded L=25781 search
                        at n=10^6+1. No 2^L, no CUDA, no CLI, no
                        Lean, no Paper A, no N0 raise, no 55293.
Promotion criterion     A reusable gap
                        Σ c_i ≤ packed − δ(L,n)
                        coming from global orbit closure, with
                        C_max(25781,10^6+1) < θ, or a recorded
                        globally realizable extremizer that is not
                        the independent packing.
Stop criterion          Relaxation still meets packed or θ; gap is
                        an archived cell / unique visit / 9/8
                        return; search is follow-depth rewritten;
                        or node-bound with neither bound nor
                        witness (then PARK, do not add CUDA).
```

## Closed-bridge gates

Classify the first output before any follow-up. Do not reopen
the boxed hybrids already **REFUTED** as
`juggler_cycle_realizable_finance`,
`juggler_cycle_valley_coupling_leftover_killer`,
`juggler_cycle_closure_leftover_killer`, or
`juggler_cycle_almost_search`.

- **PROMOTE** if \(C_{\max}<\theta\) and the prune reason is
  accumulated orbit closure, not an archived first-block cell.
- **CLOSE** if a complete (or hull-closed) itinerary has
  \(C\ge\theta\). Record the extremizer.
- **CLOSE** if the bound equals packed, or the tree dies only
  at empty `OOE` / follow \(\le 11\) / one-step \(9/8\) /
  CycleMin.
- **PARK** if the node cap hits with neither bound nor witness.
  Do not add CUDA in the same phase.

Do **not** raise \(N_0\). Do **not** open \(L=55293\).
Do **not** edit Paper A. Do **not** reopen prefix
realizability, inverse-width, or defect correlation.

## Explicitly out of Phase-0

Prefix realizability, inverse-width, defect correlation,
\(K\le 20\), the \(1054k\) family, \(L=55293\), floor raise,
\(2^L\) words, Pareto/CLI UI, ledger row, Lean, CUDA,
Paper A §5 rewrite.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(C_{\mathrm{relax}}=\texttt{budget_rhs}\) —
  **KNOWN** (Theorem 4.7)
- Small-e B&B versus brute \(F_a\)-chains —
  **COMPUTATIONALLY VERIFIED**; they match
- Calibration \(C_{\mathrm{used}}+C_{\mathrm{remain}}\ge\theta\)
  after \(365\) / \(1000057\) cheap heads —
  **COMPUTATIONALLY VERIFIED**; not a falsifier
- \(C_{\max}^{\mathrm{ub}}(25781,10^6+1)\) —
  **COMPUTATIONALLY VERIFIED**; equals packed
- Partial \(C<\theta\) —
  **REPARAMETERIZATION** of follow depth
- Trajectory-budget leftover-killer —
  **REFUTED** (`juggler_cycle_trajectory_budget`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_trajectory_budget`
- Dataset: `data/research/juggler/cycle_finance/orbit_budget/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_trajectory_budget.py`
- Window: small-e oracle \(e\le 4\) on odds \(11\ldots 79\);
  calibration \(\{365,1000057\}\); bounded B&B at
  \((L,n)=(25781,10^6+1)\), node cap \(20000\), fifteen
  `OO`-legal starts, backward \(a\in\{1,2\}\) as a fibre
  census. Fast suite reads the artifact and does not rerun
  the science search. No CLI. No Lean. No \(N_0\) raise.

## Conjectures

`juggler_cycle_trajectory_budget` — **REFUTED**.

## Counterexamples

- \(C_{\max}^{\mathrm{ub}}(25781,10^6+1)=\texttt{budget_rhs}\).
  Falsifier of a strict integrality gap at the leftover.
- Deaths are `empty_ooe` / `cyclemin` / `shared_ooe_prefix`
  after at most one circuit. Falsifier of a global joining
  law that is not an archived cell.
- \(365\) (four `OOE`) and \(1000057\) (two `OOE`) still
  have \(C_{\mathrm{used}}+C_{\mathrm{remain}}\ge\theta\).
  Not a falsifier of the conjecture; recorded as the
  required calibration.

## Formalization

None. No `OrbitBudget.lean`. Paper A is unchanged.
Do not formalize the sample table.

## Results

- **Oracle** — **COMPUTATIONALLY VERIFIED**
  (`orbit_budget/summary.json`): `match=true`.
- **Calibration** — **COMPUTATIONALLY VERIFIED**.
  `calibration_above_theta=true`.
- **Science run** — **COMPUTATIONALLY VERIFIED**.
  `gap_kind=archived_cell`; `C_max_ub_lt_theta=false`;
  `complete=false`; `max_circuits=1`; \(24\) nodes, not
  capped.
- **Charge** — does not kill \(25781\) at the published floor.
- **No leftover-killer.**

## Open questions

None from orbit-budget. Do not open a CUDA search, a
\(K=11\) proof, or \(L=55293\). The Section 5 program
stays **PARK**: every tested joining constraint dies at
an archived cell or restores Theorem 4.7.

## Decision

**CLOSE**. Changing the feasible set from independent
valleys to a single integer orbit does not produce a
certified \(\delta\). The admissible upper bound at
\(n=10^6+1\) is still `budget_rhs`. Every exhausted branch
dies at an archived `OOE` / CycleMin / shared-prefix tag
after at most one circuit; reading the tiny partial sum as
\(C_{\max}<\theta\) rewrites follow depth. Calibration
heads stay above \(\theta\) because the remainder is
allowed to return to \(n\)-scale. No Paper A edit, no
ledger row, no Lean, no CUDA, no \(N_0\) raise.

Best next question: none from orbit-budget. The
state-distribution program of Paper A Section 5 stays
**PARK**.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on the
Section 5 program; not a second manuscript and not a
Paper A edit.
