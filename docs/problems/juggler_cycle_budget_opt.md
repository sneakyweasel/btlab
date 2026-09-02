# Juggler cycle-finance budget optimization

Status: **ABSORBED** (Paper A Theorems 4.7--4.8 and Proposition 4.9)

Refinement of
[juggler_cycle_finance.md](juggler_cycle_finance.md), not a new
paper. It asks whether minimum uniqueness, odd-run type, and the
cycle maximum force a strictly smaller length-only error budget
than parity finance on \(\mathcal E_{\mathrm{par}}(10^6)\). Not a
halt theorem, not a leftover-itinerary census, and not a floor raise.
Paper A now prints the packing and the lattice.

## Problem

Parity finance charges every valley at the `CycleMin` start \(n\).
A cycle cannot put an `OE`-start at \(n\): the next state is even
and below \(n^2\). Does the exact transition geometry — unique
visit of \(n\), the `OE`/`OO` split forced at \(o_{\min}\), and a
bound on the maximum — cut the global floor-error sum enough to
shrink the leftover set?

## Exact statement

**\(n\)-circuit even cap (EXACT — HUMAN PROOF).**
A `CycleMin` circuit starting at \(n\) with \(k\) odds and
\(\ell\) evens lands at most \(n^{3^k/2^{k+\ell}}\) (floors only
make the landing smaller). The landing is \(\ge n\) only if
\(3^k\ge 2^{k+\ell}\). In particular \(k=1\) is impossible from
\(n\), and a \(k=2\) circuit can take only \(\ell=1\) (`OOE`).

**`OE`-start height (EXACT — HUMAN PROOF).**
A length-1 odd-run is followed by an even state, so
`cycleMin_even_ge_sq` gives \(T(v)\ge n^2\), hence
\(v^3\ge n^4\). The least such odd \(v\) is `oe_start_min(n)`.

**Run-type packing (EXACT — HUMAN PROOF).**
At \(o=o_{\min}(L)\) one has \(o-e<e\), so every internal odd can
sit at \(t=\lfloor n^{3/2}\rfloor\). The largest number of
\(n\)-valleys compatible with the even cap is \(o-e\) copies of
`OOE`. The remaining \(2e-o\) circuits are `OE` from
`oe_start_min(n)`. Unique visit of \(n\) (prefix return) puts the
other \(o-e-1\) low valleys at \(n+2\). Evens stay at \(n^2\).

**Run-depth exchange (EXACT — HUMAN PROOF).**
Write \(F(a)\) for the coarse odd-run cost of length \(a\)
(start at \(n\) if \(a\ge 2\), at `oe_start_min(n)` if \(a=1\);
internals at \(\tau_j\)). At \(n=10^6+1\) the increments
\(\Delta_a=F(a+1)-F(a)\) decrease, and

\[
F(2)+F(2)\ge F(3)+F(1),\qquad F(2)+F(1)\ge F(3).
\]

The finance maximum among partitions of \(o\) odds into \(e\)
runs is therefore the two-type packing. The relaxed maximum
equals `budget_rhs`.

**Cyclic adjacency (REPARAMETERIZATION / does not bind).**
A cheap `OOE` cannot be followed by `OE`: the one-even landing
is \(\operatorname{isqrt}(T^2(n))\asymp n^{9/8}\), below
`oe_start_min(n)\asymp n^{4/3}\). That is the existing
`power_bound_word` envelope. It does not cap the number of
*non-adjacent* cheap valleys, so \(N_{\mathrm{cheap}}=o-e\)
remains attainable under known constraints.

Hence

\[
\sum_i\frac1{x_i\ln x_i}
\;\le\;
\frac{1}{n\ln n}
+\frac{o-e-1}{(n+2)\ln(n+2)}
+\frac{2e-o}{v\ln v}
+\frac{1}{t\ln t}
+\frac{o-e-1}{t_+\ln t_+}
+\frac{e}{2n^2\ln n},
\]

where \(v=\)`oe_start_min(n)` and \(t_+=T(n+2)\). This is
strictly smaller than the parity sum whenever \(2e-o>0\). Sending
the maximum \(M\to\infty\) removes one even term and does not
change the valley packing.

No cycle of any length — not claimed.

## Current literature

- Length-only parity finance — **EXACT — HUMAN PROOF**
  ([juggler_cycle_finance.md](juggler_cycle_finance.md));
  table at \(N_0=10^6\) is **COMPUTATIONALLY VERIFIED**
  (prefix \(25780\), \(141\) leftovers)
- Unique visit of \(n\) — **REPARAMETERIZATION** of prefix return
  ([juggler_cycle_equal_valleys.md](juggler_cycle_equal_valleys.md));
  \(n+2\) as a leftover-killer is **REFUTED**
- Odd-run height packing — **EXACT — HUMAN PROOF**
  ([juggler_cycle_position_finance.md](juggler_cycle_position_finance.md));
  at \(o_{\min}\) it coincides with parity
- Prefix-weight leftover-killer — **REFUTED**
  (`juggler_cycle_prefix_weight_leftover_killer`)
- `cycleMin_even_ge_sq`, `power_bound_word` — **EXACT — LEAN
  VERIFIED**
- Every start reaches 1 — not claimed

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Optimize the cycle-finance error budget using
                        minimum uniqueness + odd-run depth + maximum
                        excursion, rather than counting low states only
Novelty hypothesis      A cycle cannot simultaneously:
                        (i) concentrate many finance-expensive states
                        near n,
                        (ii) have deep odd runs, and
                        (iii) keep the maximum small.
                        The exact transition geometry forces a strictly
                        smaller global floor-error budget than parity finance.
Falsifier               The parity bound is already extremal: there exist
                        abstract/cyclic state geometries satisfying all
                        known transition constraints whose error sum matches
                        the parity RHS; or the max/run-position constraints
                        give no additional reduction for the 141 survivors.
Existing machinery      cycleMin, AboveAnchor,
                        cycle_min uniqueness/rotation,
                        power_bound_word,
                        log_step_even / log_step_odd,
                        cycleMin_log_envelope,
                        parity_rhs / parity_n_max,
                        floor cells,
                        odd-run structure,
                        known minima/maxima on cycle controls
Maximum Phase-0 scope   Symbolic optimization first; exact integer checks
                        only for the 141 survivors; derive run-depth lower
                        bounds and max-forced states; no new dynamical
                        invariant, no Q-section, no p-adic/residue system,
                        no terminal-cluster reopen
Promotion criterion     A reusable finance theorem of the form
                        Σ_i 1/(x_i log x_i)
                        ≤ F(L,o,n,M,{a_j})
                        with F strictly smaller than parity_rhs for every
                        admissible cycle configuration, yielding a new
                        period cutoff or shrinking E_par(10^6)
Stop criterion          The optimization collapses to parity finance;
                        maximum M can be sent arbitrarily large without
                        changing the extremum; run-depth information can be
                        rearranged to reproduce the same RHS; or only
                        numerical optimization with no exact theorem
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(n\)-circuit even cap \(3^k\ge 2^{k+\ell}\) —
  **EXACT — HUMAN PROOF** (ideal power; floors only help)
- `OE`-start \(v^3\ge n^4\) — **EXACT — HUMAN PROOF**
  (`cycleMin_even_ge_sq`)
- Run-type packing \(o-e\) copies of `OOE` and \(2e-o\) copies of
  `OE` — **EXACT — HUMAN PROOF**
- Unique visit of \(n\) — **REPARAMETERIZATION** (already known)
- Maximum \(M\to\infty\) — does not change the extremum
- Height packing at \(\tau_j\), \(j\ge 2\) — not forced at
  \(o_{\min}\)
- Run-depth exchange \(F(2)+F(2)\ge F(3)+F(1)\) —
  **EXACT — HUMAN PROOF** (this dossier)
- Cheap-`OOE` landing \(\asymp n^{9/8}\) cannot feed `OE` —
  **REPARAMETERIZATION** of `power_bound_word`;
  \(N_{\mathrm{cheap}}=o-e\) still attainable
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_budget_opt`,
  `cycle_run_extremum`, `cycle_prefix_feasibility`
- Dataset: `data/research/juggler/cycle_finance/budget_opt.json`,
  `run_extremum.json`, `prefix_feasibility.json`
- Tests: `tests/research/juggler_sequence/test_cycle_budget_opt.py`,
  `test_cycle_run_extremum.py`,
  `test_cycle_prefix_feasibility.py`
-   Window: the \(141\) parity leftovers at \(n=10^6+1\). Fast suite
  only. No CLI. Lean arithmetic of the leftover lattice is
  `RunSurvivorLattice.lean`.

## Conjectures

None opened.

## Counterexamples

The hypothesis that uniqueness or a bound on \(M\) is the leftover
killer is false: dropping the unique-min split or sending
\(M\to\infty\) does not change which leftovers die. The shrink
comes from the `OE`-start lift.

The hypothesis that cyclic run-depth / adjacency forces
\(S_{\mathrm{exact}}<\texttt{budget_rhs}\) and shrinks the
\(99\) leftovers is **REFUTED**
(`conjectures/refuted/juggler_cycle_run_extremum_leftover_killer.json`).

The hypothesis that a near-convergent leftover has no
prefix-expanding \(O/E\) path is **REFUTED**
(`conjectures/refuted/juggler_cycle_prefix_feasibility_leftover_killer.json`).
See
[juggler_cycle_prefix_feasibility.md](juggler_cycle_prefix_feasibility.md).

## Formalization

The packing inequality is a human proof (Paper A Theorem 4.7).
The \(99\)-list is a verified table (Theorem 4.8). The lattice
arithmetic is `formal/Problems/Juggler/RunSurvivorLattice.lean`
(Proposition 4.9), imported by `Problems.JugglerPaper`. No
`CycleBudgetOpt.lean`: Lean does not prove the packed comparison.

## Results

- **Run-type finance** — **EXACT — HUMAN PROOF**. At
  \(n=10^6+1\), \(L=25781\): parity RHS \(\approx 8.27\cdot 10^{-4}\),
  packed RHS \(\approx 5.89\cdot 10^{-4}\) (factor \(23\) above
  \(\theta\approx 2.55\cdot 10^{-5}\)). Unique-min and
  \(M\to\infty\) change the seventh significant digit.
- **Leftover shrink** — **COMPUTATIONALLY VERIFIED**
  (`budget_opt.json`): \(42\) of the \(141\) leftovers die,
  namely \(56347+1054k\) for \(k=0,\ldots,41\). First survivor
  remains \(25781\). \(L=55293\) still lives
  (\(\theta\approx 1.247\cdot 10^{-3}\) versus
  RHS \(\approx 1.262\cdot 10^{-3}\)).   \(99\) leftovers remain.
  Every leftover has packed RHS strictly below parity. Climb
  packing at \(\tau_1\) holds for all \(141\). Dropping the max
  even term does not change the kill list. The \(99\) are three
  affine families of difference \(1054\) on the unimodular
  basis \((25781,16266)\), \((1054,665)\); the \(42\) deaths
  continue \(F_1\) past \(b=28\). See
  [juggler_run_survivor_lattice_note.md](../theory/juggler_run_survivor_lattice_note.md).

- **Cyclic run-type extremum** — **COMPUTATIONALLY VERIFIED**
  (`run_extremum.json`): on all \(99\) run-type survivors the
  two-type packing is the relaxed maximum and matches
  `budget_rhs`. Deepening one `OOE` or merging two `OOE` into
  `OOO`+`OE` strictly lowers the odd-state sum. Level C does
  not drop \(N_{\mathrm{cheap}}\) below \(o-e\) and excludes
  none of the \(99\).

- **Prefix-expansion feasibility** — **COMPUTATIONALLY VERIFIED**
  (`prefix_feasibility.json`): every one of the \(99\) leftovers
  admits the extremal path \(o_k=r(k)\) and the ceiling
  Christoffel word of slope \(o_{\min}/L\). Both start `OOE`
  with first isolated-`OE` count \(0\). No leftover dies.
  Separate dossier:
  [juggler_cycle_prefix_feasibility.md](juggler_cycle_prefix_feasibility.md).

## Open questions

None from cyclic run packing. The necklace
\((\mathtt{OOE})^{o-e}(\mathtt{OE})^{2e-o}\) is not a feasible
consecutive itinerary, but that is the existing envelope: other cheap
valleys may still sit at \(n+2\). Do not reopen extremal
scale composition.

## Decision

**PROMOTE**. The run-type bound is not a reparameterization of
parity finance: it replaces \(2e-o\) valleys at \(n\) by valleys
at \(n^{4/3}\), using only `cycleMin_even_ge_sq` and the ideal
power cap on \(n\)-circuits. It shrinks
\(\mathcal E_{\mathrm{par}}(10^6)\) from \(141\) to \(99\). The
period cutoff stays \(25780\). Uniqueness and the maximum do not
bind. Paper A prints the parity table as Theorem 4.6 and the
run-type leftover with the lattice as Theorems 4.7--4.8 and
Proposition 4.9. Not a halt theorem.

The cyclic run-type leftover-killer is **CLOSE**
(`juggler_cycle_run_extremum_leftover_killer`). Two-type is
already the relaxed finance maximum. Cheap-`OOE` adjacency is
`power_bound_word` and does not prove \(N_{\mathrm{cheap}}<o-e\).
No leftover among the \(99\) dies. Keep the exchange lemma as
negative knowledge. The leftover set and its lattice are in
Paper A; the cyclic leftover-killer is not.

The prefix-expansion leftover-killer is **CLOSE**
(`juggler_cycle_prefix_feasibility_leftover_killer`). The
extremal path \(o_k=r(k)\) realises every leftover, including
\(25781\) and \(55293\). Prefix constraints collapse to the
endpoint plus \(a_0\ge 2\). No leftover among the \(99\) dies.

Exact pair-level floor closure is **CLOSE**
(`juggler_cycle_closure_leftover_killer`). Word-independent
intervals are the exponent envelope. No leftover \((L,o)\)
dies.

Exact modular floor-cell closure is **CLOSE**
(`juggler_cycle_mod_closure_leftover_killer`). Cycle-scale
\(R_{\mathrm{nec}}\) is first-letter parity; every listed
modulus has a diagonal on \(L=25781\) and \(L=55293\).

Finance-conditioned exact closure is **CLOSE**
(`juggler_cycle_conditioned_closure_leftover_killer`). Leftover
\(\theta\) does not force the `OOE`/`OE` packing. Deepening
every `OE` still leaves packed \(>\theta\). No leftover
\((L,o)\) dies.

Ordered excursion closure is **CLOSE**
(`juggler_cycle_ordered_excursion_leftover_killer`). The
two-block persistence \((2,2,1)\) at \(v=n\) is the composed
OOE envelope. No leftover \((L,o)\) dies.

Correlated floor-defect finance is **CLOSE**
(`juggler_cycle_defect_correlation_leftover_killer`). Realized
`OE`/`OO` pairs occupy both cheap and finance-maximal cell
corners. Pair-finance gap \(0\). No leftover \((L,o)\) dies.

Cross-excursion usable-loss persistence is **CLOSE**
(`juggler_cycle_loss_persistence_leftover_killer`). CycleMin-scale
pairs reach \(\max\min(U_0,U_1)=0.9767\) and
\(\max(U_0+U_1)=1.968\). `OOE` near-top events cluster. No
leftover \((L,o)\) dies as a theorem.

Near-top defect anti-clustering is **CLOSE**
(`juggler_cycle_defect_anticluster`). Same-pair near-top
occurs at \((0.9976,0.99989)\); \(f(0.995)=0.99996\). No leftover
\((L,o)\) dies.

Best next question: none from cyclic run packing, prefix
expansion, exact pair-level closure, low-order modular
closure, finance-conditioned closure, ordered excursion
closure, correlated floor-defect finance, cross-excursion
usable-loss persistence, or two-step
defect anti-clustering. The frontier
leftover \(L=25781\) still has a factor-\(23\) valley gap at
\(P=1\).

## Publication assessment

Status: `ABSORBED`. Laboratory refinement of the finance
dossier; the packing and lattice are Paper A Theorems 4.7--4.8
and Proposition 4.9. Not a second manuscript.
