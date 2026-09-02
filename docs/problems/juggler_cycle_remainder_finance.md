# Juggler finance-weighted floor-remainder control

Status: **ARCHIVED**

Refinement of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md) and
[juggler_floor_boundary.md](juggler_floor_boundary.md),
not a new paper. It asks whether CycleMin-legal square/cube-cell
positions are forced away from the top often enough to shrink the
run-type budget on \(\mathcal E_{\mathrm{run}}(10^6)\).
Not a halt theorem, not a leftover-itinerary census, not a new period
identity, not Fourier, not a \(Q\)-return, and not a residue /
\(p\)-adic system.

## Problem

The run-type bound charges every step at the top of its dyadic
cell, \(\log z\le 2\log(y+1)\). Can the normalized remainders of
finance-relevant odd and even steps stay that high, or does exact
cell geometry cut the usable floor loss?

## Exact statement

Write \(T\) for the image and \(\rho\) for the local defect. The
cell width is \(2T+1\), and

\[
\mathrm{pos}(x)=\frac{\rho(x)}{2T(x)+1}\in[0,1).
\]

The usable fraction of the cell-top logarithm is

\[
\mathrm{usable}(x)
=
\frac{\log\bigl(1+\rho/T^2\bigr)}{2\log(1+1/T)}.
\]

These are **REPARAMETERIZATION**s of `local_defect` plus
`log_le_two_log_add`. On a finance window they agree to many
digits: \(\mathrm{usable}\approx\mathrm{pos}\).

Even terms sit at \(n^2\) and do not move \(\mathcal E_{\mathrm{run}}(10^6)\).
The budget is paid at odd valleys. A uniform factor
\(\mathrm{pos}\le 0.988\) would be needed to kill \(L=55293\)
(\(P/\theta\approx 1.012\)). \(L=25781\) would need
\(\mathrm{pos}\le 0.043\).

**No uniform cut (COMPUTATIONALLY VERIFIED).**
In \([10^6+1,10^6+20001)\) there are \(5045\) `OOE`-legal odds.
The mean usable is \(0.492\). The maximum is \(0.9999737\) at
\(n=1016445\) (`OOE`-legal, \(T\) odd). Sixty-two starts have
\(\mathrm{pos}\ge 0.988\). Fifty-six have \(\mathrm{pos}\ge 0.99\).
The same window has even landings with \(\mathrm{pos}=0.99989\).
At the `OE` scale \(n^{4/3}\) the maximum odd position is
\(0.99996\).

A mean-usable factor \(0.492\) would exclude \(49\) of the \(99\)
survivors, including \(55293\). That average is not a `CycleMin`
theorem: the same window already contains near-top witnesses, and
the run-type adversary may sit on those starts. The observed
maximum as a uniform factor excludes nobody.

No cycle of any length — not claimed.

## Current literature

- `log_le_two_log_add` / `log_step_even` / `log_step_odd` /
  `cycleMin_finance` —
  **EXACT — LEAN VERIFIED**
- Run-type packing, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- \((e,u)\) cell coordinates —
  **REPARAMETERIZATION**
  ([juggler_floor_boundary.md](juggler_floor_boundary.md));
  even-cell position is inert for \(J\)
- Cyclic remainder balance / all-zero rigidity —
  **EXACT — LEAN VERIFIED**
  ([juggler_cycle_rounding.md](juggler_cycle_rounding.md));
  not a finance cut
- Pair-level and ordered-block closure —
  **CLOSE**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-pair killer;
normalized position is a **REPARAMETERIZATION** of the existing
cell-top bound.

## Branch budget

```text
Mathematical target     Finance-weighted floor-remainder control:
                        can a CycleMin orbit realize enough near-top
                        cell remainders to pay the surplus of a
                        finance-surviving period?
Novelty hypothesis      Finance-relevant even/odd remainders cannot
                        stay near the top of their cells often
                        enough to support budget_rhs
Falsifier               Remainders can be arbitrarily close to the
                        top in every finance-relevant class; the
                        6/5 / run-type RHS stays attainable; or the
                        quantity is local_defect rewritten
Existing machinery      cycleMin_finance; budget_rhs; log_step_*;
                        exact cells; local_defect; E_run(10^6);
                        L=25781 and 55293
Maximum Phase-0 scope   Remainder geometry only. Normalized
                        positions on OOE/OE classes near n=10^6+1
                        and at oe_start; finance-weighted usable
                        versus budget_rhs. No new period identity,
                        no Q-return, no Fourier, no residues, no
                        word enumeration, no perfect-square target
Promotion criterion     A proved cut Σ w_i ε_i ≤ B_strict < B_run
                        from exact cell geometry, killing at least
                        one of the 99
Stop criterion          Remainders unrestricted in every finance
                        class; any average is not a theorem or is
                        too weak; large remainders occur where
                        finance needs them
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Normalized cell position \(\mathrm{pos}=\rho/(2T+1)\) —
  **REPARAMETERIZATION** of `local_defect` plus cell width
- Usable logarithm fraction —
  **REPARAMETERIZATION** of `log_le_two_log_add`
- Uniform \(\mathrm{pos}\le 0.988\) leftover-killer —
  **REFUTED** (`juggler_cycle_remainder_finance_leftover_killer`)
- Window-mean usable as a `CycleMin` bound —
  **REFUTED** as a theorem (diagnostic only)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_remainder_finance`
- Dataset: `data/research/juggler/cycle_finance/remainder_finance/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_remainder_finance.py`
- Window: odds in \([10^6+1,10^6+20001)\) and
  \([\mathtt{oe\_start},\,\mathtt{oe\_start}+8000)\);
  \(99\) run-type survivors. Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_remainder_finance_leftover_killer` — **REFUTED**.

## Counterexamples

- `OOE`-legal \(n=1016445\) has \(\mathrm{pos}=0.9999737\) and
  \(\mathrm{usable}=0.9999737\). Falsifier A.
- In the same valley window, \(62\) `OOE` starts have
  \(\mathrm{pos}\ge 0.988\), the factor that \(L=55293\) would
  need as a uniform cut. Falsifier A.
- `OE`-legal starts at scale \(n^{4/3}\) reach
  \(\mathrm{pos}=0.99996\). Even landings reach \(0.99989\).
  Falsifier A on every finance class.
- The observed maximum as a uniform factor excludes none of the
  \(99\). The window mean \(0.492\) would exclude \(49\), but that
  average is not forced by cell geometry.

## Formalization

None. No `CycleRemainderFinance.lean`. Paper A is unchanged.
`log_step_even` / `log_step_odd` stay the cell-top bounds.

## Results

- **Even terms do not bind** — **EXACT — HUMAN PROOF**: they are
  charged at \(n^2\) in `budget_rhs`.
- **No uniform remainder cut** — **COMPUTATIONALLY VERIFIED**
  (`remainder_finance/summary.json`): `remainders_unrestricted=true`,
  `killed_count_max=0`, `emptied_count=0`.
- **Mean usable is not a theorem** — **OBSERVATION**:
  `mean_ooe_usable=0.492` on \(5045\) `OOE` starts; `killed_count_mean=49`.
- **Cell-top bound remains attainable** — **COMPUTATIONALLY VERIFIED**
  on exact Juggler images, not on an abstract cell.

## Open questions

None from remainder geometry. A mean-value theorem for
\(\{n^{3/2}\}\) on a `CycleMin` arithmetic progression would be a
different analytic project and is not implied by the cells.

## Decision

**CLOSE**. Normalized remainders are unrestricted in every
finance-relevant class. The quantity is the existing cell-top
logarithm in other coordinates. Large remainders occur exactly
where run-type packing wants them: `OOE` valleys near \(n\) and
`OE` starts near \(n^{4/3}\). A window average of \(1/2\) is not
a `CycleMin` bound and is the only figure that would have moved
\(\mathcal E_{\mathrm{run}}(10^6)\). Keep the witness
\(n=1016445\) as negative knowledge. No Paper A edit, no ledger
row, no Lean.

Best next question: none from finance-weighted remainder control.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.
