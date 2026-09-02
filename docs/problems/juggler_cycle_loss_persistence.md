# Juggler cross-excursion usable-loss persistence

Status: **ARCHIVED**

Refinement of
[juggler_cycle_remainder_finance.md](juggler_cycle_remainder_finance.md)
and
[juggler_cycle_defect_correlation.md](juggler_cycle_defect_correlation.md),
not a new paper. It asks whether large usable odd-run floor loss
can persist across successive finance-critical odd valleys, or
whether a two-excursion tax appears after finance weighting.
Not a halt theorem, not a leftover-itinerary census, not a new period
identity, not Fourier, not a \(Q\)-return, and not a residue /
\(p\)-adic system.

## Problem

One-step remainders can sit at the top of their cells, and
consecutive letters can occupy independently finance-maximal
corners. Can a CycleMin orbit keep that near-maximal usable loss
at successive odd-run blocks \(v_i\xrightarrow{O^{a_i}E}v_{i+1}\),
or does exact dynamics force a compensating deficit on the next
excursion?

## Exact statement

For odd \(x\) write \(y=T(x)=\lfloor x^{3/2}\rfloor\),
\(\rho=x^3-y^2\), and

\[
p(x)=\frac{\rho}{2y+1},\qquad
\varepsilon_O(x)=\tfrac12\log\bigl(1+\rho/y^2\bigr),\qquad
u_O(x)=\varepsilon_O(x)/\varepsilon_O^{\max}(x).
\]

These are **REPARAMETERIZATION**s of `local_defect` plus the
cell-top logarithm. On an odd-run block the score is

\[
R=\sum\varepsilon_O,\qquad U=R/R^{\max}.
\]

Pairs are kept only when the next odd valley satisfies
\(v_1\ge n\) (CycleMin scale). Collapses to \(3\) after a long
even tail are not finance-relevant.

**No two-excursion tax (COMPUTATIONALLY VERIFIED).**
In \([10^6+1,10^6+20001)\) there are \(2878\) CycleMin-scale
pairs (\(6340\) landings fall below \(n\)). Among them

- \(\max\min(U_0,U_1)=0.9767\) at \(n=1018335\)
  (`OOOE` then `OE`, \(U_1=0.9846\));
- \(\max(U_0+U_1)=1.9681\) at \(n=1000301\)
  (`OOE` then a length-\(4\) run, \(U_0=0.9737\), \(U_1=0.9945\));
- `OE` from the cheap window never returns \(v_1\ge n\)
  (the known \(n^{3/4}\) landing);
- `OOE` near-top events are positively persistent:
  \(P(U_1>0.9\mid U_0>0.9)=0.175\) against
  \(P(U>0.9)=0.066\);
- finance-weighted \(U^{(w)}\) agrees with \(U\) to many digits,
  and \(\operatorname{Corr}(U_0,U_1)\approx 0\).

At the `OE` scale \(n^{4/3}\), \(2297\) pairs have
\(\max\min(U_0,U_1)=0.9754\) and \(\max(U_0+U_1)=1.9646\).

A uniform factor \(0.977\) would bookkeeping-kill \(L=55293\)
(\(P/\theta\approx 1.012\)). That average-style cut is not a
`CycleMin` theorem: the same window already contains jointly
near-maximal pairs, and \(L=25781\) would need a factor
\(0.043\).

No cycle of any length — not claimed.

## Current literature

- `log_le_two_log_add` / `log_step_odd` / `cycleMin_finance` —
  **EXACT — LEAN VERIFIED**
- Run-type packing, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- One-step remainder control —
  **CLOSE**
  ([juggler_cycle_remainder_finance.md](juggler_cycle_remainder_finance.md))
- Consecutive-letter defect correlation —
  **CLOSE**
  ([juggler_cycle_defect_correlation.md](juggler_cycle_defect_correlation.md))
- Ordered excursion closure —
  **CLOSE**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Cheap `OOE` cannot feed `OE` at \(v=n\) —
  **KNOWN**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-pair killer;
the multi-step signature is the existing cell-top bound read
along two excursions.

## Branch budget

```text
Mathematical target     Can large usable odd-run floor loss persist
                        at successive CycleMin-scale valleys, or is
                        max(R_0+R_1) strictly below the independent
                        pair of maxima?
Novelty hypothesis      Near-top remainders occur, but cannot occur
                        repeatedly at finance-critical odd valleys;
                        a two-excursion deficit would cut budget_rhs
Falsifier               Consecutive CycleMin-scale excursions both
                        sit near their own cell-top; persistence is
                        independent or positive; the gap vanishes
                        after finance weighting; or the effect is
                        only a finite-window zero at c=0.99
Existing machinery      cell_record; ε_O from log_le_two_log_add;
                        excursion_map / Q; E_run(10^6); L=25781
                        and 55293; remainder_finance;
                        defect_correlation
Maximum Phase-0 scope   The consecutive-excursion table
                        (x, p_0, R_0, v_1, p_1, R_1) on OOE/OE
                        starts in the finance window, with
                        persistence, payment timing, and weighted U.
                        No adversary necklace, no cumulative D_k
                        process, no signature optimization, no
                        Fourier, no residues, no itinerary enumeration
Promotion criterion     A reusable inequality
                        R_i+R_{i+1} ≤ R_i^max+R_{i+1}^max-δ
                        strong enough to kill at least one of the 99
Stop criterion          Positive persistence; pair maxima equal
                        independent maxima; anti-correlation dies
                        after weighting; only a window zero at
                        c=0.99; or max(U_0+U_1) is not strictly
                        below 2
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\varepsilon_O=\tfrac12\log(1+\rho/y^2)\) —
  **REPARAMETERIZATION** of the odd cell-top logarithm
- Block scores \(R,U\) —
  **REPARAMETERIZATION** of the same quantity along a run
- Two-excursion leftover-killer —
  **REFUTED** (`juggler_cycle_loss_persistence_leftover_killer`)
- Window \(\max\min(U_0,U_1)\) as a uniform cut —
  **REFUTED** as a theorem (diagnostic only)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_loss_persistence`
- Dataset: `data/research/juggler/cycle_finance/loss_persistence/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_loss_persistence.py`
- Window: CycleMin-scale pairs from odds in
  \([10^6+1,10^6+20001)\) and
  \([\mathtt{oe\_start},\,\mathtt{oe\_start}+8000)\);
  \(99\) run-type survivors. Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_loss_persistence_leftover_killer` — **REFUTED**.

## Counterexamples

- `OOE` start \(n=1000301\) has \(U_0=0.9737\) and next-run
  \(U_1=0.9945\) at \(v_1=5625317\). \(\max(U_0+U_1)=1.968\).
  Falsifier: pair maxima equal the independent maxima.
- `OOOE` start \(n=1018335\) has \(\min(U_0,U_1)=0.9767\) with
  next `OE` at \(v_1=1.375\cdot 10^{10}\) and \(U_1=0.9846\).
- `OOE` start \(n=1017101\) has \(p_0=0.9948\) and lands on the
  envelope \(v_1/x=5.635\) with \(U_1=0.9395\). Near-top loss
  does not force the next valley off the envelope or off a
  large usable fraction.
- On \(1210\) CycleMin-scale `OOE` pairs,
  \(P(U_1>0.9\mid U_0>0.9)=0.175>P(U>0.9)=0.066\).
  Near-top events are positively persistent. Falsifier.
- A uniform factor \(0.977\) would bookkeeping-kill \(55293\)
  and would not touch \(25781\). That cut is not forced.

## Formalization

None. No `CycleLossPersistence.lean`. Paper A is unchanged.
`log_step_odd` stays the cell-top bound.

## Results

- **Usable loss is the cell-top logarithm** —
  **REPARAMETERIZATION**: \(u_O\approx p\) on the finance window,
  and finance weighting does not change the joint picture.
- **No two-excursion tax** — **COMPUTATIONALLY VERIFIED**
  (`loss_persistence/summary.json`):
  `max_min_U=0.9767`, `max_Usum=1.968`,
  `two_excursion_tax=false`, `emptied_count=0`.
- **Positive `OOE` persistence** — **OBSERVATION**:
  conditional probability at \(c=0.9\) exceeds the marginal.
- **Payment timing is the envelope** — **OBSERVATION**:
  near-top `OOE` landings sit at \(v_1/x\approx 5.63\), the
  existing \(n^{9/8}\) scale.
- **Cheap `OE` does not return above \(n\)** — **KNOWN**.
- **Window max is not a theorem** — **OBSERVATION**:
  `would_kill_if_uniform` at \(L=55293\) is bookkeeping.

## Open questions

None from cross-excursion usable-loss coupling. An adversary
necklace or a cumulative \(D_k\) process is not implied: the
first experiment already finds jointly near-maximal successive
signatures.

## Decision

**CLOSE**. Successive CycleMin-scale odd-run blocks can both
realize near-maximal usable loss. Near-top `OOE` events cluster
rather than compensate. Finance weighting does not create an
anti-correlation. The \(c=0.99\) double-zero is a sample of
\(25\) first hits, not a theorem. Keep the witnesses
\(n=1000301\) and \(n=1018335\) as negative knowledge. No
Paper A edit, no ledger row, no Lean.

Best next question: none from cross-excursion usable-loss
persistence.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.
