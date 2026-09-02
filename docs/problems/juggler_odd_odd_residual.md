# Juggler odd-odd residual admissibility

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

After a non-extremal `ResidualStep` lands on another odd-odd state,
do the successor constraints for a further non-extremal odd-odd step
tighten until the next step is impossible?

## Exact statement

Keep the existing successor. Do not replace it with a peak-based
state.

\[
\mathrm{ResidualStep}(x,y)
\iff
\exists\,a,b\ (b\ge 1\ \wedge\ x\ \text{follows}\ O^aE^b\ \wedge\ T_{O^aE^b}(x)=y).
\]

A step is non-extremal when some odd prefix defect is positive. The
landing is odd-odd when \(y\) is odd and \(T(y)\) is odd. The Phase-0
question is whether the joint conditions for another such step —

- a first even residual exists,
- the even run lands,
- that landing is odd-odd,
- the next odd prefix is again non-extremal —

form a finitely admissible relation, or whether some derived quantity
of \(S=(x,a,z,b,y)\) is recursively necessary and strictly tightens.

This says nothing about totality. A search-horizon depth is not a
bound \(L\). Do not prove that every residual chain reaches 1.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- `ResidualStep` / `PersistentOddResidual` certificate propagation —
  **EXACT — LEAN VERIFIED**.
- First-even residual trichotomy and post-overshoot leftover —
  **EXACT — LEAN VERIFIED** / **COMPUTATIONALLY VERIFIED**.
- Peak Diophantine composition —
  **REPARAMETERIZATION** of the nested cells; closed as
  `DIOPHANTINE_REPACKAGING`.

Project relationship: **extended**. The leftover after residual
certificates and the closed peak identity is tested as finite
admissibility. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Can a non-extremal ResidualStep chain remain
                        arithmetically admissible indefinitely, or do
                        successor constraints eventually fail?
Novelty hypothesis      The joint conditions for another odd-odd step
                        tighten (interval, valuation, residue) until
                        no next ResidualStep exists.
Falsifier               Arbitrarily long non-extremal continuations
                        on known traces, or every proposed I(S) dies
                        and the “recurrence” is ResidualStep rewritten.
Existing machinery      ResidualStep, PersistentOddResidual,
                        residual_chain / HARD_PROBES, localDefect,
                        is_odd_odd
Maximum Phase-0 scope   Write the successor observables; cheap
                        persistent probe; HARD_PROBES + odd-odd n≤80;
                        test admissibility first; Lean only if a law
                        survives. No census, no peak identity.
Promotion criterion     An exact successor obstruction or a finite L
                        that is not the search horizon; or a minimized
                        counterexample that closes a natural I(S).
Stop criterion          ODD_ODD_RESIDUAL_COMPLEX; no jointly necessary
                        and recursively preserved condition; ResidualStep
                        rewritten. No RemainderDynamics, PowerHeight,
                        halt, prefix-NC project, CycleItinerary growth.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `ResidualStep` as the only successor —
  **EXACT — LEAN VERIFIED** (already present; not rewritten)
- another non-extremal odd-odd step is finitely admissible —
  **REFUTED** as a uniform law on the window: successor cells do not
  tighten, and a next step can exist while widths grow
- interval widths of the even-run cell and last odd cell shrink —
  **REFUTED** at \(37\to 9317\to 2233\) and \(69\to 117\to 3\)
- \(v_2(z)\) or \(v_3\) is monotone along continuation —
  **REFUTED** on the \(37\)-chain (\(v_2\): \(2,5,1\))
- \(y>x\) on every non-extremal odd-odd step —
  **REFUTED**; smallest first-step witness \(53\to 9\); after a
  persistent step, \(69\to 117\to 3\) and \(9317\to 2233\)
- exact \(O^k\) towers are the unbounded residual branch —
  **REFUTED** in \(2\le n\le 80\): every first odd prefix is
  non-extremal
- a finite bound \(L\) on non-extremal odd-odd depth —
  not claimed; depth \(2\) is the search-horizon maximum
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_odd_residuals`
  (`init` / `run` / `resume` / `status` / `summarize`)
- Records: [juggler_odd_odd_residual.md](../research/juggler_odd_odd_residual.md),
  [juggler_odd_odd_residual.json](../research/juggler_odd_odd_residual.json)
- Dataset: `data/research/juggler/odd_odd_residuals/`
- Tests: `tests/research/juggler_sequence/test_odd_odd_residuals.py`
- The Research Engine control layer is not modified.
- Window: `HARD_PROBES = (9, 37, 49, 69, 77)` and every odd-odd
  start \(2\le n\le 80\).

## Conjectures

None opened.

## Counterexamples

Recorded under `data/research/juggler/odd_odd_residuals/analysis/counterexamples.json`.

- \(y>x\): first-step \(53\to 9\) and \(55\to 9\); after persistence,
  \(69\to 117\to 3\) and \(37\to 9317\to 2233\) with \(2233>37\).
- Interval tightening: even-run width \(18635\to 44567460015\) on
  \(37\to 9317\to 2233\); \(235\to 58975\) on \(69\to 117\to 3\).
- Valuation monotonicity: \(v_2(z)\) on the \(37\)-chain is
  \(2,5,1\).
- Exact towers: no first residual in the window has an all-zero odd
  prefix.

These kill the proposed \(I(S)\) list. They do not produce a halt
statement and do not imply a bound \(L\).

## Formalization

None added. `ResidualStep` and `PersistentOddResidual` already live
in `formal/Problems/Engine/ResidualChain.lean`. No
`OddOddResidual.lean`. `CycleItinerary.lean`, `CycleDiophantine.lean`, and
`FloorPower.lean` are not rewritten. No `sorry`. No ledger row.

## Results

Classification **ODD_ODD_RESIDUAL_COMPLEX**, with secondary
**ODD_ODD_COUNTEREXAMPLE** for scalar monotonicity.

`HARD_PROBES` reproduce the known traces: \(37\to 9317\) (`O^4E^1`),
\(9317\to 2233\) (`O^3E^2`), \(69\to 117\), \(77\to 1523\to 243\),
\(9\to 11\) (automatic `FiniteProgress`). Every odd-odd start in
\(2\le n\le 80\) has a non-extremal first residual. Successor
existence for another odd-odd step is `ResidualStep` plus
`is_odd_odd` plus a positive odd defect. Those conditions do not
tighten: interval widths can grow, valuations are not monotone, and
\(y>x\) fails. The window maximum non-extremal odd-odd depth is
\(2\). That is a horizon count, not \(L\).

## Open questions

Do not reopen ResidualStep invariants, another peak identity, or a
remainder-dynamics object. Answered in
[juggler_prefix_nc_admissibility.md](juggler_prefix_nc_admissibility.md):
backward floor-cell pullback of mixed prefix-NC words is
`PREFIX_NC_ARITHMETIC_COMPLEX`.

## Decision

**CLOSE** the non-extremal odd-odd continuation branch as
`ODD_ODD_RESIDUAL_COMPLEX`. Record the traces, the killed
invariants, and the horizon-versus-\(L\) distinction. Do not add
Lean. Do not infer a bound from the window. Do not claim
termination.

Best next question: answered in
[juggler_prefix_nc_admissibility.md](juggler_prefix_nc_admissibility.md).

## Publication assessment

Status: `EXPLORATORY`. A negative admissibility result, not a paper
candidate and not a Juggler totality result.
