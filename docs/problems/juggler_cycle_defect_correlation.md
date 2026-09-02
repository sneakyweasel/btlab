# Juggler correlated floor-defect finance

Status: **ARCHIVED**

Refinement of
[juggler_cycle_finance.md](juggler_cycle_finance.md) and
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md),
not a new paper. It asks whether successive exact floor defects
are coupled strongly enough that the run-type finance budget is
unattainable, even though aggregate \((L,o)\) packing remains
feasible. Not a halt theorem, not a leftover-itinerary census, not a
new global finance identity, not Fourier, and not a residue /
\(p\)-adic system.

## Problem

The global defect is not an additive sum. After run-type packing
leaves \(99\) lengths, can two nearby local remainders both sit
at their independently finance-maximal cell corners, or does the
power-gap recurrence force a compensating defect?

## Exact statement

For a realized step write \(x^e=y^2+\rho\) with
\(0\le\rho<2y+1\) and \(\eta=\rho/(2y+1)\). The two-step
identities are existing machinery:

**OE cell expansion (EXACT — HUMAN PROOF).**
If \(x\) follows `OE`, then \(x^3=(z^2+\eta)^2+\rho\). This is
the chained odd/even cells, not a new relation.

**OO substitution (EXACT — LEAN VERIFIED).**
If \(x\) follows `OO`, then \((x^3-\rho)^3=(z^2+\sigma)^2\).
This is `two_step_mordell_identity`, a
**REPARAMETERIZATION** of \(y^6=y^6\).

**Composition (EXACT — LEAN VERIFIED).**
\(\Delta(uv)=\texttt{global\_defect\_append}\). Not additive,
and not a pair-tax.

**Independent corners (COMPUTATIONALLY VERIFIED).**
At \(n=10^6+1\), among realized `OE` and `OO` blocks:

- both \(\eta\le 0.1\) occurs (\(21\) `OE`, \(18\) `OO` near \(n\));
- both \(\eta\ge 0.9\) occurs (\(23\) `OE`, \(19\) `OO\));
- \(\max(\varepsilon_i+\varepsilon_{i+1})/(\varepsilon_i^{\max}+\varepsilon_{i+1}^{\max})\ge 0.9999\);
- pair-finance \(\sum 1/(x\ln x)\) matches the separable maximum
  (gap \(0\)).

An `OOE` triple did not hit all three \(\eta\le 0.1\) in \(914\)
samples; one triple hit all three \(\eta\ge 0.9\). The pair-eps
ratio on `OOE` is still \(0.998\). That is not a finance tax.

**No leftover \((L,o)\) dies (COMPUTATIONALLY VERIFIED).**
The bookkeeping gap \(1-0.9999\) is \(\mathrm{tax}/\theta\approx
0.0019\) at \(L=25781\) and \(8\cdot 10^{-5}\) at \(L=55293\).
Packed still exceeds \(\theta\). `emptied_count=0`.

No cycle of any length — not claimed.

## Current literature

- `global_defect_identity`, `global_defect_append` —
  **EXACT — LEAN VERIFIED**
- `two_step_mordell_identity` —
  **REPARAMETERIZATION**
- Run-type packing, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- Cumulative floor loss / weighted \(\rho\)-product —
  **CLOSE** / **REFUTED**
  ([juggler_cumulative_floor_loss.md](juggler_cumulative_floor_loss.md))
- Sum-\(\rho\) word statistics —
  **CLOSE**
  ([juggler_sum_rho.md](juggler_sum_rho.md))
- Ordered excursion closure —
  **CLOSE**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Finance-conditioned exact closure —
  **CLOSE**
  ([juggler_cycle_conditioned_closure.md](juggler_cycle_conditioned_closure.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-pair killer;
the two-step identities are the existing defect spine.

## Branch budget

```text
Mathematical target     Determine whether successive exact floor defects
                        are arithmetically coupled strongly enough that
                        the current finance budget is unattainable for a
                        cycle, even though aggregate (L,o), run-type,
                        prefix, Fourier, pair-level closure, and
                        finance-conditioned closure all remain feasible.
Novelty hypothesis      The global defect is not an additive sum. Its exact
                        power-gap recurrence may prevent consecutive local
                        defects from simultaneously being near their
                        finance-maximizing values.
Falsifier               Two- and three-step defect optimization admits
                        the independently finance-maximal defects at all
                        relevant scales; every derived inequality reduces
                        to the existing global defect identity / 6/5
                        finance bound; or correlations vanish after
                        projecting away the exact intermediate integer.
Existing machinery      global_defect_identity; globalDefect;
                        global_defect_append; onePlusSlack;
                        lowerDenom; CycleMin; AboveAnchor;
                        run-type finance; 99 survivor set;
                        exact odd/even floor cells;
                        odd_preimage_unique; power-gap recurrence
Maximum Phase-0 scope   First derive exact two-step and three-step
                        defect-correlation inequalities.
                        Test them on the finance-hardest survivors,
                        especially L=25781 and L=55293, at N0=10^6+1.
                        Work with O/E block types and exact intermediate
                        states, not complete words.
                        No new global finance identity, no Fourier,
                        no residue/p-adic system, no Q-return,
                        no complete-word enumeration.
Promotion criterion     A reusable local incompatibility such as
                        (small defect at i) ⇒ (defect at i+1 ≥ f(...))
                        strong enough that a cycle's total required
                        defect cannot be distributed within the
                        existing finance budget.
Stop criterion          Defect pairs can be simultaneously optimized
                        independently; the only relation is the exact
                        global recurrence already used; the correlation
                        bound is asymptotically negligible; or it
                        requires fixing the complete word.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- OE identity \(x^3=(z^2+\eta)^2+\rho\) —
  **KNOWN** (chained cells)
- OO identity \((x^3-\rho)^3=(z^2+\sigma)^2\) —
  **REPARAMETERIZATION** of `two_step_mordell_identity`
- `global_defect_append` —
  **KNOWN**
- Independent \(\eta\)-corners on `OE`/`OO` —
  **COMPUTATIONALLY VERIFIED**
- Pair-eps tax —
  **OBSERVATION**; relative size \(<10^{-4}\)
- Pair-finance gap —
  **COMPUTATIONALLY VERIFIED** (exactly \(0\) on the samples)
- Correlated leftover-killer —
  **REFUTED** (`juggler_cycle_defect_correlation_leftover_killer`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_defect_correlation`
- Dataset: `data/research/juggler/cycle_finance/defect_correlation/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_defect_correlation.py`
- Window: \(4000\) odds from \(n=10^6+1\) and from
  `oe_start_min(n)`; blocks `OE`, `OO`, `OOE`; spotlights
  \(L=25781\) and \(L=55293\). Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_defect_correlation_leftover_killer` — **REFUTED**.

## Counterexamples

- `OE` near \(n\): \(21\) pairs with both \(\eta\le 0.1\) and
  \(23\) with both \(\eta\ge 0.9\). Falsifier A.
- `OO` near \(n\): \(18\) cheap pairs and \(19\) max pairs;
  first-step \(\eta=0\) occurs. Falsifier A.
- Pair-finance gap \(0\) and pair-eps ratio \(0.9999\).
  Falsifier B / C.
- `tax/\theta\approx 0.0019` at \(L=25781\) does not drop packed
  below \(\theta\). Falsifier E.

## Formalization

None. No `CycleDefectCorrelation.lean`. Paper A is unchanged.
`global_defect_append` and `two_step_mordell_identity` are not
re-proved.

## Results

- **Two-step identities** — **KNOWN** / **REPARAMETERIZATION**.
- **No correlation tax** — **COMPUTATIONALLY VERIFIED**
  (`defect_correlation/summary.json`):
  `both_max_attained=true`, `both_cheap_attained=true`,
  `finance_gap=0`, `emptied_count=0`.
- **OOE triple cheap-corner** — **OBSERVATION**: not hit in
  \(914\) samples; not a leftover-killer.

## Open questions

None from two-/three-step defect correlation. The sharper
map \(u\ge p\Rightarrow u'\le f(p)\) is also **CLOSE**
([juggler_cycle_defect_anticluster.md](juggler_cycle_defect_anticluster.md)).
A kill would require a complete word or a new global finance
identity.

## Decision

**CLOSE**. Successive local defects can occupy both the cheap
and the finance-maximal cell corners on the run-type blocks
`OE` and `OO`. The only exact pair relations are the existing
cells and `global_defect_append`. The residual pair-eps gap is
bookkeeping, not a tax. Keep the identities as negative
knowledge. No Paper A edit, no ledger row, no Lean.

Best next question: none from correlated floor-defect finance.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.
