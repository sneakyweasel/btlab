# Juggler near-top defect anti-clustering

Status: **ARCHIVED**

Sharpening of
[juggler_cycle_defect_correlation.md](juggler_cycle_defect_correlation.md),
not a new paper and not a reopen of phases 2–13 of the
anti-clustering plan. The closed correlation branch already found
same-pair \(\eta\ge 0.9\). This phase asks only whether a sharper
map \(u\ge p\Rightarrow u(T(x))\le f(p)<1\) exists at the
thresholds that could move \(\mathcal E_{\mathrm{run}}(10^6)\).
Not a halt theorem, not a leftover-itinerary census, not a new finance
identity, not Fourier, and not a residue search.

## Problem

Pointwise remainders can have \(u(x)>0.99997\). Can two successive
dynamically relevant odd states both stay near the top, or does
high \(u(x)\) force a quantitative drop at \(T(x)\)?

## Exact statement

For odd \(x\) write \(y=T(x)\), \(\rho=x^3-y^2\), and

\[
u(x)=\frac{\rho}{2y+1},\qquad
\delta(x)=\frac{\rho}{x^3},\qquad
\lambda(x)=\frac{x^3}{y^2}.
\]

**Conversions (EXACT — HUMAN PROOF).**
\(\rho=x^3-y^2\) gives \(\delta=1-1/\lambda\) and
\(\lambda-1=\rho/y^2\) as rationals. \(u\) uses the same
numerator. At fixed \(x\), the three coordinates are strictly
monotone in \(\rho\). A forbidden region in \(u\) is a forbidden
region in \(\delta\) and \(\lambda\).

**No finance-useful \(f(p)\) (COMPUTATIONALLY VERIFIED).**
On consecutive odds (`OO`) in \([10^6+1,3\cdot10^6)\):

- \(2893\) pairs with \(u\ge 0.995\); \(f(0.995)=0.999958\);
- \(12\) pairs have both coordinates \(\ge 0.995\);
- \(576\) pairs with \(u\ge 0.999\); \(f(0.999)=0.9936>0.988\);
- none have both \(\ge 0.999\);
- witness \(x=2745367\): \((u,u')=(0.99759,0.99989)\).

At \(10^7\), \(x=10356211\) gives \((0.99889,0.99850)\).
`OE` landings are the same: \(f(0.995)=0.99997\).

The previous branch's componentwise maxima
\((0.99994,0.99993)\) were not same-pair. Same-pair near-top
still occurs at \(0.997\)–\(0.999\). \(L=55293\) would need
\(f(p)\le 0.988\). Observed \(f(0.995)\) is \(0.99996\).

No cycle of any length — not claimed.

## Current literature

- Independent \(\eta\)-corners on `OE`/`OO` —
  **COMPUTATIONALLY VERIFIED** / leftover-killer **REFUTED**
  ([juggler_cycle_defect_correlation.md](juggler_cycle_defect_correlation.md))
- Pointwise \(u>0.99997\) —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_remainder_finance.md](juggler_cycle_remainder_finance.md))
- `two_step_mordell_identity` / `global_defect_append` —
  **REPARAMETERIZATION** / **EXACT — LEAN VERIFIED**
- Run-type packing, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a sharper leftover-killer;
the coordinate change is a **REPARAMETERIZATION**.

## Branch budget

```text
Mathematical target     Does u(x)>=p imply u(T(x))<=f(p)<1 with a
                        gap strong enough to cut budget_rhs,
                        especially at p~0.988?
Novelty hypothesis      Near-top defects anti-cluster at two steps
Falsifier               Arbitrarily large pairs with both u,u' near 1;
                        f(p) too weak to beat 0.988; only averages;
                        residue-only; disappears on OOE/OE
Existing machinery      cell_record; step_record; defect_correlation;
                        two_step_mordell_identity; remainder-finance
Maximum Phase-0 scope   Conversions; f(p) on OO/OE; high-u followup
                        at 10^6 and 10^7. No phases 2-13; no Lean;
                        no survivor rescan; no three-step rescue
Promotion criterion     An exact u>=p => u'<=q<0.988, or a finite
                        window bound that cuts S_run
Stop criterion          Same-pair near-top persists; f(0.995)~1;
                        or the claim is the closed 0.9-corner result
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(u,\delta,\lambda\) —
  **REPARAMETERIZATION** of \(\rho=x^3-y^2\)
- \(f(p)=\sup\{u(T(x)):u(x)\ge p\}\) —
  **OBSERVATION**; \(f(0.995)=0.99996\)
- Same-pair \((0.9976,0.99989)\) —
  **COMPUTATIONALLY VERIFIED** (Falsifier A)
- Anti-clustering leftover-killer —
  **REFUTED** (`juggler_cycle_defect_anticluster`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_defect_anticluster`
- Dataset: `data/research/juggler/cycle_finance/defect_anticluster/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_defect_anticluster.py`
- Windows: odds in \([10^6+1,10^6+20001)\),
  \([10^6+1,3\cdot10^6)\), \([10^7+1,10^7+400001)\),
  and the `oe_start` window of width \(8000\).
  Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_defect_anticluster` — **REFUTED**.

## Counterexamples

- \(x=2745367\) is `OO`-legal with
  \((u,u')=(0.99759,0.99989)\). Falsifier A.
- \(x=10356211\) gives \((0.99889,0.99850)\). Falsifier A at
  a larger scale.
- \(12\) `OO` pairs in the high followup have both
  \(u,u'\ge 0.995\). Falsifier A at the finance-adjacent
  threshold.
- \(f(0.995)=0.99996>0.988\). Falsifier B for \(L=55293\).

## Formalization

None. No `CycleDefectAnticluster.lean`. Paper A is unchanged.
Do not formalize the exploratory \(f(p)\) table.

## Results

- **Conversions** — **EXACT — HUMAN PROOF**.
- **No useful two-step cut** — **COMPUTATIONALLY VERIFIED**
  (`defect_anticluster/summary.json`):
  `high_f_oo=0.999958`, `both_995_total=12`,
  `both_999_total=0`, `emptied_count=0`.
- **Coordinate change** — no new forbidden region.

## Open questions

None from two-step anti-clustering. A three-step or excursion-level
rescue would be a new target; this phase forbids auto-continuation.

## Decision

**CLOSE**. Near-top defects can occur repeatedly: same-pair
\((u,u')\) reaches \((0.9976,0.99989)\) and twelve pairs exceed
\(0.995\). The map \(f(0.995)\) is \(0.99996\), so there is no
gap that can cut `budget_rhs` below \(\theta\) at \(L=55293\).
\(\delta\) and \(\lambda\) are the same \(\rho\). This is
Falsifier A plus Falsifier B of the plan, and it is the closed
correlation branch at a sharper threshold. Do not run phases
2–13. No Paper A edit, no ledger row, no Lean.

Best next question: none from two-step defect anti-clustering.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.
