# Juggler decoration-and-mode budget census

Status: **PARK** (Phase-0 effectiveness). Paper B stays frozen at
\(13/16\). No retag of `J-kernel-cancellation` or
`J-depth4-complete`.

Child of
[juggler_two_step_parity.md](juggler_two_step_parity.md).
Sibling of the engine-harvest children. Not a \(K_3\) attack
and not a Paper B edit.

## Problem

Theorem T died because a passenger sat outside the Lemma 5.2
slot it was assigned. Do the frozen Theorem 5.3 Step 3 and
Theorem 6.1 Step A–D pieces themselves sit inside the printed
budgets at the paper's \((H_1,H_2,k)\)?

## Exact statement

At dyadic \(P\in\{10^6,10^8,10^{10}\}\), with
\(H_1=P^{1/48}\), \(H_2=P^{1/24}\), kernel
\(k\le P^{1/24}\) and depth-4 \(k\le 2P^{1/96}\), do all
printed expansion pieces
\((q,u,j,h,h',\mathrm{class})\) of Theorem 5.3 Step 3 and
Theorem 6.1 Step A satisfy Lemma 5.2
(\(|q_d|\le P^{1/16}\), \(|j|\le 3\), at most eight
decorations, (D3) curvature), Lemma 5.2(i)
(\(h\le P^{1/8}\), \(uh\le P^{1/2}\)), and the Theorem 6.1
passenger \(\theta\)-coefficient \(2.5\) that shrinks the
offset margin from \(4.375:1\) to \(7:4\)? A witness whose
ratio does not tend to \(0\) as \(P\to\infty\), or
\(|j|>3\) at the paper's shifts, is a Theorem-T-type
blocking point.

## Current literature

- Paper B Lemma 5.2 / Theorem 5.3 / Theorem 6.1
  (`J-kernel-cancellation`, `J-depth4-complete`) —
  **EXACT — HUMAN PROOF**. **reproduced**.
- Theorem T passenger hole (Phase 26): modes
  \(\asymp lP^{3/16}>P^{1/16}\) asymptotically —
  **REFUTED** as a proof; later repaired in
  [juggler_engine_harvest.md](juggler_engine_harvest.md) by
  re-slotting as Stage-2 \(r\)-modes. **independent**.
- Scale-invariant copy of Theorem R —
  **REFUTED**. Not re-tested.
- Paper B §5: every numerical margin is claimed only for
  \(P\ge P_0\) with \(P_0\) ineffective. **reproduced**.

## Branch budget

```text
Mathematical target     At the paper's (H1, H2, k) and truncations,
                        do the actual Step-3 / Step-A pieces all
                        sit inside the printed Lemma 5.2 and
                        Theorem 6.1 budgets?
Novelty hypothesis      Theorem T died because a passenger was
                        larger than the slot it was assigned.
                        The same check has never been run on the
                        frozen kernel / depth-4 inventory itself.
Falsifier               One witness with |q| > P^{1/16} or |j| > 3
                        at the paper's (H1, H2, k) whose ratio does
                        not tend to 0 as P → ∞ (Theorem-T type);
                        or a θ-coefficient that kills the 7:4
                        offset composite.
Existing machinery      two_step_parity.master_identity_check,
                        kernel_margin_scan (bare 4.375 only),
                        branch_freeze_scan; Paper B Lemma 5.1–5.2,
                        Theorem 5.3 Steps 3–5, Theorem 6.1 A–E.
Maximum Phase-0 scope   Combinatorial mode inventory at three P
                        plus a sampled j / curvature / θ-coefficient
                        orbit census. No Paper B edit, no CLI, no
                        Lean, no harvest reopen, no K3.
Promotion criterion     Every load-bearing budget holds
                        asymptotically; finite-P failures are named
                        as P0; 7:4 composite confirmed on the
                        decorated phase.
Stop criterion          A Theorem-T-type witness, or machinery
                        gravity (visualizer, extra P, extra itineraries).
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge stays closed.

## Candidate operations / invariants

- Combinatorial inventory of Step 3 / Step A
  \((q,u,j,h,h',\mathrm{class})\) —
  **COMPUTATIONALLY VERIFIED**
- Named \(P_0\) for the printed line
  \(|t|\le 3J_2\le P^{1/16}\): effective only at
  \(P\ge 3^{48}\) — **OBSERVATION**
- Orbit \(j=\beta_{12}-\beta_1-\beta_2\) at paper
  \((H_1,H_2)\) — **COMPUTATIONALLY VERIFIED**
  (\(|j|\le 3\))
- Decorated offset composite \(945:540=7:4\) —
  **EXACT — HUMAN PROOF** (algebra) plus
  **COMPUTATIONALLY VERIFIED** (interpolant)
- Kernel / depth-4 theorems — untouched
  **EXACT — HUMAN PROOF**
- \(K_3\) bound — **PARK** (BB/GG/JJ)

## Experiments

Runner:
`python -m research.juggler_sequence.decoration_budget`.
Writes
`data/research/juggler/decoration_budget/summary.json`.
Tests:
`tests/research/juggler_sequence/test_decoration_budget.py`.

## Conjectures

None new. `J-kernel-cancellation` and `J-depth4-complete`
stay **EXACT — HUMAN PROOF**.

## Counterexamples

None of Theorem-T type. Finite-\(P\) overflow of
\(|t|\le 3J_2\le P^{1/16}\) at \(P\le 10^{10}\) is the
paper's own ineffective \(P_0\) (ratio
\(3P^{-1/48}\to 0\)). Term count \(9>8\) is a fixed
constant, not a growing family.

## Formalization

None added. Packaging the census in Lean would be
machinery gravity.

## Results

- **Combinatorial inventory (COMPUTATIONALLY VERIFIED).**
  At \(P\in\{10^6,10^8,10^{10}\}\) the printed Step-3 / Step-A
  pieces give 15 rows each: 11 `none`, 4 `p0`, 0 `structural`.
  The four \(P_0\) rows are `product_t` (\(|t|\le 3J_2\),
  ratios \(2.25\), \(2.04\), \(1.86\)), `product_qd`
  (\(|q_d|\le 2J_2\)), `thm61_j_passenger_qd`
  (\(|q_d|\le 3P^{1/24}+P^{1/96}\)), and `term_count_rho`
  (fixed \(9>8\)). Lemma 5.2(i) \(uh_1\le P^{1/2}\) and
  \(h\le P^{1/8}\), single-layer \(|q|\le J_2\), the
  \(i\)-passenger (D3), and \(|i|,|j|,|k|\le 2P^{1/96}\) all
  hold. Named threshold for the printed line
  \(|t|\le 3J_2\le P^{1/16}\): \(P\ge 3^{48}\).
- **Orbit \(j\) (COMPUTATIONALLY VERIFIED).** At paper
  integer shifts, \(152000\) odd \(n\) per \(P\):
  \(\max|j|=2\) at \(10^6\) (live \(\{-1,0,1,2\}\)),
  \(\max|j|=1\) at \(10^8\) and \(10^{10}\). No
  \(|j|>3\). At most four live \(\boldsymbol\kappa\)-branches
  in the carry subsample (cap eight).
- **Offset composite (EXACT algebra + COMPUTATIONALLY
  VERIFIED interpolant).**
  \(945/512:540/512=7:4\), composite \(405/512>0\);
  window-centre factor exactly \(5/2\). Interpolant
  \(\theta\)-coefficients track the predictions
  (kernel ratio \(0.985\to 1.000\), factor
  \(2.537\to 2.501\)). Single-signed at every \(P\).

## Open questions

The independent human check of Paper B Section 5 remains.
Do not open a \(P_0\)-effectiveness campaign.

## Decision

**PARK** as effectiveness. The only overflows at
\(P\in\{10^6,10^8,10^{10}\}\) die as \(P\to\infty\)
(ratio \(3P^{-1/48}\to 0\)); \(|j|\le 3\) on every
sampled orbit; the \(7:4\) composite is single-signed;
term count is a fixed \(9\). Not a Theorem-T witness.
Do not retag the kernel. The printed \(|t|\le P^{1/16}\)
and “at most eight” holes are absorbed in the 2 September
2026 Paper B writeup (\(|q_d|\le 4P^{1/24}\), nine
decorations). Claim set still \(13/16\). Best next
question: one independent human check of Section 5.

## Publication assessment

Status: `EXPLORATORY` (laboratory census). Not a Paper B
edit.
