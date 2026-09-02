# Juggler finance-conditioned exact closure

Status: **ARCHIVED**

Refinement of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md) and
[juggler_cycle_closure.md](juggler_cycle_closure.md),
not a new paper. It asks whether leftover surplus forces
near-extremal run structure tightly enough that exact floor cells
empty a surviving \((L,o)\) in \(\mathcal E_{\mathrm{run}}(10^6)\).
Not a halt theorem, not a leftover-itinerary census, not a new global
finance identity, not Fourier, not a \(Q\)-return, and not a
residue / \(p\)-adic system.

## Problem

Pair-level closure is the exponent envelope. Run-type packing is
already the finance maximum. After those two facts, does the
surviving surplus

\[
\theta(L)=\frac{3^{o_{\min}}}{2^L}-1
\]

still force a hypothetical cycle into a small near-extremal
run class on which exact cells can contradict?

## Exact statement

**Finance deficit (EXACT — HUMAN PROOF).**
Write \(P\) for the packed run-type RHS at \(n=N_0+1\). A
deviation that drops the packed sum by \(c>0\) remains finance-legal
for at most \(\lfloor(P-\theta)/c\rfloor\) copies, and at most the
number of available runs. Deepening \((\mathtt{OOE},\mathtt{OE})\to
\mathtt{OOOE}\) costs

\[
c_{\mathrm{deep}}=\tfrac65\bigl(F(2)+F(1)-F(3)\bigr),
\]

which is essentially the isolated-`OE` term: the third odd sits
near \(n^{9/4}\) and does not bind. Losing one cheap `OOE` start
from \(n+2\) to `oe_start_min(n)` costs

\[
c_{\mathrm{lose}}=\tfrac65\bigl(\tfrac{1}{(n+2)\ln(n+2)}-\tfrac{1}{v\ln v}\bigr).
\]

**No structural concentration (COMPUTATIONALLY VERIFIED).**
At \(n=10^6+1\):

- \(L=25781\): \(P/\theta\approx 23.12\). One may lose \(6532\) of
  \(6751\) cheap `OOE` starts, or deepen all \(2764\) `OE` runs.
  After deepening every `OE`, packed still exceeds \(\theta\).
- \(L=55293\): \(P/\theta\approx 1.012\). One may lose \(177\) of
  \(14479\) cheap starts, or deepen all \(5928\) `OE` runs. After
  deepening every `OE`, packed still exceeds \(\theta\).

The residual lose-class satisfies
\(\log_{10}\binom{14479}{177}>200\) and
\(\log_{10}\binom{6751}{6532}>300\). Finance survival is not a
stronger structural statement than the existing `OOE`/`OE`
packing theorem.

**Run-type window (COMPUTATIONALLY VERIFIED).**
The raw crossing \(\theta=P(n)\) is \(n_{\max}^{\mathrm{run}}(25781)
=19010076\) and \(n_{\max}^{\mathrm{run}}(55293)=1011446\).
Conditioning the pair-level hull on that window still meets the
start and reduces to \(T\le n^{P_L}\).

No cycle of any length — not claimed.

## Current literature

- Run-type packing, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- Cyclic run-depth / adjacency leftover-killer —
  **REFUTED**
  (`juggler_cycle_run_extremum_leftover_killer`);
  two-type is already the relaxed maximum
- Pair-level exact closure —
  **REFUTED**
  (`juggler_cycle_closure_leftover_killer`);
  word-independent intervals are the envelope
- Prefix expansion of near-convergents —
  **REFUTED**
  (`juggler_cycle_prefix_feasibility_leftover_killer`)
- `cycleMin_finance`, `cycleMin_even_ge_sq`, `power_bound_word` —
  **EXACT — LEAN VERIFIED**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-pair killer;
deficit arithmetic is the existing packed RHS.

## Branch budget

```text
Mathematical target     Finance-conditioned exact closure:
                        after the 99 period survivors are restricted to
                        finance-near-extremal run configurations, can
                        exact floor-cell constraints eliminate the
                        remaining configurations?
Novelty hypothesis      Finance is not only a final period filter.
                        For a surviving (L,o), its tiny surplus
                        θ(L)=3^o/2^L−1 forces any hypothetical cycle
                        to lie very close to the run-type finance
                        extremum. That converts exact closure from a
                        pair-level problem into a small near-extremal
                        structural problem.
Falsifier               The finance margin is still large enough that
                        many qualitatively different run configurations
                        remain feasible; or every finance-near-extremal
                        configuration admits exact floor-cell closure;
                        or conditioning on finance produces no stronger
                        structural statement than the existing
                        OOE/OE packing theorem.
Existing machinery      cycleMin; AboveAnchor; cycleMin_finance;
                        parity_rhs; run_type_rhs / budget_rhs;
                        99 survivors E_run(10^6);
                        odd/even floor cells;
                        odd_preimage_unique; even_preimage_iff;
                        first-run a0≥2;
                        isolated-OE r-bound;
                        known local finite-progress exclusions;
                        exact block interval machinery
Maximum Phase-0 scope   Start with L=25781 and L=55293 only.
                        Derive an exact quantitative finance deficit
                        for non-extremal run structures, then feed only
                        the resulting near-extremal classes into exact
                        block/cell closure.
                        No full word enumeration;
                        no new global finance identity;
                        no Q-return;
                        no Fourier;
                        no p-adic/residue automaton;
                        no terminal-cluster reopen.
Promotion criterion     A theorem of the form
                        CycleMin + finance survival
                        ⇒ structural_near_extremality
                        followed by
                        structural_near_extremality
                        + exact floor closure
                        ⇒ contradiction
                        for at least one survivor.
Stop criterion          Finance margin does not force meaningful
                        structural concentration; every deviation from
                        the extremizer costs too little; the residual
                        class is still exponentially large with no
                        compressible structure; or exact closure again
                        reduces to the old word-independent envelope.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Packed-to-\(\theta\) slack \(P-\theta\) —
  **EXACT — HUMAN PROOF** (this dossier)
- Deepen-all still above \(\theta\) —
  **COMPUTATIONALLY VERIFIED**
- Residual \(\binom{o-e}{k_{\mathrm{lose}}}\) —
  **COMPUTATIONALLY VERIFIED** (exponential)
- Finance-restricted hull \(T\le n^{P_L}\) —
  **REPARAMETERIZATION** of `power_bound_word`
- Finance-conditioned leftover-killer —
  **REFUTED** (`juggler_cycle_conditioned_closure_leftover_killer`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_conditioned_closure`
- Dataset: `data/research/juggler/cycle_finance/conditioned_closure/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_conditioned_closure.py`
- Window: \(L=25781\) and \(L=55293\) at \(n=10^6+1\);
  run-type \(n_{\max}\) raw crossing; legal `OO` start \(1000053\)
  for landing geometry. Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_conditioned_closure_leftover_killer` — **REFUTED**.

## Counterexamples

- Deepening every `OE` into `OOOE` leaves packed \(>\theta\) at
  both leftover lengths. Deepen cost \(\approx 6.51\cdot 10^{-10}\).
- Losing a cheap valley costs \(\approx 8.62\cdot 10^{-8}\), so
  \(6532\) losses fit at \(L=25781\) and \(177\) at \(L=55293\).
- The finance-restricted hull meets the start on both run-type
  windows and reduces to the exponent envelope.
- \(\log_{10}\) of the residual lose-class is \(>200\) at the
  tight leftover.

## Formalization

None. No `CycleConditionedClosure.lean`. Paper A is unchanged.

## Results

- **No near-extremal forcing** — **COMPUTATIONALLY VERIFIED**
  (`conditioned_closure/summary.json`):
  `concentrates=false`, `deepen_all_still_above_theta=true`.
- **No leftover \((L,o)\) dies** — **COMPUTATIONALLY VERIFIED**:
  `emptied_count=0`. Both finance-restricted hulls meet.
- **Closure** — **REPARAMETERIZATION** of the pair-level envelope
  on a possibly smaller \(n\)-window.

## Open questions

None from finance-conditioned closure. The leftover surplus does
not convert pair-level closure into a small structural problem.

## Decision

**CLOSE**. Leftover \(\theta\) is a final period filter, not a
run-type concentrator. Every tested deviation from the extremizer
costs too little: one may deepen every `OE` and still survive, and
the residual lose-class is exponentially large. Exact closure on
the finance-restricted \(n\)-window is the existing envelope.
Keep the deficit arithmetic as negative knowledge. No Paper A
edit, no ledger row, no Lean.

Best next question: none from finance-conditioned exact closure.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.
