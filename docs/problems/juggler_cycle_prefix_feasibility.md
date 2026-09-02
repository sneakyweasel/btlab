# Juggler cycle prefix-expansion feasibility

Status: **ARCHIVED**

Refinement of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md), not a new
paper. It asks whether a run-type leftover \((L,o_{\min})\) admits
any cyclic \(O/E\) lattice path whose every prefix stays expanding.
Not a halt theorem, not a leftover-itinerary census, not a finance
reoptimization, not a \(Q\) / Fourier / residue reopen, and not a
claim that a symbolic path is an integer cycle.

## Problem

Finance survivors exist because the endpoint is extraordinarily
close to \(3^o=2^L\). A `CycleMin` word also needs every proper
prefix to stay `AboveAnchor`-compatible, hence

\[
3^{o_k}\ge 2^k.
\]

Does that prefix ordering kill any leftover that the endpoint
inequality still allows?

## Exact statement

Write \(r(k)=\min\{r:3^r\ge 2^k\}\) and \(o_{\min}(L)=r(L)\).
The unique extremal path \(o_k=r(k)\) is a lattice path from
\((0,0)\) to \((L,o_{\min})\): the increments lie in \(\{0,1\}\)
because \(3^a=2^b\) never holds for \(a,b\ge 1\). Every prefix
satisfies \(3^{o_k}\ge 2^k\) by construction. The first letters
are `OOE`, so \(a_0=2\) and the first isolated-`OE` block is
empty (\(r=0=R(2)\)).

The ceiling Christoffel word of slope \(o_{\min}/L\) is a second
witness: \(\lceil k\,o/L\rceil\ge r(k)\).

Therefore \(\mathcal A_{L,o_{\min}}\) is nonempty for every
positive \(L\). Prefix expansion plus the proved first-run
constraints is equivalent to the endpoint condition \(3^o>2^L\)
together with \(a_0\ge 2\).

No cycle of any length — not claimed. A nonempty \(\mathcal A_{L,o}\)
does not produce an integer trajectory.

## Current literature

- Prefix law \(3^{O_k}\ge 2^k\) —
  **REPARAMETERIZATION** of `power_bound_word` plus `AboveAnchor`
  ([juggler_growth_balance.md](juggler_growth_balance.md))
- Isolated-`OE` bound \(R(2)=0\) —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-first-oo-r-bound`)
- Shared parity-density gap below \(\log 2/\log 3\) —
  **REFUTED** (`J-shared-parity-balance-gap`)
- Christoffel necklace as one-parameter leftover cell —
  **REFUTED** (`juggler_christoffel_one_parameter`);
  the mechanical word itself remains **KNOWN**
- Later \((2,1)\) runs —
  **REFUTED** as a global ban
  ([juggler_odd_run_itinerary.md](juggler_odd_run_itinerary.md))
- Run-type leftover table —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))

Project relationship: **refuted** as a leftover-killer; the
extremal path is **known** Beatty / mechanical combinatorics.

## Branch budget

```text
Mathematical target     nonempty A_{L,o} for finance leftovers?
Novelty hypothesis      near-convergent 3^o > 2^L cannot be assembled
                        from prefixes that stay expanding
Falsifier               a constructive path (or a general construction
                        for every leftover)
Existing machinery      r(k)=min{r: 3^r >= 2^k}; christoffel_bits;
                        first-OO R(2)=0; budget_opt 99-list
Maximum Phase-0 scope   exact lattice witness on 25781, 55293, then 99;
                        then only proved symbolic filters
Promotion criterion     some leftover has A_{L,o}=empty, preferably
                        an infinite near-convergent family
Stop criterion          every leftover has a witness; prefix ≡ endpoint
                        plus a0>=2; or it becomes an itinerary census
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Extremal path \(o_k=r(k)\) —
  **EXACT — HUMAN PROOF** (Beatty / integer power comparison)
- Ceiling Christoffel of slope \(o_{\min}/L\) —
  **KNOWN** (mechanical words); also prefix-admissible
- First-run `OO` and \(R(2)=0\) —
  already proved; the extremal path satisfies both
- `OOEOOE` as a forbidden string — not a symbolic ban
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_prefix_feasibility`
- Dataset: `data/research/juggler/cycle_finance/prefix_feasibility.json`
- Tests: `tests/research/juggler_sequence/test_cycle_prefix_feasibility.py`
- Window: the \(99\) run-type leftovers. Fast suite only. No CLI.
  No Lean.

## Conjectures

None opened. The leftover-killer slogan is recorded as
**REFUTED**
(`conjectures/refuted/juggler_cycle_prefix_feasibility_leftover_killer.json`).

## Counterexamples

Every one of the \(99\) leftovers, and in fact every positive
length, admits the extremal path \(o_k=r(k)\). Spotlight words
begin `OOEOOEOOEOEOOEOOEOEOOEOOEOOEOEOO`. The first isolated-`OE`
count is \(0\). The ceiling Christoffel word is a second witness
and matches that prefix on \(L=25781\) and \(L=55293\).

## Formalization

None. No `PrefixBalance.lean`. Paper A is unchanged.

## Results

- **Extremal path** — **EXACT — HUMAN PROOF**. The walk that
  emits `O` exactly when \(3^{o}<2^{k}\) stays on \(r(k)\), ends
  at \(o_{\min}(L)\), and starts `OOE`.
- **First-OO** — **COMPUTATIONALLY VERIFIED** on the \(99\):
  \(a_0=2\) and \(r=0=R(2)\). No prefix `OOEOE`.
- **Christoffel** — **COMPUTATIONALLY VERIFIED** on the \(99\):
  the integer ceiling word of slope \(o_{\min}/L\) is also
  prefix-admissible and first-OO legal.
- **No leftover dies** — **COMPUTATIONALLY VERIFIED**
  (`prefix_feasibility.json`): \(\mathcal A_{L,o}\) is nonempty
  for every run-type survivor. First survivor remains \(25781\)
  (\(o=16266\), min log-surplus \(\approx 2.55\cdot 10^{-5}\) at
  the endpoint). \(L=55293\) still lives (tightest recorded
  prefix surplus at \(k=50508\), still positive).
- sha256 of the \(99\) lengths:
  `9e2098923ccb39933630b116133a3fc2ddaf98ace4eb76dbab9b5ab9f6e604e6`.

## Open questions

None from prefix expansion. The order of letters does not add a
constraint beyond the endpoint plus \(a_0\ge 2\). Do not start a
itinerary census. Do not treat a symbolic path as an integer cycle.

## Decision

**CLOSE**. The unique extremal path \(o_k=r(k)\) is an admissible
symbolic prefix path for every leftover, including \(25781\) and
\(55293\). The ceiling Christoffel word is a second witness.
Prefix constraints are equivalent to the endpoint inequality plus
the already-proved first-run laws. Keep the construction as
negative knowledge. No Paper A edit, no ledger row, no Lean.

Best next question: none from prefix expansion.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.
