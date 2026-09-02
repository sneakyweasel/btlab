# Juggler prefix growth / retention balance

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a new cell,
not a \(Q\)-descriptor reopen, not a scalar Lyapunov attempt, not
Paper A, and not a claim that every positive integer reaches 1.

After local and mesoscopic compression of the leftover
`AboveAnchor` trajectory failed, this phase asks whether an
**exact finite-prefix balance law** constrains infinite residual
orbits independently of the known word envelope.

## Problem

Can an infinite `AboveAnchor` orbit keep enough cumulative
expansion to stay above \(n\) forever, once even contractions and
floor losses are written as one prefix identity?

## Exact statement

Write \(x_0=n\) and \(x_{i+1}=T(x_i)\). For a prefix of length
\(k\) let \(O_k\) be the number of odd states among
\(x_0,\ldots,x_{k-1}\) and \(E_k=k-O_k\). The existing envelope is

\[
x_k^{2^k}\le n^{3^{O_k}}.
\]

Define the power-form retention by

\[
x_k^{2^k}=n^{3^{O_k}}F_k,
\qquad
0<F_k\le 1.
\]

`AboveAnchor` on that prefix is \(x_k\ge n\). Phase 0 asks whether
either of the proposed survival laws

\[
3^{O_k}\ge 2^k,
\qquad
F_k\ge n^{2^k-3^{O_k}}
\]

is a new global budget, or whether both are restatements of
`power_bound_word` and \(x_k\ge n\).

This is not a halt theorem.

## Current literature

- Finite-itinerary envelope \(x_k^{2^k}\le n^{3^{O_k}}\) —
  **EXACT — LEAN VERIFIED** (`J-power-envelope-contraction`)
- `AboveAnchor` plus \(3^{O_k}<2^k\) forbids the prefix —
  **EXACT — LEAN VERIFIED** (`aboveAnchor_not_envelope_drop`)
- Weighted floor product
  \(n^{3^{O_k}}=x_k^{2^k}+\Delta_w(n)\) —
  **EXACT — LEAN VERIFIED** (`J-global-defect-identity`)
- Log-slack comparison \(c<(\lambda-1)\log n\) is \(T_w(n)>n\) —
  **REPARAMETERIZATION** (`J-weighted-slack-cocycle`)
- Compensated contraction \(\Delta>n^{3^O}-n^{2^k}\Rightarrow x_k<n\) —
  **EXACT — LEAN VERIFIED** (`power_bound_compensated_contracts`)
- Naive path-sum of local defects —
  **CLOSE** (`juggler_sum_rho.md`)
- First-defect Amplify versus surplus on leftovers —
  **REFUTED** as an independent leftover halt
  (`juggler_amplify_surplus.md`)
- Normalized residual \(R=\Delta/S\) —
  **CLOSE** (`juggler_normalized_defect.md`)
- Odd-run financing \(n^{2^{a+1}}\le x^{3^a}\) —
  **EXACT — LEAN VERIFIED**
- Compressed \(Q\)-predictors and Poincaré \(Q\)-sections —
  **PARK** (`juggler_block_map_q.md`,
  `juggler_q_return_section.md`)
- Every start reaches 1 — not claimed

Project relationship: **extended**, then **reparameterized**. The
designated global question after \(Q\)-section PARK.

## Branch budget

```text
Mathematical target     a prefix growth/retention law that
                        constrains infinite AboveAnchor orbits
                        independently of the itinerary envelope
Novelty hypothesis      required retention F_k >= n^{2^k-3^{O_k}}
                        is a new budget, or leftover prefixes
                        separate min F from max F
Falsifier A             arbitrarily long prefixes with Gamma>=1
                        and retention bounded away from 0
Falsifier B             near-maximal odd lifts with no increasing
                        cost (Amplify already failed this)
Falsifier C             even resets compensate arbitrary odd loss
Falsifier D             the exact inequality is x_k >= n rewritten
Existing machinery      power_bound_word; aboveAnchor_not_envelope_drop;
                        globalDefect; compensated contraction;
                        leftovers 365, 501, 1517, 6187
Maximum Phase-0 scope   algebraic identity; leftover prefix tables;
                        modest odd window; no Lean; no itinerary census
Promotion criterion     a necessary law not equivalent to
                        3^{O}>=2^{k} or x_k>=n, or a floor upper
                        bound on F that is not Delta
Stop criterion          restatement of the envelope; another
                        scalar; cell list; ReturnSection.lean;
                        Q-descriptor; W_5; Amplify reopen
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\Gamma_k=3^{O_k}/2^k\) — **REPARAMETERIZATION** of the
  existing envelope exponents
- \(F_k=x_k^{2^k}/n^{3^{O_k}}\) — **REPARAMETERIZATION** of
  \(1-\Delta_w(n)/n^{3^{O_k}}\)
- \(F_k\ge n^{2^k-3^{O_k}}\) — **REPARAMETERIZATION** of
  \(x_k\ge n\) (`J-prefix-retention-budget`)
- Mean odd-run \(O_k/E_k\) — **REPARAMETERIZATION** of
  \(3^{O_k}\ge 2^k\)
- Weighted \(\rho\)-product — **KNOWN** (`globalDefect`)
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.growth_balance`
- Records: [juggler_growth_balance.md](../research/juggler_growth_balance.md),
  [juggler_growth_balance.json](../research/juggler_growth_balance.json)
- Tests: `tests/research/juggler_sequence/test_growth_balance.py`

No CLI. No Lean. No \(\alpha\)-grid. No return-itinerary census.

## Conjectures

None opened.

## Counterexamples

None required. The preferred independent-budget hypothesis is
false by algebra, not by a special start.

On leftovers, every prefix with \(x_k\ge n\) has \(3^{O_k}\ge 2^k\),
and the first drop is a formally contracting prefix
(\(3^{O}<2^{k}\)). That is `aboveAnchor_not_envelope_drop` plus
`power_bound_lt_pow`, not a new obstruction.

## Formalization

None added. Existing `Envelope`, `GlobalDefect`, and
`MinimumRelative` already contain the identities. No
`GrowthBalance.lean`. No `sorry`.

## Results

Classification **GROWTH_BALANCE_CLOSED**.

Write \(x_k^{2^k}=n^{3^{O_k}}F_k\). Then

\[
F_k\ge n^{2^k-3^{O_k}}
\iff
x_k^{2^k}\ge n^{2^k}
\iff
x_k\ge n.
\]

So the boxed minimum required retention is `AboveAnchor` on that
prefix. The boxed growth law \(3^{O_k}\ge 2^k\) is the envelope
plus \(x_k\ge n\), already Lean as
`aboveAnchor_not_envelope_drop`. The weighted floor product is
`globalDefect`. The two bounds never separate because they are
the same inequality.

Leftover prefixes \(365,501,1517,6187\) (and contrast \(69,89\))
stay in the noncontracting exponent region until the drop
letter, which is an extra even step that makes \(3^{O}<2^{k}\).
Mean odd-run lengths sit just above
\(\log 2/(\log 3-\log 2)\), which is the same comparison.

This is Falsifier D. It is not Falsifier A: leftovers are finite
and do drop, but they drop by the existing formal envelope, not
by a new retention budget.

## Open questions

None from prefix-level growth or retention budgets. Do not
build `GrowthBalance.lean`. Do not reopen Amplify, sum-\(\rho\),
normalized defect, \(Q\)-descriptors, Poincaré sections, \(W_5\),
or Paper A.

## Decision

**CLOSE**. Every proposed aggregate law is `KNOWN` or a
`REPARAMETERIZATION` of `power_bound_word`, `globalDefect`, or
\(x_k\ge n\). A branch of that kind is a close, however attractive
the product calculus looks. The leftover residual is still the
integer landing. Infinite `AboveAnchor` is not ruled out by
rewriting the envelope.

Best next question: none from prefix growth/retention balance.

## Publication assessment

Status: `EXPLORATORY`.

A negative global-budget fragment. Not a paper candidate and
not a Juggler totality result.
