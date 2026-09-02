# Juggler cycle second-valley bound

Status: **ARCHIVED**

Compiled leftover written as
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).

Standalone application phase on the Juggler floor-power map, on the
**cycle half** of the `cycles_or_escapes` split. It asks whether
CycleMin geometry forces the other valleys on leftover
\(L=84\), \(m\ge 3\) to sit at \(\ge 281\). It is not a
leftover-itinerary census, not a floor raise, not a reopen of equal
valleys or the ceiling, and not a halt theorem.

## Problem

Equal-valleys recorded that height-split at floor \(261\) kills
leftover \(L=84\), \(m=3\) only if the other valleys sit at
\(\ge 281\). Unique visit gives only \(n+2=263\). Does
`cycleMin_not_odd_even`, `cycleMin_even_ge_sq`, and
`even_iter_lt_succ_pow` force that \(281\) bound?

## Exact statement

Write \(\theta=1-2^{84}/3^{53}\approx 0.002086\). On a `CycleMin`
of length \(84\) with \(o=53\) and \(m=3\), unique visit makes
the other two valleys distinct odds \(\ge n+2\). A first circuit
from \(n\) cannot start `OE` (`cycleMin_not_odd_even`). After
\(k\ge 2\) odds the even-run landing is an odd \(p\ge n\)
(`even_iter_lt_succ_pow` plus odd parity).

**Second-valley landing (REPARAMETERIZATION of
`even_iter_lt_succ_pow`).**
The first circuit from \(n=261\) can land at \(281\) (\(k=12\),
\(r=7\)). From that valley the next circuit can land at \(303\)
(\(k=12\), \(r=7\)). Both are the named upper cell.

**Second-valley leftover-killer (REFUTED).**
Forcing the other valleys to \(\ge 281\) excludes leftover
\(L=84\) at \(m=3\) at floor \(261\) under a proved constant
(\(6/5\) on \(\sum 1/(x\ln x)\), or the Lean inv-sum versus
\(\theta\cdot 61/11\)).

Counterexample: the Lean-allowed triple \(261,281,303\).

- height constant \(1\): RHS \(\approx 0.002024<\theta\) (not a
  proved form: the human-proof bound carries \(6/5\));
- height constant \(6/5\): RHS \(\approx 0.002429>\theta\);
- Lean inv-sum: \(S\approx 0.011868>\theta\cdot 61/11\approx 0.011568\).

Charging both others at \(281\) still misses the inv-sum
(\(S\approx 0.012126\)). Height \(6/5\) first kills at
\(n_2\ge 369\). A later `OE` landing at \(263\) exists
(\(v=1687\), \(T(v)=69290\)), but that start is itself a valley,
so the triple is \(261,263,1687\) and dies under every constant.
It is not the adversary.

No cycle of any length — not claimed.

## Current literature

- Height leftover period \(84\) with \(m\ge 3\) or \(\ge 85\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`)
- Equal-valleys \(n+2\); height-split would need \(281\) —
  **REFUTED** as a leftover-killer
  ([juggler_cycle_equal_valleys.md](juggler_cycle_equal_valleys.md))
- Upper cell \((p+1)^{2^r}\) —
  **REFUTED** as a leftover-killer
  ([juggler_cycle_ceiling_finance.md](juggler_cycle_ceiling_finance.md))
- Cheap \(m\ge 3\) refinements at floor \(261\) —
  **REFUTED**
  ([juggler_cycle_l84_m3.md](juggler_cycle_l84_m3.md))
- Residual-floor factory to \(1981\) / \(4756\) — **PARK**
- Every start reaches 1 — not claimed

Project relationship: **refuted** slogan; the \(281\) landing is
the existing cell.

## Branch budget

```text
Mathematical target     Do CycleMin + even_ge_sq + the upper cell
                        force every non-start valley ≥ 281 on leftover
                        L=84, m≥3 at floor 261?
Novelty hypothesis      281 is a forced landing, not a residual floor
Falsifier               a Lean-allowed triple has proved RHS ≥ θ
                        (or S ≥ θ log n)
Existing machinery      even_iter_lt_succ_pow, cycleMin_not_odd_even,
                        cycleMin_even_ge_sq, height_split killing
                        n2=281, leftover 84 with m≥3
Maximum Phase-0 scope   first-circuit k=2..24 at n=261; later
                        landings from 281; k=1 OE window; mixed
                        packing 261/281/303. No Lean, no floor
                        raise, no itinerary census
Promotion criterion     a forced valley bound that kills leftover
                        under a proved constant and is not the
                        ceiling cell
Stop criterion          the adversarial triple survives every
                        proved constant; or the bound is only
                        the named cell
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- First-circuit odd landing \(k=12\), \(p=281\) —
  **REPARAMETERIZATION** of `even_iter_lt_succ_pow`
- Later landing from \(281\), \(k=12\), \(p=303\) —
  **REPARAMETERIZATION** of the same cell
- Later `OE` once \(T(v)\) is even and \(\ge n^2\) —
  **EXACT — HUMAN PROOF** (`cycleMin_even_ge_sq`); the witness
  \(v=1687\) lands at \(263\)
- Second-valley leftover-killer for \(m=3\) at floor \(261\) —
  **REFUTED** (`juggler_second_valley_leftover_killer`)
- Residual floor \(273\) / \(1981\) — **PARK**
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_second_valley`
- Records: [juggler_cycle_second_valley.md](../research/juggler_cycle_second_valley.md),
  [juggler_cycle_second_valley.json](../research/juggler_cycle_second_valley.json)
- Dataset: `data/research/juggler/cycle_second_valley/`
- Tests: `tests/research/juggler_sequence/test_cycle_second_valley.py`

Science window: leftover \(L=84\) at floor \(261\), first-circuit
\(k=2,\ldots,24\), later landings from \(281\), \(k=1\) `OE`
window through \(v=20000\). No CLI. No new Lean. Paper A is
unchanged.

## Conjectures

`juggler_second_valley_leftover_killer` — **REFUTED**.

## Counterexamples

\(L=84\), \(o=53\), \(m=3\), valleys \(261,281,303\),
\(\theta\approx 0.002086\): constant \(6/5\) RHS \(\approx 0.002429\);
Lean inv-sum \(S\approx 0.011868>0.011568\). Both others at
\(281\) still has \(S\approx 0.012126\). The \(6/5\) killing
height is \(n_2\ge 369\).

## Formalization

None added. `even_iter_lt_succ_pow` and `cycleMin_even_ge_sq`
already exist. Not added: `CycleSecondValley.lean`,
`SecondValley.lean`, `ValleyFloor.lean`. No `sorry`. Paper A is
unchanged. Not a halt theorem.

## Results

Classification **CLOSED**. The slogan is false under every proved
constant.

- Height-split constant \(1\) first kills at \(281\). That form
  is not proved (it drops the \(6/5\) from
  \(-\ln(1-\delta)\le(6/5)\delta\)).
- Lean inv-sum misses even the ideal pair of extra valleys at
  \(281\).
- The first circuit from \(261\) can land at exactly \(281\).
  From there the next odd landing can be \(303\). Both sit
  below the \(6/5\) threshold \(369\).
- A landing at \(263\) is possible, but only as `OE` from a
  valley \(\ge 1687\). That triple dies and is not the
  adversary.
- The \(k=24\) raw ceiling landing \(304\) is even, so the
  actual odd valley on that run is \(92495\).

## Open questions

Stop. The laboratory leftover remains period \(84\) with
\(m\ge 3\), or \(\ge 85\). Do not raise the residual floor. Do
not open a leftover-itinerary census.

## Decision

**CLOSE**. The named \(281\) bound was attacked. The first-circuit
landing is `even_iter_lt_succ_pow`. The leftover-killer slogan is
false: the adversarial triple \(261,281,303\) survives both
proved constants, and Lean inv-sum misses even \(261,281,281\).
This is not a reason to raise the floor. Not a halt theorem.

Best next question: answered in
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).

## Publication assessment

Status: `ARCHIVED`. Negative knowledge. The unopened \(281\)
bound is now an evaluated finance attack, not an open object.
Not a paper candidate.
