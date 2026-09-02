# Juggler cycle ceiling finance

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map, on the
**cycle half** of the `cycles_or_escapes` split. It attacks the
named even-run upper cell \((p+1)^{2^r}\) as leftover finance. It
is not a leftover-itinerary census at the peak, not a floor raise, not
a `PositionFinance` layer, and not a halt theorem.

## Problem

A leftover cycle cannot put almost all of its \(1/(x\ln x)\) mass
at the valleys: enough of the orbit is forced into the top window
that \(\sum 1/(x\ln x)<\theta\).

Everything else either was run and collapsed to the envelope, or
is a leftover-itinerary census at the peak, or is another floor raise.
The upper cell \((p+1)^{2^r}\) is the only named object that was
recorded (`even_iter_lt_succ_pow`) and then left unused.

Does that ceiling, coupled to the odd-run height of the peak,
exclude leftover length \(84\) at \(m\ge 3\) at the live residual
floor \(261\)?

## Exact statement

Write \(\theta=1-2^{84}/3^{53}\approx 0.002086\). On a `CycleMin`
of length \(84\) with \(o=53\) odd letters and \(m\) odd-runs, some
odd-run has length \(k\ge\lceil 53/m\rceil\). After \(k-1\) odds
from a valley \(\ge n\) the state is at least \(\tau_{k-1}\). The
next odd step produces an even
\(M_{\min}=T(\tau_{k-1})\), or \(T(\tau_{k-1})+1\) if that image is
odd. The top even-run of length \(r\) then satisfies

\[
M<(p+1)^{2^r}
\]

(`even_iter_lt_succ_pow`). Combined with \(M\ge M_{\min}\) and
monotone integer square-root,

\[
p\ge\operatorname{isqrt}^{r}(M_{\min}).
\]

`CycleMin` forces \(p\ge n\), so \(r\) cannot exceed the last root
that stays at least \(n\). The adversarial choice (smallest
landing, largest finance RHS) is that maximal \(r\). Height packing
then charges one valley at this \(p\) and the other \(m-1\) at
\(n\).

**Ceiling landing (REPARAMETERIZATION of
`even_iter_lt_succ_pow`).**
The displayed root bound is the named upper cell plus monotone
`isqrt`. It is not a new defect law.

**Ceiling leftover-killer (REFUTED).**
That landing, stacked on height packing, excludes every length-\(84\)
`CycleMin` with \(m\ge 3\) at floor \(261\) under a proved constant
(\(6/5\) on \(\sum 1/(x\ln x)\), or the Lean inv-sum versus
\(\theta\cdot 61/11\)).

Counterexample: \(n=261\), \(m=3\), peak run \(k=24\),
\(r=14\), \(p=304\). Then

- height constant \(1\): RHS \(\approx 0.002079<\theta\) (not a
  proved form: the human-proof bound carries \(6/5\));
- height constant \(6/5\): RHS \(\approx 0.002495>\theta\);
- Lean inv-sum: \(S\approx 0.012130>\theta\cdot 61/11\approx 0.011568\).

The \(6/5\) form first kills at \(p\ge 659\); the inv-sum form
first kills at \(p\ge 367\). The pigeonhole length \(k=18\) lands
at \(p=3075\) and would kill both; a leftover \(m=3\) word may
use \(k=24\). Every \(k=25,\ldots,51\) has a log-two lower bound
strictly above \(304\). Larger \(m\) is worse (more valleys at
\(n\)).

No cycle of any length — not claimed.

## Current literature

- Even-run upper cell \(M<(p+1)^{2^r}\) —
  **EXACT — LEAN VERIFIED** (`even_iter_lt_succ_pow`,
  [juggler_cycle_top_excursion.md](juggler_cycle_top_excursion.md))
- Nested top cells and peak descent —
  **EXACT — LEAN VERIFIED**; composing them is envelope
  **REPARAMETERIZATION**
  ([juggler_cycle_extremal_composition.md](juggler_cycle_extremal_composition.md))
- Height leftover period \(84\) with \(m\ge 3\) or \(\ge 85\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`)
- Cheap \(m\ge 3\) refinements at floor \(261\) —
  **REFUTED**
  ([juggler_cycle_l84_m3.md](juggler_cycle_l84_m3.md))
- Residual-floor factory to \(1981\) / \(4756\) — **PARK**
- Every start reaches 1 — not claimed

Project relationship: **refuted** slogan; the landing corollary
is the existing cell.

## Branch budget

```text
Mathematical target     Does M < (p+1)^{2^r} plus the odd-run
                        height of the peak force a landing
                        p ≥ iterated_isqrt(M_min, r) that puts
                        leftover L=84, m≥3 below θ at floor 261?
Novelty hypothesis      the unused upper cell couples peak height
                        to a valley that height packing still
                        charges at n
Falsifier               adversarial r still leaves some m≥3 with
                        proved RHS ≥ θ (or S ≥ θ log n)
Existing machinery      even_iter_lt_succ_pow, odd-run heights,
                        cycleMin_even_ge_sq, height packing,
                        leftover 84 with m≥3
Maximum Phase-0 scope   exact landing table at n=261 for peak
                        runs k=18..24 and a pigeonhole m-table;
                        no Lean, no floor raise, no peak-word
                        census
Promotion criterion     a new leftover (L, m) kill that is not
                        height packing, not a floor raise, and
                        not a leftover-itinerary census
Stop criterion          some leftover m survives under every
                        proved constant; or the coupling is only
                        the named cell
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Ceiling landing \(p\ge\operatorname{isqrt}^{r}(M_{\min})\) —
  **REPARAMETERIZATION** of `even_iter_lt_succ_pow`
- Pigeonhole \(k=18\) landing \(p=3075\) excludes \(m=3\) —
  **COMPUTATIONALLY VERIFIED**, and not the leftover (the itinerary
  may use a longer peak run)
- Ceiling leftover-killer for every \(m\ge 3\) at floor \(261\) —
  **REFUTED** (`juggler_ceiling_finance_leftover_killer`)
- Adversarial \(k=24\), \(r=14\), \(p=304\) misses \(6/5\) and
  the Lean inv-sum —
  **COMPUTATIONALLY VERIFIED**
- Residual floor \(273\) / \(1981\) — **PARK**
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_ceiling_finance`
- Records: [juggler_cycle_ceiling_finance.md](../research/juggler_cycle_ceiling_finance.md),
  [juggler_cycle_ceiling_finance.json](../research/juggler_cycle_ceiling_finance.json)
- Dataset: `data/research/juggler/cycle_ceiling_finance/`
- Tests: `tests/research/juggler_sequence/test_cycle_ceiling_finance.py`

Science window: leftover \(L=84\) at floor \(261\), exact peak
runs \(k=18,\ldots,24\), log-two lower bounds through \(k=51\),
pigeonhole \(m=3,\ldots,31\). No CLI. No new Lean. Paper A is
unchanged.

## Conjectures

`juggler_ceiling_finance_leftover_killer` — **REFUTED**.

## Counterexamples

\(L=84\), \(o=53\), \(m=3\), \(n=261\), peak run \(k=24\),
\(r=14\), \(p=304\), \(\theta\approx 0.002086\): constant \(6/5\)
RHS \(\approx 0.002495\); Lean inv-sum \(S\approx 0.012130>
0.011568\). The \(6/5\) killing landing is \(p\ge 659\); the
inv-sum killing landing is \(p\ge 367\).

## Formalization

None added. `even_iter_lt_succ_pow` already exists in
`CycleExtrema.lean`. Not added: `CycleCeilingFinance.lean`,
`CeilingFinance.lean`, `TopWindowFinance.lean`,
`cycle_ceiling_finance`. No `sorry`. Paper A is unchanged. Not a
halt theorem.

## Results

Classification **CLOSED**. The slogan is false at floor \(261\).

- The upper cell does force a landing above \(n\) for every
  tested peak run. That is the named cell, not a new inequality.
- Pigeonhole \(k=18\) is the *best* case for exclusion
  (\(p=3075\)), not the worst. The fractional part
  \(\{k\log_2(3/2)\}\) can sit near \(0\), and then
  \(p\approx n^{1+\varepsilon}\).
- The worst exact run in \(18\le k\le 24\) is \(k=24\),
  \(p=304\). Log-two lower bounds for \(k=25,\ldots,51\) all
  sit above \(304\).
- Neither proved finance form kills \(k=24\). Constant \(1\) on
  \(\sum 1/(x\ln x)\) would, by \(0.31\%\), but that drops the
  \(6/5\) from \(-\ln(1-\delta)\le(6/5)\delta\).
- Large \(m\) keeps almost all valleys at \(n\). The top window
  holds one even-run, not almost all of the orbit.

## Open questions

Stop. The laboratory leftover remains period \(84\) with
\(m\ge 3\), or \(\ge 85\). Do not raise the residual floor. Do
not open a leftover-itinerary census of peak runs.

## Decision

**CLOSE**. The named ceiling was attacked. The coupling is
`even_iter_lt_succ_pow` plus monotone `isqrt`. The leftover-killer
slogan is false: a leftover \(m=3\) word can run \(k=24\) odds
and land at \(304\), and both proved constants survive. This is
not a reason to raise the floor. Not a halt theorem.

Best next question: answered in
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).

## Publication assessment

Status: `ARCHIVED`. Negative knowledge. The unused upper cell is
now an evaluated finance attack, not an open object. Not a paper
candidate.
