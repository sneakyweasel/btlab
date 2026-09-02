# Juggler m-cycle finance

Status: **EXPLORATORY**

Compiled leftover written as
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).

Standalone application phase on the Juggler floor-power map, on the
**cycle half** of the `cycles_or_escapes` split. It transfers the
Simons–de Weger m-cycle / circuit template — log-unroll of
`CycleFinance` at each local minimum, not only at `CycleMin` — and
asks whether \(m\) small minima can jointly pay a large formal
surplus. It is not a halt theorem, not a leftover-itinerary census, not a
floor raise, not a reopen of peak finance or extremal composition,
and not a claim that every positive integer reaches 1.

## Problem

Collatz \(m\)-cycles are classified by the number of local minima.
Juggler already has whole-period finance at the global minimum
(`cycleMin_finance`) and one-peak finance (`cycle_peak_finance`).
Composing min / first-even / top-cell / peak scale laws closed as
envelope repackaging. What has not been tried is the log-unroll at
each local minimum separately.

## Exact statement

On Juggler, every odd step with \(n\ge 2\) strictly increases and
every even step strictly decreases. A **local minimum** is a cyclic
even-to-odd landing. A **local maximum** is a cyclic odd-to-even
landing. An **\(m\)-cycle** is a cycle itinerary with exactly \(m\)
blocks \(O^{k_i}E^{l_i}\).

**Joint-minima finance (EXACT — HUMAN PROOF).**
Let \(x_0\to\cdots\to x_L=x_0\) be a `CycleMin` cycle of length
\(L\), \(o\) odd letters, \(m\) local minima, and start \(n\ge 53\).
Write \(\theta=1-2^L/3^o\) and \(t=\lfloor n^{3/2}\rfloor\). The
existing per-step identity gives
\(\theta\le\tfrac65\sum_i 1/(x_i\ln x_i)\). Local minima contribute
at most \(m/(n\ln n)\). Every other odd is a climb interior, hence
at least \(T(n)=t\). Every even is at least \(n^2\)
(`cycleMin_even_ge_sq`). Therefore

\[
\theta
\;\le\;
\frac65\left(
\frac{m}{n\ln n}
+\frac{o-m}{t\ln t}
+\frac{L-o}{n^2\cdot 2\ln n}
\right).
\]

If the right-hand side at \(n=53\) is already smaller than
\(\theta\), no such cycle exists (the right-hand side decreases in
\(n\)).

At \(n=53\), \(t=385\). In particular:

- \(L=19\), \(o=12\), \(m=1\): RHS \(=0.01184<\theta=0.01346\).
  A length-19 **1-cycle** is impossible.
- \(L=30\), \(o=19\), any \(m\le 11\): even the worst case
  \(m=11\) has RHS \(=0.06751<\theta=0.07616\).
  **No length-30 cycle exists.**

Whole-period finance at the same floor leaves both lengths live
(\(n_{\max}(19)\approx 297\), \(n_{\max}(30)\approx 102\)).

The error-free Steiner copy \(\theta<\tfrac65\sum_i 1/(n_i\ln n_i)\)
is not claimed: climb and even remainders are positive. Adversarial
circuit-partition \(\theta\le\tfrac65\sum_k L_k/(\mu_k\ln\mu_k)\)
with every \(\mu_k=n\) is a **REPARAMETERIZATION** of
`cycleMin_finance`.

No cycle of any length — not claimed.

## Current literature

- Collatz \(m\)-cycle exclusion by financing-versus-gap plus
  \(\lvert 2^L-3^o\rvert\) — **known**
  (`simons-de-weger-2005-collatz-m-cycles`). Steiner's 1-cycle form
  is \(0<\Lambda<1/x_{\min}\); the \(m\)-cycle form is
  \(0<\Lambda<\sum_i 1/x_i\). This branch is the floor-power
  adaptation at extrema, **independent** of that proof's details.
- Whole-cycle finance — **EXACT — LEAN VERIFIED**
  (`cycleMin_finance`,
  [juggler_cycle_finance.md](juggler_cycle_finance.md))
- Peak-block finance — **REPARAMETERIZATION**
  (`cycle_peak_finance`,
  [juggler_cycle_peak_descent.md](juggler_cycle_peak_descent.md))
- Extremal composition — **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_extremal_composition.md](juggler_cycle_extremal_composition.md))
- Cycle-gap Baker transfer — **CLOSE** / **REFUTED** as a leftover
  killer
  ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md))
- Residual floor \(n<53\) reaches 1 — **EXACT — LEAN VERIFIED**
- Every start reaches 1 — not claimed

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Does the CycleFinance log-unroll, applied at each
                        local minimum / Simons circuit rather than only at
                        CycleMin, produce a joint bound
                        θ < C Σ_i 1/(n_i ln n_i)
                        that is strictly stronger than
                        n ln n · (3^o − 2^L) ≤ L · 3^o,
                        and does it exclude any leftover (L, m) at floor 53?
Novelty hypothesis      Steiner–Simons Λ < Σ 1/x_i on the floor-power map
Falsifier               the joint-minima form fails on the exact identity
                        or on transient circuits; or every leftover (L, m)
                        restates cycleMin_finance
Existing machinery      cycleMin_finance, cycle_peak_finance,
                        cycle_distinguished_order, global_defect_identity,
                        even-count ≥ 4, floor 53, leftover 19 or ≥ 30
Maximum Phase-0 scope   dossier + probe: define m-cycle/circuits; derive
                        or refute the joint bound; tabulate leftover
                        (L, m); transient circuit census. No Lean, no CLI,
                        no floor raise, no Paper A
Promotion criterion     a new inequality that is not a reparameterization
                        and that excludes some leftover (L, m)
Stop criterion          REPARAMETERIZATION / minima-only bound REFUTED /
                        no leftover (L, m) dies that global finance misses
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Joint-minima finance with climb/even error terms —
  **EXACT — HUMAN PROOF** (this dossier)
- Length-19 1-cycle impossible at floor 53 —
  **EXACT — HUMAN PROOF**
- No length-30 cycle at floor 53, any \(m\) —
  **EXACT — HUMAN PROOF**
- Cycle-like transient concentration
  \(\sum 1/(x\ln x)\le 1.21\sum 1/(n_i\ln n_i)\) on named starts —
  **OBSERVATION**
- Error-free Steiner copy \(\theta<\tfrac65\sum 1/(n_i\ln n_i)\) —
  not claimed
- Adversarial circuit-partition — **REPARAMETERIZATION** of
  `cycleMin_finance`
- Peak finance, extremal composition — not reopened
- No cycle of any length — not claimed
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_m_finance`
- Records: [juggler_cycle_m_finance.md](../research/juggler_cycle_m_finance.md),
  [juggler_cycle_m_finance.json](../research/juggler_cycle_m_finance.json)
- Dataset: `data/research/juggler/cycle_m_finance/`
- Tests: `tests/research/juggler_sequence/test_cycle_m_finance.py`
- Named transients: \(25,37,77,365,1999,30817\). Leftover table
  \(L\in\{19,30,84\}\). Lean-surviving scan \(L\le 90\).
- No CLI. No new Lean. Paper A is unchanged.

## Conjectures

None opened.

## Counterexamples

None to the joint-minima inequality with error terms.

The error-free Steiner copy is not an identity: climb and even
states contribute a positive remainder. Terminal transient circuits
that drop below 12 (365 lands at 5; 1999 lands at 11) inflate the
raw full/minima ratio to \(\approx 12\). Those landings are residual
class, not cycle valleys. On cycle-like circuits (both valleys
\(\ge 12\)) the same orbits have ratio \(1.01\)–\(1.21\).

Adversarial \(\mu_k=n\) circuit-partition never beats
`cycleMin_finance`.

## Formalization

None added. `CycleFinance.lean` and `CycleExtrema.lean` are
unchanged. Not added: `CycleMFinance.lean`, `CircuitFinance.lean`,
`cycle_m_finance`, `cycle_circuit_finance`, `CycleLocalMin`,
`no_juggler_cycle`. No `sorry`. Paper A is unchanged. Not a halt
theorem.

## Results

Classification **M_CYCLE_FINANCE_GREEN**. Regenerate with
`python -m research.juggler_sequence.cycle_m_finance`.

- **Joint-minima finance** — **EXACT — HUMAN PROOF**: the displayed
  inequality. It is the CycleFinance log-unroll with the sum split
  at Simons circuits, using `cycleMin_even_ge_sq` and odd growth,
  not a new defect law.
- **Length 19 as a 1-cycle** — **EXACT — HUMAN PROOF**: excluded at
  floor 53. Length 19 with \(m\ge 2\) still survives
  (\(m=7\) has RHS \(0.0429>\theta\)).
- **Length 30** — **EXACT — HUMAN PROOF**: excluded for every
  \(m\le 11\). The Lean leftover `19 or ≥ 30` is therefore not
  sharp: 30 dies by extrema finance, not by a floor raise.
- **Other Lean-surviving lengths \(\le 90\) killed for all \(m\)**
  — **COMPUTATIONALLY VERIFIED** at the 6/5 constant:
  \(30,41,44,52,55,60,63,66,71,74,77,82,85,88,90\). Near-convergents
  \(19\) (\(m\ge 2\)), \(38\), \(57\), \(76\), \(84\) survive.
- **Valley concentration on transients** — **OBSERVATION**:
  cycle-like full/minima \(\le 1.21\) on the named starts.
- No cycle of any length — not claimed.

## Open questions

The Lean leftover is
`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`
(floor \(261\)). Evaluating the *same* joint-minima bound at
floor \(257\) excludes every length-38 cycle; the odd-run height
refinement
([juggler_cycle_position_finance.md](juggler_cycle_position_finance.md))
kills length \(84\) as a 1-cycle or 2-cycle in Lean. Joint-minima
kills no \(m\) for \(L=84\) at the live floor. Raising the
residual floor to \(1981\) (all \(m\)) or \(4756\) (global
finance) is **PARK**. Excluding length \(84\) at \(m\ge 3\) at
floor \(261\) is **REFUTED**
([juggler_cycle_l84_m3.md](juggler_cycle_l84_m3.md)).
The upper cell \((p+1)^{2^r}\) is also **REFUTED** as a
leftover-killer
([juggler_cycle_ceiling_finance.md](juggler_cycle_ceiling_finance.md)).
A second-valley bound \(\ge 281\) is also **REFUTED**
([juggler_cycle_second_valley.md](juggler_cycle_second_valley.md)).

## Decision

**PROMOTE**. The CycleFinance log-unroll at each local minimum, with
the climb/even error terms forced by `CycleMin` geometry, is a new
inequality and it excludes leftover \((L,m)\) pairs that
`cycleMin_finance` misses — in particular every length-30 cycle and
every length-19 1-cycle. Adversarial circuit-partition is a
reparameterization and is not promoted. No Lean in this phase. Paper
A is unchanged. Not a halt theorem.

Best next question: answered in
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).
Length \(84\) at \(m\ge 3\) at floor \(261\) is **REFUTED**
([juggler_cycle_l84_m3.md](juggler_cycle_l84_m3.md)). The
floor-\(257\) evaluation, the height leftover, and the PARK of
the \(4756\) residual-floor campaign are recorded in
[juggler_cycle_position_finance.md](juggler_cycle_position_finance.md).

## Publication assessment

Status: `EXPLORATORY`. One exact human-proof inequality with a
genuine leftover consequence (length 30 dies; length 19 cannot be a
1-cycle) and a clear literature distinction: Steiner–Simons
\(\Lambda<\sum 1/x_i\) transferred to the floor-power map at
extrema. Not Lean, not a totality result, not Paper A.
