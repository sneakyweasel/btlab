# Juggler position-dependent cycle finance

Status: **EXPLORATORY**

Compiled leftover written as
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).

Refinement of
[m-cycle finance](juggler_cycle_m_finance.md), not a new paper.
Joint-minima already splits valleys / climb interiors / evens. After
an odd run of length \(k\) the state is \(\asymp n^{(3/2)^k}\), so
most of the finance sum is far smaller than the \(T(n)\) bound.
Adversarial circuit-partition without a height law is a
reparameterization of `cycleMin_finance`; only a stronger height law
is new. Not a halt theorem, not a leftover-itinerary census, not a floor
raise, and not a claim that every positive integer reaches 1.

## Problem

The Collatz form after \(k\) odds is \(\asymp n\,3^k/2^k\). On the
Juggler floor-power map the analogous height is the odd iterate
\(\lfloor x^{3/2}\rfloor\), hence \(\asymp n^{(3/2)^k}\). Joint-minima
charges every climb interior at the first image \(T(n)\). That is
conservative once some circuit is forced to carry two or more extra
odds. Does the odd-run height law exclude leftover \((L,m)\) pairs
at the Lean residual floor \(257\), in particular \(L=38\) at small
\(m\)?

## Exact statement

On Juggler, every odd step with \(n\ge 3\) strictly increases and
every even step strictly decreases. An \(m\)-cycle is a cycle itinerary
with exactly \(m\) blocks \(O^{k_i}E^{l_i}\). Write
\(\theta=1-2^L/3^o\) and \(T(x)=\lfloor x^{3/2}\rfloor\) on odds.

**Odd-run height law (EXACT — HUMAN PROOF).**
Let \(x_0\to\cdots\to x_L=x_0\) be a `CycleMin` cycle with global
minimum \(n\ge 3\). Every local minimum \(n_i\) is odd and
\(n_i\ge n\). The odd step is nondecreasing on odd integers
(`floorPower_odd_mono`). After \(j\) consecutive odd steps from
\(n_i\), the state is at least \(\tau_j(n)\), where
\(\tau_0(n)=n\) and \(\tau_{j+1}(n)\) is the least odd integer
\(\ge T(\tau_j(n))\). In particular \(\tau_j(n)\asymp n^{(3/2)^j}\).
At the Lean floor \(n=257\), \(T(257)=4120\) is even, so
\(\tau_1=4121\) and \(\tau_2=T(4121)=264547\).

**Position-dependent finance (EXACT — HUMAN PROOF).**
There are \(m\) valleys and \(C=o-m\) climb interiors. At most
\(m\) interiors can sit at each height \(\tau_j\), \(j\ge 1\): a
circuit contributes at most one first-climb, at most one
second-climb, and so on. The worst-case \(6/5\)-sum is therefore
the greedy packing \(C_j=\min(m,\,C-\sum_{i<j}C_i)\),

\[
\theta
\;\le\;
\frac65\left(
\frac{m}{n\ln n}
+\sum_{j\ge 1}\frac{C_j}{\tau_j\ln\tau_j}
+\frac{L-o}{n^2\cdot 2\ln n}
\right).
\]

When \(C\le m\) this coincides with joint-minima (every climb can
sit at \(\tau_1\), which is \(T(n)\) or the next odd). Evens remain
at \(n^2\) (`cycleMin_even_ge_sq`). Adversarial circuit-partition
\(\theta\le\tfrac65\sum_k L_k/(\mu_k\ln\mu_k)\) with every
\(\mu_k=n\) is still a **REPARAMETERIZATION** of
`cycleMin_finance`.

**Length 38 at floor 257 (EXACT — HUMAN PROOF).**
The *existing* joint-minima bound already excludes every length-38
cycle, any \(m\le 14\). At \(n=257\), \(t=T(257)=4120\), the worst
case \(m=14\) has RHS \(=0.01215<\theta=0.02674\). Global
`cycleMin_finance` does not exclude \(L=38\)
(\(n_{\max}\approx 299\)). The Lean leftover
`cycle_itinerary_length_thirty_eight_or_ge_thirty_nine` is therefore not
sharp: \(38\) dies by extrema finance at the residual floor, not by
a height law and not by a leftover-itinerary census.

**Length 84 at small \(m\) (EXACT — HUMAN PROOF).**
Joint-minima at \(n=257\) misses every \(m\): already \(m=1\) has
RHS \(=0.002712>\theta=0.002086\). The height law kills \(m=1\)
(RHS \(=0.000928\)) and \(m=2\) (RHS \(=0.001804\)). For \(m\ge 3\)
both bounds survive. This is the first leftover near-convergent
that needs the height law at floor \(257\).

No cycle of any length — not claimed.

## Current literature

- Collatz \(m\)-cycle exclusion — **known**
  (`simons-de-weger-2005-collatz-m-cycles`). The Collatz height
  after \(k\) odds is \(\asymp n\,3^k/2^k\). This branch is the
  floor-power adaptation of that height, **independent** of Baker
  bounds.
- Whole-cycle finance — **EXACT — LEAN VERIFIED**
  (`cycleMin_finance`,
  [juggler_cycle_finance.md](juggler_cycle_finance.md)); Lean
  leftover is period \(84\) with \(m\ge 3\) or \(\ge 85\) at
  residual floor \(261\)
  (`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`)
- Joint-minima finance — **EXACT — HUMAN PROOF**
  ([juggler_cycle_m_finance.md](juggler_cycle_m_finance.md));
  tabulated there at floor \(53\), not at \(257\)
- Peak finance, extremal composition, cycle-gap Baker — not
  reopened
- Residual floor \(n<261\) reaches 1 — **EXACT — LEAN VERIFIED**
- Every start reaches 1 — not claimed

Project relationship: **extended** (refinement of m-finance).

## Branch budget

```text
Mathematical target     Does the Juggler odd-run height
                        τ_j ≍ n^{(3/2)^j}, packed at most m per
                        level, exclude leftover (L, m) at floor 257
                        that joint-minima (all climbs at T(n))
                        misses — in particular L=38 at small m?
Novelty hypothesis      only a stronger height law is new;
                        circuit-partition without it restates
                        cycleMin_finance
Falsifier               the packed height bound fails on the exact
                        identity, or every new (L, m) kill is
                        already a joint-minima or global-finance
                        restatement
Existing machinery      cycleMin_finance, joint-minima steiner_rhs,
                        cycleMin_even_ge_sq, floorPower_odd_mono,
                        floor 257, leftover 38 or ≥ 39
Maximum Phase-0 scope   dossier + probe: define τ_j; compare
                        joint-minima vs packed heights at floors
                        53 and 257; tabulate leftover (L, m).
                        No Lean, no CLI, no new paper, no floor raise
Promotion criterion     a height-law inequality that is not a
                        reparameterization and that excludes some
                        leftover (L, m) joint-minima misses
Stop criterion          REPARAMETERIZATION / no new leftover pair /
                        L=38 already dies by the old bound and the
                        height law adds nothing
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Odd-run height \(\tau_j\) — **EXACT — HUMAN PROOF** (this dossier)
- Position-dependent finance with greedy \(m\)-packing —
  **EXACT — HUMAN PROOF**
- No length-38 cycle at floor \(257\), any \(m\) —
  **EXACT — HUMAN PROOF** (existing joint-minima, new floor)
- Length-84 1-cycle and 2-cycle impossible at floor \(261\) —
  **EXACT — LEAN VERIFIED**
  (`no_cycleMin_length_eighty_four_of_circuit_le_two`)
- Laboratory leftover period \(84\) with \(m\ge 3\), or
  \(\ge 85\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`)
- Adversarial circuit-partition — **REPARAMETERIZATION** of
  `cycleMin_finance`
- Peak finance, extremal composition — not reopened
- No cycle of any length — not claimed
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_position_finance`
- Records: [juggler_cycle_position_finance.md](../research/juggler_cycle_position_finance.md),
  [juggler_cycle_position_finance.json](../research/juggler_cycle_position_finance.json)
- Dataset: `data/research/juggler/cycle_position_finance/`
- Tests: `tests/research/juggler_sequence/test_cycle_position_finance.py`
- Focus lengths \(19,38,84,168\). Finance-surviving scan \(L\le 200\)
  at floor \(257\). Comparison table at floor \(53\). Leftover-\(84\)
  kill floors: `l84_floors.json` (live Lean floor \(261\)).
- No CLI. Lean leftover in `CycleHeightFinance.lean` (not a
  `PositionFinance` / `CyclePositionFinance` layer). Paper A is
  unchanged.

## Conjectures

None opened.

## Counterexamples

None to the packed height-law inequality.

Adversarial \(\mu_k=n\) circuit-partition never beats
`cycleMin_finance`. The hypothesis that a height law is needed to
kill \(L=38\) at floor \(257\) is **false**: joint-minima already
does it for every \(m\).

## Formalization

`CycleHeightFinance.lean` sits on `CycleFinance.lean` and packages
the inv-sum height cap at floor \(261\): length \(84\) with at
most two odd-runs is impossible, leftover
`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`.
Not added: `CyclePositionFinance.lean`, `PositionFinance.lean`,
`cycle_position_finance`, `cycle_height_finance`,
`OddRunHeight`. The full \(6/5\) greedy packing stays
**EXACT — HUMAN PROOF**. No `sorry`. Paper A is unchanged. Not a
halt theorem.

## Results

Classification **POSITION_FINANCE_GREEN**. Regenerate with
`python -m research.juggler_sequence.cycle_position_finance`.

- **Odd-run height law** — **EXACT — HUMAN PROOF**: after \(j\)
  consecutive odds from a valley \(\ge n\), the state is at least
  \(\tau_j(n)\). This is the Juggler form of \(\asymp n\,3^k/2^k\).
- **Position-dependent packing** — **EXACT — HUMAN PROOF**: the
  displayed inequality. It is the joint-minima log-unroll with
  climb interiors charged at successive \(\tau_j\), not a new
  defect law.
- **Length 38** — **EXACT — HUMAN PROOF**: excluded for every
  \(m\) by *joint-minima* at floor \(257\). The height law is not
  required. Global finance leaves \(n_{\max}\approx 299>257\).
  The same joint-minima evaluation also kills every finance
  survivor \(\le 200\) except the near-convergents
  \(84,103,168,187\) (and length \(19\), already dead by global
  finance at this floor).
- **Length 84** — **EXACT — LEAN VERIFIED** at constant \(1\)
  and floor \(261\): at most two odd-runs are impossible
  (`no_cycleMin_length_eighty_four_of_circuit_le_two`). The
  \(6/5\) greedy packing that also kills \(m=1,2\) at floor
  \(257\) remains **EXACT — HUMAN PROOF**. Joint-minima excludes
  none. Length \(168\) dies for \(m\le 4\) by the same packing;
  \(103\) and \(187\) lose a few large-\(m\) slots.
- **Leftover-\(84\) kill floors** — **COMPUTATIONALLY VERIFIED**
  (existing inequalities evaluated at new \(n\); `l84_floors.json`).
  Lean constant \(1\): height kills \(m=1\) at \(121\), \(m=2\)
  at \(199\), \(m=3\) at \(273\); joint and height kill every
  \(m\) at \(1981\); global finance at \(4756\). Constant \(6/5\):
  all-\(m\) at \(2325\), global \(n_{\max}=5599\). Killing every
  \(m\) is limited by \(m=31\) (all valleys at \(n\)); the two
  bounds coincide there. A \(4756\) residual-floor campaign is
  \(2247\) new odd certificates (peak \(19694\) bits at
  \(n=2183\)). The all-\(m\) campaign at \(1981\) is still
  \(859\) odds (peak \(900\) bits). Both are machinery gravity.
  Height already killed the 1-cycle and 2-cycle cases at the
  current floor. The hypothesis that \(4756\) is the cheapest
  kill is **REFUTED**.
- **Floor 53 comparison** — the height law also newly kills
  \(L=19\) at \(m=2\) and \(L=38\) at \(m=3,4\), which is
  academic once the residual floor is \(257\).
- No cycle of any length — not claimed.

## Open questions

The Lean leftover is
`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`.
Excluding length \(84\) at \(m\ge 3\) at floor \(261\) is
**REFUTED**
([juggler_cycle_l84_m3.md](juggler_cycle_l84_m3.md)).
The upper cell \((p+1)^{2^r}\) is also **REFUTED** as a
leftover-killer
([juggler_cycle_ceiling_finance.md](juggler_cycle_ceiling_finance.md)).
A second-valley bound \(\ge 281\) is also **REFUTED**
([juggler_cycle_second_valley.md](juggler_cycle_second_valley.md)).
Raising the residual floor to \(1981\) or \(4756\) to kill every
\(m\) is **PARK**. The full \(6/5\) greedy packing and the
length-38 joint-minima evaluation stay human proof.

## Decision

**PROMOTE**. The odd-run height law is not a reparameterization of
`cycleMin_finance` and it excludes leftover \((L,m)\) that
joint-minima misses — in particular every length-84 1-cycle and
2-cycle at floor \(261\), now **EXACT — LEAN VERIFIED**. Length
\(38\) dies for every \(m\) by the *old* joint-minima bound at
floor \(257\), so the motivating \(L=38\) example is a floor
evaluation, not a height-law consequence. Circuit-partition
without a height law remains a reparameterization. Not a new
paper. Not a halt theorem.

The residual-floor campaign to \(1981\) or \(4756\) is **PARK**.

Best next question: answered in
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).
Length \(84\) at \(m\ge 3\) at floor \(261\) is closed as a
leftover-killer.

## Publication assessment

Status: `EXPLORATORY`. Refinement of m-finance, not a new paper.
The \(m\le 2\) leftover at constant \(1\) is **EXACT — LEAN
VERIFIED**. The full \(6/5\) greedy packing and the length-38
joint-minima evaluation remain human proof. Not a totality
result, not Paper A.
