# Juggler cycle peak count

Status: **ARCHIVED**

Refinement of
[juggler_cycle_finance.md](juggler_cycle_finance.md) and
[juggler_cycle_m_finance.md](juggler_cycle_m_finance.md),
not a new paper. After the closed return-cost / descent leftover-killers,
this phase asks whether peak count \(p\) is a new structural axis
between Section 3 run form and Section 4 finance. Not a halt theorem,
not a leftover-itinerary census, not a floor raise, and not a reopen of
Section 5.

## Problem

On a CycleMin itinerary, write the parity itinerary in run form
\(O^{a_1}E^{b_1}\cdots O^{a_p}E^{b_p}\) with \(a_i,b_i\ge 1\) and
\(a_1\ge 2\). Then \(p\) is the number of nonempty odd runs. Is
\(p=1\) impossible for an elementary cell/return reason that is not
already height finance?

## Exact statement

**Identity (KNOWN).**
The proposed peak count is the existing circuit count \(m\):
Lemma 3.21b already writes a CycleMin word as
\(O^{a_1}E\cdots O^{a_e}E\) with \(a_1\ge 2\). Grouping consecutive
evens gives \(p=\#\{\text{nonempty odd runs}\}=m\). This is not the
CycleMax landing of
[juggler_cycle_peak_descent.md](juggler_cycle_peak_descent.md).

**Target A (REPARAMETERIZATION).**
Every CycleMin word satisfies \(p\le\min(e,o-1)\) and therefore
\(p<(1-\log 2/\log 3)L\approx 0.36907\,L\). The bound \(p\le e\) is
already in Paper A §4. The bound \(p\le o-1\) never binds on an
expanding itinerary of length \(\ge 4\). Theorem 4.7 packing achieves
\(p=e\), so no sharper \(c<0.36907\) exists at the itinerary level.

**B1 leftover table (COMPUTATIONALLY VERIFIED).**
At floor \(N_0=10^6\), existing joint-minima and height packing
kill \(m=1\) and \(m=2\) on every length in
\(\mathcal E_{\mathrm{run}}\) (99 lengths). Live \(m=1\) and
\(m=2\) lists are empty. Thus \(p\ge 3\) on leftover lengths is a
corollary of Section 4, not a new cell theorem.

**B2 cells (COMPUTATIONALLY VERIFIED / REPARAMETERIZATION).**
The one-peak word is \(O^o E^e\). For \(e\le 3\) this is already
Theorems 3.4 / 3.12 / 3.14. On the grid \(4\le e\le 12\) the
O7-style +1-chain fires on all 36 expanding pairs; slack is
exactly \(3^o-2^L\). The denom-cell \(n^{3^o}>2^{e_o}(n+1)^{2^{o+e}}\)
leaks at \(O^{12}E^7\) (\(L=19\), the leftover one-peak shape) and
at leftover-scale \((o,e)\). Spotlight leftovers:

\[
L=25781:\quad\text{denom leaks},\quad +1\text{-chain }N_0=12492,
\]
\[
L=55293:\quad\text{denom leaks},\quad +1\text{-chain }N_0=401.
\]

The +1-chain comparison is the CycleMin slack identity
\(n^{A}>(n+1)^{A-(3^o-2^L)}\), already named for \(e=4\) as
`slack_of_four_even`.

**Uniform no-\(p=1\) by cells (REFUTED).**
There is no floor-free cell exclusion of every \(O^o E^e\) that is
independent of height finance and of CycleMin slack.

No cycle of any length — not claimed.

## Current literature

- Canonical run form, \(a_1\ge 2\) —
  **EXACT — HUMAN PROOF** (Lemma 3.21b)
- Even-count \(e\ge 4\) —
  **EXACT — LEAN VERIFIED** (Theorem 3.22)
- \(O^a EE\), \(O^a EEE\) —
  **EXACT — LEAN VERIFIED** (Theorems 3.12, 3.14)
- \(O^7\mathrm{EEEE}\) +1-chain —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_oooooooeeee`)
- Odd-run starts \(\le e\) —
  **EXACT — HUMAN PROOF** (Paper A §4)
- Run-type packing achieves \(p=e\) —
  **EXACT — HUMAN PROOF** (Theorem 4.7)
- Joint-minima / height \(m\)-packing —
  **EXACT — HUMAN PROOF** /
  **EXACT — LEAN VERIFIED** at \(L=84\), \(m\le 2\)
  ([juggler_cycle_m_finance.md](juggler_cycle_m_finance.md),
  [juggler_cycle_position_finance.md](juggler_cycle_position_finance.md))
- CycleMin slack \(3^o-2^{o+4}\) —
  **EXACT — LEAN VERIFIED** (`slack_of_four_even`)
- Canonical peak descent \(OE^r\) —
  **REPARAMETERIZATION**
  ([juggler_cycle_peak_descent.md](juggler_cycle_peak_descent.md))
- Return-cost / descent leftover-killers —
  **CLOSE** / **REFUTED**
- Collatz \(m\)-cycles —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new structural axis;
\(p\equiv m\) and the \(p=1\) kill is existing Section 4.

## Branch budget

```text
Mathematical target     Is every CycleMin one-peak word
                        w = O^o E^e (e≥4, 2^{o+e}<3^o)
                        impossible for a reason that is not
                        already height/joint-minima finance?
Novelty hypothesis      a floor-free p≥2, orthogonal to e≥4,
                        by trailing-evens + odd-run cells or
                        exact return after one climb
Falsifier               leftover-scale (o,e) leak the cell and
                        +1-chain (slack = 3^o-2^L), and every
                        leftover L already has m=1 dead by
                        existing height packing
Existing machinery      Lemma 3.21b run form; Thm 3.22 e≥4;
                        trailing-evens (Lemma 3.9);
                        O^a EE / O^a EEE (Thm 3.12, 3.14);
                        no_cycle_itinerary_oooooooeeee;
                        CycleMin slack 3^o-2^{o+4};
                        m-finance / height packing;
                        adversarial_valley_count
Maximum Phase-0 scope   dossier + probe: identify p≡m;
                        tabulate m=1,2 on E_run;
                        test O^o E^e cell/+1-chain on a
                        bounded (o,e) grid. No Lean, no
                        Paper A, no peak-finance, no p=2,3
                        census, no height/depth statistics
Promotion criterion     uniform no-p=1 by cells, or a p≥2
                        that is not a height-finance corollary
Stop criterion          Target A only (REPARAMETERIZATION);
                        p=1 exclusion restates height finance;
                        leftover (o,e) leak and no other
                        elementary obstruction
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Peak count \(p=\#\{\text{nonempty odd runs}\}\) —
  **KNOWN**; equals circuit count \(m\)
- \(p\le\min(e,o-1)<0.36907\,L\) —
  **REPARAMETERIZATION** of Lemma 3.21b and Theorem 3.2
- Sharper \(p\le cL-C\) with \(c<0.36907\) —
  **REFUTED** at the itinerary level by Theorem 4.7
- Height / joint-minima kill of leftover \(m=1,2\) —
  **COMPUTATIONALLY VERIFIED**; Section 4 corollary
- Denom-cell on leftover \(O^o E^e\) —
  **REFUTED** (leaks; \(L=19\) and \(L=25781,55293\))
- +1-chain on \(O^o E^e\) —
  **REPARAMETERIZATION** of CycleMin slack \(3^o-2^L\)
- Uniform no-\(p=1\) by cells —
  **REFUTED** (`juggler_cycle_peak_count`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_peak_count`
- Records: [juggler_cycle_peak_count.md](../research/juggler_cycle_peak_count.md),
  [juggler_cycle_peak_count.json](../research/juggler_cycle_peak_count.json)
- Dataset: `data/research/juggler/cycle_finance/peak_count/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_peak_count.py`
- B1: 99 run-type leftovers at \(n=10^6+1\)
- B2: grid \(4\le e\le 12\), \(o\) from \(o_{\min}\) through three extra
  odds (36 pairs); spotlights \(L=25781,55293\)
- Fast suite does not rerun the leftover table. No CLI. No Lean.

## Conjectures

`juggler_cycle_peak_count` — **REFUTED**.

## Counterexamples

- \(O^{12}E^7\) (\(L=19\)): denom-cell leaks through \(N_0=10^{12}\);
  +1-chain fires at \(55\), which is CycleMin slack \(7153=3^{12}-2^{19}\).
  Length 19 as a 1-cycle was already excluded by joint-minima at
  floor 53.
- \(O^{16266}E^{9515}\) (\(L=25781\)): denom-cell leaks; +1-chain
  \(N_0=12492\) is \(n\ln n\gtrsim 3/\theta\). Height packing already
  kills \(m=1\) at \(n=10^6+1\).
- Theorem 4.7 packing uses \(o-e\) copies of `OOE` and \(2e-o\)
  copies of `OE`, so \(p=e\) is achieved. No sharper combinatorial
  \(c<0.36907\).

## Formalization

None. No `CyclePeakCount.lean`. Paper A is unchanged.
Do not formalize the table. Do not reopen `cycle_peak_finance`.

## Results

- **\(p\equiv m\)** — **KNOWN**.
- **Target A** — **REPARAMETERIZATION**. On \(\mathcal E_{\mathrm{run}}\),
  \(p_{\max}=e\) and \(o-1\) never binds.
- **B1** — **COMPUTATIONALLY VERIFIED**. Height and joint-minima
  kill \(m=1\) and \(m=2\) on all 99 leftovers at floor \(10^6\).
  Artifact `peak_count/summary.json`.
- **B2 denom-cell** — leaks at leftover \((o,e)\) and at
  \(O^{12}E^7\). On the small grid it fires except that one pair.
- **B2 +1-chain** — fires on the grid and at leftover spotlights,
  with slack \(3^o-2^L\). This is CycleMin slack, not a new
  obstruction. \(O^7\mathrm{EEEE}\) recovers
  \(\mathrm{LEFT}=6177\), \(\mathrm{RIGHT}=6038\), slack \(139\).
- **No leftover dies** that height finance had left alive: every
  leftover already had \(m=1\) dead.

## Open questions

None from peak count as a new axis. A two-peak cell return
(\(p=2\)) that is not height finance is not opened here.

## Decision

**CLOSE**. Peak count is the existing circuit count \(m\). The
combinatorial upper bound is packaging of Lemma 3.21b, expansion,
and Theorem 4.7. One-peak words \(O^o E^e\) for \(e\ge 4\) are
already excluded on leftover lengths by joint-minima / height
packing (\(m=1,2\) die on all 99 run-type leftovers). The
trailing-evens denom-cell leaks at leftover scale. The +1-chain
is the CycleMin slack identity \(3^o-2^L\). No Paper A edit, no
ledger theorem row, no Lean.

Best next question: none from peak count. Do not open \(p=2\)
automatically. The Section 5 program stays **PARK**.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge: \(p\) is \(m\),
not a new Section 3 theorem. Not a second manuscript and not a
Paper A edit.
