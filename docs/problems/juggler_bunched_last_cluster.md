# Juggler bunched last-cluster leftover tails

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-8 or length-9
census, not first-E transport at \(e\ge 4\), and not induction on
\(n\) or on the period.

## Problem

After the two-even families and gapped first-E transport, do the
seven bunched last-cluster leftovers \(O^a\) plus a fixed short
tail fire as prefix-cell tails for every expanding \(a\), with
\(N_0\) bounded independently of \(a\)?

## Exact statement

A leftover three-even `CycleMin` is even-terminating
\(O^aEO^bEO^cE\) with \(a\ge 2\) and \(c\in\{0,1\}\). First-E
transport already excludes the gapped cases \(b\ge 4\) (EE) and
\(b\ge 3\) (EOE). The bunched remainder is seven families

\[
O^a\texttt{EEE},\ 
O^a\texttt{EOEE},\ 
O^a\texttt{EOOEE},\ 
O^a\texttt{EOOOEE},\ 
O^a\texttt{EEOE},\ 
O^a\texttt{EOEOE},\ 
O^a\texttt{EOOEOE}.
\]

The prefix-cell tail is

\[
n^{3^a}>2^{e_a}Z(n,b,c)^{2^a},
\]

where \(e_a=\log_2(\mathrm{lowerDenom}(O^a))\) and \(Z\) is the
last-even / last-odd bound on \(T_{O^a}(n)\) through the fixed
tail. Phase 0 asked whether each family first fires at some
\(N_0(a)\), whether \(N_0(a)\) stays bounded, and whether there is
no `CycleItinerary` on \(2\le n<N_0(a)\).

All seven families are now Lean-excluded as `CycleItinerary`s. A
uniform coarse \((n+1)^K\) cell for the last four families is
**REFUTED**; those four use a tight last-odd cell. This is not a
halt theorem. There is no `no_cycle_itinerary_length_eight` and no
`no_cycle_itinerary_length_nine`. There is no
`no_cycle_itinerary_bunched`.

## Current literature

- Uniform two-even leftover families —
  **EXACT — LEAN VERIFIED**.
- Gapped three-even `CycleMin`s —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_gapped_three_even_ee`,
  `no_cycleMin_gapped_three_even_eoe`).
- Leftover `OOOOOOEEE` —
  **EXACT — LEAN VERIFIED**. Computational \(N_0=73\); Lean
  algebraic cutoff \(n\ge 128\). This is the \(a=6\) instance
  of the `EEE` family.
- Uniform bunched `O^a`EEE —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eee`).
- Uniform bunched `O^a`EOEE —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eoee`).
- Uniform bunched `O^a`EOOEE —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eooee`).
  The \(K=4\) cell is the shared two-even tail at \(n\ge 256\).
- Uniform bunched `O^a`EOOOEE —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eoooee`).
  For \(a\ge 4\) the \(K=4\) cell; at \(a=3\) a tight last-odd
  split.
- Uniform bunched `O^a`EEOE —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eeoe`).
  Reuses the `EOEE` cell \(z<(n+1)^6\).
- Uniform bunched `O^a`EOEOE —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eoeoe`).
  Reuses the `EOOEE` cell \(z<(n+1)^4\).
- Uniform bunched `O^a`EOOEOE —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eooeoe`).
  For \(a\ge 4\) the \(K=4\) cell; at \(a=3\) the same tight
  split as `EOOOEE`.
- Uniform coarse \((n+1)^K\) cell for the last four
  bunched families —
  **REFUTED**. At the first expanding \(a\), \(K\cdot 2^a\ge 3^a\)
  for `EOOOEE`, `EEOE`, `EOEOE`, and `EOOEOE`.
- Length-9 three-even leftovers —
  **COMPUTATIONALLY VERIFIED** as prefix-cell tails. Those nine
  words are the first expanding instance of each bunched family
  plus the two gapped \(a=2\) words.
- Prefix-OOO extra scale from \(n=3\) —
  **REFUTED**. That `CLOSE` is not reopened.

Project relationship: **extended**. This is the bunched remainder
after even-count steps (i) and (ii).

## Branch budget

```text
Mathematical target     Do the seven bunched last-cluster tails
                        fire for every large a, with N0 bounded in a?
Novelty hypothesis      Fixed mixed tail plus C_{O^a}; cutoffs drop
                        as a grows, as they did for two evens
Falsifier               A tail whose N0 grows with a, or never fires
Existing machinery      trailing-even / last-odd cells; denomBits;
                        OOOOOOEEE; first-E for the gapped complement
Maximum Phase-0 scope   N0(a) for the seven families; empty tables
                        below N0. No Lean, no length-8/9 census,
                        no e≥4 transport, no halt
Promotion criterion     All seven fire with N0 bounded and an
                        algebraic reason (n≤4 never; plateau at 5)
Stop criterion          A family that never fires; unbounded N0;
                        a census; e≥4 machinery
```

Phase 1: Lean-exclude all seven bunched families as `CycleItinerary`s.
No length-8/9 census, no halt, no `no_cycle_itinerary_bunched`.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- seven bunched tails, independent of length —
  **EXACT — HUMAN PROOF**
- first expanding \(a\) is \(6,5,4,3,5,4,3\) —
  **EXACT — HUMAN PROOF**
- prefix-cell tails fire at first-expanding
  \(N_0\in\{73,89,120,188,60,81,126\}\) —
  **COMPUTATIONALLY VERIFIED**
- \(N_0\) drops to 5 and stays there through \(a=20\) —
  **COMPUTATIONALLY VERIFIED**
- the shared comparison never holds for \(n\le 4\) —
  **COMPUTATIONALLY VERIFIED**
- `EEE` coarse cell \(n^{3^a}>2^{e_a}(n+1)^{2^{a+3}}\) cubes
  from \(a=6\) at \(n\ge 73\) —
  **COMPUTATIONALLY VERIFIED**; Lean uses the same cell at the
  algebraic cutoff \(n\ge 128\)
- `O^a`EEE is not a `CycleItinerary` for \(a\ge 6\), \(n\ge 2\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eee`)
- `EOEE` coarse cell \(n^{3^a}>2^{e_a}(n+1)^{6\cdot 2^a}\) cubes
  from \(a=5\) at \(n\ge 314\); \(z<(n+1)^6\) for \(n\ge 4\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eoee`)
- `EOOEE` coarse cell \(n^{3^a}>2^{e_a}(n+1)^{4\cdot 2^a}\) is
  the shared two-even tail; \(z<(n+1)^4\) for \(n\ge 32\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eooee`)
- `EOOOEE` for \(a\ge 4\) reuses that \(K=4\) cell; at \(a=3\)
  a tight last-odd split —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eoooee`)
- `EEOE` reuses the `EOEE` cell \(z<(n+1)^6\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eeoe`)
- `EOEOE` reuses the `EOOEE` cell \(z<(n+1)^4\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eoeoe`)
- `EOOEOE` for \(a\ge 4\) reuses the \(K=4\) cell; at \(a=3\)
  the same tight split as `EOOOEE` —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_three_even_eooeoe`)
- a uniform coarse \((n+1)^K\) cell for the last four
  families — **REFUTED**
- no bunched family is a `CycleItinerary` on \(2\le n<N_0(a)\)
  for expanding \(a\le 20\) —
  **COMPUTATIONALLY VERIFIED**
- every three-even cycle itinerary is impossible — not claimed
- no cycle of length eight or nine — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.bunched_last_cluster`
- Records: [juggler_bunched_last_cluster.md](../research/juggler_bunched_last_cluster.md),
  [juggler_bunched_last_cluster.json](../research/juggler_bunched_last_cluster.json)
- Tests: `tests/research/juggler_sequence/test_bunched_last_cluster.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length-8 or length-9 census.
- Lean lives in `BunchedEEE.lean`, `BunchedEOEE.lean`,
  `BunchedEOOEE.lean`, `BunchedEEOE.lean`,
  `BunchedEOEOE.lean`, `BunchedEOOOEE.lean`,
  `BunchedEOOEOE.lean`, and the shared tight-cell file
  `BunchedTight.lean`. Paper A records Theorems 3.14--3.20.

## Conjectures

None opened.

## Counterexamples

None to the seven tails or to the empty tables. The stronger
claims that remain false or unproved:

- “\(N_0\) tends to 2” — still **REFUTED**. The leading \(3^a\)
  coefficients force \(n>4\).
- “prefix-OOO extra scale from \(n=3\)” — still **REFUTED**.
- “first-E transport at \(e\ge 4\) reduces bunched last clusters”
  — not claimed. A bunched last cluster is exactly the remainder
  that last-cluster two-even transport does not take.
- “a uniform coarse \((n+1)^K\) cell excludes all four remaining
  bunched families” — **REFUTED**. The first-expanding exponent
  \(K\cdot 2^a\) meets or beats \(3^a\) on `EOOOEE`, `EEOE`,
  `EOEOE`, and `EOOEOE`.
- “every bunched leftover is one Lean theorem
  `no_cycle_itinerary_bunched`” — not claimed. The seven families
  are seven theorems.
- “every three-even leftover is Lean-excluded” — not claimed
  beyond the seven bunched families and the two gapped
  `CycleItinerary` families of Theorem 3.21.
- no cycle of length eight or nine — not claimed.

## Formalization

`formal/Problems/Juggler/BunchedEEE.lean` excludes the `EEE`
family: `no_cycle_itinerary_three_even_eee`.
`formal/Problems/Juggler/BunchedEOEE.lean` excludes the `EOEE`
family: `no_cycle_itinerary_three_even_eoee`.
`formal/Problems/Juggler/BunchedEOOEE.lean` excludes the `EOOEE`
family: `no_cycle_itinerary_three_even_eooee`.
`formal/Problems/Juggler/BunchedEEOE.lean` excludes the `EEOE`
family: `no_cycle_itinerary_three_even_eeoe`.
`formal/Problems/Juggler/BunchedEOEOE.lean` excludes the `EOEOE`
family: `no_cycle_itinerary_three_even_eoeoe`.
`formal/Problems/Juggler/BunchedEOOOEE.lean` excludes the
`EOOOEE` family: `no_cycle_itinerary_three_even_eoooee`.
`formal/Problems/Juggler/BunchedEOOEOE.lean` excludes the
`EOOEOE` family: `no_cycle_itinerary_three_even_eooeoe`.
There is no `no_cycle_itinerary_bunched` and no
`no_cycleMin_bunched`. `SmallCycleCensus.lean` still assembles
only through length seven. No `no_cycle_itinerary_length_eight`. No
`no_cycle_itinerary_length_nine`. No `sorry`. No halt theorem.
Paper A records Theorems 3.14--3.20.

## Results

Classification **BUNCHED_LAST_CLUSTER_GREEN**.

The seven bunched last-cluster leftovers are one type: a fixed
short tail against \(C_{O^a}\). All seven fire at the first
expanding \(a\), with largest cutoff \(N_0=188\) on
`OOOEOOOEE`. Lean now excludes every bunched family as a
`CycleItinerary`: `O^a`EEE for \(a\ge 6\), `O^a`EOEE and `O^a`EEOE
for \(a\ge 5\), `O^a`EOOEE and `O^a`EOEOE for \(a\ge 4\), and
`O^a`EOOOEE and `O^a`EOOEOE for \(a\ge 3\). A uniform coarse
\((n+1)^K\) cell for the last four families is **REFUTED**.
Tables below each cutoff are empty through \(a=20\).

This is a seven-family Lean exclusion, not a length-8 or
length-9 census and not a no-cycles theorem.

## Open questions

Gapped `CycleItinerary` exclusion is now Paper A Theorem 3.21.
First-E at \(e=4\) is `CLOSE` as a reparameterization
([first-E at four evens](juggler_first_e_e4.md)). The
thirty-shape remainder is `PARK`
([four-even short-first-gap](juggler_four_even_short_gap.md)).
Do not assemble `no_cycle_itinerary_length_eight` or
`no_cycle_itinerary_length_nine`. Do not claim halt.

## Decision

**PROMOTE**. All seven bunched last-cluster families are Lean
`CycleItinerary` exclusions. A uniform coarse \(K\) for the last four
stays **REFUTED**; those four use a tight last-odd cell. Not a
length-8/9 census and not a halt theorem.

Best next question: first-E transport at \(e\ge 4\), or stop.

## Publication assessment

Status: `EXPLORATORY`.

A seven-family Lean exclusion inside the bunched remainder,
recorded in Paper A as Theorems 3.14--3.20, not a length-9
census and not a Juggler totality result.
