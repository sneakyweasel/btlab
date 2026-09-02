# Juggler four-even short-first-gap prefix-cell

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-8, length-9, or
length-11 census, not a thirty-family Lean list, and not induction on
\(n\) or on the period.

## Problem

The first-E \(e=4\) remainder is thirty four-even leftovers with
bunched last cluster and short first remainder gap. Do they fire as
**one** prefix-cell, or is that a thirty-family tail list?

## Exact statement

The leftover is \(O^{a_0}EO^{a_1}EO^{a_2}EO^{a_3}E\) with
\(a_0\ge 2\), \(a_3\in\{0,1\}\), last cluster bunched, and
\(a_1\) below that family's \(a_{\min}\). There are thirty such
shapes. Write \(Z_3(n,a_2,a_3)\) for the existing three-even
last-cluster bound, and

\[
Z_4(n,a_1,a_2,a_3)
=
\begin{cases}
(Z_3+1)^2-1 & a_1=0,\\
(y_{\max}+1)^2-1 & a_1\ge 1,
\end{cases}
\]

where \(y_{\max}\) is the odd-run pullback of \(Z_3\) through
\(O^{a_1}\). The prefix-cell is

\[
n^{3^{a_0}}>2^{e_{a_0}}Z_4^{2^{a_0}}.
\]

Phase 0 asks whether this cell fires at the first expanding
\(a_0\), and whether \(N_0\) stays bounded one and two odds later.

This is not a `CycleItinerary` theorem. It is not a length-8, length-9,
or length-11 census and not a halt theorem. There is no
`no_cycle_itinerary_length_eight`, no `no_cycle_itinerary_length_nine`,
no `no_cycle_itinerary_length_eleven`, and no
`no_cycle_itinerary_four_even`.

## Current literature

- Uniform two-even leftover families —
  **EXACT — LEAN VERIFIED** (Paper A Theorem 3.12).
- Gapped three-even leftovers —
  **EXACT — LEAN VERIFIED** (Theorems 3.13 and 3.21).
- Seven bunched last-cluster families —
  **EXACT — LEAN VERIFIED** (Theorems 3.14--3.20). Those fire
  at the first expanding \(a\) with \(N_0\le 188\).
- First-E at four evens —
  **REPARAMETERIZATION** / **CLOSE**
  ([juggler_first_e_e4](juggler_first_e_e4.md)). Named this
  thirty-shape remainder.
- A uniform coarse \((n+1)^K\) cell for the last four three-even
  families — **REFUTED**. Not reopened here as a uniform \(K\).

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Do the 30 four-even short-first-gap
                        leftovers fire as one prefix-cell?
Novelty hypothesis      Z4 = three-even Z pulled back through
                        E O^{a1} is one family, not 30 tails
Falsifier               The cell misses the first expanding
                        a0, or N0 is unbounded after it
Existing machinery      three-even Z; denom bits; 30-shape list
Maximum Phase-0 scope   Log-cell N0 for 30 shapes; no Lean,
                        no tables, no Paper A
Promotion criterion     The cell fires at first expanding a0
                        with bounded N0, as one schema
Stop criterion          First expanding layer leaks; a
                        thirty-family Lean list; a census
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- the thirty shapes are \(O^{a_0}\) plus a fixed four-even tail
  with bunched last cluster and \(a_1<a_{\min}\) —
  **EXACT — HUMAN PROOF**
- first expanding four-even leftover has seven odds, length
  \(11\) —
  **EXACT — HUMAN PROOF**
- \(Z_4\) is the three-even last-cluster bound pulled back
  through \(E O^{a_1}\) —
  **EXACT — HUMAN PROOF**
- at the first expanding \(a_0\), \(Z_4\) misses \(n\le 800\)
  on every shape; the log cutoff is \(4\cdot 10^8\) to
  \(1.6\cdot 10^{15}\) —
  **COMPUTATIONALLY VERIFIED**
- at \(a_0+1\), every shape fires with \(N_0\le 180\); at
  \(a_0+2\), with \(N_0\le 22\) —
  **COMPUTATIONALLY VERIFIED**
- every four-even leftover dies — not claimed
- no cycle of length eight, nine, or eleven — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.four_even_short_gap`
- Records: [juggler_four_even_short_gap.md](../research/juggler_four_even_short_gap.md),
  [juggler_four_even_short_gap.json](../research/juggler_four_even_short_gap.json)
- Tests: `tests/research/juggler_sequence/test_four_even_short_gap.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length-8, length-9, or length-11
  census. No four-even Lean. No Paper A theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that \(Z_4\) fires at the first expanding
\(a_0\) with a practical cutoff is **REFUTED**. The thirty
length-11 words, for example \(O^7\mathrm{EEEE}\) and
\(O^2EO^5\mathrm{EEE}\), have log-cutoffs from \(4\cdot 10^8\)
to \(1.6\cdot 10^{15}\).

The stronger claims that remain false or unproved:

- “the thirty shapes need thirty different cells” — false;
  \(Z_4\) is one pullback.
- “\(Z_4\) is a Lean exclusion” — not claimed.
- “no cycle of length eleven” — not claimed.
- every four-even leftover dies — not claimed.

## Formalization

None. Existing first-E, gapped CycleItinerary, and bunched modules
are not rewritten. `SmallCycleCensus.lean` still assembles only
through length seven. No `no_cycle_itinerary_length_eight`. No
`no_cycle_itinerary_length_nine`. No `no_cycle_itinerary_length_eleven`.
No `no_cycle_itinerary_four_even`. No `sorry`. No halt theorem.
Paper A is unchanged.

## Results

Classification **FOUR_EVEN_SHORT_GAP_PARK**.

The thirty short-first-gap shapes are one prefix-cell: the
three-even \(Z\) pulled back through \(E O^{a_1}\). That cell
fires uniformly one odd past first expanding (\(N_0\le 180\))
and two odds past it (\(N_0\le 22\)). At the first expanding
length it does not: those are thirty itineraries of length \(11\),
and the cutoff is \(10^8\) to \(10^{15}\).

Three-even bunched families fired at the first expanding \(a\)
with \(N_0\le 188\). The extra even in \(Z_4\) spends that
margin. Writing thirty Lean files for the infinite tails while
length \(11\) leaks is machinery gravity.

## Open questions

A tighter last-cluster pullback is `CLOSE`
([e4 tight pullback](juggler_e4_tight_pullback.md)):
\(O^7\mathrm{EEEE}\) already uses the sharp \(r=4\) cell.
Rotation and internal-E next-square are `CLOSE`
([length-11 non-pullback](juggler_length11_nonpullback.md)).
Stop on the thirty length-11 leftovers as a leftover-path
target. Do not assemble `no_cycle_itinerary_length_eight`,
`no_cycle_itinerary_length_nine`, or `no_cycle_itinerary_length_eleven`.
Do not claim halt.

## Decision

**PARK**. \(Z_4\) is a unifying cell and kills the infinite
families after one extra odd, but it fails at the first
expanding layer — the thirty length-11 words that the
even-count programme is supposed to hit first. A thirty-file
Lean list of the later tails is the wrong next step.

Best next question: stop. The tighter last-cluster cell is
`CLOSE`, and so are rotation and internal-E.

## Publication assessment

Status: `EXPLORATORY`.

A method gate: one four-even prefix-cell exists and fires after
the first expanding length, and leaks at length \(11\). Not a
paper theorem and not a Juggler totality result.
