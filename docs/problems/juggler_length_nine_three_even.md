# Juggler length-9 three-even leftovers

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It does not reopen Paper B densities,
does not start induction on \(n\) or on the period, and is not a
length-9 census.

## Problem

What argument excludes the even-terminating expanding length-9 words
that have three even letters and survive the Paper A filters — the
words that the two leftover families \(O^{k-2}EE\) and \(O^{k-3}EOE\)
no longer cover?

## Exact statement

A length-9 word is formally expanding if and only if it has at least
six odd letters (\(2^9=512<729=3^6\)). Every mixed cycle itinerary rotates
to an even-terminating orientation. Every even-terminating three-even
word is uniquely

\[
O^aEO^bEO^cE,\qquad a+b+c=6.
\]

The suffix after the last internal even letter is always \(O^c\). It
never contains \(E\). Last-internal bootstrap therefore still applies
exactly when \(c\ge 2\). The leftover orientations are the nine words
with \(a\ge 2\) and \(c\in\{0,1\}\):

\[
\begin{align*}
&OOOOOOEEE,\ OOOOOEOEE,\ OOOOOEEOE,\\
&OOOOEOOEE,\ OOOOEOEOE,\\
&OOOEOOOEE,\ OOOEOOEOE,\\
&OOEOOOOEE,\ OOEOOOEOE.
\end{align*}
\]

Phase 0 asks whether each of these satisfies an odd-prefix cell tail

\[
n^{3^a}>C_{O^a}\,Z^{2^a}
\]

for all \(n\ge N_0\), where \(Z\) is a last-even / last-odd upper bound
on \(T_{O^a}(n)\) through the mixed tail \(EO^bEO^cE\), and whether
there is no `CycleItinerary` realization on \(2\le n<N_0\).

This is not a Lean census and not a halt theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Small-cycle census (Paper A Theorem 3.6) —
  **EXACT — LEAN VERIFIED**. No cycle itinerary of length at most six.
- Internal-E bootstrap —
  **EXACT — LEAN VERIFIED**. Last-internal next-square suffix.
- Leftover length-six orientations (Lemma 3.5) —
  **EXACT — LEAN VERIFIED**. Finite table plus
  \(n^{81}>2^{130}(n+1)^{64}\).
- Length-7 leftover inventory and census —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_oooooee`,
  `no_cycle_itinerary_ooooeoe`, `no_cycle_itinerary_length_le_seven`).
  Length eight is open. Not reopened.
- Trailing-even cell (`cycle_trailing_evens_lt`) —
  **EXACT — LEAN VERIFIED**. If a cycle itinerary ends with
  \(r\ge 1\) evens then \(T_v(n)<(n+1)^{2^r}\).
- Leftover `OOOOOOEEE` —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_ooooooeee`).
  Finite table below \(128\) plus
  \(n^{729}>2^{1330}(n+1)^{512}\). Not a length-9 census.
- Prefix-OOO extra scale from \(n=3\) —
  **REFUTED**. That `CLOSE` is not reopened.

Project relationship: **extended**. The first length at which an
expanding even-terminating word can have three evens.

## Branch budget

```text
Mathematical target     What argument excludes the length-9 three-even
                        leftover CycleItineraries?
Novelty hypothesis      Last-internal suffix is always O^c; leftovers
                        are nine words O^a E O^b E O^c E; odd-prefix
                        plus mixed-tail cells replace the two-even
                        families
Falsifier               A leftover whose prefix-cell tail never fires,
                        or a CycleItinerary realization below N0
Existing machinery      expansion; rotation; odd-run; OO/OOO/odd-run
                        thresholds; CycleMin; internal-E bootstrap;
                        Lemma 3.5 last-even / last-odd cells;
                        lowerDenom
Maximum Phase-0 scope   inventory + prefix-cell N0 + finite table on
                        the nine leftovers. No Lean, no Paper A edit,
                        no length 10, no four-even, no halt, no cycle
                        search, no CLI
Promotion criterion     A named argument that computationally excludes
                        all nine leftovers, not a rewrite of induction
Stop criterion          A leftover whose tail never fires; a table hit;
                        machinery gravity (census engine, length 10,
                        Paper A). Phase 0 did not add Lean.
```

Phase-1 budget (one leftover, not a census):

```text
Mathematical target     Does the trailing-even cell plus the O^6
                        envelope exclude CycleItinerary on OOOOOOEEE
                        for every n ≥ 2?
Novelty hypothesis      Three trailing evens are one cell
                        z < (n+1)^8, not two last-even cells
Falsifier               A CycleItinerary realization, or the algebraic
                        tail n^729 > 2^1330 (n+1)^512 failing
Existing machinery      cycle_last_even_interval; leftover 6/7
                        tables; lowerDenom(O^6)=2^1330
Maximum Phase-1 scope   cycle_trailing_evens_lt and
                        no_cycle_itinerary_ooooooeee. No remaining
                        eight leftovers, no length-9 census,
                        no Paper A, no length 8/10, no halt
Promotion criterion     Lean theorem no_cycle_itinerary_ooooooeee
Stop criterion          remaining eight leftovers; census;
                        length 8; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- even-terminating expanding length-9 family has 37 words (1 odd-run,
  8 two-even, 28 three-even) —
  **COMPUTATIONALLY VERIFIED**
- last-internal suffix of a three-even even-terminating word is always
  \(O^c\) —
  **COMPUTATIONALLY VERIFIED**
- six three-even words with \(c\ge 2\) and \(a\ge 2\) are last-internal
  bootstrap shapes; \(n=3,5\) fail by parity —
  **COMPUTATIONALLY VERIFIED**
- leftovers are exactly the nine words above —
  **COMPUTATIONALLY VERIFIED**
- for \(a=2\) the remainder after the first \(E\) is a Lemma 3.5 word
  (`OOOOEE` / `OOOEOE`) —
  **COMPUTATIONALLY VERIFIED**
- odd-prefix cell tails fire at
  \(N_0\in\{60,73,81,89,120,126,188,250,374\}\),
  with `OOOOOOEEE` at \(N_0=73\) after the three-even
  cell \(z<(n+1)^8\) —
  **COMPUTATIONALLY VERIFIED**
- the two-even cell \(z<(n+1)^4\) on `OOOOOOEEE` is
  a spurious cutoff \(N_0=8\) —
  **REFUTED**
- no leftover is a `CycleItinerary` on \(2\le n<N_0\) —
  **COMPUTATIONALLY VERIFIED**
- `OOOOOOEEE` is not a `CycleItinerary` at any \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- `OOOEOOOEE` is realized at \(n=183\) but returns \(1664\), not \(183\) —
  **COMPUTATIONALLY VERIFIED**
- every length-9 cycle itinerary is impossible — not claimed
- cycles of length ten or more are impossible — not claimed
- global halt — not claimed
- induction on \(n\) or on the period excludes cycles — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_length_nine`
- Records: [juggler_cycle_length_nine.md](../research/juggler_cycle_length_nine.md),
  [juggler_cycle_length_nine.json](../research/juggler_cycle_length_nine.json)
- Tests: `tests/research/juggler_sequence/test_cycle_length_nine.py`,
  `tests/research/juggler_sequence/test_cycle_leftover_itineraries.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length 10. No four-even programme.
- Phase 1 Lean: `cycle_trailing_evens_lt` in
  `formal/Problems/Juggler/Cycles.lean` and
  `no_cycle_itinerary_ooooooeee` in
  `formal/Problems/Juggler/LeftoverCycles.lean`.
  No `no_cycle_itinerary_length_nine`. Paper A records the trailing-even
  cell as Lemma 3.9 and \(OOOOOOEEE\) as the \(a=6\) case of
  Theorem 3.14.

## Conjectures

None opened.

## Counterexamples

None to the inventory or to the nine leftover tails. The stronger
claims that remain false or unproved:

- “the last two \(E\)s can be separated by a suffix containing \(E\)” —
  false for an even-terminating word; the last-internal suffix is
  \(O^c\).
- “induction on the period reduces length 9 to length 8” — still
  false. A period-9 cycle does not produce a period-\(\le 8\) cycle.
  The case \(T_{O^aE}(n)=n\) is divisor reduction (\(a+1\mid 9\)), not
  an inductive step on \(k\).
- “a general no-cycle induction on \(n\)” — still the census of
  odd-to-odd cycle minima.
- “every length-9 word is Lean-excluded” — not claimed.
- “`OOOOOOEEE` is a two-even tail \(z<(n+1)^4\)” —
  **REFUTED**. The prefix image sits before three square
  roots, so \(z<(n+1)^8\). The old cell produced a
  spurious \(N_0=8\).

## Formalization

`cycle_trailing_evens_lt` in `Cycles.lean`: if a cycle itinerary ends
with \(r\ge 1\) even letters then the state before that run is
strictly less than \((n+1)^{2^r}\). The case \(r=3\) is the
three-even cell for `OOOOOOEEE`.

`no_cycle_itinerary_ooooooeee` in `LeftoverCycles.lean`: finite
evaluation on `Fin 128` plus
\(n^{729}>2^{1330}(n+1)^{512}\) for \(n\ge 128\). The
computational prefix-cell first fires at \(N_0=73\); \(128\) is
the algebraic cutoff.

`SmallCycleCensus.lean` still assembles only through length
seven and records that length eight is open. No
`no_cycle_itinerary_length_nine`. The remaining eight leftovers are
not Lean-excluded. No `sorry`. No halt theorem. No
`CycleSearch`. FloorPower, Progress, and Minimal are not
rewritten. Paper A records Lemma 3.9 and Theorem 3.14. This is
not a Lean census.

## Results

Classification **THREE_EVEN_PREFIX_CELL_GREEN**, with secondary
**FIRST_E_TRANSPORT_FOR_A2** and
**LAST_INTERNAL_SUFFIX_ALWAYS_O_RUN**.

The 28 three-even words split as: 7 start \(E\), 6 start \(OE\), 6
last-internal bootstrap, 9 leftovers. The last-internal suffix never
contains \(E\), so “bootstrap does not fire because the suffix is
`OE…`” is a first-\(E\) remark, not a last-internal one.

The argument that covers the nine leftovers is the Lemma 3.5 method
with the extra even kept in the cell chain, not in `lowerDenom`.
Naive `cycle_pow_le_lowerDenom` on the full word inflates the
constant through the internal \(E\)s (\(N_0\) in the thousands). The
refined comparison uses \(C_{O^a}\) only and bounds \(T_{O^a}(n)\)
by last-even / last-odd cells through \(EO^bEO^cE\). The unique
leftover with three trailing evens (`OOOOOOEEE`, \(b=c=0\)) uses
the cell \(z<(n+1)^8\), not the two-even cell \(z<(n+1)^4\). All
nine tails fire, with `OOOOOOEEE` at \(N_0=73\) and largest cutoff
\(N_0=374\) on `OOEOOOOEE`; the exact tables below the cutoffs have
zero returns. Lean excludes `OOOOOOEEE` only.

For the two \(a=2\) leftovers the remainder after the first \(E\) is
exactly a length-6 leftover. On a cycle minimum that remainder starts
at \(y\ge n\), so Lemma 3.5 transports at \(256\). The prefix-cell
bound already excludes those two words as `CycleItinerary`, so the
transport is a CycleMin simplification, not a second method.

This is a computational exclusion of the nine leftover `CycleItinerary`s
and a Lean exclusion of one leftover, not a Lean census and not a
no-cycles theorem.

## Open questions

Lean-exclude the remaining eight three-even leftovers by the
prefix-cell tails. Do not open length 8, length 10, or four-even
words automatically. A uniform two-even theorem for lengths 6–8
remains a later distill. Do not start an O-terminating
`CycleItinerary` programme. Do not claim halt. Do not assemble
`no_cycle_itinerary_length_nine`.

## Decision

**PROMOTE**. Phase 0 named the three-even leftover list and fired
all nine prefix-cell tails. Phase 1 repaired the three-trailing-even
cell (\(z<(n+1)^8\), computational \(N_0=73\)) and Lean-excluded
`OOOOOOEEE`. That is one leftover, not a length-9 census and not
induction on \(n\) or on the period.

Best next question: Lean-exclude the remaining eight leftovers,
starting with the next EE leftover `OOOOOEOEE`.

## Publication assessment

Status: `EXPLORATORY`.

A Phase-0 inventory plus a Phase-1 Lean exclusion of one leftover,
not a paper candidate, not a length-9 census, and not a Juggler
totality result. Paper A records the trailing-even cell and the
\(O^aEEE\) family, not a length-9 census.
