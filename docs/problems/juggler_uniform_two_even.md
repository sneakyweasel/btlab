# Juggler uniform two-even leftover tails

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-8 census, not a
three-even programme, and not induction on \(n\) or on the period.

## Problem

Do both two-even leftover families \(O^{k-2}EE\) and \(O^{k-3}EOE\)
have leftover tails that fire for every expanding length \(k\ge 6\),
with a cutoff \(N_0\) bounded independently of \(k\)?

## Exact statement

Both families are formally expanding for every \(k\ge 6\)
(\(3^{k-2}>2^k\)). Write \(e_a=\log_2(\mathrm{lowerDenom}(O^a))\).
The last-even cell on \(O^{k-2}EE\) and the last-odd cube trick on
\(O^{k-3}EOE\) reduce to the same comparison

\[
n^{3^{k-2}}>2^{e_{k-2}}(n+1)^{2^k}.
\]

The EOE auxiliary \((y+1)^3<2(n+1)^4\) for every \(y\) with
\(y^3<(n+1)^4\) is independent of \(k\). Phase 0 asks whether this
shared tail first fires at some \(N_0(k)\), whether \(N_0(k)\) stays
bounded, and whether there is no `CycleItinerary` realization on
\(2\le n<N_0(k)\).

The two leftover families are now Lean-excluded for every
\(k\ge 6\). This is not a length-8 census and not a halt theorem.
There is no `no_cycle_itinerary_length_eight`.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Leftover length-six orientations (Lemma 3.5) —
  **EXACT — LEAN VERIFIED**. Finite table plus
  \(n^{81}>2^{130}(n+1)^{64}\) for \(n\ge 256\). First fire is
  \(N_0=205\); \(256\) is the algebraic cutoff.
- Length-7 leftover inventory and census —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_oooooee`,
  `no_cycle_itinerary_ooooeoe`, `no_cycle_itinerary_length_le_seven`).
  Shared tail \(n^{243}>2^{422}(n+1)^{128}\) first fires at
  \(N_0=14\). Length eight is open. Not reopened as a census.
- Trailing-even cell (`cycle_trailing_evens_lt`) —
  **EXACT — LEAN VERIFIED**. The EE case is \(r=2\).
- Prefix-OOO extra scale from \(n=3\) —
  **REFUTED**. That `CLOSE` is not reopened.

Project relationship: **extended**. The two leftover families are
one type, parameterized by \(k\), not a new shape at each length.

## Branch budget

```text
Mathematical target     Do both two-even leftover tails fire for
                        every k≥6 with N0 bounded independently of k?
Novelty hypothesis      Cutoffs get easier as k grows; N0 drops to 5
                        and stays there; EOE adds no extra cutoff
Falsifier               A k whose tail never fires, or N0(k)→∞
Existing machinery      Lemma 3.5/3.7 cells; lowerDenom(O^a);
                        cycle_trailing_evens_lt; y-succ cube lemma
Maximum Phase-0 scope   N0(k) for k=6..24; empty tables below N0.
                        No Lean, no length-8 census, no three-even,
                        no halt, no Paper A edit
Promotion criterion     Both tails fire with N0 bounded and an
                        algebraic reason (n≤4 never; plateau at 5)
Stop criterion          A k that never fires; unbounded N0; a
                        length-8 census; three-even leftovers
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(e_a=2\cdot 3^a-2^{a+1}=\log_2(\mathrm{lowerDenom}(O^a))\) —
  **EXACT — LEAN VERIFIED** (`denomBits`, `lowerDenom_replicate_odd`)
- both families expanding for every \(k\ge 6\) —
  **EXACT — HUMAN PROOF**
- the shared tail never holds for \(n\le 4\) —
  **EXACT — HUMAN PROOF**
- EOE auxiliary \((y+1)^3<2(n+1)^4\) holds for every \(n\ge 2\) —
  **EXACT — LEAN VERIFIED** (`cube_succ_lt_two_mul_of_cube_lt_pow4`)
- first-fire cutoffs
  \(N_0(6)=205\), \(N_0(7)=14\), \(N_0(8)=8\), \(N_0(9)=6\),
  \(N_0(10)=6\), and \(N_0(k)=5\) for \(11\le k\le 24\) —
  **COMPUTATIONALLY VERIFIED**
- neither leftover family is a `CycleItinerary` at any \(n\ge 2\)
  and any \(k\ge 6\) —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_two_even_ee`,
  `no_cycle_itinerary_two_even_eoe`)
- every two-even cycle itinerary is Lean-excluded — not claimed
- no cycle of length eight — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.uniform_two_even`
- Records: [juggler_uniform_two_even.md](../research/juggler_uniform_two_even.md),
  [juggler_uniform_two_even.json](../research/juggler_uniform_two_even.json)
- Tests: `tests/research/juggler_sequence/test_uniform_two_even.py`,
  `tests/research/juggler_sequence/test_cycle_leftover_itineraries.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length-8 census. No three-even programme.
- Lean: `formal/Problems/Juggler/LeftoverTwoEven.lean`, imported by
  `Problems.Juggler` only. Paper A records the families as
  Theorem 3.12. No `no_cycle_itinerary_length_eight`.

## Conjectures

None opened.

## Counterexamples

None to the shared tail or to the empty tables. The stronger claims
that remain false or unproved:

- “induction on the period reduces length \(k\) to length \(k-1\)” —
  still false.
- “a general no-cycle induction on \(n\)” — still the census of
  odd-to-odd cycle minima.
- “every two-even word is Lean-excluded” — still not claimed;
  only the two leftover families are.
- “\(N_0\) tends to 2” — **REFUTED**. The leading \(3^{k-2}\)
  coefficients force \(n>4\).

## Formalization

`formal/Problems/Juggler/LeftoverTwoEven.lean` proves
`no_cycle_itinerary_two_even_ee` and `no_cycle_itinerary_two_even_eoe` for
every \(k\ge 6\) and \(n\ge 2\). Large \(n\) is the shared tail at
the uniform cutoff \(n\ge 256\), inducting from the length-6
comparison by cubing. Below \(256\) the longest odd run on
\(n\ge 2\) has length 6, so only \(k=8\) (EE) and \(k=8,9\) (EOE)
need `Fin 256` tables; longer words require seven consecutive
odds. `SmallCycleCensus.lean` still assembles only through length
seven and records that length eight is open. No
`no_cycle_itinerary_length_eight`. No `sorry`. No halt theorem. Paper A
is not edited. Ledger: `J-two-even-leftover-ee`,
`J-two-even-leftover-eoe`.

## Results

Classification **TWO_EVEN_UNIFORM_TAIL_GREEN**.

Both leftover families are Lean-excluded for every \(k\ge 6\) and
every \(n\ge 2\). The shared tail \(n^{3^{k-2}}>2^{e_{k-2}}(n+1)^{2^k}\)
is the large-\(n\) engine; \(e_a=2(3^a-2^a)\) is now
`lowerDenom(O^a)` in Lean. Computational first-fire remains
\(205,14,8,6,6\) then \(N_0=5\) for \(k\ge 11\). This is not a
length-8 census and not a no-cycles theorem.

## Open questions

First-E transport is now a separate branch
([juggler_first_e_transport.md](juggler_first_e_transport.md)).
Do not assemble `no_cycle_itinerary_length_eight` automatically. Do not
claim halt.

## Decision

**PROMOTE**. Both two-even leftover families are Lean-excluded for
every \(k\ge 6\). The method is one type, not a period-by-period
can. A length-8 census is not automatic.

Best next question: first-E transport of the uniform two-even tail
for three-even leftovers with second gap \(a_1\ge 2\), or
bunched-tail cells.

## Publication assessment

Status: `EXPLORATORY`.

A uniform Lean exclusion of the two leftover families, not a paper
candidate and not a Juggler totality result. Paper A records
Theorem 3.12 without assembling a length-8 census.
