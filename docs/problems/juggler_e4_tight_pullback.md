# Juggler tighter last-cluster pullback at length 11

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-8, length-9, or
length-11 census, not a thirty-family Lean list, and not induction on
\(n\) or on the period.

## Problem

\(Z_4\) leaks at the thirty first-expanding four-even short-gap
words, all of length \(11\). Does a tighter last-cluster pullback
make those itineraries fire?

## Exact statement

The thirty words are \(O^{a_0}EO^{a_1}EO^{a_2}EO^{a_3}E\) at the
first expanding \(a_0\), so seven odds and length \(11\). One of
them is \(O^7\mathrm{EEEE}\). After the leading odd run the
state \(z\) is followed by four even letters. The Lean last-cluster
cell is `cycle_trailing_evens_lt` at \(r=4\):

\[
z<(n+1)^{16}.
\]

That bound is already the even-tower cell; there is no further
pullback. The idealisation \(Z=n^{16}\) (drop the \(+1\)) is the
strongest last-cluster comparison of this type:

\[
n^{3^7}>2^{e_7}n^{16\cdot 2^7}
\qquad\Longleftrightarrow\qquad
n^{139}>2^{4118},
\]

since \(e_7=\log_2(\mathrm{lowerDenom}(O^7))=4118\). Phase 0 asks
whether this fires at a practical \(N_0\) (below the seven-odd
cut \(256\), or at least in a table window), and whether any of
the other twenty-nine words fire in \(n\le 800\) under \(Z_4\).

This is not a `CycleItinerary` theorem. It is not a length-8, length-9,
or length-11 census and not a halt theorem. There is no
`no_cycle_itinerary_length_eight`, no `no_cycle_itinerary_length_eleven`,
and no `no_cycle_itinerary_oooooooeeee`.

## Current literature

- `cycle_trailing_evens_lt` for every \(r\ge 1\) —
  **EXACT — LEAN VERIFIED**. \(r=3\) is the `EEE` cell; \(r=4\)
  is the `EEEE` cell.
- Seven bunched last-cluster families —
  **EXACT — LEAN VERIFIED**. They fire at the first expanding
  \(a\) with \(N_0\le 188\).
- Four-even short-first-gap \(Z_4\) —
  **OBSERVATION** / **PARK**
  ([juggler_four_even_short_gap](juggler_four_even_short_gap.md)).
  Fires at \(a_0+1\) with \(N_0\le 180\); leaks at length \(11\).
- A uniform coarse \((n+1)^K\) for the last four three-even
  families — **REFUTED**. Not reopened.

Project relationship: **extended**, then **refuted**.

## Branch budget

```text
Mathematical target     Does a tighter last-cluster cell fire
                        at all 30 length-11 leftovers?
Novelty hypothesis      Slack in the Z4 pullback, not in the
                        last-cluster bound itself
Falsifier               O^7 EEEE is already the sharp r=4
                        trailing-evens cell and still leaks
Existing machinery      cycle_trailing_evens_lt; denom bits;
                        the 30-word list
Maximum Phase-0 scope   Ideal EEEE cell plus window miss;
                        no Lean, no tables, no Paper A
Promotion criterion     A tighter cell fires all 30 at N0
                        in a practical window
Stop criterion          EEEE is already sharp and N0 is huge;
                        a length-11 census
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(O^7\mathrm{EEEE}\) is the first-expanding EEEE leftover —
  **EXACT — HUMAN PROOF**
- the last-cluster bound is \(z<(n+1)^{16}\)
  (`cycle_trailing_evens_lt`, \(r=4\)) —
  **EXACT — LEAN VERIFIED**
- the ideal cell \(Z=n^{16}\) is \(n^{139}>2^{4118}\) —
  **EXACT — HUMAN PROOF**
- that inequality first holds at \(n=828\,484\,394\) and fails
  at \(n=256\) and at \(n=10^8\) —
  **COMPUTATIONALLY VERIFIED**
- the Lean cell \(Z=(n+1)^{16}\) is weaker and still fails at
  that same \(N_0\) —
  **COMPUTATIONALLY VERIFIED**
- all thirty length-11 words miss \(n\le 256\) and \(n\le 800\)
  under \(Z_4\) —
  **COMPUTATIONALLY VERIFIED**
- a tighter last-cluster pullback fires at all thirty —
  **REFUTED**
- no cycle of length eleven — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.e4_tight_pullback`
- Records: [juggler_e4_tight_pullback.md](../research/juggler_e4_tight_pullback.md),
  [juggler_e4_tight_pullback.json](../research/juggler_e4_tight_pullback.json)
- Tests: `tests/research/juggler_sequence/test_e4_tight_pullback.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length-8, length-9, or length-11
  census. No four-even Lean. No Paper A theorem.

## Conjectures

None opened.

## Counterexamples

\(O^7\mathrm{EEEE}\) at every \(2\le n\le 10^8\): the strongest
last-cluster comparison of this type fails. The first integer
where \(n^{139}>2^{4118}\) is \(n=828\,484\,394\).

The stronger claims that remain false or unproved:

- “\(Z_4\) is loose on `EEEE` because of the pullback” — false;
  there is no pullback, only four trailing evens.
- “seven odds plus the tail seal `EEEE` below \(256\) and above
  some small \(N_0\)” — the tail only from \(8\cdot 10^8\).
- “no cycle of length eleven” — not claimed.

## Formalization

None new. `cycle_trailing_evens_lt` already covers \(r=4\).
`SmallCycleCensus.lean` still assembles only through length
seven. No `no_cycle_itinerary_length_eight`. No
`no_cycle_itinerary_length_eleven`. No `no_cycle_itinerary_oooooooeeee`.
No `sorry`. No halt theorem. Paper A is unchanged.

## Results

Classification **E4_TIGHT_PULLBACK_REFUTED**.

The last-cluster cell on \(O^7\mathrm{EEEE}\) is already sharp.
Tightening the \(Z_4\) pullback cannot help that itinerary: the tail
is four evens, and `cycle_trailing_evens_lt` at \(r=4\) is the
bound. The ideal form \(n^{139}>2^{4118}\) first fires at
\(828\,484\,394\). All thirty length-11 words still miss
\(n\le 800\).

Seven consecutive odds cover `EEEE` only for \(n<256\). That
leaves \(256\le n<828\,484\,394\) untouched by last-cluster
methods.

## Open questions

Rotation and internal-E next-square are `CLOSE`
([length-11 non-pullback](juggler_length11_nonpullback.md)).
Stop on the thirty length-11 leftovers as a leftover-path
target. Do not assemble `no_cycle_itinerary_length_eight`,
`no_cycle_itinerary_length_nine`, or `no_cycle_itinerary_length_eleven`.
Do not claim halt. Do not start a thirty-family Lean list from
this `CLOSE`.

## Decision

**CLOSE**. A tighter last-cluster pullback cannot fire at all
thirty length-11 words, because \(O^7\mathrm{EEEE}\) already
uses the sharp even-tower cell and still needs
\(n>2^{4118/139}\). That kills the method. It is not a
length-11 census and not a halt theorem.

Best next question: stop. Rotation and internal-E are
`CLOSE` on these thirty words.

## Publication assessment

Status: `ARCHIVED`.

A negative method gate: the length-11 leak is not slack in
\(Z_4\). Not a paper theorem and not a Juggler totality result.
