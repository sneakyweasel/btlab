# Juggler length-11 non-pullback leftover attacks

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-8, length-9, or
length-11 census, not last-cluster pullback, and not a thirty-family
Lean list.

## Problem

Last-cluster methods leak at the thirty first-expanding four-even
short-gap words, all of length \(11\). \(Z_4\) is `PARK`. A tighter
last-cluster cell is `CLOSE`: \(O^7\mathrm{EEEE}\) is already sharp.
Do the leftover-path methods that are *not* last-cluster pullback
exclude any of those thirty words?

## Exact statement

The thirty words are the first-expanding leftovers
\(O^{a_0}EO^{a_1}EO^{a_2}EO^{a_3}E\) with seven odds, last cluster
bunched, and \(a_1\) below the bunched family's \(a_{\min}\). Each
already starts \(\mathrm{OO}\) and ends \(E\), so each is a
`CycleMin`-legal spelling.

Phase 0 tests the two leftover-path attacks that are not last-cluster
pullback:

1. **Rotation** (the Theorem 3.21 playbook). A `CycleItinerary` has a
   `CycleMin` rotation. That upgrades an excluded `CycleMin` class to
   a `CycleItinerary` theorem only when *every* `CycleMin`-legal orientation
   is already excluded. The thirty words are the orientations that are
   still open as `CycleMin`s.
2. **Internal-E next-square**
   (`no_cycleMin_internal_even_threshold`). A `CycleMin` of the form
   \(uEvE\) dies if \(T_v(m)\ge(m+1)^2\) for all large \(m\) that
   follow \(v\). That is the formal comparison
   \(3^{\#O(v)}\ge 2^{\mathrm{len}(v)+1}\). Here \(v\) is the suffix
   strictly between an internal \(E\) and the last \(E\).

This is not a `CycleItinerary` theorem. It is not a length-8, length-9, or
length-11 census and not a halt theorem. There is no
`no_cycle_itinerary_length_eight`, no `no_cycle_itinerary_length_eleven`, and
no `no_cycle_itinerary_oooooooeeee`.

## Current literature

- Uniform two-even leftover families —
  **EXACT — LEAN VERIFIED** (Paper A Theorem 3.12).
- Gapped three-even leftovers —
  **EXACT — LEAN VERIFIED** (Theorems 3.13 and 3.21). Theorem 3.21
  is rotation of an already-excluded `CycleMin` class.
- Seven bunched last-cluster families —
  **EXACT — LEAN VERIFIED** (Theorems 3.14--3.20).
- Internal-E next-square bootstrap —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_internal_even_threshold`;
  `OO`/`OOO` suffixes).
- First-E at \(e=4\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_first_e_e4](juggler_first_e_e4.md)).
- Four-even short-first-gap \(Z_4\) —
  **OBSERVATION** / **PARK**
  ([juggler_four_even_short_gap](juggler_four_even_short_gap.md)).
- Tighter last-cluster pullback —
  **REFUTED** / **CLOSE**
  ([juggler_e4_tight_pullback](juggler_e4_tight_pullback.md)).
- Prefix-OOO extra scale from \(n=3\) —
  **REFUTED**. That `CLOSE` is not reopened.

Project relationship: **extended**, then **refuted**.

## Branch budget

```text
Mathematical target     Do rotation or internal-E next-square
                        exclude any of the 30 length-11 leftovers?
Novelty hypothesis      A mixed itinerary dies by orientation or by
                        a next-square suffix after an internal E
Falsifier               Every word is already a surviving
                        CycleMin spelling; every internal-E
                        suffix has exponent < 2
Existing machinery      exists_cycleMin; internal-E threshold;
                        the 30-word list
Maximum Phase-0 scope   Classify rotations and exponents;
                        no Lean, no census, no Paper A
Promotion criterion     At least one cyclic word is excluded
                        as CycleItinerary or CycleMin by one of
                        these two methods
Stop criterion          Both methods are inapplicable or
                        exponent-obstructed; or a census
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- each of the thirty words is `CycleMin`-legal and is its own
  surviving short-gap orientation —
  **EXACT — HUMAN PROOF**
- the thirty words are thirty distinct necklaces —
  **COMPUTATIONALLY VERIFIED**
- rotation upgrades `CycleMin` to `CycleItinerary` only after the
  `CycleMin` class is already excluded —
  **EXACT — HUMAN PROOF** (Theorem 3.21 playbook)
- every suffix between an internal \(E\) and the last \(E\)
  satisfies \(3^{\#O}<2^{\mathrm{len}+1}\) —
  **EXACT — HUMAN PROOF** on the thirty words (closest margin
  \(243/256\) on \(v=\mathrm{OOOOOEE}\))
- that closest suffix undershoots \((m+1)^2\) at
  \(m=1\,000\,215\) —
  **COMPUTATIONALLY VERIFIED**
- rotation or internal-E excludes one of the thirty —
  **REFUTED**
- no cycle of length eleven — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.length11_nonpullback`
- Records: [juggler_length11_nonpullback.md](../research/juggler_length11_nonpullback.md),
  [juggler_length11_nonpullback.json](../research/juggler_length11_nonpullback.json)
- Tests: `tests/research/juggler_sequence/test_length11_nonpullback.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length-8, length-9, or length-11
  census. No four-even Lean. No Paper A theorem.

## Conjectures

None opened.

## Counterexamples

Each of the thirty words is already a surviving `CycleMin`
spelling, so `exists_cycleMin` has nothing to upgrade.

The strongest internal-E suffix is \(v=\mathrm{OOOOOEE}\) on
`OOEOOOOOEEE`: \(3^5=243<256=2^8\). At \(m=1\,000\,215\) one has
\(T_v(m)=245\,924\,753\,167<(m+1)^2=1\,000\,432\,046\,656\).
`OOOOOOOEEEE` has suffixes \(\mathrm{EE}\), \(\mathrm{E}\), and
empty; all are farther from next-square.

The stronger claims that remain false or unproved:

- “a mixed length-11 leftover rotates onto an excluded class,
  so the necklace dies” — false; the original spelling survives.
- “an internal \(E\) bootstraps a next-square suffix on some
  of the thirty” — false; seven odds leave at most five odds
  after the first \(E\), and two further evens keep the exponent
  below \(2\).
- “no cycle of length eleven” — not claimed.

## Formalization

None new. `exists_cycleMin` and
`no_cycleMin_internal_even_threshold` already exist.
`SmallCycleCensus.lean` still assembles only through length
seven. No `no_cycle_itinerary_length_eight`. No
`no_cycle_itinerary_length_eleven`. No `no_cycle_itinerary_oooooooeeee`.
No `sorry`. No halt theorem. Paper A is unchanged.

## Results

Classification **LENGTH11_NONPULLBACK_REFUTED**.

Rotation is the 3.21 upgrade, not a method for leftovers that
are still open as `CycleMin`s. Internal-E next-square is
exponent-obstructed on every split of every one of the thirty
words. The closest miss is \(243/256\). `OOOOOOOEEEE` is not a
special case of this obstruction: the mixed itineraries fail too.

Together with the \(Z_4\) `PARK` and the EEEE tight-pullback
`CLOSE`, the leftover-cell / rotation / internal-E toolkit does
not hit the thirty length-11 words.

## Open questions

Stop on the thirty length-11 leftovers as a leftover-path
target. Do not assemble `no_cycle_itinerary_length_eight`,
`no_cycle_itinerary_length_nine`, or `no_cycle_itinerary_length_eleven`.
Do not claim halt. Do not start a thirty-family Lean list from
this `CLOSE`. Length 8 remains open as a census; that is a
different branch.

## Decision

**CLOSE**. Rotation cannot exclude an open `CycleMin` leftover.
Internal-E next-square needs exponent at least \(2\) and every
internal-E suffix on the thirty words is strictly below that.
The methods that are not last-cluster pullback fail for a
reason that is not slack in \(Z_4\). It is not a length-11
census and not a halt theorem.

Best next question: stop. The leftover toolkit is exhausted at
these thirty words.

## Publication assessment

Status: `ARCHIVED`.

A negative method gate: the unused leftover-path attacks are
inapplicable or exponent-obstructed. Not a paper theorem and
not a Juggler totality result.
