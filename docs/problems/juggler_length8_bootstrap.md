# Juggler length-8 two-even bootstrap

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-8 census and not
a leftover-cell family.

## Problem

The even-terminating expanding length-8 words that Theorem 3.12 does
not cover look like new leftovers. Two of them are squares:
\(\mathrm{OOOOEOOE}=\mathrm{OO}(\mathrm{OOE})^2\) and
\(\mathrm{OOOEOOOE}=(\mathrm{OOOE})^2\). Are they a new last-cluster
family, or the next instances of the existing OO/OOO bootstrap?

## Exact statement

A length-8 word is formally expanding if and only if it has at least
six odd letters (\(2^8=256<729=3^6\)). The even-terminating expanding
words are exactly eight spellings. After Theorem 3.12, odd-run, and
CycleMin filters, the remaining CycleMin-legal two-even words are

\[
\mathrm{OOOOEOOE}=O^4EO^2E,\qquad
\mathrm{OOOEOOOE}=O^3EO^3E,\qquad
\mathrm{OOEOOOOE}=O^2EO^4E.
\]

The suffix \(v\) strictly between the internal \(E\) and the last
\(E\) is \(\mathrm{OO}\), \(\mathrm{OOO}\), or \(\mathrm{OOOO}\).
Each already satisfies \(3^{\#O(v)}\ge 2^{\mathrm{len}(v)+1}\), so
`no_cycleMin_internal_even_threshold` applies with
`oo_suffix_threshold` (\(N=5\)), `ooo_suffix_threshold` (\(N=3\)),
or `odd_run_suffix_threshold` (\(N=3\)).

The same words as transients are not excluded by repeated-block
scale: \(69\xrightarrow{(\mathrm{OOE})^2}212\) and
\(225\xrightarrow{(\mathrm{OOOE})^2}4990602\).

This CLOSE is not a leftover cell and not itself a census. A later
laboratory branch assembled `no_cycle_itinerary_length_le_eight` from
these named filters; that packaging is
[juggler_length_eight_cycles.md](juggler_length_eight_cycles.md).
There is still no `no_cycle_itinerary_length_eight` (the Paper A name
was not used) and no halt theorem.

## Current literature

- Uniform two-even leftover families —
  **EXACT — LEAN VERIFIED** (Paper A Theorem 3.12).
- Internal-E next-square —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_internal_even_threshold`).
  Instantiated at `OOEOOE`, `OOOEOOE`, `OOEOOOE`.
- Repeated \(O^aE^b\) blocks —
  **EXACT — LEAN VERIFIED** scale plus **OBSERVATION** that
  expanding repetition survives as a transient.
- Length-11 non-pullback —
  **REFUTED**. That `CLOSE` is not reopened: there the suffixes
  were sub-next-square. Here they are next-square.

Project relationship: **extended**. The square reading is the
bootstrap split, not a new cell.

## Branch budget

```text
Mathematical target     Are OOOOEOOE and OOOEOOOE new leftovers,
                        or OO/OOO bootstrap?
Novelty hypothesis      The square reading is a new leftover last
                        cluster
Falsifier               The suffix between the internal E and the
                        last E is already next-square
Existing machinery      no_cycleMin_internal_even_threshold;
                        oo/ooo thresholds; Theorem 3.12; odd-run;
                        repeated-block transients
Maximum Phase-0 scope   Name the eight-word inventory; no Lean,
                        no census, no Paper A
Promotion criterion     A new leftover cell that is not bootstrap
Stop criterion          The suffixes are already next-square; or
                        assembling no_cycle_itinerary_length_eight
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- eight even-terminating expanding length-8 words, all named —
  **COMPUTATIONALLY VERIFIED**
- \(\mathrm{OOOOEOOE}=\mathrm{OO}(\mathrm{OOE})^2\) and
  \(\mathrm{OOOEOOOE}=(\mathrm{OOOE})^2\) —
  **EXACT — HUMAN PROOF**
- suffixes \(\mathrm{OO}\), \(\mathrm{OOO}\), \(\mathrm{OOOO}\) are
  next-square —
  **EXACT — HUMAN PROOF**
- repeated-block transients \(69\) and \(225\) follow and do not
  return —
  **OBSERVATION**
- a new leftover last cluster — **REFUTED**
- no cycle of length eight — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.length8_bootstrap`
- Records: [juggler_length8_bootstrap.md](../research/juggler_length8_bootstrap.md),
  [juggler_length8_bootstrap.json](../research/juggler_length8_bootstrap.json)
- Tests: `tests/research/juggler_sequence/test_length8_bootstrap.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length-8 census. No leftover cell.

## Conjectures

None opened.

## Counterexamples

None to the inventory or to the next-square suffixes. The stronger
claims that fail:

- “\(\mathrm{OOOOEOOE}\) and \(\mathrm{OOOEOOOE}\) are leftovers” —
  the suffix after the internal \(E\) is already next-square.
- “the square reading is a new cycle obstruction” — it is the
  bootstrap split \(uEvE\); \((\mathrm{OOE})^2\) is already
  `no_cycle_itinerary_ooeooe`.
- “repeated expansion contradicts a cycle” — the recorded
  transients expand and do not return.

## Formalization

None in this CLOSE. `no_cycleMin_internal_even_threshold` already
existed. `SmallCycleCensus.lean` still assembles only through
length seven and records that length eight is open in that Paper A
assembly. The later laboratory file `LengthEightCensus.lean`
packages the named filters. No `sorry`. No halt theorem. Paper A
is unchanged.

## Results

Classification **LENGTH8_BOOTSTRAP_REPARAMETERIZATION**.

There is no new length-8 leftover. The two squares are the next
\(\mathrm{OO}/\mathrm{OOO}\) bootstrap instances. The third
two-even CycleMin spelling is \(O^2EO^4E\), already an odd-run
suffix threshold. Named filters cover every even-terminating
expanding length-8 word. That is not a census theorem.

## Open questions

Answered by the laboratory census
[juggler_length_eight_cycles.md](juggler_length_eight_cycles.md):
`no_cycle_itinerary_length_le_eight`. Do not claim halt. Do not reopen
the thirty length-11 leftovers.

## Decision

**CLOSE**. The square reading is the existing internal-E
bootstrap, not a leftover cell. Repeated-block scale still does
not exclude the same words as transients. It is not a length-8
census and not a halt theorem.

Best next question: answered by the length-8 census; stop this
leftover-novelty branch.

## Publication assessment

Status: `ARCHIVED`.

A negative leftover-inventory result: the suspected new families
are bootstrap. Not a paper theorem and not a Juggler totality
result.
