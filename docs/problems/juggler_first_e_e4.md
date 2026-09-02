# Juggler first-E transport at four evens

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-8 or length-9
census, not a four-even bunched-tail programme, and not induction on
\(n\) or on the period.

## Problem

Once every three-even leftover is excluded, do leftover `CycleMin`s
with four even letters die by first-E transport of an already-excluded
three-even family?

## Exact statement

After bootstrap an even-terminating leftover on a `CycleMin` is
\(O^{a_0}EO^{a_1}EO^{a_2}EO^{a_3}E\) with \(a_0\ge 2\) and
\(a_3\in\{0,1\}\). First-E at \(e=3\) transported a two-even remainder
across the first \(E\). At \(e=4\) the remainder after the first \(E\)
has three evens. Phase 0 asks whether expanding four-even leftovers
fall into an already-excluded class, or whether a new remainder
survives.

The partition is:

- **gapped last-cluster:** \(a_2\ge 4\) (EE) or \(a_2\ge 3\) (EOE).
  The suffix after the penultimate \(E\) is a two-even leftover, and
  `CycleMin` puts that state at \(\ge n\). This is Theorem 3.13, not
  first-E of the four-even word.
- **bunched remainder:** last cluster bunched and \(a_1\) at least
  that family's expanding \(a_{\min}\). The leftover cell against
  \(n\) versus the bunched tail at \(y=T_{O^{a_0}E}(n)\) is Theorems
  3.14--3.20 after \(y\ge n\) tightens \(Z(n)\le Z(y)\).
- **short first-gap remainder:** last cluster bunched and
  \(a_1<a_{\min}\). Neither reduction hits.

This is not a `CycleItinerary` or `CycleMin` theorem at \(e=4\). It is
not a length-8 or length-9 census and not a halt theorem. There is
no `no_cycle_itinerary_length_eight` and no `no_cycle_itinerary_length_nine`.
There is no `no_cycle_itinerary_four_even` and no
`no_cycle_itinerary_bunched`.

## Current literature

- Uniform two-even leftover families —
  **EXACT — LEAN VERIFIED** (Paper A Theorem 3.12).
- Gapped three-even leftovers —
  **EXACT — LEAN VERIFIED** (Theorems 3.13 and 3.21).
- Seven bunched last-cluster families —
  **EXACT — LEAN VERIFIED** (Theorems 3.14--3.20).
- Prefix-OOO extra scale from \(n=3\) —
  **REFUTED**. That `CLOSE` is not reopened.
- First-E at \(e\ge 4\) as the next bunched attack —
  already recorded as a refuted idea. This branch asks the
  complementary question: whether a known three-even tail
  transports across the first \(E\) of a four-even leftover.

Project relationship: **extended**, then **reparameterization**.

## Branch budget

```text
Mathematical target     Do leftover CycleMins with e=4 even
                        letters die by first-E transport of
                        an excluded three-even family?
Novelty hypothesis      A new infinite e=4 layer, not e=3 again
Falsifier               Gapped last-cluster is Theorem 3.13;
                        long-a1 bunched remainder is 3.14-3.20
                        at y; a large class has short gaps
Existing machinery      two-even tail; first-E; bunched Z;
                        CycleMin y>=n
Maximum Phase-0 scope   Classify expanding e=4 leftovers;
                        no Lean, no census, no Paper A
Promotion criterion     A leftover class whose exclusion is
                        not a reparameterization of 3.12-3.21
Stop criterion          Every transportable class is KNOWN or
                        REPARAMETERIZATION; or a census/halt grab
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- four-even leftovers split as gapped last-cluster, bunched
  remainder, or short first-gap —
  **EXACT — HUMAN PROOF**
- gapped last-cluster is Theorem 3.13 on the last two-even
  suffix, not first-E of the four-even word —
  **REPARAMETERIZATION**
- long-\(a_1\) bunched remainder is the existing bunched tail
  at \(y\) after \(y\ge n\) tightens \(Z(n)\le Z(y)\) —
  **REPARAMETERIZATION**
- through odd-count \(16\), \(1185\) expanding leftovers:
  \(570\) gapped last-cluster, \(315\) bunched remainder,
  \(300\) short first-gap —
  **COMPUTATIONALLY VERIFIED**
- the short first-gap remainder is \(30\) shapes
  (seven last-clusters times \(a_1<a_{\min}\)), each expanding
  once \(a_0\) is large enough —
  **EXACT — HUMAN PROOF**
- every four-even leftover dies by first-E — **REFUTED**
- no cycle of length eight or nine — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.first_e_e4`
- Records: [juggler_first_e_e4.md](../research/juggler_first_e_e4.md),
  [juggler_first_e_e4.json](../research/juggler_first_e_e4.json)
- Tests: `tests/research/juggler_sequence/test_first_e_e4.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length-8 or length-9 census.
- No four-even bunched-tail list. No new Lean. No Paper A
  theorem.

## Conjectures

None opened.

## Counterexamples

None to the partition. The hypothesis that first-E at \(e=4\)
excludes four-even leftovers is **REFUTED** by the \(30\)
short-first-gap shapes, for example \(O^a\mathrm{EEEE}\)
(\(a\ge 7\)) and \(O^a\mathrm{EOEEE}\).

The stronger claims that remain false or unproved:

- “gapped last-cluster at \(e=4\) is a new theorem” — false;
  it is Theorem 3.13 on the last two-even suffix.
- “bunched remainder transport is a new tail” — false; it is
  Theorems 3.14--3.20 at \(y\).
- “every four-even leftover dies” — **REFUTED**.
- no cycle of length eight or nine — not claimed.

## Formalization

None. Existing first-E, gapped CycleItinerary, and bunched modules
are not rewritten. `SmallCycleCensus.lean` still assembles only
through length seven. No `no_cycle_itinerary_length_eight`. No
`no_cycle_itinerary_length_nine`. No `no_cycle_itinerary_four_even`. No
`no_cycle_itinerary_bunched`. No `sorry`. No halt theorem. Paper A
is unchanged.

## Results

Classification **FIRST_E_E4_REPARAMETERIZATION**.

On expanding four-even leftovers with odd-count \(7\) through
\(16\):

- \(570\) have a gapped last cluster (Theorem 3.13);
- \(315\) have a bunched three-even remainder with
  \(a_1\ge a_{\min}\) (Theorems 3.14--3.20 at \(y\));
- \(300\) have bunched last cluster and \(a_1<a_{\min}\).

The bunched-remainder slice is empty at the first expanding
odd-count \(o=7\) and appears at \(o=8\)
(\(O^2EO^6\mathrm{EEE}\)). \(Z(n,b,c)\) is monotone on
\(2\le n<80\) for every bunched tail, so \(y\ge n\) tightens
the leftover cell whenever the existing tail fires at \(y\).

The short-first-gap remainder is thirty infinite families, not
one leftover itinerary. Opening them is a four-even bunched-tail
programme. That is outside this scope.

## Open questions

The thirty-shape prefix-cell is `PARK`
([four-even short-first-gap](juggler_four_even_short_gap.md)).
A tighter last-cluster pullback is `CLOSE`
([e4 tight pullback](juggler_e4_tight_pullback.md)).
Rotation and internal-E next-square are `CLOSE`
([length-11 non-pullback](juggler_length11_nonpullback.md)).
Stop on the thirty length-11 leftovers as a leftover-path
target. Do not assemble `no_cycle_itinerary_length_eight` or
`no_cycle_itinerary_length_nine`. Do not claim halt.

## Decision

**CLOSE**. Every transportable class is a reparameterization of
Theorems 3.13--3.20. First-E at \(e=4\) does not exclude
four-even leftovers: thirty short-first-gap shapes remain, each
an infinite family in \(a_0\). That kills the method as a way
to finish even-count leftovers. It is not a length-8/9 census
and not a halt theorem.

Best next question: four-even leftovers with bunched last
cluster and short first remainder gap, or stop.

## Publication assessment

Status: `ARCHIVED`.

A negative method gate: first-E transport at four evens restates
the three-even theorems and leaves a thirty-family remainder.
Not a paper theorem and not a Juggler totality result.
