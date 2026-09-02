# Juggler cycle Christoffel maximizers

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map, on the
**cycle half** of the `cycles_or_escapes` split. It transfers the
only unused Collatz word technique that does not need the affine
equation: Fernández–Ibáñez Christoffel / mechanical words as unique
maximizers, **without** Lebel modular sieving. It is not a halt
theorem, not a leftover-itinerary census, not a floor raise, and not a
reopen of the closed almost-monochrome near-tight branch.

## Problem

Worst cycle finance is \(o=o_{\min}(L)\), the Beatty / Christoffel
approximation to \(\log 2/\log 3\). The leftover lengths
\(38,84,569,1054,\ldots\) are exactly those approximations. Does a
hypothetical cycle at such an \(L\) have to be combinatorially
close to the Christoffel word of slope \(o/L\), so that leftover-itinerary
cells apply to a one-parameter necklace instead of \(\binom{L}{o}\)
words?

## Exact statement

Write \(o=o_{\min}(L)=\min\{o:3^o>2^L\}\) and let \(c_L\) be the
ceiling Christoffel word of slope \(o/L\), written in letters
\(O,E\). Its CycleMin conjugates are the necklace of balanced
words of that slope (floor and ceiling Christoffel are conjugates).

**Beatty identification (KNOWN / already in cycle finance).**
The record leftover lengths track one-sided approximations of
\(\log 2/\log 3\): \(7/11=2/3\oplus 5/8\), \(12/19\) principal,
\(24/38=2\cdot(12/19)\), \(53/84\) principal,
\(359/569=53/84\oplus 306/485\), \(665/1054\) principal.

**Balance (KNOWN combinatorics on words).**
\(c_L\) is balanced, with \(\max O\)-run \(2\) and \(\max E\)-run
\(1\) for every tested leftover \(L\ge 3\). Local minima \(m\)
equal the even count. The itinerary at \(L=38\) is \(c_{19}^2\).

**One-parameter leftover-cell slogan (REFUTED).**
Leftover-word cells, or CycleMin-legal expanding itineraries of weight
\(o_{\min}\), concentrate on the Christoffel necklace, so those
cells apply to a one-parameter family instead of
\(\binom{L}{o}\) words.

Counterexamples:

- Length 11: the thirty first-expanding short-gap leftovers
  include \(c_{11}=\mathrm{OOEOOEOOEOE}\) and also
  \(\mathrm{OOOOOOOEEEE}\) at cyclic Hamming \(4\). Histogram
  \(0:1,\;2:16,\;4:13\). Family \(30\) versus necklace \(4\).
  CycleMin slack \(139=3^7-2^{11}\) is word-order-independent.
- Length 19: all \(12376\) CycleMin words of weight \(12\) have
  median cyclic Hamming \(6\) to \(c_{19}\); radius \(0\) is
  \(7\) (the necklace); radius \(\le 2\) is \(389\).
- Isolated-even words (max \(E\)-run \(1\), worst \(m\)-finance)
  number \(462\) at length 19, not \(7\). Finance itself depends
  only on \((L,o)\), not on letter order.

**Cycle-only near-Christoffel rigidity** — a hypothetical realized
cycle itinerary at leftover \(L\) must still be close to \(c_L\) — is
**not** refuted. There is no cycle in range. That is the same
open question as cycle-only near-tightness after open-orbit
approximate-equality rigidity and the almost-monochrome slogan
were **REFUTED**. This branch does not reopen those.

Lebel modular sieving does not come along. No leftover length
dies.

## Current literature

- Fernández–Ibáñez, Christoffel words as extremal Collatz
  structures — **known** as a preprint claim
  (`fernandez-ibanez-2026`). Their maximizer is the Terras /
  affine constant \(C\). Juggler has no affine equation; only
  the combinatorial half is tested here. Those Collatz
  statements are **not** adopted as theorems.
- Lebel, Christoffel modular sieving — **known** as a preprint
  (`lebel-2026`). **Not transferred.**
- Cycle finance leftover lengths are near-convergents of
  \(\ln 2/\ln 3\) —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_finance.md](juggler_cycle_finance.md)).
- Leftover-word cells at length 11 —
  **EXACT — LEAN VERIFIED** / **PARK** on the thirty short-gap
  shapes ([juggler_cyclemin_fudge.md](juggler_cyclemin_fudge.md)).
- Open-orbit approximate-equality rigidity —
  **REFUTED** (`J-approx-equality-rigidity`).
- Cycle near-tight monochrome leftover-killer —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_near_tight.md](juggler_cycle_near_tight.md)).
  That slogan is the opposite end of the necklace (almost
  monochrome, not almost Christoffel).
- Finite balanced words of a given slope are Christoffel
  conjugates — **KNOWN** combinatorics on words.

Project relationship: **refuted** as a one-parameter leftover-cell
reduction; the Beatty identification remains **known**.

## Branch budget

```text
Mathematical target     At leftover near-convergent L with o=o_min(L),
                        do leftover-itinerary / CycleMin-legal expanding
                        words concentrate on the Christoffel necklace
                        of slope o/L, so leftover-itinerary cells apply to
                        a one-parameter family instead of C(L,o) words?
Novelty hypothesis      Fernández–Ibáñez unique-maximizer combinatorics
                        transfers without the affine equation and
                        without Lebel modular sieving
Falsifier               leftover-itinerary survivors or CycleMin candidates
                        sit at large cyclic Hamming distance from the
                        Christoffel necklace, or the surviving family
                        is exponential rather than one-parameter
Existing machinery      o_min / finance leftovers, L=11 leftover-itinerary
                        cells, ceiling Christoffel formula, closed
                        almost-monochrome near-tight branch,
                        J-approx-equality-rigidity REFUTED
Maximum Phase-0 scope   define Juggler Christoffel words; Farey / CF
                        identification; Hamming census of the thirty
                        L=11 leftovers and all CycleMin weight-o_min
                        words at L=11,19; isolated-even worst-m
                        family; no Lean, no Lebel, no monochrome reopen
Promotion criterion     survivors concentrate on the Christoffel
                        necklace so cells apply to one family
Stop criterion          distance is large / family is wide; or the
                        statement is KNOWN Beatty plus leftover cells
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Ceiling Christoffel O/E word of slope \(o_{\min}/L\) —
  **KNOWN** (mechanical words)
- Leftover \(L\) are Beatty / Farey approximations of
  \(\log 2/\log 3\) —
  **KNOWN** (already in cycle finance)
- Floor and ceiling Christoffel are conjugates —
  **COMPUTATIONALLY VERIFIED** on the probe lengths
- \(c_{38}=c_{19}^2\) —
  **COMPUTATIONALLY VERIFIED**
- One-parameter leftover-cell reduction —
  **REFUTED** (`juggler_christoffel_one_parameter`)
- A realized cycle at leftover \(L\) is near \(c_L\) —
  not claimed; **OPEN**
- Lebel modular half — not transferred
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_christoffel`
- Records: [juggler_cycle_christoffel.md](../research/juggler_cycle_christoffel.md),
  [juggler_cycle_christoffel.json](../research/juggler_cycle_christoffel.json)
- Dataset: `data/research/juggler/cycle_christoffel/`
- Tests: `tests/research/juggler_sequence/test_cycle_christoffel.py`

Science window: leftover records \(38,84,569,1054\) plus the
killed near-convergents \(11,19\) for leftover-itinerary / CycleMin
censuses. No CLI. No new Lean. Paper A is unchanged.

## Conjectures

`juggler_christoffel_one_parameter` — **REFUTED**.

## Counterexamples

- Length-11 leftover family of \(30\) words, cyclic Hamming
  histogram \(0:1,\;2:16,\;4:13\), including
  \(\mathrm{OOOOOOOEEEE}\).
- Length-19 CycleMin weight-\(12\): \(12376\) words, median
  Hamming \(6\), radius \(0\) only \(7\).
- Isolated-even worst-\(m\) family at length 19: \(462\) words.

## Formalization

None. `CycleFinance.lean` and `NearTightScale.lean` are unchanged.
No `CycleChristoffel.lean`, no `MechanicalWord.lean`, no Lebel
walk, and no `sorry`. Paper A is unchanged. Not a halt theorem.

## Results

Classification **CYCLE_CHRISTOFFEL_CLOSED**. Regenerate with
`python -m research.juggler_sequence.cycle_christoffel`.

- Leftover lengths are the named Beatty / Farey approximations
  (**KNOWN**).
- Christoffel words at those lengths are balanced with
  \(\max O=2\), \(\max E=1\), \(m=\) even count
  (**COMPUTATIONALLY VERIFIED**).
- The one-parameter leftover-cell slogan is **REFUTED** on the
  candidate set: leftover-itinerary cells at length 11 hit a
  \(30\)-word family; CycleMin candidates at length 19 have
  median Hamming \(6\); worst \(m\)-finance is \(462\)
  isolated-even words.
- Finance and the length-11 CycleMin slack are
  word-order-independent, so they cannot select Christoffel
  among words of the same weight.
- No leftover length is excluded. Lebel sieving was not used.
  The almost-monochrome branch stays closed.

## Open questions

Stop on Christoffel unique-maximizers as a leftover-cell
reduction. Do not import Lebel. Do not reopen almost-monochrome
near-tightness. Cycle-only near-Christoffel rigidity — if a
cycle exists at leftover \(L\), must its word be close to
\(c_L\)? — remains open and is the same question as cycle-only
near-tightness. The leftover lengths remain a floor question.

## Decision

**CLOSE**. The unused Fernández–Ibáñez half does not become a
Juggler reduction to a one-parameter family. The Beatty
identification is already recorded; balance of \(c_L\) is
classical; leftover-itinerary and CycleMin candidates stay far from
the necklace. Cycle-only near-Christoffel rigidity is not
refuted and is not a new branch. This is not a halt theorem
and not a reason to raise the floor inside this branch.

Best next question: can a tighter \(\log 257\) certificate, or a
few more odd seeds, kill \(L=38\), or is the next real target
the convergent \(L=84\)?

## Publication assessment

Status: `ARCHIVED`.

A negative transfer: Christoffel unique-maximizers without the
affine equation do not reduce leftover Juggler words to a
necklace. The obstruction is finite and exact on the candidate
set. Not a paper candidate and not a Juggler totality result.
