# Juggler first shared AboveAnchor failure

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a two-sided
corridor reopen, not a first-lift-eighth reopen, not a PE-walk
census, not Paper A, and not a claim that every positive integer
reaches 1.

The odd-escape close left one honest question: which leftover
odd-landing corridor first fails a shared `AboveAnchor`
obstruction, if any. Generic `image < n` is excluded. The last
even-below-square letter is the tautological drop, not an answer.

## Problem

On a leftover-looking odd-odd start, is the first failure of
`AboveAnchor` a named shared cell already in the spine, or an
unexplained square-cell even after an odd landing?

## Exact statement

Let \(n\ge 3\) be odd with \(T(n)\) odd. Walk the realized
`AboveAnchor` prefix until the first \(k\) with \(T^k(n)<n\).
A *named shared obstruction* is a finite pattern whose
`FiniteProgress` bridge does not mention `CycleMin` or
`MinimalNonTerm`:

- envelope gap \(3^{\#O}<2^{|w|}\) on a still-high prefix
- start `OE`
- isolated \(O^aE(OE)^r\) with \(2^{a+2r+1}>3^{a+r}\)
- cube-even then even (`finiteProgress_of_cube_even_even`)
- cube-odd, even lift, even return below \(n^{2}\)
- eighth-cell `OEE` (`finiteProgress_of_odd_even_eighth`)
- two evens from \(n^{3}\le x<n^{4}\)

The last even state in \([n,n^{2})\) is excluded: every drop is
`even_below_square`. Phase 0 asks which named leftover first
hits a non-tautological cell, and whether that cell is new.

Named starts: \(37,69,89,365,501,1517,6187\). Odd-odd window
\(n<201\). This is not a halt theorem.

## Current literature

- `AboveAnchor` / square trap / isolated \(a=2\Rightarrow r=0\) —
  **EXACT — LEAN VERIFIED** (`J-above-anchor`)
- eighth-cell `OEE` —
  **EXACT — LEAN VERIFIED** (`J-mixed-oe-eighth`)
- cube even is already `FiniteProgress` —
  **REFUTED** (`J-cube-even-is-progress`); the second even is
  required
- first leftover cube-odd lift lies below \(n^{8}\) —
  **REFUTED** (`J-leftover-first-eighth`)
- two-sided corridor gap \(\Gamma\) —
  **CLOSE** (`juggler_odd_escape_corridor.md`)
- \(6187\) exits by `OE` from the \(L\)-image \(11189\) —
  **COMPUTATIONALLY VERIFIED** (`J-minimal-anchor-leftover-spine`)
- \(365/501\) merge at \(12707\) —
  **COMPUTATIONALLY VERIFIED** (`J-minimal-anchor-leftover-spine`)
- \(1517\) cube-odd \(43916043\) even-below-square —
  **EXACT — LEAN VERIFIED** as a cell, not a leftover law
  (`J-cube-odd-even-reset`)
- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**.
  Totality is not claimed

Project relationship: **extended**, then **reparameterized**.
The designated leftover question after the odd-escape close.

## Branch budget

```text
Mathematical target     which leftover odd-landing corridor
                        first fails a named shared
                        AboveAnchor cell, if any
Novelty hypothesis      a leftover hits a missed shared
                        lemma, or a new first-kill cell
Falsifier A             every non-tautological first kill
                        is eighth_oee / cube EE /
                        cube-odd-OEE / isolated / OE
Falsifier B             6187 (and a contrast twin) fail
                        only even_below_square after
                        square-odd OE
Falsifier C             the last square even is treated
                        as a new corridor
Existing machinery      AboveAnchor; even_below_square;
                        cube_even_even; eighth OEE;
                        cube_odd_even_below_square;
                        isolated_two; EnvelopeState
Maximum Phase-0 scope   named starts; odd-odd n<201;
                        no Lean; no letter census
Promotion criterion     a leftover first-fails a named
                        shared cell that uniformly kills
                        the leftover class, or a new cell
                        with a FiniteProgress bridge
Stop criterion          Falsifier A+B; machinery gravity;
                        halt claim; reopen of Gamma or
                        first-lift-eighth
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- last even in \([n,n^{2})\) as a new leftover corridor —
  **REPARAMETERIZATION** of `even_below_square`
- \(365,501\) first-fail eighth `OEE` at \(12707\) —
  **OBSERVATION**; already `finiteProgress_of_odd_even_eighth`
- \(1517\) first-fails cube-odd even-below-square at
  \(43916043\) — **OBSERVATION**; the named cube-odd witness
- \(37\) first-fails cube `EE` at \(5854\) — **OBSERVATION**
- \(69\) first-fails eighth `OEE` at \(1265\) — **OBSERVATION**
- \(6187,89\) first-fail only tautological square-odd `OE` —
  **OBSERVATION**; \(11189\to 1183550\to 1087\) was already
  the \(L\)-image exit
- a new shared first-kill cell —
  **REFUTED** on the named set and on odd-odd \(n<201\)
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.above_anchor_first_fail`
- Records: [juggler_above_anchor_first_fail.md](../research/juggler_above_anchor_first_fail.md),
  [juggler_above_anchor_first_fail.json](../research/juggler_above_anchor_first_fail.json)
- Tests: `tests/research/juggler_sequence/test_above_anchor_first_fail.py`

No CLI. No Lean. No leftover-itinerary census.

## Conjectures

None opened.

## Counterexamples

“Every leftover first-fails a non-tautological shared cell”
is false. \(6187\) and contrast \(89\) drop by `OE` from a
square-odd landing (\(11189\) and \(291\)) whose even image
is already below \(n^{2}\). That is `even_below_square`.

“A leftover first-fails a shared cell that was missed as a
uniform kill” is false. \(365\) and \(501\) die on the already
named eighth `OEE` at the merged state \(12707\). \(1517\)
dies on the already named cube-odd even-below-square witness
\(43916043\).

“The tautological square-odd `OE` is a new corridor” is
false. Odd-odd \(n<201\) adds only \(111,163\) of that shape,
together with \(89\). Isolated `OOEOE` is `aboveAnchor_isolated_two`.

## Formalization

None added. The catalog is already in `MinimumRelative`,
`FirstInternalOO`, `CubeCorridor`, `Corridor`, and `Progress`.
No `FirstAnchorFail.lean`. No `SharedObstruction.lean`.
Paper A is unchanged. No `sorry`.

## Results

Classification **FIRST_ANCHOR_FAIL_CLOSED**.

Non-tautological first kills on the named set are exactly

| Start | First strong cell | State |
|-------|-------------------|-------|
| \(37\) | cube `EE` | \(5854\) |
| \(69\) | eighth `OEE` | \(1265\) |
| \(365,501\) | eighth `OEE` | \(12707\) |
| \(1517\) | cube-odd even-below-square | \(43916043\) |
| \(89,6187\) | none | square-odd `OE` |

On odd-odd \(n<201\) the histogram is eighth `OEE` \(26\),
isolated scale-gap \(11\), cube-odd-OEE \(8\), cube `EE` \(4\),
two-even-below-fourth \(4\), tautological-only \(89,111,163\).
No tag leaves the catalog. No envelope gap fires while the
state is still \(\ge n\).

This is Falsifier A and B. Falsifier C is the excluded
reading. There is no missed shared lemma that kills the
leftover class, and no new first-kill cell.

## Open questions

None from first-kill classification. Do not add
`FirstAnchorFail.lean`. Do not census square-odd `OE` exits.
Do not reopen \(\Gamma\) or first-lift-eighth. The leftover
hole is unchanged: a cube cell without a square cell, now
with the explicit rider that some finite leftovers never hit
a longer named pattern before the tautological square trap.

## Decision

**CLOSE**. The leftover question is answered: no odd-landing
corridor first fails a *new* shared `AboveAnchor` obstruction.
When a leftover dies on a strong cell, that cell is already
`finiteProgress_of_odd_even_eighth`,
`finiteProgress_of_cube_even_even`, or
`finiteProgress_of_cube_odd_even_below_square`. The leftover
that avoids those cells, \(6187\), fails only
`even_below_square` after a square-odd `OE`. Contrast \(89\)
is the same shape. A branch of that kind is a close.

Best next question: none from first-kill classification.

## Publication assessment

Status: `EXPLORATORY`.

A negative first-kill classification. Not a paper candidate
and not a Juggler totality result.
