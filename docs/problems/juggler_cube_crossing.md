# Juggler cube-boundary crossing

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
power-cell hierarchy, not `OddEscapeCorridor`, not a relational
\(\Sigma\) automaton, not \(Z_5\), not a length-11 assembly, not a
four-even cell, not p-adic machinery, not Paper A, and not a claim
that every positive integer reaches 1.

Phase 0 of the two-sided corridor program closed: the leftover hole
is the odd cube cell \(n^{2}\le x<n^{3}\) with \(T(x)\ge n^{3}\).
This phase treats that crossing as one arithmetic operation and
asks what, if anything, survives into the first re-entry.

## Problem

What arithmetic information about an odd cube-band state \(x\)
survives the exact crossing \(y=T(x)\ge n^{3}\) and constrains the
first return from \(y\)?

## Exact statement

Let \(n\ge 2\) and \(n^{2}\le x<n^{3}\) with \(x\) odd. Write
\(y=\lfloor x^{3/2}\rfloor\), so

\[
x^{3}=y^{2}+\delta,\qquad 0\le\delta<2y+1.
\]

Let \(F(x)\) be the next odd state in \([n^{2},n^{3})\) on the
realized `AboveAnchor` orbit, if it exists. Phase 0 asks whether
the pair \((x^{3}=y^{2}+\delta,\; n^{2}\le x<n^{3})\) imposes a
reusable restriction on \(F(x)\) or on the first return to
\([n,n^{3})\), beyond `CubeOddLanding`, `cube_odd_lift`,
`cube_lift_even_reset`, `odd_preimage_unique`, and `EnvelopeState`.

The named starts are \(37,69,89,365,501,1517,6187\). This is not
a halt theorem.

## Current literature

- Cube-odd even reset \(T^{2}(x)<x\) and odd continuation
  \(T^{2}(x)>x\), \(T^{2}(x)\ge n^{4}\) —
  **EXACT — LEAN VERIFIED** (`J-cube-odd-even-reset`)
- Even return always below \(n^{2}\) —
  **REFUTED** (`J-cube-odd-even-below-square`)
- Persistent-odd first even below \(x^{2}\) —
  **REFUTED** (`J-source-relative-odd-reset`)
- Two-sided corridor width as a Lyapunov quantity —
  **CLOSE** (`juggler_odd_escape_corridor.md`)
- Unique occupant of an odd floor cell —
  **EXACT — LEAN VERIFIED** (`odd_preimage_unique`)
- Empty-odd-cell PE forward law —
  **REFUTED** (`J-empty-odd-pe-forward`)
- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**.
  Totality is not claimed

Project relationship: **extended**, then **reparameterized**. The
designated local question after the corridor CLOSE.

## Branch budget

```text
Mathematical target     a reusable restriction on the first
                        re-entry from the exact crossing
                        x^3 = y^2 + delta inside n^2 <= x < n^3
Novelty hypothesis      source-cell position or the defect
                        couples to F(x) or a forbidden return
                        cell
Falsifier A             F undefined on most surviving states
Falsifier B             source/target defect as unconstrained
                        as a generic odd step
Falsifier C             F moves broadly across the cube band
Falsifier D             a periodic orbit of F
Falsifier E             every relation is EnvelopeState,
                        cube_odd_lift, or even_below_anchor_pow
Existing machinery      CubeOddLanding; cube_odd_lift;
                        cube_lift_even_reset; odd_preimage_unique;
                        EnvelopeState; 37 / leftover laboratories
Maximum Phase-0 scope   cube-crossing dataset on named starts;
                        no Lean; no inverse census; no Sigma
Promotion criterion     F(x) in a strict parameterized I(x),
                        or no periodic orbit of a stable F,
                        or AboveAnchor + repeated crossings
                        implies FiniteProgress or recurrence
Stop criterion          generic defects; unstable F; power-cell
                        chain; residue automaton; Z5 / length-11
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\delta\) even and \(\delta\equiv x-1\pmod 8\) when \(y\) is
  odd — **REPARAMETERIZATION** of a generic odd-odd step
- unique \(x\) with \(T(x)=y\) — **KNOWN** (`odd_preimage_unique`)
- \(n^{3}\le y<n^{5}\) — **EXACT — LEAN VERIFIED**
  (`cube_odd_lift`)
- even \(y\) gives \(T^{2}(x)<x\) — **EXACT — LEAN VERIFIED**
- odd \(y\) leaves the cube band, so the cube-band even-return
  theorem cannot apply to \(y\) — **OBSERVATION**
- induced \(F\) on odd cube states —
  **COMPUTATIONALLY VERIFIED** as partial and two-sided
- \(F^{2}(x)<x\) when \(F^{2}\) exists —
  **OBSERVATION** on two terminating orbits; not a law
- source offset \(a=x-n^{2}\) transports \(y\) into a proper
  subinterval of \([n^{3},n^{5})\) beyond \(x^{3/2}\) —
  **REFUTED** as an independent restriction
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cube_crossing`
- Records: [juggler_cube_crossing.md](../research/juggler_cube_crossing.md),
  [juggler_cube_crossing.json](../research/juggler_cube_crossing.json)
- Tests: `tests/research/juggler_sequence/test_cube_crossing.py`

No CLI. No Lean. No generic predecessor enumeration.

## Conjectures

None opened.

## Counterexamples

“\(F\) is defined on every surviving cube-odd state” is false.
Of ten named crossings, five have no later odd cube landing.
The first leftover crossings of \(365\) and \(1517\) even-reset
below \(n^{2}\) and drop without a second odd cube. Contrast
starts \(69,89\) have no cube-odd landing at all.

“The crossing defect is stricter than a generic odd-odd step”
is false. When \(y\) is odd, \(\delta\equiv x-1\pmod 8\) holds
for every odd-odd step on the same orbits, cube or not, and
\(\delta/(2y+1)\) fills a broad subinterval of \((0,1)\).

“\(F(x)<x\)” is false: \(F(3375)=9317\) and
\(F(6812597)=48693935\). “\(F(x)>x\)” is also false:
\(F(9317)=2233\) and \(F(48693935)=296551\).

“An additional condition makes the cube-band even-return
theorem apply after one more odd step” is false. The odd lift
satisfies \(y\ge n^{3}\), so \(y\) is not a cube-band source.

## Formalization

None added. Existing `MinimumRelative`, `Corridor`, and
`Cells` already contain the crossing and uniqueness lemmas.
No `CubeCrossing.lean`. No `CrossingMap.lean`. Paper A is
unchanged. No `sorry`.

## Results

Classification **CUBE_CROSSING_CLOSED**.

Ten cube-odd landings occur on the named starts. Contrast
\(69,89\) contribute none. Every leftover first crossing has
even \(y\) and \(\tau=1\); that branch is
`cube_lift_even_reset`. The only odd lifts are the three
\(37\)-crossings \(3375,9317,2233\).

The exact floor identity \(x^{3}=y^{2}+\delta\) forces only
generic odd-odd arithmetic: \(\delta\) even and
\(\delta\equiv x-1\pmod 8\) when both are odd. The same
congruence holds on non-cube odd-odd steps. Unique preimage
is `odd_preimage_unique`, independent of the source cell. The
two-step identity
\(x^{9}-z^{4}=3y^{4}\delta_{1}+3y^{2}\delta_{1}^{2}+\delta_{1}^{3}+2\delta_{2}y^{3}-\delta_{2}^{2}\)
holds, but \(\Psi\) does not exclude a return cell.

The induced map \(F\) is defined on five of ten crossings,
moves both up and down, and is not periodic. Where \(F^{2}\)
exists it drops, but those orbits already terminate by the
ordinary envelope. First re-entry to \([n,n^{3})\) is
sometimes below \(n^{2}\), sometimes even in the cube band
(\(501\) later, \(6187\) second, \(2233\to 5854\)), sometimes
odd in the cube band. There is no forced “cube-odd to
cube-odd” recurrence.

This is Falsifier A, B, C, and E. Not Falsifier D.

## Open questions

None from local crossing arithmetic. Do not introduce
`CubeCrossing`. Do not push a further power-cell chain. Do
not build a residue automaton. The leftover hole is still a
cube cell without a square cell; any further attack has to be
a genuinely global property of repeated crossings, not another
local identity at the boundary.

## Decision

**CLOSE**. The exact near-power relation together with the
source cell adds no restriction beyond `odd_preimage_unique`,
`cube_odd_lift`, and generic odd-odd parity. \(F\) is not a
stable residual class. The missing hypothesis that would
reuse the even-return theorem after one more odd step does
not exist: the image has already left the cube band. A branch
of that kind is a close.

Best next question: none from local cube-boundary arithmetic.
The residual is still an odd cube cell whose even lift is
known and whose odd lift is a generic high odd step.

## Publication assessment

Status: `EXPLORATORY`.

A negative local-crossing fragment. Not a paper candidate and
not a Juggler totality result.
