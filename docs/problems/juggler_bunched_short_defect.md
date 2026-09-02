# Juggler exact short-cluster closure via defect

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
leftover-suffix path table, not a predecessor-cell census, not a
raise-above invariant, not a preimage enumerator, not a \(Z_5\)
family, not a length-11 assembler, not a four-even leftover cell,
and not a claim that every positive integer reaches 1.

## Problem

After exact return sets \(R_{b,c}(n)\) are characterized and
**PARK**, does rewriting

\[
T_{O^bEO^cE}(y)=n
\]

as a local floor-defect identity force a size, parity, or
signature that a `CycleMin` prefix cannot meet?

## Exact statement

Let \(n\) be odd and \(y=T_u(n)\ge n\). Write
\(\varepsilon=\mathrm{localDefectEven}(t)\) and
\(\eta=\mathrm{localDefectEven}(y)\) on even steps, and
\(\delta=\mathrm{localDefectOdd}(z)\) on odd steps. Exact
closure is equivalent to the identities below, not to a search
for \(y\).

The Phase-0 questions are:

1. What is the exact \(c=0\) relation between the `EE` entrance
   and \(n^4\)?
2. What is the exact \(c=1\) last-odd equation, and is
   \(z^3=n^4+\delta\) with tiny \(\delta\) possible?
3. Do the local bounds \(0\le\rho<2T+1\) and the known
   odd-to-odd parity force a residue the closure cannot meet?
4. After composition, is the terminal \(1+Q\) a new obstruction
   or the leftover `EE` cell in defect coordinates?

This is not a `CycleItinerary` theorem at a non-minimum start. It is
not a four-even cell and not a halt theorem.

## Current literature

- Local even / odd defects —
  **EXACT — LEAN VERIFIED** (`localDefectEven_add`,
  `localDefectOdd_add`, `localDefectOdd_lt_succ`).
- Odd-to-odd remainder is even —
  **EXACT — LEAN VERIFIED** (`odd_remainder_even`).
- Last even landing is not an odd square —
  **EXACT — LEAN VERIFIED** (`cycle_last_even_ne_odd_sq`).
- Exact return sets \(R_{b,c}(n)\) —
  **PARK** (`J-cyclemin-short-return-census`). The `EE` fibre
  is abundant. Not reopened as a \(y\)-table.
- Leftover-suffix, predecessor cells, front overshoot —
  **PARK**. Not reopened.

Project relationship: **extended**. The defect rewrite of the
parked exact-return characterisation.

## Branch budget

```text
Mathematical target     Exact T_{O^b E O^c E}(y)=n forces a
                        defect equation CycleMin y cannot meet
Novelty hypothesis      local closure defects have impossible
                        size, parity, or signature
Falsifier               ordinary-size defects; unrestricted
                        signatures; leftover-cell rewrite
Existing machinery      localDefectEven/Odd; cycle_last_even
                        ne_odd_sq; odd_remainder_even
Maximum Phase-0 scope   c=0/c=1 identities; last-odd defect
                        scan; EE signatures; no Lean
Promotion criterion     one closure obstruction, or all seven
                        families from one prefix lemma
Stop criterion          cell/interval rewrite; inversion;
                        ad hoc per (b,c); arbitrary modulus
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(z^3=n^4+\delta\) with tiny \(\delta\) is the last-odd
  equation —
  **REFUTED**. CycleMin \(n\) is odd, so the last even landing
  is \(t=n^2+\varepsilon\) with \(\varepsilon\ge 1\) odd, and
  \(t^2-n^4\ge 2n^2+1\)
- exact `EE` closure is an impossible defect equation —
  **REFUTED**. \(y=n^4+2\varepsilon n^2+\varepsilon^2+\eta\)
  with ordinary \(\varepsilon,\eta\) in the successor windows
- last-odd \(\delta\) has the wrong parity for an even landing —
  **REFUTED**. Onto an even \(t\), \(\delta\) is odd; the scan
  has 15 such hits for odd \(13\le n<49\), all ordinary
- composed \(1+Q\) is a new sign obstruction —
  **REFUTED**. \(1+Q=y/n^4=(1+\varepsilon/n^2)^2+\eta/n^4\) is
  the leftover `EE` cell
- `EE` defect signatures form a finite algebraic type —
  **REFUTED**. At \(n=13\) and \(n=15\) every admissible
  \((\varepsilon,\eta)\bmod 8\) pair occurs
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.bunched_short_defect`
- Records: [juggler_bunched_short_defect.md](../research/juggler_bunched_short_defect.md),
  [juggler_bunched_short_defect.json](../research/juggler_bunched_short_defect.json)
- Tests: `tests/research/juggler_sequence/test_bunched_short_defect.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The tiny-gap last-odd equation is **REFUTED**. For odd \(n\),

\[
t^2-n^4\ge 2n^2+1,
\]

and \(n=13\) already has last-odd \(z=31\),
\(\delta=207\), gap \(1023\).

The impossible-`EE`-defect claim is **REFUTED** by the
parametrization. At \(n=13\), \(\varepsilon=1\), \(\eta=0\)
gives \(y=28900=13^4+339\) and \(T_{EE}(y)=13\). The fibre has
2366 even-even states and all 16 admissible 8-adic pairs.

The stronger claims that remain false or unproved:

- “exact closure forces a residue \(r\not\equiv s\)” — false;
  last-odd \(\delta\) occupies all odd classes mod 8.
- “the seven families need seven defect theories” — false;
  they collapse to \(c=0\) (`EE` fibre plus \(b\) odd defects)
  and \(c=1\) (last-odd layer).
- “every last-cluster class is now excluded” — false.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

None. Existing `Defect.lean`, `SequentialMordell.lean`, and
`cycle_last_even_ne_odd_sq` are cited, not rewritten. No
`no_cycleMin_prefix_short`. No `no_cycleMin_four_even`. No
`no_cycle_itinerary_length_eleven`. No `no_juggler_cycle`. Paper A
is unchanged.

## Results

Classification **SHORT_DEFECT_PARK**.

Exact closure is two identities, not seven theories.

For \(c=0\),

\[
y=n^4+2\varepsilon n^2+\varepsilon^2+\eta,
\]

with \(\varepsilon=\mathrm{localDefectEven}(t)\) odd,
\(\eta=\mathrm{localDefectEven}(y)\) even, and \(t\) even in
\([n^2,(n+1)^2)\). The \(b=1,2,3\) cases add ordinary odd-step
defects in front of that `EE` fibre.

For \(c=1\),

\[
z^3=t^2+\delta=n^4+2\varepsilon n^2+\varepsilon^2+\delta,
\]

with \(0<\delta\le 2t\) and \(\delta\) odd. That is the natural
odd-to-even window, not a tiny gap to \(n^4\).

The composed \(1+Q\) is the leftover `EE` cell. Defect
signatures are unrestricted. This is not \(Z_5\), not a
length-11 census, not a four-even assembler, and not a halt
theorem.

## Open questions

Prefixes with no `OO` at all cannot occupy the fibre
([juggler_isolated_odd_return.md](juggler_isolated_odd_return.md)).
Prefixes with \(a_0\ge 2\) that stay isolated-odd after the
first even are parked
([juggler_isolated_odd_fibre.md](juggler_isolated_odd_fibre.md)).
Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`. Do not reopen leftover-suffix
tables, raise-above, or \(y\)-preimage enumeration.

## Decision

**PARK**. Exact closure is a defect identity, and that identity
is satisfiable with ordinary unrestricted defects. It is the
leftover `EE` cell in other coordinates, not a new obstruction.
Do not claim that every cycle itinerary is impossible.

Best next question: answered in
[juggler_isolated_odd_return.md](juggler_isolated_odd_return.md)
and [juggler_isolated_odd_fibre.md](juggler_isolated_odd_fibre.md).

## Publication assessment

Status: `EXPLORATORY`.

A named pair of closure identities plus a refuted tiny-gap /
impossible-signature hypothesis. Not a paper candidate and not
a Juggler totality result.
