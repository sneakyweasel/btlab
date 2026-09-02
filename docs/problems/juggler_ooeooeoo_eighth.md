# Juggler OOEOOEOO eighth lower cell

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a W_5
reopen, not a first-return \(Q\)-map, not a defect census, not
Paper A, and not a claim that every positive integer reaches 1.

The leftover first-lift theorem is already **REFUTED**. The gap
word is \(\mathtt{OOEOOEOO}\). This phase asks whether that itinerary
forces the complementary side \(x^{3}\ge n^{8}\).

## Problem

Is every first cube-odd even lift of \(\mathtt{OOEOOEOO}\) forced
above \(n^{8}\), or is that only the \(4309\) family?

## Exact statement

Let \(n\) be odd and suppose the first cube-odd landing \(x\) of
\(n\) follows \(\mathtt{OOEOOEOO}\). The preferred lower-cell
theorem was

\[
x\text{ odd},\qquad T(x)\text{ even}
\Longrightarrow
x^{3}\ge n^{8}.
\]

The inherited upper envelope only gives \(x^{256}\le n^{729}\),
hence \(x<n^{3}\). The full-word `LowerPowerBound` would force
\(x^{3}\ge n^{8}\) only for \(n\) of about \(73\) bits. No
laboratory-scale lower cell was obtained.

On every odd \(n<200001\) with this first lift, \(x^{3}\ge n^{8}\)
holds, including odd \(T(x)\). The ratio tracks the formal
upper scale

\[
\frac{x^{3}}{n^{8}}\approx n^{139/256}
\]

and therefore moves away from the boundary as \(n\) grows. The
smallest even-\(T\) example \(n=4309\) already has
\(x^{3}/n^{8}\approx 94\).

## Current literature

- mixed OE cell \(T^{2}(x)<n^{2}\Leftrightarrow x^{3}<n^{8}\) —
  **EXACT — LEAN VERIFIED** (`J-mixed-oe-eighth`)
- first leftover cube-odd even lift always below \(n^{8}\) —
  **REFUTED** (`J-leftover-first-eighth`)
- \(\mathtt{OOEOOEOO}\) cube envelope \(x<n^{3}\) —
  **EXACT — LEAN VERIFIED** (`follows_ooeooeoo_image_lt_cube`)
- `LowerPowerBound` on the full word forces the eighth cell
  at laboratory \(n\) —
  false (denominator has \(3395\) bits)
- Every start reaches 1 — not claimed

Project relationship: **extended**. The designated next question
of the first-lift refutation.

## Branch budget

```text
Mathematical target     OOEOOEOO first cube-odd => x^3 >= n^8?
Novelty hypothesis      a reusable lower envelope, not 4309
Falsifier               first cube-odd OOEOOEOO with x^3 < n^8
                        or only upper-envelope restated
Existing machinery      follows_ooeooeoo_image_lt_cube;
                        LowerPowerBound; odd_even_eighth_lt_sq
Maximum Phase-0 scope   first-hit census; LPB bits;
                        n^{139/256} tracking; no defect census
Promotion criterion     shared lower cell consumed by
                        MinimumRelative
Stop criterion          only x < n^3; LPB fires at 2^73;
                        defect tightness census; word table
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- full-word `LowerPowerBound` forces \(x^{3}\ge n^{8}\) for
  leftover \(n\) —
  false
- composed `OOE` then `OOEOO` lower bounds —
  the same \(73\)-bit threshold
- first cube-odd even lift of \(\mathtt{OOEOOEOO}\) sits next
  to \(n^{729/256}\) —
  **COMPUTATIONALLY VERIFIED** on \(n<200001\)
- odd \(T(x)\) can sit below \(n^{8}\) on this itinerary —
  not observed in the window
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.ooeooeoo_eighth`
- Records: [juggler_ooeooeoo_eighth.md](../research/juggler_ooeooeoo_eighth.md),
  [juggler_ooeooeoo_eighth.json](../research/juggler_ooeooeoo_eighth.json)
- Tests: `tests/research/juggler_sequence/test_ooeooeoo_eighth.py`
- Lean: none new. The existing cube envelope of
  \(\mathtt{OOEOOEOO}\) is reused. Paper A unchanged. No `sorry`.

## Conjectures

None opened. A finite scan is not a conjecture.

## Counterexamples

“`LowerPowerBound` on \(\mathtt{OOEOOEOO}\) is a laboratory-scale
eighth-cell lower bound” is false. The denominator has \(3395\)
bits; the comparison \(n^{139/3}\ge D\) begins near \(73\)-bit
\(n\).

No first cube-odd landing of the itinerary with \(x^{3}<n^{8}\) was
found for odd \(n<200001\). That is not a counterexample to a
proved lower cell, because no such cell was obtained.

## Formalization

No new Lean file and no eighth-lower primitive. The existing
theorem `follows_ooeooeoo_image_lt_cube` remains the only
word-level bound. Paper A is unchanged. No `sorry`. No halt
theorem.

## Results

Classification **OOEOOEOO_EIGHTH_PARKED**.

The complementary side of the mixed cell is the cube envelope,
not a new \(n^{8}\) lower cell. On the scanned window the
first-hit images hug that envelope: at \(n=4309\),
\(1000\cdot x^{3}/n^{8}=94024\) against the formal
\(94048\). The same pattern holds for the long leftover
\(n=5791\) and for the odd-\(T\) first hit \(n=565\).

This is not a halt theorem and not a first-return section.

## Open questions

None from forcing \(\mathtt{OOEOOEOO}\) above \(n^{8}\). Do not
open a defect-tightness census. Do not resume a first-return
\(Q\)-map. Do not reopen W_5.

## Decision

**PARK**. The preferred lower-cell theorem was not proved and
is not a restatement of `even_below_fourth`. The laboratory
evidence is that first hits hug \(n^{729/256}\) and recede from
\(n^{8}\). Existing lower-power machinery is too weak to turn
that into a shared lemma.

Best next question: none from the eighth-gap lower bound. The
mixed cell already names both sides.

## Publication assessment

Status: `EXPLORATORY`.

A negative lower-cell check plus an envelope-tracking scan.
Not a paper candidate and not a Juggler totality result.
