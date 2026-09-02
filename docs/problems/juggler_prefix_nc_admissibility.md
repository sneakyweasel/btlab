# Juggler prefix-NC arithmetic admissibility

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can a mixed prefix-noncontracting itinerary remain arithmetically realizable
as its length grows, once every exact floor-cell constraint is imposed
backwards?

## Exact statement

An itinerary \(w\) of length \(k\) is prefix-noncontracting when every prefix
has

\[
G_j=2^j-3^{o_j}\le 0.
\]

Exclude monochrome \(E^k\) and \(O^k\). For a prescribed \(w\), write
\(A(w)\) for the set of starts that realize every letter, and
\(A(w;I)\) for the subset whose image after \(w\) lies in a finite
image interval \(I\). The Phase-0 question is whether backward even
and odd cells make \(A(w)\) empty for long mixed \(w\), or whether
those cells only rewrite the existing inverse-floor lemmas.

This says nothing about totality. An empty fiber over a bounded image
interval is not \(A(w)=\varnothing\). A search-horizon realization is
not an infinite family.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Inverse-floor cells
  `floorPower_even_eq_iff_sq_interval` /
  `floorPower_odd_eq_iff_cube_interval` / `odd_preimage_unique` —
  **EXACT — LEAN VERIFIED**.
- Compensated contraction —
  **EXACT — LEAN VERIFIED**.
- Prefix-NC language and a forward scan through length 10 —
  **OBSERVATION**, parked as `NEAR_EXTREMAL_STRUCTURE_GREEN`.
- Odd-odd residual continuation —
  **REFUTED** as a scalar invariant; closed as
  `ODD_ODD_RESIDUAL_COMPLEX`.

Project relationship: **extended**. The leftover after the prefix-NC
language and the closed residual branch is tested as backward
arithmetic admissibility. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does arithmetic realizability eliminate
                        long mixed prefix-NC words?
Novelty hypothesis      backward floor cells empty or shrink A_NC
                        until no integer start survives
Falsifier               the constraints are the existing cells;
                        every mixed prefix-NC word of the window
                        is realized; empty-over-I is not empty
Existing machinery      inverse-floor iff, odd_preimage_unique,
                        prefix_nc_words, follows_itinerary, compensated
                        contraction, known horizon witnesses
Maximum Phase-0 scope   exact pullback on mixed k≤8 plus the known
                        length-10/11 witnesses; compare min n,
                        small-image emptiness, one-letter extension;
                        Lean only if a law survives
Promotion criterion     an exact emptiness law for a specified
                        family, with Lean or a short in-phase proof
Stop criterion          PREFIX_NC_ARITHMETIC_COMPLEX; cell-tree
                        engine; ResidualStep growth; inferred L; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Even pullback of an image \(q\) is the even cell
  \([q^2,(q+1)^2)\) — **EXACT — LEAN VERIFIED**
- Odd pullback of an image \(m\) has at most one integer —
  **EXACT — LEAN VERIFIED** (`odd_preimage_unique`)
- \(A(\mathtt{OOE},6)=\{5\}\) —
  **COMPUTATIONALLY VERIFIED**
- every mixed prefix-NC itinerary of length \(\le 8\) is realized with
  \(n\le 800\) — **OBSERVATION**
- empty fiber over images \(1..24\) implies unrealizable —
  **REFUTED**; `OOEOOOOOOO` is empty over that interval and
  realized at \(173\)
- long mixed prefix-NC words are arithmetically empty —
  **REFUTED** in the window: \(37\) realizes `OOOOEOOOEE`,
  \(173\) realizes `OOEOOOOOOO`, \(2127\) realizes `OOOOEOOOOEE`
- a finite bound \(L\) — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.prefix_nc_admissibility`
  (`init` / `run` / `resume` / `status` / `summarize`)
- Records: [juggler_prefix_nc_admissibility.md](../research/juggler_prefix_nc_admissibility.md),
  [juggler_prefix_nc_admissibility.json](../research/juggler_prefix_nc_admissibility.json)
- Dataset: `data/research/juggler/prefix_nc_admissibility/`
- Tests: `tests/research/juggler_sequence/test_prefix_nc_admissibility.py`
- The Research Engine control layer is not modified.
- `ResidualStep` is not extended.

## Conjectures

None opened.

## Counterexamples

- H1 (every mixed prefix-NC itinerary of length \(\ge L\) is
  unrealizable): all \(43\) mixed itineraries of length \(\le 8\) are
  realized with \(n\le 800\). Length-\(10\) and length-\(11\)
  witnesses exist.
- H2 (those itineraries require compensated contraction): `OOE` at
  \(n=5\) has \(\Delta\) below the formal gap. Horizon witnesses
  do not produce a defect-driven certificate inside the bit
  budget.
- Empty-over-image-\(24\) as unrealizable: `OOEOOOOOOO` at
  \(173\).
- Interval collapse under every one-letter extension: E-extension
  did not widen the small-image slice, because most parents were
  already empty there. That is a cap artefact, not a law.

These kill H1–H2 in the window. They do not produce an infinite
family and do not imply a bound \(L\).

## Formalization

None added. The inverse-floor lemmas and `odd_preimage_unique` already
live in `formal/Problems/Engine/FloorPower.lean`. No
`PrefixNCAdmissibility.lean`. `ResidualChain.lean` is not
rewritten. No `sorry`. No ledger row.

## Results

Classification **PREFIX_NC_ARITHMETIC_COMPLEX**.

Backward admissibility is the existing even cell and the existing
odd cell, composed along the itinerary. On mixed prefix-NC words of
length \(\le 8\) the combinatorial language and the arithmetic
language agree: every such word has a realizing start. Empty
fibers over a bounded image interval are not empty realizing
sets. Long odd tails produce images too large for a cheap exact
fiber, which is a computational truncation, not an obstruction.
No Lean file.

## Open questions

Do not build a cell-tree engine and do not reopen ResidualStep.
Answered in [juggler_escape_state.md](juggler_escape_state.md):
the combined escape margin is `ESCAPE_STATE_COMPLEX`.

## Decision

**CLOSE** the backward-admissibility branch as
`PREFIX_NC_ARITHMETIC_COMPLEX`. Record the exact `OOE` fiber, the
killing of H1/H2 in the window, and the image-cap versus
unrealizable distinction. Do not add Lean. Do not infer a bound
from the window. Do not claim termination.

Best next question: answered in
[juggler_escape_state.md](juggler_escape_state.md).

## Publication assessment

Status: `EXPLORATORY`. A negative admissibility result, not a
paper candidate and not a Juggler totality result.
