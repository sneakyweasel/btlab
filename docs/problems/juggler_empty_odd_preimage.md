# Juggler empty-odd-preimage geometry of PE landings

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
`PredClosure` reopen, not Paper A, and not a claim that every
positive integer reaches 1.

The parked minimal-anchor attack left a unique odd spine into PE
landings with no odd predecessor. This phase asks what emptiness
is arithmetically, and whether it forces anything forward.

## Problem

Characterize PE landings whose odd predecessor cell is empty, and
decide whether repeated empty-cell landings impose a new forward
constraint.

## Exact statement

For \(x\in\mathbb N\), an odd predecessor requires
\(x^2\le z^3<(x+1)^2\). Let \(k=\lceil x^{2/3}\rceil\), computed as
the least integer with \(k^3\ge x^2\). Then the cell has

- Type 0 (no integer) iff \(k^3\ge(x+1)^2\),
- Type 1 (even occupant) iff \(k^3<(x+1)^2\) and \(k\) is even,
- Type 2 (odd occupant) iff \(k^3<(x+1)^2\) and \(k\) is odd.

`OddPredEmpty`(\(x\)) means Type 0 or Type 1:
\(k^3\ge(x+1)^2\) or \(k\) even. Decide whether a leftover
`AboveAnchor` PE landing with `OddPredEmpty` forces a next-step
parity restriction, a square-cell subinterval, or a finite
empty-landing chain.

## Current literature

- `odd_preimage_unique` / `odd_preimage_iff` —
  **EXACT — LEAN VERIFIED**
- leftover PE landings `763`, `1749`, `4447`, `12707` have no odd
  predecessor — **COMPUTATIONALLY VERIFIED**
  (`J-minimal-anchor-leftover-spine`)
- minimal-anchor descent / short structured return —
  **REFUTED** (`J-minimal-anchor-closure`)
- escape-episode rank descent —
  **REFUTED** (`J-escape-episode-dichotomy`)
- `PredClosure \leftrightarrow ReachesOne` — closed, not reopened
- Every start reaches 1 — not claimed

Project relationship: **extended**. The designated next question of
the parked empty-spine observation.

## Branch budget

```text
Mathematical target     exact OddPredEmpty, and whether PE
                        landings with empty odd cells force a
                        forward transition law
Novelty hypothesis      emptiness is a geometric state with a
                        local map, not just a missing pred
Falsifier               generic width; no next-step restriction;
                        reduces to odd_preimage_unique
Existing machinery      odd_preimage_unique; odd_preimage_iff; pred_odd;
                        leftover controls; AboveAnchor
Maximum Phase-0 scope   cube iff; Type 0/1/2; 365/501/1517/6187;
                        no new Lean
Promotion criterion     exact next-step restriction, or finite
                        consecutive-empty bound
Stop criterion          no forward consequence; density only;
                        itinerary census; PredClosure rename
```

## Balanced-ternary formulation

Optional coordinate on cube-gap residue of \(x^2\). No forced BT
law appeared.

## Why BT may be relevant

A sparse lsd description of Type 2 occupants would have been a BT
observation. Emptiness is a cube-versus-square comparison and does
not need a ternary digit.

## Candidate operations / invariants

- Type 0 iff \(k^3\ge(x+1)^2\) —
  **EXACT — HUMAN PROOF**
- `OddPredEmpty` iff Type 0 or Type 1 —
  **EXACT — HUMAN PROOF**
- leftover PE landings of `365`, `501`, `1517`, `6187` are Type 0 —
  **COMPUTATIONALLY VERIFIED**
- ambient PE landings are Type 0 with share \(>4/5\) —
  **COMPUTATIONALLY VERIFIED**
- empty PE landing forces the next parity —
  **REFUTED**
- empty PE landing forces a square-cell subinterval —
  **REFUTED**
- emptiness persists along the orbit —
  **REFUTED** (an odd step always makes \(T(x)\) Type 2)
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.empty_odd_preimage`
- Records: [juggler_empty_odd_preimage.md](../research/juggler_empty_odd_preimage.md),
  [juggler_empty_odd_preimage.json](../research/juggler_empty_odd_preimage.json)
- Tests: `tests/research/juggler_sequence/test_empty_odd_preimage.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

Ordinary terminating orbits, not `MinimalNonTerm` witnesses.

- “empty \(\Rightarrow\) next even” — `763\to 21075` is odd;
  `12707\to 1432400` is even.
- “empty \(\Rightarrow\) \(y\) in a forced subinterval of
  \([x^2,(x+1)^2)\)” — leftover offsets run from about \(0.04\)
  (`10613`) to about \(0.92\) (`12707`).
- “empty persists” — \(T(763)=21075\) is Type 2 with occupant
  `763`. Any odd \(x\) makes \(T(x)\) Type 2, empty or not.
- “leftover emptiness is special” — Type 0 is about \(95\%\) of
  \(x\le 4000\). `69` has Type 1 at `117`; `89` has Type 2 at `70`.
- `763` on `501` is the same Type 0 state as on `365`, not a new
  transition type.

## Formalization

No new Lean module. The cube criterion is recorded as a human
proof. `odd_preimage_unique` and `odd_preimage_iff` stay in `Preimages.lean`.
Not imported by `Problems.JugglerPaper`. No `sorry`. No
`OddPredEmpty` API. No `juggler_reaches_one`.

## Results

Classification **EMPTY_ODD_PREIMAGE_PARK**.

`OddPredEmpty` is the exact cube test
\(k=\lceil x^{2/3}\rceil\), then \(k^3\ge(x+1)^2\) or \(k\) even.
That is the arithmetic content of an empty odd branch. On leftover
controls every PE landing is Type 0, but so is the ambient PE
population. An odd step always produces a Type 2 image, so
empty-to-empty PE sequences are not orbit persistence: emptiness
breaks at every odd letter and reappears generically after the
next even. No next-parity law and no square-cell subinterval.

## Open questions

Stop. Do not count empty cells. Do not reopen interval closure.
Do not attach a residue automaton to the cube gap.

## Decision

**PARK**. The emptiness criterion is exact and reusable, but it
has no forward dynamical consequence beyond `odd_preimage_unique` and
generic cell width. Leftover Type 0 landings are the expected
ambient type. Falsifiers A, C, and D hold: future behaviour is
generic, empty PE chains can be long with no changing exact
quantity, and the only forced Type 2 after an odd step is the
definition of \(T\).

Best next question: none from emptiness itself. The leftover
corridor remains an odd-landing PE walk whose landings are
generically Type 0.

## Publication assessment

Status: `EXPLORATORY`. An exact emptiness predicate plus a
negative forward-law fragment, not a paper candidate and not a
Juggler totality result.
