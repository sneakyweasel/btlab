# Juggler (19,12) landing-cell law

Status: **CLOSE** (the two-way landing slogan is **REFUTED**; remaining
cell labels are \(T\)-parity and do not force letter 3)

Child of [juggler_flight_post19_tail.md](juggler_flight_post19_tail.md).
Not a halt theorem, not a divergence exclusion, not a mechanical-lift
\(\xi\)-cocycle reopen, not a CF census, and not a Paper A edit.

## Problem

A long post-19 miss is walk-height overshoot, and both long
witnesses leave hug at letter 3. That extra \(O\) is not forced by
`AboveAnchor` alone. Does the *landing cell* after a realized
\((19,12)\) near-return force extra \(O\) within bounded depth, or
else start another \(R_\varepsilon\) block?

## Exact statement

**Slogan (REFUTED).** A realizable \((19,12)\) landing cell implies
either a forced extra odd letter within bounded depth, or another
\(R_{0.05}\) fan block.

**Counterexamples (COMPUTATIONALLY VERIFIED).** On the existing
fan-concat windows:

- 12 odd landings in \(n\le 2000\) and 5 on the high-flyers are
  `hug_follow_die`: the next prefix stays on hug and the tail dies
  before length 19. No extra \(O\), no \(R_{0.05}\) block.
- Five of those window holdouts are OOE-legal (image odd), the
  same exact cell type as all five `extra_O` landings, including
  the long overshoot \(n=761\). Witnesses
  \(n=193,539,1119,1121,1459\) continue \(\mathtt{OOE}\) then die.
- The odd-cell key \((\mathrm{OOE},\mathrm{OE},M\bmod 8)\) is mixed
  on both windows. Normalized cell position \(\xi\) of
  hug-follow and extra-\(O\) both cover almost \((0,1)\).

**What remains (REPARAMETERIZATION).** Even landings (27/44) die
immediately: that is `even_preimage_iff`. Among odd landings,
`image_odd` is the parity of \(T(M)\), i.e. letter 2 of the tail.
`extra_O` implies OOE-legal, but OOE-legal does not imply
`extra_O`. Letter 3 is \(T^2(M)\bmod 2\). No surviving arithmetic
class of \((19,12)\) images forces it.

No launch invariant. No infinite fan sequence. Exclusion of
divergent flights is not claimed.

## Current literature

- Post-19 dichotomy and the two long overshoots — **PARK**
  ([juggler_flight_post19_tail.md](juggler_flight_post19_tail.md)).
- Hug-follow after a (19,12) landing exists and dies before 19 —
  **OBSERVATION** (same parent).
- Floor cells — **EXACT — LEAN VERIFIED** (`even_preimage_iff`,
  `odd_preimage_unique`, `preimage_same_next_state`).
- Mechanical-lift \(\xi\)-cocycle — **CLOSE**
  ([juggler_cycle_mechanical_lift.md](juggler_cycle_mechanical_lift.md)).
  Not reopened: \(\xi\) is used only as a bin, and it does not
  separate the launch classes.
- Local cycle attacks — closed; this branch is a launch-cell
  question, not a cycle-fibre contradiction.

Project relationship: **refuted** (the named two-way slogan).

## Branch budget

```text
Mathematical target     does a realizable (19,12) landing cell
                        force extra O within bounded depth, or
                        else start another R_ε block?
Novelty hypothesis      the extra O at letter 3 on the two long
                        tails is a landing-cell constraint, not
                        a global fan fact
Falsifier               an odd (19,12) landing that hug-follows
                        and neither overshoots nor starts R_ε;
                        or every cell label is T-parity
Existing machinery      post-19 kinds, cell_record, ooe/oe
                        legality, even_preimage_iff
Maximum Phase-0 scope   existing 44+8 endpoints only; no new
                        n-window, no xi-cocycle, no Lean, no
                        Paper A
Promotion criterion     a cell class that forces extra O or R_ε
                        and is not T iterated two steps
Stop criterion          slogan false, or labels are archived
                        cells (CLOSE)
```

## Balanced-ternary formulation

None required.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Two-way landing slogan — **REFUTED**
  (`juggler_fan_landing_two_way`).
- `extra_O \(\Rightarrow\) OOE-legal` — **OBSERVATION**, converse
  false.
- \(\xi\) or \(M\bmod 8\) separates hug-follow from extra \(O\) —
  **false**.
- A new cell beyond `even_preimage_iff` / `odd_preimage_unique` —
  not obtained.

## Experiments

- Probe: `research.juggler_sequence.flight_fan_landing`
- Artifact:
  `data/research/juggler/flight_fan_landing/summary.json`
- Tests:
  `tests/research/juggler_sequence/test_flight_fan_landing.py`

Same starts as fan-concat / post-19. No \(n_{\max}\) raise.

## Conjectures

- `juggler_fan_landing_two_way` — **REFUTED**.

## Counterexamples

- Twelve window and five flyer `hug_follow_die` landings.
- Sharp OOE-legal hug-followers \(193,539,1119,1121,1459\)
  (prefix \(\mathtt{OOE}\), then descent before length 19).

## Formalization

None new. Cell labels used for the negative are existing Lean.
No `sorry`. No Paper A edit.

## Results

Classification **LANDING_CELL_NO_LAW**.

- The proposed useful theorem is false on the same witnesses that
  produced the overshoot diagnostic.
- Remaining “cell” information is the parity of \(M\) and of
  \(T(M)\). Letter 3 is not forced by that pair.
- Fan-following is not killed by landing-cell arithmetic on the
  existing images.

## Open questions

- None from landing cells. A new window or a law that is not
  \(T^{\le 2}\) would be a different object; not opened.
- Infinite concatenable fan blocks remain unconstructed and
  unobstructed.

## Decision

**CLOSE.** The slogan is refuted, and every tested landing
invariant is an archived one-step cell or a failed \(\xi\) bin.
That is the stop criterion. Best next question: none from this
door; the fan-follower stays a coherent surviving failure mode,
and the laboratory does not owe it another cell census.

## Publication assessment

Status: `EXPLORATORY`. A refutation record. Not a paper candidate.
No Paper A/B edit. No flight-note rewrite.
