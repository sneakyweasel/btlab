# Juggler 2-adic / positive-integer bridge

Status: **EXPLORATORY**

Standalone arithmetic layer on the exact Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not an automaton,
and not a claim that every positive integer reaches 1.

## Problem

Is there a structural distinction between finite O/E itineraries that
survive 2-adic residue / valuation constraints and those that are
realized by a positive integer under the exact Juggler map?

## Exact statement

For a finite itinerary \(w\) and precision \(P\ge 1\), `Admissible_P(w)` is
the existing residue-class predicate: the first letter is \(n\bmod 2\),
and later letters are `INCONCLUSIVE` once a cylinder splits.
`IntReal(w)` is \(\exists n>0,\ \operatorname{follows}(n,w)\). Phase 0
asks whether the two predicates differ by anything other than witness
scale, and whether a finite balanced-ternary jet constrains the 2-adic
class. This says nothing about totality.

## Current literature

- `follows` / `floorPower` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Itinerary`.
- `even_tower_to_one` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Collapse`.
- Odd-odd remainder \(\rho\equiv y-1\pmod 8\) —
  **EXACT — LEAN VERIFIED**; landing valuation **CLOSE** as
  `LANDING_VALUATION_IS_Y_MOD_8`.
- Collatz valuation cylinders / Layer C —
  a different map; not imported.
- Word language / PE-factor —
  **CLOSE**. Do not reopen.
- Residual future-quotient / information complexity —
  **CLOSE**. Sample-relative \(k^*_2\) is not `Admissible_P`.
- Realization geometry —
  **CLOSE**. First holes `EEEEEE` / `EEEEOE` / `EEEOEO` are
  `SCALE_LIMITED`.
- Prefix-NC admissibility / preimage cylinders / backward geometry /
  accelerated odd-to-odd —
  **CLOSE**.

Project relationship: **extended**. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     For finite Juggler O/E words, is Admissible_P
                        a strictly weaker predicate than IntReal, and
                        does a finite BT jet constrain the 2-adic class?
Novelty hypothesis      A Type-3 integer obstruction, a BT↔2-adic
                        constraint, or an exact P(w) vs m(w) lift bound
Falsifier               Only the first letter is 2-adically forced;
                        every A_P\\I gap is SCALE_LIMITED or bound-
                        limited; BT jets and 2-adic residues are
                        CRT-transverse
Existing machinery      follows_itinerary, floor_power, landing_valuation,
                        even_tower_to_one, integer_jet / encode / lsd,
                        SCALE_LIMITED hole certificates
Maximum Phase-0 scope   k<=12, P<=16, n<=4000; constructive cylinder
                        splits; selected-word lifting; BT jet tables
Promotion criterion     Type-3 certificate, exact BT constraint on
                        admissibility, or explicit lifting bound
Stop criterion          Gaps are Type 1; BT and 2-adic remain
                        transverse; Admissible_P is first-letter only
```

## Balanced-ternary formulation

\(J_k(n)\) is the length-\(k\) integer jet. A 2-adic cylinder is
\(n\equiv r\pmod{2^P}\). Their intersection is the CRT class modulo
\(2^P 3^k\).

## Why BT may be relevant

The map mixes parity (powers of 2) with floor powers that see the
factor 3. BT is the laboratory coordinate for powers of 3. Relevance is
a question, not a claim that BT solves Juggler.

## Candidate operations / invariants

- First letter is \(n\bmod 2\) —
  **EXACT — HUMAN PROOF**
- Even 2-adic cylinders split at letter 2 —
  **EXACT — HUMAN PROOF**
- Odd 2-adic cylinders split at letter 2 for \(P\le 16\) —
  **COMPUTATIONALLY VERIFIED**
- Finite BT jet determines the first letter —
  **REFUTED** (\(n=1,4\))
- CRT intersection empty —
  **REFUTED**
- Type-3 obstruction for the first holes —
  **REFUTED**; they are `SCALE_LIMITED`
- `ADMISSIBILITY_REALIZATION_GREEN` —
  **REFUTED** as a Phase-0 promotion
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.two_adic_bridge`
- Records: [juggler_2adic_integer_bridge.md](../research/juggler_2adic_integer_bridge.md),
  [juggler_2adic_integer_bridge.json](../research/juggler_2adic_integer_bridge.json)
- Tests: `tests/research/juggler_sequence/test_two_adic_bridge.py`

No GPU. No atlas recensus. No new Lean file. The Research Engine
control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- “A finite 2-adic cylinder forces the second Juggler letter”: every
  residue at \(P\le 16\) splits.
- “Same BT 1-jet implies the same first letter”: \(1\) and \(4\).
- “`EEEEEE` is 2-adically forbidden”: it is weakly admissible and
  realized at \(2^{32}\).
- “Absence in \(n\le 4000\) is Type 3”: the first holes have
  `SCALE_LIMITED` witnesses.

## Formalization

None added. Existing lemmas in `Itinerary`, `Collapse`,
`LandingValuation`, and `Cells` stay as they are. No `sorry`.

## Results

Classification **BRIDGE_COMPLEX**.

Every tested 2-adic cylinder splits at the second Juggler letter. Weak Admissible_P is first-letter survival and therefore contains every finite itinerary. Every Phase-0 gap is Type 1 or INTEGER-WITNESS-ABSENT-WITHIN-BOUND. Finite BT jets are CRT-transverse to 2-adic residues and do not determine the first letter. No Type-3 integer obstruction and no lifting bound survived.

## Open questions

None from this branch. Do not invent another coordinate system. Do not
return to residual quotients or information-complexity.

## Decision

**CLOSE**. Every tested 2-adic cylinder splits at the second Juggler letter. Weak Admissible_P is first-letter survival and therefore contains every finite itinerary. Every Phase-0 gap is Type 1 or INTEGER-WITNESS-ABSENT-WITHIN-BOUND. Finite BT jets are CRT-transverse to 2-adic residues and do not determine the first letter. No Type-3 integer obstruction and no lifting bound survived. Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A negative bridge census and two elementary
exact facts (even-cylinder split; CRT transversality), not a paper
candidate and not a Juggler totality result.
