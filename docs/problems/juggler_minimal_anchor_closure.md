# Juggler minimal-anchor closure for the leftover odd-escape corridor

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
`PredClosure`-from-`{1}` reopen, not Paper A, and not a claim that
every positive integer reaches 1.

After shared `AboveAnchor` obstructions, the remaining termination
class is an unbounded odd-landing escape corridor. This phase asks
whether a minimal nonterminating anchor can support that corridor
without generating a strictly smaller bad start, or without falling
into a short structured predecessor of the known-good interval.

## Problem

Does the leftover odd-escape episode of a minimal-bad-looking start
encode a smaller instance of the same nontermination problem, or a
short structured return into `[1, n-1]`?

## Exact statement

Let \(G = \{ m : \text{the orbit of } m \text{ reaches } 1 \}\). For a
least \(n_\ast > 1\) outside \(G\),

\[
[1, n_\ast-1] \subseteq G
\qquad\text{and}\qquad
\forall k,\quad T^k(n_\ast) \ge n_\ast.
\]

The second display is the shared `AboveAnchor` hypothesis. Decide
whether the first obstruction-free escape episode of a leftover
control forces one of

- Route A: a strictly smaller start with the same bad behaviour,
- Route B: membership of a high corridor state in
  \(\operatorname{Pred}_w([1, n-1])\) for
  \(w \in \{E, OE, OOE, OOOE\}\).

Do not demand that every high integer is good. Do not reopen
predecessor closure from \(\{1\}\).

## Current literature

- `AboveAnchor` shared by `CycleMin` and `MinimalNonTerm` —
  **EXACT — LEAN VERIFIED** (`J-above-anchor`).
- `PredClosure \leftrightarrow ReachesOne` —
  **EXACT — LEAN VERIFIED**. **REPARAMETERIZATION**. Closed as
  `juggler_minimal_counterexample`.
- “A visit \(\ge n_\ast\) is automatically good” —
  **REFUTED** in that same dossier.
- Isolated-`OE` survival and the `OOEOOE` even trap —
  **EXACT — LEAN VERIFIED**.
- Uniform later contractor after even-\(y\) overshoot —
  **REFUTED** (`juggler_overshoot_return`).
- Leftover odd-landing corridors remain after the shared layer —
  **OBSERVATION** (`juggler_minimum_relative`).
- Every start reaches 1 — not claimed.

Project relationship: **independent** as a minimality-propagation
question on the leftover corridor; the generic closure experiment is
already archived.

## Branch budget

```text
Mathematical target     leftover odd-escape episode of a
                        minimal-bad-looking control encodes a
                        smaller start or Pred_{E,OE,OOE,OOOE}(G)
Novelty hypothesis      unique to a minimal anchor, or inherited
Falsifier               no smaller analogue; no short return;
                        rank is not a potential
Existing machinery      AboveAnchor; ReturnBelow; PredEven/PredOdd;
                        PredClosure <-> ReachesOne (CLOSED);
                        odd_preimage_unique; even_below_anchor_pow
Maximum Phase-0 scope   365, 501, 1517, 6187; 69/89 contrast; no new Lean
Promotion criterion     exact smaller-bad descent, or good-interval
                        closure that is not ReachesOne restated
Stop criterion          minimality = AboveAnchor; no smaller
                        structured predecessor; short Pred stalls;
                        exponent/cell census; PredClosure reopen
```

## Balanced-ternary formulation

Optional coordinate on the unique odd spine. No forced BT law
appeared.

## Why BT may be relevant

A sparse lsd cylinder of leftover generators, or a balanced-ternary
description of empty odd cells at PE landings, would have been a BT
observation. Neither is required for the Phase-0 verdict.

## Candidate operations / invariants

- `AboveAnchor` on the realized prefix —
  **EXACT — LEAN VERIFIED**
- `x \in \operatorname{Pred}_w([1,n-1])` iff `ReturnBelow` —
  **EXACT — LEAN VERIFIED**. Already the FiniteProgress bridge
- unique odd predecessor of \(T(n)\) is \(n\) —
  **EXACT — LEAN VERIFIED** (`odd_preimage_unique`)
- leftover first overshoot has only `OE`, and `OE` stays above \(n\) —
  **COMPUTATIONALLY VERIFIED**
- leftover high corridor has no odd predecessor \(< n\) —
  **COMPUTATIONALLY VERIFIED**
- `501` merges into the orbit of `365` at `763` —
  **COMPUTATIONALLY VERIFIED**
- `6187` exits by `OE` from the \(L\)-image `11189` —
  **COMPUTATIONALLY VERIFIED**
- corridor rank is a well-founded potential —
  **REFUTED**
- first overshoot of `365`/`1517` lies in
  \(\operatorname{Pred}_{E,OE,OOE,OOOE}([1,n-1])\) —
  **REFUTED**
- every leftover corridor inherits a smaller same-word start —
  **REFUTED**
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.minimal_anchor_closure`
- Records: [juggler_minimal_anchor_closure.md](../research/juggler_minimal_anchor_closure.md),
  [juggler_minimal_anchor_closure.json](../research/juggler_minimal_anchor_closure.json)
- Tests: `tests/research/juggler_sequence/test_minimal_anchor_closure.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

Ordinary terminating leftovers, not `MinimalNonTerm` witnesses.

- “first overshoot returns under `E`/`OE`/`OOE`/`OOOE`” — `OE` from
  \(T(365)=6973\) lands at `763 > 365`; the same stay holds at
  `501`, `1517`, `6187`.
- “every leftover corridor is inherited” — `365` and `1517`
  have no smaller high-orbit merge and no smaller same-word start.
- “corridor rank decreases through a reset” — `365` resets
  `582276 \to 763` (rank `3 \to 2`) and later reaches rank `4`.
- `501` is the inheritance control, not a counterexample to
  uniqueness: it hits `763 = T^3(365)` while still above `501`.
- `6187` is not an unbounded leftover: after \(L\) it takes `OE`
  from `11189` to `1087 < 6187`. That is a named-word exit, not
  a general closure operator (`501` follows \(L\) to `763` and
  continues).

## Formalization

No new Lean module. `Good` / `Bad` / `PredClosure` stay in
`MinimalClosure.lean`. `AboveAnchor` and the ReturnBelow bridge stay
in `MinimumRelative.lean`. Not imported by
`Problems.JugglerPaper`. No `sorry`. No `EscapeEpisode` API. No
`juggler_reaches_one`.

Route B as “high state in `Pred^*(G)`” is the existing ReturnBelow
bridge, not a new induction.

## Results

Classification **MINIMAL_ANCHOR_PARK**.

The leftover corridor is a unique odd spine. The first overshoot has
odd-cell predecessor \(n\) only. Subsequent PE landings often have
empty odd cells, so there is no backward odd branch to a smaller
start. On `365` and `1517`, short structured words from the
obstruction-free corridor do not meet `[1, n-1]`. Corridor rank
oscillates. `501` inherits `365`. `6187` exits by `OE` from its
\(L\)-image; that is a finite named-word drop, not a closure law.
`69` remains the shared even `OOEOOE` trap. Minimality therefore
adds no information beyond `AboveAnchor` on the remaining corridor.

## Open questions

What arithmetic feature of an empty-odd-preimage PE landing, if any,
could force a later even-below-square without a minimality argument?
Do not reopen interval closure. Do not build a residue automaton.

## Decision

**PARK**. The proposed termination-by-minimality attack fails on the
remaining leftover generators `365` and `1517`: no smaller structured
predecessor, no short good-set closure at the first escape layer, and
no well-founded corridor rank. `6187` drops by `OE` after \(L\), which
is an itinerary exit rather than a minimality descent. The one inheritance
example (`501 \to 365`) is a larger start merging into a smaller
*good* orbit, which is the already-known implication “hit a good
state \(\Rightarrow\) good”. That does not produce a smaller *bad*
anchor.

Best next question: the leftover generator is a unique odd spine
into empty-odd-preimage PE landings — is there a Diophantine constraint
on those landings that is not another word/scale census?

## Publication assessment

Status: `EXPLORATORY`. A negative minimality-propagation fragment on
four finite-escape controls, not a paper candidate and not a Juggler
totality result.
