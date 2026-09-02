# Juggler maximal odd-run itinerary

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a residue
automaton, not empty-cell dynamics, not Paper A, and not a claim
that every positive integer reaches 1.

After PE-scalar PARK, the leftover is an `AboveAnchor` walk of
maximal odd runs. This phase asks whether the symbolic itinerary
\((a_i)\) has exact transition constraints beyond the known
isolated-`OE` bound.

## Problem

What sequences of maximal odd-run lengths are compatible with an
`AboveAnchor` trajectory, and can any such sequence be infinite
without descent below the anchor or exact arithmetic return?

## Exact statement

For odd \(x\), let \(a(x)\) be the length of the next maximal odd
run and \(Q(x)=T_{O^{a(x)}E}(x)\). On leftover controls and on odd
starts \(n<2001\), form pairs \((a_i,a_{i+1})\) while the orbit
stays \(\ge n\). Decide whether some pairs are forbidden, whether
a long run forces a short successor, and whether
\(\Lambda=\prod 3^{a_i}/2^{a_i+1}\) predicts drop. Isolated
\(a_0=2\Rightarrow r=0\) is already Lean and is not restated as a
new grammar.

## Current literature

- Isolated-`OE` survival \(R(2)=0\) —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-first-oo-r-bound`)
- `OOE` then `OE` from the start is `FiniteProgress` —
  **EXACT — LEAN VERIFIED**
- Same envelope \(729/512\), different next block —
  **COMPUTATIONALLY VERIFIED** (`J-pe-walk-predictors`)
- Expanding PE grammar / finite run bound —
  **REFUTED**
- Empty-cell forward law —
  **REFUTED**
- Every start reaches 1 — not claimed

Project relationship: **extended**. The PE walk is rewritten as a
run-length itinerary; the isolated-`OE` bound is the only known
exact pair constraint.

## Branch budget

```text
Mathematical target     exact (a,b) constraints under
                        AboveAnchor, beyond isolated OE
Novelty hypothesis      some later transitions are forbidden,
                        or a long run forces a short next run
Falsifier               T as free as parity; same a-prefix
                        splits; burst tradeoff fails
Existing machinery      isolated-OE r-bound; ooe_oe FP;
                        pe_blocks; leftover controls
Maximum Phase-0 scope   leftovers + odd n<2001; no automaton
Promotion criterion     a later forbidden pair or a run-balance law
Stop criterion          unrestricted T; itinerary census; modulus split
```

## Balanced-ternary formulation

Optional coordinate on run-length words. No forced BT law
appeared.

## Why BT may be relevant

A sparse lsd description of the \(365\) versus \(1517\) split after
\((2,2,2)\) would have been a BT observation. The split is the
next parity of the landing.

## Candidate operations / invariants

- leftover itineraries
  \(365=(2,2,2,2,1)\), \(1517=(2,2,2,1,3)\) —
  **COMPUTATIONALLY VERIFIED**
- first \((2,1)\) cannot stay `AboveAnchor` —
  **EXACT — LEAN VERIFIED** (isolated \(r=0\));
  **COMPUTATIONALLY VERIFIED** on \(n<2001\)
- later \((2,1)\) can stay —
  **COMPUTATIONALLY VERIFIED** (`12707\to1196` on `365`)
- long run forces short successor —
  **REFUTED** (`241` has \((5,5)\); `173` has \((8,2)\))
- \(\Lambda\) predicts drop —
  **REFUTED** (`365` drops with \(\Lambda>1\))
- run-length graph is a grammar —
  **REFUTED**
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_run_itinerary`
- Records: [juggler_odd_run_itinerary.md](../research/juggler_odd_run_itinerary.md),
  [juggler_odd_run_itinerary.json](../research/juggler_odd_run_itinerary.json)
- Tests: `tests/research/juggler_sequence/test_odd_run_itinerary.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

Ordinary terminating orbits, not `MinimalNonTerm` witnesses.

- “\((2,1)\) is always FiniteProgress” — later on `365`,
  `12707\xrightarrow{\mathrm{OE}}1196\ge365`.
- “long run forces short next run” — `241` realizes \((5,5)\);
  `293` realizes \((8,5)\).
- “the itinerary \((2,2,2)\) determines the next run” — `365`
  continues \(2\), `1517` continues \(1\).
- “\(\Lambda>1\) forbids drop” — `365` has
  \(\Lambda=19683/16384>1\) and then drops by a trailing `E`.

## Formalization

No new Lean module. Isolated-`OE` and `finiteProgress_of_ooe_oe`
stay in `FirstInternalOO.lean`. Not imported by
`Problems.JugglerPaper`. No `sorry`. No `RunItinerary` API. No
`juggler_reaches_one`.

## Results

Classification **ODD_RUN_ITINERARY_PARK**.

The only exact forbidden pair is the known first-block isolated
`OE`: after \(O^2E\) from the anchor, a following `OE` cannot stay
\(\ge n\). Later pairs, including \((2,1)\), \((1,3)\), \((5,5)\),
and \((8,2)\), occur on ordinary `AboveAnchor` prefixes. The
transition set on \(n<2001\) is broad. The same prefix \((2,2,2)\)
does not determine \(a_3\). \(\Lambda\) is an envelope heuristic,
not a drop law. Run length is still too coarse: the next \(a\) is
the next landing's parity itinerary.

## Open questions

Stop. Do not build a run-length automaton. The next letter is the
arithmetic state of the landing, not a function of \((a_i)\).

## Decision

**PARK**. Falsifiers A, B, and D hold. No later forbidden
transition appeared. The isolated-`OE` pair is already Lean and is
not a grammar on the whole itinerary. Do not reopen residues to
split \(365\) from \(1517\).

Best next question: none from run-length pairs. The leftover next
letter is still the landing's forward parity, which is the
existing residual. Consecutive-episode length coupling is closed
in [juggler_macro_event.md](juggler_macro_event.md).

## Publication assessment

Status: `EXPLORATORY`. A negative itinerary-grammar fragment, not
a paper candidate and not a Juggler totality result.
