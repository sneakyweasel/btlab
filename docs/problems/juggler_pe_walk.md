# Juggler PE-block walk

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not an
`OE`-contracts reopen, not empty-cell dynamics, not episode-rank,
not Paper A, and not a claim that every positive integer reaches 1.

After empty-odd-preimage PARK, the leftover residual is an odd-landing
PE walk. This phase asks whether repeated residual blocks
\(O^a E\) move a forward predictive anchor-relative quantity.

## Problem

Does repeated PE recovery have a systematic effect on the
anchor-relative state, even when individual PE blocks do not fall
below the original \(n\)?

## Exact statement

Write \(Q(x)=T_{O^{a(x)}E}(x)\) for the next residual block from an
odd state, and \(Q(x)=T_E(x)\) from an even state. On a leftover
`AboveAnchor` start \(n\), let \(m_k\) be the successive landings.
Decide whether one of

- \(m_k/n\),
- the square remainder \((y_k-m_k^2)/(2m_k+1)\),
- the inherited envelope \(\alpha=3^{\#O}/2^{|w|}\)

is monotone, or predicts the next block type. Isolated
\(P(x)=T_{OE}(x)\) is used only when `OE` follows; it is not
re-tested as a halt mechanism.

## Current literature

- `oe_block_contracts` / `repeated_oe_scale` —
  **EXACT — LEAN VERIFIED**. Not a halt theorem.
- Isolated-`OE` survival \(r\le R(a_0)\) —
  **EXACT — LEAN VERIFIED**
- Two consecutive expanding `OOE` blocks —
  **REFUTED** as impossible (`365\to763\to1749`)
- Expanding-grammar bound on PE runs —
  **REFUTED**
- Episode-rank descent / exact recurrence —
  **REFUTED** (`J-escape-episode-dichotomy`)
- Empty-cell forward law —
  **REFUTED** (`J-empty-odd-pe-forward`)
- `OE` contracts \(\Rightarrow\) termination — already false
  globally; not reopened
- Every start reaches 1 — not claimed

Project relationship: **extended**. The leftover is rewritten as a
PE-block walk; the proposed predictors are new relative to
episode-rank and emptiness.

## Branch budget

```text
Mathematical target     repeated PE recovery moves a forward
                        predictive anchor-relative quantity
Novelty hypothesis      landing/n, remainder, or envelope
                        predicts the next PE landing
Falsifier               same envelope, different next block;
                        no monotone scalar
Existing machinery      oe_block_contracts; power_bound_word;
                        AboveAnchor; leftover controls
Maximum Phase-0 scope   O^a E walk on 365/501/1517/6187;
                        no new Lean
Promotion criterion     a forward predictive PE invariant
Stop criterion          no predictive quantity; OE-census;
                        empty-cell reopen; higher power cells
```

## Balanced-ternary formulation

Optional coordinate on PE landings. No forced BT law appeared.

## Why BT may be relevant

A sparse lsd description of the \(365\) versus \(1517\) split after
the same envelope would have been a BT observation. The split is
the next parity of the landing, not a ternary digit.

## Candidate operations / invariants

- leftover residual is an \(O^a E\) walk —
  **COMPUTATIONALLY VERIFIED**
- \(m_k/n\) is a Lyapunov —
  **REFUTED**
- square remainder is a Lyapunov —
  **REFUTED**
- inherited \(\alpha\) predicts the next block —
  **REFUTED** (`365` and `1517` share \(729/512\))
- `OE` may decrease the state and stay \(\ge n\) —
  **COMPUTATIONALLY VERIFIED** (`33811\to2493`)
- `oe_block_contracts` —
  **EXACT — LEAN VERIFIED**. Already known; not a halt law
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.pe_walk`
- Records: [juggler_pe_walk.md](../research/juggler_pe_walk.md),
  [juggler_pe_walk.json](../research/juggler_pe_walk.json)
- Tests: `tests/research/juggler_sequence/test_pe_walk.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

Ordinary terminating leftovers, not `MinimalNonTerm` witnesses.

- “landing/\(n\) climbs until drop” — `1517` has
  `33811\to2493` still above `1517`.
- “envelope predicts the next PE type” — after three `OOE`,
  both `365` and `1517` have \(\alpha=729/512\); `365` continues
  `OOE` to `12707`, `1517` takes `OE` to `2493`.
- “`OE` recovery falls below \(n\)” — `2493>1517`.
- `6187` ends by `OE` below \(n\); that is an itinerary exit, not a
  closure law (`501` follows the same early \(L\) and continues).

## Formalization

No new Lean module. `oe_block_contracts` and `power_bound_word`
stay in place. Not imported by `Problems.JugglerPaper`. No
`sorry`. No `PEWalk` API. No `juggler_reaches_one`.

## Results

Classification **PE_WALK_PARK**.

The leftover corridor is an \(O^a E\) walk. Repeated expanding
blocks can raise the landing (`365`: `763,1749,4447,12707`). A
later `OE` can lower the state without crossing \(n\). The
inherited envelope is not predictive: the same \(\alpha=729/512\)
has two different next blocks. Square remainders are not
monotone. Isolated `OE` contraction versus the current state is
already Lean and does not imply contraction versus the anchor.

## Open questions

Stop manufacturing scalars on this walk. The remaining object is
the next parity after an expanding PE landing, which is the
existing leftover residual, not a new PE calculus.

## Decision

**PARK**. The PE-walk formulation is the right residual language,
but none of the proposed forward predictors works. Same envelope,
different next block is decisive. This is not `OE`-contracts, not
empty-cell, and not episode-rank.

Best next question: none from these PE scalars. The leftover is
still an odd-landing \(O^a E\) walk whose next letter is not
determined by \(\alpha\).

## Publication assessment

Status: `EXPLORATORY`. A negative predictor fragment on four
finite-escape controls, not a paper candidate and not a Juggler
totality result.
