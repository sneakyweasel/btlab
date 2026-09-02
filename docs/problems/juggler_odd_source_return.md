# Juggler induced odd-source return

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a W_5
reopen, not an \(n^{6}\) census, not Paper A, and not a claim that
every positive integer reaches 1.

Scalar source descent and postponed source-relative reset are
already **REFUTED**. This phase asks whether successive *induced*
odd expansion sources carry an exact pair or triple relation.

## Problem

Can the induced odd-source dynamics support an infinite
`AboveAnchor` orbit, or must every sufficiently long chain
descend, recur, or enter a previously controlled class?

## Exact statement

On an `AboveAnchor` prefix of \(n\), an **odd expansion source**
is the start of a maximal odd run. After that run and its closing
even step the landing is the existing block map \(Q\). The next
source is the next odd run start; if \(Q(x)\) is odd and
\(\ge n\), that landing is the next source.

Phase 0 asks whether

\[
x_{i+2}<x_i
\]

holds for every two-episode block, or whether some other exact
relation \(\Phi(x_i,x_{i+1},x_{i+2})\) survives the laboratories
\(37,69,89,365,501,1517,6187\).

Do not assume \(x_{i+1}<x_i\). Do not introduce a new scalar
Lyapunov function. Do not prove totality.

## Current literature

- Maximal odd-run block map \(Q\) —
  **PARK** (`J-block-map-q-trajectories`); no compressed predictor
- \(Q(x)>x\) forces later contraction below \(x\) —
  **REFUTED** in the \(Q\) dossier
- Episode-source descent on cube-interior states —
  **REFUTED** (`J-episode-source-descent`)
- Induced source map is new —
  **REPARAMETERIZATION** of \(Q\)
- Two-episode descent \(x_{i+2}<x_i\) —
  **REFUTED** (`J-two-episode-source-descent`)
- Every start reaches 1 — not claimed

Project relationship: **extended**. One semantic identification
of sources, then a two-episode test. Not a new map.

## Branch budget

```text
Mathematical target     exact pair/triple law on induced
                        odd-run sources
Novelty hypothesis      two-episode descent, or a Phi that
                        is not generic Q-growth
Falsifier               3375 is not a source; x_{i+2}<x_i
                        fails; Phi fails like Q-pairs
Existing machinery      q_blocks; Q; AboveAnchor; 37 / leftovers
Maximum Phase-0 scope   define sources; 37/365/321 triples;
                        no new Lean; no source automaton
Promotion criterion     well-founded two-episode relation
                        or a finite exact transition type
Stop criterion          Q-reopen; only correlations; W_5
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- induced sources are odd-run starts; next source is \(Q\)
  when \(Q\) is odd —
  **REPARAMETERIZATION**
- \(3375\) is interior to the \(37\)-episode, not a source —
  **COMPUTATIONALLY VERIFIED**
- leftover cube-odd states are likewise interior —
  **COMPUTATIONALLY VERIFIED**
- \(37\to9317\to2233\) and \(365\to763\to1749\) violate
  \(x_{i+2}<x_i\) —
  **COMPUTATIONALLY VERIFIED**
- cube-odd two-episode descent —
  false (\(n=321\), \(225539\to5958969\to520655\))
- \(x_i x_{i+2}<x_{i+1}^{2}\) —
  false on the \(n<400\) window
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_source_return`
- Records: [juggler_odd_source_return.md](../research/juggler_odd_source_return.md),
  [juggler_odd_source_return.json](../research/juggler_odd_source_return.json)
- Tests: `tests/research/juggler_sequence/test_odd_source_return.py`
- Lean: none new. `q_blocks` is reused. Paper A unchanged.
  No `sorry`.

## Conjectures

None opened.

## Counterexamples

“\(3375\to9317\to2233\) is an induced-source triple” is false.
The sources of \(n=37\) are \(37,9317,2233\). The state \(3375\)
lies inside the first odd run.

“Every two-episode block has \(x_{i+2}<x_i\)” is false:
\(2233>37\), and on \(365\) every consecutive triple ascends
(\(365\to763\to1749\to4447\to12707\)). A cube-odd triple also
fails: \(n=321\), \(520655>225539\).

## Formalization

No new Lean file and no `NextOddSource` primitive. The induced
map is the existing \(Q\)-landing sequence. Paper A is unchanged.
No `sorry`. No halt theorem.

## Results

Classification **ODD_SOURCE_RETURN_CLOSED**.

Once sources are defined as maximal odd-run starts, the induced
map is the parked block map \(Q\). The motivating \(37\) triple
used an interior cube-odd state. Two-episode descent fails on
the true source chain and on the leftover \(365\) climb. No
exact pair or triple inequality survived that is not generic
Juggler growth.

This is not a halt theorem and not a new source calculus.

## Open questions

None from induced-source relations. Do not build a source
automaton. Do not reopen the \(Q\)-compression attack. Do not
reopen W_5.

## Decision

**CLOSE**. The preferred two-episode well-founded relation is
false. The induced object is a reparameterization of \(Q\),
already parked as having no exact compressed transition law.

Best next question: none from induced sources. The leftover is
still an odd-to-odd cube lift interior to a \(Q\)-block. The
sequence-of-episodes restatement is closed in
[juggler_macro_event.md](juggler_macro_event.md).

## Publication assessment

Status: `EXPLORATORY`.

A semantic correction plus a two-episode refutation. Not a
paper candidate and not a Juggler totality result.
