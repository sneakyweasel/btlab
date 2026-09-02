# Juggler macro-event coupling

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
\(Q\)-compression reopen, not a run-length automaton, not a
source-descent replay, not Paper A, and not a claim that every
positive integer reaches 1.

Local episode arithmetic is closed. This phase asks whether the
*sequence* of expansion/reset episodes carries an exact constraint
that no single episode has.

## Problem

Can an infinite `AboveAnchor` orbit realize an arbitrary sequence
of complete expansion/reset episodes, or does one episode restrict
the next by the exact Juggler map?

## Exact statement

The intrinsic episode boundary is the existing maximal-odd-run
block: source \(X\) is an odd-run start, \(r=a(X)\), reset \(R\) is
the first even state, and the landing is \(Q(X)=T^{r+1}(X)\). The
next source is the next odd-run start on the `AboveAnchor` prefix.
The state \(3375\) is interior to the first \(37\)-episode, not a
source.

Phase 0 asks whether any exact pair or triple law

\[
F(X_i,X_{i+1})\le 0,
\qquad
F(X_i,X_{i+1},X_{i+2})\le 0,
\qquad
r_i\ge k\Rightarrow r_{i+1}<k
\]

survives the laboratories \(37,69,89,365,501,1517,6187\) and odd
starts \(n<401\), beyond `EnvelopeState` and the already-known
first-block isolated `OE`.

This is not a halt theorem.

## Current literature

- Induced sources are \(Q\)-landings —
  **REPARAMETERIZATION** / **CLOSE**
  (`juggler_odd_source_return.md`)
- Two-episode descent \(X_{i+2}<X_i\) —
  **REFUTED** (`J-two-episode-source-descent`)
- Episode-source descent —
  **REFUTED** (`J-episode-source-descent`)
- Run-length grammar; long forces short —
  **REFUTED** (`juggler_odd_run_itinerary.md`; \(241=(5,5)\),
  \(293=(8,5)\))
- Consecutive expanding PE blocks —
  **REFUTED** as an impossibility
  (`juggler_two_block_residual.md`; \(365\to763\to1749\))
- \(Q\) has a compressed transition state —
  **PARK** (`juggler_block_map_q.md`)
- Escape-episode rank descent —
  **REFUTED** (`juggler_escape_episode.md`)
- Isolated first \((2,1)\) —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-first-oo-r-bound`)
- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**.
  Totality is not claimed

Project relationship: **reparameterized**. The designated
sequence question after those closes.

## Branch budget

```text
Mathematical target     exact pair/triple / length-coupling
                        law on consecutive Q-episodes
Novelty hypothesis      the episode sequence carries a
                        constraint absent from one episode
Falsifier A             episodes are unconstrained
                        concatenations of local Q-blocks
Falsifier B             every pair/triple relation has CEs
Falsifier C             long can follow long with no
                        structural compensation
Falsifier D             recurrence is only approximate
Falsifier E             the only useful quantity is
                        EnvelopeState
Existing machinery      q_blocks; run_itinerary; source_chain;
                        isolated OE; two-episode refutations
Maximum Phase-0 scope   named starts; odd n<401; no Lean;
                        no automaton
Promotion criterion     a nontrivial R(Sigma_i, Sigma_{i+1})
                        or a two-episode F that is not T<n
Stop criterion          Falsifier A–E; Q reopen; letter census;
                        MacroAutomaton from observations
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- episode = \(Q\)-block —
  **REPARAMETERIZATION** of `q_blocks`
- \(3375\to9317\to2233\) as a source triple —
  **REFUTED**; sources are \(37,9317,2233\)
- \(X_{i+2}<X_i\) —
  **REFUTED** (\(2233>37\); \(365\) climb)
- \(X_i X_{i+2}<X_{i+1}^2\) —
  **REFUTED** (\(89\to155\to291\))
- \(X_{i+2}^2<X_i X_{i+1}\) —
  **REFUTED** (\(37\to9317\to2233\))
- \(X_{i+2}<X_{i+1}\) —
  **REFUTED** (\(89\to155\to291\))
- long forces strictly shorter —
  **REFUTED** (\(241=(5,5)\); \(183=(3,3)\); \(113=(3,5)\))
- extra evens only at the drop —
  **REFUTED** (\(37\) second episode has \(s=2\) while still
  \(\ge 37\))
- exact macro recurrence of \(X\) —
  **REFUTED** on leftovers (already `J-block-map-q-trajectories`)
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.macro_event`
- Records: [juggler_macro_event.md](../research/juggler_macro_event.md),
  [juggler_macro_event.json](../research/juggler_macro_event.json)
- Tests: `tests/research/juggler_sequence/test_macro_event.py`

No CLI. No Lean. No macro automaton.

## Conjectures

None opened.

## Counterexamples

“\(3375\) is an episode source” is false. It lies inside
\(37\xrightarrow{O^4}9317\).

“Every two-episode block descends” is false: \(2233>37\), and
\(365\to763\to1749\to4447\to12707\) is strictly increasing.

“A long episode forces a shorter next episode” is false.
\(241\) realizes \((5,5)\); \(183\) realizes \((3,3)\); \(113\)
realizes \((3,5)\). \(365\) has four consecutive length-\(2\)
episodes. \(1517\) has a later length-\(3\) after a length-\(1\).

“A geometric or bilinear triple law holds on all named sources”
is false. Each tested inequality fails on \(37\), \(89\), or
\(501\).

## Formalization

None added. No `ExpansionEpisode.lean`. No `EpisodeRelation.lean`.
No `MacroAutomaton.lean`. Paper A is unchanged. No `sorry`.

## Results

Classification **MACRO_EVENT_CLOSED**.

The stable episode boundary is the existing \(Q\)-block. Named
run sequences are

| \(n\) | \((r_i)\) | sources |
|------|-----------|---------|
| \(37\) | \(4,3,2\) | \(37,9317,2233\) |
| \(365\) | \(2,2,2,2,1\) | \(365,763,1749,4447,12707\) |
| \(501\) | \(2,3,2,2,2,2,1\) | joins \(365\) at \(763\) |
| \(1517\) | \(2,2,2,1,3\) | \(33811\to2493\) contracts |
| \(6187\) | \(2,3,2,1\) | exits by `OE` |

No tested triple inequality is universal. Odd \(n<401\) has
eleven long-then-long pairs, including growth \(3\to5\). Extra
evens occur mid-orbit. The only exact pair constraint remains
the first-block isolated `OE`, already Lean.

This is Falsifier A, B, C, and E.

## Open questions

None from macro-event coupling. Do not add `ExpansionEpisode`.
Do not build a run-length or source automaton. Do not reopen
\(Q\)-compression or two-episode descent. The leftover hole is
unchanged: a cube cell without a square cell, interior to a
\(Q\)-block.

## Decision

**CLOSE**. The episode sequence is a concatenation of existing
\(Q\)-blocks. Every proposed coupling is already refuted or
fails on the named laboratories. A branch whose statements are
all `KNOWN` or `REPARAMETERIZATION` is a close.

Best next question: none from macro-event coupling.

## Publication assessment

Status: `EXPLORATORY`.

A negative sequence-of-episodes fragment. Not a paper candidate
and not a Juggler totality result.
