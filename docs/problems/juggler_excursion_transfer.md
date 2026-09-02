# Juggler long-excursion transfer

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a reopen of
macro-event coupling, odd-source return, two-episode source descent,
first-return maximality, prefix-cylinder occupancy, or the itinerary
language, not a new atlas language tag, not an automaton, not Paper A,
and not a claim that every positive integer reaches 1.

Those branches already closed letter, episode, and start-set
structure. This phase measures a different object: the numerical
triple \((L_i,H_i,L_{i+1})\) of a complete climb-and-reset, and
whether successive triples obey a hold-out-stable compensation or
envelope that is invisible to `EnvelopeState` and \(Q\)-word
statistics.

## Problem

Can large Juggler excursions be concatenated arbitrarily, or does
the exact integer dynamics impose a stable transfer law between one
complete excursion and the next?

## Exact statement

On an `AboveAnchor` prefix of an odd start \(n\), a **record
excursion** begins at an odd source \(L\), climbs to the block
maximum \(H\), and returns at the first subsequent local minimum
\(L'\) (Return B: the next odd source, the existing \(Q\)-landing
when that landing is odd). Return A is the first state strictly
below \(H\) after the peak and is recorded only as a diagnostic.

Phase 0 asks whether any of

\[
L_{i+2}^{A}<L_i^{B},
\qquad
\frac{H_i}{L_i}\text{ large }\Rightarrow\frac{L_{i+2}}{L_i}\text{ small},
\qquad
L_{i+1}^{a}L_{i+2}^{b}<L_i^{c}
\]

survives a train/hold-out split by starting \(n\), beyond
`EnvelopeState`, the already-refuted \(L_{i+2}<L_i\), and the
already-closed \(Q\)-episode couplings.

Absence under a bound is `NOT OBSERVED WITHIN SEARCH BOUND`.
This is not a halt theorem.

## Current literature

- Induced sources are \(Q\)-landings —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_odd_source_return.md](juggler_odd_source_return.md))
- Two-episode descent \(L_{i+2}<L_i\) —
  **REFUTED** (`J-two-episode-source-descent`;
  \(37\to 9317\to 2233\), \(365\) climb)
- Episode-source descent —
  **REFUTED** (`J-episode-source-descent`)
- Macro-event pair/triple / long-then-long —
  **CLOSE** as `MACRO_EVENT_CLOSED`
  ([juggler_macro_event.md](juggler_macro_event.md))
- First-return maximality —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_first_return_excursions.md](juggler_first_return_excursions.md))
- Nested start-set occupancy —
  **CLOSE** as `ANCHOR_CYLINDER_CLOSED`
- Formal versus AAn itinerary gap —
  **CLOSE** as `FORMAL_REALIZED_GAP_CLOSED`
- Shared formal language is `prefixNoncontracting` —
  **CLOSE** as `PARITY_BALANCE_CLOSED`
- Cube cell without a square cell — a **separate** leftover
- Every start reaches 1 — not claimed

Project relationship: **extended**. The designated numerical
diagnostic after those closes. Do not reopen the refuted
descent statements as hoped-for theorems.

## Branch budget

```text
Mathematical target     On record excursions (L,H,L'), does a
                        hold-out-stable two-step / compensation
                        / weighted inequality exist that is
                        not EnvelopeState and not the already
                        refuted L_{i+2}<L_i?
Novelty hypothesis      The peak H carries inter-episode
                        compensation invisible to Q-word
                        statistics.
Falsifier               Transfer cloud unconstrained; all
                        candidates fail hold-out or labs;
                        every relation is EnvelopeState or a
                        known source-descent counterexample.
Existing machinery      floor_power; q_blocks; source_chain;
                        leftover laboratories; REFUTED
                        J-two-episode-source-descent;
                        MACRO_EVENT_CLOSED
Maximum Phase-0 scope   Odd n plus labs; stream (L,H,L',r);
                        one-step and two-step envelopes;
                        (u,v) extrema; compensation; product;
                        hold-out by start n; near exact L
                        recurrence. No Lean, no ML, no
                        automaton, no CUDA.
Promotion criterion     Hold-out-stable Class B/C/D inequality
                        not equivalent to T^k(n)<n.
Stop criterion          Unconstrained cloud; hold-out failure;
                        only EnvelopeState; already-refuted
                        descent restated; long-then-long free.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Return B equals the next odd \(Q\)-source —
  **REPARAMETERIZATION** of `q_blocks` (`37\to 9317\to 2233`)
- One-step / two-step log envelopes —
  **REPARAMETERIZATION** of the formal scale
  \(3^{r}/2^{r+1}\) (`EnvelopeState` / `power_bound_word`)
- High-peak compensation \(H/L\) large \(\Rightarrow\) later
  source small —
  **REFUTED** at the Phase-0 window (\(37\); \(1.2\cdot 10^6\)
  growth-then-growth pairs)
- Weighted product and bilinear triples —
  **REFUTED** (same first CEs as `MACRO_EVENT_CLOSED`)
- \(L_{i+2}<L_i\) —
  **REFUTED** (`J-two-episode-source-descent`); not reopened
- Exact source recurrence —
  `NOT OBSERVED WITHIN SEARCH BOUND`
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.excursion_transfer`
- Records: [juggler_excursion_transfer.md](../research/juggler_excursion_transfer.md),
  [juggler_excursion_transfer.json](../research/juggler_excursion_transfer.json)
- Dataset: `data/research/juggler/excursion_transfer/`
- Tests: `tests/research/juggler_sequence/test_excursion_transfer.py`

Science window: odd \(n\le 2\cdot 10^7\) plus laboratories
\(37,69,89,365,501,1517,6187,329,33391\). Hold-out split
\(10^7\). Tests use \(n\le 400\). No CLI. No Lean.

## Conjectures

None opened.

## Counterexamples

- “Return B is a new excursion map.” False: it reproduces
  the \(Q\)-source chain on \(37\) and \(365\).
- “\(L_{i+2}<L_i\).” False: \(37\to 9317\to 2233\)
  (`J-two-episode-source-descent`). About \(2.3\cdot 10^6\)
  further CEs in-window.
- “Growth forces the next source down.” False: \(89\to 155\to 291\)
  and the \(365\) climb; \(1.237620\cdot 10^6\) growth-then-growth
  pairs.
- “\(H\ge L^2\) forces \(L_{i+2}<L\).” False at \(37\)
  (\(H=86818724\), \(L_2=2233\)).
- “\(r\ge 4\) forces a shorter next run.” False: first CE
  \(n=193\) with \((r_i,r_{i+1})=(5,4)\); \(150131\) further CEs.
- “A bilinear or cubic product bound holds.” False on \(37\)
  and \(89\), the same witnesses as `MACRO_EVENT_CLOSED`.
- “The log-log envelope exceeds the formal \(r\)-scale.”
  False for every \(r\le 10\) with a sample; \(r=11\) is a
  single floor-lossy point below \(3^{11}/2^{12}\).

## Formalization

None added. Existing `AboveAnchor` and `EnvelopeState` already
contain the identities. No `ExcursionTransfer.lean`. No `sorry`.
Paper A is unchanged.

## Results

Classification **EXCURSION_TRANSFER_CLOSED**.

Science window: odd \(n\le 2\cdot 10^7\) (\(9\,999\,999\)
starts), \(16\,333\,230\) excursions, \(6\,352\,626\)
consecutive pairs, hold-out split \(10^7\)
(`COMPUTATIONALLY VERIFIED` as a bounded observation):

- Return B is the existing \(Q\)-source chain. Return A
  differs on \(5\,130\,806\) blocks (extra evens after the
  peak), including the second \(37\)-episode. The numerical
  sources remain \(37,9317,2233\) and the \(365\) climb.
- Every tested Class A/B/C/D integer inequality has a
  first CE on \(37\), \(89\), \(173\), or \(193\), and
  fails on \(1.5\cdot 10^5\)–\(2.3\cdot 10^6\) pairs.
- Growth can follow growth: \(1\,237\,620\) pairs with
  \(L_{i+1}>L_i\) and \(L_{i+2}>L_{i+1}\).
- The only hold-out-stable envelope is
  \(\sup\log L'/\log L=3^{r}/2^{r+1}\) in each odd-run
  bin \(r\le 10\). That is `EnvelopeState`, not a new
  transfer law. Train/hold-out \(\sup c=28.83\) is the
  \(r=10\) formal scale.
- Exact source recurrence: \(0\)
  (`NOT OBSERVED WITHIN SEARCH BOUND`). Bit-cap aborts:
  \(142\,302\). Horizon misses: \(0\).

This is the unconstrained-concatenation falsifier and the
“only EnvelopeState” falsifier. User PARK labels
“transfer is generic” / “no hold-out-stable relation” /
“current abstractions are complete” are this close.

## Open questions

None from numerical excursion transfer. Do not recensus at
\(10^8\), do not fit a black-box \((u,v)\) classifier, and
do not reopen `J-two-episode-source-descent`. The leftover
residual is still the cube cell without a square cell.

## Decision

**CLOSE**. Record excursions with Return B are the existing
\(Q\)-source chain. The peak \(H\) does not impose a
hold-out-stable compensation, two-step, or weighted law
beyond `EnvelopeState`. Expanding excursions concatenate
freely. Two-episode descent remains the already-refuted
\(37\to 9317\to 2233\). A branch whose statements are all
`KNOWN`, `REPARAMETERIZATION`, or previously `REFUTED` is
a close.

Best next question: none from excursion transfer. The
leftover hole is still a cube cell without a square cell.

## Publication assessment

Status: `EXPLORATORY`. A bounded transfer census, not a paper
candidate and not a Juggler totality result.
