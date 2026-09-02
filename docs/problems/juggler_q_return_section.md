# Juggler Q first-return section

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
Q-descriptor reopen, not first-return-below \(T^{k}(n)<n\), not
Paper A, and not a claim that every positive integer reaches 1.

The parked block-map dossier asked for a global property of an
infinite residual \(Q\)-orbit. This phase tests Poincaré returns
to exact scale sections, not another local invariant of \(Q(x)\).

## Problem

Does any exact scale section \(S_n(\alpha)\) make leftover
\(Q\)-returns structurally simpler than one-step \(Q\)?

## Exact statement

Let \(Q(x)=T^{a(x)+1}(x)\) on odd AboveAnchor landings, as in
[juggler_block_map_q.md](juggler_block_map_q.md). For rationals
\(\alpha=B/A\) write

\[
S_n(\alpha)=\{x:n\le x\text{ and }x^{A}<n^{B}\}.
\]

On the \(Q\)-skeleton of \(n\) (odd starts and their \(Q\)-images),
the first return time \(\tau_S(x)\) is the first later skeleton
point that lies in \(S_n(\alpha)\). Then \(R_S(x)=Q^{\tau_S(x)}(x)\)
in the skeleton sense.

A section is **rejected** when every leftover defined return has
\(\tau_S=1\), or when no leftover has a multi-block return. In
that case \(R_S=Q\).

Phase 0 tests \(\alpha\in\{3/2,2,9/4,8/3,3\}\) on
\(365,501,1517,6187\) and a modest odd window \(n<2001\).

## Current literature

- Maximal odd-run map \(Q\) has no compressed predictor —
  **PARK** (`J-block-map-q-trajectories`, `J-block-map-q-state`)
- Two-episode source descent —
  **REFUTED** (`J-two-episode-source-descent`)
- First-return-below \(T^{k}(n)<n\) —
  a different object (`juggler_excursions`)
- Isolated `OE` contracts \(Q(x)<x\) —
  **EXACT — LEAN VERIFIED** (`oe_block_contracts`); one-step,
  not a section return
- \(R_S(x)<x\) or \(R_S(x)=x\) on leftover \(Q\)-orbits —
  **REFUTED** (`J-q-return-section-descent`)
- Every start reaches 1 — not claimed

Project relationship: **extended**. The designated global
question after \(Q\)-compression PARK.

## Branch budget

```text
Mathematical target     a scale section S_n on which leftover Q
                        first-returns are simpler than one-step Q
Novelty hypothesis      exit-and-reenter returns carry a well-founded
                        relation that one-step Q hides
Falsifier A             every reasonable S has typical return time 1
                        (R_S = Q) or unstructured returns
Falsifier B             repeated returns with no descent and no exact
                        recurrence
Falsifier C             permanent escape with no cumulative constraint
Existing machinery      q_blocks / block_map / a_of; AboveAnchor;
                        leftover controls 365, 501, 1517, 6187
Maximum Phase-0 scope   leftovers + odd n<2001; five exact α; no Lean
Promotion criterion     one section with multi-block returns and a
                        structural Type I split or well-founded order
Stop criterion          R_S collapses to Q; another local invariant;
                        word enumeration; ReturnSection.lean; W_5
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(S_n(9/4)\), \(S_n(8/3)\), \(S_n(3)\) on leftovers —
  rejected (\(\tau_S=1\); \(R_S=Q\))
- \(S_n(2)\) on \(365\) and \(1517\) —
  rejected; on \(501\) the multi-block return
  \(133347\to763\) is Type I after peak \(582916\)
- \(S_n(3/2)\) on \(365\): \(4447\to1196\) is Type I after
  peak \(12707\); the three prior returns are Type plus
- record-low of section visits —
  false on every leftover (the minimum stays the start \(n\))
- exact section recurrence Type II —
  not observed
- permanent section escape Type III —
  not observed on leftovers; \(1517\) leaves \(S_n(3/2)\)
  at \(539470\) and then drops
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.q_return_section`
- Records: [juggler_q_return_section.md](../research/juggler_q_return_section.md),
  [juggler_q_return_section.json](../research/juggler_q_return_section.json)
- Tests: `tests/research/juggler_sequence/test_q_return_section.py`
- Lean: none. No `ReturnSection.lean`. Paper A unchanged.
  No `sorry`.

## Conjectures

None opened.

## Counterexamples

“\(R_S(x)<x\) or \(R_S(x)=x\) on a surviving leftover section”
is false. On \(S_{365}(3/2)\) the returns \(365\to763\to1749\to4447\)
are strictly ascending and not recurrent; only the later excursion
\(4447\to1196\) descends.

“Section record-lows \(m_{k+1}<m_k\) unless periodic” is false.
Every leftover section-visit sequence has first visit \(n\) and
later visits \(>n\).

“\(S_n=[n,n^{2})\) is already a useful leftover section” is
false for \(365\) and \(1517\): every defined return has
\(\tau_S=1\).

## Formalization

No new Lean file. `AboveAnchor`, `oe_block_contracts`, and
`ReturnBelow` are reused as names only. `ReturnBelow` is
first-return-below the start, not a \(Q\)-section return.
Paper A is unchanged. No `sorry`. No halt theorem.

## Results

Classification **Q_RETURN_SECTION_PARK**.

Leftover section verdicts (defined returns only):

- \(\alpha=3/2\): \(15\) defined, \(11\) with \(\tau=1\),
  \(4\) multi-block, Type I \(5\), Type plus \(10\). Survives.
- \(\alpha=2\): \(20\) defined, \(18\) with \(\tau=1\),
  \(2\) multi-block. Survives only because of \(501\) and
  \(6187\). Rejected on \(365\) and \(1517\).
- \(\alpha=9/4,8/3,3\): no leftover multi-block return.
  Rejected.

The multi-block leftover returns that do occur are Type I
(\(4447\to1196\), \(1089\to763\), \(133347\to763\),
\(18425\to11189\), \(15771571\to11189\)). They sit next to
ordinary one-step ascents on the same section. The odd window
\(n<2001\) is the same mixture: on \(S(3/2)\), \(410\) plus
versus \(29\) Type I.

This is Falsifier B, not a shared well-founded return order.
It is not a reparameterization of `ReturnBelow`.

## Open questions

None from leftover Poincaré sections. The subsequent
prefix-balance attack is **CLOSE** in
[juggler_growth_balance.md](juggler_growth_balance.md). Do not
build `ReturnSection.lean`. Do not reopen \(Q\)-descriptors. Do
not open a nested-section hierarchy. Do not reopen W_5.

## Decision

**PARK**. Two thin sections produce genuine exit-and-reenter
returns, so the attack is not empty. Those returns are not
simpler than one-step \(Q\): the same leftover climbs by
one-step plus-returns, then sometimes descends after a high
peak. Record-lows fail. Thick sections collapse to \(Q\).
There is no Type-B lemma to package.

Best next question: none from first-return sections of \(Q\).
The residual is still the integer landing.

## Publication assessment

Status: `EXPLORATORY`.

A section-selection negative: Poincaré \(Q\)-returns do not
supply the missing termination order. Not a paper candidate
and not a Juggler totality result.
