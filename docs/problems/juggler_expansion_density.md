# Juggler expansion density and long-run block compatibility

Status: **STRUCTURAL**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

After two consecutive expanding persistent residual blocks were shown
to exist, how dense can such blocks be along a residual chain? Is
there a finite run bound, or a nontrivial density bound strictly
below 1, that is not the concatenated endpoint inequality?

## Exact statement

Decompose a persistent residual chain into blocks
\(x_i\xrightarrow{w_i}x_{i+1}\). Write
\(E(w)=3^{\#O(w)}-2^{|w|}\) and call a residual block expanding when
\(E(w)>0\).

There is **no** proved finite \(M\) such that every persistent chain
of length \(M\) contains a non-expanding block. There is **no**
useful bound
\(\limsup r/m<1\) when density is taken among persistent residual
steps: on the scanned windows that density is 1.

What is exact:

- \(E(w)>0\) if and only if the itinerary is formally expanding;
- an expanding residual block \(O^a E^b\) (\(b\ge 1\)) satisfies
  \(b<a\) (and already \(a\ge 2\));
- relative slack multiplies under concatenation; the numerator folds
  as \(n^{3^{o(v)+o(w)}}\) on a three-block word;
- the chain
  \(365\xrightarrow{\mathrm{OOE}}763\xrightarrow{\mathrm{OOE}}1749\xrightarrow{\mathrm{OOE}}4447\)
  is a `PersistentExpansionChain`.

## Current literature

- ResidualStep / PersistentOddResidual —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Residuals`.
- Expanding residual \(\Rightarrow a\ge 2\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Scale`.
- Two consecutive expanding persistent blocks impossible —
  **REFUTED** in `docs/problems/juggler_two_block_residual.md`.
- Normalized slack \(1+q\) product —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.NormalizedDefect`.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     How dense can PE residual blocks be? Is there
                        finite M or a density bound <1?
Novelty hypothesis      cumulative slack/surplus across blocks forbids
                        dense expansion
Falsifier               arbitrarily long PE runs; density=1 among
                        persistent; every bound is T<n
Existing machinery      PersistentExpandingResidual, exponentExpanding,
                        1+q concat, residual_excursion
Maximum Phase-0 scope   run-length census; integer grammar; exact slack
                        product; Lean identities or recorded long run;
                        no halt
Promotion criterion     new structural constraint on sequences of PE
                        blocks, or an exact forbidden grammar
Stop criterion          Falsifier A–E; machinery gravity; endpoint
                        rewrite only
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Integer surplus \(E(w)=3^{\#O}-2^{|w|}\) —
  **EXACT — LEAN VERIFIED**
- Expanding residual \(\Rightarrow \#E<\#O\) —
  **EXACT — LEAN VERIFIED**
- Block-growth identity \(n^{3^o}=n^{2^k+E(w)}\) on expanding itineraries —
  **EXACT — LEAN VERIFIED**
- Slack-numerator three-block fold —
  **EXACT — LEAN VERIFIED**
- Certified PE chain of length 3 starting at 365 —
  **EXACT — LEAN VERIFIED**
- Finite \(M\) forbidding \(M\) consecutive PE blocks —
  not proved
- Density of expanding among persistent steps \(\le 1-c\) —
  **REFUTED** as a useful attack (density 1 on the scanned windows)
- Consecutive PE run length bounded by 3 —
  **REFUTED** computationally (\(L=7\) at 11681)

## Experiments

Residual-block census, not a raw trajectory hunt.

- Consecutive PE run length grows with the window: max \(L=3\) on
  \(n\le 4000\), \(L=5\) on \(n\le 8000\), \(L=7\) on
  \(n\le 20000\) and \(n\le 30000\).
- Length-7 starts include 11681, 14237, 15343, 27623. Word types in
  long runs are dominated by `OOE`, `OOOE`, `OOOOE`, `OOOOEE`.
- The certified triple at 365 has length **3**, not 4:
  \(4447\xrightarrow{\mathrm{OOE}}12707\) is expanding (\(E=1\)) but
  not persistent, because 12707 is odd-to-even. Runs also end by
  a later contracting residual.
- Density of expanding among persistent residual steps is 1 on
  odd-odd starts \(n\le 2000\) (and already on \(n\le 200\)). For
  large \(x\), persistence \(y>x\) essentially requires
  \(3^o>2^k\).

Tests: `tests/research/juggler_sequence/test_expansion_density.py`.
Do not default-test the \(n\le 30000\) census.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- No two consecutive PE blocks. Already false; the length-3
  continuation \(1749\xrightarrow{\mathrm{OOE}}4447\) is now
  Lean-certified.
- Consecutive PE runs have length at most 3. False:
  `walk_pe_run(11681)` has length 7.
- Expanding fraction among persistent residual blocks is bounded
  by \(1-c\). False on the scanned windows: the fraction is 1.
- One expanding block forces the next to contract. Already
  **REFUTED** by the two-block branch.

## Formalization

`formal/Problems/Juggler/ExpansionBlocks.lean`, after
`NormalizedDefect` and before `Cycles`. No `sorry`. No halt
theorem. No real logarithms: surplus and slack stay in \(\mathbb{N}\).

## Results

- The integer grammar of one expanding residual block is
  \(a\ge 2\) and \(b<a\). That is the combinatorial cost of one
  expansion, not a sequence obstruction.
- The \(1+q\) product remains the exact multi-block slack law.
  Per-block \(q\) is not monotone.
- A uniform finite \(M\) is not justified: certified \(L=3\),
  computed \(L=7\), and the maximum grew with the search window.
- Density among persistent steps is the wrong coordinate. It
  collapses to persistence itself at large scale.
- A PE run can end without a contracting residual: the next image
  may be odd-to-even, so the sequel is expanding but not
  persistent.

## Open questions

What forces a PE run to end — a later contracting residual versus
an odd-to-even landing — as a finite-state grammar that is not
\(T_w(n)<n\)?

## Decision

**PROMOTE** the integer expanding-block grammar and the certified
length-3 chain. Do not promote a finite-\(M\) theorem or a density
bound strictly below 1. Do not claim termination.

Best next question: what forces a PE run to end (contracting
residual versus odd-to-even landing) without becoming
\(T_w(n)<n\)?

## Publication assessment

Status: `STRUCTURAL`. Exact single-block grammar and a certified
triple. Not a Juggler totality result.
