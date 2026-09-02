# Juggler Halbeisen-style cyclic word functional

Status: **ARCHIVED**

Refinement of
[juggler_cycle_word.md](juggler_cycle_word.md),
[juggler_expansion_slack.md](juggler_expansion_slack.md), and
[juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md),
not a new paper. It asks whether the unfolded slack-weight vector
of a cyclic word plays the role of the Collatz functional
\(\varphi(s)\) and yields a closure inequality beyond \((L,o)\),
`lowerDenom`, or run-type finance.
Not a halt theorem, not a leftover-itinerary census, not a new finance
identity, not Fourier, not a \(Q\)-return, and not a residue /
\(p\)-adic system.

## Problem

After pair-level closure, finance-conditioned closure, and ordered
block maps all reduced to the exponent envelope, is there a
compressed functional of the *ordered cyclic word* that survives
the floor-power recursion and gives a sharp closure inequality?

## Exact statement

Unfold the exact \(1+q\) one-step laws. For a realized itinerary \(w\),

\[
\alpha_i(w)=2^i\,3^{\#O(w[i+1:])},\qquad
S(w)=\sum_i\alpha_i(w),
\]

and

\[
\frac{n^{3^{\#O(w)}}}{T_w(n)^{2^{|w|}}}
=
\prod_i\bigl(1+\eta_i\bigr)^{\alpha_i(w)}.
\]

The universal cell bound \(1+\eta<4\) then gives

\[
\mathrm{lowerDenom}(w)=4^{S(w)}.
\]

On a `CycleItinerary`, \(T_w(n)=n\), so \(n^{3^o-2^L}\le 4^{S(w)}\).
This is the existing size bound `cycle_pow_le_lowerDenom`.

Same \((L,o)\) need not give the same \(\alpha\) or \(S\):
\(\mathtt{OE}\) has \(S=3\), \(\mathtt{EO}\) has \(S=5\). Those two
words are cyclic shifts, and \(\min_\sigma S\) is a necklace
invariant. Every word that starts \(\mathtt{OO}\) with a fixed
\((L,o)\) shares the leading weights
\((3^{o-1},\,2\cdot 3^{o-2})\). Halbeisen-style
\(M_{L,o}=\max_w\min_\sigma S(w)\) therefore does not produce a
bound on the `CycleMin` start that `lowerDenom` of that orientation
does not already give.

No cycle of any length — not claimed.

## Current literature

- Weighted slack cocycle / \(1+q\) concatenation —
  **REPARAMETERIZATION**
  (`J-weighted-slack-cocycle`;
  [juggler_expansion_slack.md](juggler_expansion_slack.md))
- `lowerDenom` is order-sensitive —
  **EXACT — LEAN VERIFIED** (definitional) /
  **OBSERVATION**
  ([juggler_uniform_thresholds.md](juggler_uniform_thresholds.md))
- Cycle size bound \(n^{3^o-2^L}\le D_w\) —
  **EXACT — LEAN VERIFIED**
  ([juggler_cycle_word.md](juggler_cycle_word.md))
- Pair-level and ordered-block closure —
  **CLOSE**
  ([juggler_cycle_closure.md](juggler_cycle_closure.md),
  [juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Run-type finance, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- Halbeisen–Hungerbühler \(\varphi(s)\) and cyclic-shift optimum
  \(M_{l,n}\) —
  **known** (`halbeisen-hungerbuehler-1997-collatz-cycles`)
- Hercher local-minima count \(m\ge 92\) —
  **known** (`hercher-2023-collatz-m-cycles`);
  the Juggler analogue is the valley count \(e\) already used in
  run-type packing
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new closure obstruction;
the weight vector is a **REPARAMETERIZATION** of `lowerDenom`.

## Branch budget

```text
Mathematical target     Is there a compressed cyclic-word functional
                        Ψ(w), not determined by (L,o), that survives
                        the floor-power 1+q recursion and yields a
                        closure inequality beyond lowerDenom / run-type?
Novelty hypothesis      Collatz learned that (L,o) is too coarse and
                        introduced φ(s), then optimized it over cyclic
                        shifts. The unfolded weights α_i(w) are the
                        Juggler analogue and might exclude leftover-
                        shaped necklaces that (L,o) cannot see.
Falsifier               α-unfolding is only 1+q / lowerDenom in other
                        coordinates; CycleMin freezes the leading
                        weights; min_σ S bounds a non-minimum start;
                        Halbeisen M kills no necklace that D_w does
                        not; or 4^{S/g} is useless on near-convergents.
Existing machinery      onePlusSlack_concat; relative_slack_even/odd;
                        lowerDenom / cycle_le_lowerDenom;
                        run-type packing; extremal_word;
                        closed pair-level / ordered-excursion branches
Maximum Phase-0 scope   Define α and S; prove D_w = 4^{S(w)}; verify
                        the product identity on short orbits; census
                        expanding itineraries through length 8; compare
                        bunched / mechanical / extremal shapes at
                        L=5,8,11,19. No leftover enumeration at
                        L=25781; no CLI; no Lean; no new finance.
Promotion criterion     A reusable inequality involving Ψ(w) that
                        excludes a leftover-shaped necklace, or a
                        cyclic-shift optimum that is not D_w rewritten.
Stop criterion          The functional is lowerDenom; cyclic
                        optimization does not transfer; no necklace
                        dies; or the attack becomes another envelope.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Slack weights \(\alpha_i(w)=2^i 3^{o_{>i}}\) —
  **EXACT — HUMAN PROOF** (unfolding of `relative_slack_even` /
  `relative_slack_odd`)
- Product identity \(1+q=\prod(1+\eta_i)^{\alpha_i}\) —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED**
  (\(92\) short orbits, \(0\) fails)
- \(\mathrm{lowerDenom}(w)=4^{S(w)}\) —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED**
  (all \(511\) itineraries of length \(\le 8\))
- Same \((L,o)\), different \(S\) —
  **EXACT — HUMAN PROOF** (\(\mathtt{OE}\) versus \(\mathtt{EO}\))
- `CycleMin` leading-weight freeze —
  **EXACT — HUMAN PROOF** (any start \(\mathtt{OO}\) with fixed
  \(o\) has \(\alpha_0=3^{o-1}\), \(\alpha_1=2\cdot 3^{o-2}\))
- Halbeisen \(M_{L,o}\) leftover-killer —
  **REFUTED** (`juggler_cycle_itinerary_functional_closure`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_itinerary_functional`
- Dataset: `data/research/juggler/cycle_finance/word_functional/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_itinerary_functional.py`
- Window: identity \(n\le 24\), \(k\le 4\); denom and necklace
  census \(k\le 8\); shaped words at \(L=5,8,11,19\).
  Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_itinerary_functional_closure` — **REFUTED**.

## Counterexamples

- \(\mathtt{OE}\) and \(\mathtt{EO}\) have the same counts and
  different \(S\), but they are rotations: \(\min_\sigma S=3\) on
  both. Order-sensitivity of \(S\) inside a necklace is start
  dependence, not a new necklace invariant.
- Every `OO`-prefix with fixed \((L,o)\) shares the leading
  weights. Cyclic-shift optimization cannot be applied to the
  `CycleMin` start: one must use that orientation's \(D_w\).
- On \(17\) expanding pairs through length \(8\), nine have
  several \(S\) values and three have several \(\min_\sigma S\)
  values. None of those necklaces dies by \(M_{L,o}\) beyond
  `lowerDenom`.
- At \(L=19\) the bunched, mechanical, and extremal words have
  \(S=1047537,2816889,3130233\). The finance-relevant mechanical
  word has *larger* \(S\), hence a weaker \(n\le 4^{S/g}\) bound
  than the bunched word. The leftover-shaped word is the one the
  functional treats most generously.

## Formalization

None. No `CycleItineraryFunctional.lean`. The identities are the
existing `onePlusSlack` laws plus the closed-form
`lowerDenom=4^S`. Paper A is unchanged.

## Results

- **Weight unfolding** — **EXACT — HUMAN PROOF**.
- **\(D_w=4^{S(w)}\)** — **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED** (`word_functional/summary.json`):
  `denom.fails=0`.
- **Product identity** — **COMPUTATIONALLY VERIFIED**:
  `identity.fails=0` on \(92\) orbits.
- **No leftover-shaped necklace dies** — **COMPUTATIONALLY VERIFIED**:
  `new_necklace_kills=0`, `emptied_count=0`.
- **Halbeisen transfer** — **REFUTED**. The \(n\)-independent
  functional is `lowerDenom`. Cyclic minimization recovers the
  odds-first orientation already used for `CycleMin`.

## Open questions

None from cyclic-word functionals extracted from \(1+q\). The
Collatz affine formula \(\varphi(s)\) has no floor-power analogue
that is independent of the remainder sequence. A kill still
requires the exact ordered remainders, which is the complete word.

## Decision

**CLOSE**. The natural Juggler analogue of \(\varphi(s)\) exists
and is already in the platform: the slack-weight sum \(S(w)\) is
\(\log_4\mathrm{lowerDenom}(w)\). It is order-sensitive, and
\(\min_\sigma S\) is a necklace invariant, but the only closure
inequality it produces is `cycle_pow_le_lowerDenom`. CycleMin
freezes the leading weights, so cyclic-shift optimization does
not improve the bound at the minimum. Hercher's valley count is
already the run-type parameter \(e\). Keep the identities as
negative knowledge. No Paper A edit, no ledger row, no Lean.

Best next question: none from a cyclic-word functional extracted
from the \(1+q\) recursion.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a Collatz
methodology import; not a second manuscript and not a Paper A
edit.
