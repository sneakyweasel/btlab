# Juggler reviewer bundle (three manuscripts)

Author: Philippe Cochin. Date: 3 September 2026.
Status: Paper A is a submission candidate; Paper B is a revised
working draft (writeup repaired; length-5 harvest imported;
certified density \(7/8\)); Paper C (fate contagion and the
almost-all reformulation, 3 September 2026) is a first complete
draft whose main theorem is unconditional and whose Section 10 alone
depends on Paper B.

This folder is a snapshot of the files to send for external review. It
is not the laboratory. No termination theorem is claimed.

**Source of truth is `docs/theory/`.** Edit
[juggler_finite_dynamics_note.md](../docs/theory/juggler_finite_dynamics_note.md),
[juggler_parity_discrepancy_note.md](../docs/theory/juggler_parity_discrepancy_note.md)
and
[juggler_fate_almost_all_note.md](../docs/theory/juggler_fate_almost_all_note.md)
there, then rebuild this bundle. Do not hand-edit both copies.

Interactive glossary and playground (Paper A vocabulary only):
https://sneakyweasel.github.io/balanced_ternary/

## Read this first

1. [juggler_finite_dynamics_note.pdf](juggler_finite_dynamics_note.pdf)
   — **Paper A**: *Cycle Financing and Near-Convergent
   Diophantine Obstructions in the Juggler Map*. Finance inequality
   plus the verified
   descent floor give \(L\ge 25781\) at \(10^6\) and
   \(L\ge 50508\) at the laboratory floor \(26254995\); the
   Section 5 walk-charge envelope (transport, hug adversary,
   Denjoy–Koksma over certified Ostrowski blocks, window
   theorem on \([50508,301994)\)) raises the bound to
   \(L\ge 176251\) at that floor. Corollary 5.10 evaluates the
   same kill criterion at the second certified floor
   \(162849448\) and gives \(L\ge 478245\). The main numerical
   result is \(L\ge 780239\) at the third certified floor
   \(350000000\) (Corollary 5.11) — certified evaluations of
   the same kill criterion on the survivors beyond the
   census-free window, not extensions of the window theorem.
   Every nontrivial cycle has at least four even letters, hence
   period at least eleven. Finance-survivor lengths through
   \(10^5\) are supporting material. Updated 3 September 2026 with
   the companion context (new Section 6.1; references [16], [17]):
   the power envelope of Theorem 2.2 is Paper C's descent step and
   the certified floor is its bounded target; the basin of any
   nontrivial cycle has logarithmic count \(\gg(\log x)^{0.405}\)
   (Paper C, Theorem 1) while this paper bounds the cycle's states —
   the two constraints do not meet; a cycle's word sits at the
   critical odd share \(\log 2/\log 3\) of Paper C's no-momentum
   hypothesis (the survivor lengths are convergent and semiconvergent
   denominators); the floor stratifies the failure set exactly as it
   does a cycle minimum. Nothing in Section 6.1 excludes a cycle; the
   theorems and numbers of Sections 2–5 are unchanged.
2. [juggler_parity_discrepancy_note.pdf](juggler_parity_discrepancy_note.pdf)
   — **Paper B**: parity equidistribution of nested floor powers, the
   level-2 wave bound (Lemma 5.2) and the kernel theorem, complete
   depth-4 parity equidistribution for odd-rooted itineraries, the
   length-5 contractors, and the certified-descent densities
   \(13/16\) (four steps) and \(7/8\) (five steps). Human proofs.
   Revised 3 September 2026 after a first external review: a full
   audit of Sections 4–6 (Appendix A, one row per displayed
   estimate; machine layer `research.juggler_sequence.paper_b_audit`
   — exact identities at 60–120 digits, standing estimates on three
   scales, 75 exponent checks) with three corrections that change no
   statement (Lemma 4.3 proof coefficient, the norm named in
   Lemma 3.9, two displayed remainders in Lemma 6.2); new Section 4.5
   proving Theorems 4.4 and 4.7 on sub-dyadic intervals of length
   \(\ge P^{1/2}\) with a slow twist (Theorems 4.11–4.12, Corollary
   4.13 — the \(OOEEE\) production that Paper C's Appendix C uses);
   new Section 7.6 on what the kernel program buys for termination
   and what it cannot; novelty and "certificate density" phrasing
   tightened. Two more exact identities in Lean
   (`carry_eq_fract_add_sub_fract`, `second_difference_product_rule`).
   Length 7/8 remain laboratory conjectures.
3. [juggler_fate_almost_all_note.pdf](juggler_fate_almost_all_note.pdf)
   — **Paper C**: *Fate Contagion in the Juggler Map and the
   Almost-All Reduction of Termination* (revised 3 September 2026
   after a first external review). Theorem 1: every nonempty
   backward-closed set (every realized fate class: reaching \(1\), a
   cycle basin, divergence) has \(\sum_{n\le x}1/n\gg(\log x)^{\lambda}\)
   for \(\lambda<0.4050\) (elementary: even blocks are intervals,
   \(OE\) fibers sweep parity; abstract recursion lemma). Theorem 2:
   odd generation (Lean). Theorem 3: the conjecture is equivalent to
   a Tao-type almost-all bound with bounded target and rate
   \((\log y)^{-e}\), \(e>0.595\). Theorem 4: that bound follows from
   parity control on itinerary cylinders of depth \(C\log_2\log y\),
   in a hierarchy of forms down to a single exponential moment of the
   odd count on live starts (\(C\ge 21\) unconditionally). Theorem 5:
   the exact first-letter decomposition has one free term, the
   infinite-depth live mass; \(S\)-fairness is defined and the walk
   argument labelled a heuristic; a narrowly stated depth-uniformity
   budget. Appendix C (exponent \(0.4922\), \(C\ge 19\)) is
   conditional on the standalone Hypothesis L, the only import from
   Paper B (now its Theorem 4.12, Section 4.5, still an unrefereed
   working draft), with the downstream derivations written out. Three
   figures (dependency map, productions, decomposition). Lean exact
   layer; one numerical section, labelled observation. Excludes no
   fate.
4. [juggler_finite_dynamics_reviewer_packet.md](juggler_finite_dynamics_reviewer_packet.md)
   — claim map and falsifiers for the three papers. Optional for the
   proofs.

Markdown sources:
[juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md),
[juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md)
and [juggler_fate_almost_all_note.md](juggler_fate_almost_all_note.md).
Paper B's Section 7 figure is
[figures/juggler_frontier.png](figures/juggler_frontier.png).

## Optional Lean map

- [juggler_finite_dynamics_formalization.md](juggler_finite_dynamics_formalization.md)
  — theorem names. The Lean import graph is
  [figures/juggler_lean_layers.png](figures/juggler_lean_layers.png).

The paper barrel depends on the repository's full Lean source tree and is
therefore not duplicated in this snapshot. To check the Lean proofs, clone
the repository and from `formal/` run

```text
lake build Problems.JugglerPaper
```

Paper A Zenodo deposit kit (one PDF, paste-ready fields):
[zenodo_paper_a/](zenodo_paper_a/).

Repository: https://github.com/sneakyweasel/balanced_ternary/

The core mathematical lemmas of Paper A are mechanized in Lean 4;
selected finite classifications and the descent floor are
independently certified computations. Theorems 4.6 and 4.8 are
verified computations. Proposition 4.9's arithmetic is Lean.
Every analytic estimate of Paper B (including the kernel theorem
and the shift-average theorem) is a human proof and is not in
Lean; only the exact floor reductions beneath them are
(`GapCells.lean`, including the double-gap identity
`seq_floor_gap_second`). Paper C's exact layer (closure of the fate
classes, trichotomy and exclusion, the even block and \(OE\) fiber
as intervals, odd generation, envelope descent into the floor) is
Lean (`FateContagion.lean`); its counting, its conditional
reduction and its exact map are human proofs; its censuses are
observations.

## What is not here

The full `Problems.Juggler` laboratory stack, the Word Atlas, pytest
records, and internal dossiers. Those are not required to read either
paper.
