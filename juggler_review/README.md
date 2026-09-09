# Juggler reviewer bundle (three manuscripts)

Author: Philippe Cochin. Review-repair snapshot: 9 September 2026.
Status: Paper A is a submission candidate; Paper B is a revised
working draft (8-section journal form; Theorem 5.3 the monomial
\(c=\tfrac{3k}4 n^{9/8}\); certified density \(7/8\)); Paper C
(fate contagion and the almost-all reformulation, 4 September 2026)
is a complete draft whose main theorem is unconditional and whose
Appendix C alone depends on Paper B.

This folder is a snapshot of the files to send for external review. It
is not the laboratory. No unconditional termination theorem is claimed.

The 9 September repair corrects six reviewed claim-level issues: general
floor fibers, cycle-run scope, the new kernel application's interval scale,
biased pressure rates and their hypotheses, the charge obstruction's
anchor assumption, and the extended window's formal coverage and endpoint.
The exact integer core and existing conditional reductions are retained;
unproved extensions are not promoted by these corrections.

**Source of truth is `docs/theory/`.** Edit
[juggler_finite_dynamics_note.md](../docs/theory/juggler_finite_dynamics_note.md),
[juggler_parity_discrepancy_note.md](../docs/theory/juggler_parity_discrepancy_note.md)
and
[juggler_fate_almost_all_note.md](../docs/theory/juggler_fate_almost_all_note.md)
there, then rebuild this bundle. Do not hand-edit both copies.

Interactive glossary and playground (Paper A vocabulary only):
https://sneakyweasel.github.io/btlab/

## Read this first

1. [juggler_finite_dynamics_note.pdf](juggler_finite_dynamics_note.pdf)
   — **Paper A**: *Cycle Financing and Near-Convergent
   Diophantine Obstructions in the Juggler Map*. Finance inequality
   plus the verified
   descent floor give \(L\ge 25781\) at \(10^6\) and
   \(L\ge 50508\) at the laboratory floor \(26254995\); the
   Section 5 walk-charge envelope (transport, hug adversary,
   Denjoy–Koksma over certified Ostrowski blocks, window
   theorem on \([50508,16785921)\) — the fan through \(k=54\),
   excluding its \(k=55\) endpoint) raises the bound to
   \(L\ge 176251\) at that floor. Corollary 5.10 evaluates the
   same kill criterion at the second certified floor
   \(162849448\) and gives \(L\ge 478245\). The main numerical
   result is \(L\ge 780239\) at the third certified floor
   \(350000000\) (Corollary 5.11) — certified evaluations of
   the same kill criterion on the survivors; those lengths sit
   inside the census-free window, and the comparison against
   \(\theta(L)\) stays per-length — not extensions of the window
   theorem. Every nontrivial cycle has at least four even letters,
   hence period at least eleven (Theorem 3.22). Once the cycle
   minimum is at least \(300\), that bound strengthens to eight
   even letters and period at least twenty-two (Theorem 3.31;
   computationally verified, not Lean). Finance-survivor lengths
   through \(10^5\) are supporting material. Updated 7 September
   2026 with Theorem 3.31 in the front matter and with the
   companion context (Section 6.1; references [16], [17]):
   the power envelope of Theorem 2.2 is Paper C's descent step and
   the certified floor is its bounded target; the basin of any
   nontrivial cycle has logarithmic count \(\gg(\log x)^{\lambda}\)
   for \(\lambda<\lambda^{**}=0.4926\)
   (Paper C, Theorem 1) while this paper bounds the cycle's states —
   the two constraints do not meet; a cycle's odd share is strictly
   above \(\log 2/\log 3\), with its excess constrained by finance
   (the survivor lengths are convergent and semiconvergent
   denominators); the floor stratifies the failure set exactly as it
   does a cycle minimum. Nothing in Section 6.1 excludes a cycle; the
   theorems and numbers of Sections 2–5 are unchanged.
2. [juggler_parity_discrepancy_note.pdf](juggler_parity_discrepancy_note.pdf)
   — **Paper B**: parity equidistribution of nested floor powers, the
   level-2 wave bound (Lemma 5.2) and the kernel theorem, complete
   depth-4 parity equidistribution for odd-rooted itineraries, the
   length-5 contractors, and the certified-descent densities
   \(13/16\) (four steps) and \(7/8\) (five steps). Human proofs.
   Eight-section journal form, 4 September 2026. Theorem 5.3 is the
   monomial \(c=\tfrac{3k}4 n^{9/8}\); the frozen zero-offset
   coefficient is \(B=-\tfrac9{32}k\beta_1\beta_2\nu^{-9/8}\) with
   \(\lvert B\rvert\le6\); \(\rho_0\) ratios are \(O(P^{-1/4})\).
   Companion audit ledger
   [paper_b_audit_ledger.md](paper_b_audit_ledger.md) and
   `research.juggler_sequence.paper_b_audit` (114 exponent checks).
   Lemma 5.2(ii) from (i) is Claims A–H; Stages 1–5 of (i) remain
   author-chain.
   Section 3.5 proves the depth-\(\le3\) Theorems 4.4 and 4.7 on
   sub-dyadic intervals of length \(\ge P^{1/2}\) with a slow twist
   (Theorems 4.11–4.12, Corollary 4.13 — the \(OOEEE\) production
   that Paper C's Appendix C uses). Theorem 5.3 is dyadic;
   Theorem 5.5 is a human-proof localization to length
   \(P^{29/48+\delta}\), not an established application at the
   \(P^{37/64}\) scale needed by the proposed new productions.
   Section 8 records what the kernel program
   buys for termination and what it cannot. Two more exact identities in Lean
   (`carry_eq_fract_add_sub_fract`, `second_difference_product_rule`).
   Length 7/8 remain laboratory conjectures.
3. [juggler_fate_almost_all_note.pdf](juggler_fate_almost_all_note.pdf)
   — **Paper C**: *Fate Contagion in the Juggler Map and the
   Almost-All Reduction of Termination* (4 September 2026; first
   complete draft 3 September, revised the same day after a first
   external review; pairing and consistency pass 4 September).
   Theorem 1: every nonempty backward-closed set (every realized fate
   class: reaching \(1\), a cycle basin, divergence) has
   \(\sum_{n\le x}1/n\gg(\log x)^{\lambda}\) for
   \(\lambda<\lambda^{**}=0.4926\) (elementary: even blocks are
   intervals, \(OE\) fibers have monotone pairing \(H_m/3-2\);
   abstract recursion lemma). Theorem 2: odd generation (Lean).
   Theorem 3: the conjecture is equivalent to a Tao-type almost-all
   bound with bounded target and rate \((\log y)^{-e}\),
   \(e>0.5074\). Theorem 4:
   that bound follows from parity control on itinerary cylinders of
   depth \(C\log_2\log y\), in a hierarchy of forms down to a single
   exponential moment of the odd count on live starts (\(C\ge19\)
   for the fair optimized-tilt hypothesis; biased forms have
   \(q\)-dependent rates and depths). These hypotheses remain unproved.
   Theorem 5: the exact first-letter decomposition
   has one free term, the infinite-depth live mass; \(S\)-fairness is
   defined and the walk argument labelled a heuristic; a narrowly
   stated depth-uniformity budget. Appendix C (exponent \(0.5392\),
   \(C\ge 18\)) is conditional on the standalone Hypothesis L, the
   only import from Paper B (now its Theorem 4.12, Section 3.5, still
   an unrefereed working draft), with the downstream derivations
   written out. Proposition 4.4 now carries the explicit constant
   \(C_0=250\). Three figures (dependency map, productions,
   decomposition). Lean exact layer; one numerical section, labelled
   observation. Excludes no fate.
4. [juggler_finite_dynamics_reviewer_packet.md](juggler_finite_dynamics_reviewer_packet.md)
   — claim map and falsifiers for the three papers. Optional for the
   proofs.

Markdown sources:
[juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md),
[juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md)
and [juggler_fate_almost_all_note.md](juggler_fate_almost_all_note.md).
Paper B's Section 8 figure is
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

Repository: https://github.com/sneakyweasel/btlab/

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
Lean (`FateContagion.lean`). The seed and abstract recursion are also
formalized. `tao_rate_implies_conjecture` is a compiled conditional
theorem assuming the contagion lower bound and the Tao-rate upper bound;
it does not establish those hypotheses. The production estimates and
asymptotic counting remain human-proof objects; censuses are observations.

## What is not here

The full `Problems.Juggler` laboratory stack, the Word Atlas, pytest
records, and internal dossiers. Those are not required to read either
paper.
