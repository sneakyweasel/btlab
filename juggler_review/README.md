> **Paper B update, 9 September 2026:** the current PDF is the conditional preprint *Parity Statistics of Nested Floor Powers*. The older Paper B description below is historical and superseded. The kernel estimates remain unproved; 13/16 and 7/8 require explicit correlation hypotheses. See [the review](paper_b_review.md) and [build instructions](../docs/theory/PAPER_B_BUILD.md). Companion cross-citations still require review.

# Juggler reviewer bundle (three manuscripts)

Author: Philippe Cochin. Review-repair snapshot: 9 September 2026.

**Later 9 September source correction:** the canonical Paper C now
restricts H to bad words and H_q to bad prefixes. The unrestricted
versions are refuted by the exact
[absorbed-cylinder proof](../docs/problems/juggler_absorbed_cylinder.md).
This snapshot's Paper C Markdown and PDF predate that correction and
must be rebuilt from `docs/theory/` before further external review.
The stopped live-pressure hypothesis is unchanged and unproved.

Status: Paper A is the regenerated Zenodo preprint of 9 September 2026; Paper B is a revised
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
   is the current **Paper A** preprint. It includes the corrected rotation
   cells, full finite-window estimate, exact threshold table, updated Lean
   uniqueness result, scoped companion context, and explicit AI disclosure.
   Theorem 3.31 gives the computational eight-even-step exclusion.
   The finite-window charge theorem covers \([50508,16785921)\).
   Its strongest reported period floor remains 780239 at the supplied
   descent floor 350000000. The formalization map and reviewer packet are
   generated copies of their canonical `docs/theory/` inputs.
   Rebuild with `python tools/build_paper_a.py`; verify every copy with
   `python tools/build_paper_a.py --check`. See
   [build instructions](../docs/theory/PAPER_A_BUILD.md).
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
