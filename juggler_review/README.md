# Juggler reviewer bundle (two manuscripts)

Author: Philippe Cochin. Date: 2 September 2026.
Status: Paper A is a submission candidate; Paper B is a revised
working draft (writeup repaired; length-5 harvest imported;
certified density \(7/8\)).

This folder is a snapshot of the files to send for external review. It
is not the laboratory. No termination theorem is claimed.

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
   \(L\ge 176251\) at that floor. The main numerical result is
   \(L\ge 478245\) at the second certified floor \(162849448\)
   (Corollary 5.10) — a certified evaluation of the same kill
   criterion on the survivors beyond the census-free window,
   not an extension of the window theorem.
   Every nontrivial cycle has at least four even letters, hence
   period at least eleven. Finance-survivor lengths through
   \(10^5\) are supporting material.
2. [juggler_parity_discrepancy_note.pdf](juggler_parity_discrepancy_note.pdf)
   — **Paper B**: parity equidistribution of nested floor powers, the
   kernel theorem, depth-4 completeness over odd starts, the
   length-5 contractors, and the certified-descent densities
   \(13/16\) (four steps) and \(7/8\) (five steps). Human proofs.
   Writeup repaired and harvest imported 2 September 2026
   (Lemma 5.2 budget, Step 5b interpolant, named \(P_0\);
   Lemma 6.2 / Theorem 6.3 / Corollary 6.4). Length 7/8 remain
   laboratory conjectures.
3. [juggler_finite_dynamics_reviewer_packet.md](juggler_finite_dynamics_reviewer_packet.md)
   — claim map and falsifiers for both papers. Optional for the proofs.

Markdown sources:
[juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md) and
[juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md).
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
`seq_floor_gap_second`).

## What is not here

The full `Problems.Juggler` laboratory stack, the Word Atlas, pytest
records, and internal dossiers. Those are not required to read either
paper.
