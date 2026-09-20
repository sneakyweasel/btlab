/-
  The eight declarations the PUBLISHED Paper B edition names as machine-checked.

  `AxiomCheckPaperB.lean` audits the historical 2026-09-04 snapshot and says so in its own
  header; `tools/trust_boundary.py` and `tools/manuscript_self_audit.py` read that snapshot,
  and their tests assert that artifact asks about exactly its 49 citations, neither more nor
  fewer. That invariant is worth keeping, so the shipping edition gets its own artifact here
  rather than eight extra lines there.

  Until this file existed, the machine-checked column of
  `docs/theory/juggler_parity_discrepancy_note.md` was the one published trust claim in this
  repository with no gate behind it. The names below are all kernel-trusted today; nothing
  here reproves anything. What it adds is that they cannot silently stop being so.

  Seven of the eight are inside the Paper B root's import closure. The eighth,
  `OneSided.klDiv_nonneg`, is not: `FateOneSidedCorollary` is reachable from the Paper C
  root, not this one. That the shipping manuscript cites a theorem outside its own root's
  closure is a fact about the manuscript, recorded here rather than hidden by the import
  that makes this file compile.

  Run `lake env lean AxiomCheckPaperBPublished.lean` from `formal/`.  Every line of the
  output must read `[propext, Classical.choice, Quot.sound]` -- Mathlib's three and nothing
  else.  `AxiomCheckPaperBPublished.expected` is the recorded output.
-/

import Problems.JugglerParityPaper
-- for OneSided.klDiv_nonneg only; see the header.
import Problems.Juggler.FateOneSidedCorollary

#print axioms Problems.Juggler.PaperBChernoff.theta_lt_one
#print axioms Problems.Juggler.PaperBChernoff.klDiv_pos
#print axioms Problems.Juggler.PaperBMarkov.chernoff_density
#print axioms Problems.Juggler.PaperBMarkov.tilt_gives_theta
#print axioms Problems.Juggler.PaperBMarkov.sum_choose_mul_pow
#print axioms Problems.Juggler.PaperBDensity.density_of_finite_union
#print axioms Problems.Juggler.PaperBDensity.exceptional_density_zero
#print axioms Problems.Juggler.OneSided.klDiv_nonneg
