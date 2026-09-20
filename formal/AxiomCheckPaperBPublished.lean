/-
  The declarations the PUBLISHED Paper B edition names as machine-checked.

  `AxiomCheckPaperB.lean` audits the historical 2026-09-04 snapshot and says so in its own
  header; `tools/trust_boundary.py` and `tools/manuscript_self_audit.py` read that snapshot,
  and their tests assert that artifact asks about exactly its 49 citations, neither more nor
  fewer. That invariant is worth keeping, so the shipping edition gets its own artifact here
  rather than extra lines there.

  Until this file existed, the machine-checked column of
  `docs/theory/juggler_parity_discrepancy_note.md` was the one published trust claim in this
  repository with no gate behind it. The names below are all kernel-trusted today; nothing
  here reproves anything. What it adds is that they cannot silently stop being so.

  The first eight are the declarations the 19 September edition cited in the proof of
  Theorem 6.1. The 20 September edition lists, in Section 8, the twelve modules that check
  its finite combinatorics and the declarations audited for each; the twenty-one added below
  are those. Eight of the twelve modules -- the certificate, recursion, decay, tilt,
  barrier-step and transposition modules -- are not in the Paper B root's import closure,
  and neither is `OneSided.klDiv_nonneg`, which `FateOneSidedCorollary` reaches from the
  Paper C root. That the shipping manuscript cites declarations outside its own root's
  closure is a fact about the manuscript, recorded here rather than hidden by the imports
  that make this file compile.

  Run `lake env lean AxiomCheckPaperBPublished.lean` from `formal/`.  No line of the output
  may show an axiom beyond Mathlib's three, `propext`, `Classical.choice` and `Quot.sound`.
  `AxiomCheckPaperBPublished.expected` is the recorded output.
-/

import Problems.JugglerParityPaper
-- for OneSided.klDiv_nonneg only; see the header.
import Problems.Juggler.FateOneSidedCorollary
-- the Section 8 modules outside the root's closure; see the header.
import Problems.Juggler.PaperBCertificates
import Problems.Juggler.PaperBCertificateLengths
import Problems.Juggler.PaperBFiveStepDensity
import Problems.Juggler.PaperBCertificateRecursion
import Problems.Juggler.PaperBSurvivorDecay
import Problems.Juggler.PaperBTilt
import Problems.Juggler.PaperBBarrierStep
import Problems.Juggler.PaperBJumpTransposition

-- the proof of Theorem 6.1
#print axioms Problems.Juggler.PaperBChernoff.theta_lt_one
#print axioms Problems.Juggler.PaperBChernoff.klDiv_pos
#print axioms Problems.Juggler.PaperBMarkov.chernoff_density
#print axioms Problems.Juggler.PaperBMarkov.tilt_gives_theta
#print axioms Problems.Juggler.PaperBMarkov.sum_choose_mul_pow
#print axioms Problems.Juggler.PaperBDensity.density_of_finite_union
#print axioms Problems.Juggler.PaperBDensity.exceptional_density_zero
#print axioms Problems.Juggler.OneSided.klDiv_nonneg
-- Section 8, in the order of its list
#print axioms Problems.Juggler.PaperBCertificates.lemma51
#print axioms Problems.Juggler.PaperBCertificates.lemma51_complete
#print axioms Problems.Juggler.minimalCert_exists_iff
#print axioms Problems.Juggler.certWindow_unique
#print axioms Problems.Juggler.minimalCert_concat_even
#print axioms Problems.Juggler.five_cylinders_cover
#print axioms Problems.Juggler.certifiedCount_five_eq
#print axioms Problems.Juggler.no_minimal_certificate_six
#print axioms Problems.Juggler.minimal_certificates_seven
#print axioms Problems.Juggler.neverNegCount_add_minimalCertCount
#print axioms Problems.Juggler.minimalCert_tail_eq
#print axioms Problems.Juggler.neverNegCount_succ_of_window_empty
#print axioms Problems.Juggler.PaperBSurvivorDecay.neverNegCount_div_pow_le_theta
#print axioms Problems.Juggler.PaperBSurvivorDecay.neverNegCount_div_pow_tendsto_zero
#print axioms Problems.Juggler.PaperBThreshold.breakEven_saturates
#print axioms Problems.Juggler.PaperBThreshold.first_usable_depth
#print axioms Problems.Juggler.PaperBTilt.lamStar_mean_zero
#print axioms Problems.Juggler.PaperBTilt.rho_closed_form
#print axioms Problems.Juggler.PaperBBarrierStep.survives_succ_of_no_rise
#print axioms Problems.Juggler.PaperBBarrierStep.dies_iff_on_barrier
#print axioms Problems.Juggler.JumpTransposition.stepRise_stepFlat_eq_add_barrierMass
