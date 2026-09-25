/-
  Axiom check for `J-paper-b-minimal-prefixes-five` (Paper B Lemma 5.1 over starts).

  Run `lake env lean AxiomCheckPaperBMinimalPrefixes.lean` from `formal/`.  Every line of the
  output must read `[propext, Classical.choice, Quot.sound]`, or a subset of it.
  `AxiomCheckPaperBMinimalPrefixes.expected` is the recorded output.
-/

import Problems.Juggler.PaperBMinimalPrefixes

open Problems.Juggler

#print axioms PaperBCertificates.lemma51
#print axioms PaperBCertificates.certE_is
#print axioms PaperBCertificates.certOE_is
#print axioms PaperBCertificates.certOOEE_is
#print axioms PaperBCertificates.certOOOEE_is
#print axioms PaperBCertificates.certOOEOE_is
#print axioms PaperBMinimalPrefixes.minimal_certificates_five_iff
#print axioms PaperBMinimalPrefixes.exists_minimal_prefix
#print axioms PaperBMinimalPrefixes.fiveCertificates_minimal
#print axioms PaperBMinimalPrefixes.fiveCertificates_prefix_free
#print axioms PaperBMinimalPrefixes.minimal_prefix_mem
#print axioms PaperBMinimalPrefixes.prefix_or_prefix_of_follows
#print axioms PaperBMinimalPrefixes.prefix_classes_disjoint
#print axioms PaperBMinimalPrefixes.certifiedAt_five_iff
#print axioms PaperBMinimalPrefixes.certifiedAt_five_unique
#print axioms PaperBMinimalPrefixes.certifiedAt_descends
