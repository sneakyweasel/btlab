/-
# Laboratory extensions of the Collatz bridge

Two statements of `CollatzBridge` that need laboratory modules outside Paper A's proof object:
the minimal-certificate count as a residue count, through `PaperBCertificateRecursion` (Paper B),
and the `-17` cycle word as an inhabitant of the laboratory's `CycleMinShape` (`IdealCycleMin`).
They stay in the namespace `Problems.Juggler.CollatzBridge`; only the file is different, so that
the paper barrel imports the bridge without either laboratory dependency.
-/
import Mathlib.Tactic
import Problems.Juggler.CollatzBridge
import Problems.Juggler.PaperBCertificateRecursion
import Problems.Juggler.IdealCycleMin

namespace Problems.Juggler

namespace CollatzBridge

/-- The residues modulo `2 ^ d` whose word first contracts at length `d`. -/
def decidedAtResidues (d : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ d)).filter fun r ↦ PaperBCertificates.IsMinimalCertificate (parityWord r d)

/-- **The minimal-certificate count is a Collatz count.** `M_d` is the number of residue classes
modulo `2 ^ d` whose stopping time is decided at exactly `d` -- OEIS A100982 read by length. -/
theorem decidedAtResidues_card (d : ℕ) : (decidedAtResidues d).card = minimalCertCount d := by
  unfold decidedAtResidues minimalCertCount minimalCertWords
  exact card_filter_parityWord d PaperBCertificates.IsMinimalCertificate

/-- **Collatz's `-17` cycle inhabits Paper A's `CycleMinShape`**, with the length bound `11` and
the even-count bound `4` both met with equality. The Juggler-specific parts of `CycleMin` (the
floor-power realisation) are not claimed; this is the word-level shape only. -/
theorem neg_seventeen_inhabits_cycleMinShape : CycleMinShape (parityWordZ (-17) 11) := by
  rw [neg_seventeen_cycle.2]
  refine ⟨by decide, by decide, ?_, ?_, rfl, by decide, by decide⟩
  · exact ⟨[.odd, .odd, .odd, .odd, .even, .odd, .odd, .odd, .even, .even], 0, rfl, Nat.zero_le 1,
      Or.inr rfl⟩
  · exact ⟨[.odd, .odd, .even, .odd, .odd, .odd, .even, .even, .even], rfl⟩

end CollatzBridge

end Problems.Juggler
