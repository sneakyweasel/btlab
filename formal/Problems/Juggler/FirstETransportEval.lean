import Problems.Juggler.LeftoverEval

set_option maxRecDepth 4000000

namespace Problems.Juggler

/-!
Isolated `decide +kernel` tables for gapped three-even leftovers
with short gaps `2 ≤ a ≤ 6` and `b ≤ 6`. Longer gaps are
seven-odd. This is not a length-8 or length-9 census.
-/

set_option maxHeartbeats 8000000

def firstEPrefix (a : ℕ) : List Branch :=
  List.replicate a Branch.odd ++ [Branch.even]

def gappedThreeEvenEE (a b : ℕ) : List Branch :=
  firstEPrefix a ++ List.replicate b Branch.odd ++ [Branch.even, Branch.even]

def gappedThreeEvenEOE (a b : ℕ) : List Branch :=
  firstEPrefix a ++ List.replicate b Branch.odd ++
    [Branch.even, Branch.odd, Branch.even]

theorem cycleItineraryB_gapped_ee_short_lt256 :
    ∀ n : Fin 256, ∀ a : Fin 5, ∀ b : Fin 3,
      2 ≤ n.val →
        cycleItineraryB n.val (gappedThreeEvenEE (a.val + 2) (b.val + 4)) =
          false := by
  decide +kernel

theorem cycleItineraryB_gapped_eoe_short_lt256 :
    ∀ n : Fin 256, ∀ a : Fin 5, ∀ b : Fin 4,
      2 ≤ n.val →
        cycleItineraryB n.val (gappedThreeEvenEOE (a.val + 2) (b.val + 3)) =
          false := by
  decide +kernel

end Problems.Juggler
