import Problems.Juggler.PrefixTwoEvenEval
import Problems.Juggler.LeftoverEval

namespace Problems.Juggler

/-!
Isolated `returnsIntoB` tables for short bunched leftovers after an
arbitrary CycleMin prefix. Longer odd runs are seven-odd. Not a
bunched-short attack, not Z5, and not a halt theorem.
-/

set_option maxHeartbeats 8000000

theorem returnsIntoB_ooooooeee_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val →
      returnsIntoB y.val itineraryOOOOOOEEE = false := by
  decide +kernel

theorem returnsIntoB_ooooo_eoee_lt314 :
    ∀ y : Fin 314, 2 ≤ y.val →
      returnsIntoB y.val itineraryOOOOOEOEE = false := by
  decide +kernel

theorem returnsIntoB_oooooo_eoee_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val →
      returnsIntoB y.val itineraryOOOOOOEOEE = false := by
  decide +kernel

theorem returnsIntoB_eooee_lt256 :
    ∀ y : Fin 256, ∀ a : Fin 3, 2 ≤ y.val →
      returnsIntoB y.val (threeEvenEOOEE (a.val + 4)) = false := by
  decide +kernel

theorem returnsIntoB_eoooee_lt256 :
    ∀ y : Fin 256, ∀ a : Fin 4, 2 ≤ y.val →
      returnsIntoB y.val (threeEvenEOOOEE (a.val + 3)) = false := by
  decide +kernel

theorem returnsIntoB_ooooo_eeoe_lt314 :
    ∀ y : Fin 314, 2 ≤ y.val →
      returnsIntoB y.val itineraryOOOOOEEOE = false := by
  decide +kernel

theorem returnsIntoB_oooooo_eeoe_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val →
      returnsIntoB y.val itineraryOOOOOOEEOE = false := by
  decide +kernel

theorem returnsIntoB_eoeoe_lt256 :
    ∀ y : Fin 256, ∀ a : Fin 3, 2 ≤ y.val →
      returnsIntoB y.val (threeEvenEOEOE (a.val + 4)) = false := by
  decide +kernel

theorem returnsIntoB_eooeoe_lt256 :
    ∀ y : Fin 256, ∀ a : Fin 4, 2 ≤ y.val →
      returnsIntoB y.val (threeEvenEOOEOE (a.val + 3)) = false := by
  decide +kernel

end Problems.Juggler
