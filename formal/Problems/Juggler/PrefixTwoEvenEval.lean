import Problems.Juggler.LeftoverEval

set_option maxRecDepth 4000000

namespace Problems.Juggler

/-!
Isolated `decide +kernel` tables: no start `y < 256` follows a short
two-even leftover and lands in `[2, y]`. Longer leftovers are
seven-odd. Not a length-8 census and not a halt theorem.
-/

set_option maxHeartbeats 8000000

def returnsIntoB (y : ℕ) (w : List Branch) : Bool :=
  followsB y w && decide (2 ≤ image y w) && decide (image y w ≤ y)

theorem returnsIntoB_ooooee_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val → returnsIntoB y.val itineraryOOOOEE = false := by
  decide +kernel

theorem returnsIntoB_oooooee_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val → returnsIntoB y.val itineraryOOOOOEE = false := by
  decide +kernel

theorem returnsIntoB_two_even_ee8_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val →
      returnsIntoB y.val itineraryTwoEvenEE8 = false := by
  decide +kernel

theorem returnsIntoB_oooeoe_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val → returnsIntoB y.val itineraryOOOEOE' = false := by
  decide +kernel

theorem returnsIntoB_ooooeoe_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val → returnsIntoB y.val itineraryOOOOEOE = false := by
  decide +kernel

theorem returnsIntoB_two_even_eoe8_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val →
      returnsIntoB y.val itineraryTwoEvenEOE8 = false := by
  decide +kernel

theorem returnsIntoB_two_even_eoe9_lt256 :
    ∀ y : Fin 256, 2 ≤ y.val →
      returnsIntoB y.val itineraryTwoEvenEOE9 = false := by
  decide +kernel

end Problems.Juggler
