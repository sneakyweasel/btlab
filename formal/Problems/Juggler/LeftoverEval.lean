import Problems.Juggler.Itinerary

namespace Problems.Juggler

/-! Isolated `native_decide` facts for leftover cycle exclusion. -/

set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2048

def itineraryOOOOEE : List Branch :=
  [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even, Branch.even]

def itineraryOOOEOE' : List Branch :=
  [Branch.odd, Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.even]

def cycleItineraryB (n : ℕ) (w : List Branch) : Bool :=
  followsB n w && (image n w == n) && decide (1 ≤ w.length)

theorem two_mul_pow256_gt_pow257 :
    (257 : ℕ) ^ 64 < 2 * 256 ^ 64 := by
  norm_num

theorem cycleItineraryB_oooeoe_lt256 :
    ∀ n : Fin 256, cycleItineraryB n.val itineraryOOOEOE' = false := by
  native_decide

theorem cycleItineraryB_ooooee_lt256 :
    ∀ n : Fin 256, cycleItineraryB n.val itineraryOOOOEE = false := by
  native_decide

def itineraryOOOOOEE : List Branch :=
  [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
    Branch.even, Branch.even]

def itineraryOOOOEOE : List Branch :=
  [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even,
    Branch.odd, Branch.even]

/-- Base comparison for the length-7 leftover tail: `n ≥ 14`. -/
theorem pow14_243_gt_two_pow422_pow15_128 :
    (2 : ℕ) ^ 422 * 15 ^ 128 < 14 ^ 243 := by
  norm_num

theorem cycleItineraryB_oooooee_lt14 :
    ∀ n : Fin 14, cycleItineraryB n.val itineraryOOOOOEE = false := by
  native_decide

theorem cycleItineraryB_ooooeoe_lt14 :
    ∀ n : Fin 14, cycleItineraryB n.val itineraryOOOOEOE = false := by
  native_decide

def itineraryOOOOOOEEE : List Branch :=
  [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
    Branch.even, Branch.even, Branch.even]

/-- `(1 + 1/128)^{512} < 64`, used by the `n ≥ 128` tail for `OOOOOOEEE`. -/
theorem pow129_512_lt_64_mul_pow128_512 :
    (129 : ℕ) ^ 512 < 64 * 128 ^ 512 := by
  norm_num

theorem cycleItineraryB_ooooooeee_lt128 :
    ∀ n : Fin 128, cycleItineraryB n.val itineraryOOOOOOEEE = false := by
  native_decide

/-! Uniform two-even leftovers. Below `256` no start `n ≥ 2` realizes
seven consecutive odds, so only `k = 8` (EE) and `k = 8,9` (EOE)
need tables. -/

def sevenOdds : List Branch :=
  List.replicate 7 Branch.odd

def itineraryTwoEvenEE8 : List Branch :=
  List.replicate 6 Branch.odd ++ [Branch.even, Branch.even]

def itineraryTwoEvenEOE8 : List Branch :=
  List.replicate 5 Branch.odd ++
    [Branch.even, Branch.odd, Branch.even]

def itineraryTwoEvenEOE9 : List Branch :=
  List.replicate 6 Branch.odd ++
    [Branch.even, Branch.odd, Branch.even]

theorem followsB_seven_odds_of_lt256 :
    ∀ n : Fin 256, 2 ≤ n.val → followsB n.val sevenOdds = false := by
  native_decide

theorem cycleItineraryB_two_even_ee8_lt256 :
    ∀ n : Fin 256, cycleItineraryB n.val itineraryTwoEvenEE8 = false := by
  native_decide

theorem cycleItineraryB_two_even_eoe8_lt256 :
    ∀ n : Fin 256, cycleItineraryB n.val itineraryTwoEvenEOE8 = false := by
  native_decide

theorem cycleItineraryB_two_even_eoe9_lt256 :
    ∀ n : Fin 256, cycleItineraryB n.val itineraryTwoEvenEOE9 = false := by
  native_decide



/-!
## Bunched leftover tables

The six four-even bunched families, formerly the isolated
`Bunched*Eval` files. Isolation was for kernel timeouts, not
mathematics; one `maxHeartbeats` header covers them all.
-/

/-!
Isolated `native_decide` facts for the bunched leftover `O^a EOEE`.
The `a = 5` table is the coarse cutoff `n < 314`. The `a = 6`
table is `n < 16`. This is not a length-9 census and not the
other five bunched families.
-/


def itineraryOOOOOEOEE : List Branch :=
  List.replicate 5 Branch.odd ++
    [Branch.even, Branch.odd, Branch.even, Branch.even]

def itineraryOOOOOOEOEE : List Branch :=
  List.replicate 6 Branch.odd ++
    [Branch.even, Branch.odd, Branch.even, Branch.even]

theorem cycleItineraryB_ooooo_eoee_lt314 :
    ∀ n : Fin 314, 2 ≤ n.val →
      cycleItineraryB n.val itineraryOOOOOEOEE = false := by
  native_decide

theorem cycleItineraryB_oooooo_eoee_lt16 :
    ∀ n : Fin 16, 2 ≤ n.val →
      cycleItineraryB n.val itineraryOOOOOOEOEE = false := by
  native_decide

theorem pow314_243_gt_two_pow422_succ_pow192 :
    (2 : ℕ) ^ 422 * 315 ^ 192 < 314 ^ 243 := by
  norm_num

theorem pow16_729_gt_two_pow1330_succ_pow384 :
    (2 : ℕ) ^ 1330 * 17 ^ 384 < 16 ^ 729 := by
  norm_num

/-!
Isolated `native_decide` table for the bunched leftover `O^a EOOEE`
on `4 ≤ a ≤ 6` and `n < 256`. Longer prefixes are seven-odd.
This is not a length-10 census and not the other four bunched
families.
-/


def threeEvenEOOEE (a : ℕ) : List Branch :=
  List.replicate a Branch.odd ++
    [Branch.even, Branch.odd, Branch.odd, Branch.even, Branch.even]

theorem cycleItineraryB_eooee_prefix_lt256 :
    ∀ n : Fin 256, ∀ a : Fin 3, 2 ≤ n.val →
      cycleItineraryB n.val (threeEvenEOOEE (a.val + 4)) = false := by
  native_decide

/-!
Isolated `native_decide` facts for the bunched leftover `O^a EEOE`.
The `a = 5` table is the coarse cutoff `n < 314`. The `a = 6`
table is `n < 16`. This is not a length-9 census and not the
other bunched families.
-/


def itineraryOOOOOEEOE : List Branch :=
  List.replicate 5 Branch.odd ++
    [Branch.even, Branch.even, Branch.odd, Branch.even]

def itineraryOOOOOOEEOE : List Branch :=
  List.replicate 6 Branch.odd ++
    [Branch.even, Branch.even, Branch.odd, Branch.even]

theorem cycleItineraryB_ooooo_eeoe_lt314 :
    ∀ n : Fin 314, 2 ≤ n.val →
      cycleItineraryB n.val itineraryOOOOOEEOE = false := by
  native_decide

theorem cycleItineraryB_oooooo_eeoe_lt16 :
    ∀ n : Fin 16, 2 ≤ n.val →
      cycleItineraryB n.val itineraryOOOOOOEEOE = false := by
  native_decide

/-!
Isolated `native_decide` table for the bunched leftover `O^a EOEOE`
on `4 ≤ a ≤ 6` and `n < 256`. Longer prefixes are seven-odd.
This is not a length-9 census and not the other bunched families.
-/


def threeEvenEOEOE (a : ℕ) : List Branch :=
  List.replicate a Branch.odd ++
    [Branch.even, Branch.odd, Branch.even, Branch.odd, Branch.even]

theorem cycleItineraryB_eoeoe_prefix_lt256 :
    ∀ n : Fin 256, ∀ a : Fin 3, 2 ≤ n.val →
      cycleItineraryB n.val (threeEvenEOEOE (a.val + 4)) = false := by
  native_decide

/-!
Isolated `native_decide` facts for the bunched leftover `O^a EOOOEE`.
The short-prefix table is `3 ≤ a ≤ 6` and `n < 256`. The `a = 3`
tight comparison starts at `n = 197`. This is not a length-9
census and not the other bunched families.
-/

set_option exponentiation.threshold 2048

def threeEvenEOOOEE (a : ℕ) : List Branch :=
  List.replicate a Branch.odd ++
    [Branch.even, Branch.odd, Branch.odd, Branch.odd,
      Branch.even, Branch.even]

theorem cycleItineraryB_eoooee_prefix_lt256 :
    ∀ n : Fin 256, ∀ a : Fin 4, 2 ≤ n.val →
      cycleItineraryB n.val (threeEvenEOOOEE (a.val + 3)) = false := by
  native_decide

theorem pow40_27_lt_two_mul_pow39_27 :
    (40 : ℕ) ^ 27 < 2 * 39 ^ 27 := by
  norm_num

theorem two_pow38_mul_pow39_16_lt_pow24_27 :
    (2 : ℕ) ^ 38 * 39 ^ 16 < 24 ^ 27 := by
  norm_num

theorem pow197_729_gt_two_pow1650_succ_pow512 :
    (2 : ℕ) ^ 1650 * 198 ^ 512 < 197 ^ 729 := by
  norm_num

/-!
Isolated `native_decide` facts for the bunched leftover `O^a EOOEOE`.
The short-prefix table is `3 ≤ a ≤ 6` and `n < 256`. The `a = 3`
tight comparison starts at `n = 222`. This is not a length-9
census and not the other bunched families.
-/

set_option exponentiation.threshold 2048

def threeEvenEOOEOE (a : ℕ) : List Branch :=
  List.replicate a Branch.odd ++
    [Branch.even, Branch.odd, Branch.odd, Branch.even,
      Branch.odd, Branch.even]

theorem cycleItineraryB_eooeoe_prefix_lt256 :
    ∀ n : Fin 256, ∀ a : Fin 4, 2 ≤ n.val →
      cycleItineraryB n.val (threeEvenEOOEOE (a.val + 3)) = false := by
  native_decide

theorem pow40_9_lt_two_mul_pow39_9 :
    (40 : ℕ) ^ 9 < 2 * 39 ^ 9 := by
  norm_num

theorem pow222_243_gt_two_pow560_succ_pow171 :
    (2 : ℕ) ^ 560 * 223 ^ 171 < 222 ^ 243 := by
  norm_num

end Problems.Juggler
