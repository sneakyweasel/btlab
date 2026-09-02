import Problems.Juggler.LeftoverShort
import Problems.Juggler.LeftoverPreimage
import Problems.Juggler.FirstETransportEval
import Problems.Juggler.BunchedTight
import Problems.Juggler.LeftoverEval

namespace Problems.Juggler

/-!
# Infinite leftover families

Instances of `leftover_prefix_preimage`: two-even, seven bunched
last-cluster words, and first-E transport of the two-even tail.
Gapped `CycleItinerary` is `exists_cycleMin` plus rotation onto an
already-excluded `CycleMin` class, not a cell instance.

Existing theorem names stay. This is not a length-8 census and
not a halt theorem.
-/

/-! ## Two-even leftovers -/

def twoEvenEE (k : ℕ) : List Branch :=
  List.replicate (k - 2) Branch.odd ++ List.replicate 2 Branch.even

def twoEvenEOE (k : ℕ) : List Branch :=
  List.replicate (k - 3) Branch.odd ++
    [Branch.even, Branch.odd, Branch.even]

theorem twoEvenEE_of_six : twoEvenEE 6 = itineraryOOOOEE :=
  rfl

theorem twoEvenEE_of_seven : twoEvenEE 7 = itineraryOOOOOEE :=
  rfl

theorem twoEvenEE_of_eight : twoEvenEE 8 = itineraryTwoEvenEE8 :=
  rfl

theorem twoEvenEOE_of_six : twoEvenEOE 6 = itineraryOOOEOE :=
  rfl

theorem twoEvenEOE_of_seven : twoEvenEOE 7 = itineraryOOOOEOE :=
  rfl

theorem twoEvenEOE_of_eight : twoEvenEOE 8 = itineraryTwoEvenEOE8 :=
  rfl

theorem twoEvenEOE_of_nine : twoEvenEOE 9 = itineraryTwoEvenEOE9 :=
  rfl

theorem no_cycle_itinerary_two_even_ee_of_ge {n k : ℕ}
    (hn : 256 ≤ n) (hk : 6 ≤ k) (h : CycleItinerary n (twoEvenEE k)) : False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hk2 : 2 ≤ k := le_trans (by decide : (2 : ℕ) ≤ 6) hk
  have hz := cycle_trailing_evens_lt (r := 2) (by decide) h
  have hO : follows n (List.replicate (k - 2) Branch.odd) :=
    follows_of_append_left (v := List.replicate 2 Branch.even) h.1
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 4) ^ (2 ^ (k - 2)) = (n + 1) ^ (2 ^ k) := by
    rw [← Nat.pow_mul, four_mul_two_pow_sub hk2]
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using shared_two_even_tail hn hk)

theorem cycle_eoe_suffix_y_cube_lt {n : ℕ} {u : List Branch}
    (h : CycleItinerary n (u ++ [Branch.even, Branch.odd, Branch.even])) :
    image n (u ++ [Branch.even]) ^ 3 < (n + 1) ^ 4 := by
  have hcell : CycleItinerary n
      ((u ++ [Branch.even, Branch.odd]) ++ [Branch.even]) := by
    simpa [List.append_assoc] using h
  have hI := cycle_last_even_interval hcell
  have hyO :
      follows (image n (u ++ [Branch.even])) [Branch.odd, Branch.even] :=
    follows_of_append_right (u := u ++ [Branch.even])
      (by simpa [List.append_assoc] using h.1)
  have hyodd : image n (u ++ [Branch.even]) % 2 = 1 := hyO.1
  have hz : image n (u ++ [Branch.even, Branch.odd]) =
      floorPower (image n (u ++ [Branch.even])) := by
    simp [image_append, image]
  have hcube := (floorPower_odd_eq_iff_cube_interval hyodd).mp rfl
  have hylt :
      image n (u ++ [Branch.even]) ^ 3 <
        (floorPower (image n (u ++ [Branch.even])) + 1) ^ 2 :=
    hcube.2
  have hflt :
      floorPower (image n (u ++ [Branch.even])) < (n + 1) ^ 2 := by
    simpa [hz] using hI.2
  have hsucc :
      floorPower (image n (u ++ [Branch.even])) + 1 ≤ (n + 1) ^ 2 :=
    Nat.succ_le_of_lt hflt
  have hsq :
      (floorPower (image n (u ++ [Branch.even])) + 1) ^ 2 ≤
        ((n + 1) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left hsucc 2
  have hexp : ((n + 1) ^ 2) ^ 2 = (n + 1) ^ 4 :=
    (Nat.pow_mul (n + 1) 2 2).symm
  exact lt_of_lt_of_le hylt (hexp ▸ hsq)

theorem no_cycle_itinerary_two_even_eoe_of_ge {n k : ℕ}
    (hn : 256 ≤ n) (hk : 6 ≤ k) (h : CycleItinerary n (twoEvenEOE k)) : False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hk2 : 2 ≤ k := le_trans (by decide : (2 : ℕ) ≤ 6) hk
  have hk3 : 3 ≤ k := le_trans (by decide : (3 : ℕ) ≤ 6) hk
  set u := List.replicate (k - 3) Branch.odd
  set z := image n u
  set y := image n (u ++ [Branch.even])
  have hC : CycleItinerary n (u ++ [Branch.even, Branch.odd, Branch.even]) := h
  have hO : follows n u :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even]) h.1
  have he : z % 2 = 0 := by
    have hf : follows z [Branch.even, Branch.odd, Branch.even] :=
      follows_of_append_right (u := u) h.1
    exact hf.1
  have hyeq : floorPower z = y := by
    simp [z, y, u, image_append, image]
  have hzlt : z < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq).2
  have hpow := odd_run_lower_growth hn1 hO
  have hm : 2 ^ (k - 3) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow : z ^ (2 ^ (k - 3)) < (y + 1) ^ (2 ^ (k - 2)) := by
    have := pow_lt_of_lt_pow_mul (k := 2) (m := 2 ^ (k - 3)) hzlt hm
    have hexp : 2 * 2 ^ (k - 3) = 2 ^ (k - 2) := by
      rw [two_mul_two_pow]
      congr 1
      omega
    rwa [hexp] at this
  have hmid : n ^ (3 ^ (k - 3)) <
      2 ^ denomBits (k - 3) * (y + 1) ^ (2 ^ (k - 2)) :=
    lt_of_le_of_lt hpow
      (Nat.mul_lt_mul_of_pos_left hzpow
        (pow_pos (by decide : (0 : ℕ) < 2) _))
  have hcube : n ^ (3 ^ (k - 2)) <
      2 ^ (3 * denomBits (k - 3)) * (y + 1) ^ (3 * 2 ^ (k - 2)) := by
    have hlt : (n ^ (3 ^ (k - 3))) ^ 3 <
        (2 ^ denomBits (k - 3) * (y + 1) ^ (2 ^ (k - 2))) ^ 3 :=
      Nat.pow_lt_pow_left hmid (by decide : (3 : ℕ) ≠ 0)
    have hL : (n ^ (3 ^ (k - 3))) ^ 3 = n ^ (3 ^ (k - 2)) := by
      rw [← Nat.pow_mul, three_pow_succ_sub hk3]
    have hR : (2 ^ denomBits (k - 3) * (y + 1) ^ (2 ^ (k - 2))) ^ 3 =
        2 ^ (3 * denomBits (k - 3)) * (y + 1) ^ (3 * 2 ^ (k - 2)) :=
      two_mul_pow_cube _ _ _
    rwa [hL, hR] at hlt
  have hy3 := cycle_eoe_suffix_y_cube_lt (u := u) hC
  have hA : 3 ≤ n + 1 :=
    le_trans (by decide : (3 : ℕ) ≤ 257) (Nat.succ_le_succ hn)
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA (by simpa [y, u] using hy3)
  have hyraise : (y + 1) ^ (3 * 2 ^ (k - 2)) <
      2 ^ (2 ^ (k - 2)) * (n + 1) ^ (2 ^ k) := by
    have hm' : 2 ^ (k - 2) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
    have hlt : ((y + 1) ^ 3) ^ (2 ^ (k - 2)) <
        (2 * (n + 1) ^ 4) ^ (2 ^ (k - 2)) :=
      Nat.pow_lt_pow_left hysucc hm'
    have hL : ((y + 1) ^ 3) ^ (2 ^ (k - 2)) =
        (y + 1) ^ (3 * 2 ^ (k - 2)) :=
      (Nat.pow_mul (y + 1) 3 (2 ^ (k - 2))).symm
    have hR : (2 * (n + 1) ^ 4) ^ (2 ^ (k - 2)) =
        2 ^ (2 ^ (k - 2)) * (n + 1) ^ (4 * 2 ^ (k - 2)) := by
      rw [mul_pow, Nat.pow_mul]
    rw [hL, hR, four_mul_two_pow_sub hk2] at hlt
    exact hlt
  have hlt : n ^ (3 ^ (k - 2)) <
      2 ^ denomBits (k - 2) * (n + 1) ^ (2 ^ k) := by
    have hmid' : n ^ (3 ^ (k - 2)) <
        2 ^ (3 * denomBits (k - 3)) *
          (2 ^ (2 ^ (k - 2)) * (n + 1) ^ (2 ^ k)) :=
      lt_trans hcube
        (Nat.mul_lt_mul_of_pos_left hyraise
          (pow_pos (by decide : (0 : ℕ) < 2) _))
    have hexp :
        2 ^ (3 * denomBits (k - 3)) *
            (2 ^ (2 ^ (k - 2)) * (n + 1) ^ (2 ^ k)) =
          2 ^ (3 * denomBits (k - 3) + 2 ^ (k - 2)) * (n + 1) ^ (2 ^ k) := by
      rw [← mul_assoc, ← Nat.pow_add]
    have hbits : 3 * denomBits (k - 3) + 2 ^ (k - 2) = denomBits (k - 2) := by
      have : k - 2 = (k - 3) + 1 := by omega
      rw [this, denomBits_succ]
    rwa [hexp, hbits] at hmid'
  exact (not_lt_of_gt (shared_two_even_tail hn hk)) hlt

theorem no_follows_seven_odds_of_lt256 {n : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 256) : ¬follows n sevenOdds := by
  intro hf
  have hfalse : followsB n sevenOdds = false :=
    followsB_seven_odds_of_lt256 ⟨n, hn⟩ hn2
  have htrue : followsB n sevenOdds = true := (followsB_iff n sevenOdds).mpr hf
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem twoEvenEE_follows_seven_odds {n k : ℕ}
    (hk : 9 ≤ k) (h : CycleItinerary n (twoEvenEE k)) :
    follows n sevenOdds := by
  have hO : follows n (List.replicate (k - 2) Branch.odd) :=
    follows_of_append_left (v := List.replicate 2 Branch.even) h.1
  have hsplit : List.replicate (k - 2) Branch.odd =
      sevenOdds ++ List.replicate (k - 9) Branch.odd := by
    have hsum : 7 + (k - 9) = k - 2 := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  have hO' : follows n (sevenOdds ++ List.replicate (k - 9) Branch.odd) := by
    simpa [hsplit] using hO
  exact follows_of_append_left (v := List.replicate (k - 9) Branch.odd) hO'

theorem twoEvenEOE_follows_seven_odds {n k : ℕ}
    (hk : 10 ≤ k) (h : CycleItinerary n (twoEvenEOE k)) :
    follows n sevenOdds := by
  have hO : follows n (List.replicate (k - 3) Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even]) h.1
  have hsplit : List.replicate (k - 3) Branch.odd =
      sevenOdds ++ List.replicate (k - 10) Branch.odd := by
    have hsum : 7 + (k - 10) = k - 3 := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  have hO' : follows n (sevenOdds ++ List.replicate (k - 10) Branch.odd) := by
    simpa [hsplit] using hO
  exact follows_of_append_left (v := List.replicate (k - 10) Branch.odd) hO'

theorem no_cycle_itinerary_two_even_ee_of_lt {n k : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 256) (hk : 6 ≤ k)
    (h : CycleItinerary n (twoEvenEE k)) : False := by
  have hcases : k = 6 ∨ k = 7 ∨ k = 8 ∨ 9 ≤ k := by omega
  rcases hcases with h6 | h7 | h8 | hge
  · subst h6
    exact no_cycle_itinerary_ooooee hn2 (by simpa [twoEvenEE_of_six] using h)
  · subst h7
    exact no_cycle_itinerary_oooooee hn2 (by simpa [twoEvenEE_of_seven] using h)
  · subst h8
    have hfalse := cycleItineraryB_two_even_ee8_lt256 ⟨n, hn⟩
    have htrue : cycleItineraryB n itineraryTwoEvenEE8 = true :=
      cycleItineraryB_iff.mpr (by simpa [twoEvenEE_of_eight] using h)
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  · exact no_follows_seven_odds_of_lt256 hn2 hn
      (twoEvenEE_follows_seven_odds hge h)

theorem no_cycle_itinerary_two_even_eoe_of_lt {n k : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 256) (hk : 6 ≤ k)
    (h : CycleItinerary n (twoEvenEOE k)) : False := by
  have hcases : k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ 10 ≤ k := by omega
  rcases hcases with h6 | h7 | h8 | h9 | hge
  · subst h6
    exact no_cycle_itinerary_oooeoe hn2 (by simpa [twoEvenEOE_of_six] using h)
  · subst h7
    exact no_cycle_itinerary_ooooeoe hn2 (by simpa [twoEvenEOE_of_seven] using h)
  · subst h8
    have hfalse := cycleItineraryB_two_even_eoe8_lt256 ⟨n, hn⟩
    have htrue : cycleItineraryB n itineraryTwoEvenEOE8 = true :=
      cycleItineraryB_iff.mpr (by simpa [twoEvenEOE_of_eight] using h)
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  · subst h9
    have hfalse := cycleItineraryB_two_even_eoe9_lt256 ⟨n, hn⟩
    have htrue : cycleItineraryB n itineraryTwoEvenEOE9 = true :=
      cycleItineraryB_iff.mpr (by simpa [twoEvenEOE_of_nine] using h)
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  · exact no_follows_seven_odds_of_lt256 hn2 hn
      (twoEvenEOE_follows_seven_odds hge h)

theorem no_cycle_itinerary_two_even_ee {n k : ℕ} (hn : 2 ≤ n) (hk : 6 ≤ k) :
    ¬CycleItinerary n
      (List.replicate (k - 2) Branch.odd ++ List.replicate 2 Branch.even) := by
  intro h
  cases lt_or_ge n 256 with
  | inl hlt => exact no_cycle_itinerary_two_even_ee_of_lt hn hlt hk h
  | inr hge => exact no_cycle_itinerary_two_even_ee_of_ge hge hk h

theorem no_cycle_itinerary_two_even_eoe {n k : ℕ} (hn : 2 ≤ n) (hk : 6 ≤ k) :
    ¬CycleItinerary n
      (List.replicate (k - 3) Branch.odd ++
        [Branch.even, Branch.odd, Branch.even]) := by
  intro h
  cases lt_or_ge n 256 with
  | inl hlt => exact no_cycle_itinerary_two_even_eoe_of_lt hn hlt hk h
  | inr hge => exact no_cycle_itinerary_two_even_eoe_of_ge hge hk h


/-! ## `OOOOOOEEE` as the `a = 6` EEE instance -/

/-! Length-9 leftover `OOOOOOEEE`. Finite evaluation below `128`
plus `n^729 > 2^1330 (n+1)^512` for `n ≥ 128`. The prefix-cell
comparison first fires at `73`; `128` is the algebraic cutoff.
Not a length-nine census. -/

set_option exponentiation.threshold 2048
set_option maxRecDepth 2048

theorem no_cycle_itinerary_ooooooeee_of_lt {n : ℕ} (hn : n < 128) :
    ¬CycleItinerary n itineraryOOOOOOEEE := by
  intro h
  have hfalse := cycleItineraryB_ooooooeee_lt128 ⟨n, hn⟩
  have htrue : cycleItineraryB n itineraryOOOOOOEEE = true := cycleItineraryB_iff.mpr h
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem lowerDenom_oooooo :
    lowerDenom
      [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
        Branch.odd] = 2 ^ 1330 := by
  rw [lowerDenom, lowerDenomFrom_odd_cons]
  have s0 : (1 : ℕ) ^ 3 * 4 ^ (2 ^ 0) = 2 ^ 2 := by decide
  rw [s0, lowerDenomFrom_odd_cons]
  have s1 : (2 ^ 2) ^ 3 * 4 ^ (2 ^ 1) = 2 ^ 10 := by
    rw [two_pow_mul, four_pow_two_pow, ← Nat.pow_add]
    rfl
  rw [s1, lowerDenomFrom_odd_cons]
  have s2 : (2 ^ 10) ^ 3 * 4 ^ (2 ^ 2) = 2 ^ 38 := by
    rw [two_pow_mul, four_pow_two_pow, ← Nat.pow_add]
    rfl
  rw [s2, lowerDenomFrom_odd_cons]
  have s3 : (2 ^ 38) ^ 3 * 4 ^ (2 ^ 3) = 2 ^ 130 := by
    rw [two_pow_mul, four_pow_two_pow, ← Nat.pow_add]
    rfl
  rw [s3, lowerDenomFrom_odd_cons]
  have s4 : (2 ^ 130) ^ 3 * 4 ^ (2 ^ 4) = 2 ^ 422 := by
    rw [two_pow_mul, four_pow_two_pow, ← Nat.pow_add]
    rfl
  rw [s4, lowerDenomFrom_odd_cons]
  have s5 : (2 ^ 422) ^ 3 * 4 ^ (2 ^ 5) = 2 ^ 1330 := by
    rw [two_pow_mul, four_pow_two_pow, ← Nat.pow_add]
    rfl
  rw [s5, lowerDenomFrom_nil]

theorem oddCount_oooooo :
    oddCount
      [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
        Branch.odd] = 6 :=
  rfl

theorem oooooo_lower_growth {n : ℕ} (hn : 1 ≤ n)
    (hw : follows n
      [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
        Branch.odd]) :
    n ^ 729 ≤ 2 ^ 1330 *
      image n
        [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
          Branch.odd] ^ 64 := by
  have hL := lower_growth_word hn hw
  rw [LowerPowerBound, oddCount_oooooo, lowerDenom_oooooo] at hL
  have hlen :
      ([Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
          Branch.odd] : List Branch).length = 6 :=
    rfl
  rw [hlen] at hL
  have h3 : (3 : ℕ) ^ 6 = 729 := by decide
  have h2 : (2 : ℕ) ^ 6 = 64 := by decide
  rw [h3, h2] at hL
  exact hL

theorem two_pow_128 : (128 : ℕ) = 2 ^ 7 := by
  decide

theorem succ_pow512_lt {n : ℕ} (hn : 128 ≤ n) :
    (n + 1) ^ 512 < 64 * n ^ 512 := by
  have hlin : 128 * (n + 1) ≤ 129 * n := by omega
  have hpow : (128 * (n + 1)) ^ 512 ≤ (129 * n) ^ 512 :=
    Nat.pow_le_pow_left hlin 512
  rw [mul_pow, mul_pow] at hpow
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 128) hn
  have hstrict : 129 ^ 512 * n ^ 512 < 64 * 128 ^ 512 * n ^ 512 :=
    Nat.mul_lt_mul_of_pos_right pow129_512_lt_64_mul_pow128_512
      (pow_pos hn0 512)
  have hmid : 128 ^ 512 * (n + 1) ^ 512 < 64 * 128 ^ 512 * n ^ 512 :=
    lt_of_le_of_lt hpow hstrict
  have hRHS : 64 * 128 ^ 512 * n ^ 512 = 128 ^ 512 * (64 * n ^ 512) :=
    calc
      64 * 128 ^ 512 * n ^ 512 = 64 * (128 ^ 512 * n ^ 512) := by
        rw [mul_assoc]
      _ = (128 ^ 512 * n ^ 512) * 64 := by rw [mul_comm]
      _ = 128 ^ 512 * (n ^ 512 * 64) := by rw [mul_assoc]
      _ = 128 ^ 512 * (64 * n ^ 512) := by rw [mul_comm (n ^ 512)]
  have hpos : 0 < 128 ^ 512 := pow_pos (by decide : (0 : ℕ) < 128) 512
  exact (Nat.mul_lt_mul_left hpos).mp (hmid.trans_eq hRHS)

theorem pow729_gt_two_pow1330_succ_pow512 {n : ℕ} (hn : 128 ≤ n) :
    2 ^ 1330 * (n + 1) ^ 512 < n ^ 729 := by
  have hsucc := succ_pow512_lt hn
  have hmul : 2 ^ 1330 * (n + 1) ^ 512 < 2 ^ 1330 * (64 * n ^ 512) :=
    Nat.mul_lt_mul_of_pos_left hsucc
      (pow_pos (by decide : (0 : ℕ) < 2) 1330)
  have h64 : (64 : ℕ) = 2 ^ 6 := by decide
  have hexp : 2 ^ 1330 * (64 * n ^ 512) = 2 ^ 1336 * n ^ 512 := by
    rw [h64, ← mul_assoc, ← Nat.pow_add]
  have h1336 : 2 ^ 1330 * (n + 1) ^ 512 < 2 ^ 1336 * n ^ 512 :=
    hmul.trans_eq hexp
  have hn217 : 2 ^ 1519 ≤ n ^ 217 := by
    have hpow : (128 : ℕ) ^ 217 ≤ n ^ 217 := Nat.pow_le_pow_left hn 217
    have h128 : (128 : ℕ) ^ 217 = 2 ^ 1519 := by
      rw [two_pow_128, ← Nat.pow_mul]
    exact h128 ▸ hpow
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 128) hn
  have h1519 : 2 ^ 1336 * n ^ 512 < 2 ^ 1519 * n ^ 512 :=
    Nat.mul_lt_mul_of_pos_right
      (Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2)
        (by decide : (1336 : ℕ) < 1519))
      (pow_pos hn0 512)
  have hle : 2 ^ 1519 * n ^ 512 ≤ n ^ 217 * n ^ 512 :=
    Nat.mul_le_mul_right _ hn217
  have h729 : n ^ 217 * n ^ 512 = n ^ 729 := by
    rw [← Nat.pow_add]
  exact (h1336.trans h1519).trans_le (hle.trans_eq h729)

theorem itineraryOOOOOOEEE_split :
    itineraryOOOOOOEEE =
      [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
          Branch.odd] ++
        List.replicate 3 Branch.even :=
  rfl

theorem no_cycle_itinerary_ooooooeee_of_ge {n : ℕ} (hn : 128 ≤ n)
    (h : CycleItinerary n itineraryOOOOOOEEE) : False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 128) hn
  have hsplit := itineraryOOOOOOEEE_split
  have hC : CycleItinerary n
      ([Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
          Branch.odd] ++
        List.replicate 3 Branch.even) := by
    simpa [hsplit] using h
  have hz := cycle_trailing_evens_lt (r := 3) (by decide) hC
  have hOOOOOO :
      follows n
        [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
          Branch.odd] :=
    follows_of_append_left (v := List.replicate 3 Branch.even)
      (by simpa [hsplit] using h.1)
  have hpow := oooooo_lower_growth hn1 hOOOOOO
  have hz64 :
      image n
          [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
            Branch.odd] ^ 64 <
        (n + 1) ^ 512 := by
    have := pow_lt_of_lt_pow_mul (k := 8) (m := 64) hz (by decide)
    simpa using this
  have hlt : n ^ 729 < 2 ^ 1330 * (n + 1) ^ 512 :=
    lt_of_le_of_lt hpow (Nat.mul_lt_mul_of_pos_left hz64
      (pow_pos (by decide : (0 : ℕ) < 2) 1330))
  exact (not_lt_of_gt (pow729_gt_two_pow1330_succ_pow512 hn)) hlt

theorem no_cycle_itinerary_ooooooeee {n : ℕ} (_hn : 2 ≤ n) :
    ¬CycleItinerary n itineraryOOOOOOEEE := by
  intro h
  cases lt_or_ge n 128 with
  | inl hlt => exact no_cycle_itinerary_ooooooeee_of_lt hlt h
  | inr hge => exact no_cycle_itinerary_ooooooeee_of_ge hge h

/-! ## Bunched EEE -/

/-!
# Uniform three-trailing-even leftovers `O^a EEE`

`OOOOOOEEE` is the first expanding instance. The three-even cell
`z < (n+1)^8` against `C_{O^a}` is the comparison

`n^{3^a} > 2^{e_a} (n+1)^{2^{a+3}}`

with `e_a = denomBits a`. Large `n` is the `a = 6` comparison at
`n ≥ 128`, cubed in `a`. Below `128`, `a = 6` is the existing table
and `a ≥ 7` is seven consecutive odds.

This excludes that one bunched family only. It is not the other six
bunched tails, not a length-8 or length-9 census, and not a halt
theorem. Paper A records the family as Theorem 3.14.
-/

def threeEvenEEE (a : ℕ) : List Branch :=
  List.replicate a Branch.odd ++ List.replicate 3 Branch.even

theorem eight_mul_two_pow (a : ℕ) : 8 * 2 ^ a = 2 ^ (a + 3) := by
  have h8 : (8 : ℕ) = 2 ^ 3 := rfl
  rw [h8, ← Nat.pow_add]
  congr 1
  omega

theorem four_mul_two_pow_succ (a : ℕ) : 4 * 2 ^ (a + 1) = 2 ^ (a + 3) := by
  have h4 : (4 : ℕ) = 2 ^ 2 := rfl
  rw [h4, ← Nat.pow_add]
  congr 1
  omega

theorem denomBits_six : denomBits 6 = 1330 := by
  native_decide

theorem three_pow_six : (3 : ℕ) ^ 6 = 729 := by
  decide

theorem two_pow_nine : (2 : ℕ) ^ 9 = 512 := by
  decide

theorem two_pow_six_add_three : (2 : ℕ) ^ (6 + 3) = 512 :=
  two_pow_nine

theorem threeEvenEEE_of_six : threeEvenEEE 6 = itineraryOOOOOOEEE :=
  rfl

theorem three_even_eee_tail_succ {n a : ℕ} (hn : 128 ≤ n)
    (ih : 2 ^ denomBits a * (n + 1) ^ (2 ^ (a + 3)) < n ^ (3 ^ a)) :
    2 ^ denomBits (a + 1) * (n + 1) ^ (2 ^ (a + 4)) <
      n ^ (3 ^ (a + 1)) := by
  have hcube :
      2 ^ (3 * denomBits a) * (n + 1) ^ (3 * 2 ^ (a + 3)) <
        n ^ (3 ^ (a + 1)) := by
    have hlt :
        (2 ^ denomBits a * (n + 1) ^ (2 ^ (a + 3))) ^ 3 <
          (n ^ (3 ^ a)) ^ 3 :=
      Nat.pow_lt_pow_left ih (by decide : (3 : ℕ) ≠ 0)
    have hL : (2 ^ denomBits a * (n + 1) ^ (2 ^ (a + 3))) ^ 3 =
        2 ^ (3 * denomBits a) * (n + 1) ^ (3 * 2 ^ (a + 3)) :=
      two_mul_pow_cube _ _ _
    have hR : (n ^ (3 ^ a)) ^ 3 = n ^ (3 ^ (a + 1)) := by
      rw [← Nat.pow_mul, ← Nat.pow_succ]
    rwa [hL, hR] at hlt
  have hsucc4 : 2 < (n + 1) ^ 4 := by
    have h16 : (16 : ℕ) ≤ (n + 1) ^ 4 := by
      have : 2 ≤ n + 1 := by omega
      simpa using Nat.pow_le_pow_left this 4
    exact lt_of_lt_of_le (by decide : (2 : ℕ) < 16) h16
  have hpow4 : 2 ^ (2 ^ (a + 1)) < (n + 1) ^ (2 ^ (a + 3)) := by
    have hm : 2 ^ (a + 1) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
    have : 2 ^ (2 ^ (a + 1)) < ((n + 1) ^ 4) ^ (2 ^ (a + 1)) :=
      Nat.pow_lt_pow_left hsucc4 hm
    rwa [← Nat.pow_mul, four_mul_two_pow_succ a] at this
  have he' : denomBits (a + 1) = 3 * denomBits a + 2 ^ (a + 1) :=
    denomBits_succ a
  have hfactor :
      2 ^ denomBits (a + 1) * (n + 1) ^ (2 ^ (a + 4)) <
        2 ^ (3 * denomBits a) * (n + 1) ^ (3 * 2 ^ (a + 3)) := by
    have hL :
        2 ^ denomBits (a + 1) * (n + 1) ^ (2 ^ (a + 4)) =
          2 ^ (3 * denomBits a) *
            (2 ^ (2 ^ (a + 1)) * (n + 1) ^ (2 ^ (a + 4))) := by
      rw [he', Nat.pow_add, mul_assoc]
    have hR :
        2 ^ (3 * denomBits a) * (n + 1) ^ (3 * 2 ^ (a + 3)) =
          2 ^ (3 * denomBits a) *
            ((n + 1) ^ (2 ^ (a + 3)) * (n + 1) ^ (2 ^ (a + 4))) := by
      congr 1
      rw [← Nat.pow_add, three_mul_two_pow]
    have hpos2 : 0 < 2 ^ (3 * denomBits a) :=
      pow_pos (by decide : (0 : ℕ) < 2) _
    have hposn : 0 < (n + 1) ^ (2 ^ (a + 4)) :=
      pow_pos (Nat.succ_pos n) _
    rw [hL, hR]
    exact Nat.mul_lt_mul_of_pos_left
      (Nat.mul_lt_mul_of_pos_right hpow4 hposn) hpos2
  exact hfactor.trans hcube

theorem three_even_eee_tail {n a : ℕ} (hn : 128 ≤ n) (ha : 6 ≤ a) :
    2 ^ denomBits a * (n + 1) ^ (2 ^ (a + 3)) < n ^ (3 ^ a) := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le ha
  subst ht
  clear ha
  induction t with
  | zero =>
      rw [denomBits_six, three_pow_six, two_pow_six_add_three]
      exact pow729_gt_two_pow1330_succ_pow512 hn
  | succ t ih =>
      exact three_even_eee_tail_succ hn ih

theorem no_cycle_itinerary_three_even_eee_of_ge {n a : ℕ}
    (hn : 128 ≤ n) (ha : 6 ≤ a) (h : CycleItinerary n (threeEvenEEE a)) :
    False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 128) hn
  have hz := cycle_trailing_evens_lt (r := 3) (by decide) h
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left (v := List.replicate 3 Branch.even) h.1
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 8) ^ (2 ^ a) = (n + 1) ^ (2 ^ (a + 3)) := by
    rw [← Nat.pow_mul, eight_mul_two_pow a]
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using three_even_eee_tail hn ha)

theorem threeEvenEEE_follows_seven_odds {n a : ℕ}
    (ha : 7 ≤ a) (h : CycleItinerary n (threeEvenEEE a)) :
    follows n sevenOdds := by
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left (v := List.replicate 3 Branch.even) h.1
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycle_itinerary_three_even_eee_of_lt {n a : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 128) (ha : 6 ≤ a)
    (h : CycleItinerary n (threeEvenEEE a)) : False := by
  have hcases : a = 6 ∨ 7 ≤ a := by omega
  rcases hcases with h6 | hge
  · subst h6
    exact no_cycle_itinerary_ooooooeee hn2 (by simpa [threeEvenEEE_of_six] using h)
  · exact no_follows_seven_odds_of_lt256 hn2
      (lt_trans hn (by decide : (128 : ℕ) < 256))
      (threeEvenEEE_follows_seven_odds hge h)

theorem no_cycle_itinerary_three_even_eee {n a : ℕ} (hn : 2 ≤ n) (ha : 6 ≤ a) :
    ¬CycleItinerary n
      (List.replicate a Branch.odd ++ List.replicate 3 Branch.even) := by
  intro h
  cases lt_or_ge n 128 with
  | inl hlt => exact no_cycle_itinerary_three_even_eee_of_lt hn hlt ha h
  | inr hge => exact no_cycle_itinerary_three_even_eee_of_ge hge ha h

/-! ## Bunched EOEE -/

set_option exponentiation.threshold 2048
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# Uniform bunched leftovers `O^a EOEE`

`OOOOOEOEE` is the first expanding instance. The mixed cell is
`z < (n+1)^6` for `n ≥ 4`: two trailing evens give `p < (n+1)^4`,
the one-odd lower envelope gives `y^3 ≤ 4 p^2`, and `n ≥ 4`
upgrades that to `y < (n+1)^3`, hence `z < (y+1)^2 ≤ (n+1)^6`.

The comparison is

`n^{3^a} > 2^{e_a} (n+1)^{6 · 2^a}`

with `e_a = denomBits a`. Large `n` at `a = 5` is `n ≥ 314`,
cubed in `a`. At `a = 6` the same cell already fires at `n ≥ 16`.
Below those cutoffs, `a = 5` and `a = 6` are tables and `a ≥ 7`
is seven consecutive odds.

This excludes that one bunched family only. It is not the other
five bunched tails, not a length-8 or length-9 census, and not a
halt theorem. Paper A records the family as Theorem 3.15.
-/

def threeEvenEOEE (a : ℕ) : List Branch :=
  List.replicate a Branch.odd ++
    [Branch.even, Branch.odd, Branch.even, Branch.even]

theorem denomBits_one : denomBits 1 = 2 := by
  decide

theorem denomBits_five : denomBits 5 = 422 := by
  native_decide

theorem three_pow_five : (3 : ℕ) ^ 5 = 243 := by
  decide

theorem six_mul_two_pow_five : 6 * 2 ^ 5 = 192 := by
  decide

theorem six_mul_two_pow_six : 6 * 2 ^ 6 = 384 := by
  decide

theorem threeEvenEOEE_of_five : threeEvenEOEE 5 = itineraryOOOOOEOEE :=
  rfl

theorem threeEvenEOEE_of_six : threeEvenEOEE 6 = itineraryOOOOOOEOEE :=
  rfl

theorem eoee_tail_five_succ {n : ℕ} (hn : 1 ≤ n)
    (ih : 2 ^ 422 * (n + 1) ^ 192 < n ^ 243) :
    2 ^ 422 * (n + 2) ^ 192 < (n + 1) ^ 243 := by
  have hpq := persist_succ_pow (p := 243) (q := 192) hn
    (by decide) (by decide)
  have hpos2 : 0 < 2 ^ 422 := pow_pos (by decide : (0 : ℕ) < 2) _
  have hposn : 0 < n ^ 243 :=
    pow_pos (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hn) _
  have hmid : (2 ^ 422 * (n + 2) ^ 192) * n ^ 243 <
      (n + 1) ^ 243 * n ^ 243 :=
    calc
      (2 ^ 422 * (n + 2) ^ 192) * n ^ 243 =
          2 ^ 422 * ((n + 2) ^ 192 * n ^ 243) := by
        rw [mul_assoc]
      _ = 2 ^ 422 * (n ^ 243 * (n + 2) ^ 192) := by
        rw [mul_comm ((n + 2) ^ 192)]
      _ < 2 ^ 422 * (n + 1) ^ (243 + 192) :=
        Nat.mul_lt_mul_of_pos_left hpq hpos2
      _ = 2 ^ 422 * ((n + 1) ^ 243 * (n + 1) ^ 192) := by
        rw [Nat.pow_add]
      _ = 2 ^ 422 * ((n + 1) ^ 192 * (n + 1) ^ 243) := by
        rw [mul_comm ((n + 1) ^ 243)]
      _ = (2 ^ 422 * (n + 1) ^ 192) * (n + 1) ^ 243 := by
        rw [mul_assoc]
      _ < n ^ 243 * (n + 1) ^ 243 :=
        Nat.mul_lt_mul_of_pos_right ih (pow_pos (Nat.succ_pos n) _)
      _ = (n + 1) ^ 243 * n ^ 243 := mul_comm _ _
  exact (Nat.mul_lt_mul_right hposn).mp hmid

theorem eoee_tail_six_succ {n : ℕ} (hn : 1 ≤ n)
    (ih : 2 ^ 1330 * (n + 1) ^ 384 < n ^ 729) :
    2 ^ 1330 * (n + 2) ^ 384 < (n + 1) ^ 729 := by
  have hpq := persist_succ_pow (p := 729) (q := 384) hn
    (by decide) (by decide)
  have hpos2 : 0 < 2 ^ 1330 := pow_pos (by decide : (0 : ℕ) < 2) _
  have hposn : 0 < n ^ 729 :=
    pow_pos (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hn) _
  have hmid : (2 ^ 1330 * (n + 2) ^ 384) * n ^ 729 <
      (n + 1) ^ 729 * n ^ 729 :=
    calc
      (2 ^ 1330 * (n + 2) ^ 384) * n ^ 729 =
          2 ^ 1330 * ((n + 2) ^ 384 * n ^ 729) := by
        rw [mul_assoc]
      _ = 2 ^ 1330 * (n ^ 729 * (n + 2) ^ 384) := by
        rw [mul_comm ((n + 2) ^ 384)]
      _ < 2 ^ 1330 * (n + 1) ^ (729 + 384) :=
        Nat.mul_lt_mul_of_pos_left hpq hpos2
      _ = 2 ^ 1330 * ((n + 1) ^ 729 * (n + 1) ^ 384) := by
        rw [Nat.pow_add]
      _ = 2 ^ 1330 * ((n + 1) ^ 384 * (n + 1) ^ 729) := by
        rw [mul_comm ((n + 1) ^ 729)]
      _ = (2 ^ 1330 * (n + 1) ^ 384) * (n + 1) ^ 729 := by
        rw [mul_assoc]
      _ < n ^ 729 * (n + 1) ^ 729 :=
        Nat.mul_lt_mul_of_pos_right ih (pow_pos (Nat.succ_pos n) _)
      _ = (n + 1) ^ 729 * n ^ 729 := mul_comm _ _
  exact (Nat.mul_lt_mul_right hposn).mp hmid

theorem eoee_tail_five_at {n : ℕ} (hn : 314 ≤ n) :
    2 ^ 422 * (n + 1) ^ 192 < n ^ 243 := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hn
  subst ht
  clear hn
  induction t with
  | zero => exact pow314_243_gt_two_pow422_succ_pow192
  | succ t ih =>
      have h1 : 1 ≤ 314 + t := by omega
      exact eoee_tail_five_succ h1 ih

theorem eoee_tail_six_at {n : ℕ} (hn : 16 ≤ n) :
    2 ^ 1330 * (n + 1) ^ 384 < n ^ 729 := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hn
  subst ht
  clear hn
  induction t with
  | zero => exact pow16_729_gt_two_pow1330_succ_pow384
  | succ t ih =>
      have h1 : 1 ≤ 16 + t := by omega
      exact eoee_tail_six_succ h1 ih

theorem three_even_eoee_tail_succ {n a : ℕ} (hn : 1 ≤ n)
    (ih : 2 ^ denomBits a * (n + 1) ^ (6 * 2 ^ a) < n ^ (3 ^ a)) :
    2 ^ denomBits (a + 1) * (n + 1) ^ (6 * 2 ^ (a + 1)) <
      n ^ (3 ^ (a + 1)) := by
  have hcube :
      2 ^ (3 * denomBits a) * (n + 1) ^ (3 * (6 * 2 ^ a)) <
        n ^ (3 ^ (a + 1)) := by
    have hlt :
        (2 ^ denomBits a * (n + 1) ^ (6 * 2 ^ a)) ^ 3 <
          (n ^ (3 ^ a)) ^ 3 :=
      Nat.pow_lt_pow_left ih (by decide : (3 : ℕ) ≠ 0)
    have hL : (2 ^ denomBits a * (n + 1) ^ (6 * 2 ^ a)) ^ 3 =
        2 ^ (3 * denomBits a) * (n + 1) ^ (3 * (6 * 2 ^ a)) :=
      two_mul_pow_cube _ _ _
    have hR : (n ^ (3 ^ a)) ^ 3 = n ^ (3 ^ (a + 1)) := by
      rw [← Nat.pow_mul, ← Nat.pow_succ]
    rwa [hL, hR] at hlt
  have hsucc6 : 4 < (n + 1) ^ 6 := by
    have h64 : (64 : ℕ) ≤ (n + 1) ^ 6 := by
      have : 2 ≤ n + 1 := by omega
      simpa using Nat.pow_le_pow_left this 6
    exact lt_of_lt_of_le (by decide : (4 : ℕ) < 64) h64
  have hpow4 : 2 ^ (2 ^ (a + 1)) < (n + 1) ^ (6 * 2 ^ a) := by
    have hm : 2 ^ a ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
    have : 4 ^ (2 ^ a) < ((n + 1) ^ 6) ^ (2 ^ a) :=
      Nat.pow_lt_pow_left hsucc6 hm
    have h4 : (4 : ℕ) ^ (2 ^ a) = 2 ^ (2 ^ (a + 1)) := by
      have : (4 : ℕ) = 2 ^ 2 := rfl
      rw [this, ← Nat.pow_mul, Nat.mul_comm, ← Nat.pow_succ]
    rwa [h4, ← Nat.pow_mul] at this
  have he' : denomBits (a + 1) = 3 * denomBits a + 2 ^ (a + 1) :=
    denomBits_succ a
  have hfactor :
      2 ^ denomBits (a + 1) * (n + 1) ^ (6 * 2 ^ (a + 1)) <
        2 ^ (3 * denomBits a) * (n + 1) ^ (3 * (6 * 2 ^ a)) := by
    have hexp : 3 * (6 * 2 ^ a) = 6 * 2 ^ a + 6 * 2 ^ (a + 1) := by
      have : 6 * 2 ^ (a + 1) = 12 * 2 ^ a := by
        rw [pow_succ]
        ring
      rw [this]
      ring
    have hL :
        2 ^ denomBits (a + 1) * (n + 1) ^ (6 * 2 ^ (a + 1)) =
          2 ^ (3 * denomBits a) *
            (2 ^ (2 ^ (a + 1)) * (n + 1) ^ (6 * 2 ^ (a + 1))) := by
      rw [he', Nat.pow_add, mul_assoc]
    have hR :
        2 ^ (3 * denomBits a) * (n + 1) ^ (3 * (6 * 2 ^ a)) =
          2 ^ (3 * denomBits a) *
            ((n + 1) ^ (6 * 2 ^ a) * (n + 1) ^ (6 * 2 ^ (a + 1))) := by
      congr 1
      rw [hexp, Nat.pow_add]
    have hpos2 : 0 < 2 ^ (3 * denomBits a) :=
      pow_pos (by decide : (0 : ℕ) < 2) _
    have hposn : 0 < (n + 1) ^ (6 * 2 ^ (a + 1)) :=
      pow_pos (Nat.succ_pos n) _
    rw [hL, hR]
    exact Nat.mul_lt_mul_of_pos_left
      (Nat.mul_lt_mul_of_pos_right hpow4 hposn) hpos2
  exact hfactor.trans hcube

theorem three_even_eoee_tail_of_five {n a : ℕ} (hn : 314 ≤ n)
    (ha : 5 ≤ a) :
    2 ^ denomBits a * (n + 1) ^ (6 * 2 ^ a) < n ^ (3 ^ a) := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le ha
  subst ht
  clear ha
  induction t with
  | zero =>
      rw [denomBits_five, three_pow_five, six_mul_two_pow_five]
      exact eoee_tail_five_at hn
  | succ t ih =>
      exact three_even_eoee_tail_succ
        (le_trans (by decide : (1 : ℕ) ≤ 314) hn) ih

theorem three_even_eoee_tail_of_six {n a : ℕ} (hn : 16 ≤ n)
    (ha : 6 ≤ a) :
    2 ^ denomBits a * (n + 1) ^ (6 * 2 ^ a) < n ^ (3 ^ a) := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le ha
  subst ht
  clear ha
  induction t with
  | zero =>
      rw [denomBits_six, three_pow_six, six_mul_two_pow_six]
      exact eoee_tail_six_at hn
  | succ t ih =>
      exact three_even_eoee_tail_succ
        (le_trans (by decide : (1 : ℕ) ≤ 16) hn) ih

theorem four_mul_succ_pow8_lt_succ_pow9 {n : ℕ} (hn : 4 ≤ n) :
    4 * (n + 1) ^ 8 < (n + 1) ^ 9 := by
  have : (4 : ℕ) < n + 1 := by omega
  have hpos : 0 < (n + 1) ^ 8 := pow_pos (Nat.succ_pos n) 8
  have hr : (n + 1) ^ 9 = (n + 1) * (n + 1) ^ 8 :=
    (pow_succ (n + 1) 8).trans (mul_comm _ _)
  rw [hr]
  exact Nat.mul_lt_mul_of_pos_right this hpos

theorem threeEvenEOEE_z_lt {n a : ℕ} (hn : 4 ≤ n)
    (h : CycleItinerary n (threeEvenEOEE a)) :
    image n (List.replicate a Branch.odd) < (n + 1) ^ 6 := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 4) hn
  have hsplit : threeEvenEOEE a =
      (List.replicate a Branch.odd ++ [Branch.even, Branch.odd]) ++
        List.replicate 2 Branch.even := by
    simp [threeEvenEOEE]
  have hC : CycleItinerary n
      ((List.replicate a Branch.odd ++ [Branch.even, Branch.odd]) ++
        List.replicate 2 Branch.even) := by
    simpa [hsplit] using h
  have hp := cycle_trailing_evens_lt (r := 2) (by decide) hC
  set z := image n (List.replicate a Branch.odd)
  set y := image n (List.replicate a Branch.odd ++ [Branch.even])
  have hyeq : y = floorPower z := by
    simp [y, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.even, Branch.even] :=
    follows_of_append_right (u := List.replicate a Branch.odd)
      (by simpa [threeEvenEOEE] using h.1)
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq.symm).2
  have hyO : follows y [Branch.odd] :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [y, hyeq, image] using hf.2)
  have hy1 : 1 ≤ y := by
    have hz1 : 1 ≤ z := image_pos hn1 _
    simpa [y, hyeq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := y) (a := 1) hy1 hyO
  have hpimg :
      image n (List.replicate a Branch.odd ++ [Branch.even, Branch.odd]) =
        floorPower y := by
    simp [y, image_append, image]
  have hle' : y ^ 3 ≤ 4 * floorPower y ^ 2 := by
    simpa [denomBits_one] using hpow
  have hp' : floorPower y < (n + 1) ^ 4 := by
    rwa [hpimg] at hp
  have hplt : 4 * floorPower y ^ 2 < 4 * (n + 1) ^ 8 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 2) hp' (by decide)
    exact Nat.mul_lt_mul_of_pos_left this (by decide : (0 : ℕ) < 4)
  have hy3 : y ^ 3 < (n + 1) ^ 9 :=
    lt_of_le_of_lt hle' (hplt.trans (four_mul_succ_pow8_lt_succ_pow9 hn))
  have h9 : (n + 1) ^ 9 = ((n + 1) ^ 3) ^ 3 := by
    rw [← Nat.pow_mul]
  have hylt : y < (n + 1) ^ 3 :=
    (Nat.pow_lt_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp (h9 ▸ hy3)
  have hys : y + 1 ≤ (n + 1) ^ 3 := Nat.succ_le_of_lt hylt
  have hz6 : z < (n + 1) ^ 6 := by
    have : (y + 1) ^ 2 ≤ ((n + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left hys 2
    have hexp : ((n + 1) ^ 3) ^ 2 = (n + 1) ^ 6 := by rw [← Nat.pow_mul]
    exact lt_of_lt_of_le hzlt (hexp ▸ this)
  exact hz6

theorem no_cycle_itinerary_three_even_eoee_of_ge_five {n a : ℕ}
    (hn : 314 ≤ n) (ha : 5 ≤ a) (h : CycleItinerary n (threeEvenEOEE a)) :
    False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 314) hn
  have hn4 : 4 ≤ n := le_trans (by decide : (4 : ℕ) ≤ 314) hn
  have hz := threeEvenEOEE_z_lt hn4 h
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.even, Branch.even])
      (by simpa [threeEvenEOEE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 6) ^ (2 ^ a) = (n + 1) ^ (6 * 2 ^ a) :=
    (Nat.pow_mul (n + 1) 6 (2 ^ a)).symm
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using three_even_eoee_tail_of_five hn ha)

theorem no_cycle_itinerary_three_even_eoee_of_ge_six {n a : ℕ}
    (hn : 16 ≤ n) (ha : 6 ≤ a) (h : CycleItinerary n (threeEvenEOEE a)) :
    False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 16) hn
  have hn4 : 4 ≤ n := le_trans (by decide : (4 : ℕ) ≤ 16) hn
  have hz := threeEvenEOEE_z_lt hn4 h
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.even, Branch.even])
      (by simpa [threeEvenEOEE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 6) ^ (2 ^ a) = (n + 1) ^ (6 * 2 ^ a) :=
    (Nat.pow_mul (n + 1) 6 (2 ^ a)).symm
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using three_even_eoee_tail_of_six hn ha)

theorem threeEvenEOEE_follows_seven_odds {n a : ℕ}
    (ha : 7 ≤ a) (h : CycleItinerary n (threeEvenEOEE a)) :
    follows n sevenOdds := by
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.even, Branch.even])
      (by simpa [threeEvenEOEE] using h.1)
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycle_itinerary_three_even_eoee_of_lt_five {n : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 314) (h : CycleItinerary n (threeEvenEOEE 5)) :
    False := by
  have hfalse : cycleItineraryB n itineraryOOOOOEOEE = false :=
    cycleItineraryB_ooooo_eoee_lt314 ⟨n, hn⟩ hn2
  have htrue : cycleItineraryB n itineraryOOOOOEOEE = true :=
    cycleItineraryB_iff.mpr (by simpa [threeEvenEOEE_of_five] using h)
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_three_even_eoee_of_lt_six {n : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 16) (h : CycleItinerary n (threeEvenEOEE 6)) :
    False := by
  have hfalse : cycleItineraryB n itineraryOOOOOOEOEE = false :=
    cycleItineraryB_oooooo_eoee_lt16 ⟨n, hn⟩ hn2
  have htrue : cycleItineraryB n itineraryOOOOOOEOEE = true :=
    cycleItineraryB_iff.mpr (by simpa [threeEvenEOEE_of_six] using h)
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_three_even_eoee {n a : ℕ} (hn : 2 ≤ n) (ha : 5 ≤ a) :
    ¬CycleItinerary n
      (List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.even, Branch.even]) := by
  intro h
  have hcases : a = 5 ∨ a = 6 ∨ 7 ≤ a := by omega
  rcases hcases with h5 | hrest
  · subst h5
    cases lt_or_ge n 314 with
    | inl hlt => exact no_cycle_itinerary_three_even_eoee_of_lt_five hn hlt h
    | inr hge => exact no_cycle_itinerary_three_even_eoee_of_ge_five hge (by decide) h
  rcases hrest with h6 | hge
  · subst h6
    cases lt_or_ge n 16 with
    | inl hlt => exact no_cycle_itinerary_three_even_eoee_of_lt_six hn hlt h
    | inr hge => exact no_cycle_itinerary_three_even_eoee_of_ge_six hge (by decide) h
  · cases lt_or_ge n 256 with
    | inl hlt =>
        exact no_follows_seven_odds_of_lt256 hn hlt
          (threeEvenEOEE_follows_seven_odds hge h)
    | inr hge' =>
        exact no_cycle_itinerary_three_even_eoee_of_ge_six
          (le_trans (by decide : (16 : ℕ) ≤ 256) hge')
          (le_trans (by decide : (6 : ℕ) ≤ 7) hge) h

/-! ## Bunched EOOEE -/

/-!
# Uniform bunched leftovers `O^a EOOEE`

`OOOOEOOEE` is the first expanding instance. The mixed cell is
`z < (n+1)^4` for `n ≥ 32`: two trailing evens give `p < (n+1)^4`,
the two-odd lower envelope gives `y^9 ≤ 1024 p^4`, and `n ≥ 32`
upgrades that to `y < (n+1)^2`, hence `z < (y+1)^2 ≤ (n+1)^4`.

The comparison is then exactly the shared two-even tail

`n^{3^a} > 2^{e_a} (n+1)^{2^{a+2}}`

with `e_a = denomBits a`. Large `n` is `n ≥ 256`, already proved
for every `a ≥ 4`. Below `256`, `4 ≤ a ≤ 6` is a table and
`a ≥ 7` is seven consecutive odds.

This excludes that one bunched family only. It is not the other
four bunched tails, not a length-8 or length-9 census, and not a
halt theorem. Paper A records the family as Theorem 3.16.
-/

set_option exponentiation.threshold 2048
set_option maxRecDepth 2048

theorem four_mul_two_pow_a (a : ℕ) : 4 * 2 ^ a = 2 ^ (a + 2) := by
  have h4 : (4 : ℕ) = 2 ^ 2 := rfl
  rw [h4, ← Nat.pow_add]
  congr 1
  omega

theorem denomBits_two : denomBits 2 = 10 := by
  decide

theorem three_pow_two : (3 : ℕ) ^ 2 = 9 := by
  decide

theorem two_pow_ten : (2 : ℕ) ^ 10 = 1024 := by
  decide

theorem two_pow10_lt_succ_sq {n : ℕ} (hn : 32 ≤ n) :
    1024 < (n + 1) ^ 2 := by
  have : 33 ≤ n + 1 := by omega
  have h : (33 : ℕ) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left this 2
  exact lt_of_lt_of_le (by decide : (1024 : ℕ) < 1089) h

theorem two_pow10_succ_pow16_lt_succ_pow18 {n : ℕ} (hn : 32 ≤ n) :
    1024 * (n + 1) ^ 16 < (n + 1) ^ 18 := by
  have hpos : 0 < (n + 1) ^ 16 := pow_pos (Nat.succ_pos n) 16
  have hr : (n + 1) ^ 18 = (n + 1) ^ 2 * (n + 1) ^ 16 := by
    rw [← Nat.pow_add]
  rw [hr]
  exact Nat.mul_lt_mul_of_pos_right (two_pow10_lt_succ_sq hn) hpos

theorem three_even_eooee_tail {n a : ℕ} (hn : 256 ≤ n) (ha : 4 ≤ a) :
    2 ^ denomBits a * (n + 1) ^ (4 * 2 ^ a) < n ^ (3 ^ a) := by
  have hk : 6 ≤ a + 2 := by omega
  have h := shared_two_even_tail (k := a + 2) hn hk
  have hsub : a + 2 - 2 = a := by omega
  simpa [hsub, four_mul_two_pow_a a] using h

theorem threeEvenEOOEE_z_lt {n a : ℕ} (hn : 32 ≤ n)
    (h : CycleItinerary n (threeEvenEOOEE a)) :
    image n (List.replicate a Branch.odd) < (n + 1) ^ 4 := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 32) hn
  have hsplit : threeEvenEOOEE a =
      (List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even := by
    simp [threeEvenEOOEE]
  have hC : CycleItinerary n
      ((List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even) := by
    simpa [hsplit] using h
  have hp := cycle_trailing_evens_lt (r := 2) (by decide) hC
  set z := image n (List.replicate a Branch.odd)
  set y := image n (List.replicate a Branch.odd ++ [Branch.even])
  have hyeq : y = floorPower z := by
    simp [y, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.even, Branch.even] :=
    follows_of_append_right (u := List.replicate a Branch.odd)
      (by simpa [threeEvenEOOEE] using h.1)
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq.symm).2
  have hyO : follows y (List.replicate 2 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [y, hyeq, image, List.replicate] using hf.2)
  have hy1 : 1 ≤ y := by
    have hz1 : 1 ≤ z := image_pos hn1 _
    simpa [y, hyeq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := y) (a := 2) hy1 hyO
  have hpimg :
      image n (List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd]) =
        image y (List.replicate 2 Branch.odd) := by
    simp [y, image_append, image]
  have hle' : y ^ 9 ≤ 1024 * image y (List.replicate 2 Branch.odd) ^ 4 := by
    simpa [denomBits_two, three_pow_two, two_pow_ten] using hpow
  have hp' : image y (List.replicate 2 Branch.odd) < (n + 1) ^ 4 := by
    rwa [← hpimg]
  have hplt : 1024 * image y (List.replicate 2 Branch.odd) ^ 4 <
      1024 * (n + 1) ^ 16 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 4) hp' (by decide)
    exact Nat.mul_lt_mul_of_pos_left this
      (by decide : (0 : ℕ) < 1024)
  have hy9 : y ^ 9 < (n + 1) ^ 18 :=
    lt_of_le_of_lt hle' (hplt.trans (two_pow10_succ_pow16_lt_succ_pow18 hn))
  have h18 : (n + 1) ^ 18 = ((n + 1) ^ 2) ^ 9 := by
    rw [← Nat.pow_mul]
  have hylt : y < (n + 1) ^ 2 :=
    (Nat.pow_lt_pow_iff_left (by decide : (9 : ℕ) ≠ 0)).mp (h18 ▸ hy9)
  have hys : y + 1 ≤ (n + 1) ^ 2 := Nat.succ_le_of_lt hylt
  have : (y + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hys 2
  have hexp : ((n + 1) ^ 2) ^ 2 = (n + 1) ^ 4 := by rw [← Nat.pow_mul]
  exact lt_of_lt_of_le hzlt (hexp ▸ this)

theorem no_cycle_itinerary_three_even_eooee_of_ge {n a : ℕ}
    (hn : 256 ≤ n) (ha : 4 ≤ a) (h : CycleItinerary n (threeEvenEOOEE a)) :
    False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hn32 : 32 ≤ n := le_trans (by decide : (32 : ℕ) ≤ 256) hn
  have hz := threeEvenEOOEE_z_lt hn32 h
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.even, Branch.even])
      (by simpa [threeEvenEOOEE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 4) ^ (2 ^ a) = (n + 1) ^ (4 * 2 ^ a) :=
    (Nat.pow_mul (n + 1) 4 (2 ^ a)).symm
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using three_even_eooee_tail hn ha)

theorem threeEvenEOOEE_follows_seven_odds {n a : ℕ}
    (ha : 7 ≤ a) (h : CycleItinerary n (threeEvenEOOEE a)) :
    follows n sevenOdds := by
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.even, Branch.even])
      (by simpa [threeEvenEOOEE] using h.1)
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycle_itinerary_three_even_eooee_of_lt {n a : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 256) (ha4 : 4 ≤ a) (ha6 : a ≤ 6)
    (h : CycleItinerary n (threeEvenEOOEE a)) : False := by
  have hA : a - 4 < 3 := by omega
  have hfalse :
      cycleItineraryB n (threeEvenEOOEE (a - 4 + 4)) = false :=
    cycleItineraryB_eooee_prefix_lt256 ⟨n, hn⟩ ⟨a - 4, hA⟩ hn2
  have ha : a - 4 + 4 = a := by omega
  have hfalse' : cycleItineraryB n (threeEvenEOOEE a) = false := by
    simpa [ha] using hfalse
  have htrue : cycleItineraryB n (threeEvenEOOEE a) = true :=
    cycleItineraryB_iff.mpr h
  rw [hfalse'] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_three_even_eooee {n a : ℕ} (hn : 2 ≤ n) (ha : 4 ≤ a) :
    ¬CycleItinerary n
      (List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.even, Branch.even]) := by
  intro h
  cases lt_or_ge n 256 with
  | inl hlt =>
      have hcases : a ≤ 6 ∨ 7 ≤ a := by omega
      rcases hcases with hle | hge
      · exact no_cycle_itinerary_three_even_eooee_of_lt hn hlt ha hle h
      · exact no_follows_seven_odds_of_lt256 hn hlt
          (threeEvenEOOEE_follows_seven_odds hge h)
  | inr hge => exact no_cycle_itinerary_three_even_eooee_of_ge hge ha h

/-! ## Bunched EEOE -/

set_option exponentiation.threshold 2048
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# Uniform bunched leftovers `O^a EEOE`

`OOOOOEEOE` is the first expanding instance. The mixed cell is
`z < (n+1)^6` for `n ≥ 4`: the last-odd cube gives `y^3 < (n+1)^4`,
two leading evens give `z < (y+1)^4`, and `n ≥ 4` upgrades that to
`z < (n+1)^6`.

The comparison is then the same EOEE tail

`n^{3^a} > 2^{e_a} (n+1)^{6 · 2^a}`

already proved for `a ≥ 5`. Large `n` at `a = 5` is `n ≥ 314`.
At `a = 6` the same cell already fires at `n ≥ 16`. Below those
cutoffs, `a = 5` and `a = 6` are tables and `a ≥ 7` is seven
consecutive odds.

This excludes that one bunched family only. It is not the other
bunched tails, not a length-8 or length-9 census, and not a halt
theorem. Paper A records the family as Theorem 3.18.
-/

def threeEvenEEOE (a : ℕ) : List Branch :=
  List.replicate a Branch.odd ++
    [Branch.even, Branch.even, Branch.odd, Branch.even]

theorem threeEvenEEOE_of_five : threeEvenEEOE 5 = itineraryOOOOOEEOE :=
  rfl

theorem threeEvenEEOE_of_six : threeEvenEEOE 6 = itineraryOOOOOOEEOE :=
  rfl

theorem two_mul_succ_cube_lt_succ_pow6 {n y : ℕ} (hn : 4 ≤ n)
    (h : (y + 1) ^ 3 < 2 * (n + 1) ^ 4) :
    (y + 1) ^ 4 < (n + 1) ^ 6 := by
  have h8 : 8 * (y + 1) ^ 3 < 16 * (n + 1) ^ 4 := by
    have h' : 8 * (y + 1) ^ 3 < 8 * (2 * (n + 1) ^ 4) :=
      Nat.mul_lt_mul_of_pos_left h (by decide : (0 : ℕ) < 8)
    have hexp : 8 * (2 * (n + 1) ^ 4) = 16 * (n + 1) ^ 4 := by ring
    rwa [hexp] at h'
  have h16 : 16 * (n + 1) ^ 4 < (n + 1) ^ 6 := by
    have hsq : (16 : ℕ) < (n + 1) ^ 2 := by
      have : 5 ≤ n + 1 := by omega
      have h25 : (25 : ℕ) ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left this 2
      exact lt_of_lt_of_le (by decide : (16 : ℕ) < 25) h25
    have hpos : 0 < (n + 1) ^ 4 := pow_pos (Nat.succ_pos n) 4
    have hr : (n + 1) ^ 6 = (n + 1) ^ 2 * (n + 1) ^ 4 := by
      rw [← Nat.pow_add]
    rw [hr]
    exact Nat.mul_lt_mul_of_pos_right hsq hpos
  have hcube : (2 * (y + 1)) ^ 3 < (n + 1) ^ 6 := by
    have hexp : (2 * (y + 1)) ^ 3 = 8 * (y + 1) ^ 3 := by ring
    exact hexp ▸ (h8.trans h16)
  have h6 : (n + 1) ^ 6 = ((n + 1) ^ 2) ^ 3 := by rw [← Nat.pow_mul]
  have hlin : 2 * (y + 1) < (n + 1) ^ 2 :=
    (Nat.pow_lt_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp (h6 ▸ hcube)
  have h4 : (y + 1) ^ 4 = (y + 1) * (y + 1) ^ 3 :=
    (pow_succ (y + 1) 3).trans (mul_comm _ _)
  have hmid : (y + 1) * (y + 1) ^ 3 < (y + 1) * (2 * (n + 1) ^ 4) :=
    Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos y)
  have hmid' : (y + 1) * (2 * (n + 1) ^ 4) = 2 * (y + 1) * (n + 1) ^ 4 := by
    ring
  have hfin : 2 * (y + 1) * (n + 1) ^ 4 < (n + 1) ^ 6 := by
    have hr : (n + 1) ^ 6 = (n + 1) ^ 2 * (n + 1) ^ 4 := by
      rw [← Nat.pow_add]
    rw [hr]
    exact Nat.mul_lt_mul_of_pos_right hlin (pow_pos (Nat.succ_pos n) 4)
  exact h4 ▸ (hmid.trans_eq hmid').trans hfin

theorem threeEvenEEOE_z_lt {n a : ℕ} (hn : 4 ≤ n)
    (h : CycleItinerary n (threeEvenEEOE a)) :
    image n (List.replicate a Branch.odd) < (n + 1) ^ 6 := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 4) hn
  set u := List.replicate a Branch.odd ++ [Branch.even]
  have hsplit : threeEvenEEOE a =
      u ++ [Branch.even, Branch.odd, Branch.even] := by
    simp [threeEvenEEOE, u]
  have hC : CycleItinerary n (u ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [hsplit] using h
  have hy3 := cycle_eoe_suffix_y_cube_lt (u := u) hC
  set z := image n (List.replicate a Branch.odd)
  set s := image n (List.replicate a Branch.odd ++ [Branch.even])
  set y := image n (u ++ [Branch.even])
  have hy3' : y ^ 3 < (n + 1) ^ 4 := by
    simpa [y, u] using hy3
  have hf : follows z
      [Branch.even, Branch.even, Branch.odd, Branch.even] :=
    follows_of_append_right (u := List.replicate a Branch.odd)
      (by simpa [threeEvenEEOE] using h.1)
  have he : z % 2 = 0 := hf.1
  have hseq : s = floorPower z := by
    simp [s, z, image_append, image]
  have hzlt : z < (s + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hseq.symm).2
  have hf2 : follows s [Branch.even, Branch.odd, Branch.even] := by
    simpa [s, hseq, image] using hf.2
  have he2 : s % 2 = 0 := hf2.1
  have hyeq : y = floorPower s := by
    simp [y, s, u, image_append, image]
  have hslt : s < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he2).mp hyeq.symm).2
  have hys : s + 1 ≤ (y + 1) ^ 2 := Nat.succ_le_of_lt hslt
  have hz4 : z < (y + 1) ^ 4 := by
    have : (s + 1) ^ 2 ≤ ((y + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hys 2
    have hexp : ((y + 1) ^ 2) ^ 2 = (y + 1) ^ 4 := by rw [← Nat.pow_mul]
    exact lt_of_lt_of_le hzlt (hexp ▸ this)
  have hA : 3 ≤ n + 1 := by omega
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hy3'
  exact lt_of_lt_of_le hz4 (le_of_lt (two_mul_succ_cube_lt_succ_pow6 hn hysucc))

theorem no_cycle_itinerary_three_even_eeoe_of_ge_five {n a : ℕ}
    (hn : 314 ≤ n) (ha : 5 ≤ a) (h : CycleItinerary n (threeEvenEEOE a)) :
    False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 314) hn
  have hn4 : 4 ≤ n := le_trans (by decide : (4 : ℕ) ≤ 314) hn
  have hz := threeEvenEEOE_z_lt hn4 h
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.even, Branch.odd, Branch.even])
      (by simpa [threeEvenEEOE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 6) ^ (2 ^ a) = (n + 1) ^ (6 * 2 ^ a) :=
    (Nat.pow_mul (n + 1) 6 (2 ^ a)).symm
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using three_even_eoee_tail_of_five hn ha)

theorem no_cycle_itinerary_three_even_eeoe_of_ge_six {n a : ℕ}
    (hn : 16 ≤ n) (ha : 6 ≤ a) (h : CycleItinerary n (threeEvenEEOE a)) :
    False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 16) hn
  have hn4 : 4 ≤ n := le_trans (by decide : (4 : ℕ) ≤ 16) hn
  have hz := threeEvenEEOE_z_lt hn4 h
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.even, Branch.odd, Branch.even])
      (by simpa [threeEvenEEOE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 6) ^ (2 ^ a) = (n + 1) ^ (6 * 2 ^ a) :=
    (Nat.pow_mul (n + 1) 6 (2 ^ a)).symm
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using three_even_eoee_tail_of_six hn ha)

theorem threeEvenEEOE_follows_seven_odds {n a : ℕ}
    (ha : 7 ≤ a) (h : CycleItinerary n (threeEvenEEOE a)) :
    follows n sevenOdds := by
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.even, Branch.odd, Branch.even])
      (by simpa [threeEvenEEOE] using h.1)
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycle_itinerary_three_even_eeoe_of_lt_five {n : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 314) (h : CycleItinerary n (threeEvenEEOE 5)) :
    False := by
  have hfalse : cycleItineraryB n itineraryOOOOOEEOE = false :=
    cycleItineraryB_ooooo_eeoe_lt314 ⟨n, hn⟩ hn2
  have htrue : cycleItineraryB n itineraryOOOOOEEOE = true :=
    cycleItineraryB_iff.mpr (by simpa [threeEvenEEOE_of_five] using h)
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_three_even_eeoe_of_lt_six {n : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 16) (h : CycleItinerary n (threeEvenEEOE 6)) :
    False := by
  have hfalse : cycleItineraryB n itineraryOOOOOOEEOE = false :=
    cycleItineraryB_oooooo_eeoe_lt16 ⟨n, hn⟩ hn2
  have htrue : cycleItineraryB n itineraryOOOOOOEEOE = true :=
    cycleItineraryB_iff.mpr (by simpa [threeEvenEEOE_of_six] using h)
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_three_even_eeoe {n a : ℕ} (hn : 2 ≤ n) (ha : 5 ≤ a) :
    ¬CycleItinerary n
      (List.replicate a Branch.odd ++
        [Branch.even, Branch.even, Branch.odd, Branch.even]) := by
  intro h
  have hcases : a = 5 ∨ a = 6 ∨ 7 ≤ a := by omega
  rcases hcases with h5 | hrest
  · subst h5
    cases lt_or_ge n 314 with
    | inl hlt => exact no_cycle_itinerary_three_even_eeoe_of_lt_five hn hlt h
    | inr hge => exact no_cycle_itinerary_three_even_eeoe_of_ge_five hge (by decide) h
  rcases hrest with h6 | hge
  · subst h6
    cases lt_or_ge n 16 with
    | inl hlt => exact no_cycle_itinerary_three_even_eeoe_of_lt_six hn hlt h
    | inr hge => exact no_cycle_itinerary_three_even_eeoe_of_ge_six hge (by decide) h
  · cases lt_or_ge n 256 with
    | inl hlt =>
        exact no_follows_seven_odds_of_lt256 hn hlt
          (threeEvenEEOE_follows_seven_odds hge h)
    | inr hge' =>
        exact no_cycle_itinerary_three_even_eeoe_of_ge_six
          (le_trans (by decide : (16 : ℕ) ≤ 256) hge')
          (le_trans (by decide : (6 : ℕ) ≤ 7) hge) h

/-! ## Bunched EOEOE -/

/-!
# Uniform bunched leftovers `O^a EOEOE`

`OOOOEOEOE` is the first expanding instance. The mixed cell is
`z < (n+1)^4` for `n ≥ 32`: the last-odd cube gives `y^3 < (n+1)^4`,
the one-odd envelope on the first gap gives `w^3 ≤ 4 s^2`, and
`n ≥ 32` upgrades that to `w < (n+1)^2`, hence `z < (w+1)^2 ≤ (n+1)^4`.

The comparison is then exactly the shared two-even tail already
proved for `O^a EOOEE`. Large `n` is `n ≥ 256`. Below `256`,
`4 ≤ a ≤ 6` is a table and `a ≥ 7` is seven consecutive odds.

This excludes that one bunched family only. It is not the other
bunched tails, not a length-8 or length-9 census, and not a halt
theorem. Paper A records the family as Theorem 3.19.
-/

set_option exponentiation.threshold 2048
set_option maxRecDepth 2048

theorem eight_mul_succ_lt_succ_sq {n y : ℕ} (hn : 32 ≤ n)
    (h : (y + 1) ^ 3 < 2 * (n + 1) ^ 4) :
    8 * (y + 1) < (n + 1) ^ 2 := by
  have h512 : 512 * (y + 1) ^ 3 < 1024 * (n + 1) ^ 4 := by
    have h' : 512 * (y + 1) ^ 3 < 512 * (2 * (n + 1) ^ 4) :=
      Nat.mul_lt_mul_of_pos_left h (by decide : (0 : ℕ) < 512)
    have hexp : 512 * (2 * (n + 1) ^ 4) = 1024 * (n + 1) ^ 4 := by ring
    rwa [hexp] at h'
  have h1024 : 1024 * (n + 1) ^ 4 < (n + 1) ^ 6 := by
    have hsq : (1024 : ℕ) < (n + 1) ^ 2 := by
      have : 33 ≤ n + 1 := by omega
      have h : (33 : ℕ) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left this 2
      exact lt_of_lt_of_le (by decide : (1024 : ℕ) < 1089) h
    have hpos : 0 < (n + 1) ^ 4 := pow_pos (Nat.succ_pos n) 4
    have hr : (n + 1) ^ 6 = (n + 1) ^ 2 * (n + 1) ^ 4 := by
      rw [← Nat.pow_add]
    rw [hr]
    exact Nat.mul_lt_mul_of_pos_right hsq hpos
  have hcube : (8 * (y + 1)) ^ 3 < (n + 1) ^ 6 := by
    have hexp : (8 * (y + 1)) ^ 3 = 512 * (y + 1) ^ 3 := by ring
    exact hexp ▸ (h512.trans h1024)
  have h6 : (n + 1) ^ 6 = ((n + 1) ^ 2) ^ 3 := by rw [← Nat.pow_mul]
  exact (Nat.pow_lt_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp (h6 ▸ hcube)

theorem threeEvenEOEOE_z_lt {n a : ℕ} (hn : 32 ≤ n)
    (h : CycleItinerary n (threeEvenEOEOE a)) :
    image n (List.replicate a Branch.odd) < (n + 1) ^ 4 := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 32) hn
  set pref := List.replicate a Branch.odd ++ [Branch.even, Branch.odd]
  have hsplit : threeEvenEOEOE a =
      pref ++ [Branch.even, Branch.odd, Branch.even] := by
    simp [threeEvenEOEOE, pref]
  have hC : CycleItinerary n
      (pref ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [hsplit] using h
  have hy3 := cycle_eoe_suffix_y_cube_lt (u := pref) hC
  set z := image n (List.replicate a Branch.odd)
  set w := image n (List.replicate a Branch.odd ++ [Branch.even])
  set s := image n (List.replicate a Branch.odd ++ [Branch.even, Branch.odd])
  set y := image n (pref ++ [Branch.even])
  have hy3' : y ^ 3 < (n + 1) ^ 4 := by
    simpa [y, pref] using hy3
  have hf : follows z
      [Branch.even, Branch.odd, Branch.even, Branch.odd, Branch.even] :=
    follows_of_append_right (u := List.replicate a Branch.odd)
      (by simpa [threeEvenEOEOE] using h.1)
  have he : z % 2 = 0 := hf.1
  have hweq : w = floorPower z := by
    simp [w, z, image_append, image]
  have hzlt : z < (w + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hweq.symm).2
  have hwO : follows w (List.replicate 1 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even])
      (by simpa [w, hweq, image, List.replicate] using hf.2)
  have hw1 : 1 ≤ w := by
    have hz1 : 1 ≤ z := image_pos hn1 _
    simpa [w, hweq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := w) (a := 1) hw1 hwO
  have hseq : s = image w (List.replicate 1 Branch.odd) := by
    simp [s, w, image_append, image]
  have hle' : w ^ 3 ≤ 4 * s ^ 2 := by
    simpa [denomBits_one, hseq] using hpow
  have hf2 : follows s [Branch.even, Branch.odd, Branch.even] := by
    have hf1 : follows w
        [Branch.odd, Branch.even, Branch.odd, Branch.even] := by
      simpa [w, hweq, image] using hf.2
    simpa [s, hseq, image, List.replicate] using hf1.2
  have hes : s % 2 = 0 := hf2.1
  have hyeq : y = floorPower s := by
    simp [y, s, pref, image_append, image]
  have hslt : s < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval hes).mp hyeq.symm).2
  have hss : s + 1 ≤ (y + 1) ^ 2 := Nat.succ_le_of_lt hslt
  have hs4 : s ^ 2 < (y + 1) ^ 4 := by
    have : s < (y + 1) ^ 2 := hslt
    exact pow_lt_of_lt_pow_mul (k := 2) (m := 2) this (by decide)
  have hplt : 4 * s ^ 2 < 4 * (y + 1) ^ 4 :=
    Nat.mul_lt_mul_of_pos_left hs4 (by decide : (0 : ℕ) < 4)
  have hw3 : w ^ 3 < 4 * (y + 1) ^ 4 := lt_of_le_of_lt hle' hplt
  have hA : 3 ≤ n + 1 := by omega
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hy3'
  have h8 : 8 * (y + 1) < (n + 1) ^ 2 := eight_mul_succ_lt_succ_sq hn hysucc
  have hy4 : (y + 1) ^ 4 = (y + 1) * (y + 1) ^ 3 :=
    (pow_succ (y + 1) 3).trans (mul_comm _ _)
  have h4y : 4 * (y + 1) ^ 4 < (n + 1) ^ 6 := by
    have hmid : 4 * (y + 1) * (y + 1) ^ 3 <
        4 * (y + 1) * (2 * (n + 1) ^ 4) :=
      Nat.mul_lt_mul_of_pos_left hysucc
        (Nat.mul_pos (by decide : (0 : ℕ) < 4) (Nat.succ_pos y))
    have hexp : 4 * (y + 1) * (2 * (n + 1) ^ 4) =
        8 * (y + 1) * (n + 1) ^ 4 := by ring
    have hfin : 8 * (y + 1) * (n + 1) ^ 4 < (n + 1) ^ 6 := by
      have hr : (n + 1) ^ 6 = (n + 1) ^ 2 * (n + 1) ^ 4 := by
        rw [← Nat.pow_add]
      rw [hr]
      exact Nat.mul_lt_mul_of_pos_right h8 (pow_pos (Nat.succ_pos n) 4)
    have h4y' : 4 * (y + 1) ^ 4 = 4 * (y + 1) * (y + 1) ^ 3 := by
      rw [hy4, mul_assoc]
    exact h4y' ▸ (hmid.trans_eq hexp).trans hfin
  have hw6 : w ^ 3 < (n + 1) ^ 6 := hw3.trans h4y
  have h6 : (n + 1) ^ 6 = ((n + 1) ^ 2) ^ 3 := by rw [← Nat.pow_mul]
  have hwlt : w < (n + 1) ^ 2 :=
    (Nat.pow_lt_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp (h6 ▸ hw6)
  have hws : w + 1 ≤ (n + 1) ^ 2 := Nat.succ_le_of_lt hwlt
  have : (w + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hws 2
  have hexp : ((n + 1) ^ 2) ^ 2 = (n + 1) ^ 4 := by rw [← Nat.pow_mul]
  exact lt_of_lt_of_le hzlt (hexp ▸ this)

theorem no_cycle_itinerary_three_even_eoeoe_of_ge {n a : ℕ}
    (hn : 256 ≤ n) (ha : 4 ≤ a) (h : CycleItinerary n (threeEvenEOEOE a)) :
    False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hn32 : 32 ≤ n := le_trans (by decide : (32 : ℕ) ≤ 256) hn
  have hz := threeEvenEOEOE_z_lt hn32 h
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.even, Branch.odd, Branch.even])
      (by simpa [threeEvenEOEOE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 4) ^ (2 ^ a) = (n + 1) ^ (4 * 2 ^ a) :=
    (Nat.pow_mul (n + 1) 4 (2 ^ a)).symm
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using three_even_eooee_tail hn ha)

theorem threeEvenEOEOE_follows_seven_odds {n a : ℕ}
    (ha : 7 ≤ a) (h : CycleItinerary n (threeEvenEOEOE a)) :
    follows n sevenOdds := by
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.even, Branch.odd, Branch.even])
      (by simpa [threeEvenEOEOE] using h.1)
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycle_itinerary_three_even_eoeoe_of_lt {n a : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 256) (ha4 : 4 ≤ a) (ha6 : a ≤ 6)
    (h : CycleItinerary n (threeEvenEOEOE a)) : False := by
  have hA : a - 4 < 3 := by omega
  have hfalse :
      cycleItineraryB n (threeEvenEOEOE (a - 4 + 4)) = false :=
    cycleItineraryB_eoeoe_prefix_lt256 ⟨n, hn⟩ ⟨a - 4, hA⟩ hn2
  have ha : a - 4 + 4 = a := by omega
  have hfalse' : cycleItineraryB n (threeEvenEOEOE a) = false := by
    simpa [ha] using hfalse
  have htrue : cycleItineraryB n (threeEvenEOEOE a) = true :=
    cycleItineraryB_iff.mpr h
  rw [hfalse'] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_three_even_eoeoe {n a : ℕ} (hn : 2 ≤ n) (ha : 4 ≤ a) :
    ¬CycleItinerary n
      (List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.even, Branch.odd, Branch.even]) := by
  intro h
  cases lt_or_ge n 256 with
  | inl hlt =>
      have hcases : a ≤ 6 ∨ 7 ≤ a := by omega
      rcases hcases with hle | hge
      · exact no_cycle_itinerary_three_even_eoeoe_of_lt hn hlt ha hle h
      · exact no_follows_seven_odds_of_lt256 hn hlt
          (threeEvenEOEOE_follows_seven_odds hge h)
  | inr hge => exact no_cycle_itinerary_three_even_eoeoe_of_ge hge ha h

/-! ## Bunched EOOOEE -/

/-!
# Uniform bunched leftovers `O^a EOOOEE`

`OOOEOOOEE` is the first expanding instance. For `a ≥ 4` the mixed
cell is `z < (n+1)^4`. At `a = 3` the coarse exponent is impossible,
so the argument uses the tight cell against `C_{O^3}`.

Large `n` is `n ≥ 256`. Below `256`, `3 ≤ a ≤ 6` is a table and
`a ≥ 7` is seven consecutive odds.

This excludes that one bunched family only. It is not a length-8
or length-9 census and not a halt theorem. Paper A records the
family as Theorem 3.17.
-/

set_option exponentiation.threshold 16
set_option maxRecDepth 512
set_option maxHeartbeats 400000

theorem denomBits_three : denomBits 3 = 38 := by
  decide

theorem three_pow_three : (3 : ℕ) ^ 3 = 27 := by
  decide

theorem threeEvenEOOOEE_z_lt {n a : ℕ} (hn : 3 ≤ n)
    (h : CycleItinerary n (threeEvenEOOOEE a)) :
    image n (List.replicate a Branch.odd) < (n + 1) ^ 4 := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 3) hn
  have hsplit : threeEvenEOOOEE a =
      (List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even := by
    simp [threeEvenEOOOEE]
  have hC : CycleItinerary n
      ((List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even) := by
    simpa [hsplit] using h
  have hp := cycle_trailing_evens_lt (r := 2) (by decide) hC
  set z := image n (List.replicate a Branch.odd)
  set y := image n (List.replicate a Branch.odd ++ [Branch.even])
  have hyeq : y = floorPower z := by
    simp [y, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.odd,
        Branch.even, Branch.even] :=
    follows_of_append_right (u := List.replicate a Branch.odd)
      (by simpa [threeEvenEOOOEE] using h.1)
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq.symm).2
  have hyO : follows y (List.replicate 3 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [y, hyeq, image, List.replicate] using hf.2)
  have hy1 : 1 ≤ y := by
    have hz1 : 1 ≤ z := image_pos hn1 _
    simpa [y, hyeq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := y) (a := 3) hy1 hyO
  have hpimg :
      image n (List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) =
        image y (List.replicate 3 Branch.odd) := by
    simp [y, image_append, image]
  have hle' : y ^ 27 ≤ 2 ^ 38 * image y (List.replicate 3 Branch.odd) ^ 8 := by
    simpa [denomBits_three, three_pow_three] using hpow
  have hp' : image y (List.replicate 3 Branch.odd) < (n + 1) ^ 4 := by
    rwa [← hpimg]
  have hplt : 2 ^ 38 * image y (List.replicate 3 Branch.odd) ^ 8 <
      2 ^ 38 * (n + 1) ^ 32 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 8) hp' (by decide)
    exact Nat.mul_lt_mul_of_pos_left this
      (pow_pos (by decide : (0 : ℕ) < 2) 38)
  have hy27 : y ^ 27 < 2 ^ 38 * (n + 1) ^ 32 := lt_of_le_of_lt hle' hplt
  exact z_lt_succ_pow4_of_y hzlt (y_lt_succ_sq_of_odd27 hn hy27)

theorem no_cycle_itinerary_three_even_eoooee_of_ge_four {n a : ℕ}
    (hn : 256 ≤ n) (ha : 4 ≤ a) (h : CycleItinerary n (threeEvenEOOOEE a)) :
    False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hn3 : 3 ≤ n := le_trans (by decide : (3 : ℕ) ≤ 256) hn
  have hz := threeEvenEOOOEE_z_lt hn3 h
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.odd,
        Branch.even, Branch.even])
      (by simpa [threeEvenEOOOEE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 4) ^ (2 ^ a) = (n + 1) ^ (4 * 2 ^ a) :=
    (Nat.pow_mul (n + 1) 4 (2 ^ a)).symm
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using three_even_eooee_tail hn ha)

theorem no_cycle_itinerary_three_even_eoooee_of_ge_three {n : ℕ}
    (hn : 256 ≤ n) (h : CycleItinerary n (threeEvenEOOOEE 3)) : False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hn197 : 197 ≤ n := le_trans (by decide : (197 : ℕ) ≤ 256) hn
  have hn24 : 24 ≤ n := le_trans (by decide : (24 : ℕ) ≤ 256) hn
  set z := image n (List.replicate 3 Branch.odd)
  set y := image n (List.replicate 3 Branch.odd ++ [Branch.even])
  have hyeq : y = floorPower z := by
    simp [y, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.odd,
        Branch.even, Branch.even] :=
    follows_of_append_right (u := List.replicate 3 Branch.odd)
      (by simpa [threeEvenEOOOEE] using h.1)
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq.symm).2
  have hO : follows n (List.replicate 3 Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.odd,
        Branch.even, Branch.even])
      (by simpa [threeEvenEOOOEE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hz8 : z ^ 8 < (y + 1) ^ 16 :=
    pow_lt_of_lt_pow_mul (k := 2) (m := 8) hzlt (by decide)
  have h27 : n ^ 27 < 2 ^ 38 * (y + 1) ^ 16 := by
    have hle : n ^ 27 ≤ 2 ^ 38 * z ^ 8 := by
      simpa [denomBits_three, three_pow_three, z] using hpow
    exact lt_of_le_of_lt hle
      (Nat.mul_lt_mul_of_pos_left hz8
        (pow_pos (by decide : (0 : ℕ) < 2) 38))
  have hsplit : threeEvenEOOOEE 3 =
      (List.replicate 3 Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even := by
    simp [threeEvenEOOOEE]
  have hC : CycleItinerary n
      ((List.replicate 3 Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even) := by
    simpa [hsplit] using h
  have hp := cycle_trailing_evens_lt (r := 2) (by decide) hC
  have hyO : follows y (List.replicate 3 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [y, hyeq, image, List.replicate] using hf.2)
  have hy1 : 1 ≤ y := by
    have hz1 : 1 ≤ z := image_pos hn1 _
    simpa [y, hyeq] using floorPower_pos hz1
  have hpowy := odd_run_lower_growth (n := y) (a := 3) hy1 hyO
  have hpimg :
      image n (List.replicate 3 Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) =
        image y (List.replicate 3 Branch.odd) := by
    simp [y, image_append, image]
  have hle' : y ^ 27 ≤ 2 ^ 38 * image y (List.replicate 3 Branch.odd) ^ 8 := by
    simpa [denomBits_three, three_pow_three] using hpowy
  have hp' : image y (List.replicate 3 Branch.odd) < (n + 1) ^ 4 := by
    rwa [← hpimg]
  have hplt : 2 ^ 38 * image y (List.replicate 3 Branch.odd) ^ 8 <
      2 ^ 38 * (n + 1) ^ 32 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 8) hp' (by decide)
    exact Nat.mul_lt_mul_of_pos_left this
      (pow_pos (by decide : (0 : ℕ) < 2) 38)
  have hy27 : y ^ 27 < 2 ^ 38 * (n + 1) ^ 32 := lt_of_le_of_lt hle' hplt
  cases lt_or_ge y 39 with
  | inl hlt => exact eoooee_small_y_false hn24 hlt h27
  | inr hge => exact eoooee_large_y_false hn197 hge hy27 h27

theorem threeEvenEOOOEE_follows_seven_odds {n a : ℕ}
    (ha : 7 ≤ a) (h : CycleItinerary n (threeEvenEOOOEE a)) :
    follows n sevenOdds := by
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.odd,
        Branch.even, Branch.even])
      (by simpa [threeEvenEOOOEE] using h.1)
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycle_itinerary_three_even_eoooee_of_lt {n a : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 256) (ha3 : 3 ≤ a) (ha6 : a ≤ 6)
    (h : CycleItinerary n (threeEvenEOOOEE a)) : False := by
  have hA : a - 3 < 4 := by omega
  have hfalse :
      cycleItineraryB n (threeEvenEOOOEE (a - 3 + 3)) = false :=
    cycleItineraryB_eoooee_prefix_lt256 ⟨n, hn⟩ ⟨a - 3, hA⟩ hn2
  have ha : a - 3 + 3 = a := by omega
  have hfalse' : cycleItineraryB n (threeEvenEOOOEE a) = false := by
    simpa [ha] using hfalse
  have htrue : cycleItineraryB n (threeEvenEOOOEE a) = true :=
    cycleItineraryB_iff.mpr h
  rw [hfalse'] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_three_even_eoooee {n a : ℕ} (hn : 2 ≤ n) (ha : 3 ≤ a) :
    ¬CycleItinerary n
      (List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd,
          Branch.even, Branch.even]) := by
  intro h
  cases lt_or_ge n 256 with
  | inl hlt =>
      have hcases : a ≤ 6 ∨ 7 ≤ a := by omega
      rcases hcases with hle | hge
      · exact no_cycle_itinerary_three_even_eoooee_of_lt hn hlt ha hle h
      · exact no_follows_seven_odds_of_lt256 hn hlt
          (threeEvenEOOOEE_follows_seven_odds hge h)
  | inr hge =>
      have hcases : a = 3 ∨ 4 ≤ a := by omega
      rcases hcases with h3 | h4
      · subst h3
        exact no_cycle_itinerary_three_even_eoooee_of_ge_three hge h
      · exact no_cycle_itinerary_three_even_eoooee_of_ge_four hge h4 h

/-! ## Bunched EOOEOE -/

/-!
# Uniform bunched leftovers `O^a EOOEOE`

`OOOEOOEOE` is the first expanding instance. For `a ≥ 4` the mixed
cell is `z < (n+1)^4`. At `a = 3` the two-odd plus last-odd geometry
recovers the same tight comparison already used for `O^3 EOOOEE`.

Large `n` is `n ≥ 256`. Below `256`, `3 ≤ a ≤ 6` is a table and
`a ≥ 7` is seven consecutive odds.

This excludes that one bunched family only. It is not a length-8
or length-9 census and not a halt theorem. Paper A records the
family as Theorem 3.20.
-/

set_option exponentiation.threshold 16
set_option maxRecDepth 512
set_option maxHeartbeats 400000

theorem threeEvenEOOEOE_z_lt {n a : ℕ} (hn : 4 ≤ n)
    (h : CycleItinerary n (threeEvenEOOEOE a)) :
    image n (List.replicate a Branch.odd) < (n + 1) ^ 4 := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 4) hn
  set pref :=
    List.replicate a Branch.odd ++ [Branch.even, Branch.odd, Branch.odd]
  have hsplit : threeEvenEOOEOE a =
      pref ++ [Branch.even, Branch.odd, Branch.even] := by
    simp [threeEvenEOOEOE, pref]
  have hC : CycleItinerary n
      (pref ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [hsplit] using h
  have hy3 := cycle_eoe_suffix_y_cube_lt (u := pref) hC
  set z := image n (List.replicate a Branch.odd)
  set uimg := image n (List.replicate a Branch.odd ++ [Branch.even])
  set s := image n pref
  set y := image n (pref ++ [Branch.even])
  have hy3' : y ^ 3 < (n + 1) ^ 4 := by
    simpa [y, pref] using hy3
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.even,
        Branch.odd, Branch.even] :=
    follows_of_append_right (u := List.replicate a Branch.odd)
      (by simpa [threeEvenEOOEOE] using h.1)
  have he : z % 2 = 0 := hf.1
  have hueq : uimg = floorPower z := by
    simp [uimg, z, image_append, image]
  have hzlt : z < (uimg + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hueq.symm).2
  have huO : follows uimg (List.replicate 2 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even])
      (by simpa [uimg, hueq, image, List.replicate] using hf.2)
  have hu1 : 1 ≤ uimg := by
    have hz1 : 1 ≤ z := image_pos hn1 _
    simpa [uimg, hueq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := uimg) (a := 2) hu1 huO
  have hseq : s = image uimg (List.replicate 2 Branch.odd) := by
    simp [s, uimg, pref, image_append, image]
  have hle' : uimg ^ 9 ≤ 1024 * s ^ 4 := by
    simpa [denomBits_two, three_pow_two, two_pow_ten, hseq] using hpow
  have hf1 : follows uimg
      [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.even] := by
    simpa [uimg, hueq, image] using hf.2
  have hf2 : follows s [Branch.even, Branch.odd, Branch.even] := by
    have := follows_of_append_right (u := List.replicate 2 Branch.odd) hf1
    simpa [s, hseq, image, List.replicate] using this
  have hes : s % 2 = 0 := hf2.1
  have hyeq : y = floorPower s := by
    simp [y, s, pref, image_append, image]
  have hslt : s < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval hes).mp hyeq.symm).2
  have hs4 : s ^ 4 < (y + 1) ^ 8 :=
    pow_lt_of_lt_pow_mul (k := 2) (m := 4) hslt (by decide)
  have hu9 : uimg ^ 9 < 1024 * (y + 1) ^ 8 :=
    lt_of_le_of_lt hle'
      (Nat.mul_lt_mul_of_pos_left hs4 (by decide : (0 : ℕ) < 1024))
  have hA : 3 ≤ n + 1 := by omega
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hy3'
  exact z_lt_succ_pow4_of_y hzlt (eooeoe_u_lt_succ_sq hn hu9 hysucc)

theorem no_cycle_itinerary_three_even_eooeoe_of_ge_four {n a : ℕ}
    (hn : 256 ≤ n) (ha : 4 ≤ a) (h : CycleItinerary n (threeEvenEOOEOE a)) :
    False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hn4 : 4 ≤ n := le_trans (by decide : (4 : ℕ) ≤ 256) hn
  have hz := threeEvenEOOEOE_z_lt hn4 h
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.even,
        Branch.odd, Branch.even])
      (by simpa [threeEvenEOOEOE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hZ : ((n + 1) ^ 4) ^ (2 ^ a) = (n + 1) ^ (4 * 2 ^ a) :=
    (Nat.pow_mul (n + 1) 4 (2 ^ a)).symm
  exact leftover_prefix_preimage hpow hz
    (by simpa [hZ] using three_even_eooee_tail hn ha)

theorem no_cycle_itinerary_three_even_eooeoe_of_ge_three {n : ℕ}
    (hn : 256 ≤ n) (h : CycleItinerary n (threeEvenEOOEOE 3)) : False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hn197 : 197 ≤ n := le_trans (by decide : (197 : ℕ) ≤ 256) hn
  have hn24 : 24 ≤ n := le_trans (by decide : (24 : ℕ) ≤ 256) hn
  set z := image n (List.replicate 3 Branch.odd)
  set uimg := image n (List.replicate 3 Branch.odd ++ [Branch.even])
  set pref :=
    List.replicate 3 Branch.odd ++ [Branch.even, Branch.odd, Branch.odd]
  set s := image n pref
  set y := image n (pref ++ [Branch.even])
  have hueq : uimg = floorPower z := by
    simp [uimg, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.even,
        Branch.odd, Branch.even] :=
    follows_of_append_right (u := List.replicate 3 Branch.odd)
      (by simpa [threeEvenEOOEOE] using h.1)
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (uimg + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hueq.symm).2
  have hO : follows n (List.replicate 3 Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.even,
        Branch.odd, Branch.even])
      (by simpa [threeEvenEOOEOE] using h.1)
  have hpow := odd_run_lower_growth hn1 hO
  have hz8 : z ^ 8 < (uimg + 1) ^ 16 :=
    pow_lt_of_lt_pow_mul (k := 2) (m := 8) hzlt (by decide)
  have h27 : n ^ 27 < 2 ^ 38 * (uimg + 1) ^ 16 := by
    have hle : n ^ 27 ≤ 2 ^ 38 * z ^ 8 := by
      simpa [denomBits_three, three_pow_three, z] using hpow
    exact lt_of_le_of_lt hle
      (Nat.mul_lt_mul_of_pos_left hz8
        (pow_pos (by decide : (0 : ℕ) < 2) 38))
  have hC : CycleItinerary n
      (pref ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [threeEvenEOOEOE, pref] using h
  have hy3 := cycle_eoe_suffix_y_cube_lt (u := pref) hC
  have hy3' : y ^ 3 < (n + 1) ^ 4 := by
    simpa [y, pref] using hy3
  have huO : follows uimg (List.replicate 2 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even])
      (by simpa [uimg, hueq, image, List.replicate] using hf.2)
  have hu1 : 1 ≤ uimg := by
    have hz1 : 1 ≤ z := image_pos hn1 _
    simpa [uimg, hueq] using floorPower_pos hz1
  have hpowu := odd_run_lower_growth (n := uimg) (a := 2) hu1 huO
  have hseq : s = image uimg (List.replicate 2 Branch.odd) := by
    simp [s, uimg, pref, image_append, image]
  have hle' : uimg ^ 9 ≤ 1024 * s ^ 4 := by
    simpa [denomBits_two, three_pow_two, two_pow_ten, hseq] using hpowu
  have hf1 : follows uimg
      [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.even] := by
    simpa [uimg, hueq, image] using hf.2
  have hf2 : follows s [Branch.even, Branch.odd, Branch.even] := by
    have := follows_of_append_right (u := List.replicate 2 Branch.odd) hf1
    simpa [s, hseq, image, List.replicate] using this
  have hes : s % 2 = 0 := hf2.1
  have hyeq : y = floorPower s := by
    simp [y, s, pref, image_append, image]
  have hslt : s < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval hes).mp hyeq.symm).2
  have hs4 : s ^ 4 < (y + 1) ^ 8 :=
    pow_lt_of_lt_pow_mul (k := 2) (m := 4) hslt (by decide)
  have hu9 : uimg ^ 9 < 1024 * (y + 1) ^ 8 :=
    lt_of_le_of_lt hle'
      (Nat.mul_lt_mul_of_pos_left hs4 (by decide : (0 : ℕ) < 1024))
  have hA : 3 ≤ n + 1 := by omega
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hy3'
  have hu27 : uimg ^ 27 < 2 ^ 38 * (n + 1) ^ 32 :=
    eooeoe_u_pow27 hu9 hysucc
  cases lt_or_ge uimg 39 with
  | inl hlt => exact eoooee_small_y_false hn24 hlt h27
  | inr hge => exact eoooee_large_y_false hn197 hge hu27 h27

theorem threeEvenEOOEOE_follows_seven_odds {n a : ℕ}
    (ha : 7 ≤ a) (h : CycleItinerary n (threeEvenEOOEOE a)) :
    follows n sevenOdds := by
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.even,
        Branch.odd, Branch.even])
      (by simpa [threeEvenEOOEOE] using h.1)
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycle_itinerary_three_even_eooeoe_of_lt {n a : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 256) (ha3 : 3 ≤ a) (ha6 : a ≤ 6)
    (h : CycleItinerary n (threeEvenEOOEOE a)) : False := by
  have hA : a - 3 < 4 := by omega
  have hfalse :
      cycleItineraryB n (threeEvenEOOEOE (a - 3 + 3)) = false :=
    cycleItineraryB_eooeoe_prefix_lt256 ⟨n, hn⟩ ⟨a - 3, hA⟩ hn2
  have ha : a - 3 + 3 = a := by omega
  have hfalse' : cycleItineraryB n (threeEvenEOOEOE a) = false := by
    simpa [ha] using hfalse
  have htrue : cycleItineraryB n (threeEvenEOOEOE a) = true :=
    cycleItineraryB_iff.mpr h
  rw [hfalse'] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_three_even_eooeoe {n a : ℕ} (hn : 2 ≤ n) (ha : 3 ≤ a) :
    ¬CycleItinerary n
      (List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.even,
          Branch.odd, Branch.even]) := by
  intro h
  cases lt_or_ge n 256 with
  | inl hlt =>
      have hcases : a ≤ 6 ∨ 7 ≤ a := by omega
      rcases hcases with hle | hge
      · exact no_cycle_itinerary_three_even_eooeoe_of_lt hn hlt ha hle h
      · exact no_follows_seven_odds_of_lt256 hn hlt
          (threeEvenEOOEOE_follows_seven_odds hge h)
  | inr hge =>
      have hcases : a = 3 ∨ 4 ≤ a := by omega
      rcases hcases with h3 | h4
      · subst h3
        exact no_cycle_itinerary_three_even_eooeoe_of_ge_three hge h
      · exact no_cycle_itinerary_three_even_eooeoe_of_ge_four hge h4 h

/-! ## First-E transport -/

/-!
# First-E transport of the uniform two-even tail

On a `CycleMin` the remainder after the first even letter of a
gapped three-even leftover is a two-even leftover family, started
at `y ≥ n`. The leftover one-step preimage is measured against the cycle start
`n`, so `y ≥ n` tightens it against the shared two-even tail at
`y`. Large `y` is the uniform cutoff `y ≥ 256`. Below `256`, short
gaps are tables and long gaps are seven-odd.

This excludes gapped `CycleMin`s only. It is not a `CycleItinerary`
theorem at a non-minimum start, not a bunched-tail attack, not a
length-8 or length-9 census, and not a halt theorem. Paper A
records the transport as Theorem 3.13.
-/

theorem four_mul_two_pow (b : ℕ) : 4 * 2 ^ b = 2 ^ (b + 2) := by
  have h4 : (4 : ℕ) = 2 ^ 2 := rfl
  rw [h4, ← Nat.pow_add]
  congr 1
  omega

theorem gappedThreeEvenEE_eq_twoEven (a b : ℕ) :
    gappedThreeEvenEE a b = firstEPrefix a ++ twoEvenEE (b + 2) := by
  have hb : b + 2 - 2 = b := Nat.add_sub_cancel b 2
  simp [gappedThreeEvenEE, twoEvenEE, hb, List.append_assoc]

theorem gappedThreeEvenEOE_eq_twoEven (a b : ℕ) :
    gappedThreeEvenEOE a b = firstEPrefix a ++ twoEvenEOE (b + 3) := by
  have hb : b + 3 - 3 = b := Nat.add_sub_cancel b 3
  simp [gappedThreeEvenEOE, twoEvenEOE, hb, List.append_assoc]

theorem gappedThreeEvenEE_length (a b : ℕ) :
    (gappedThreeEvenEE a b).length = a + b + 3 := by
  simp [gappedThreeEvenEE, firstEPrefix, List.length_append, List.length_replicate]
  omega

theorem gappedThreeEvenEOE_length (a b : ℕ) :
    (gappedThreeEvenEOE a b).length = a + b + 4 := by
  simp [gappedThreeEvenEOE, firstEPrefix, List.length_append, List.length_replicate]
  omega

theorem firstEPrefix_length (a : ℕ) : (firstEPrefix a).length = a + 1 := by
  simp [firstEPrefix, List.length_append, List.length_replicate]

theorem firstEPrefix_image (n a : ℕ) :
    image n (firstEPrefix a) = floorPower^[a + 1] n := by
  simp [firstEPrefix, image_eq_iterate, List.length_append, List.length_replicate]

theorem cycleMin_gapped_ee_y_ge {n a b : ℕ}
    (h : CycleMin n (gappedThreeEvenEE a b)) :
    n ≤ image n (firstEPrefix a) := by
  have hlen := gappedThreeEvenEE_length a b
  have hj : a + 1 < (gappedThreeEvenEE a b).length := by omega
  have : n ≤ floorPower^[a + 1] n := cycleMin_ge h hj
  simpa [firstEPrefix_image] using this

theorem cycleMin_gapped_eoe_y_ge {n a b : ℕ}
    (h : CycleMin n (gappedThreeEvenEOE a b)) :
    n ≤ image n (firstEPrefix a) := by
  have hlen := gappedThreeEvenEOE_length a b
  have hj : a + 1 < (gappedThreeEvenEOE a b).length := by omega
  have : n ≤ floorPower^[a + 1] n := cycleMin_ge h hj
  simpa [firstEPrefix_image] using this

theorem follows_gapped_ee_prefix {n a b : ℕ}
    (h : follows n (gappedThreeEvenEE a b)) : follows n (firstEPrefix a) :=
  follows_of_append_left
    (v := List.replicate b Branch.odd ++ [Branch.even, Branch.even])
    (by simpa [gappedThreeEvenEE, List.append_assoc] using h)

theorem follows_gapped_eoe_prefix {n a b : ℕ}
    (h : follows n (gappedThreeEvenEOE a b)) : follows n (firstEPrefix a) :=
  follows_of_append_left
    (v := List.replicate b Branch.odd ++
      [Branch.even, Branch.odd, Branch.even])
    (by simpa [gappedThreeEvenEOE, List.append_assoc] using h)

theorem follows_gapped_ee_remaining_odds {n a b : ℕ}
    (h : follows n (gappedThreeEvenEE a b)) :
    follows (image n (firstEPrefix a)) (List.replicate b Branch.odd) :=
  follows_of_append_left (v := [Branch.even, Branch.even])
    (follows_of_append_right (u := firstEPrefix a)
      (by simpa [gappedThreeEvenEE, List.append_assoc] using h))

theorem follows_gapped_eoe_remaining_odds {n a b : ℕ}
    (h : follows n (gappedThreeEvenEOE a b)) :
    follows (image n (firstEPrefix a)) (List.replicate b Branch.odd) :=
  follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even])
    (follows_of_append_right (u := firstEPrefix a)
      (by simpa [gappedThreeEvenEOE, List.append_assoc] using h))

theorem firstEPrefix_image_ge_two {n a : ℕ}
    (hn : 2 ≤ n) (ha : 1 ≤ a) (h : follows n (firstEPrefix a)) :
    2 ≤ image n (firstEPrefix a) := by
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left (v := [Branch.even]) (by simpa [firstEPrefix] using h)
  have hcons : List.replicate a Branch.odd =
      Branch.odd :: List.replicate (a - 1) Branch.odd := by
    cases a with
    | zero => exact (Nat.not_succ_le_zero 0 ha).elim
    | succ a => rfl
  have hnOdd : n % 2 = 1 := by
    have : follows n (Branch.odd :: List.replicate (a - 1) Branch.odd) := by
      simpa [hcons] using hO
    exact this.1
  have hn3 : 3 ≤ n := by omega
  have hz : n < image n (List.replicate a Branch.odd) := by
    simpa [image_eq_iterate, List.length_replicate] using
      odd_itinerary_expands hn3 ha hO
  have hz4 : 4 ≤ image n (List.replicate a Branch.odd) := by omega
  have he : image n (List.replicate a Branch.odd) % 2 = 0 := by
    have hf : follows (image n (List.replicate a Branch.odd)) [Branch.even] :=
      follows_of_append_right (u := List.replicate a Branch.odd)
        (by simpa [firstEPrefix] using h)
    change _ % 2 = 0 ∧ follows (floorPower _) [] at hf
    exact hf.1
  have hy : image n (firstEPrefix a) =
      (image n (List.replicate a Branch.odd)).sqrt := by
    simp [firstEPrefix, image_append, image, floorPower_even_eq he]
  have : 2 ≤ (image n (List.replicate a Branch.odd)).sqrt :=
    Nat.le_sqrt.mpr (by simpa [pow_two] using hz4)
  simpa [hy] using this

theorem gapped_ee_preimage {n a b : ℕ}
    (hy : 1 ≤ image n (firstEPrefix a))
    (h : CycleItinerary n (gappedThreeEvenEE a b)) :
    image n (firstEPrefix a) ^ (3 ^ b) <
      2 ^ denomBits b * (n + 1) ^ (2 ^ (b + 2)) := by
  set y := image n (firstEPrefix a)
  set v := firstEPrefix a ++ List.replicate b Branch.odd
  have hsplit : gappedThreeEvenEE a b =
      v ++ List.replicate 2 Branch.even := by
    simp [gappedThreeEvenEE, v, List.append_assoc]
  have hC : CycleItinerary n (v ++ List.replicate 2 Branch.even) := by
    simpa [hsplit] using h
  have hz := cycle_trailing_evens_lt (r := 2) (by decide) hC
  have hO : follows y (List.replicate b Branch.odd) :=
    follows_gapped_ee_remaining_odds h.1
  have hpow := odd_run_lower_growth hy hO
  have himg : image y (List.replicate b Branch.odd) = image n v := by
    simp [y, v, image_append]
  have hz' : image y (List.replicate b Branch.odd) < (n + 1) ^ 4 := by
    simpa [himg] using hz
  have hm : 2 ^ b ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow :
      image y (List.replicate b Branch.odd) ^ (2 ^ b) <
        (n + 1) ^ (2 ^ (b + 2)) := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 2 ^ b) hz' hm
    rwa [four_mul_two_pow b] at this
  exact lt_of_le_of_lt hpow
    (Nat.mul_lt_mul_of_pos_left hzpow
      (pow_pos (by decide : (0 : ℕ) < 2) _))

theorem gapped_eoe_preimage {n a b : ℕ}
    (hn : 2 ≤ n) (hy : 1 ≤ image n (firstEPrefix a))
    (h : CycleItinerary n (gappedThreeEvenEOE a b)) :
    image n (firstEPrefix a) ^ (3 ^ (b + 1)) <
      2 ^ denomBits (b + 1) * (n + 1) ^ (2 ^ (b + 3)) := by
  set y := image n (firstEPrefix a)
  set u := List.replicate b Branch.odd
  set z := image y u
  set w := image y (u ++ [Branch.even])
  have hC' : CycleItinerary n
      ((firstEPrefix a ++ u) ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [gappedThreeEvenEOE, List.append_assoc] using h
  have hO : follows y u := follows_gapped_eoe_remaining_odds h.1
  have he : z % 2 = 0 := by
    have hf : follows y (u ++ [Branch.even, Branch.odd, Branch.even]) :=
      follows_of_append_right (u := firstEPrefix a)
        (by simpa [gappedThreeEvenEOE, List.append_assoc] using h.1)
    have hfE : follows z [Branch.even, Branch.odd, Branch.even] :=
      follows_of_append_right (u := u) hf
    change z % 2 = 0 ∧ follows (floorPower z) [Branch.odd, Branch.even] at hfE
    exact hfE.1
  have hyeq : floorPower z = w := by
    simp [z, w, u, image_append, image]
  have hzlt : z < (w + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq).2
  have hpow := odd_run_lower_growth hy hO
  have hm : 2 ^ b ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow : z ^ (2 ^ b) < (w + 1) ^ (2 ^ (b + 1)) := by
    have := pow_lt_of_lt_pow_mul (k := 2) (m := 2 ^ b) hzlt hm
    rwa [two_mul_two_pow b] at this
  have hmid : y ^ (3 ^ b) <
      2 ^ denomBits b * (w + 1) ^ (2 ^ (b + 1)) :=
    lt_of_le_of_lt hpow
      (Nat.mul_lt_mul_of_pos_left hzpow
        (pow_pos (by decide : (0 : ℕ) < 2) _))
  have hcube : y ^ (3 ^ (b + 1)) <
      2 ^ (3 * denomBits b) * (w + 1) ^ (3 * 2 ^ (b + 1)) := by
    have hlt : (y ^ (3 ^ b)) ^ 3 <
        (2 ^ denomBits b * (w + 1) ^ (2 ^ (b + 1))) ^ 3 :=
      Nat.pow_lt_pow_left hmid (by decide : (3 : ℕ) ≠ 0)
    have hL : (y ^ (3 ^ b)) ^ 3 = y ^ (3 ^ (b + 1)) := by
      rw [← Nat.pow_mul, ← Nat.pow_succ]
    have hR : (2 ^ denomBits b * (w + 1) ^ (2 ^ (b + 1))) ^ 3 =
        2 ^ (3 * denomBits b) * (w + 1) ^ (3 * 2 ^ (b + 1)) :=
      two_mul_pow_cube _ _ _
    rwa [hL, hR] at hlt
  have hw3 : w ^ 3 < (n + 1) ^ 4 := by
    have hcube' := cycle_eoe_suffix_y_cube_lt (u := firstEPrefix a ++ u) hC'
    simpa [w, y, u, image_append, List.append_assoc] using hcube'
  have hA : 3 ≤ n + 1 := by omega
  have hwsucc : (w + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hw3
  have hwraise : (w + 1) ^ (3 * 2 ^ (b + 1)) <
      2 ^ (2 ^ (b + 1)) * (n + 1) ^ (2 ^ (b + 3)) := by
    have hm' : 2 ^ (b + 1) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
    have hlt : ((w + 1) ^ 3) ^ (2 ^ (b + 1)) <
        (2 * (n + 1) ^ 4) ^ (2 ^ (b + 1)) :=
      Nat.pow_lt_pow_left hwsucc hm'
    have hL : ((w + 1) ^ 3) ^ (2 ^ (b + 1)) =
        (w + 1) ^ (3 * 2 ^ (b + 1)) :=
      (Nat.pow_mul (w + 1) 3 (2 ^ (b + 1))).symm
    have hR : (2 * (n + 1) ^ 4) ^ (2 ^ (b + 1)) =
        2 ^ (2 ^ (b + 1)) * (n + 1) ^ (4 * 2 ^ (b + 1)) := by
      rw [mul_pow, Nat.pow_mul]
    have hexp : 4 * 2 ^ (b + 1) = 2 ^ (b + 3) := by
      have h4 : (4 : ℕ) = 2 ^ 2 := rfl
      rw [h4, ← Nat.pow_add]
      congr 1
      omega
    rw [hL, hR, hexp] at hlt
    exact hlt
  have hmid' : y ^ (3 ^ (b + 1)) <
      2 ^ (3 * denomBits b) *
        (2 ^ (2 ^ (b + 1)) * (n + 1) ^ (2 ^ (b + 3))) :=
    lt_trans hcube
      (Nat.mul_lt_mul_of_pos_left hwraise
        (pow_pos (by decide : (0 : ℕ) < 2) _))
  have hexp :
      2 ^ (3 * denomBits b) *
          (2 ^ (2 ^ (b + 1)) * (n + 1) ^ (2 ^ (b + 3))) =
        2 ^ (3 * denomBits b + 2 ^ (b + 1)) * (n + 1) ^ (2 ^ (b + 3)) := by
    rw [← mul_assoc, ← Nat.pow_add]
  have hbits : 3 * denomBits b + 2 ^ (b + 1) = denomBits (b + 1) :=
    (denomBits_succ b).symm
  rwa [hexp, hbits] at hmid'

theorem no_cycleMin_gapped_three_even_ee_of_y {n a b : ℕ}
    (hb : 4 ≤ b) (h : CycleMin n (gappedThreeEvenEE a b))
    (hy : 256 ≤ image n (firstEPrefix a)) : False := by
  set y := image n (firstEPrefix a)
  have hC : CycleItinerary n (gappedThreeEvenEE a b) := cycleMin_cycleItinerary h
  have hyn : n ≤ y := cycleMin_gapped_ee_y_ge h
  have hy1 : 1 ≤ y := le_trans (by decide : (1 : ℕ) ≤ 256) hy
  have hcell := gapped_ee_preimage (n := n) (a := a) (b := b) hy1 hC
  have hk : 6 ≤ b + 2 := by omega
  have htail := shared_two_even_tail (n := y) hy hk
  have hle : (n + 1) ^ (2 ^ (b + 2)) ≤ (y + 1) ^ (2 ^ (b + 2)) :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _
  have hlt : y ^ (3 ^ b) <
      2 ^ denomBits b * (y + 1) ^ (2 ^ (b + 2)) :=
    lt_of_lt_of_le hcell (Nat.mul_le_mul_left _ hle)
  have hbits : b + 2 - 2 = b := Nat.add_sub_cancel b 2
  have htail' : 2 ^ denomBits b * (y + 1) ^ (2 ^ (b + 2)) < y ^ (3 ^ b) := by
    simpa [hbits] using htail
  exact (not_lt_of_gt htail') hlt

theorem no_cycleMin_gapped_three_even_eoe_of_y {n a b : ℕ}
    (hn : 2 ≤ n) (hb : 3 ≤ b) (h : CycleMin n (gappedThreeEvenEOE a b))
    (hy : 256 ≤ image n (firstEPrefix a)) : False := by
  set y := image n (firstEPrefix a)
  have hC : CycleItinerary n (gappedThreeEvenEOE a b) := cycleMin_cycleItinerary h
  have hyn : n ≤ y := cycleMin_gapped_eoe_y_ge h
  have hy1 : 1 ≤ y := le_trans (by decide : (1 : ℕ) ≤ 256) hy
  have hcell := gapped_eoe_preimage hn hy1 hC
  have hk : 6 ≤ b + 3 := by omega
  have htail := shared_two_even_tail (n := y) hy hk
  have hle : (n + 1) ^ (2 ^ (b + 3)) ≤ (y + 1) ^ (2 ^ (b + 3)) :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _
  have hlt : y ^ (3 ^ (b + 1)) <
      2 ^ denomBits (b + 1) * (y + 1) ^ (2 ^ (b + 3)) :=
    lt_of_lt_of_le hcell (Nat.mul_le_mul_left _ hle)
  have hbits : b + 3 - 2 = b + 1 := by omega
  have htail' :
      2 ^ denomBits (b + 1) * (y + 1) ^ (2 ^ (b + 3)) <
        y ^ (3 ^ (b + 1)) := by
    simpa [hbits] using htail
  exact (not_lt_of_gt htail') hlt

theorem gapped_ee_prefix_seven_odds {n a b : ℕ}
    (ha : 7 ≤ a) (h : CycleItinerary n (gappedThreeEvenEE a b)) :
    follows n sevenOdds := by
  have hP := follows_gapped_ee_prefix h.1
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left (v := [Branch.even])
      (by simpa [firstEPrefix] using hP)
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem gapped_eoe_prefix_seven_odds {n a b : ℕ}
    (ha : 7 ≤ a) (h : CycleItinerary n (gappedThreeEvenEOE a b)) :
    follows n sevenOdds := by
  have hP := follows_gapped_eoe_prefix h.1
  have hO : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left (v := [Branch.even])
      (by simpa [firstEPrefix] using hP)
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem gapped_ee_remaining_seven_odds {n a b : ℕ}
    (hb : 7 ≤ b) (h : CycleItinerary n (gappedThreeEvenEE a b)) :
    follows (image n (firstEPrefix a)) sevenOdds := by
  have hO := follows_gapped_ee_remaining_odds h.1
  have hsplit : List.replicate b Branch.odd =
      sevenOdds ++ List.replicate (b - 7) Branch.odd := by
    have hsum : 7 + (b - 7) = b := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (b - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem gapped_eoe_remaining_seven_odds {n a b : ℕ}
    (hb : 7 ≤ b) (h : CycleItinerary n (gappedThreeEvenEOE a b)) :
    follows (image n (firstEPrefix a)) sevenOdds := by
  have hO := follows_gapped_eoe_remaining_odds h.1
  have hsplit : List.replicate b Branch.odd =
      sevenOdds ++ List.replicate (b - 7) Branch.odd := by
    have hsum : 7 + (b - 7) = b := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (b - 7) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycle_itinerary_gapped_ee_short_of_lt {n a b : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 256) (ha2 : 2 ≤ a) (ha6 : a ≤ 6)
    (hb4 : 4 ≤ b) (hb6 : b ≤ 6)
    (h : CycleItinerary n (gappedThreeEvenEE a b)) : False := by
  have hA : a - 2 < 5 := by omega
  have hB : b - 4 < 3 := by omega
  have hfalse :
      cycleItineraryB n (gappedThreeEvenEE (a - 2 + 2) (b - 4 + 4)) = false :=
    cycleItineraryB_gapped_ee_short_lt256 ⟨n, hn⟩ ⟨a - 2, hA⟩ ⟨b - 4, hB⟩ hn2
  have ha : a - 2 + 2 = a := by omega
  have hb : b - 4 + 4 = b := by omega
  have hfalse' : cycleItineraryB n (gappedThreeEvenEE a b) = false := by
    simpa [ha, hb] using hfalse
  have htrue : cycleItineraryB n (gappedThreeEvenEE a b) = true :=
    cycleItineraryB_iff.mpr h
  rw [hfalse'] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_gapped_eoe_short_of_lt {n a b : ℕ}
    (hn2 : 2 ≤ n) (hn : n < 256) (ha2 : 2 ≤ a) (ha6 : a ≤ 6)
    (hb3 : 3 ≤ b) (hb6 : b ≤ 6)
    (h : CycleItinerary n (gappedThreeEvenEOE a b)) : False := by
  have hA : a - 2 < 5 := by omega
  have hB : b - 3 < 4 := by omega
  have hfalse :
      cycleItineraryB n (gappedThreeEvenEOE (a - 2 + 2) (b - 3 + 3)) = false :=
    cycleItineraryB_gapped_eoe_short_lt256 ⟨n, hn⟩ ⟨a - 2, hA⟩ ⟨b - 3, hB⟩ hn2
  have ha : a - 2 + 2 = a := by omega
  have hb : b - 3 + 3 = b := by omega
  have hfalse' : cycleItineraryB n (gappedThreeEvenEOE a b) = false := by
    simpa [ha, hb] using hfalse
  have htrue : cycleItineraryB n (gappedThreeEvenEOE a b) = true :=
    cycleItineraryB_iff.mpr h
  rw [hfalse'] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycleMin_gapped_three_even_ee_of_lt {n a b : ℕ}
    (hn : 2 ≤ n) (hnlt : n < 256) (ha : 2 ≤ a) (hb : 4 ≤ b)
    (h : CycleMin n (gappedThreeEvenEE a b)) : False := by
  have hC : CycleItinerary n (gappedThreeEvenEE a b) := cycleMin_cycleItinerary h
  cases lt_or_ge a 7 with
  | inr ha7 =>
      exact no_follows_seven_odds_of_lt256 hn hnlt
        (gapped_ee_prefix_seven_odds ha7 hC)
  | inl ha6 =>
      have hP := follows_gapped_ee_prefix hC.1
      have ha1 : 1 ≤ a := le_trans (by decide : (1 : ℕ) ≤ 2) ha
      set y := image n (firstEPrefix a)
      cases lt_or_ge y 256 with
      | inr hyge =>
          exact no_cycleMin_gapped_three_even_ee_of_y hb h hyge
      | inl hylt =>
          have hy2 : 2 ≤ y := firstEPrefix_image_ge_two hn ha1 hP
          cases lt_or_ge b 7 with
          | inr hb7 =>
              exact no_follows_seven_odds_of_lt256 hy2 hylt
                (gapped_ee_remaining_seven_odds hb7 hC)
          | inl hb6 =>
              exact no_cycle_itinerary_gapped_ee_short_of_lt hn hnlt ha
                (Nat.le_of_lt_succ ha6) hb (Nat.le_of_lt_succ hb6) hC

theorem no_cycleMin_gapped_three_even_eoe_of_lt {n a b : ℕ}
    (hn : 2 ≤ n) (hnlt : n < 256) (ha : 2 ≤ a) (hb : 3 ≤ b)
    (h : CycleMin n (gappedThreeEvenEOE a b)) : False := by
  have hC : CycleItinerary n (gappedThreeEvenEOE a b) := cycleMin_cycleItinerary h
  cases lt_or_ge a 7 with
  | inr ha7 =>
      exact no_follows_seven_odds_of_lt256 hn hnlt
        (gapped_eoe_prefix_seven_odds ha7 hC)
  | inl ha6 =>
      have hP := follows_gapped_eoe_prefix hC.1
      have ha1 : 1 ≤ a := le_trans (by decide : (1 : ℕ) ≤ 2) ha
      set y := image n (firstEPrefix a)
      cases lt_or_ge y 256 with
      | inr hyge =>
          exact no_cycleMin_gapped_three_even_eoe_of_y hn hb h hyge
      | inl hylt =>
          have hy2 : 2 ≤ y := firstEPrefix_image_ge_two hn ha1 hP
          cases lt_or_ge b 7 with
          | inr hb7 =>
              exact no_follows_seven_odds_of_lt256 hy2 hylt
                (gapped_eoe_remaining_seven_odds hb7 hC)
          | inl hb6 =>
              exact no_cycle_itinerary_gapped_eoe_short_of_lt hn hnlt ha
                (Nat.le_of_lt_succ ha6) hb (Nat.le_of_lt_succ hb6) hC

theorem no_cycleMin_gapped_three_even_ee {n a b : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (hb : 4 ≤ b) :
    ¬CycleMin n
      (List.replicate a Branch.odd ++ [Branch.even] ++
        List.replicate b Branch.odd ++ [Branch.even, Branch.even]) := by
  intro h
  have hw : gappedThreeEvenEE a b =
      List.replicate a Branch.odd ++ [Branch.even] ++
        List.replicate b Branch.odd ++ [Branch.even, Branch.even] := by
    simp [gappedThreeEvenEE, firstEPrefix, List.append_assoc]
  have h' : CycleMin n (gappedThreeEvenEE a b) := by
    simpa [hw] using h
  cases lt_or_ge n 256 with
  | inl hlt => exact no_cycleMin_gapped_three_even_ee_of_lt hn hlt ha hb h'
  | inr hge =>
      have hy : 256 ≤ image n (firstEPrefix a) :=
        le_trans hge (cycleMin_gapped_ee_y_ge h')
      exact no_cycleMin_gapped_three_even_ee_of_y hb h' hy

theorem no_cycleMin_gapped_three_even_eoe {n a b : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (hb : 3 ≤ b) :
    ¬CycleMin n
      (List.replicate a Branch.odd ++ [Branch.even] ++
        List.replicate b Branch.odd ++
        [Branch.even, Branch.odd, Branch.even]) := by
  intro h
  have hw : gappedThreeEvenEOE a b =
      List.replicate a Branch.odd ++ [Branch.even] ++
        List.replicate b Branch.odd ++
        [Branch.even, Branch.odd, Branch.even] := by
    simp [gappedThreeEvenEOE, firstEPrefix, List.append_assoc]
  have h' : CycleMin n (gappedThreeEvenEOE a b) := by
    simpa [hw] using h
  cases lt_or_ge n 256 with
  | inl hlt => exact no_cycleMin_gapped_three_even_eoe_of_lt hn hlt ha hb h'
  | inr hge =>
      have hy : 256 ≤ image n (firstEPrefix a) :=
        le_trans hge (cycleMin_gapped_eoe_y_ge h')
      exact no_cycleMin_gapped_three_even_eoe_of_y hn hb h' hy

/-! ## Gapped CycleItinerary by rotation -/

/-!
# Gapped three-even leftovers as `CycleItinerary`s

First-E transport excludes the gapped leftovers only as `CycleMin`s.
Every rotation is already an excluded `CycleMin` orientation, so
`exists_cycleMin` upgrades both families to `CycleItinerary`.

Not a length-8 or length-9 census and not a halt theorem. Paper A
records the families as Theorem 3.21.
-/

theorem rotateItinerary_cons {w : List Branch} {k : ℕ} (hk : k < w.length) :
    rotateItinerary w k = w[k] :: (w.drop (k + 1) ++ w.take k) := by
  rw [rotateItinerary_eq_drop_append_take w k (Nat.le_of_lt hk),
    List.drop_eq_getElem_cons hk, List.cons_append]

theorem rotateItinerary_cons_cons {w : List Branch} {k : ℕ}
    (hk : k + 1 < w.length) :
    rotateItinerary w k =
      w[k] :: w[k + 1] :: (w.drop (k + 2) ++ w.take k) := by
  have hk0 : k < w.length := Nat.lt_of_succ_lt hk
  rw [rotateItinerary_cons hk0, List.drop_eq_getElem_cons hk, List.cons_append]

theorem take_snoc {w : List Branch} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ w.length) :
    w.take k = w.take (k - 1) ++
      [w[k - 1]'(Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt hk0) hk)] := by
  have hi : k - 1 < w.length :=
    Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt hk0) hk
  have h := List.take_succ_eq_append_getElem (l := w) (i := k - 1) hi
  have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk0)
  rw [hsucc] at h
  exact h

theorem rotateItinerary_snoc {w : List Branch} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ w.length) :
    rotateItinerary w k =
      (w.drop k ++ w.take (k - 1)) ++
        [w[k - 1]'(Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt hk0) hk)] := by
  rw [rotateItinerary_eq_drop_append_take w k hk, take_snoc hk0 hk,
    List.append_assoc]

theorem cycleMin_of_rotate_ends_odd {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k ≤ w.length)
    (hodd : w[k - 1]'(Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt hk0) hk) =
      Branch.odd)
    (h : CycleMin n (rotateItinerary w k)) : False := by
  rw [rotateItinerary_snoc hk0 hk, hodd] at h
  exact cycleMin_not_end_odd hn h

theorem cycleMin_rotate_start_even {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (hk : k < w.length)
    (he : w[k] = Branch.even)
    (h : CycleMin n (rotateItinerary w k)) : False := by
  rw [rotateItinerary_cons hk, he] at h
  exact cycleMin_not_start_even hn h

theorem cycleMin_rotate_start_OE {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (hk : k + 1 < w.length)
    (ho : w[k] = Branch.odd) (he : w[k + 1] = Branch.even)
    (h : CycleMin n (rotateItinerary w k)) : False := by
  rw [rotateItinerary_cons_cons hk, ho, he] at h
  exact cycleMin_not_odd_even hn h

theorem getElem_of_list_eq {w w' : List Branch} (h : w = w') {i : ℕ}
    (hi : i < w.length) :
    w[i] = w'[i]'(by rw [← h]; exact hi) := by
  subst h; rfl

theorem getElem_nat_eq {w : List Branch} {i j : ℕ} (h : i = j)
    (hi : i < w.length) :
    w[i] = w[j]'(by rw [← h]; exact hi) := by
  subst h; rfl

theorem gapped_ee_as_prefix (a b : ℕ) :
    gappedThreeEvenEE a b =
      firstEPrefix a ++
        (List.replicate b Branch.odd ++ [Branch.even, Branch.even]) := by
  simp [gappedThreeEvenEE]

theorem gapped_eoe_as_prefix (a b : ℕ) :
    gappedThreeEvenEOE a b =
      firstEPrefix a ++
        (List.replicate b Branch.odd ++
          [Branch.even, Branch.odd, Branch.even]) := by
  simp [gappedThreeEvenEOE]

theorem gapped_ee_expanded (a b : ℕ) :
    gappedThreeEvenEE a b =
      List.replicate a Branch.odd ++ [Branch.even] ++
        List.replicate b Branch.odd ++ [Branch.even, Branch.even] := by
  simp [gappedThreeEvenEE, firstEPrefix, List.append_assoc]

theorem gapped_eoe_expanded (a b : ℕ) :
    gappedThreeEvenEOE a b =
      List.replicate a Branch.odd ++ [Branch.even] ++
        List.replicate b Branch.odd ++
        [Branch.even, Branch.odd, Branch.even] := by
  simp [gappedThreeEvenEOE, firstEPrefix, List.append_assoc]

theorem firstEPrefix_get_lt {a i : ℕ} (hia : i < a) :
    (firstEPrefix a)[i]'(by simp [firstEPrefix_length]; omega) =
      Branch.odd := by
  have hiL : i < (List.replicate a Branch.odd).length := by
    simp [List.length_replicate]; exact hia
  simp [firstEPrefix, List.getElem_append_left hiL, List.getElem_replicate]

theorem firstEPrefix_get_last (a : ℕ) :
    (firstEPrefix a)[a]'(by simp [firstEPrefix_length]) = Branch.even := by
  have hge : (List.replicate a Branch.odd).length ≤ a := by
    simp [List.length_replicate]
  simp [firstEPrefix, List.getElem_append_right hge]

theorem gappedThreeEvenEE_get_lt_a {a b i : ℕ} (hia : i < a) :
    (gappedThreeEvenEE a b)[i]'(by
        have := gappedThreeEvenEE_length a b; omega) =
      Branch.odd := by
  have hi : i < (gappedThreeEvenEE a b).length := by
    have := gappedThreeEvenEE_length a b; omega
  have hiL : i < (firstEPrefix a).length := by
    simp [firstEPrefix_length]; omega
  rw [getElem_of_list_eq (gapped_ee_as_prefix a b) hi,
    List.getElem_append_left hiL]
  exact firstEPrefix_get_lt hia

theorem gappedThreeEvenEE_get_a {a b : ℕ} :
    (gappedThreeEvenEE a b)[a]'(by
        have := gappedThreeEvenEE_length a b; omega) =
      Branch.even := by
  have hi : a < (gappedThreeEvenEE a b).length := by
    have := gappedThreeEvenEE_length a b; omega
  have hiL : a < (firstEPrefix a).length := by
    simp [firstEPrefix_length]
  rw [getElem_of_list_eq (gapped_ee_as_prefix a b) hi,
    List.getElem_append_left hiL]
  exact firstEPrefix_get_last a

theorem gappedThreeEvenEE_get_mid {a b i : ℕ}
    (hgt : a < i) (hlt : i < a + b + 1) :
    (gappedThreeEvenEE a b)[i]'(by
        have := gappedThreeEvenEE_length a b; omega) =
      Branch.odd := by
  have hi : i < (gappedThreeEvenEE a b).length := by
    have := gappedThreeEvenEE_length a b; omega
  have hge : (firstEPrefix a).length ≤ i := by
    simp [firstEPrefix_length]; omega
  have hiL : i - (a + 1) < (List.replicate b Branch.odd).length := by
    simp [List.length_replicate]; omega
  rw [getElem_of_list_eq (gapped_ee_as_prefix a b) hi,
    List.getElem_append_right hge]
  simp [firstEPrefix_length, List.getElem_append_left hiL,
    List.getElem_replicate]

theorem gappedThreeEvenEE_get_last {a b : ℕ} :
    (gappedThreeEvenEE a b)[a + b + 2]'(by
        have := gappedThreeEvenEE_length a b; omega) =
      Branch.even := by
  have hi : a + b + 2 < (gappedThreeEvenEE a b).length := by
    have := gappedThreeEvenEE_length a b; omega
  have hge : (firstEPrefix a).length ≤ a + b + 2 := by
    simp [firstEPrefix_length]; omega
  have hge2 : (List.replicate b Branch.odd).length ≤ b + 1 := by
    simp [List.length_replicate]
  have hidx : a + b + 2 - (firstEPrefix a).length = b + 1 := by
    rw [firstEPrefix_length]; omega
  have hiR : a + b + 2 - (firstEPrefix a).length <
      (List.replicate b Branch.odd ++ [Branch.even, Branch.even]).length := by
    simp [List.length_replicate]; omega
  rw [getElem_of_list_eq (gapped_ee_as_prefix a b) hi,
    List.getElem_append_right hge, getElem_nat_eq hidx hiR,
    List.getElem_append_right hge2]
  simp [List.length_replicate]

theorem gappedThreeEvenEE_pred_odd {a b k : ℕ}
    (hk0 : 0 < k) (hk : k < a + b + 3) (hne1 : k ≠ a + 1)
    (hne2 : k ≠ a + b + 2) :
    (gappedThreeEvenEE a b)[k - 1]'(by
        have := gappedThreeEvenEE_length a b; omega) =
      Branch.odd := by
  cases lt_or_ge (k - 1) a with
  | inl hlt => exact gappedThreeEvenEE_get_lt_a hlt
  | inr hge =>
      have hgt : a < k - 1 := lt_of_le_of_ne hge (by omega)
      exact gappedThreeEvenEE_get_mid hgt (by omega)

theorem gappedThreeEvenEOE_get_lt_a {a b i : ℕ} (hia : i < a) :
    (gappedThreeEvenEOE a b)[i]'(by
        have := gappedThreeEvenEOE_length a b; omega) =
      Branch.odd := by
  have hi : i < (gappedThreeEvenEOE a b).length := by
    have := gappedThreeEvenEOE_length a b; omega
  have hiL : i < (firstEPrefix a).length := by
    simp [firstEPrefix_length]; omega
  rw [getElem_of_list_eq (gapped_eoe_as_prefix a b) hi,
    List.getElem_append_left hiL]
  exact firstEPrefix_get_lt hia

theorem gappedThreeEvenEOE_get_a {a b : ℕ} :
    (gappedThreeEvenEOE a b)[a]'(by
        have := gappedThreeEvenEOE_length a b; omega) =
      Branch.even := by
  have hi : a < (gappedThreeEvenEOE a b).length := by
    have := gappedThreeEvenEOE_length a b; omega
  have hiL : a < (firstEPrefix a).length := by
    simp [firstEPrefix_length]
  rw [getElem_of_list_eq (gapped_eoe_as_prefix a b) hi,
    List.getElem_append_left hiL]
  exact firstEPrefix_get_last a

theorem gappedThreeEvenEOE_get_mid {a b i : ℕ}
    (hgt : a < i) (hlt : i < a + b + 1) :
    (gappedThreeEvenEOE a b)[i]'(by
        have := gappedThreeEvenEOE_length a b; omega) =
      Branch.odd := by
  have hi : i < (gappedThreeEvenEOE a b).length := by
    have := gappedThreeEvenEOE_length a b; omega
  have hge : (firstEPrefix a).length ≤ i := by
    simp [firstEPrefix_length]; omega
  have hiL : i - (a + 1) < (List.replicate b Branch.odd).length := by
    simp [List.length_replicate]; omega
  rw [getElem_of_list_eq (gapped_eoe_as_prefix a b) hi,
    List.getElem_append_right hge]
  simp [firstEPrefix_length, List.getElem_append_left hiL,
    List.getElem_replicate]

theorem gappedThreeEvenEOE_get_o {a b : ℕ} :
    (gappedThreeEvenEOE a b)[a + b + 2]'(by
        have := gappedThreeEvenEOE_length a b; omega) =
      Branch.odd := by
  have hi : a + b + 2 < (gappedThreeEvenEOE a b).length := by
    have := gappedThreeEvenEOE_length a b; omega
  have hge : (firstEPrefix a).length ≤ a + b + 2 := by
    simp [firstEPrefix_length]; omega
  have hge2 : (List.replicate b Branch.odd).length ≤ b + 1 := by
    simp [List.length_replicate]
  have hidx : a + b + 2 - (firstEPrefix a).length = b + 1 := by
    rw [firstEPrefix_length]; omega
  have hiR : a + b + 2 - (firstEPrefix a).length <
      (List.replicate b Branch.odd ++
        [Branch.even, Branch.odd, Branch.even]).length := by
    simp [List.length_replicate]; omega
  rw [getElem_of_list_eq (gapped_eoe_as_prefix a b) hi,
    List.getElem_append_right hge, getElem_nat_eq hidx hiR,
    List.getElem_append_right hge2]
  simp [List.length_replicate]

theorem gappedThreeEvenEOE_get_last {a b : ℕ} :
    (gappedThreeEvenEOE a b)[a + b + 3]'(by
        have := gappedThreeEvenEOE_length a b; omega) =
      Branch.even := by
  have hi : a + b + 3 < (gappedThreeEvenEOE a b).length := by
    have := gappedThreeEvenEOE_length a b; omega
  have hge : (firstEPrefix a).length ≤ a + b + 3 := by
    simp [firstEPrefix_length]; omega
  have hge2 : (List.replicate b Branch.odd).length ≤ b + 2 := by
    simp [List.length_replicate]
  have hidx : a + b + 3 - (firstEPrefix a).length = b + 2 := by
    rw [firstEPrefix_length]; omega
  have hiR : a + b + 3 - (firstEPrefix a).length <
      (List.replicate b Branch.odd ++
        [Branch.even, Branch.odd, Branch.even]).length := by
    simp [List.length_replicate]; omega
  rw [getElem_of_list_eq (gapped_eoe_as_prefix a b) hi,
    List.getElem_append_right hge, getElem_nat_eq hidx hiR,
    List.getElem_append_right hge2]
  simp [List.length_replicate]

theorem gappedThreeEvenEOE_pred_odd {a b k : ℕ}
    (hk0 : 0 < k) (hk : k < a + b + 4) (hne1 : k ≠ a + 1)
    (hne2 : k ≠ a + b + 2) :
    (gappedThreeEvenEOE a b)[k - 1]'(by
        have := gappedThreeEvenEOE_length a b; omega) =
      Branch.odd := by
  cases lt_or_ge (k - 1) a with
  | inl hlt => exact gappedThreeEvenEOE_get_lt_a hlt
  | inr hge =>
      have hgt : a < k - 1 := lt_of_le_of_ne hge (by omega)
      cases lt_or_ge (k - 1) (a + b + 1) with
      | inl hlt => exact gappedThreeEvenEOE_get_mid hgt hlt
      | inr hge2 =>
          have : k - 1 = a + b + 2 := by omega
          simpa [this] using gappedThreeEvenEOE_get_o (a := a) (b := b)

def gappedEEBootstrap (a b : ℕ) : List Branch :=
  List.replicate b Branch.odd ++ [Branch.even, Branch.even] ++
    List.replicate a Branch.odd ++ [Branch.even]

def gappedEOEBootstrap (a b : ℕ) : List Branch :=
  List.replicate b Branch.odd ++ [Branch.even, Branch.odd, Branch.even] ++
    List.replicate a Branch.odd ++ [Branch.even]

theorem gappedEEBootstrap_split (a b : ℕ) :
    gappedEEBootstrap a b =
      (List.replicate b Branch.odd ++ [Branch.even]) ++ [Branch.even] ++
        List.replicate a Branch.odd ++ [Branch.even] := by
  simp [gappedEEBootstrap, List.append_assoc]

theorem gappedEOEBootstrap_split (a b : ℕ) :
    gappedEOEBootstrap a b =
      (List.replicate b Branch.odd ++ [Branch.even, Branch.odd]) ++
        [Branch.even] ++ List.replicate a Branch.odd ++ [Branch.even] := by
  simp [gappedEOEBootstrap, List.append_assoc]

theorem gapped_ee_rotate_succ_a {a b : ℕ} :
    rotateItinerary (gappedThreeEvenEE a b) (a + 1) = gappedEEBootstrap a b := by
  have hlen := gappedThreeEvenEE_length a b
  have hk : a + 1 ≤ (gappedThreeEvenEE a b).length := by rw [hlen]; omega
  have hpre := firstEPrefix_length a
  have hle : a + 1 ≤ (firstEPrefix a).length := Nat.le_of_eq hpre.symm
  have hword := gapped_ee_as_prefix a b
  have hdrop : (firstEPrefix a).drop (a + 1) = [] :=
    List.drop_eq_nil_of_le (Nat.le_of_eq hpre)
  have htake : (firstEPrefix a).take (a + 1) = firstEPrefix a :=
    List.take_of_length_le (Nat.le_of_eq hpre)
  rw [rotateItinerary_eq_drop_append_take _ _ hk, hword,
    List.drop_append_of_le_length hle, List.take_append_of_le_length hle,
    hdrop, htake]
  simp [gappedEEBootstrap, firstEPrefix]

theorem gapped_eoe_rotate_succ_a {a b : ℕ} :
    rotateItinerary (gappedThreeEvenEOE a b) (a + 1) = gappedEOEBootstrap a b := by
  have hlen := gappedThreeEvenEOE_length a b
  have hk : a + 1 ≤ (gappedThreeEvenEOE a b).length := by rw [hlen]; omega
  have hpre := firstEPrefix_length a
  have hle : a + 1 ≤ (firstEPrefix a).length := Nat.le_of_eq hpre.symm
  have hword := gapped_eoe_as_prefix a b
  have hdrop : (firstEPrefix a).drop (a + 1) = [] :=
    List.drop_eq_nil_of_le (Nat.le_of_eq hpre)
  have htake : (firstEPrefix a).take (a + 1) = firstEPrefix a :=
    List.take_of_length_le (Nat.le_of_eq hpre)
  rw [rotateItinerary_eq_drop_append_take _ _ hk, hword,
    List.drop_append_of_le_length hle, List.take_append_of_le_length hle,
    hdrop, htake]
  simp [gappedEOEBootstrap, firstEPrefix]

theorem no_followsB_3_four_odds :
    followsB 3 (List.replicate 4 Branch.odd) = false := by
  native_decide

theorem no_follows_three_four_odds :
    ¬follows 3 (List.replicate 4 Branch.odd) := by
  intro hf
  have htrue : followsB 3 (List.replicate 4 Branch.odd) = true :=
    (followsB_iff 3 _).mpr hf
  rw [no_followsB_3_four_odds] at htrue
  exact Bool.false_ne_true htrue

theorem no_follows_three_long_odds {b : ℕ} (hb : 4 ≤ b) :
    ¬follows 3 (List.replicate b Branch.odd) := by
  intro hf
  have hsplit : List.replicate b Branch.odd =
      List.replicate 4 Branch.odd ++ List.replicate (b - 4) Branch.odd := by
    have : 4 + (b - 4) = b := by omega
    rw [← List.replicate_add, this]
  exact no_follows_three_four_odds
    (follows_of_append_left (v := List.replicate (b - 4) Branch.odd)
      (by simpa [hsplit] using hf))

theorem no_followsB_3_eoe_boot3 :
    followsB 3 (gappedEOEBootstrap 2 3) = false := by
  native_decide

theorem no_follows_three_eoe_bootstrap {b : ℕ} (hb : 3 ≤ b) :
    ¬follows 3 (gappedEOEBootstrap 2 b) := by
  intro hf
  cases lt_or_ge b 4 with
  | inr hb4 =>
      exact no_follows_three_long_odds hb4
        (follows_of_append_left
          (v := [Branch.even, Branch.odd, Branch.even] ++
            List.replicate 2 Branch.odd ++ [Branch.even])
          (by simpa [gappedEOEBootstrap] using hf))
  | inl hb3 =>
      have : b = 3 := by omega
      subst this
      have htrue : followsB 3 (gappedEOEBootstrap 2 3) = true :=
        (followsB_iff 3 _).mpr hf
      rw [no_followsB_3_eoe_boot3] at htrue
      exact Bool.false_ne_true htrue

theorem oo_run_suffix_threshold :
    ∀ m, 5 ≤ m → follows m (List.replicate 2 Branch.odd) →
      (m + 1) ^ 2 ≤ image m (List.replicate 2 Branch.odd) := by
  intro m hm hf
  have hlist : List.replicate 2 Branch.odd = [.odd, .odd] := rfl
  rw [hlist] at hf ⊢
  simpa [image_eq_iterate] using oo_suffix_threshold hm hf

theorem no_cycleMin_gapped_ee_bootstrap {n a b : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (hb : 4 ≤ b)
    (h : CycleMin n (gappedEEBootstrap a b)) : False := by
  have hodd : n % 2 = 1 := cycleMin_start_odd hn h
  have hn3 : 3 ≤ n := by omega
  rw [gappedEEBootstrap_split] at h
  cases lt_or_ge a 3 with
  | inr ha3 =>
      exact no_cycleMin_internal_even_threshold
        (odd_run_suffix_threshold ha3) hn3 h
  | inl ha2 =>
      have : a = 2 := by omega
      subst this
      cases lt_or_ge n 5 with
      | inr hge =>
          exact no_cycleMin_internal_even_threshold
            oo_run_suffix_threshold hge h
      | inl hlt =>
          have : n = 3 := by omega
          subst this
          exact no_follows_three_long_odds hb
            (follows_of_append_left
              (v := [Branch.even, Branch.even] ++
                List.replicate 2 Branch.odd ++ [Branch.even])
              (by simpa [gappedEEBootstrap] using h.1.1))

theorem no_cycleMin_gapped_eoe_bootstrap {n a b : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (hb : 3 ≤ b)
    (h : CycleMin n (gappedEOEBootstrap a b)) : False := by
  have hodd : n % 2 = 1 := cycleMin_start_odd hn h
  have hn3 : 3 ≤ n := by omega
  rw [gappedEOEBootstrap_split] at h
  cases lt_or_ge a 3 with
  | inr ha3 =>
      exact no_cycleMin_internal_even_threshold
        (odd_run_suffix_threshold ha3) hn3 h
  | inl ha2 =>
      have : a = 2 := by omega
      subst this
      cases lt_or_ge n 5 with
      | inr hge =>
          exact no_cycleMin_internal_even_threshold
            oo_run_suffix_threshold hge h
      | inl hlt =>
          have : n = 3 := by omega
          subst this
          exact no_follows_three_eoe_bootstrap hb
            (by simpa [gappedEOEBootstrap_split] using h.1.1)

theorem no_cycle_itinerary_gapped_three_even_ee {n a b : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (hb : 4 ≤ b) :
    ¬CycleItinerary n (gappedThreeEvenEE a b) := by
  intro h
  obtain ⟨k, hk, hm⟩ := exists_cycleMin hn h
  have hlen := gappedThreeEvenEE_length a b
  rw [hlen] at hk
  have hnk : 2 ≤ floorPower^[k] n :=
    cycleItinerary_iterate_ge_two hn h (by simpa [hlen] using hk)
  have hcases :
      k = 0 ∨ k = a + 1 ∨ k = a + b + 2 ∨
        (0 < k ∧ k ≠ a + 1 ∧ k ≠ a + b + 2) := by omega
  rcases hcases with h0 | hsucc | hlast | hmid
  · subst h0
    exact no_cycleMin_gapped_three_even_ee hnk ha hb
      (by simpa [rotateItinerary, gapped_ee_expanded] using hm)
  · subst hsucc
    exact no_cycleMin_gapped_ee_bootstrap hnk ha hb
      (by simpa [gapped_ee_rotate_succ_a] using hm)
  · subst hlast
    exact cycleMin_rotate_start_even hnk (by simpa [hlen] using hk)
      (gappedThreeEvenEE_get_last (a := a) (b := b)) hm
  · exact cycleMin_of_rotate_ends_odd hnk hmid.1
      (by simpa [hlen] using Nat.le_of_lt hk)
      (gappedThreeEvenEE_pred_odd hmid.1 hk hmid.2.1 hmid.2.2) hm

theorem no_cycle_itinerary_gapped_three_even_eoe {n a b : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (hb : 3 ≤ b) :
    ¬CycleItinerary n (gappedThreeEvenEOE a b) := by
  intro h
  obtain ⟨k, hk, hm⟩ := exists_cycleMin hn h
  have hlen := gappedThreeEvenEOE_length a b
  rw [hlen] at hk
  have hnk : 2 ≤ floorPower^[k] n :=
    cycleItinerary_iterate_ge_two hn h (by simpa [hlen] using hk)
  have hcases :
      k = 0 ∨ k = a + 1 ∨ k = a + b + 2 ∨
        (0 < k ∧ k ≠ a + 1 ∧ k ≠ a + b + 2) := by omega
  rcases hcases with h0 | hsucc | hO | hmid
  · subst h0
    exact no_cycleMin_gapped_three_even_eoe hnk ha hb
      (by simpa [rotateItinerary, gapped_eoe_expanded] using hm)
  · subst hsucc
    exact no_cycleMin_gapped_eoe_bootstrap hnk ha hb
      (by simpa [gapped_eoe_rotate_succ_a] using hm)
  · subst hO
    exact cycleMin_rotate_start_OE hnk (by
        have := hlen; omega)
      (gappedThreeEvenEOE_get_o (a := a) (b := b))
      (gappedThreeEvenEOE_get_last (a := a) (b := b)) hm
  · exact cycleMin_of_rotate_ends_odd hnk hmid.1
      (by simpa [hlen] using Nat.le_of_lt hk)
      (gappedThreeEvenEOE_pred_odd hmid.1 hk hmid.2.1 hmid.2.2) hm

end Problems.Juggler
