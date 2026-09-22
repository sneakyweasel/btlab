import Problems.Juggler.CycleCore
import Problems.Juggler.CycleObstructions
import Problems.Juggler.LeftoverEval
import Problems.Juggler.LeftoverPreimage

namespace Problems.Juggler

/-!
# Named leftover cycle itineraries at lengths six and seven

`OOOEOE` and `OOOOEE` are the remaining legal `CycleMin` orientations
among the expanding length-six even-terminating words. `OOOOEOE` and
`OOOOOEE` are the corresponding length-seven leftovers.

Census food only. The infinite leftover families, including the
`a = 6` instance `OOOOOOEEE`, live in `LeftoverFamilies`.
This is not a length-8 census and not a halt theorem.
-/

/-!
Uniform extra scale from `n = 3` fails. Length six is a finite
evaluation below `256` plus `n^81 > 2^130 (n+1)^64`. Length seven
is a finite evaluation below `14` plus
`n^243 > 2^422 (n+1)^128`. Not an exclusion of odd-terminating
cycle itineraries. The length-six and length-seven censuses are assembled
in `SmallCycleCensus.lean`.
-/

theorem itineraryOOOEOE_eq_eval : itineraryOOOEOE = itineraryOOOEOE' :=
  rfl

theorem cycleItineraryB_iff {n : ℕ} {w : List Branch} :
    cycleItineraryB n w = true ↔ CycleItinerary n w := by
  simp [cycleItineraryB, CycleItinerary, followsB_iff, Bool.and_eq_true, beq_iff_eq]
  exact and_assoc

theorem no_cycle_itinerary_oooeoe_of_lt {n : ℕ} (hn : n < 256) :
    ¬CycleItinerary n itineraryOOOEOE := by
  intro h
  have hfalse : cycleItineraryB n itineraryOOOEOE = false := by
    simpa [itineraryOOOEOE_eq_eval] using cycleItineraryB_oooeoe_lt256 ⟨n, hn⟩
  have htrue : cycleItineraryB n itineraryOOOEOE = true := cycleItineraryB_iff.mpr h
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_ooooee_of_lt {n : ℕ} (hn : n < 256) :
    ¬CycleItinerary n itineraryOOOOEE := by
  intro h
  have hfalse := cycleItineraryB_ooooee_lt256 ⟨n, hn⟩
  have htrue : cycleItineraryB n itineraryOOOOEE = true := cycleItineraryB_iff.mpr h
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem four_pow_two_pow (k : ℕ) : (4 : ℕ) ^ (2 ^ k) = 2 ^ (2 * 2 ^ k) := by
  rw [four_eq_two_pow, ← Nat.pow_mul]

theorem lowerDenom_ooo :
    lowerDenom [Branch.odd, Branch.odd, Branch.odd] = 2 ^ 38 := by
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
  rw [s2, lowerDenomFrom_nil]

theorem lowerDenom_oooo :
    lowerDenom [Branch.odd, Branch.odd, Branch.odd, Branch.odd] = 2 ^ 130 := by
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
  rw [s3, lowerDenomFrom_nil]

theorem oddCount_ooo :
    oddCount [Branch.odd, Branch.odd, Branch.odd] = 3 :=
  rfl

theorem oddCount_oooo :
    oddCount [Branch.odd, Branch.odd, Branch.odd, Branch.odd] = 4 :=
  rfl

theorem cube_succ (y : ℕ) :
    (y + 1) ^ 3 = y ^ 3 + 3 * y ^ 2 + 3 * y + 1 := by
  ring

theorem succ_cube_lt_two_mul_pow4 {A : ℕ} (hA : 2 ≤ A) :
    (A + 1) ^ 3 < 2 * A ^ 4 := by
  have hL : (A + 1) ^ 3 = A ^ 3 + 3 * A ^ 2 + 3 * A + 1 := cube_succ A
  rw [hL]
  have hle : A ^ 2 + A + 1 ≤ A ^ 3 := by
    cases lt_or_ge A 3 with
    | inl hlt =>
        have : A = 2 := by omega
        subst this
        decide
    | inr hge =>
        have hmul : 3 * A ^ 2 ≤ A * A ^ 2 :=
          Nat.mul_le_mul_right (A ^ 2) hge
        have hA3 : A * A ^ 2 = A ^ 3 := by
          ring
        have hsmall : A ^ 2 + A + 1 ≤ 3 * A ^ 2 := by
          have hA1 : 1 ≤ A := by omega
          have hself : A ≤ A ^ 2 := by
            simpa [pow_two] using Nat.le_mul_of_pos_right A hA1
          have : A + 1 ≤ 2 * A ^ 2 :=
            calc
              A + 1 ≤ A + A := Nat.add_le_add_left hA1 A
              _ = 2 * A := by ring
              _ ≤ 2 * A ^ 2 := Nat.mul_le_mul_left 2 hself
          have : A ^ 2 + (A + 1) ≤ A ^ 2 + 2 * A ^ 2 := Nat.add_le_add_left this _
          have h3A : A ^ 2 + 2 * A ^ 2 = 3 * A ^ 2 := by ring
          simpa [Nat.add_assoc, h3A] using this
        exact le_trans hsmall (by simpa [hA3] using hmul)
  have h3 : 3 * A ^ 2 + 3 * A + 1 < 3 * A ^ 3 := by
    have hmul : 3 * (A ^ 2 + A + 1) ≤ 3 * A ^ 3 := Nat.mul_le_mul_left 3 hle
    have hlt : 3 * A ^ 2 + 3 * A + 1 < 3 * (A ^ 2 + A + 1) := by omega
    exact lt_of_lt_of_le hlt hmul
  have hge : 3 * A ^ 3 ≤ (2 * A - 1) * A ^ 3 := by
    have : 3 ≤ 2 * A - 1 := by omega
    exact Nat.mul_le_mul_right (A ^ 3) this
  have hge' : 3 * A ^ 3 ≤ A ^ 3 * (2 * A - 1) := by
    simpa [mul_comm] using hge
  have hsum :
      A ^ 3 + (3 * A ^ 2 + 3 * A + 1) < A ^ 3 + A ^ 3 * (2 * A - 1) :=
    Nat.add_lt_add_left (lt_of_lt_of_le h3 hge') _
  have hsum' :
      A ^ 3 + 3 * A ^ 2 + 3 * A + 1 < A ^ 3 + A ^ 3 * (2 * A - 1) := by
    simpa [Nat.add_assoc] using hsum
  have hadd : A ^ 3 + A ^ 3 * (2 * A - 1) = A ^ 3 * (2 * A) := by
    have hk : 1 + (2 * A - 1) = 2 * A := by omega
    calc
      A ^ 3 + A ^ 3 * (2 * A - 1)
          = A ^ 3 * 1 + A ^ 3 * (2 * A - 1) := by ring
      _ = A ^ 3 * (1 + (2 * A - 1)) := (Nat.mul_add (A ^ 3) 1 (2 * A - 1)).symm
      _ = A ^ 3 * (2 * A) := by rw [hk]
  have h2 : A ^ 3 * (2 * A) = 2 * A ^ 4 := by ring
  exact hsum'.trans_eq (hadd.trans h2)

theorem cube_succ_lt_two_mul_of_cube_lt_pow4 {y A : ℕ}
    (hA : 3 ≤ A) (h : y ^ 3 < A ^ 4) :
    (y + 1) ^ 3 < 2 * A ^ 4 := by
  cases le_or_gt y A with
  | inl hle =>
      have : (y + 1) ^ 3 ≤ (A + 1) ^ 3 :=
        Nat.pow_le_pow_left (Nat.succ_le_succ hle) 3
      exact lt_of_le_of_lt this (succ_cube_lt_two_mul_pow4 (by omega))
  | inr hgt =>
      have hyA : A + 1 ≤ y := Nat.succ_le_of_lt hgt
      have hy4 : 4 ≤ y := le_trans (by omega : (4 : ℕ) ≤ A + 1) hyA
      have hy0 : 0 < y := lt_of_lt_of_le (by decide : (0 : ℕ) < 4) hy4
      have hlin : 3 * y + 1 < y ^ 2 := by
        have h4 : 4 * y ≤ y * y := Nat.mul_le_mul_right y hy4
        have h3 : 3 * y + 1 < 4 * y := by omega
        exact lt_of_lt_of_le h3 (by simpa [pow_two] using h4)
      have h4y' : 3 * y ^ 2 + 3 * y + 1 < 4 * y ^ 2 := by
        have : 3 * y ^ 2 + y ^ 2 = 4 * y ^ 2 := by ring
        have h' : 3 * y ^ 2 + (3 * y + 1) < 3 * y ^ 2 + y ^ 2 :=
          Nat.add_lt_add_left hlin (3 * y ^ 2)
        simpa [Nat.add_assoc, this] using h'
      have h4cube : 4 * y ^ 3 < 4 * A ^ 4 :=
        Nat.mul_lt_mul_of_pos_left h (by decide : (0 : ℕ) < 4)
      have h4A : 4 * A ^ 4 ≤ y * A ^ 4 :=
        Nat.mul_le_mul_right (A ^ 4) hy4
      have hy3 : 4 * y ^ 2 * y = 4 * y ^ 3 := by ring
      have h4sq : 4 * y ^ 2 < A ^ 4 := by
        have : 4 * y ^ 2 * y < A ^ 4 * y := by
          have hlt : 4 * y ^ 3 < y * A ^ 4 := lt_of_lt_of_le h4cube h4A
          rw [hy3, mul_comm (A ^ 4)]
          exact hlt
        exact (Nat.mul_lt_mul_right hy0).mp this
      have hsum : (y + 1) ^ 3 < A ^ 4 + 4 * y ^ 2 := by
        rw [cube_succ]
        have hleft :
            y ^ 3 + (3 * y ^ 2 + 3 * y + 1) <
              A ^ 4 + (3 * y ^ 2 + 3 * y + 1) :=
          Nat.add_lt_add_right h _
        have hleft' : y ^ 3 + 3 * y ^ 2 + 3 * y + 1 <
            A ^ 4 + (3 * y ^ 2 + 3 * y + 1) := by
          simpa [Nat.add_assoc] using hleft
        exact lt_of_lt_of_le hleft' (Nat.add_le_add_left (le_of_lt h4y') _)
      have htwo : A ^ 4 + 4 * y ^ 2 < 2 * A ^ 4 := by
        have : A ^ 4 + 4 * y ^ 2 < A ^ 4 + A ^ 4 := Nat.add_lt_add_left h4sq _
        have hexp : A ^ 4 + A ^ 4 = 2 * A ^ 4 := by ring
        simpa [hexp] using this
      exact hsum.trans htwo

theorem ooooee_prefix_lt_succ_pow4 {n : ℕ}
    (h : CycleItinerary n itineraryOOOOEE) :
    image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd] < (n + 1) ^ 4 := by
  have hcell :
      CycleItinerary n
        ([Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even] ++
          [Branch.even]) := by
    simpa [itineraryOOOOEE] using h
  have hI := cycle_last_even_interval hcell
  have hf4 :
      follows (image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd])
        [Branch.even, Branch.even] :=
    follows_of_append_right
      (u := [Branch.odd, Branch.odd, Branch.odd, Branch.odd])
      (by simpa [itineraryOOOOEE] using h.1)
  have he4 :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd] % 2 = 0 :=
    hf4.1
  have hz5 :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even] =
        floorPower
          (image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd]) := by
    simp [image]
  have hz4lt :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd] <
        (floorPower
            (image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd]) + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he4).mp rfl).2
  have hz5lt :
      floorPower (image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd]) <
        (n + 1) ^ 2 := by
    simpa [hz5] using hI.2
  have hsucc :
      floorPower (image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd]) + 1 ≤
        (n + 1) ^ 2 :=
    Nat.succ_le_of_lt hz5lt
  have hsq :
      (floorPower
            (image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd]) + 1) ^ 2 ≤
        ((n + 1) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left hsucc 2
  have hexp : ((n + 1) ^ 2) ^ 2 = (n + 1) ^ 4 :=
    (Nat.pow_mul (n + 1) 2 2).symm
  exact lt_of_lt_of_le hz4lt (hexp ▸ hsq)

theorem oooo_lower_growth {n : ℕ} (hn : 1 ≤ n)
    (hw : follows n [Branch.odd, Branch.odd, Branch.odd, Branch.odd]) :
    n ^ 81 ≤ 2 ^ 130 *
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd] ^ 16 := by
  have hL := lower_growth_word hn hw
  rw [LowerPowerBound, oddCount_oooo, lowerDenom_oooo] at hL
  have hlen :
      ([Branch.odd, Branch.odd, Branch.odd, Branch.odd] : List Branch).length = 4 :=
    rfl
  rw [hlen] at hL
  have h3 : (3 : ℕ) ^ 4 = 81 := by decide
  have h2 : (2 : ℕ) ^ 4 = 16 := by decide
  rw [h3, h2] at hL
  exact hL

theorem ooo_lower_growth {n : ℕ} (hn : 1 ≤ n)
    (hw : follows n [Branch.odd, Branch.odd, Branch.odd]) :
    n ^ 27 ≤ 2 ^ 38 * image n [Branch.odd, Branch.odd, Branch.odd] ^ 8 := by
  have hL := lower_growth_word hn hw
  rw [LowerPowerBound, oddCount_ooo, lowerDenom_ooo] at hL
  have hlen :
      ([Branch.odd, Branch.odd, Branch.odd] : List Branch).length = 3 :=
    rfl
  rw [hlen] at hL
  have h3 : (3 : ℕ) ^ 3 = 27 := by decide
  have h2 : (2 : ℕ) ^ 3 = 8 := by decide
  rw [h3, h2] at hL
  exact hL

theorem cube_ooo_lower {n y : ℕ}
    (h : n ^ 27 < 2 ^ 38 * (y + 1) ^ 16) :
    n ^ 81 < 2 ^ 114 * (y + 1) ^ 48 := by
  have hcube : (n ^ 27) ^ 3 < (2 ^ 38 * (y + 1) ^ 16) ^ 3 :=
    Nat.pow_lt_pow_left h (by decide : (3 : ℕ) ≠ 0)
  have hn81 : n ^ (27 * 3) = (n ^ 27) ^ 3 := Nat.pow_mul n 27 3
  have h27 : (27 : ℕ) * 3 = 81 := by decide
  rw [h27] at hn81
  have hR : (2 ^ 38) ^ 3 * ((y + 1) ^ 16) ^ 3 =
      2 ^ (38 * 3) * (y + 1) ^ (16 * 3) := by
    rw [two_pow_mul, Nat.pow_mul (y + 1) 16 3]
  have h114 : (38 : ℕ) * 3 = 114 := by decide
  have h48 : (16 : ℕ) * 3 = 48 := by decide
  rw [h114, h48] at hR
  have hmul : (2 ^ 38 * (y + 1) ^ 16) ^ 3 =
      (2 ^ 38) ^ 3 * ((y + 1) ^ 16) ^ 3 := mul_pow _ _ 3
  rw [← hn81, hmul, hR] at hcube
  exact hcube

theorem y_succ_pow48 {y n : ℕ}
    (h : (y + 1) ^ 3 < 2 * (n + 1) ^ 4) :
    (y + 1) ^ 48 < 2 ^ 16 * (n + 1) ^ 64 := by
  have hlt : ((y + 1) ^ 3) ^ 16 < (2 * (n + 1) ^ 4) ^ 16 :=
    Nat.pow_lt_pow_left h (by decide : (16 : ℕ) ≠ 0)
  have hL : (y + 1) ^ (3 * 16) = ((y + 1) ^ 3) ^ 16 := Nat.pow_mul (y + 1) 3 16
  have h48 : (3 : ℕ) * 16 = 48 := by decide
  rw [h48] at hL
  have hR : 2 ^ 16 * (n + 1) ^ (4 * 16) = (2 * (n + 1) ^ 4) ^ 16 := by
    rw [mul_pow, Nat.pow_mul]
  have h64 : (4 : ℕ) * 16 = 64 := by decide
  rw [h64] at hR
  rw [← hL, ← hR] at hlt
  exact hlt

theorem combine_ooo_tail {n y : ℕ}
    (h81 : n ^ 81 < 2 ^ 114 * (y + 1) ^ 48)
    (hy48 : (y + 1) ^ 48 < 2 ^ 16 * (n + 1) ^ 64) :
    n ^ 81 < 2 ^ 130 * (n + 1) ^ 64 := by
  have hmid : n ^ 81 < 2 ^ 114 * (2 ^ 16 * (n + 1) ^ 64) :=
    lt_trans h81 (Nat.mul_lt_mul_of_pos_left hy48
      (pow_pos (by decide : (0 : ℕ) < 2) 114))
  have hexp : 2 ^ 114 * (2 ^ 16 * (n + 1) ^ 64) = 2 ^ (114 + 16) * (n + 1) ^ 64 := by
    rw [← mul_assoc, ← Nat.pow_add]
  have h130 : (114 : ℕ) + 16 = 130 := by decide
  rw [h130] at hexp
  exact hexp ▸ hmid

theorem no_cycle_itinerary_ooooee_of_ge {n : ℕ} (hn : 256 ≤ n)
    (h : CycleItinerary n itineraryOOOOEE) : False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hOOOO :
      follows n [Branch.odd, Branch.odd, Branch.odd, Branch.odd] :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [itineraryOOOOEE] using h.1)
  have hz := ooooee_prefix_lt_succ_pow4 h
  have hpow := oooo_lower_growth hn1 hOOOO
  have hz16 : image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd] ^ 16 <
      (n + 1) ^ 64 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 16) hz (by decide)
    simpa using this
  have hlt : n ^ 81 < 2 ^ 130 * (n + 1) ^ 64 :=
    lt_of_le_of_lt hpow (Nat.mul_lt_mul_of_pos_left hz16
      (pow_pos (by decide : (0 : ℕ) < 2) 130))
  exact (not_lt_of_gt (pow81_gt_two_pow130_succ_pow64 hn)) hlt

theorem oooeoe_y_cube_lt {n : ℕ} (h : CycleItinerary n itineraryOOOEOE) :
    image n [Branch.odd, Branch.odd, Branch.odd, Branch.even] ^ 3 <
      (n + 1) ^ 4 := by
  have hcell :
      CycleItinerary n
        ([Branch.odd, Branch.odd, Branch.odd, Branch.even, Branch.odd] ++
          [Branch.even]) := by
    simpa [itineraryOOOEOE] using h
  have hI := cycle_last_even_interval hcell
  have hyO :
      follows (image n [Branch.odd, Branch.odd, Branch.odd, Branch.even])
        [Branch.odd, Branch.even] :=
    follows_of_append_right
      (u := [Branch.odd, Branch.odd, Branch.odd, Branch.even])
      (by simpa [itineraryOOOEOE] using h.1)
  have hyodd :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.even] % 2 = 1 :=
    hyO.1
  have hz5 :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.even, Branch.odd] =
        floorPower
          (image n [Branch.odd, Branch.odd, Branch.odd, Branch.even]) := by
    simp [image]
  have hcube := (floorPower_odd_eq_iff_cube_interval hyodd).mp rfl
  have hylt :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.even] ^ 3 <
        (floorPower
            (image n [Branch.odd, Branch.odd, Branch.odd, Branch.even]) + 1) ^ 2 :=
    hcube.2
  have hz5lt :
      floorPower (image n [Branch.odd, Branch.odd, Branch.odd, Branch.even]) <
        (n + 1) ^ 2 := by
    simpa [hz5] using hI.2
  have hsucc :
      floorPower (image n [Branch.odd, Branch.odd, Branch.odd, Branch.even]) + 1 ≤
        (n + 1) ^ 2 :=
    Nat.succ_le_of_lt hz5lt
  have hsq :
      (floorPower
            (image n [Branch.odd, Branch.odd, Branch.odd, Branch.even]) + 1) ^ 2 ≤
        ((n + 1) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left hsucc 2
  have hexp : ((n + 1) ^ 2) ^ 2 = (n + 1) ^ 4 :=
    (Nat.pow_mul (n + 1) 2 2).symm
  exact lt_of_lt_of_le hylt (hexp ▸ hsq)

theorem no_cycle_itinerary_oooeoe_of_ge {n : ℕ} (hn : 256 ≤ n)
    (h : CycleItinerary n itineraryOOOEOE) : False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 256) hn
  have hOOO : follows n [Branch.odd, Branch.odd, Branch.odd] :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.even])
      (by simpa [itineraryOOOEOE] using h.1)
  set z3 := image n [Branch.odd, Branch.odd, Branch.odd]
  set y := image n [Branch.odd, Branch.odd, Branch.odd, Branch.even]
  have he3 : z3 % 2 = 0 := by
    have hf : follows z3 [Branch.even, Branch.odd, Branch.even] :=
      follows_of_append_right (u := [Branch.odd, Branch.odd, Branch.odd])
        (by simpa [itineraryOOOEOE] using h.1)
    exact hf.1
  have hyeq : floorPower z3 = y := by
    simp [z3, y, image]
  have hz3lt : z3 < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he3).mp hyeq).2
  have hpow := ooo_lower_growth hn1 hOOO
  have hz8 : z3 ^ 8 < (y + 1) ^ 16 := by
    have := pow_lt_of_lt_pow_mul (k := 2) (m := 8) hz3lt (by decide)
    simpa using this
  have h27 : n ^ 27 < 2 ^ 38 * (y + 1) ^ 16 :=
    lt_of_le_of_lt hpow (Nat.mul_lt_mul_of_pos_left hz8
      (pow_pos (by decide : (0 : ℕ) < 2) 38))
  have h81 := cube_ooo_lower h27
  have hy3 := oooeoe_y_cube_lt h
  have hA : 3 ≤ n + 1 :=
    le_trans (by decide : (3 : ℕ) ≤ 257) (Nat.succ_le_succ hn)
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA (by simpa [y] using hy3)
  have hy48 := y_succ_pow48 hysucc
  have hlt := combine_ooo_tail h81 hy48
  exact (not_lt_of_gt (pow81_gt_two_pow130_succ_pow64 hn)) hlt

theorem no_cycle_itinerary_oooeoe {n : ℕ} (_hn : 2 ≤ n) :
    ¬CycleItinerary n itineraryOOOEOE := by
  intro h
  cases lt_or_ge n 256 with
  | inl hlt => exact no_cycle_itinerary_oooeoe_of_lt hlt h
  | inr hge => exact no_cycle_itinerary_oooeoe_of_ge hge h

theorem no_cycle_itinerary_ooooee {n : ℕ} (_hn : 2 ≤ n) :
    ¬CycleItinerary n itineraryOOOOEE := by
  intro h
  cases lt_or_ge n 256 with
  | inl hlt => exact no_cycle_itinerary_ooooee_of_lt hlt h
  | inr hge => exact no_cycle_itinerary_ooooee_of_ge hge h

/-! Length-7 leftovers `OOOOOEE` and `OOOOEOE`. Finite evaluation
below `14` plus `n^243 > 2^422 (n+1)^128` for `n ≥ 14`. -/

set_option exponentiation.threshold 512
set_option maxRecDepth 1024

theorem no_cycle_itinerary_oooooee_of_lt {n : ℕ} (hn : n < 14) :
    ¬CycleItinerary n itineraryOOOOOEE := by
  intro h
  have hfalse := cycleItineraryB_oooooee_lt14 ⟨n, hn⟩
  have htrue : cycleItineraryB n itineraryOOOOOEE = true := cycleItineraryB_iff.mpr h
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycle_itinerary_ooooeoe_of_lt {n : ℕ} (hn : n < 14) :
    ¬CycleItinerary n itineraryOOOOEOE := by
  intro h
  have hfalse := cycleItineraryB_ooooeoe_lt14 ⟨n, hn⟩
  have htrue : cycleItineraryB n itineraryOOOOEOE = true := cycleItineraryB_iff.mpr h
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

theorem lowerDenom_ooooo :
    lowerDenom [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd] =
      2 ^ 422 := by
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
  rw [s4, lowerDenomFrom_nil]

theorem oddCount_ooooo :
    oddCount [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd] = 5 :=
  rfl

theorem ooooo_lower_growth {n : ℕ} (hn : 1 ≤ n)
    (hw : follows n
      [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd]) :
    n ^ 243 ≤ 2 ^ 422 *
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd] ^ 32 := by
  have hL := lower_growth_word hn hw
  rw [LowerPowerBound, oddCount_ooooo, lowerDenom_ooooo] at hL
  have hlen :
      ([Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd] :
          List Branch).length = 5 :=
    rfl
  rw [hlen] at hL
  have h3 : (3 : ℕ) ^ 5 = 243 := by decide
  have h2 : (2 : ℕ) ^ 5 = 32 := by decide
  rw [h3, h2] at hL
  exact hL

set_option maxHeartbeats 800000 in
theorem pow243_gt_two_pow422_succ_pow128 {n : ℕ} (hn : 14 ≤ n) :
    2 ^ 422 * (n + 1) ^ 128 < n ^ 243 := by
  have hlin : 14 * (n + 1) ≤ 15 * n := by omega
  have hpow : (14 * (n + 1)) ^ 128 ≤ (15 * n) ^ 128 :=
    Nat.pow_le_pow_left hlin 128
  rw [mul_pow, mul_pow] at hpow
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 14) hn
  have hmid : 2 ^ 422 * 14 ^ 128 * (n + 1) ^ 128 ≤
      2 ^ 422 * 15 ^ 128 * n ^ 128 := by
    have h := Nat.mul_le_mul_left (2 ^ 422) hpow
    rw [← mul_assoc, ← mul_assoc] at h
    exact h
  have hbase : 2 ^ 422 * 15 ^ 128 * n ^ 128 < 14 ^ 243 * n ^ 128 :=
    Nat.mul_lt_mul_of_pos_right pow14_243_gt_two_pow422_pow15_128
      (pow_pos hn0 128)
  have hchain : 2 ^ 422 * 14 ^ 128 * (n + 1) ^ 128 < 14 ^ 243 * n ^ 128 :=
    lt_of_le_of_lt hmid hbase
  have h243 : (14 : ℕ) ^ 243 = 14 ^ 115 * 14 ^ 128 := by
    rw [← Nat.pow_add]
  have hR : 14 ^ 243 * n ^ 128 = 14 ^ 115 * 14 ^ 128 * n ^ 128 := by
    rw [h243, mul_assoc]
  rw [hR] at hchain
  have h14 : 0 < (14 : ℕ) ^ 128 := pow_pos (by decide : (0 : ℕ) < 14) 128
  have hcancel : 2 ^ 422 * (n + 1) ^ 128 < 14 ^ 115 * n ^ 128 := by
    have hL : 2 ^ 422 * 14 ^ 128 * (n + 1) ^ 128 =
        14 ^ 128 * (2 ^ 422 * (n + 1) ^ 128) :=
      calc
        2 ^ 422 * 14 ^ 128 * (n + 1) ^ 128
            = 2 ^ 422 * (14 ^ 128 * (n + 1) ^ 128) := by rw [mul_assoc]
        _ = (14 ^ 128 * (n + 1) ^ 128) * 2 ^ 422 := by rw [mul_comm]
        _ = 14 ^ 128 * ((n + 1) ^ 128 * 2 ^ 422) := by rw [mul_assoc]
        _ = 14 ^ 128 * (2 ^ 422 * (n + 1) ^ 128) := by
            rw [mul_comm ((n + 1) ^ 128)]
    have hR' : 14 ^ 115 * 14 ^ 128 * n ^ 128 =
        14 ^ 128 * (14 ^ 115 * n ^ 128) :=
      calc
        14 ^ 115 * 14 ^ 128 * n ^ 128
            = 14 ^ 115 * (14 ^ 128 * n ^ 128) := by rw [mul_assoc]
        _ = (14 ^ 128 * n ^ 128) * 14 ^ 115 := by rw [mul_comm]
        _ = 14 ^ 128 * (n ^ 128 * 14 ^ 115) := by rw [mul_assoc]
        _ = 14 ^ 128 * (14 ^ 115 * n ^ 128) := by rw [mul_comm (n ^ 128)]
    rw [hL, hR'] at hchain
    exact (Nat.mul_lt_mul_left h14).mp hchain
  have hn115 : 14 ^ 115 ≤ n ^ 115 := Nat.pow_le_pow_left hn 115
  have hle : 14 ^ 115 * n ^ 128 ≤ n ^ 115 * n ^ 128 :=
    Nat.mul_le_mul_right _ hn115
  have h243n : n ^ 115 * n ^ 128 = n ^ 243 := by
    rw [← Nat.pow_add]
  exact (hcancel.trans_le hle).trans_eq h243n

theorem oooooee_prefix_lt_succ_pow4 {n : ℕ}
    (h : CycleItinerary n itineraryOOOOOEE) :
    image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd] <
      (n + 1) ^ 4 := by
  have hcell :
      CycleItinerary n
        ([Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
            Branch.even] ++ [Branch.even]) := by
    simpa [itineraryOOOOOEE] using h
  have hI := cycle_last_even_interval hcell
  have hf5 :
      follows
        (image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd])
        [Branch.even, Branch.even] :=
    follows_of_append_right
      (u := [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd])
      (by simpa [itineraryOOOOOEE] using h.1)
  have he5 :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd] % 2 =
        0 :=
    hf5.1
  have hz6 :
      image n
          [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd,
            Branch.even] =
        floorPower
          (image n
            [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd]) := by
    simp [image]
  have hz5lt :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd] <
        (floorPower
            (image n
              [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd]) +
          1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he5).mp rfl).2
  have hz6lt :
      floorPower
          (image n
            [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd]) <
        (n + 1) ^ 2 := by
    simpa [hz6] using hI.2
  have hsucc :
      floorPower
          (image n
            [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd]) +
        1 ≤ (n + 1) ^ 2 :=
    Nat.succ_le_of_lt hz6lt
  have hsq :
      (floorPower
            (image n
              [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd]) +
          1) ^ 2 ≤
        ((n + 1) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left hsucc 2
  have hexp : ((n + 1) ^ 2) ^ 2 = (n + 1) ^ 4 :=
    (Nat.pow_mul (n + 1) 2 2).symm
  exact lt_of_lt_of_le hz5lt (hexp ▸ hsq)

theorem no_cycle_itinerary_oooooee_of_ge {n : ℕ} (hn : 14 ≤ n)
    (h : CycleItinerary n itineraryOOOOOEE) : False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 14) hn
  have hOOOOO :
      follows n
        [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd] :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [itineraryOOOOOEE] using h.1)
  have hz := oooooee_prefix_lt_succ_pow4 h
  have hpow := ooooo_lower_growth hn1 hOOOOO
  have hz32 :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.odd] ^ 32 <
        (n + 1) ^ 128 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 32) hz (by decide)
    simpa using this
  have hlt : n ^ 243 < 2 ^ 422 * (n + 1) ^ 128 :=
    lt_of_le_of_lt hpow (Nat.mul_lt_mul_of_pos_left hz32
      (pow_pos (by decide : (0 : ℕ) < 2) 422))
  exact (not_lt_of_gt (pow243_gt_two_pow422_succ_pow128 hn)) hlt

theorem ooooeoe_y_cube_lt {n : ℕ} (h : CycleItinerary n itineraryOOOOEOE) :
    image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even] ^ 3 <
      (n + 1) ^ 4 := by
  have hcell :
      CycleItinerary n
        ([Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even,
            Branch.odd] ++ [Branch.even]) := by
    simpa [itineraryOOOOEOE] using h
  have hI := cycle_last_even_interval hcell
  have hyO :
      follows
        (image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even])
        [Branch.odd, Branch.even] :=
    follows_of_append_right
      (u := [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even])
      (by simpa [itineraryOOOOEOE] using h.1)
  have hyodd :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even] % 2 =
        1 :=
    hyO.1
  have hz6 :
      image n
          [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even,
            Branch.odd] =
        floorPower
          (image n
            [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even]) := by
    simp [image]
  have hcube := (floorPower_odd_eq_iff_cube_interval hyodd).mp rfl
  have hylt :
      image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even] ^ 3 <
        (floorPower
            (image n
              [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even]) +
          1) ^ 2 :=
    hcube.2
  have hz6lt :
      floorPower
          (image n
            [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even]) <
        (n + 1) ^ 2 := by
    simpa [hz6] using hI.2
  have hsucc :
      floorPower
          (image n
            [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even]) +
        1 ≤ (n + 1) ^ 2 :=
    Nat.succ_le_of_lt hz6lt
  have hsq :
      (floorPower
            (image n
              [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even]) +
          1) ^ 2 ≤
        ((n + 1) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left hsucc 2
  have hexp : ((n + 1) ^ 2) ^ 2 = (n + 1) ^ 4 :=
    (Nat.pow_mul (n + 1) 2 2).symm
  exact lt_of_lt_of_le hylt (hexp ▸ hsq)

theorem cube_oooo_lower {n y : ℕ}
    (h : n ^ 81 < 2 ^ 130 * (y + 1) ^ 32) :
    n ^ 243 < 2 ^ 390 * (y + 1) ^ 96 := by
  have hcube : (n ^ 81) ^ 3 < (2 ^ 130 * (y + 1) ^ 32) ^ 3 :=
    Nat.pow_lt_pow_left h (by decide : (3 : ℕ) ≠ 0)
  have hn243 : n ^ (81 * 3) = (n ^ 81) ^ 3 := Nat.pow_mul n 81 3
  have h81 : (81 : ℕ) * 3 = 243 := by decide
  rw [h81] at hn243
  have hR : (2 ^ 130) ^ 3 * ((y + 1) ^ 32) ^ 3 =
      2 ^ (130 * 3) * (y + 1) ^ (32 * 3) := by
    rw [two_pow_mul, Nat.pow_mul (y + 1) 32 3]
  have h390 : (130 : ℕ) * 3 = 390 := by decide
  have h96 : (32 : ℕ) * 3 = 96 := by decide
  rw [h390, h96] at hR
  have hmul : (2 ^ 130 * (y + 1) ^ 32) ^ 3 =
      (2 ^ 130) ^ 3 * ((y + 1) ^ 32) ^ 3 := mul_pow _ _ 3
  rw [← hn243, hmul, hR] at hcube
  exact hcube

theorem y_succ_pow96 {y n : ℕ}
    (h : (y + 1) ^ 3 < 2 * (n + 1) ^ 4) :
    (y + 1) ^ 96 < 2 ^ 32 * (n + 1) ^ 128 := by
  have hlt : ((y + 1) ^ 3) ^ 32 < (2 * (n + 1) ^ 4) ^ 32 :=
    Nat.pow_lt_pow_left h (by decide : (32 : ℕ) ≠ 0)
  have hL : (y + 1) ^ (3 * 32) = ((y + 1) ^ 3) ^ 32 := Nat.pow_mul (y + 1) 3 32
  have h96 : (3 : ℕ) * 32 = 96 := by decide
  rw [h96] at hL
  have hR : 2 ^ 32 * (n + 1) ^ (4 * 32) = (2 * (n + 1) ^ 4) ^ 32 := by
    rw [mul_pow, Nat.pow_mul]
  have h128 : (4 : ℕ) * 32 = 128 := by decide
  rw [h128] at hR
  rw [← hL, ← hR] at hlt
  exact hlt

theorem combine_oooo_tail {n y : ℕ}
    (h243 : n ^ 243 < 2 ^ 390 * (y + 1) ^ 96)
    (hy96 : (y + 1) ^ 96 < 2 ^ 32 * (n + 1) ^ 128) :
    n ^ 243 < 2 ^ 422 * (n + 1) ^ 128 := by
  have hmid : n ^ 243 < 2 ^ 390 * (2 ^ 32 * (n + 1) ^ 128) :=
    lt_trans h243 (Nat.mul_lt_mul_of_pos_left hy96
      (pow_pos (by decide : (0 : ℕ) < 2) 390))
  have hexp : 2 ^ 390 * (2 ^ 32 * (n + 1) ^ 128) =
      2 ^ (390 + 32) * (n + 1) ^ 128 := by
    rw [← mul_assoc, ← Nat.pow_add]
  have h422 : (390 : ℕ) + 32 = 422 := by decide
  rw [h422] at hexp
  exact hexp ▸ hmid

theorem no_cycle_itinerary_ooooeoe_of_ge {n : ℕ} (hn : 14 ≤ n)
    (h : CycleItinerary n itineraryOOOOEOE) : False := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 14) hn
  have hOOOO :
      follows n [Branch.odd, Branch.odd, Branch.odd, Branch.odd] :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.even])
      (by simpa [itineraryOOOOEOE] using h.1)
  set z4 := image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd]
  set y := image n [Branch.odd, Branch.odd, Branch.odd, Branch.odd, Branch.even]
  have he4 : z4 % 2 = 0 := by
    have hf : follows z4 [Branch.even, Branch.odd, Branch.even] :=
      follows_of_append_right
        (u := [Branch.odd, Branch.odd, Branch.odd, Branch.odd])
        (by simpa [itineraryOOOOEOE] using h.1)
    exact hf.1
  have hyeq : floorPower z4 = y := by
    simp [z4, y, image]
  have hz4lt : z4 < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he4).mp hyeq).2
  have hpow := oooo_lower_growth hn1 hOOOO
  have hz16 : z4 ^ 16 < (y + 1) ^ 32 := by
    have := pow_lt_of_lt_pow_mul (k := 2) (m := 16) hz4lt (by decide)
    simpa using this
  have h81 : n ^ 81 < 2 ^ 130 * (y + 1) ^ 32 :=
    lt_of_le_of_lt hpow (Nat.mul_lt_mul_of_pos_left hz16
      (pow_pos (by decide : (0 : ℕ) < 2) 130))
  have h243 := cube_oooo_lower h81
  have hy3 := ooooeoe_y_cube_lt h
  have hA : 3 ≤ n + 1 :=
    le_trans (by decide : (3 : ℕ) ≤ 15) (Nat.succ_le_succ hn)
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA (by simpa [y] using hy3)
  have hy96 := y_succ_pow96 hysucc
  have hlt := combine_oooo_tail h243 hy96
  exact (not_lt_of_gt (pow243_gt_two_pow422_succ_pow128 hn)) hlt

theorem no_cycle_itinerary_oooooee {n : ℕ} (_hn : 2 ≤ n) :
    ¬CycleItinerary n itineraryOOOOOEE := by
  intro h
  cases lt_or_ge n 14 with
  | inl hlt => exact no_cycle_itinerary_oooooee_of_lt hlt h
  | inr hge => exact no_cycle_itinerary_oooooee_of_ge hge h

theorem no_cycle_itinerary_ooooeoe {n : ℕ} (_hn : 2 ≤ n) :
    ¬CycleItinerary n itineraryOOOOEOE := by
  intro h
  cases lt_or_ge n 14 with
  | inl hlt => exact no_cycle_itinerary_ooooeoe_of_lt hlt h
  | inr hge => exact no_cycle_itinerary_ooooeoe_of_ge hge h

end Problems.Juggler
