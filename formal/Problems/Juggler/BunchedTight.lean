import Problems.Juggler.LeftoverPreimage
import Problems.Juggler.LeftoverShort
import Problems.Juggler.LeftoverEval

namespace Problems.Juggler

/-!
Algebraic cells for the remaining bunched leftovers. CycleItinerary
extraction stays in the family files.
-/

set_option exponentiation.threshold 2048
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

theorem two_pow38_lt_succ_pow22 {n : ℕ} (hn : 3 ≤ n) :
    2 ^ 38 < (n + 1) ^ 22 := by
  have : 4 ≤ n + 1 := by omega
  have h : (4 : ℕ) ^ 22 ≤ (n + 1) ^ 22 := Nat.pow_le_pow_left this 22
  have h4 : (4 : ℕ) ^ 22 = 2 ^ 44 := by
    have : (4 : ℕ) = 2 ^ 2 := rfl
    rw [this, ← Nat.pow_mul]
  rw [h4] at h
  exact lt_of_lt_of_le
    (Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2) (by decide : (38 : ℕ) < 44)) h

theorem two_pow38_succ_pow32_lt_succ_pow54 {n : ℕ} (hn : 3 ≤ n) :
    2 ^ 38 * (n + 1) ^ 32 < (n + 1) ^ 54 := by
  have hpos : 0 < (n + 1) ^ 32 := pow_pos (Nat.succ_pos n) 32
  have hr : (n + 1) ^ 54 = (n + 1) ^ 22 * (n + 1) ^ 32 := by
    rw [← Nat.pow_add]
  rw [hr]
  exact Nat.mul_lt_mul_of_pos_right (two_pow38_lt_succ_pow22 hn) hpos

theorem y_lt_succ_sq_of_odd27 {y n : ℕ} (hn : 3 ≤ n)
    (h : y ^ 27 < 2 ^ 38 * (n + 1) ^ 32) : y < (n + 1) ^ 2 := by
  refine lt_of_not_ge ?_
  intro hge
  have hy : (n + 1) ^ 54 ≤ y ^ 27 := by
    have := Nat.pow_le_pow_left hge 27
    rwa [← Nat.pow_mul] at this
  exact (not_lt_of_gt (two_pow38_succ_pow32_lt_succ_pow54 hn))
    (lt_of_le_of_lt hy h)

theorem z_lt_succ_pow4_of_y {z y n : ℕ}
    (hz : z < (y + 1) ^ 2) (hy : y < (n + 1) ^ 2) :
    z < (n + 1) ^ 4 := by
  have hys : y + 1 ≤ (n + 1) ^ 2 := Nat.succ_le_of_lt hy
  have : (y + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hys 2
  have hexp : ((n + 1) ^ 2) ^ 2 = (n + 1) ^ 4 := by rw [← Nat.pow_mul]
  exact lt_of_lt_of_le hz (hexp ▸ this)

theorem two_mul_pow_27 (e y m : ℕ) :
    (2 ^ e * y ^ m) ^ 27 = 2 ^ (27 * e) * y ^ (27 * m) := by
  rw [mul_pow, two_pow_mul, ← Nat.pow_mul, Nat.mul_comm e 27, Nat.mul_comm m 27]

theorem succ_pow27_lt_two_mul_of_ge39 {y : ℕ} (hy : 39 ≤ y) :
    (y + 1) ^ 27 < 2 * y ^ 27 := by
  have hlin : (y + 1) * 39 ≤ y * 40 := by omega
  have hpow : ((y + 1) * 39) ^ 27 ≤ (y * 40) ^ 27 :=
    Nat.pow_le_pow_left hlin 27
  have hL : ((y + 1) * 39) ^ 27 = (y + 1) ^ 27 * 39 ^ 27 := mul_pow _ _ 27
  have hR : (y * 40) ^ 27 = y ^ 27 * 40 ^ 27 := mul_pow _ _ 27
  have hmid : (y + 1) ^ 27 * 39 ^ 27 ≤ y ^ 27 * 40 ^ 27 := by
    rwa [hL, hR] at hpow
  have hy0 : 0 < y ^ 27 :=
    pow_pos (lt_of_lt_of_le (by decide : (0 : ℕ) < 39) hy) 27
  have hmid' : y ^ 27 * 40 ^ 27 < y ^ 27 * (2 * 39 ^ 27) :=
    Nat.mul_lt_mul_of_pos_left pow40_27_lt_two_mul_pow39_27 hy0
  have hpos : 0 < 39 ^ 27 := pow_pos (by decide : (0 : ℕ) < 39) 27
  have hcomb : (y + 1) ^ 27 * 39 ^ 27 < 2 * y ^ 27 * 39 ^ 27 := by
    have hring : y ^ 27 * (2 * 39 ^ 27) = 2 * y ^ 27 * 39 ^ 27 := by ring
    exact (lt_of_le_of_lt hmid hmid').trans_eq hring
  exact (Nat.mul_lt_mul_right hpos).mp hcomb

theorem eoooee_tight_succ {n : ℕ} (hn : 1 ≤ n)
    (ih : 2 ^ 1650 * (n + 1) ^ 512 < n ^ 729) :
    2 ^ 1650 * (n + 2) ^ 512 < (n + 1) ^ 729 := by
  have hpq := persist_succ_pow (p := 729) (q := 512) hn
    (by decide) (by decide)
  have hpos2 : 0 < 2 ^ 1650 := pow_pos (by decide : (0 : ℕ) < 2) _
  have hposn : 0 < n ^ 729 :=
    pow_pos (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hn) _
  have hmid : (2 ^ 1650 * (n + 2) ^ 512) * n ^ 729 <
      (n + 1) ^ 729 * n ^ 729 :=
    calc
      (2 ^ 1650 * (n + 2) ^ 512) * n ^ 729 =
          2 ^ 1650 * ((n + 2) ^ 512 * n ^ 729) := by
        rw [mul_assoc]
      _ = 2 ^ 1650 * (n ^ 729 * (n + 2) ^ 512) := by
        rw [mul_comm ((n + 2) ^ 512)]
      _ < 2 ^ 1650 * (n + 1) ^ (729 + 512) :=
        Nat.mul_lt_mul_of_pos_left hpq hpos2
      _ = 2 ^ 1650 * ((n + 1) ^ 729 * (n + 1) ^ 512) := by
        rw [Nat.pow_add]
      _ = 2 ^ 1650 * ((n + 1) ^ 512 * (n + 1) ^ 729) := by
        rw [mul_comm ((n + 1) ^ 729)]
      _ = (2 ^ 1650 * (n + 1) ^ 512) * (n + 1) ^ 729 := by
        rw [mul_assoc]
      _ < n ^ 729 * (n + 1) ^ 729 :=
        Nat.mul_lt_mul_of_pos_right ih (pow_pos (Nat.succ_pos n) _)
      _ = (n + 1) ^ 729 * n ^ 729 := mul_comm _ _
  exact (Nat.mul_lt_mul_right hposn).mp hmid

theorem eoooee_tight_at {n : ℕ} (hn : 197 ≤ n) :
    2 ^ 1650 * (n + 1) ^ 512 < n ^ 729 := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hn
  subst ht
  clear hn
  induction t with
  | zero => exact pow197_729_gt_two_pow1650_succ_pow512
  | succ t ih =>
      have h1 : 1 ≤ 197 + t := by omega
      exact eoooee_tight_succ h1 ih

theorem eoooee_small_y_false {n y : ℕ}
    (hn : 24 ≤ n) (hy : y < 39)
    (h27 : n ^ 27 < 2 ^ 38 * (y + 1) ^ 16) : False := by
  have hys : y + 1 ≤ 39 := Nat.succ_le_of_lt hy
  have hbound : (y + 1) ^ 16 ≤ 39 ^ 16 := Nat.pow_le_pow_left hys 16
  have hsmall : n ^ 27 < 2 ^ 38 * 39 ^ 16 :=
    lt_of_lt_of_le h27 (Nat.mul_le_mul_left _ hbound)
  have h24 : (24 : ℕ) ^ 27 ≤ n ^ 27 := Nat.pow_le_pow_left hn 27
  exact (lt_irrefl _)
    (hsmall.trans (two_pow38_mul_pow39_16_lt_pow24_27.trans_le h24))

theorem cube_ooo_to_243 {n y : ℕ}
    (h : n ^ 81 < 2 ^ 114 * (y + 1) ^ 48) :
    n ^ 243 < 2 ^ 342 * (y + 1) ^ 144 := by
  have hcube : (n ^ 81) ^ 3 < (2 ^ 114 * (y + 1) ^ 48) ^ 3 :=
    Nat.pow_lt_pow_left h (by decide : (3 : ℕ) ≠ 0)
  have hL : (n ^ 81) ^ 3 = n ^ 243 := by rw [← Nat.pow_mul]
  have hR : (2 ^ 114 * (y + 1) ^ 48) ^ 3 = 2 ^ 342 * (y + 1) ^ 144 := by
    rw [mul_pow, two_pow_mul, ← Nat.pow_mul]
  rwa [hL, hR] at hcube

theorem cube_ooo_to_729 {n y : ℕ}
    (h : n ^ 243 < 2 ^ 342 * (y + 1) ^ 144) :
    n ^ 729 < 2 ^ 1026 * (y + 1) ^ 432 := by
  have hcube : (n ^ 243) ^ 3 < (2 ^ 342 * (y + 1) ^ 144) ^ 3 :=
    Nat.pow_lt_pow_left h (by decide : (3 : ℕ) ≠ 0)
  have hL : (n ^ 243) ^ 3 = n ^ 729 := by rw [← Nat.pow_mul]
  have hR : (2 ^ 342 * (y + 1) ^ 144) ^ 3 = 2 ^ 1026 * (y + 1) ^ 432 := by
    rw [mul_pow, two_pow_mul, ← Nat.pow_mul]
  rwa [hL, hR] at hcube

theorem eoooee_cycle_bound {n y : ℕ}
    (h : n ^ 27 < 2 ^ 38 * (y + 1) ^ 16) :
    n ^ 729 < 2 ^ 1026 * (y + 1) ^ 432 :=
  cube_ooo_to_729 (cube_ooo_to_243 (cube_ooo_lower h))

theorem eoooee_raise16 {y n : ℕ}
    (h : (y + 1) ^ 27 < 2 ^ 39 * (n + 1) ^ 32) :
    (y + 1) ^ 432 < 2 ^ 624 * (n + 1) ^ 512 := by
  have hlt : ((y + 1) ^ 27) ^ 16 < (2 ^ 39 * (n + 1) ^ 32) ^ 16 :=
    Nat.pow_lt_pow_left h (by decide : (16 : ℕ) ≠ 0)
  have hL : ((y + 1) ^ 27) ^ 16 = (y + 1) ^ 432 := by rw [← Nat.pow_mul]
  have hR : (2 ^ 39 * (n + 1) ^ 32) ^ 16 = 2 ^ 624 * (n + 1) ^ 512 := by
    rw [mul_pow, two_pow_mul, ← Nat.pow_mul]
  rwa [hL, hR] at hlt

theorem eoooee_combine_tight {n y : ℕ} (hn : 197 ≤ n)
    (hraise : (y + 1) ^ 432 < 2 ^ 624 * (n + 1) ^ 512) :
    2 ^ 1026 * (y + 1) ^ 432 < n ^ 729 := by
  have htail := eoooee_tight_at hn
  have hexp : 2 ^ 1650 * (n + 1) ^ 512 =
      2 ^ 1026 * (2 ^ 624 * (n + 1) ^ 512) := by
    have : (1650 : ℕ) = 1026 + 624 := by decide
    rw [this, Nat.pow_add, mul_assoc]
  have hmid : 2 ^ 1026 * (2 ^ 624 * (n + 1) ^ 512) < n ^ 729 := by
    rwa [← hexp]
  exact (Nat.mul_lt_mul_of_pos_left hraise
    (pow_pos (by decide : (0 : ℕ) < 2) 1026)).trans hmid

theorem eoooee_large_y_false {n y : ℕ}
    (hn : 197 ≤ n) (hy : 39 ≤ y)
    (hy27 : y ^ 27 < 2 ^ 38 * (n + 1) ^ 32)
    (h27 : n ^ 27 < 2 ^ 38 * (y + 1) ^ 16) : False := by
  have hsucc : (y + 1) ^ 27 < 2 * y ^ 27 :=
    succ_pow27_lt_two_mul_of_ge39 hy
  have h2y : 2 * y ^ 27 < 2 ^ 39 * (n + 1) ^ 32 := by
    have : 2 * y ^ 27 < 2 * (2 ^ 38 * (n + 1) ^ 32) :=
      Nat.mul_lt_mul_of_pos_left hy27 (by decide : (0 : ℕ) < 2)
    have hexp : 2 * (2 ^ 38 * (n + 1) ^ 32) = 2 ^ 39 * (n + 1) ^ 32 := by
      rw [← mul_assoc, two_mul_two_pow]
    rwa [hexp] at this
  have hgt := eoooee_combine_tight hn
    (eoooee_raise16 (hsucc.trans h2y))
  exact (not_lt_of_gt hgt) (eoooee_cycle_bound h27)

theorem eooeoe_u_pow27 {u y n : ℕ}
    (hu : u ^ 9 < 1024 * (y + 1) ^ 8)
    (hy : (y + 1) ^ 3 < 2 * (n + 1) ^ 4) :
    u ^ 27 < 2 ^ 38 * (n + 1) ^ 32 := by
  have hu27 : u ^ 27 < 1024 ^ 3 * (y + 1) ^ 24 := by
    have hlt : (u ^ 9) ^ 3 < (1024 * (y + 1) ^ 8) ^ 3 :=
      Nat.pow_lt_pow_left hu (by decide : (3 : ℕ) ≠ 0)
    have hL : (u ^ 9) ^ 3 = u ^ 27 := by rw [← Nat.pow_mul]
    have hR : (1024 * (y + 1) ^ 8) ^ 3 = 1024 ^ 3 * (y + 1) ^ 24 := by
      rw [mul_pow, ← Nat.pow_mul]
    rwa [hL, hR] at hlt
  have h1024 : (1024 : ℕ) ^ 3 = 2 ^ 30 := by
    have : (1024 : ℕ) = 2 ^ 10 := by decide
    rw [this, ← Nat.pow_mul]
  have hy24 : (y + 1) ^ 24 < 2 ^ 8 * (n + 1) ^ 32 := by
    have hlt : ((y + 1) ^ 3) ^ 8 < (2 * (n + 1) ^ 4) ^ 8 :=
      Nat.pow_lt_pow_left hy (by decide : (8 : ℕ) ≠ 0)
    have hL : ((y + 1) ^ 3) ^ 8 = (y + 1) ^ 24 := by rw [← Nat.pow_mul]
    have hR : (2 * (n + 1) ^ 4) ^ 8 = 2 ^ 8 * (n + 1) ^ 32 := by
      rw [mul_pow, ← Nat.pow_mul]
    rwa [hL, hR] at hlt
  have hmid : 1024 ^ 3 * (y + 1) ^ 24 < 2 ^ 30 * (2 ^ 8 * (n + 1) ^ 32) := by
    rw [h1024]
    exact Nat.mul_lt_mul_of_pos_left hy24 (pow_pos (by decide : (0 : ℕ) < 2) 30)
  have hexp : 2 ^ 30 * (2 ^ 8 * (n + 1) ^ 32) = 2 ^ 38 * (n + 1) ^ 32 := by
    have : (38 : ℕ) = 30 + 8 := by decide
    rw [this, Nat.pow_add, mul_assoc]
  exact hu27.trans (hmid.trans_eq hexp)

theorem eooeoe_u_lt_succ_sq {u y n : ℕ} (hn : 4 ≤ n)
    (hu : u ^ 9 < 1024 * (y + 1) ^ 8)
    (hy : (y + 1) ^ 3 < 2 * (n + 1) ^ 4) :
    u < (n + 1) ^ 2 :=
  y_lt_succ_sq_of_odd27 (le_trans (by decide : (3 : ℕ) ≤ 4) hn)
    (eooeoe_u_pow27 hu hy)

end Problems.Juggler

