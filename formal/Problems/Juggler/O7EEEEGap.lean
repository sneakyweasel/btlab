import Problems.Juggler.LeftoverFamilies

namespace Problems.Juggler

/-!
# O^7 image above the EEEE cell

Laboratory satellite. If `n ≥ 2` follows seven odds, then
`T^7(n) ≥ (n+1)^16`. The leftover `4`-fudge is not used; the exact
cell `(T+1)^2 > x^3` plus `x_k ≥ n` fires at the existing seven-odd
cutoff `256`.

Not imported by `Problems.JugglerPaper`. Not a length-11 census and
not a halt theorem.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 2048
set_option exponentiation.threshold 10000

def itineraryO7EEEE : List Branch :=
  sevenOdds ++ List.replicate 4 Branch.even

theorem iterate_floorPower_one : ∀ k, floorPower^[k] 1 = 1
  | 0 => rfl
  | k + 1 => by
      rw [Function.iterate_succ_apply, floorPower_one, iterate_floorPower_one k]

theorem image_one_sevenOdds : image 1 sevenOdds = 1 := by
  rw [sevenOdds, image_eq_iterate, List.length_replicate, iterate_floorPower_one]

theorem odd_cube_lt_succ_sq {n : ℕ} (hodd : n % 2 = 1) :
    n ^ 3 < (floorPower n + 1) ^ 2 :=
  ((floorPower_odd_eq_iff_cube_interval hodd).mp rfl).2

theorem cross_mul_pow {n x e : ℕ} (hx : n ≤ x) :
    (x + 1) ^ e * n ^ e ≤ (n + 1) ^ e * x ^ e := by
  have h : n * (x + 1) ≤ (n + 1) * x := by
    have : n * x + n ≤ n * x + x := Nat.add_le_add_left hx _
    simpa [Nat.mul_add, Nat.add_mul] using this
  have hpow := Nat.pow_le_pow_left h e
  have hL : (n * (x + 1)) ^ e = n ^ e * (x + 1) ^ e := mul_pow _ _ _
  have hR : ((n + 1) * x) ^ e = (n + 1) ^ e * x ^ e := mul_pow _ _ _
  have hL' : n ^ e * (x + 1) ^ e = (x + 1) ^ e * n ^ e := mul_comm _ _
  exact (hL'.symm ▸ (hL ▸ (hR ▸ hpow)))

theorem image_replicate_odd_succ (n k : ℕ) :
    image n (List.replicate (k + 1) Branch.odd) =
      image (floorPower n) (List.replicate k Branch.odd) := by
  rw [List.replicate_succ, image_cons]

theorem odd_run_ge {n : ℕ} (hn : 1 ≤ n) :
    ∀ k, follows n (List.replicate k Branch.odd) →
      n ≤ image n (List.replicate k Branch.odd)
  | 0, _ => le_rfl
  | k + 1, hw => by
      have hge : n ≤ floorPower n := floorPower_odd_ge hw.1
      have ih := odd_run_ge (floorPower_pos hn) k hw.2
      exact le_trans hge (by simpa [image_replicate_odd_succ] using ih)

theorem follows_odd_drop {n a k : ℕ} (hka : k ≤ a)
    (hw : follows n (List.replicate a Branch.odd)) :
    follows (image n (List.replicate k Branch.odd))
      (List.replicate (a - k) Branch.odd) := by
  have hsplit :
      List.replicate a Branch.odd =
        List.replicate k Branch.odd ++ List.replicate (a - k) Branch.odd := by
    rw [← List.replicate_add, Nat.add_sub_cancel' hka]
  have hw' :
      follows n
        (List.replicate k Branch.odd ++ List.replicate (a - k) Branch.odd) := by
    simpa [hsplit] using hw
  exact follows_of_append_right hw'

theorem follows_odd_take {n a k : ℕ} (hka : k ≤ a)
    (hw : follows n (List.replicate a Branch.odd)) :
    follows n (List.replicate k Branch.odd) := by
  have hsplit :
      List.replicate a Branch.odd =
        List.replicate k Branch.odd ++ List.replicate (a - k) Branch.odd := by
    rw [← List.replicate_add, Nat.add_sub_cancel' hka]
  have hw' :
      follows n
        (List.replicate k Branch.odd ++ List.replicate (a - k) Branch.odd) := by
    simpa [hsplit] using hw
  exact follows_of_append_left hw'

theorem odd_image_is_odd {n a k : ℕ} (hka : k < a)
    (hw : follows n (List.replicate a Branch.odd)) :
    image n (List.replicate k Branch.odd) % 2 = 1 := by
  have hrest := follows_odd_drop (Nat.le_of_lt hka) hw
  have hpos : 1 ≤ a - k := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hka)
  exact follows_replicate_odd_head hpos hrest

theorem odd_image_step (n k : ℕ) :
    image n (List.replicate (k + 1) Branch.odd) =
      floorPower (image n (List.replicate k Branch.odd)) := by
  induction k generalizing n with
  | zero => simp [image, List.replicate]
  | succ k ih =>
      rw [image_replicate_odd_succ, ih, image_replicate_odd_succ]

/-- One +1-step: replace `(x+1)^{3t}` by `(T(x)+1)^{2t}` after crossing `n ≤ x`. -/
theorem absorb_odd_step {n x A B t : ℕ} (hn : 1 ≤ n)
    (h : n ^ A < (n + 1) ^ B * (x + 1) ^ (3 * t))
    (hx : n ≤ x) (hodd : x % 2 = 1) (ht : t ≠ 0) :
    n ^ (A + 3 * t) <
      (n + 1) ^ (B + 3 * t) * (floorPower x + 1) ^ (2 * t) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hn
  have hL : n ^ (A + 3 * t) = n ^ A * n ^ (3 * t) := Nat.pow_add _ _ _
  have hmul : n ^ A * n ^ (3 * t) <
      (n + 1) ^ B * (x + 1) ^ (3 * t) * n ^ (3 * t) :=
    Nat.mul_lt_mul_of_pos_right h (pow_pos hn0 _)
  have hcross := cross_mul_pow (n := n) (x := x) (e := 3 * t) hx
  have hmid :
      (n + 1) ^ B * ((x + 1) ^ (3 * t) * n ^ (3 * t)) ≤
        (n + 1) ^ B * ((n + 1) ^ (3 * t) * x ^ (3 * t)) :=
    Nat.mul_le_mul_left _ hcross
  have hassoc :
      (n + 1) ^ B * (x + 1) ^ (3 * t) * n ^ (3 * t) =
        (n + 1) ^ B * ((x + 1) ^ (3 * t) * n ^ (3 * t)) :=
    mul_assoc _ _ _
  have hassoc' :
      (n + 1) ^ B * ((n + 1) ^ (3 * t) * x ^ (3 * t)) =
        (n + 1) ^ (B + 3 * t) * x ^ (3 * t) := by
    rw [← mul_assoc, ← Nat.pow_add]
  have hle :
      (n + 1) ^ B * (x + 1) ^ (3 * t) * n ^ (3 * t) ≤
        (n + 1) ^ (B + 3 * t) * x ^ (3 * t) :=
    (hassoc ▸ hmid).trans_eq hassoc'
  have hcube : x ^ 3 < (floorPower x + 1) ^ 2 := odd_cube_lt_succ_sq hodd
  have hxt : (x ^ 3) ^ t < ((floorPower x + 1) ^ 2) ^ t :=
    Nat.pow_lt_pow_left hcube ht
  have hx3 : (x ^ 3) ^ t = x ^ (3 * t) := (Nat.pow_mul x 3 t).symm
  have h2t : ((floorPower x + 1) ^ 2) ^ t = (floorPower x + 1) ^ (2 * t) :=
    (Nat.pow_mul (floorPower x + 1) 2 t).symm
  have hxlt : x ^ (3 * t) < (floorPower x + 1) ^ (2 * t) := by
    rw [← hx3, ← h2t]
    exact hxt
  have hposB : 0 < (n + 1) ^ (B + 3 * t) := pow_pos (Nat.succ_pos n) _
  have hfin :
      (n + 1) ^ (B + 3 * t) * x ^ (3 * t) <
        (n + 1) ^ (B + 3 * t) * (floorPower x + 1) ^ (2 * t) :=
    Nat.mul_lt_mul_of_pos_left hxlt hposB
  exact ((hL ▸ hmul).trans_le hle).trans hfin

theorem three_mul_pow256_gt_pow257 :
    (257 : ℕ) ^ 256 < 3 * 256 ^ 256 := by
  native_decide

theorem three_pow24_lt_two_pow40 : (3 : ℕ) ^ 24 < 2 ^ 40 := by
  decide

theorem eight_mul_139 : (8 : ℕ) * 139 = 1112 := rfl

theorem pow256_139_eq_two_pow1112 : (256 : ℕ) ^ 139 = 2 ^ 1112 := by
  have h : (256 : ℕ) = 2 ^ 8 := rfl
  rw [h, ← Nat.pow_mul, eight_mul_139]

theorem two_five_six_mul_23_add_150 : (256 : ℕ) * 23 + 150 = 6038 := rfl

theorem one_three_nine_add_6038 : (139 : ℕ) + 6038 = 6177 := rfl

theorem three_nine_nine_zero_add_2048 : (3990 : ℕ) + 2048 = 6038 := rfl

theorem sixteen_mul_128 : (16 : ℕ) * 128 = 2048 := rfl

theorem three_mul_729 : (3 : ℕ) * 729 = 2187 := rfl

theorem two_mul_729 : (2 : ℕ) * 729 = 1458 := rfl

theorem pow257_150_lt_three_mul : (257 : ℕ) ^ 150 < 3 * 256 ^ 150 := by
  have h256 := three_mul_pow256_gt_pow257
  have h106 : (256 : ℕ) ^ 106 < 257 ^ 106 :=
    Nat.pow_lt_pow_left (by decide : (256 : ℕ) < 257) (by decide : (106 : ℕ) ≠ 0)
  have hL : (257 : ℕ) ^ 150 * 256 ^ 106 < 257 ^ 150 * 257 ^ 106 :=
    Nat.mul_lt_mul_of_pos_left h106 (pow_pos (by decide : (0 : ℕ) < 257) 150)
  have hadd : (257 : ℕ) ^ 150 * 257 ^ 106 = 257 ^ 256 := by
    rw [← Nat.pow_add]
  have hlt : (257 : ℕ) ^ 150 * 256 ^ 106 < 257 ^ 256 := hL.trans_eq hadd
  have hR : (3 : ℕ) * 256 ^ 256 = 3 * 256 ^ 150 * 256 ^ 106 := by
    rw [mul_assoc, ← Nat.pow_add]
  have hmid : (257 : ℕ) ^ 150 * 256 ^ 106 < 3 * 256 ^ 150 * 256 ^ 106 :=
    (hlt.trans h256).trans_eq hR
  have hpos : 0 < (256 : ℕ) ^ 106 := pow_pos (by decide : (0 : ℕ) < 256) 106
  exact (Nat.mul_lt_mul_right hpos).mp hmid

theorem pow257_6038_lt_three_pow24_mul :
    (257 : ℕ) ^ 6038 < 3 ^ 24 * 256 ^ 6038 := by
  have h256 := three_mul_pow256_gt_pow257
  have h150 := pow257_150_lt_three_mul
  have hsplit : (257 : ℕ) ^ 6038 = ((257 : ℕ) ^ 256) ^ 23 * 257 ^ 150 := by
    rw [← two_five_six_mul_23_add_150, Nat.pow_add, Nat.pow_mul]
  have hL : ((257 : ℕ) ^ 256) ^ 23 < (3 * 256 ^ 256) ^ 23 :=
    Nat.pow_lt_pow_left h256 (by decide : (23 : ℕ) ≠ 0)
  have hexp : (3 * 256 ^ 256) ^ 23 = 3 ^ 23 * 256 ^ (256 * 23) := by
    rw [mul_pow, ← Nat.pow_mul]
  have hleft : ((257 : ℕ) ^ 256) ^ 23 * 257 ^ 150 <
      (3 * 256 ^ 256) ^ 23 * (3 * 256 ^ 150) :=
    Nat.mul_lt_mul_of_lt_of_lt hL h150
  have hR : (3 * 256 ^ 256) ^ 23 * (3 * 256 ^ 150) =
      3 ^ 24 * 256 ^ 6038 := by
    rw [hexp]
    have h3 : (3 : ℕ) ^ 23 * 3 = 3 ^ 24 := (pow_succ' 3 23).symm
    have h256e : (256 : ℕ) ^ (256 * 23) * 256 ^ 150 = 256 ^ 6038 := by
      rw [← Nat.pow_add, two_five_six_mul_23_add_150]
    rw [mul_assoc, mul_left_comm (256 ^ (256 * 23)), ← mul_assoc, h3, h256e]
  exact (hsplit ▸ hleft).trans_eq hR

theorem pow256_6177_gt_pow257_6038 : (257 : ℕ) ^ 6038 < 256 ^ 6177 := by
  have h1 := pow257_6038_lt_three_pow24_mul
  have h2 := three_pow24_lt_two_pow40
  have h3 : (2 : ℕ) ^ 40 < 2 ^ 1112 :=
    Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2) (by decide : (40 : ℕ) < 1112)
  have h4 := pow256_139_eq_two_pow1112
  have h5 : (3 : ℕ) ^ 24 < 256 ^ 139 := (h2.trans h3).trans_eq h4.symm
  have hmid : (3 : ℕ) ^ 24 * 256 ^ 6038 < 256 ^ 139 * 256 ^ 6038 :=
    Nat.mul_lt_mul_of_pos_right h5 (pow_pos (by decide : (0 : ℕ) < 256) 6038)
  have hsum : (256 : ℕ) ^ 139 * 256 ^ 6038 = 256 ^ 6177 := by
    rw [← Nat.pow_add, one_three_nine_add_6038]
  exact h1.trans (hmid.trans_eq hsum)

theorem succ_pow6038_lt_of_ge_256 {n : ℕ} (hn : 256 ≤ n) :
    (n + 1) ^ 6038 < n ^ 6177 := by
  have hlin : 256 * (n + 1) ≤ 257 * n := by omega
  have hpow : (256 * (n + 1)) ^ 6038 ≤ (257 * n) ^ 6038 :=
    Nat.pow_le_pow_left hlin 6038
  rw [mul_pow, mul_pow] at hpow
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 256) hn
  have hstrict : (257 : ℕ) ^ 6038 * n ^ 6038 < 256 ^ 6177 * n ^ 6038 :=
    Nat.mul_lt_mul_of_pos_right pow256_6177_gt_pow257_6038 (pow_pos hn0 6038)
  have hmid : (256 : ℕ) ^ 6038 * (n + 1) ^ 6038 < 256 ^ 6177 * n ^ 6038 :=
    lt_of_le_of_lt hpow hstrict
  have hsplit : (256 : ℕ) ^ 6177 = 256 ^ 139 * 256 ^ 6038 := by
    rw [← Nat.pow_add, one_three_nine_add_6038]
  have hRHS : (256 : ℕ) ^ 6177 * n ^ 6038 =
      256 ^ 6038 * (256 ^ 139 * n ^ 6038) := by
    rw [hsplit, mul_assoc, mul_left_comm (256 ^ 139)]
  have hpos : 0 < (256 : ℕ) ^ 6038 := pow_pos (by decide : (0 : ℕ) < 256) 6038
  have hcancel : (n + 1) ^ 6038 < 256 ^ 139 * n ^ 6038 :=
    (Nat.mul_lt_mul_left hpos).mp (hmid.trans_eq hRHS)
  have hn139 : (256 : ℕ) ^ 139 ≤ n ^ 139 := Nat.pow_le_pow_left hn 139
  have hle : (256 : ℕ) ^ 139 * n ^ 6038 ≤ n ^ 139 * n ^ 6038 :=
    Nat.mul_le_mul_right _ hn139
  have h6177 : n ^ 139 * n ^ 6038 = n ^ 6177 := by
    rw [← Nat.pow_add, one_three_nine_add_6038]
  exact hcancel.trans_le (hle.trans_eq h6177)

theorem o7_start_preimage {n : ℕ} (hodd : n % 2 = 1) :
    n ^ 2187 < (floorPower n + 1) ^ 1458 := by
  have hcube := odd_cube_lt_succ_sq hodd
  have hpow := Nat.pow_lt_pow_left hcube (by decide : (729 : ℕ) ≠ 0)
  have hL : (n ^ 3) ^ 729 = n ^ 2187 := by
    rw [← Nat.pow_mul, three_mul_729]
  have hR : ((floorPower n + 1) ^ 2) ^ 729 = (floorPower n + 1) ^ 1458 := by
    rw [← Nat.pow_mul, two_mul_729]
  rwa [hL, hR] at hpow

theorem o7_plus_one_chain {n : ℕ} (hn : 1 ≤ n)
    (hw : follows n sevenOdds) :
    n ^ 6177 < (n + 1) ^ 3990 * (image n sevenOdds + 1) ^ 128 := by
  have hw7 : follows n (List.replicate 7 Branch.odd) := by
    simpa [sevenOdds] using hw
  have hodd0 : n % 2 = 1 :=
    follows_replicate_odd_head (by decide : (1 : ℕ) ≤ 7) hw7
  set z1 := image n (List.replicate 1 Branch.odd)
  set z2 := image n (List.replicate 2 Branch.odd)
  set z3 := image n (List.replicate 3 Branch.odd)
  set z4 := image n (List.replicate 4 Branch.odd)
  set z5 := image n (List.replicate 5 Branch.odd)
  set z6 := image n (List.replicate 6 Branch.odd)
  set z7 := image n (List.replicate 7 Branch.odd)
  have hz1 : z1 = floorPower n := by simp [z1, image, List.replicate]
  have hz2 : z2 = floorPower z1 := odd_image_step n 1
  have hz3 : z3 = floorPower z2 := odd_image_step n 2
  have hz4 : z4 = floorPower z3 := odd_image_step n 3
  have hz5 : z5 = floorPower z4 := odd_image_step n 4
  have hz6 : z6 = floorPower z5 := odd_image_step n 5
  have hz7 : z7 = floorPower z6 := odd_image_step n 6
  have hodd1 : z1 % 2 = 1 := odd_image_is_odd (by decide : (1 : ℕ) < 7) hw7
  have hodd2 : z2 % 2 = 1 := odd_image_is_odd (by decide : (2 : ℕ) < 7) hw7
  have hodd3 : z3 % 2 = 1 := odd_image_is_odd (by decide : (3 : ℕ) < 7) hw7
  have hodd4 : z4 % 2 = 1 := odd_image_is_odd (by decide : (4 : ℕ) < 7) hw7
  have hodd5 : z5 % 2 = 1 := odd_image_is_odd (by decide : (5 : ℕ) < 7) hw7
  have hodd6 : z6 % 2 = 1 := odd_image_is_odd (by decide : (6 : ℕ) < 7) hw7
  have hge1 : n ≤ z1 :=
    odd_run_ge hn 1 (follows_odd_take (by decide : (1 : ℕ) ≤ 7) hw7)
  have hge2 : n ≤ z2 :=
    odd_run_ge hn 2 (follows_odd_take (by decide : (2 : ℕ) ≤ 7) hw7)
  have hge3 : n ≤ z3 :=
    odd_run_ge hn 3 (follows_odd_take (by decide : (3 : ℕ) ≤ 7) hw7)
  have hge4 : n ≤ z4 :=
    odd_run_ge hn 4 (follows_odd_take (by decide : (4 : ℕ) ≤ 7) hw7)
  have hge5 : n ≤ z5 :=
    odd_run_ge hn 5 (follows_odd_take (by decide : (5 : ℕ) ≤ 7) hw7)
  have hge6 : n ≤ z6 :=
    odd_run_ge hn 6 (follows_odd_take (by decide : (6 : ℕ) ≤ 7) hw7)
  have h0 : n ^ 2187 < (n + 1) ^ 0 * (z1 + 1) ^ 1458 := by
    have hstart := o7_start_preimage hodd0
    simpa [pow_zero, one_mul, hz1] using hstart
  have h1 : n ^ 3645 < (n + 1) ^ 1458 * (z2 + 1) ^ 972 := by
    have h :=
      absorb_odd_step (n := n) (x := z1) (A := 2187) (B := 0) (t := 486) hn
        (by convert h0) hge1 hodd1 (by decide : (486 : ℕ) ≠ 0)
    simpa [hz2] using h
  have h2 : n ^ 4617 < (n + 1) ^ 2430 * (z3 + 1) ^ 648 := by
    have h :=
      absorb_odd_step (n := n) (x := z2) (A := 3645) (B := 1458) (t := 324) hn
        (by convert h1) hge2 hodd2 (by decide : (324 : ℕ) ≠ 0)
    simpa [hz3] using h
  have h3 : n ^ 5265 < (n + 1) ^ 3078 * (z4 + 1) ^ 432 := by
    have h :=
      absorb_odd_step (n := n) (x := z3) (A := 4617) (B := 2430) (t := 216) hn
        (by convert h2) hge3 hodd3 (by decide : (216 : ℕ) ≠ 0)
    simpa [hz4] using h
  have h4 : n ^ 5697 < (n + 1) ^ 3510 * (z5 + 1) ^ 288 := by
    have h :=
      absorb_odd_step (n := n) (x := z4) (A := 5265) (B := 3078) (t := 144) hn
        (by convert h3) hge4 hodd4 (by decide : (144 : ℕ) ≠ 0)
    simpa [hz5] using h
  have h5 : n ^ 5985 < (n + 1) ^ 3798 * (z6 + 1) ^ 192 := by
    have h :=
      absorb_odd_step (n := n) (x := z5) (A := 5697) (B := 3510) (t := 96) hn
        (by convert h4) hge5 hodd5 (by decide : (96 : ℕ) ≠ 0)
    simpa [hz6] using h
  have h6 : n ^ 6177 < (n + 1) ^ 3990 * (z7 + 1) ^ 128 := by
    have h :=
      absorb_odd_step (n := n) (x := z6) (A := 5985) (B := 3798) (t := 64) hn
        (by convert h5) hge6 hodd6 (by decide : (64 : ℕ) ≠ 0)
    simpa [hz7] using h
  simpa [sevenOdds, z7] using h6

theorem o7_image_ge_succ_pow16 {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n sevenOdds) :
    (n + 1) ^ 16 ≤ image n sevenOdds := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hn
  by_cases hlt : n < 256
  · exact (no_follows_seven_odds_of_lt256 hn hlt hw).elim
  · have hge : 256 ≤ n := Nat.le_of_not_gt hlt
    have hpow := succ_pow6038_lt_of_ge_256 hge
    have hchain := o7_plus_one_chain hn1 hw
    have hpos : 0 < (n + 1) ^ 3990 := pow_pos (Nat.succ_pos n) 3990
    have hmid : (n + 1) ^ 6038 < (n + 1) ^ 3990 * (image n sevenOdds + 1) ^ 128 :=
      hpow.trans hchain
    have hsplit : (n + 1) ^ 6038 = (n + 1) ^ 3990 * (n + 1) ^ 2048 := by
      rw [← Nat.pow_add, three_nine_nine_zero_add_2048]
    have hcancel : (n + 1) ^ 2048 < (image n sevenOdds + 1) ^ 128 := by
      rw [hsplit] at hmid
      exact (Nat.mul_lt_mul_left hpos).mp hmid
    have hexp : ((n + 1) ^ 16) ^ 128 = (n + 1) ^ 2048 := by
      rw [← Nat.pow_mul, sixteen_mul_128]
    have hsucc : (n + 1) ^ 16 < image n sevenOdds + 1 := by
      have h128 : (128 : ℕ) ≠ 0 := Nat.succ_ne_zero _
      have : ((n + 1) ^ 16) ^ 128 < (image n sevenOdds + 1) ^ 128 := by
        rwa [hexp]
      exact (Nat.pow_lt_pow_iff_left h128).mp this
    exact Nat.lt_succ_iff.mp hsucc

theorem no_cycle_itinerary_oooooooeeee {n : ℕ} : ¬CycleItinerary n itineraryO7EEEE := by
  intro h
  have hO : follows n sevenOdds :=
    follows_of_append_left (u := sevenOdds) (v := List.replicate 4 Branch.even) h.1
  have hodd : n % 2 = 1 :=
    follows_replicate_odd_head (by decide : (1 : ℕ) ≤ 7)
      (by simpa [sevenOdds] using hO)
  by_cases h1 : n = 1
  · subst h1
    have hE :
        follows (image 1 sevenOdds) (List.replicate 4 Branch.even) :=
      follows_of_append_right (u := sevenOdds) (v := List.replicate 4 Branch.even)
        (by simpa [itineraryO7EEEE] using h.1)
    have heven : image 1 sevenOdds % 2 = 0 := by
      simpa [List.replicate_succ] using hE.1
    rw [image_one_sevenOdds] at heven
    exact absurd heven (by decide)
  · have hn : 2 ≤ n := by
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by omega)
      omega
    have hge := o7_image_ge_succ_pow16 hn hO
    have hlt :=
      cycle_trailing_evens_lt (n := n) (v := sevenOdds) (r := 4)
        (by decide : (1 : ℕ) ≤ 4) (by simpa [itineraryO7EEEE] using h)
    exact (not_lt_of_ge hge) hlt

end Problems.Juggler
