import Problems.Juggler.CycleCore
import Problems.Juggler.LeftoverEval

set_option maxRecDepth 4000000

namespace Problems.Juggler

/-!
# Leftover prefix one-step preimage

Shared comparison for leftover families: after an odd run of length
`a`, the image `z` sits below a tail one-step preimage `Z`, and the odd-run lower
envelope contradicts that tail.

```text
n ^ (3 ^ a) ≤ 2 ^ denomBits a * z ^ (2 ^ a)
z < Z
2 ^ denomBits a * Z ^ (2 ^ a) < n ^ (3 ^ a)
```

Two-even uses `Z = (n+1)^4`. Bunched uses
`Z ∈ {(n+1)^8, (n+1)^6, (n+1)^4}` or a tight last-odd one-step preimage.
First-E is the same comparison started at `y = T_{O^a E}(n)`.

This is the one-step-preimage schema, not a family exclusion and not a census.
-/

def denomBits (a : ℕ) : ℕ :=
  2 * (3 ^ a - 2 ^ a)

theorem four_eq_two_pow : (4 : ℕ) = 2 ^ 2 := by
  decide

theorem lowerDenomFrom_odd_cons (k o D : ℕ) (w : List Branch) :
    lowerDenomFrom k o D (Branch.odd :: w) =
      lowerDenomFrom (k + 1) (o + 1) (D ^ 3 * 4 ^ (2 ^ k)) w :=
  rfl

theorem lowerDenomFrom_nil (k o D : ℕ) :
    lowerDenomFrom k o D [] = D :=
  rfl

theorem two_pow_mul (n m : ℕ) : (2 ^ n) ^ m = 2 ^ (n * m) :=
  (Nat.pow_mul 2 n m).symm

theorem two_pow_256 : (256 : ℕ) = 2 ^ 8 := by
  decide

/-- For `n ≥ 256`, `(n+1)^64 < 2 n^64`. Uses the isolated `257^64` comparison. -/
theorem succ_pow64_lt {n : ℕ} (hn : 256 ≤ n) :
    (n + 1) ^ 64 < 2 * n ^ 64 := by
  have hlin : 256 * (n + 1) ≤ 257 * n := by omega
  have hpow : (256 * (n + 1)) ^ 64 ≤ (257 * n) ^ 64 :=
    Nat.pow_le_pow_left hlin 64
  rw [mul_pow, mul_pow] at hpow
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 256) hn
  have hstrict : 257 ^ 64 * n ^ 64 < 2 * 256 ^ 64 * n ^ 64 :=
    Nat.mul_lt_mul_of_pos_right two_mul_pow256_gt_pow257 (pow_pos hn0 64)
  have hmid : 256 ^ 64 * (n + 1) ^ 64 < 2 * 256 ^ 64 * n ^ 64 :=
    lt_of_le_of_lt hpow hstrict
  have hRHS : 2 * 256 ^ 64 * n ^ 64 = 256 ^ 64 * (2 * n ^ 64) :=
    calc
      2 * 256 ^ 64 * n ^ 64 = 2 * (256 ^ 64 * n ^ 64) := by rw [mul_assoc]
      _ = (256 ^ 64 * n ^ 64) * 2 := by rw [mul_comm]
      _ = 256 ^ 64 * (n ^ 64 * 2) := by rw [mul_assoc]
      _ = 256 ^ 64 * (2 * n ^ 64) := by rw [mul_comm (n ^ 64)]
  have hpos : 0 < 256 ^ 64 := pow_pos (by decide : (0 : ℕ) < 256) 64
  exact (Nat.mul_lt_mul_left hpos).mp (hmid.trans_eq hRHS)

theorem pow81_gt_two_pow130_succ_pow64 {n : ℕ} (hn : 256 ≤ n) :
    2 ^ 130 * (n + 1) ^ 64 < n ^ 81 := by
  have hsucc := succ_pow64_lt hn
  have hmul : 2 ^ 130 * (n + 1) ^ 64 < 2 ^ 130 * (2 * n ^ 64) :=
    Nat.mul_lt_mul_of_pos_left hsucc (pow_pos (by decide : (0 : ℕ) < 2) 130)
  have hexp : 2 ^ 130 * (2 * n ^ 64) = 2 ^ 131 * n ^ 64 := by
    rw [← mul_assoc, ← pow_succ]
  have h131 : 2 ^ 130 * (n + 1) ^ 64 < 2 ^ 131 * n ^ 64 :=
    hmul.trans_eq hexp
  have hn17 : 2 ^ 136 ≤ n ^ 17 := by
    have hpow : (256 : ℕ) ^ 17 ≤ n ^ 17 := Nat.pow_le_pow_left hn 17
    have h256 : (256 : ℕ) ^ 17 = 2 ^ 136 := by
      rw [two_pow_256, ← Nat.pow_mul]
    exact h256 ▸ hpow
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 256) hn
  have h136 : 2 ^ 131 * n ^ 64 < 2 ^ 136 * n ^ 64 :=
    Nat.mul_lt_mul_of_pos_right
      (Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2) (by decide : (131 : ℕ) < 136))
      (pow_pos hn0 64)
  have hle : 2 ^ 136 * n ^ 64 ≤ n ^ 17 * n ^ 64 :=
    Nat.mul_le_mul_right _ hn17
  have h81 : n ^ 17 * n ^ 64 = n ^ 81 := by
    rw [← Nat.pow_add]
  exact (h131.trans h136).trans_le (hle.trans_eq h81)

theorem pow_lt_of_lt_pow_mul {a b k m : ℕ} (h : a < b ^ k) (hm : m ≠ 0) :
    a ^ m < b ^ (k * m) := by
  have := Nat.pow_lt_pow_left h hm
  rwa [← Nat.pow_mul] at this

theorem two_pow_le_three_pow (a : ℕ) : 2 ^ a ≤ 3 ^ a :=
  Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) a

theorem nat_cast_eq_of_int {a b : ℕ} (h : (a : ℤ) = (b : ℤ)) : a = b :=
  Nat.cast_injective h

theorem denomBits_succ (a : ℕ) :
    denomBits (a + 1) = 3 * denomBits a + 2 ^ (a + 1) := by
  have ha : 2 ^ a ≤ 3 ^ a := two_pow_le_three_pow a
  have ha1 : 2 ^ (a + 1) ≤ 3 ^ (a + 1) := two_pow_le_three_pow (a + 1)
  apply nat_cast_eq_of_int
  simp only [denomBits, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_sub ha, Nat.cast_sub ha1]
  ring

theorem four_exp_odd_succ (k a : ℕ) :
    2 ^ k * 3 ^ a + 2 ^ (k + 1) * (3 ^ a - 2 ^ a) =
      2 ^ k * (3 ^ (a + 1) - 2 ^ (a + 1)) := by
  have ha : 2 ^ a ≤ 3 ^ a := two_pow_le_three_pow a
  have ha1 : 2 ^ (a + 1) ≤ 3 ^ (a + 1) := two_pow_le_three_pow (a + 1)
  apply nat_cast_eq_of_int
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub ha, Nat.cast_sub ha1]
  ring

theorem four_mul_two_pow_sub {k : ℕ} (hk : 2 ≤ k) :
    4 * 2 ^ (k - 2) = 2 ^ k := by
  have h4 : (4 : ℕ) = 2 ^ 2 := rfl
  rw [h4, ← Nat.pow_add, Nat.add_sub_of_le hk]

theorem two_mul_two_pow (t : ℕ) : 2 * 2 ^ t = 2 ^ (t + 1) := by
  rw [pow_succ, mul_comm]

theorem two_mul_two_pow_pred {k : ℕ} (hk : 1 ≤ k) :
    2 * 2 ^ (k - 1) = 2 ^ k := by
  rw [two_mul_two_pow]
  congr 1
  omega

theorem two_mul_pow_cube (e y m : ℕ) :
    (2 ^ e * y ^ m) ^ 3 = 2 ^ (3 * e) * y ^ (3 * m) := by
  rw [mul_pow, two_pow_mul, ← Nat.pow_mul, Nat.mul_comm e 3, Nat.mul_comm m 3]

theorem three_mul_two_pow (k : ℕ) :
    3 * 2 ^ k = 2 ^ k + 2 ^ (k + 1) := by
  rw [pow_succ]
  ring

theorem three_pow_succ_sub {k : ℕ} (hk : 3 ≤ k) :
    3 ^ (k - 3) * 3 = 3 ^ (k - 2) := by
  rw [← Nat.pow_succ]
  congr 1
  omega

theorem three_pow_succ_sub_two {k : ℕ} (hk : 2 ≤ k) :
    3 ^ (k - 2) * 3 = 3 ^ (k - 1) := by
  rw [← Nat.pow_succ]
  congr 1
  omega

theorem lowerDenomFrom_replicate_odd (k o D a : ℕ) :
    lowerDenomFrom k o D (List.replicate a Branch.odd) =
      D ^ (3 ^ a) * 4 ^ (2 ^ k * (3 ^ a - 2 ^ a)) := by
  induction a generalizing k o D with
  | zero =>
      rw [List.replicate_zero, lowerDenomFrom_nil]
      simp
  | succ a ih =>
      rw [List.replicate_succ, lowerDenomFrom_odd_cons, ih]
      have hD : (D ^ 3 * 4 ^ (2 ^ k)) ^ (3 ^ a) =
          D ^ (3 ^ (a + 1)) * 4 ^ (2 ^ k * 3 ^ a) := by
        rw [mul_pow, ← Nat.pow_mul, Nat.pow_mul 4 (2 ^ k) (3 ^ a)]
        congr 2
        rw [Nat.mul_comm, ← Nat.pow_succ]
      rw [hD, mul_assoc, ← Nat.pow_add, four_exp_odd_succ]

theorem lowerDenom_replicate_odd (a : ℕ) :
    lowerDenom (List.replicate a Branch.odd) = 2 ^ denomBits a := by
  rw [lowerDenom, lowerDenomFrom_replicate_odd, one_pow, pow_zero, one_mul]
  rw [four_eq_two_pow, ← Nat.pow_mul]
  unfold denomBits
  congr 1
  ring

theorem odd_run_lower_growth {n a : ℕ} (hn : 1 ≤ n)
    (hw : follows n (List.replicate a Branch.odd)) :
    n ^ (3 ^ a) ≤
      2 ^ denomBits a * image n (List.replicate a Branch.odd) ^ (2 ^ a) := by
  have hL := lower_growth_word hn hw
  simpa [LowerPowerBound, oddCount_replicate_odd, List.length_replicate,
    lowerDenom_replicate_odd] using hL

theorem denomBits_four : denomBits 4 = 130 := by
  decide +kernel

theorem three_pow_four : (3 : ℕ) ^ 4 = 81 := by
  decide

theorem two_pow_six : (2 : ℕ) ^ 6 = 64 := by
  decide

theorem shared_two_even_tail_succ {n k : ℕ} (hn : 256 ≤ n) (hk : 6 ≤ k)
    (ih : 2 ^ denomBits (k - 2) * (n + 1) ^ (2 ^ k) < n ^ (3 ^ (k - 2))) :
    2 ^ denomBits (k - 1) * (n + 1) ^ (2 ^ (k + 1)) < n ^ (3 ^ (k - 1)) := by
  have hk1 : 1 ≤ k := le_trans (by decide : (1 : ℕ) ≤ 6) hk
  have hk2 : 2 ≤ k := le_trans (by decide : (2 : ℕ) ≤ 6) hk
  have hcube :
      2 ^ (3 * denomBits (k - 2)) * (n + 1) ^ (3 * 2 ^ k) <
        n ^ (3 ^ (k - 1)) := by
    have hlt :
        (2 ^ denomBits (k - 2) * (n + 1) ^ (2 ^ k)) ^ 3 <
          (n ^ (3 ^ (k - 2))) ^ 3 :=
      Nat.pow_lt_pow_left ih (by decide : (3 : ℕ) ≠ 0)
    have hL : (2 ^ denomBits (k - 2) * (n + 1) ^ (2 ^ k)) ^ 3 =
        2 ^ (3 * denomBits (k - 2)) * (n + 1) ^ (3 * 2 ^ k) :=
      two_mul_pow_cube _ _ _
    have hR : (n ^ (3 ^ (k - 2))) ^ 3 = n ^ (3 ^ (k - 1)) := by
      rw [← Nat.pow_mul, three_pow_succ_sub_two hk2]
    rwa [hL, hR] at hlt
  have hsucc2 : 2 < (n + 1) ^ 2 := by
    have h4 : (4 : ℕ) ≤ (n + 1) ^ 2 := by
      have : 2 ≤ n + 1 := by omega
      simpa using Nat.pow_le_pow_left this 2
    exact lt_of_lt_of_le (by decide : (2 : ℕ) < 4) h4
  have hpow2 : 2 ^ (2 ^ (k - 1)) < (n + 1) ^ (2 ^ k) := by
    have hm : 2 ^ (k - 1) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
    have : 2 ^ (2 ^ (k - 1)) < ((n + 1) ^ 2) ^ (2 ^ (k - 1)) :=
      Nat.pow_lt_pow_left hsucc2 hm
    rwa [← Nat.pow_mul, two_mul_two_pow_pred hk1] at this
  have he' : denomBits (k - 1) = 3 * denomBits (k - 2) + 2 ^ (k - 1) := by
    have hsub : k - 1 = (k - 2) + 1 := by omega
    rw [hsub, denomBits_succ]
  have hfactor :
      2 ^ denomBits (k - 1) * (n + 1) ^ (2 ^ (k + 1)) <
        2 ^ (3 * denomBits (k - 2)) * (n + 1) ^ (3 * 2 ^ k) := by
    have hL :
        2 ^ denomBits (k - 1) * (n + 1) ^ (2 ^ (k + 1)) =
          2 ^ (3 * denomBits (k - 2)) *
            (2 ^ (2 ^ (k - 1)) * (n + 1) ^ (2 ^ (k + 1))) := by
      rw [he', Nat.pow_add, mul_assoc]
    have hR :
        2 ^ (3 * denomBits (k - 2)) * (n + 1) ^ (3 * 2 ^ k) =
          2 ^ (3 * denomBits (k - 2)) *
            ((n + 1) ^ (2 ^ k) * (n + 1) ^ (2 ^ (k + 1))) := by
      congr 1
      rw [← Nat.pow_add, three_mul_two_pow]
    have hpos2 : 0 < 2 ^ (3 * denomBits (k - 2)) :=
      pow_pos (by decide : (0 : ℕ) < 2) _
    have hposn : 0 < (n + 1) ^ (2 ^ (k + 1)) :=
      pow_pos (Nat.succ_pos n) _
    rw [hL, hR]
    exact Nat.mul_lt_mul_of_pos_left
      (Nat.mul_lt_mul_of_pos_right hpow2 hposn) hpos2
  exact hfactor.trans hcube

theorem shared_two_even_tail {n k : ℕ} (hn : 256 ≤ n) (hk : 6 ≤ k) :
    2 ^ denomBits (k - 2) * (n + 1) ^ (2 ^ k) < n ^ (3 ^ (k - 2)) := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hk
  subst ht
  clear hk
  induction t with
  | zero =>
      simpa [denomBits_four, three_pow_four, two_pow_six] using
        pow81_gt_two_pow130_succ_pow64 hn
  | succ t ih =>
      have h :=
        shared_two_even_tail_succ (k := 6 + t) hn (Nat.le_add_right 6 t) ih
      have h1 : 6 + t - 1 = 6 + (t + 1) - 2 := by omega
      have h2 : 6 + t + 1 = 6 + (t + 1) := by omega
      simpa [h1, h2] using h

theorem succ_sq_gt_mul_add_two {n : ℕ} (_hn : 1 ≤ n) :
    n * (n + 2) < (n + 1) ^ 2 := by
  have : n * (n + 2) + 1 = (n + 1) ^ 2 := by ring
  omega

theorem persist_succ_pow {n p q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hpq : q ≤ p) :
    n ^ p * (n + 2) ^ q < (n + 1) ^ (p + q) := by
  have hsq : n * (n + 2) < (n + 1) ^ 2 := succ_sq_gt_mul_add_two hn
  have hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  have hpair : (n * (n + 2)) ^ q < ((n + 1) ^ 2) ^ q :=
    Nat.pow_lt_pow_left hsq hq0
  have hcore : n ^ q * (n + 2) ^ q < (n + 1) ^ (2 * q) := by
    rwa [mul_pow, ← Nat.pow_mul] at hpair
  have hrest : n ^ (p - q) ≤ (n + 1) ^ (p - q) :=
    Nat.pow_le_pow_left (Nat.le_succ n) _
  have hmid : n ^ (p - q) * (n ^ q * (n + 2) ^ q) <
      (n + 1) ^ (p - q) * (n + 1) ^ (2 * q) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hrest)
      (Nat.mul_lt_mul_of_pos_left hcore (pow_pos (Nat.succ_pos n) _))
  have hL : n ^ (p - q) * (n ^ q * (n + 2) ^ q) =
      n ^ p * (n + 2) ^ q := by
    rw [← mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hpq]
  have hR : (n + 1) ^ (p - q) * (n + 1) ^ (2 * q) =
      (n + 1) ^ (p + q) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rwa [hL, hR] at hmid


theorem leftover_prefix_preimage {n a z Z : ℕ}
    (hgrow : n ^ (3 ^ a) ≤ 2 ^ denomBits a * z ^ (2 ^ a))
    (hz : z < Z)
    (htail : 2 ^ denomBits a * Z ^ (2 ^ a) < n ^ (3 ^ a)) :
    False := by
  have hm : 2 ^ a ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) a)
  have hzpow : z ^ (2 ^ a) < Z ^ (2 ^ a) := Nat.pow_lt_pow_left hz hm
  have hlt : n ^ (3 ^ a) < 2 ^ denomBits a * Z ^ (2 ^ a) :=
    lt_of_le_of_lt hgrow
      (Nat.mul_lt_mul_of_pos_left hzpow
        (pow_pos (by decide : (0 : ℕ) < 2) _))
  exact (not_lt_of_gt htail) hlt

end Problems.Juggler
