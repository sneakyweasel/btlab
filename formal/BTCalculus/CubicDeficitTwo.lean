import BTCalculus.CubicDeepestLayer

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Depth deficit r = 2: residual depth m = k-3.

The general visibility law
  N2 equality iff 3^r divides p - q
at m = k-1-r is a direct specialisation of `sameDepth_n2_succ`.
At r = 2 this is congruence modulo 9.
-/

def deficitTwoN2 (k : Nat) (p : Int) : Int :=
  2 * (3 : Int) ^ (k - 2) * p

def deficitTwoN1 (p : Int) (k : Nat) : Int :=
  3 * p ^ 2 + (3 : Int) ^ (k - 2) * p

/-- At depth `k-1-r`, `N2` residuals agree modulo `3^k` exactly when `p = q` modulo `3^r`: the deficit `r` is what the layer can see. -/
theorem depthDeficit_n2_visibility {k r : Nat} (hr : r + 1 ≤ k) (p q : Int) :
    (3 : Int) ^ k ∣ n2Resid (k - 1 - r) p - n2Resid (k - 1 - r) q ↔
      (3 : Int) ^ r ∣ p - q := by
  have hle : (k - 1 - r) + 1 ≤ k := by omega
  have hsucc := sameDepth_n2_succ (k := k) (m := k - 1 - r) hle p q
  have hexp : k - ((k - 1 - r) + 1) = r := by omega
  simpa [hexp] using hsucc

/-- At deficit zero the `N2` condition is automatic. -/
theorem depthDeficit_zero_N2 {k : Nat} (hk : 1 ≤ k) (p q : Int) :
    (3 : Int) ^ k ∣ n2Resid (k - 1) p - n2Resid (k - 1) q := by
  have h := (depthDeficit_n2_visibility (k := k) (r := 0) (by omega) p q).2
  have : (3 : Int) ^ 0 ∣ p - q := by simp
  exact h this

/-- At deficit one the `N2` condition reduces to `3 | p - q`. -/
theorem depthDeficit_one_N2 {k : Nat} (hk : 2 ≤ k) (p q : Int) :
    (3 : Int) ^ k ∣ n2Resid (k - 2) p - n2Resid (k - 2) q ↔
      (3 : Int) ∣ p - q := by
  have hdepth : k - 1 - 1 = k - 2 := by omega
  simpa [pow_one, hdepth] using
    depthDeficit_n2_visibility (k := k) (r := 1) (by omega) p q

/-- At deficit two the `N2` condition reduces to `9 | p - q`. -/
theorem depthDeficit_two_N2_visibility {k : Nat} (hk : 3 ≤ k) (p q : Int) :
    (3 : Int) ^ k ∣ n2Resid (k - 3) p - n2Resid (k - 3) q ↔
      (3 : Int) ^ 2 ∣ p - q := by
  have hdepth : k - 1 - 2 = k - 3 := by omega
  simpa [hdepth] using depthDeficit_n2_visibility (k := k) (r := 2) (by omega) p q

/-- At deficit two, `N3` vanishes modulo `3^k` once `k >= 5`. -/
theorem deficitTwo_n3_zero {k : Nat} (hk : 5 ≤ k) :
    (3 : Int) ^ k ∣ n3Resid (k - 3) := by
  unfold n3Resid
  have hle : k ≤ 2 * (k - 3) + 1 := by omega
  have hpow : (3 : Int) ^ k ∣ (3 : Int) ^ (2 * (k - 3) + 1) :=
    pow_dvd_pow _ hle
  have := hpow.mul_left (2 : Int)
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- At deficit two, `N2` is congruent to `2 * 3^(k-2) p` modulo `3^k`, for `k >= 5`. -/
theorem deficitTwo_n2_mod {k : Nat} (hk : 5 ≤ k) (p : Int) :
    (3 : Int) ^ k ∣ n2Resid (k - 3) p - deficitTwoN2 k p := by
  unfold n2Resid deficitTwoN2
  have hm : (k - 3) + 1 = k - 2 := by omega
  rw [hm]
  have hle : k ≤ (k - 2) + (k - 3) := by omega
  have hpow : (3 : Int) ^ k ∣ (3 : Int) ^ ((k - 2) + (k - 3)) :=
    pow_dvd_pow _ hle
  have hA : (3 : Int) ^ k ∣ 2 * ((3 : Int) ^ (k - 2) * (3 : Int) ^ (k - 3)) := by
    rw [← pow_add]
    exact hpow.mul_left (2 : Int)
  convert hA using 1
  ring

/-- At deficit two, `N1` is congruent to `3p^2 + 3^(k-2) p` modulo `3^k`, for `k >= 6`. -/
theorem deficitTwo_n1_mod {k : Nat} (hk : 6 ≤ k) (p : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 3) p - deficitTwoN1 p k := by
  unfold n1Resid deficitTwoN1
  have hm : (k - 3) + 1 = k - 2 := by omega
  rw [hm]
  have hle : k ≤ 2 * (k - 3) := by omega
  have hA : (3 : Int) ^ k ∣ (3 : Int) ^ (2 * (k - 3)) := pow_dvd_pow _ hle
  convert hA using 1
  ring

/-- The deficit-two `N1` condition, reduced to a divisibility at order `k-1`. -/
theorem deficitTwo_n1_iff {k : Nat} (hk : 1 ≤ k) (p q : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 3) p - n1Resid (k - 3) q ↔
      (3 : Int) ^ (k - 1) ∣ (p - q) * (p + q + (3 : Int) ^ (k - 3)) := by
  rw [n1Resid_diff]
  have hshape : (3 : Int) ^ k = 3 * (3 : Int) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  constructor
  · intro h
    have : (3 : Int) ^ k ∣ 3 * ((p - q) * (p + q + (3 : Int) ^ (k - 3))) := by
      simpa [mul_assoc] using h
    rw [hshape] at this
    have hnz : (3 : Int) ≠ 0 := by decide
    exact (mul_dvd_mul_iff_left hnz).mp this
  · intro h
    have : (3 : Int) ^ k ∣ 3 * ((p - q) * (p + q + (3 : Int) ^ (k - 3))) := by
      rw [hshape]
      exact mul_dvd_mul_left _ h
    simpa [mul_assoc] using this

/-- The deficit-two `N1` condition once `N2` has forced `9 | p - q`. -/
theorem deficitTwo_n1_after_n2 {k : Nat} (hk : 3 ≤ k) {p q d : Int}
    (hd : p - q = 9 * d) :
    (3 : Int) ^ k ∣ n1Resid (k - 3) p - n1Resid (k - 3) q ↔
      (3 : Int) ^ (k - 3) ∣ d * (p + q + (3 : Int) ^ (k - 3)) := by
  have hk1 : 1 ≤ k := by omega
  rw [deficitTwo_n1_iff hk1]
  have hshape : (3 : Int) ^ (k - 1) = 9 * (3 : Int) ^ (k - 3) := by
    have : k - 1 = (k - 3) + 2 := by omega
    rw [this, pow_add, pow_two]
    ring
  constructor
  · intro h
    rw [hd, hshape] at h
    have hnz : (9 : Int) ≠ 0 := by decide
    exact (mul_dvd_mul_iff_left hnz).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h)
  · intro h
    rw [hd, hshape]
    have := mul_dvd_mul_left (9 : Int) h
    simpa [mul_assoc] using this

/-- The deficit-two fibre criterion: `N2` and `N1` agreement at depth `k-3` together, spelled out as the congruence modulo `9`, the order-`(k-1)` product condition, and `N0`. -/
theorem deficitTwo_equiv_iff {k : Nat} (hk : 3 ≤ k) (p q : Int) :
    ((3 : Int) ^ k ∣ n2Resid (k - 3) p - n2Resid (k - 3) q) ∧
        ((3 : Int) ^ k ∣ n1Resid (k - 3) p - n1Resid (k - 3) q) ∧
          ((3 : Int) ^ k ∣ n0Resid (k - 3) p - n0Resid (k - 3) q) ↔
      ((3 : Int) ^ 2 ∣ p - q) ∧
        ((3 : Int) ^ (k - 1) ∣ (p - q) * (p + q + (3 : Int) ^ (k - 3))) ∧
          ((3 : Int) ^ k ∣ n0Resid (k - 3) p - n0Resid (k - 3) q) := by
  constructor
  · intro ⟨h2, h1, h0⟩
    exact ⟨(depthDeficit_two_N2_visibility hk p q).1 h2,
      (deficitTwo_n1_iff (by omega) p q).1 h1, h0⟩
  · intro ⟨h2, h1, h0⟩
    exact ⟨(depthDeficit_two_N2_visibility hk p q).2 h2,
      (deficitTwo_n1_iff (by omega) p q).2 h1, h0⟩

/-- At deficit two the `N2` sign condition holds exactly when `9` divides `p`. -/
theorem deficitTwo_sign_n2_iff {k : Nat} (hk : 3 ≤ k) (p : Int) :
    (3 : Int) ^ k ∣ n2Resid (k - 3) p - n2Resid (k - 3) (-p) ↔
      (3 : Int) ^ 2 ∣ p := by
  rw [depthDeficit_two_N2_visibility hk]
  constructor
  · intro h
    have h2p : (3 : Int) ^ 2 ∣ 2 * p := by
      convert h using 1
      ring
    have h3 : (3 : Int) ∣ 2 * p :=
      dvd_trans (pow_dvd_pow (3 : Int) (by decide : 1 ≤ 2)) h2p
    have hp : (3 : Int) ∣ p :=
      three_pow_dvd_of_two_mul (k := 1) (by simpa [pow_one] using h3)
    obtain ⟨t, ht⟩ := hp
    have h6 : (3 : Int) ^ 2 ∣ 6 * t := by
      convert h2p using 1
      rw [ht]
      ring
    have ht2 : (3 : Int) ∣ 2 * t := by
      have h6' : 6 * t = 3 * (2 * t) := by ring
      have : (3 : Int) ^ 2 ∣ 3 * (2 * t) := by simpa [h6'] using h6
      have hpow : (3 : Int) ^ 2 = 3 * 3 := by norm_num
      rw [hpow] at this
      have hnz : (3 : Int) ≠ 0 := by decide
      exact (mul_dvd_mul_iff_left hnz).mp this
    have ht3 : (3 : Int) ∣ t :=
      three_pow_dvd_of_two_mul (k := 1) (by simpa [pow_one] using ht2)
    obtain ⟨s, hs⟩ := ht3
    exact ⟨s, by rw [ht, hs]; ring⟩
  · intro h
    have := h.mul_left (2 : Int)
    have heq : (2 : Int) * p = p + p := by ring
    simpa [heq] using this

/-- Deficit-two agreement at horizon `k` carries down to the finer horizon. -/
theorem deficitTwo_horizon_refines {k : Nat} (_hk : 1 ≤ k) (p q : Int)
    (h2 : (3 : Int) ^ k ∣ n2Resid (k - 3) p - n2Resid (k - 3) q)
    (h1 : (3 : Int) ^ k ∣ n1Resid (k - 3) p - n1Resid (k - 3) q)
    (h0 : (3 : Int) ^ k ∣ n0Resid (k - 3) p - n0Resid (k - 3) q) :
    ((3 : Int) ^ (k - 1) ∣ n2Resid (k - 3) p - n2Resid (k - 3) q) ∧
      ((3 : Int) ^ (k - 1) ∣ n1Resid (k - 3) p - n1Resid (k - 3) q) ∧
        ((3 : Int) ^ (k - 1) ∣ n0Resid (k - 3) p - n0Resid (k - 3) q) := by
  have hpow : (3 : Int) ^ (k - 1) ∣ (3 : Int) ^ k :=
    pow_dvd_pow (3 : Int) (Nat.sub_le k 1)
  exact ⟨hpow.trans h2, hpow.trans h1, hpow.trans h0⟩

end BTCalculus
