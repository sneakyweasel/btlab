import BTCalculus.CubicFibres

noncomputable section

namespace BTCalculus

open Polynomial

/-!
First intermediate cubic layer: depth m = k-2.

N3 vanishes for k ≥ 3. N2 reduces to the congruence
3 ∣ p - q. N1 is the first correction
3^{k-1} ∣ (p-q)(p+q+3^{k-2}). The complete fibre criterion
is the conjunction of N2, N1, and N0.
-/

def interN2 (k : ℕ) (p : ℤ) : ℤ :=
  2 * (3 : ℤ) ^ (k - 1) * p

def interN1 (p : ℤ) (k : ℕ) : ℤ :=
  3 * p ^ 2 + (3 : ℤ) ^ (k - 1) * p

theorem inter_n3_zero {k : ℕ} (hk : 3 ≤ k) :
    (3 : ℤ) ^ k ∣ n3Resid (k - 2) := by
  unfold n3Resid
  have hle : k ≤ 2 * (k - 2) + 1 := by omega
  have hpow : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (2 * (k - 2) + 1) :=
    pow_dvd_pow _ hle
  have := hpow.mul_left (2 : ℤ)
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

theorem inter_n2_mod {k : ℕ} (hk : 3 ≤ k) (p : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid (k - 2) p - interN2 k p := by
  unfold n2Resid interN2
  have hm : (k - 2) + 1 = k - 1 := by omega
  rw [hm]
  have hle : k ≤ (k - 1) + (k - 2) := by omega
  have hpow : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ ((k - 1) + (k - 2)) :=
    pow_dvd_pow _ hle
  have hA : (3 : ℤ) ^ k ∣ 2 * ((3 : ℤ) ^ (k - 1) * (3 : ℤ) ^ (k - 2)) := by
    rw [← pow_add]
    exact hpow.mul_left (2 : ℤ)
  convert hA using 1
  ring

theorem inter_n2_iff {k : ℕ} (hk : 2 ≤ k) (p q : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid (k - 2) p - n2Resid (k - 2) q ↔
      (3 : ℤ) ∣ p - q := by
  have hle : (k - 2) + 1 ≤ k := by omega
  have hsucc := sameDepth_n2_succ (k := k) (m := k - 2) hle p q
  have hexp : k - ((k - 2) + 1) = 1 := by omega
  simpa [hexp, pow_one] using hsucc

theorem inter_n1_mod {k : ℕ} (hk : 4 ≤ k) (p : ℤ) :
    (3 : ℤ) ^ k ∣ n1Resid (k - 2) p - interN1 p k := by
  unfold n1Resid interN1
  have hm : (k - 2) + 1 = k - 1 := by omega
  rw [hm]
  have hle : k ≤ 2 * (k - 2) := by omega
  have hA : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (2 * (k - 2)) := pow_dvd_pow _ hle
  convert hA using 1
  ring

theorem inter_n1_iff {k : ℕ} (hk : 1 ≤ k) (p q : ℤ) :
    (3 : ℤ) ^ k ∣ n1Resid (k - 2) p - n1Resid (k - 2) q ↔
      (3 : ℤ) ^ (k - 1) ∣ (p - q) * (p + q + (3 : ℤ) ^ (k - 2)) := by
  rw [n1Resid_diff]
  have hshape : (3 : ℤ) ^ k = 3 * (3 : ℤ) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  constructor
  · intro h
    have : (3 : ℤ) ^ k ∣ 3 * ((p - q) * (p + q + (3 : ℤ) ^ (k - 2))) := by
      simpa [mul_assoc] using h
    rw [hshape] at this
    have hnz : (3 : ℤ) ≠ 0 := by decide
    exact (mul_dvd_mul_iff_left hnz).mp this
  · intro h
    have : (3 : ℤ) ^ k ∣ 3 * ((p - q) * (p + q + (3 : ℤ) ^ (k - 2))) := by
      rw [hshape]
      exact mul_dvd_mul_left _ h
    simpa [mul_assoc] using this

theorem inter_sign_n2_iff {k : ℕ} (hk : 2 ≤ k) (p : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid (k - 2) p - n2Resid (k - 2) (-p) ↔
      (3 : ℤ) ∣ p := by
  rw [inter_n2_iff hk]
  constructor
  · intro h
    have : (3 : ℤ) ∣ 2 * p := by
      have heq : p + p = 2 * p := by ring
      simpa [heq] using h
    exact three_pow_dvd_of_two_mul (k := 1) (by simpa [pow_one] using this)
  · intro h
    have := h.mul_left (2 : ℤ)
    have heq : 2 * p = p + p := by ring
    simpa [heq] using this

theorem inter_sign_n1_iff {k : ℕ} (hk : 2 ≤ k) (p : ℤ) :
    (3 : ℤ) ^ k ∣ n1Resid (k - 2) p - n1Resid (k - 2) (-p) ↔
      (3 : ℤ) ∣ p := by
  have hk1 : 1 ≤ k := by omega
  rw [inter_n1_iff hk1]
  have hprod : (p - (-p)) * (p + (-p) + (3 : ℤ) ^ (k - 2)) =
      2 * p * (3 : ℤ) ^ (k - 2) := by ring
  rw [hprod]
  have hshape : (3 : ℤ) ^ (k - 1) = 3 * (3 : ℤ) ^ (k - 2) := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, pow_succ']
  constructor
  · intro h
    rw [hshape] at h
    have hnz : (3 : ℤ) ^ (k - 2) ≠ 0 := pow_ne_zero _ (by decide)
    have : (3 : ℤ) ∣ 2 * p := (mul_dvd_mul_iff_right hnz).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h)
    exact three_pow_dvd_of_two_mul (k := 1) (by simpa [pow_one] using this)
  · intro h
    rw [hshape]
    exact mul_dvd_mul (by simpa using h.mul_left (2 : ℤ)) (dvd_refl _)

theorem inter_sign_n1_of_n2 {k : ℕ} (hk : 2 ≤ k) {p : ℤ}
    (h : (3 : ℤ) ∣ p) :
    (3 : ℤ) ^ k ∣ n1Resid (k - 2) p - n1Resid (k - 2) (-p) :=
  (inter_sign_n1_iff hk p).2 h

theorem inter_equiv_iff {k : ℕ} (hk : 2 ≤ k) (p q : ℤ) :
    ((3 : ℤ) ^ k ∣ n2Resid (k - 2) p - n2Resid (k - 2) q) ∧
        ((3 : ℤ) ^ k ∣ n1Resid (k - 2) p - n1Resid (k - 2) q) ∧
          ((3 : ℤ) ^ k ∣ n0Resid (k - 2) p - n0Resid (k - 2) q) ↔
      ((3 : ℤ) ∣ p - q) ∧
        ((3 : ℤ) ^ (k - 1) ∣ (p - q) * (p + q + (3 : ℤ) ^ (k - 2))) ∧
          ((3 : ℤ) ^ k ∣ n0Resid (k - 2) p - n0Resid (k - 2) q) := by
  constructor
  · intro ⟨h2, h1, h0⟩
    exact ⟨(inter_n2_iff hk p q).1 h2,
      (inter_n1_iff (by omega) p q).1 h1, h0⟩
  · intro ⟨h2, h1, h0⟩
    exact ⟨(inter_n2_iff hk p q).2 h2,
      (inter_n1_iff (by omega) p q).2 h1, h0⟩

/-- Horizon refinement at depth `k-2`: agreement of the `N2`, `N1` and `N0` residuals to
order `3^k` carries down to order `3^(k-1)` for each of the three. -/
theorem inter_horizon_refines {k : ℕ} (_hk : 1 ≤ k) (p q : ℤ)
    (h2 : (3 : ℤ) ^ k ∣ n2Resid (k - 2) p - n2Resid (k - 2) q)
    (h1 : (3 : ℤ) ^ k ∣ n1Resid (k - 2) p - n1Resid (k - 2) q)
    (h0 : (3 : ℤ) ^ k ∣ n0Resid (k - 2) p - n0Resid (k - 2) q) :
    ((3 : ℤ) ^ (k - 1) ∣ n2Resid (k - 2) p - n2Resid (k - 2) q) ∧
      ((3 : ℤ) ^ (k - 1) ∣ n1Resid (k - 2) p - n1Resid (k - 2) q) ∧
        ((3 : ℤ) ^ (k - 1) ∣ n0Resid (k - 2) p - n0Resid (k - 2) q) := by
  have hpow : (3 : ℤ) ^ (k - 1) ∣ (3 : ℤ) ^ k :=
    pow_dvd_pow (3 : ℤ) (Nat.sub_le k 1)
  exact ⟨hpow.trans h2, hpow.trans h1, hpow.trans h0⟩

theorem unit_sign_n2_splits {k : ℕ} (hk : 2 ≤ k) :
    ¬ (3 : ℤ) ^ k ∣ n2Resid (k - 2) 1 - n2Resid (k - 2) (-1) := by
  intro h
  have h2 := (inter_n2_iff hk 1 (-1)).1 h
  exact (by decide : ¬ (3 : ℤ) ∣ (1 - (-1 : ℤ))) h2

end BTCalculus
