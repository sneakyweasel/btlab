import Mathlib.Algebra.Order.Group.Abs
import BTCalculus.CubicResidual
import BTCalculus.Rewrite

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Fibres of the cubic Newton image map.

Same-depth collisions of residuals of `X^3` are decided by the
Newton coordinates `N2, N1, N0`. Cross-depth collisions require
both depths to satisfy `2m+1 ≥ k`.
-/

def balWidth (m : ℕ) (p : ℤ) : Prop :=
  2 * |p| ≤ (3 : ℤ) ^ m - 1

def n2Resid (m : ℕ) (p : ℤ) : ℤ :=
  2 * (3 : ℤ) ^ (m + 1) * (p + (3 : ℤ) ^ m)

def n1Resid (m : ℕ) (p : ℤ) : ℤ :=
  (3 : ℤ) ^ (2 * m) + (3 : ℤ) ^ (m + 1) * p + 3 * p ^ 2

def n3Resid (m : ℕ) : ℤ :=
  2 * (3 : ℤ) ^ (2 * m + 1)

def n0Resid (m : ℕ) (p : ℤ) : ℤ :=
  iterDZ m (p ^ 3)

/-- `N2(p) - N2(q) = 2 * 3^(m+1) * (p - q)`. -/
theorem n2Resid_diff (m : ℕ) (p q : ℤ) :
    n2Resid m p - n2Resid m q = 2 * (3 : ℤ) ^ (m + 1) * (p - q) := by
  unfold n2Resid
  ring

/-- `N1(p) - N1(q) = 3 (p - q)(p + q + 3^m)` -- the factorisation the fibre argument uses. -/
theorem n1Resid_diff (m : ℕ) (p q : ℤ) :
    n1Resid m p - n1Resid m q = 3 * (p - q) * (p + q + (3 : ℤ) ^ m) := by
  unfold n1Resid
  ring

/-- `N3(m) - N3(n) = 2 (3^(2m+1) - 3^(2n+1))`; `N3` does not depend on the point. -/
theorem n3Resid_sub (m n : ℕ) :
    n3Resid m - n3Resid n =
      2 * ((3 : ℤ) ^ (2 * m + 1) - (3 : ℤ) ^ (2 * n + 1)) := by
  unfold n3Resid
  ring

/-- The third Newton coordinate of the residual family is `N2`. -/
theorem newton_n2_eq (m : ℕ) (p : ℤ) :
    (newtonCoords ((3 : ℤ) ^ (2 * m)) ((3 : ℤ) ^ (m + 1) * p)
        (3 * p ^ 2) (iterDZ m (p ^ 3))).2.2.1 =
      n2Resid m p := by
  have h := newton_cubicResid m p
  simpa [n2Resid] using congrArg (fun t => t.2.2.1) h

/-- At one depth, `3^k` divides the `N2` difference exactly when it divides `3^(m+1)(p - q)`. -/
theorem sameDepth_n2 (k m : ℕ) (p q : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m q ↔
      (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (m + 1) * (p - q) := by
  rw [n2Resid_diff]
  constructor
  · intro h
    exact three_pow_dvd_of_two_mul (by simpa [mul_assoc] using h)
  · intro h
    have := h.mul_left (2 : ℤ)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this

/-- Below the depth, `k <= m + 1`, the `N2` difference is divisible outright. -/
theorem sameDepth_n2_of_le {k m : ℕ} (hkm : k ≤ m + 1) (p q : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m q := by
  rw [sameDepth_n2]
  have : (3 : ℤ) ^ (m + 1) ∣ (3 : ℤ) ^ (m + 1) * (p - q) :=
    dvd_mul_right _ _
  exact dvd_trans (pow_dvd_pow (3 : ℤ) hkm) this

/-- Above the depth, `m + 1 <= k`, the `N2` condition reduces to `3^(k-m-1) | p - q`. -/
theorem sameDepth_n2_succ {k m : ℕ} (hkm : m + 1 ≤ k) (p q : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m q ↔
      (3 : ℤ) ^ (k - (m + 1)) ∣ (p - q) := by
  rw [sameDepth_n2]
  have hpow : (3 : ℤ) ^ k = (3 : ℤ) ^ (m + 1) * (3 : ℤ) ^ (k - (m + 1)) := by
    rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hkm]
  constructor
  · intro h
    rw [hpow] at h
    have hnz : (3 : ℤ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by decide)
    exact (mul_dvd_mul_iff_left hnz).mp (by simpa [mul_comm] using h)
  · intro h
    rw [hpow]
    exact mul_dvd_mul_left _ h

/-- Two integers of balanced width `m` differ by at most `3^m - 1`. -/
theorem balWidth_sub {m : ℕ} {p q : ℤ}
    (hp : balWidth m p) (hq : balWidth m q) :
    |p - q| ≤ (3 : ℤ) ^ m - 1 := by
  have hsum : |p - q| ≤ |p| + |q| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le p (-q)
  have : 2 * |p| + 2 * |q| ≤ 2 * ((3 : ℤ) ^ m - 1) := by
    unfold balWidth at hp hq
    linarith
  have : |p| + |q| ≤ (3 : ℤ) ^ m - 1 := by linarith
  linarith

/-- `N2` separates points of `P_m` once `2m + 1 <= k`: agreement to that order forces `p = q`. The width bound is what closes it -- the difference cannot reach `3^(k-m-1)`. -/
theorem sameDepth_n2_injective {k m : ℕ} {p q : ℤ}
    (hp : balWidth m p) (hq : balWidth m q)
    (hmk : 2 * m + 1 ≤ k)
    (hN2 : (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m q) :
    p = q := by
  have hle : m + 1 ≤ k := by omega
  have hdiff := (sameDepth_n2_succ hle p q).1 hN2
  have hexp : m ≤ k - (m + 1) := by omega
  have hpow : (3 : ℤ) ^ m ∣ (p - q) :=
    dvd_trans (pow_dvd_pow (3 : ℤ) hexp) hdiff
  have hbound : |p - q| < (3 : ℤ) ^ m := by
    have := balWidth_sub hp hq
    have hpos : (0 : ℤ) < (3 : ℤ) ^ m := pow_pos (by decide) _
    linarith
  exact sub_eq_zero.mp (dvd_abs_lt_pow hpow hbound)

/-- `N3` residuals agree modulo `3^k` when `k` is below both depths. -/
theorem n3_dvd_of_deep {k m n : ℕ}
    (hm : k ≤ 2 * m + 1) (hn : k ≤ 2 * n + 1) :
    (3 : ℤ) ^ k ∣ n3Resid m - n3Resid n := by
  have hm' : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (2 * m + 1) := pow_dvd_pow _ hm
  have hn' : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (2 * n + 1) := pow_dvd_pow _ hn
  rw [n3Resid_sub]
  have hsub : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (2 * m + 1) - (3 : ℤ) ^ (2 * n + 1) :=
    hm'.sub hn'
  have := hsub.mul_left (2 : ℤ)
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- Cross-depth `N3` criterion: for `m <= n`, `3^k` divides `N3(m) - N3(n)` exactly when `k <= 2m + 1` or the depths coincide. -/
theorem n3_dvd_iff {k m n : ℕ} (hmn : m ≤ n) :
    (3 : ℤ) ^ k ∣ n3Resid m - n3Resid n ↔
      k ≤ 2 * m + 1 ∨ m = n := by
  constructor
  · intro h
    rcases hmn.eq_or_lt with rfl | hlt
    · exact Or.inr rfl
    · left
      have h2 : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (2 * m + 1) - (3 : ℤ) ^ (2 * n + 1) := by
        have h' : (3 : ℤ) ^ k ∣
            2 * ((3 : ℤ) ^ (2 * m + 1) - (3 : ℤ) ^ (2 * n + 1)) := by
          simpa [n3Resid_sub] using h
        exact three_pow_dvd_of_two_mul h'
      have hle : 2 * m + 1 ≤ 2 * n + 1 := by omega
      have ht : 0 < 2 * (n - m) := by omega
      have hneg : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (2 * n + 1) - (3 : ℤ) ^ (2 * m + 1) := by
        simpa [neg_sub] using h2.neg_right
      have hfac := three_pow_sub_eq (m := 2 * m + 1) (n := 2 * n + 1) hle
      have htm : 2 * n + 1 - (2 * m + 1) = 2 * (n - m) := by omega
      rw [hfac, htm] at hneg
      by_contra hk
      have hk' : 2 * m + 2 ≤ k := by omega
      have hdiv : (3 : ℤ) ^ (2 * m + 2) ∣
          (3 : ℤ) ^ (2 * m + 1) * ((3 : ℤ) ^ (2 * (n - m)) - 1) :=
        dvd_trans (pow_dvd_pow (3 : ℤ) hk') hneg
      have hnz : (3 : ℤ) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ (by decide)
      have : (3 : ℤ) ∣ ((3 : ℤ) ^ (2 * (n - m)) - 1) := by
        rw [pow_succ] at hdiv
        have : (3 : ℤ) ^ (2 * m + 1) * 3 ∣
            (3 : ℤ) ^ (2 * m + 1) * ((3 : ℤ) ^ (2 * (n - m)) - 1) := by
          simpa [mul_comm] using hdiv
        exact (mul_dvd_mul_iff_left hnz).mp this
      exact (not_three_dvd_pow_sub_one ht this).elim
  · intro h
    rcases h with hk | rfl
    · exact n3_dvd_of_deep hk (le_trans hk (by omega))
    · simp [n3Resid]

/-- The `N1` sign condition, reduced to divisibility of `2 * 3^(m+1) * p`. -/
theorem sameDepth_n1_sign (k m : ℕ) (p : ℤ) :
    (3 : ℤ) ^ k ∣ n1Resid m p - n1Resid m (-p) ↔
      (3 : ℤ) ^ k ∣ 2 * (3 : ℤ) ^ (m + 1) * p := by
  rw [n1Resid_diff]
  constructor
  · intro h
    have heq : 3 * (p + p) * (3 : ℤ) ^ m = 2 * (3 : ℤ) ^ (m + 1) * p := by
      ring
    simpa [heq] using h
  · intro h
    have heq : 2 * (3 : ℤ) ^ (m + 1) * p = 3 * (p + p) * (3 : ℤ) ^ m := by
      ring
    simpa [heq] using h

/-- The `N2` sign condition, reduced to divisibility of `3^(m+1) * p`. -/
theorem sameDepth_n2_sign (k m : ℕ) (p : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m (-p) ↔
      (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (m + 1) * p := by
  rw [sameDepth_n2]
  constructor
  · intro h
    have : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (m + 1) * (2 * p) := by
      have heq : (3 : ℤ) ^ (m + 1) * (p + p) = (3 : ℤ) ^ (m + 1) * (2 * p) := by
        ring
      simpa [heq] using h
    exact three_pow_dvd_of_two_mul (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)
  · intro h
    have := h.mul_left (2 : ℤ)
    have heq : 2 * ((3 : ℤ) ^ (m + 1) * p) = (3 : ℤ) ^ (m + 1) * (p + p) := by
      ring
    simpa [heq] using this

/-- An `N1` sign agreement implies the `N2` one: the odd pair is governed by `N1`. -/
theorem sign_n2_of_n1 {k m : ℕ} {p : ℤ}
    (h : (3 : ℤ) ^ k ∣ n1Resid m p - n1Resid m (-p)) :
    (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m (-p) := by
  have h1 := (sameDepth_n1_sign k m p).1 h
  have h2 : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (m + 1) * p :=
    three_pow_dvd_of_two_mul (by simpa [mul_assoc, mul_left_comm, mul_comm] using h1)
  exact (sameDepth_n2_sign k m p).2 h2

/-- `D^m` is odd: `D^m (-n) = - D^m n`. -/
theorem iterDZ_neg : ∀ (m : ℕ) (n : ℤ), iterDZ m (-n) = -iterDZ m n
  | 0, n => by simp [iterDZ]
  | m + 1, n => by
    have h := rewrite_N_D n
    change iterDZ m (DZ (-n)) = -iterDZ m (DZ n)
    rw [h, iterDZ_neg m]

/-- `N0(-p) = -N0(p)`. -/
theorem n0Resid_neg (m : ℕ) (p : ℤ) :
    n0Resid m (-p) = -n0Resid m p := by
  unfold n0Resid
  have : (-p) ^ 3 = -(p ^ 3) := by ring
  rw [this, iterDZ_neg]

/-- `N0(p)` and `N0(-p)` agree modulo `3^k` exactly when `3^k` divides `N0(p)`; the sign survives only where the residual already vanishes. -/
theorem sign_n0 {k m : ℕ} {p : ℤ} :
    (3 : ℤ) ^ k ∣ n0Resid m p - n0Resid m (-p) ↔
      (3 : ℤ) ^ k ∣ n0Resid m p := by
  rw [n0Resid_neg]
  constructor
  · intro h
    have : (3 : ℤ) ^ k ∣ 2 * n0Resid m p := by
      have heq : n0Resid m p - -n0Resid m p = 2 * n0Resid m p := by ring
      simpa [heq] using h
    exact three_pow_dvd_of_two_mul this
  · intro h
    have := h.mul_left (2 : ℤ)
    have heq : 2 * n0Resid m p = n0Resid m p - -n0Resid m p := by ring
    simpa [heq] using this

end BTCalculus
