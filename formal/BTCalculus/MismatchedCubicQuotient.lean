import BTCalculus.CubicN0Reduction

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Mismatched-width cubic quotient.

``qCubic t u = D^t(u^3)``. Equality modulo ``3^K`` is decided by the
reconstruction identity
``z = bal_t(z) + 3^t D^t(z)`` applied to cubes.
-/

def qCubic (t : Nat) (u : Int) : Int :=
  n0Resid t u

def balCubic (t : Nat) (u : Int) : Int :=
  packWord (integerJet t (u ^ 3))

theorem qCubic_def (t : Nat) (u : Int) :
    qCubic t u = iterDZ t (u ^ 3) :=
  rfl

theorem q_recon (t : Nat) (z : Int) :
    z = packWord (integerJet t z) + (3 : Int) ^ t * iterDZ t z :=
  packWord_integerJet_decomp t z

theorem q_recon_diff (t : Nat) (u v : Int) :
    u ^ 3 - v ^ 3 - (balCubic t u - balCubic t v) =
      (3 : Int) ^ t * (qCubic t u - qCubic t v) := by
  have hu := q_recon t (u ^ 3)
  have hv := q_recon t (v ^ 3)
  unfold qCubic balCubic n0Resid
  linarith

theorem q_eq_iff {t K : Nat} (u v : Int) :
    (3 : Int) ^ K ∣ qCubic t u - qCubic t v ↔
      (3 : Int) ^ (t + K) ∣
        u ^ 3 - v ^ 3 - (balCubic t u - balCubic t v) := by
  have hdelta := q_recon_diff t u v
  have hshape : (3 : Int) ^ (t + K) = (3 : Int) ^ t * (3 : Int) ^ K := by
    rw [← pow_add]
  constructor
  · intro h
    rw [hdelta, hshape]
    exact mul_dvd_mul_left _ h
  · intro h
    rw [hdelta, hshape] at h
    have hnz : (3 : Int) ^ t ≠ 0 := pow_ne_zero _ (by decide)
    exact (mul_dvd_mul_iff_left hnz).mp (by
      simpa [mul_assoc] using h)

theorem q_eq_of_cube_mod {t K : Nat} {u v : Int}
    (h : (3 : Int) ^ (t + K) ∣ u ^ 3 - v ^ 3) :
    (3 : Int) ^ K ∣ qCubic t u - qCubic t v :=
  n0_of_cube_mod h

/-- `qCubic t u` modulo `3^K` sees only `u` modulo `3^s` once `t + K - 1 <= s`: congruent
inputs give congruent cubic quotients. -/
theorem q_visible_mod {t K s : Nat}
    (hs : t + K - 1 ≤ s) (hs1 : 1 ≤ s) {u v : Int}
    (h : (3 : Int) ^ s ∣ u - v) :
    (3 : Int) ^ K ∣ qCubic t u - qCubic t v :=
  n0_visible_mod hs hs1 h

theorem q_val_of_le {t s : Nat} (hm : t ≤ 3 * s) (w : Int) :
    qCubic t ((3 : Int) ^ s * w) = (3 : Int) ^ (3 * s - t) * w ^ 3 :=
  n0_val_stratum_le hm w

theorem q_val_of_ge {t s : Nat} (hm : 3 * s ≤ t) (w : Int) :
    qCubic t ((3 : Int) ^ s * w) = qCubic (t - 3 * s) w :=
  n0_val_stratum_ge hm w

theorem q_zero (t : Nat) : qCubic t 0 = 0 :=
  n0Resid_zero t

theorem q_neg (t : Nat) (u : Int) : qCubic t (-u) = -qCubic t u :=
  n0Resid_neg t u

theorem q_sign {K t : Nat} {u : Int} :
    (3 : Int) ^ K ∣ qCubic t u - qCubic t (-u) ↔
      (3 : Int) ^ K ∣ qCubic t u :=
  sign_n0

theorem q_from_exhausted {k r : Nat}
    (hr : r + 1 ≤ k) (hk : 4 * r + 1 ≤ k) (u : Int) :
    n0Resid (k - 1 - r) ((3 : Int) ^ r * u) = qCubic (k - 1 - 4 * r) u :=
  n0_scaled_exhausted hr hk u

theorem q_from_unexhausted {k r : Nat}
    (hr : r + 1 ≤ k) (hk : k ≤ 4 * r + 1) (u : Int) :
    n0Resid (k - 1 - r) ((3 : Int) ^ r * u) =
      (3 : Int) ^ (4 * r + 1 - k) * u ^ 3 :=
  n0_scaled_unexhausted hr hk u

theorem cubic_q_width {k r : Nat} (_hk : 4 * r + 1 ≤ k) :
    k - 1 - 2 * r = k - 1 - 4 * r + 2 * r := by
  omega

theorem q_of_deficit_one {k : Nat} (hk : 5 ≤ k) (u : Int) :
    n0Resid (k - 2) (3 * u) = qCubic (k - 5) u := by
  have h := n0_scaled_exhausted (k := k) (r := 1) (by omega) (by omega) u
  have h1 : k - 1 - 1 = k - 2 := by omega
  have h2 : k - 1 - 4 = k - 5 := by omega
  simpa [pow_one, h1, h2, qCubic] using h

theorem q_of_deficit_two {k : Nat} (hk : 9 ≤ k) (u : Int) :
    n0Resid (k - 3) ((3 : Int) ^ 2 * u) = qCubic (k - 9) u :=
  n0_scaled_exhausted (k := k) (r := 2) (by omega) (by omega) u

theorem cube_expand (a x : Int) {s : Nat} :
    (a + (3 : Int) ^ s * x) ^ 3 =
      a ^ 3 + (3 : Int) ^ (s + 1) * a ^ 2 * x +
        (3 : Int) ^ (2 * s + 1) * a * x ^ 2 + (3 : Int) ^ (3 * s) * x ^ 3 := by
  ring

/-- Cubic carry expansion.  For `t <= s + 1` and `t <= 3s`, `qCubic t (a + 3^s x)` splits
into `qCubic t a` plus explicit terms in `x`, `x^2` and `x^3`. -/
theorem q_shift {t s : Nat} (ht : t ≤ s + 1) (h3 : t ≤ 3 * s)
    (a x : Int) :
    qCubic t (a + (3 : Int) ^ s * x) =
      qCubic t a + (3 : Int) ^ (s + 1 - t) * a ^ 2 * x +
        (3 : Int) ^ (2 * s + 1 - t) * a * x ^ 2 +
          (3 : Int) ^ (3 * s - t) * x ^ 3 := by
  have hexp := cube_expand (s := s) a x
  have hs1 : t ≤ s + 1 := ht
  have hs2 : t ≤ 2 * s + 1 := by omega
  have hA : (3 : Int) ^ (s + 1) = (3 : Int) ^ t * (3 : Int) ^ (s + 1 - t) :=
    pow3_split hs1
  have hB : (3 : Int) ^ (2 * s + 1) = (3 : Int) ^ t * (3 : Int) ^ (2 * s + 1 - t) :=
    pow3_split hs2
  have hC : (3 : Int) ^ (3 * s) = (3 : Int) ^ t * (3 : Int) ^ (3 * s - t) :=
    pow3_split h3
  have hsum :
      (a + (3 : Int) ^ s * x) ^ 3 =
        a ^ 3 + (3 : Int) ^ t *
          ((3 : Int) ^ (s + 1 - t) * a ^ 2 * x +
            (3 : Int) ^ (2 * s + 1 - t) * a * x ^ 2 +
              (3 : Int) ^ (3 * s - t) * x ^ 3) := by
    rw [hexp, hA, hB, hC]
    ring
  unfold qCubic n0Resid
  rw [hsum, iterDZ_add_pow]
  ring

theorem q_split_high (t : Nat) (a b : Int) :
    qCubic t (a + (3 : Int) ^ t * b) =
      qCubic t a + 3 * a ^ 2 * b +
        (3 : Int) ^ (t + 1) * a * b ^ 2 + (3 : Int) ^ (2 * t) * b ^ 3 := by
  have ht : t ≤ t + 1 := by omega
  have h3 : t ≤ 3 * t := by omega
  have h := q_shift (t := t) (s := t) ht h3 a b
  have h1 : t + 1 - t = 1 := by omega
  have h2 : 2 * t + 1 - t = t + 1 := by omega
  have h4 : 3 * t - t = 2 * t := by omega
  simpa [h1, h2, h4, pow_one] using h

theorem cube_diff (u v : Int) :
    u ^ 3 - v ^ 3 = (u - v) * (u ^ 2 + u * v + v ^ 2) := by
  ring

lemma sq_sum_sub_sq (u v : Int) :
    u ^ 2 + u * v + v ^ 2 - u ^ 2 = v * (u + v) := by
  ring

theorem not_three_dvd_sq_sum_of_opp {u v : Int}
    (hu : ¬ (3 : Int) ∣ u) (h : (3 : Int) ∣ u + v) :
    ¬ (3 : Int) ∣ u ^ 2 + u * v + v ^ 2 := by
  intro hsum
  have hid := sq_sum_sub_sq u v
  have hsq : (3 : Int) ∣ u ^ 2 := by
    have : u ^ 2 = (u ^ 2 + u * v + v ^ 2) - v * (u + v) := by
      linear_combination -hid
    rw [this]
    exact hsum.sub (h.mul_left v)
  exact hu (three_dvd_of_dvd_sq hsq)

theorem q_eq_iff_of_same_bal {t K : Nat} {u v : Int}
    (hbal : balCubic t u = balCubic t v) :
    (3 : Int) ^ K ∣ qCubic t u - qCubic t v ↔
      (3 : Int) ^ (t + K) ∣ u ^ 3 - v ^ 3 := by
  have hdelta := q_eq_iff (t := t) (K := K) u v
  have hbal0 : balCubic t u - balCubic t v = 0 := by
    rw [hbal]; ring
  simp [hbal0] at hdelta
  exact hdelta

theorem q_zero_of_high {t s K : Nat} (hm : t ≤ 3 * s)
    (hK : K ≤ 3 * s - t) (w : Int) :
    (3 : Int) ^ K ∣ qCubic t ((3 : Int) ^ s * w) := by
  rw [q_val_of_le hm]
  exact dvd_trans (pow_dvd_pow (3 : Int) hK) (dvd_mul_right _ _)

theorem q_of_deficit_three {k : Nat} (hk : 13 ≤ k) (u : Int) :
    n0Resid (k - 4) ((3 : Int) ^ 3 * u) = qCubic (k - 13) u :=
  n0_scaled_exhausted (k := k) (r := 3) (by omega) (by omega) u

end BTCalculus
