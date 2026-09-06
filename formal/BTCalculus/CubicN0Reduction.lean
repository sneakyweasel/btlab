import BTCalculus.CubicN1Valuation

noncomputable section

namespace BTCalculus

open Polynomial

/-!
N0 scaling on the 3^r-divisible locus.

``D(3n) = n``. Iterating on ``p^3 = 3^{3r} u^3`` gives
``D^m((3^r u)^3) = 3^{3r-m} u^3`` when ``m ≤ 3r``,
and ``D^{m-3r}(u^3)`` when ``3r ≤ m``.
-/

theorem DZ_mul_three (n : Int) : DZ (3 * n) = n :=
  D_after_S_int n

theorem pow3_mul_cube (r : Nat) (u : Int) :
    ((3 : Int) ^ r * u) ^ 3 = (3 : Int) ^ (3 * r) * u ^ 3 := by
  rw [mul_pow, ← pow_mul]
  ring

theorem iterDZ_pow_mul : ∀ (j e : Nat) (n : Int),
    j ≤ e → iterDZ j ((3 : Int) ^ e * n) = (3 : Int) ^ (e - j) * n
  | 0, e, n, _ => by simp [iterDZ]
  | j + 1, e, n, h => by
    have he : 1 ≤ e := by omega
    have hshape : (3 : Int) ^ e * n = 3 * ((3 : Int) ^ (e - 1) * n) := by
      rw [pow3_split he]
      ring
    have hdz : DZ ((3 : Int) ^ e * n) = (3 : Int) ^ (e - 1) * n := by
      rw [hshape, DZ_mul_three]
    have ih := iterDZ_pow_mul j (e - 1) n (by omega)
    have : iterDZ (j + 1) ((3 : Int) ^ e * n) =
        iterDZ j (DZ ((3 : Int) ^ e * n)) := rfl
    rw [this, hdz, ih]
    have hexp : e - 1 - j = e - (j + 1) := by omega
    rw [hexp]

theorem iterDZ_pow_mul_ge : ∀ (e j : Nat) (n : Int),
    e ≤ j → iterDZ j ((3 : Int) ^ e * n) = iterDZ (j - e) n
  | 0, j, n, _ => by simp [iterDZ]
  | e + 1, j, n, h => by
    have hshape : (3 : Int) ^ (e + 1) * n = 3 * ((3 : Int) ^ e * n) := by
      rw [pow_succ']
      ring
    have hdz : DZ ((3 : Int) ^ (e + 1) * n) = (3 : Int) ^ e * n := by
      rw [hshape, DZ_mul_three]
    have : iterDZ j ((3 : Int) ^ (e + 1) * n) =
        iterDZ (j - 1) (DZ ((3 : Int) ^ (e + 1) * n)) := by
      have : j = (j - 1) + 1 := by omega
      rw [this]
      rfl
    rw [this, hdz]
    have ih := iterDZ_pow_mul_ge e (j - 1) n (by omega)
    rw [ih]
    have hexp : j - 1 - e = j - (e + 1) := by omega
    rw [hexp]

theorem n0_scaled_of_le {m r : Nat} (hm : m ≤ 3 * r) (u : Int) :
    n0Resid m ((3 : Int) ^ r * u) = (3 : Int) ^ (3 * r - m) * u ^ 3 := by
  unfold n0Resid
  rw [pow3_mul_cube]
  exact iterDZ_pow_mul m (3 * r) (u ^ 3) hm

theorem n0_scaled_of_ge {m r : Nat} (hm : 3 * r ≤ m) (u : Int) :
    n0Resid m ((3 : Int) ^ r * u) = n0Resid (m - 3 * r) u := by
  unfold n0Resid
  rw [pow3_mul_cube]
  exact iterDZ_pow_mul_ge (3 * r) m (u ^ 3) hm

theorem n0_scaled_zero (m r : Nat) :
    n0Resid m ((3 : Int) ^ r * (0 : Int)) = 0 := by
  by_cases hm : m ≤ 3 * r
  · rw [n0_scaled_of_le hm]; simp
  · have : 3 * r ≤ m := by omega
    rw [n0_scaled_of_ge this]
    exact n0Resid_zero _

theorem deficit_unexhausted_iff {k r : Nat} (_hr : r + 1 ≤ k) :
    k - 1 - r ≤ 3 * r ↔ k ≤ 4 * r + 1 := by
  omega

theorem n0_scaled_unexhausted {k r : Nat}
    (hr : r + 1 ≤ k) (hk : k ≤ 4 * r + 1) (u : Int) :
    n0Resid (k - 1 - r) ((3 : Int) ^ r * u) =
      (3 : Int) ^ (4 * r + 1 - k) * u ^ 3 := by
  have hm : k - 1 - r ≤ 3 * r := by omega
  have hexp : 3 * r - (k - 1 - r) = 4 * r + 1 - k := by omega
  simpa [hexp] using n0_scaled_of_le (m := k - 1 - r) (r := r) hm u

theorem n0_scaled_exhausted {k r : Nat}
    (hr : r + 1 ≤ k) (hk : 4 * r + 1 ≤ k) (u : Int) :
    n0Resid (k - 1 - r) ((3 : Int) ^ r * u) = n0Resid (k - 1 - 4 * r) u := by
  have hm : 3 * r ≤ k - 1 - r := by omega
  have ht : k - 1 - r - 3 * r = k - 1 - 4 * r := by omega
  simpa [ht] using n0_scaled_of_ge (m := k - 1 - r) (r := r) hm u

/-- The depth of the reduced `N0` residual. -/
theorem n0_reduced_depth (k r : Nat) :
    k - 1 - r - 3 * r = k - 1 - 4 * r := by
  omega

theorem n0_depth_eq_n1_deepest {k r : Nat} (hk : 4 * r + 1 ≤ k) :
    k - 1 - 4 * r = k - 2 * r - 1 ↔ r = 0 := by
  have h1 : k - 1 - 4 * r = k - (4 * r + 1) := by omega
  have h2 : k - 2 * r - 1 = k - (2 * r + 1) := by omega
  rw [h1, h2]
  omega

theorem n0_width_ne_depth {k r : Nat} (hr : 1 ≤ r) (_hk : 4 * r + 1 ≤ k) :
    k - 1 - 2 * r ≠ k - 1 - 4 * r := by
  omega

/-- `N0(p)` and `N0(-p)` agree modulo `3^k` exactly when `3^k` divides `N0(p)`: the sign survives the reduction only where the residual already vanishes. -/
theorem n0_sign_survives {k m : Nat} {p : Int} :
    (3 : Int) ^ k ∣ n0Resid m p - n0Resid m (-p) ↔
      (3 : Int) ^ k ∣ n0Resid m p :=
  sign_n0

theorem n0_sign_scaled_of_le {k m r : Nat} (hm : m ≤ 3 * r) (u : Int) :
    (3 : Int) ^ k ∣
        n0Resid m ((3 : Int) ^ r * u) - n0Resid m ((3 : Int) ^ r * (-u)) ↔
      (3 : Int) ^ k ∣ (3 : Int) ^ (3 * r - m) * u ^ 3 := by
  have hneg : (3 : Int) ^ r * (-u) = -((3 : Int) ^ r * u) := by ring
  rw [hneg, n0_sign_survives, n0_scaled_of_le hm]

lemma three_dvd_sq_sum {u v : Int} (h : (3 : Int) ∣ u - v) :
    (3 : Int) ∣ u ^ 2 + u * v + v ^ 2 := by
  have hexp : u ^ 2 + u * v + v ^ 2 =
      3 * v ^ 2 + 3 * v * (u - v) + (u - v) ^ 2 := by ring
  have hsq : (u - v) ^ 2 = (u - v) * (u - v) := by ring
  rw [hexp, hsq]
  exact ((dvd_mul_right (3 : Int) (v ^ 2)).add (h.mul_left (3 * v))).add (h.mul_right (u - v))

theorem cube_val_succ {s : Nat} (hs : 1 ≤ s) {u v : Int}
    (h : (3 : Int) ^ s ∣ u - v) :
    (3 : Int) ^ (s + 1) ∣ u ^ 3 - v ^ 3 := by
  have h3 : (3 : Int) ∣ u - v :=
    dvd_trans (pow_dvd_pow (3 : Int) hs) h
  have hsum := three_dvd_sq_sum h3
  have hprod : u ^ 3 - v ^ 3 = (u - v) * (u ^ 2 + u * v + v ^ 2) := by ring
  rw [hprod, pow_succ]
  exact mul_dvd_mul h hsum

theorem n0_of_cube_mod {t k : Nat} {u v : Int}
    (h : (3 : Int) ^ (t + k) ∣ u ^ 3 - v ^ 3) :
    (3 : Int) ^ k ∣ n0Resid t u - n0Resid t v := by
  obtain ⟨d, hd⟩ := h
  have : u ^ 3 = v ^ 3 + (3 : Int) ^ t * ((3 : Int) ^ k * d) := by
    have hshape : (3 : Int) ^ (t + k) = (3 : Int) ^ t * (3 : Int) ^ k := by
      rw [← pow_add]
    calc
      u ^ 3 = v ^ 3 + (u ^ 3 - v ^ 3) := by ring
      _ = v ^ 3 + (3 : Int) ^ (t + k) * d := by rw [hd]
      _ = v ^ 3 + (3 : Int) ^ t * ((3 : Int) ^ k * d) := by
        rw [hshape]; ring
  have hiter : iterDZ t (u ^ 3) = iterDZ t (v ^ 3) + (3 : Int) ^ k * d := by
    rw [this, iterDZ_add_pow]
  unfold n0Resid
  rw [hiter]
  exact ⟨d, by ring⟩

/-- `N0` modulo a power of three sees only the input modulo a power of three. -/
theorem n0_visible_mod {t k s : Nat}
    (hs : t + k - 1 ≤ s) (hs1 : 1 ≤ s) {u v : Int}
    (h : (3 : Int) ^ s ∣ u - v) :
    (3 : Int) ^ k ∣ n0Resid t u - n0Resid t v := by
  have hcube : (3 : Int) ^ (s + 1) ∣ u ^ 3 - v ^ 3 :=
    cube_val_succ hs1 h
  have hle : t + k ≤ s + 1 := by omega
  have : (3 : Int) ^ (t + k) ∣ u ^ 3 - v ^ 3 :=
    dvd_trans (pow_dvd_pow (3 : Int) hle) hcube
  exact n0_of_cube_mod this

theorem n0_val_stratum_le {m s : Nat} (hm : m ≤ 3 * s) (w : Int) :
    n0Resid m ((3 : Int) ^ s * w) = (3 : Int) ^ (3 * s - m) * w ^ 3 :=
  n0_scaled_of_le hm w

theorem n0_val_stratum_ge {m s : Nat} (hm : 3 * s ≤ m) (w : Int) :
    n0Resid m ((3 : Int) ^ s * w) = n0Resid (m - 3 * s) w :=
  n0_scaled_of_ge hm w

end BTCalculus
