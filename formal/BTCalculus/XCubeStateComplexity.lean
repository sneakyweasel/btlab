import BTCalculus.MismatchedCubicInvariant

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Exact same-depth image decomposition and unit Q-image count for x^3.

At deficit r one has m = k-1-r. Prefixes with v_3(p) < r are injective
after N2+N1 (`n1_val_lt_injective`). The remaining core is
p = 3^r u with u in P_W, W = m-r. On units the two-scale polynomial
G_a is injective in the high word modulo 3^{K-1}. Cross-depth
collisions require the N3 gate. The zero spine is the common Newton
class of p = 0 at depths 2m >= k.
-/

theorem balWidth_mul_pow {m r : Nat} (hr : r ≤ m) {u : Int}
    (hu : balWidth (m - r) u) :
    balWidth m ((3 : Int) ^ r * u) := by
  unfold balWidth at hu ⊢
  have habs : |(3 : Int) ^ r * u| = (3 : Int) ^ r * |u| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by decide : (0 : Int) ≤ 3) r)]
  rw [habs]
  have hsplit : (3 : Int) ^ m = (3 : Int) ^ r * (3 : Int) ^ (m - r) :=
    pow3_split hr
  have hmul : (3 : Int) ^ r * (2 * |u|) ≤
      (3 : Int) ^ r * ((3 : Int) ^ (m - r) - 1) :=
    mul_le_mul_of_nonneg_left hu (pow_nonneg (by decide : (0 : Int) ≤ 3) r)
  have hshape : 2 * ((3 : Int) ^ r * |u|) = (3 : Int) ^ r * (2 * |u|) := by ring
  have hright : (3 : Int) ^ r * ((3 : Int) ^ (m - r) - 1) =
      (3 : Int) ^ m - (3 : Int) ^ r := by
    rw [hsplit]; ring
  have hone : (1 : Int) ≤ (3 : Int) ^ r :=
    one_le_pow₀ (by decide : (1 : Int) ≤ 3)
  rw [hshape]
  linarith

theorem balWidth_of_mul_pow {m r : Nat} (hr : r ≤ m) {u : Int}
    (hp : balWidth m ((3 : Int) ^ r * u)) :
    balWidth (m - r) u := by
  unfold balWidth at hp ⊢
  have habs : |(3 : Int) ^ r * u| = (3 : Int) ^ r * |u| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by decide : (0 : Int) ≤ 3) r)]
  rw [habs] at hp
  have hsplit : (3 : Int) ^ m = (3 : Int) ^ r * (3 : Int) ^ (m - r) :=
    pow3_split hr
  have hpos : (0 : Int) < (3 : Int) ^ r := pow_pos (by decide) _
  by_contra h
  have hbig : (3 : Int) ^ (m - r) ≤ 2 * |u| := by omega
  have : (3 : Int) ^ m ≤ 2 * ((3 : Int) ^ r * |u|) := by
    rw [hsplit]
    nlinarith
  linarith

theorem balWidth_pow_iff {m r : Nat} (hr : r ≤ m) (u : Int) :
    balWidth m ((3 : Int) ^ r * u) ↔ balWidth (m - r) u :=
  ⟨balWidth_of_mul_pow hr, balWidth_mul_pow hr⟩

theorem balWidth_pow_of_lt {m r : Nat} (hr : m < r) {u : Int}
    (hp : balWidth m ((3 : Int) ^ r * u)) : u = 0 := by
  unfold balWidth at hp
  have habs : |(3 : Int) ^ r * u| = (3 : Int) ^ r * |u| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by decide : (0 : Int) ≤ 3) r)]
  rw [habs] at hp
  have hlt : (3 : Int) ^ m < (3 : Int) ^ r :=
    pow_lt_pow_right₀ (by decide : (1 : Int) < 3) hr
  have hpos : (0 : Int) < (3 : Int) ^ r := pow_pos (by decide) _
  have : 2 * ((3 : Int) ^ r * |u|) < (3 : Int) ^ r := by linarith
  have hcancel : 2 * ((3 : Int) ^ r * |u|) = (3 : Int) ^ r * (2 * |u|) := by ring
  rw [hcancel] at this
  have h1 : (3 : Int) ^ r * (2 * |u|) < (3 : Int) ^ r * 1 := by
    simpa using this
  have : 2 * |u| < 1 := lt_of_mul_lt_mul_left h1 (le_of_lt hpos)
  have hu0 : |u| = 0 := le_antisymm (by linarith) (abs_nonneg _)
  exact abs_eq_zero.mp hu0

theorem n1_on_core (k r : Nat) (u : Int) :
    n1Resid (k - 1 - r) ((3 : Int) ^ r * u) =
      (3 : Int) ^ (2 * (k - 1 - r)) +
        (3 : Int) ^ ((k - 1 - r) + 1 + r) * u +
          (3 : Int) ^ (2 * r + 1) * u ^ 2 := by
  unfold n1Resid
  have hsq : 3 * ((3 : Int) ^ r * u) ^ 2 = (3 : Int) ^ (2 * r + 1) * u ^ 2 := by
    rw [mul_pow]
    have : ((3 : Int) ^ r) ^ 2 = (3 : Int) ^ (2 * r) := by
      rw [← pow_mul, mul_comm]
    rw [this, pow_succ']
    ring
  have hlin :
      (3 : Int) ^ ((k - 1 - r) + 1) * ((3 : Int) ^ r * u) =
        (3 : Int) ^ ((k - 1 - r) + 1 + r) * u := by
    rw [← mul_assoc, ← pow_add]
  rw [hsq, hlin]

theorem n1_on_core_mod {k r : Nat} (hr : r + 1 ≤ k)
    (h2 : 2 * r + 2 ≤ k) (u : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
      (3 : Int) ^ (2 * r + 1) * u ^ 2 := by
  have hexp : (k - 1 - r) + 1 + r = k := by omega
  have h2m : k ≤ 2 * (k - 1 - r) := by omega
  have hform := n1_on_core k r u
  rw [hform, hexp]
  have hA : (3 : Int) ^ k ∣ (3 : Int) ^ (2 * (k - 1 - r)) :=
    pow_dvd_pow _ h2m
  have hB : (3 : Int) ^ k ∣ (3 : Int) ^ k * u := dvd_mul_right _ _
  have := hA.add hB
  have heq :
      (3 : Int) ^ (2 * (k - 1 - r)) + (3 : Int) ^ k * u +
          (3 : Int) ^ (2 * r + 1) * u ^ 2 - (3 : Int) ^ (2 * r + 1) * u ^ 2 =
        (3 : Int) ^ (2 * (k - 1 - r)) + (3 : Int) ^ k * u := by
    ring
  simpa [heq] using this

theorem n2Resid_zero (m : Nat) :
    n2Resid m 0 = 2 * (3 : Int) ^ (2 * m + 1) := by
  unfold n2Resid
  ring

theorem zero_spine_n1 {k m : Nat} (h : k ≤ 2 * m) :
    (3 : Int) ^ k ∣ n1Resid m 0 := by
  rw [n1Resid_zero]
  exact pow_dvd_pow _ h

theorem zero_spine_n2 {k m : Nat} (h : k ≤ 2 * m + 1) :
    (3 : Int) ^ k ∣ n2Resid m 0 := by
  rw [n2Resid_zero]
  exact (pow_dvd_pow (3 : Int) h).mul_left (2 : Int)

theorem zero_spine_n0 (k m : Nat) :
    (3 : Int) ^ k ∣ n0Resid m 0 := by
  rw [n0Resid_zero]
  exact dvd_zero _

theorem zero_spine_n3 {k m : Nat} (h : k ≤ 2 * m + 1) :
    (3 : Int) ^ k ∣ n3Resid m := by
  unfold n3Resid
  exact (pow_dvd_pow (3 : Int) h).mul_left (2 : Int)

lemma q_unit_diff {t : Nat} (ht : 1 ≤ t) (a b c : Int) :
    qCubic t (a + (3 : Int) ^ t * b) - qCubic t (a + (3 : Int) ^ t * c) =
      (3 : Int) * (b - c) *
        (a ^ 2 + (3 : Int) ^ t * a * (b + c) +
          (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) := by
  have hb := q_split_high t a b
  have hc := q_split_high t a c
  have hpow : (3 : Int) ^ (2 * t) = (3 : Int) * (3 : Int) ^ (2 * t - 1) := by
    have : (3 : Int) ^ (2 * t) = (3 : Int) ^ 1 * (3 : Int) ^ (2 * t - 1) :=
      pow3_split (by omega)
    simpa [pow_one] using this
  have ht1 : (3 : Int) ^ (t + 1) = (3 : Int) * (3 : Int) ^ t := by
    have : (3 : Int) ^ (t + 1) = (3 : Int) ^ 1 * (3 : Int) ^ t :=
      pow3_split (by omega)
    simpa [pow_one] using this
  rw [hb, hc]
  have hcube : b ^ 3 - c ^ 3 = (b - c) * (b ^ 2 + b * c + c ^ 2) := by ring
  have hsq : b ^ 2 - c ^ 2 = (b - c) * (b + c) := by ring
  calc
    qCubic t a + 3 * a ^ 2 * b + (3 : Int) ^ (t + 1) * a * b ^ 2 +
        (3 : Int) ^ (2 * t) * b ^ 3 -
        (qCubic t a + 3 * a ^ 2 * c + (3 : Int) ^ (t + 1) * a * c ^ 2 +
          (3 : Int) ^ (2 * t) * c ^ 3) =
        3 * a ^ 2 * (b - c) + (3 : Int) ^ (t + 1) * a * (b ^ 2 - c ^ 2) +
          (3 : Int) ^ (2 * t) * (b ^ 3 - c ^ 3) := by ring
    _ = 3 * a ^ 2 * (b - c) + (3 : Int) ^ (t + 1) * a * ((b - c) * (b + c)) +
          (3 : Int) ^ (2 * t) * ((b - c) * (b ^ 2 + b * c + c ^ 2)) := by
        rw [hsq, hcube]
    _ = (3 : Int) * (b - c) *
          (a ^ 2 + (3 : Int) ^ t * a * (b + c) +
            (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) := by
        rw [ht1, hpow]
        ring

lemma q_unit_bracket {t : Nat} (ht : 1 ≤ t) {a : Int}
    (ha : ¬ (3 : Int) ∣ a) (b c : Int) :
    ¬ (3 : Int) ∣ (a ^ 2 + (3 : Int) ^ t * a * (b + c) +
      (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) := by
  intro h
  have hA : (3 : Int) ∣ (3 : Int) ^ t * a * (b + c) := by
    have : (3 : Int) ∣ (3 : Int) ^ t := dvd_pow_self _ (by omega)
    exact (this.mul_right a).mul_right (b + c)
  have hB : (3 : Int) ∣ (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2) :=
    dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  have h1 : (3 : Int) ∣ a ^ 2 := by
    have : a ^ 2 =
        (a ^ 2 + (3 : Int) ^ t * a * (b + c) +
          (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) -
          ((3 : Int) ^ t * a * (b + c) +
            (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) := by
      ring
    rw [this]
    exact h.sub (hA.add hB)
  exact ha (three_dvd_of_dvd_sq h1)

theorem q_unit_family_dvd {t K : Nat} (ht : 1 ≤ t) (hK : 1 ≤ K)
    {a : Int} (ha : ¬ (3 : Int) ∣ a) (b c : Int) :
    (3 : Int) ^ K ∣ qCubic t (a + (3 : Int) ^ t * b) -
        qCubic t (a + (3 : Int) ^ t * c) ↔
      (3 : Int) ^ (K - 1) ∣ b - c := by
  have hdiff := q_unit_diff ht a b c
  have hU := q_unit_bracket ht ha b c
  constructor
  · intro h
    rw [hdiff] at h
    have : (3 : Int) ^ K ∣
        (3 : Int) * ((b - c) * (a ^ 2 + (3 : Int) ^ t * a * (b + c) +
          (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2))) := by
      simpa [mul_assoc] using h
    have hshape : (3 : Int) ^ K = (3 : Int) * (3 : Int) ^ (K - 1) := by
      have : (3 : Int) ^ K = (3 : Int) ^ 1 * (3 : Int) ^ (K - 1) :=
        pow3_split (by omega)
      simpa [pow_one] using this
    rw [hshape] at this
    have hnz : (3 : Int) ≠ 0 := by decide
    have hm := (mul_dvd_mul_iff_left hnz).mp this
    exact (three_pow_dvd_mul_iff (K - 1) hU).mp hm
  · intro h
    have hshape : (3 : Int) ^ K = (3 : Int) * (3 : Int) ^ (K - 1) := by
      have : (3 : Int) ^ K = (3 : Int) ^ 1 * (3 : Int) ^ (K - 1) :=
        pow3_split (by omega)
      simpa [pow_one] using this
    rw [hdiff, hshape]
    have hm : (3 : Int) ^ (K - 1) ∣
        (b - c) * (a ^ 2 + (3 : Int) ^ t * a * (b + c) +
          (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) :=
      (three_pow_dvd_mul_iff (K - 1) hU).mpr h
    simpa [mul_assoc] using mul_dvd_mul_left (3 : Int) hm

theorem x3_crossDepth_n3 {k m n : Nat} (hmn : m ≤ n) :
    (3 : Int) ^ k ∣ n3Resid m - n3Resid n ↔
      k ≤ 2 * m + 1 ∨ m = n :=
  n3_dvd_iff hmn

theorem square_exp_eq_width {k r : Nat} :
    k - 2 * r - 1 = k - 1 - 2 * r := by
  omega

lemma not_three_dvd_two_mul {a : Int} (ha : ¬ (3 : Int) ∣ a) :
    ¬ (3 : Int) ∣ (2 : Int) * a := by
  intro h
  rcases Int.prime_three.dvd_or_dvd h with h2 | ha'
  · exact (by decide : ¬ (3 : Int) ∣ 2) h2
  · exact ha ha'

theorem n1_core_square_iff {k r : Nat} (h2 : 2 * r + 2 ≤ k) (u v : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
        n1Resid (k - 1 - r) ((3 : Int) ^ r * v) ↔
      (3 : Int) ^ (k - 2 * r - 1) ∣ u ^ 2 - v ^ 2 := by
  have hr : r + 1 ≤ k := by omega
  have hu := n1_on_core_mod hr h2 u
  have hv := n1_on_core_mod hr h2 v
  have hshape : (3 : Int) ^ k =
      (3 : Int) ^ (2 * r + 1) * (3 : Int) ^ (k - 2 * r - 1) := by
    have : 2 * r + 1 ≤ k := by omega
    exact pow3_split this
  have hnu : (3 : Int) ^ (2 * r + 1) ≠ 0 := pow_ne_zero _ (by decide)
  constructor
  · intro h
    have hdiff :
        n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
            n1Resid (k - 1 - r) ((3 : Int) ^ r * v) -
          (3 : Int) ^ (2 * r + 1) * (u ^ 2 - v ^ 2) =
          (n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
            (3 : Int) ^ (2 * r + 1) * u ^ 2) -
          (n1Resid (k - 1 - r) ((3 : Int) ^ r * v) -
            (3 : Int) ^ (2 * r + 1) * v ^ 2) := by
      ring
    have hA := hu.sub hv
    have : (3 : Int) ^ k ∣ (3 : Int) ^ (2 * r + 1) * (u ^ 2 - v ^ 2) := by
      have hleft : (3 : Int) ^ k ∣
          n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
            n1Resid (k - 1 - r) ((3 : Int) ^ r * v) := h
      have : (3 : Int) ^ k ∣
          (n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
            n1Resid (k - 1 - r) ((3 : Int) ^ r * v)) -
          (n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
            n1Resid (k - 1 - r) ((3 : Int) ^ r * v) -
            (3 : Int) ^ (2 * r + 1) * (u ^ 2 - v ^ 2)) :=
        hleft.sub (by simpa [hdiff] using hA)
      convert this using 1
      ring
    rw [hshape] at this
    exact (mul_dvd_mul_iff_left hnu).mp (by simpa [mul_comm] using this)
  · intro h
    have hpow : (3 : Int) ^ k ∣ (3 : Int) ^ (2 * r + 1) * (u ^ 2 - v ^ 2) := by
      rw [hshape]
      exact mul_dvd_mul_left _ h
    have hA := hu.sub hv
    have hdiff :
        n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
            n1Resid (k - 1 - r) ((3 : Int) ^ r * v) =
          (n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
            (3 : Int) ^ (2 * r + 1) * u ^ 2) -
          (n1Resid (k - 1 - r) ((3 : Int) ^ r * v) -
            (3 : Int) ^ (2 * r + 1) * v ^ 2) +
          (3 : Int) ^ (2 * r + 1) * (u ^ 2 - v ^ 2) := by
      ring
    rw [hdiff]
    exact hA.add hpow

/-- Units of balanced width `W` sharing a square modulo `3^W` are a sign pair: `u = v` or
`u = -v`. -/
theorem unit_square_pm {W : Nat} {u v : Int}
    (hu : balWidth W u) (hv : balWidth W v)
    (hnu : ¬ (3 : Int) ∣ u) (_hnv : ¬ (3 : Int) ∣ v)
    (h : (3 : Int) ^ W ∣ u ^ 2 - v ^ 2) :
    u = v ∨ u = -v := by
  have hfac : (3 : Int) ^ W ∣ (u - v) * (u + v) := by
    simpa [sq_factor] using h
  have hW : 1 ≤ W := by
    by_contra h0
    have : W = 0 := by omega
    have hu0 : u = 0 := by
      have : balWidth 0 u := by simpa [this] using hu
      unfold balWidth at this
      have : |u| ≤ 0 := by linarith
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    exact hnu (by simp [hu0])
  have h3prod : (3 : Int) ∣ (u - v) * (u + v) :=
    dvd_trans (dvd_pow_self (3 : Int) (by omega)) hfac
  by_cases hminus : (3 : Int) ∣ u - v
  · have hplus : ¬ (3 : Int) ∣ u + v := by
      intro hp
      have hsum : (3 : Int) ∣ (u - v) + (u + v) := hminus.add hp
      have h2u : (u - v) + (u + v) = (2 : Int) * u := by ring
      rw [h2u] at hsum
      exact not_three_dvd_two_mul hnu hsum
    have : (3 : Int) ^ W ∣ u - v := (three_pow_dvd_mul_iff W hplus).mp hfac
    exact Or.inl (balWidth_dvd_sub hu hv this)
  · have hplus : (3 : Int) ∣ u + v := by
      rcases Int.prime_three.dvd_or_dvd h3prod with hL | hR
      · exact (hminus hL).elim
      · exact hR
    have hL : ¬ (3 : Int) ∣ u - v := hminus
    have hswap : (3 : Int) ^ W ∣ (u + v) * (u - v) := by
      simpa [mul_comm] using hfac
    have : (3 : Int) ^ W ∣ u + v := (three_pow_dvd_mul_iff W hL).mp hswap
    exact Or.inr (balWidth_dvd_add hu hv this)

/-- `N0 u` and `N0 (-u)` agree modulo `3^k` exactly when `N0 u` vanishes modulo `3^k`. -/
theorem n0_eq_of_neg {k m : Nat} {u : Int} :
    (3 : Int) ^ k ∣ n0Resid m u - n0Resid m (-u) ↔
      (3 : Int) ^ k ∣ n0Resid m u := by
  have h2 : ¬ (3 : Int) ∣ (2 : Int) := by decide
  have hshape : n0Resid m u - n0Resid m (-u) = (2 : Int) * n0Resid m u := by
    rw [n0Resid_neg]; ring
  constructor
  · intro h
    have : (3 : Int) ^ k ∣ n0Resid m u * (2 : Int) := by
      simpa [hshape, mul_comm] using h
    exact (three_pow_dvd_mul_iff k h2).mp this
  · intro h
    have : (3 : Int) ^ k ∣ n0Resid m u * (2 : Int) :=
      (three_pow_dvd_mul_iff k h2).mpr h
    simpa [hshape, mul_comm] using this

end BTCalculus
