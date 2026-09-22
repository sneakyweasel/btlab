import BTCalculus.MismatchedCubicQuotient

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Invariant decision for the mismatched-width cubic quotient.

The two-scale expansion is ``q_split_high``. The family ``1 + 3^t b``
shows that residue / discarded-digit data of width ``t`` cannot classify
``Q``-fibres: equality of ``Q`` on that family is ``b ≡ c (mod 3^{K-1})``.
-/

theorem iterDZ_one {t : Nat} (ht : 1 ≤ t) : iterDZ t (1 : Int) = 0 := by
  have hn : t = (t - 1) + 1 := by omega
  rw [hn]
  change iterDZ (t - 1) (DZ 1) = 0
  rw [DZ_one]
  simpa [n0Resid] using n0Resid_zero (t - 1)

theorem qCubic_one {t : Nat} (ht : 1 ≤ t) : qCubic t 1 = 0 := by
  unfold qCubic n0Resid
  simpa using iterDZ_one ht

/-- Shift form of `Q` on the family `1 + 3^t b`. -/
theorem q_one_shift {t : Nat} (ht : 1 ≤ t) (b : Int) :
    qCubic t (1 + (3 : Int) ^ t * b) =
      3 * b + (3 : Int) ^ (t + 1) * b ^ 2 + (3 : Int) ^ (2 * t) * b ^ 3 := by
  have h := q_split_high t 1 b
  simpa [qCubic_one ht] using h

/-- Difference of two `Q` values on the family `1 + 3^t b`. -/
lemma q_one_diff {t : Nat} (ht : 1 ≤ t) (b c : Int) :
    qCubic t (1 + (3 : Int) ^ t * b) - qCubic t (1 + (3 : Int) ^ t * c) =
      (3 : Int) * (b - c) *
        (1 + (3 : Int) ^ t * (b + c) +
          (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) := by
  have hb := q_one_shift ht b
  have hc := q_one_shift ht c
  have h2 : 2 * t - 1 + 1 = 2 * t := by omega
  have hpow : (3 : Int) ^ (2 * t) = (3 : Int) * (3 : Int) ^ (2 * t - 1) := by
    have : (3 : Int) ^ (2 * t) = (3 : Int) ^ 1 * (3 : Int) ^ (2 * t - 1) :=
      pow3_split (by omega)
    simpa [pow_one] using this
  rw [hb, hc]
  have hcube : b ^ 3 - c ^ 3 = (b - c) * (b ^ 2 + b * c + c ^ 2) := by ring
  have hsq : b ^ 2 - c ^ 2 = (b - c) * (b + c) := by ring
  calc
    3 * b + (3 : Int) ^ (t + 1) * b ^ 2 + (3 : Int) ^ (2 * t) * b ^ 3 -
        (3 * c + (3 : Int) ^ (t + 1) * c ^ 2 + (3 : Int) ^ (2 * t) * c ^ 3) =
        3 * (b - c) + (3 : Int) ^ (t + 1) * (b ^ 2 - c ^ 2) +
          (3 : Int) ^ (2 * t) * (b ^ 3 - c ^ 3) := by ring
    _ = 3 * (b - c) + (3 : Int) ^ (t + 1) * ((b - c) * (b + c)) +
          (3 : Int) ^ (2 * t) * ((b - c) * (b ^ 2 + b * c + c ^ 2)) := by
        rw [hsq, hcube]
    _ = (3 : Int) * (b - c) *
          (1 + (3 : Int) ^ t * (b + c) +
            (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) := by
        have ht1 : (3 : Int) ^ (t + 1) = (3 : Int) * (3 : Int) ^ t := by
          have : (3 : Int) ^ (t + 1) = (3 : Int) ^ 1 * (3 : Int) ^ t :=
            pow3_split (by omega)
          simpa [pow_one] using this
        rw [ht1, hpow]
        ring

lemma q_one_bracket_unit {t : Nat} (ht : 1 ≤ t) (b c : Int) :
    ¬ (3 : Int) ∣ (1 + (3 : Int) ^ t * (b + c) +
      (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) := by
  intro h
  have ht0 : 1 ≤ t := ht
  have h2 : 1 ≤ 2 * t - 1 := by omega
  have hA : (3 : Int) ∣ (3 : Int) ^ t * (b + c) :=
    dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  have hB : (3 : Int) ∣ (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2) :=
    dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  have h1 : (3 : Int) ∣ (1 : Int) := by
    have : (1 : Int) =
        (1 + (3 : Int) ^ t * (b + c) +
          (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) -
          ((3 : Int) ^ t * (b + c) +
            (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) := by
      ring
    rw [this]
    exact h.sub (hA.add hB)
  exact (by decide : ¬ (3 : Int) ∣ (1 : Int)) h1

lemma three_dvd_of_dvd_mul {x U : Int} (hU : ¬ (3 : Int) ∣ U)
    (h : (3 : Int) ∣ x * U) : (3 : Int) ∣ x := by
  have hpr : Prime (3 : Int) := Int.prime_three
  rcases hpr.dvd_or_dvd h with hx | hU'
  · exact hx
  · exact (hU hU').elim

lemma three_pow_dvd_mul_iff :
    ∀ (n : Nat) {x U : Int}, ¬ (3 : Int) ∣ U →
      ((3 : Int) ^ n ∣ x * U ↔ (3 : Int) ^ n ∣ x)
  | 0, x, U, _ => by simp
  | n + 1, x, U, hU => by
    constructor
    · intro h
      have h3 : (3 : Int) ∣ x * U :=
        dvd_trans (dvd_pow_self (3 : Int) (Nat.succ_ne_zero n)) h
      have hx : (3 : Int) ∣ x := three_dvd_of_dvd_mul hU h3
      obtain ⟨x', hx'⟩ := hx
      have hshape : (3 : Int) ^ (n + 1) = (3 : Int) * (3 : Int) ^ n := by
        have : (3 : Int) ^ (n + 1) = (3 : Int) ^ 1 * (3 : Int) ^ n :=
          pow3_split (by omega)
        simpa [pow_one] using this
      have : (3 : Int) * (3 : Int) ^ n ∣ (3 : Int) * (x' * U) := by
        simpa [hx', mul_assoc, hshape] using h
      have hnz : (3 : Int) ≠ 0 := by decide
      have hn : (3 : Int) ^ n ∣ x' * U :=
        (mul_dvd_mul_iff_left hnz).mp this
      have ih := three_pow_dvd_mul_iff n (x := x') (U := U) hU
      have : (3 : Int) ^ n ∣ x' := ih.mp hn
      rw [hx', hshape]
      exact mul_dvd_mul_left _ this
    · intro hx
      exact hx.mul_right U

/-- On the family `1 + 3^t b` with `t >= 1` and `K >= 1`, `Q` values agree modulo `3^K` exactly when `3^(K-1)` divides `b - c`: one power of three is lost to the bracket unit. -/
theorem q_one_family_dvd {t K : Nat} (ht : 1 ≤ t) (hK : 1 ≤ K)
    (b c : Int) :
    (3 : Int) ^ K ∣ qCubic t (1 + (3 : Int) ^ t * b) -
        qCubic t (1 + (3 : Int) ^ t * c) ↔
      (3 : Int) ^ (K - 1) ∣ b - c := by
  have hdiff := q_one_diff ht b c
  have hU := q_one_bracket_unit ht b c
  constructor
  · intro h
    rw [hdiff] at h
    have : (3 : Int) ^ K ∣
        (3 : Int) * ((b - c) * (1 + (3 : Int) ^ t * (b + c) +
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
        (b - c) * (1 + (3 : Int) ^ t * (b + c) +
          (3 : Int) ^ (2 * t - 1) * (b ^ 2 + b * c + c ^ 2)) :=
      (three_pow_dvd_mul_iff (K - 1) hU).mpr h
    simpa [mul_assoc] using mul_dvd_mul_left (3 : Int) hm

/-- `balCubic t u` is determined by `u` modulo `3^s` whenever `1 <= s` and `t <= s + 1`. -/
theorem balCubic_of_mod {t s : Nat} (hs : 1 ≤ s) (hst : t ≤ s + 1)
    {u v : Int} (h : (3 : Int) ^ s ∣ u - v) :
    balCubic t u = balCubic t v := by
  have hcube : (3 : Int) ^ (s + 1) ∣ u ^ 3 - v ^ 3 :=
    cube_val_succ hs h
  obtain ⟨d, hd⟩ := hcube
  have hsplit : (3 : Int) ^ (s + 1) = (3 : Int) ^ t * (3 : Int) ^ (s + 1 - t) :=
    pow3_split hst
  have : u ^ 3 = v ^ 3 + (3 : Int) ^ t * ((3 : Int) ^ (s + 1 - t) * d) := by
    calc
      u ^ 3 = v ^ 3 + (u ^ 3 - v ^ 3) := by ring
      _ = v ^ 3 + (3 : Int) ^ (s + 1) * d := by rw [hd]
      _ = v ^ 3 + (3 : Int) ^ t * ((3 : Int) ^ (s + 1 - t) * d) := by
        rw [hsplit]; ring
  unfold balCubic
  rw [this, integerJet_add_pow]

theorem q_high_zero {t s K : Nat} (hm : t ≤ 3 * s)
    (hK : K ≤ 3 * s - t) (w : Int) :
    (3 : Int) ^ K ∣ qCubic t ((3 : Int) ^ s * w) :=
  q_zero_of_high hm hK w

end BTCalculus
