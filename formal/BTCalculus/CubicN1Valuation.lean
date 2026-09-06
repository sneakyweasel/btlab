import BTCalculus.CubicDeficitTwo

noncomputable section

namespace BTCalculus

open Polynomial

/-!
General N1 refinement after the depth-deficit N2 filter.

At deficit `r` one has `m = k - 1 - r`. After `p ≡ q (mod 3^r)`,
N1 equality is `3^{k-1-r} ∣ δ (p + q + 3^m)` where `p - q = 3^r δ`.
On the balanced prefix interval, `v_3(p) < r` then forces `p = q`.
-/

lemma pow3_split {a b : Nat} (h : b ≤ a) :
    (3 : Int) ^ a = (3 : Int) ^ b * (3 : Int) ^ (a - b) := by
  rw [← pow_add, Nat.add_comm b, Nat.sub_add_cancel h]

theorem deficit_n1_iff {k r : Nat} (hk : 1 ≤ k) (p q : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q ↔
      (3 : Int) ^ (k - 1) ∣ (p - q) * (p + q + (3 : Int) ^ (k - 1 - r)) := by
  rw [n1Resid_diff]
  have hshape : (3 : Int) ^ k = 3 * (3 : Int) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  constructor
  · intro h
    have : (3 : Int) ^ k ∣
        3 * ((p - q) * (p + q + (3 : Int) ^ (k - 1 - r))) := by
      simpa [mul_assoc] using h
    rw [hshape] at this
    have hnz : (3 : Int) ≠ 0 := by decide
    exact (mul_dvd_mul_iff_left hnz).mp this
  · intro h
    have : (3 : Int) ^ k ∣
        3 * ((p - q) * (p + q + (3 : Int) ^ (k - 1 - r))) := by
      rw [hshape]
      exact mul_dvd_mul_left _ h
    simpa [mul_assoc] using this

/-- Once `N2` is fixed, the depth-`k-1-r` `N1` residuals agree to order `3^k` exactly when
`3^(k-1-r)` divides `d * (p + q + 3^(k-1-r))`, where `p - q = 3^r * d`. -/
theorem n1_after_n2_iff {k r : Nat} (hk : 1 ≤ k) (hr : r + 1 ≤ k)
    {p q d : Int} (hd : p - q = (3 : Int) ^ r * d) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q ↔
      (3 : Int) ^ (k - 1 - r) ∣ d * (p + q + (3 : Int) ^ (k - 1 - r)) := by
  rw [deficit_n1_iff hk]
  have hle : r ≤ k - 1 := by omega
  have hshape : (3 : Int) ^ (k - 1) = (3 : Int) ^ r * (3 : Int) ^ (k - 1 - r) :=
    pow3_split hle
  constructor
  · intro h
    rw [hd, hshape] at h
    have hnz : (3 : Int) ^ r ≠ 0 := pow_ne_zero _ (by decide)
    exact (mul_dvd_mul_iff_left hnz).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h)
  · intro h
    rw [hd, hshape]
    simpa [mul_assoc] using mul_dvd_mul_left ((3 : Int) ^ r) h

lemma three_pow_dvd_of_two_mul_pow {r : Nat} {p : Int}
    (h : (3 : Int) ^ r ∣ 2 * p) : (3 : Int) ^ r ∣ p := by
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
    have h1 : (3 : Int) ∣ 2 * p :=
      dvd_trans (pow_dvd_pow (3 : Int) (by omega : 1 ≤ r + 1)) h
    have hp : (3 : Int) ∣ p :=
      three_pow_dvd_of_two_mul (k := 1) (by simpa [pow_one] using h1)
    obtain ⟨t, ht⟩ := hp
    have h6 : (3 : Int) ^ (r + 1) ∣ 6 * t := by
      convert h using 1
      rw [ht]
      ring
    have hnz : (3 : Int) ≠ 0 := by decide
    have h2t : (3 : Int) ^ r ∣ 2 * t := by
      have hshape : (3 : Int) ^ (r + 1) = 3 * (3 : Int) ^ r := by rw [pow_succ']
      have h6' : 6 * t = 3 * (2 * t) := by ring
      have : 3 * (3 : Int) ^ r ∣ 3 * (2 * t) := by
        simpa [hshape, h6'] using h6
      exact (mul_dvd_mul_iff_left hnz).mp this
    have ht' := ih h2t
    rw [ht, pow_succ']
    exact mul_dvd_mul_left _ ht'

lemma exists_val_lt {r : Nat} {p : Int}
    (h : ¬ (3 : Int) ^ r ∣ p) :
    ∃ s, s < r ∧ (3 : Int) ^ s ∣ p ∧ ¬ (3 : Int) ^ (s + 1) ∣ p := by
  induction r with
  | zero =>
    exact (h (by simp)).elim
  | succ r ih =>
    by_cases h' : (3 : Int) ^ r ∣ p
    · exact ⟨r, Nat.lt_succ_self r, h', h⟩
    · obtain ⟨s, hs, hs1, hs2⟩ := ih h'
      exact ⟨s, Nat.lt_succ_of_lt hs, hs1, hs2⟩

lemma not_three_dvd_add_of_unit {p q : Int}
    (hp : ¬ (3 : Int) ∣ p) (hcong : (3 : Int) ∣ p - q) :
    ¬ (3 : Int) ∣ p + q := by
  intro h
  have : (3 : Int) ∣ 2 * p := by
    have : p + q + (p - q) = 2 * p := by ring
    rw [← this]
    exact h.add hcong
  exact hp (three_pow_dvd_of_two_mul (k := 1) (by simpa [pow_one] using this))

theorem n1_unit_injective {k r : Nat} (hr : 1 ≤ r) (hk : r + 1 ≤ k)
    {p q : Int}
    (hpw : balWidth (k - 1 - r) p) (hqw : balWidth (k - 1 - r) q)
    (hunit : ¬ (3 : Int) ∣ p)
    (hN2 : (3 : Int) ^ r ∣ p - q)
    (hN1 : (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q) :
    p = q := by
  have hk1 : 1 ≤ k := by omega
  have h3 : (3 : Int) ∣ p - q :=
    dvd_trans (pow_dvd_pow (3 : Int) hr) hN2
  obtain ⟨d, hd⟩ := hN2
  have hS : ¬ (3 : Int) ∣ p + q + (3 : Int) ^ (k - 1 - r) := by
    intro h
    have hm : 1 ≤ k - 1 - r ∨ k - 1 - r = 0 := by omega
    cases hm with
    | inl hm1 =>
      have hpow : (3 : Int) ∣ (3 : Int) ^ (k - 1 - r) :=
        dvd_trans (pow_dvd_pow (3 : Int) hm1) (dvd_refl _)
      have hsum : (3 : Int) ∣ p + q := by
        have : p + q =
            p + q + (3 : Int) ^ (k - 1 - r) - (3 : Int) ^ (k - 1 - r) := by
          ring
        rw [this]
        exact dvd_sub h hpow
      exact not_three_dvd_add_of_unit hunit h3 hsum
    | inr hm0 =>
      have hp0 : p = 0 := by
        have : balWidth 0 p := by simpa [hm0] using hpw
        unfold balWidth at this
        have : |p| ≤ 0 := by
          have : 2 * |p| ≤ (3 : Int) ^ 0 - 1 := this
          simp at this
          linarith
        exact abs_nonpos_iff.mp this
      exact hunit (by simp [hp0])
  have hN1' := (n1_after_n2_iff hk1 hk hd).1 hN1
  have hcop : IsCoprime ((3 : Int) ^ (k - 1 - r))
      (p + q + (3 : Int) ^ (k - 1 - r)) :=
    IsCoprime.pow_left (three_prime.coprime_iff_not_dvd.mpr hS)
  have hdvd := hcop.dvd_of_dvd_mul_right hN1'
  have hle : r ≤ k - 1 := by omega
  have hstrong : (3 : Int) ^ (k - 1) ∣ p - q := by
    rw [hd, pow3_split hle]
    exact mul_dvd_mul_left _ hdvd
  have hm : (3 : Int) ^ (k - 1 - r) ∣ p - q :=
    dvd_trans (pow_dvd_pow (3 : Int) (by omega : k - 1 - r ≤ k - 1)) hstrong
  exact balWidth_dvd_sub hpw hqw hm

theorem n1_low_val_injective {k r s : Nat}
    (_hr : 1 ≤ r) (hk : r + 1 ≤ k) (hs : s < r)
    {p q : Int}
    (hpw : balWidth (k - 1 - r) p) (hqw : balWidth (k - 1 - r) q)
    (hps : (3 : Int) ^ s ∣ p) (hps1 : ¬ (3 : Int) ^ (s + 1) ∣ p)
    (hN2 : (3 : Int) ^ r ∣ p - q)
    (hN1 : (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q) :
    p = q := by
  have hk1 : 1 ≤ k := by omega
  have hp0 : p ≠ 0 := by
    intro hpz
    exact hps1 (by simp [hpz])
  have hmpos : |p| < (3 : Int) ^ (k - 1 - r) := by
    unfold balWidth at hpw
    have hpos : (0 : Int) < (3 : Int) ^ (k - 1 - r) := pow_pos (by decide) _
    linarith
  have hsm : s < k - 1 - r := by
    by_contra hge
    have hle : k - 1 - r ≤ s := by omega
    have : (3 : Int) ^ (k - 1 - r) ∣ p :=
      dvd_trans (pow_dvd_pow (3 : Int) hle) hps
    exact hp0 (dvd_abs_lt_pow this hmpos)
  have hdiff_s : (3 : Int) ^ s ∣ p - q :=
    dvd_trans (pow_dvd_pow (3 : Int) (le_of_lt hs)) hN2
  have hqs : (3 : Int) ^ s ∣ q := by
    have : q = p - (p - q) := by ring
    rw [this]
    exact dvd_sub hps hdiff_s
  obtain ⟨u, hu⟩ := hps
  obtain ⟨v, hv⟩ := hqs
  have hu3 : ¬ (3 : Int) ∣ u := by
    intro hu3'
    have : (3 : Int) ^ (s + 1) ∣ p := by
      rw [hu, pow_succ]
      exact mul_dvd_mul_left _ hu3'
    exact hps1 this
  have hN2keep := hN2
  obtain ⟨d, hd⟩ := hN2
  have hN1' := (n1_after_n2_iff hk1 hk hd).1 hN1
  have hle_s : s ≤ k - 1 - r := by omega
  have hexp : p + q + (3 : Int) ^ (k - 1 - r) =
      (3 : Int) ^ s * (u + v + (3 : Int) ^ (k - 1 - r - s)) := by
    rw [hu, hv, pow3_split hle_s]
    ring
  rw [hexp] at hN1'
  have hms : 1 ≤ k - 1 - r - s := by omega
  have hS' : ¬ (3 : Int) ∣ u + v + (3 : Int) ^ (k - 1 - r - s) := by
    intro hS'
    have h2 : (3 : Int) ∣ u + v := by
      have hpow : (3 : Int) ∣ (3 : Int) ^ (k - 1 - r - s) :=
        dvd_trans (pow_dvd_pow (3 : Int) hms) (dvd_refl _)
      have : u + v =
          u + v + (3 : Int) ^ (k - 1 - r - s) -
            (3 : Int) ^ (k - 1 - r - s) := by
        ring
      rw [this]
      exact dvd_sub hS' hpow
    have hcong : (3 : Int) ∣ u - v := by
      have hdiff : p - q = (3 : Int) ^ s * (u - v) := by
        rw [hu, hv]; ring
      have hsr : (3 : Int) ^ (s + 1) ∣ p - q :=
        dvd_trans (pow_dvd_pow (3 : Int) (by omega : s + 1 ≤ r)) hN2keep
      have hshape : (3 : Int) ^ (s + 1) = (3 : Int) ^ s * 3 := by
        rw [pow_succ]
      rw [hdiff, hshape] at hsr
      have hnz : (3 : Int) ^ s ≠ 0 := pow_ne_zero _ (by decide)
      simpa [mul_assoc] using (mul_dvd_mul_iff_left hnz).mp hsr
    exact not_three_dvd_add_of_unit hu3 hcong h2
  have hnz : (3 : Int) ^ s ≠ 0 := pow_ne_zero _ (by decide)
  rw [pow3_split hle_s] at hN1'
  have hmid : (3 : Int) ^ (k - 1 - r - s) ∣
      d * (u + v + (3 : Int) ^ (k - 1 - r - s)) :=
    (mul_dvd_mul_iff_left hnz).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hN1')
  have hcop : IsCoprime ((3 : Int) ^ (k - 1 - r - s))
      (u + v + (3 : Int) ^ (k - 1 - r - s)) :=
    IsCoprime.pow_left (three_prime.coprime_iff_not_dvd.mpr hS')
  have hdd := hcop.dvd_of_dvd_mul_right (by
    simpa [mul_comm] using hmid)
  have hstrong : (3 : Int) ^ (k - 1 - r) ∣ p - q := by
    rw [hd]
    have hle_rs : s ≤ r := by omega
    rw [pow3_split hle_s, pow3_split hle_rs]
    have : (3 : Int) ^ (k - 1 - r - s) ∣ (3 : Int) ^ (r - s) * d :=
      dvd_mul_of_dvd_right hdd _
    simpa [mul_assoc] using mul_dvd_mul_left ((3 : Int) ^ s) this
  exact balWidth_dvd_sub hpw hqw hstrong

theorem n1_val_lt_injective {k r : Nat} (hr : 1 ≤ r) (hk : r + 1 ≤ k)
    {p q : Int}
    (hpw : balWidth (k - 1 - r) p) (hqw : balWidth (k - 1 - r) q)
    (hnp : ¬ (3 : Int) ^ r ∣ p)
    (hN2 : (3 : Int) ^ r ∣ p - q)
    (hN1 : (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q) :
    p = q := by
  obtain ⟨s, hs, hs1, hs2⟩ := exists_val_lt hnp
  exact n1_low_val_injective hr hk hs hpw hqw hs1 hs2 hN2 hN1

/-- Every nontrivial `N2`-then-`N1` fibre lies in `3^r ZZ`: distinct `p != q` of balanced
width `k-1-r` that agree in both layers force `3^r | p`. -/
theorem n21_fibre_in_pow {k r : Nat} (hr : 1 ≤ r) (hk : r + 1 ≤ k)
    {p q : Int}
    (hpw : balWidth (k - 1 - r) p) (hqw : balWidth (k - 1 - r) q)
    (hne : p ≠ q)
    (hN2 : (3 : Int) ^ r ∣ p - q)
    (hN1 : (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q) :
    (3 : Int) ^ r ∣ p := by
  by_contra hnp
  exact hne (n1_val_lt_injective hr hk hpw hqw hnp hN2 hN1)

theorem n21_sign_n2_iff {k r : Nat} (hk : r + 1 ≤ k) (p : Int) :
    (3 : Int) ^ k ∣ n2Resid (k - 1 - r) p - n2Resid (k - 1 - r) (-p) ↔
      (3 : Int) ^ r ∣ p := by
  rw [depthDeficit_n2_visibility hk]
  constructor
  · intro h
    have : (3 : Int) ^ r ∣ p * 2 := by
      have heq : p + p = p * (2 : Int) := by ring
      simpa [heq] using h
    exact three_pow_dvd_of_two_mul_pow (by simpa [mul_comm] using this)
  · intro h
    have := h.mul_left (2 : Int)
    have heq : (2 : Int) * p = p + p := by ring
    simpa [heq] using this

theorem n21_sign_n1_iff {k r : Nat} (hk1 : 1 ≤ k) (hk : r + 1 ≤ k) (p : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) (-p) ↔
      (3 : Int) ^ r ∣ p := by
  rw [deficit_n1_iff hk1]
  have hprod : (p - (-p)) * (p + (-p) + (3 : Int) ^ (k - 1 - r)) =
      2 * p * (3 : Int) ^ (k - 1 - r) := by ring
  rw [hprod]
  have hle : r ≤ k - 1 := by omega
  constructor
  · intro h
    rw [pow3_split hle] at h
    have hnz : (3 : Int) ^ (k - 1 - r) ≠ 0 := pow_ne_zero _ (by decide)
    have : (3 : Int) ^ r ∣ 2 * p := (mul_dvd_mul_iff_right hnz).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h)
    exact three_pow_dvd_of_two_mul_pow this
  · intro h
    rw [pow3_split hle]
    exact mul_dvd_mul (by simpa using h.mul_left (2 : Int)) (dvd_refl _)

theorem n21_sign_iff {k r : Nat} (hk1 : 1 ≤ k) (hk : r + 1 ≤ k) (p : Int) :
    ((3 : Int) ^ k ∣ n2Resid (k - 1 - r) p - n2Resid (k - 1 - r) (-p)) ∧
        ((3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) (-p)) ↔
      (3 : Int) ^ r ∣ p := by
  constructor
  · intro ⟨h2, _⟩
    exact (n21_sign_n2_iff hk p).1 h2
  · intro h
    exact ⟨(n21_sign_n2_iff hk p).2 h, (n21_sign_n1_iff hk1 hk p).2 h⟩

theorem n1_high_val_scaled {k r : Nat} (hkr : 2 * r + 2 ≤ k) {u v : Int} :
    (3 : Int) ^ k ∣
        n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
          n1Resid (k - 1 - r) ((3 : Int) ^ r * v) ↔
      (3 : Int) ^ (k - 2 * r) ∣
        n1Resid (k - 2 * r - 1) u - n1Resid (k - 2 * r - 1) v := by
  have hk1 : 1 ≤ k := by omega
  have hr : r + 1 ≤ k := by omega
  have hk1' : 1 ≤ k - 2 * r := by omega
  have hd : (3 : Int) ^ r * u - (3 : Int) ^ r * v = (3 : Int) ^ r * (u - v) := by
    ring
  have hmr : r ≤ k - 1 - r := by omega
  have hm2 : k - 1 - r - r = k - 1 - 2 * r := by omega
  have hm0 : k - 1 - 2 * r = k - 2 * r - 1 := by omega
  have hexp : (3 : Int) ^ r * u + (3 : Int) ^ r * v + (3 : Int) ^ (k - 1 - r) =
      (3 : Int) ^ r * (u + v + (3 : Int) ^ (k - 1 - 2 * r)) := by
    rw [pow3_split hmr, hm2]
    ring
  constructor
  · intro h
    have hN := (n1_after_n2_iff hk1 hr hd).1 h
    rw [hexp, pow3_split hmr, hm2] at hN
    have hnz : (3 : Int) ^ r ≠ 0 := pow_ne_zero _ (by decide)
    have hmid : (3 : Int) ^ (k - 1 - 2 * r) ∣
        (u - v) * (u + v + (3 : Int) ^ (k - 1 - 2 * r)) :=
      (mul_dvd_mul_iff_left hnz).mp (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hN)
    have hmid' : (3 : Int) ^ (k - 2 * r - 1) ∣
        (u - v) * (u + v + (3 : Int) ^ (k - 2 * r - 1)) := by
      simpa [hm0] using hmid
    exact (deficit_n1_iff (k := k - 2 * r) (r := 0) hk1' u v).2 hmid'
  · intro h
    have hmid := (deficit_n1_iff (k := k - 2 * r) (r := 0) hk1' u v).1 h
    have hmid' : (3 : Int) ^ (k - 1 - 2 * r) ∣
        (u - v) * (u + v + (3 : Int) ^ (k - 1 - 2 * r)) := by
      simpa [hm0] using hmid
    have hN : (3 : Int) ^ (k - 1 - r) ∣
        (u - v) * ((3 : Int) ^ r * u + (3 : Int) ^ r * v +
          (3 : Int) ^ (k - 1 - r)) := by
      rw [hexp, pow3_split hmr, hm2]
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_dvd_mul_left ((3 : Int) ^ r) hmid'
    exact (n1_after_n2_iff hk1 hr hd).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hN)

theorem n1_unit_r1 {k : Nat} (hk : 2 ≤ k) {p q : Int}
    (hpw : balWidth (k - 2) p) (hqw : balWidth (k - 2) q)
    (hunit : ¬ (3 : Int) ∣ p)
    (hN2 : (3 : Int) ∣ p - q)
    (hN1 : (3 : Int) ^ k ∣ n1Resid (k - 2) p - n1Resid (k - 2) q) :
    p = q := by
  simpa [pow_one] using
    n1_unit_injective (r := 1) (by decide) (by omega) hpw hqw hunit hN2 hN1

theorem n1_unit_r2 {k : Nat} (hk : 3 ≤ k) {p q : Int}
    (hpw : balWidth (k - 3) p) (hqw : balWidth (k - 3) q)
    (hunit : ¬ (3 : Int) ∣ p)
    (hN2 : (3 : Int) ^ 2 ∣ p - q)
    (hN1 : (3 : Int) ^ k ∣ n1Resid (k - 3) p - n1Resid (k - 3) q) :
    p = q :=
  n1_unit_injective (r := 2) (by decide) (by omega) hpw hqw hunit hN2 hN1

end BTCalculus
