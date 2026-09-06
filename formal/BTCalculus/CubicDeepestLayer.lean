import BTCalculus.CubicFibres

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Deepest-layer Newton coordinates of residuals of X^3.

At depth m = k-1 one has N3 = 0, N2 = 0, and
N1 = 3 p^2 modulo 3^k (for k >= 2). Fibres are decided by
the square congruence and the cubic quotient iterDZ (k-1) (p^3).
-/

def deepestN1 (p : ℤ) : ℤ :=
  3 * p ^ 2

def zeroExp (k : ℕ) : ℕ :=
  (2 * k + 1) / 3

theorem n1Resid_deepest_diff {k : ℕ} (hk : 1 ≤ k) (p q : ℤ) :
    n1Resid (k - 1) p - n1Resid (k - 1) q =
      3 * (p ^ 2 - q ^ 2) + (3 : ℤ) ^ k * (p - q) := by
  rw [n1Resid_diff]
  have hpow : (3 : ℤ) * (3 : ℤ) ^ (k - 1) = (3 : ℤ) ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  have : 3 * (p - q) * (p + q + (3 : ℤ) ^ (k - 1)) =
      3 * (p ^ 2 - q ^ 2) + (3 : ℤ) * (3 : ℤ) ^ (k - 1) * (p - q) := by
    ring
  rw [this, hpow]

theorem deepest_n1_iff {k : ℕ} (hk : 1 ≤ k) (p q : ℤ) :
    (3 : ℤ) ^ k ∣ n1Resid (k - 1) p - n1Resid (k - 1) q ↔
      (3 : ℤ) ^ (k - 1) ∣ p ^ 2 - q ^ 2 := by
  have hdiff := n1Resid_deepest_diff hk p q
  have hshape : (3 : ℤ) ^ k = 3 * (3 : ℤ) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  constructor
  · intro h
    have hx : (3 : ℤ) ^ k ∣
        3 * (p ^ 2 - q ^ 2) + (3 : ℤ) ^ k * (p - q) := by
      simpa [hdiff] using h
    have hx' : (3 : ℤ) ^ k ∣
        (3 : ℤ) ^ k * (p - q) + 3 * (p ^ 2 - q ^ 2) := by
      simpa [add_comm] using hx
    have : (3 : ℤ) ^ k ∣ 3 * (p ^ 2 - q ^ 2) :=
      (dvd_add_right (dvd_mul_right _ _)).mp hx'
    rw [hshape] at this
    have hnz : (3 : ℤ) ≠ 0 := by decide
    exact (mul_dvd_mul_iff_left hnz).mp this
  · intro h
    have h1 : (3 : ℤ) ^ k ∣ 3 * (p ^ 2 - q ^ 2) := by
      rw [hshape]
      exact mul_dvd_mul_left _ h
    have h2 : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ k * (p - q) :=
      dvd_mul_right _ _
    have := h1.add h2
    simpa [hdiff] using this

theorem deepest_n1_mod {k : ℕ} (hk : 2 ≤ k) (p : ℤ) :
    (3 : ℤ) ^ k ∣ n1Resid (k - 1) p - deepestN1 p := by
  unfold n1Resid deepestN1
  have hk1 : 1 ≤ k := by omega
  have hm : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
  have hle : k ≤ 2 * (k - 1) := by omega
  rw [hm]
  have hA : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (2 * (k - 1)) := pow_dvd_pow _ hle
  have hB : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ k * p := dvd_mul_right _ _
  have := hA.add hB
  have heq :
      (3 : ℤ) ^ (2 * (k - 1)) + (3 : ℤ) ^ k * p + 3 * p ^ 2 - 3 * p ^ 2 =
        (3 : ℤ) ^ (2 * (k - 1)) + (3 : ℤ) ^ k * p := by
    ring
  simpa [heq] using this

theorem deepest_n2_zero {k : ℕ} (hk : 1 ≤ k) (p : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid (k - 1) p := by
  unfold n2Resid
  have hm : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  rw [hm]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (dvd_mul_right ((3 : ℤ) ^ k) (2 * (p + (3 : ℤ) ^ (k - 1))))

theorem deepest_n3_zero {k : ℕ} (hk : 1 ≤ k) :
    (3 : ℤ) ^ k ∣ n3Resid (k - 1) := by
  unfold n3Resid
  have hle : k ≤ 2 * (k - 1) + 1 := by omega
  have hpow : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (2 * (k - 1) + 1) :=
    pow_dvd_pow _ hle
  have := hpow.mul_left (2 : ℤ)
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

theorem sq_factor (p q : ℤ) :
    p ^ 2 - q ^ 2 = (p - q) * (p + q) := by
  ring

/-- Agreement of the depth-`k-1` `N1` residuals to order `3^k` forces `3^(k-1)` to divide
`(p - q) * (p + q)`.  It is the square factorisation, not the layer description, that
this statement carries. -/
theorem deepest_sq_of_n1 {k : ℕ} (hk : 1 ≤ k) {p q : ℤ}
    (h : (3 : ℤ) ^ k ∣ n1Resid (k - 1) p - n1Resid (k - 1) q) :
    (3 : ℤ) ^ (k - 1) ∣ (p - q) * (p + q) := by
  have := (deepest_n1_iff hk p q).1 h
  simpa [sq_factor] using this

theorem balWidth_dvd_sub {m : ℕ} {p q : ℤ}
    (hp : balWidth m p) (hq : balWidth m q)
    (h : (3 : ℤ) ^ m ∣ p - q) : p = q := by
  have hbound : |p - q| < (3 : ℤ) ^ m := by
    have := balWidth_sub hp hq
    have hpos : (0 : ℤ) < (3 : ℤ) ^ m := pow_pos (by decide) _
    linarith
  exact sub_eq_zero.mp (dvd_abs_lt_pow h hbound)

theorem balWidth_dvd_add {m : ℕ} {p q : ℤ}
    (hp : balWidth m p) (hq : balWidth m q)
    (h : (3 : ℤ) ^ m ∣ p + q) : p = -q := by
  have hq' : balWidth m (-q) := by
    simpa [balWidth, abs_neg] using hq
  have : (3 : ℤ) ^ m ∣ p - (-q) := by simpa [sub_neg_eq_add] using h
  exact balWidth_dvd_sub hp hq' this

lemma packWord_integerJet_balWidth (m : ℕ) (n : ℤ) :
    balWidth m (packWord (integerJet m n)) := by
  have := two_mul_packWord_le (isTritList_integerJet m n)
  simpa [balWidth, integerJet_length] using this

lemma iterDZ_of_dvd {m : ℕ} {n : ℤ} (h : (3 : ℤ) ^ m ∣ n) :
    packWord (integerJet m n) = 0 ∧
      n = (3 : ℤ) ^ m * iterDZ m n := by
  have hde := packWord_integerJet_decomp m n
  have hpack : (3 : ℤ) ^ m ∣ packWord (integerJet m n) := by
    have : packWord (integerJet m n) =
        n - (3 : ℤ) ^ m * iterDZ m n := by linarith
    rw [this]
    exact h.sub (dvd_mul_right _ _)
  have hbound : |packWord (integerJet m n)| < (3 : ℤ) ^ m := by
    have hb := packWord_integerJet_balWidth m n
    have hpos : (0 : ℤ) < (3 : ℤ) ^ m := pow_pos (by decide) _
    unfold balWidth at hb
    linarith
  have hz : packWord (integerJet m n) = 0 :=
    dvd_abs_lt_pow hpack hbound
  refine ⟨hz, ?_⟩
  simpa [hz] using hde

theorem n0Resid_of_dvd {m : ℕ} {p : ℤ}
    (h : (3 : ℤ) ^ m ∣ p ^ 3) :
    n0Resid m p = p ^ 3 / (3 : ℤ) ^ m := by
  unfold n0Resid
  have ⟨_, hde⟩ := iterDZ_of_dvd h
  have hpos : (3 : ℤ) ^ m ≠ 0 := pow_ne_zero _ (by decide)
  exact (Int.eq_ediv_of_mul_eq_right hpos hde.symm)

theorem n0_congr_decomp (m : ℕ) (p q : ℤ) :
    n0Resid m p - n0Resid m q =
      (p ^ 3 - q ^ 3
        - (packWord (integerJet m (p ^ 3))
            - packWord (integerJet m (q ^ 3)))) / (3 : ℤ) ^ m := by
  have hp := packWord_integerJet_decomp m (p ^ 3)
  have hq := packWord_integerJet_decomp m (q ^ 3)
  unfold n0Resid
  have hpos : (3 : ℤ) ^ m ≠ 0 := pow_ne_zero _ (by decide)
  apply Int.eq_ediv_of_mul_eq_right hpos
  linarith

lemma three_prime : Prime (3 : ℤ) :=
  Int.prime_iff_natAbs_prime.mpr (by decide)

lemma three_dvd_of_dvd_sq {p : ℤ} (h : (3 : ℤ) ∣ p ^ 2) : (3 : ℤ) ∣ p :=
  three_prime.dvd_of_dvd_pow h

lemma three_pow_dvd_sq : ∀ (n : ℕ) (p : ℤ),
    (3 : ℤ) ^ n ∣ p ^ 2 → (3 : ℤ) ^ ((n + 1) / 2) ∣ p
  | 0, p, _ => by simp
  | 1, p, h => by
    have : (3 : ℤ) ∣ p ^ 2 := by simpa using h
    simpa using three_dvd_of_dvd_sq this
  | n + 2, p, h => by
    have h3 : (3 : ℤ) ∣ p ^ 2 :=
      dvd_trans (pow_dvd_pow (3 : ℤ) (by omega : 1 ≤ n + 2)) h
    have hp := three_dvd_of_dvd_sq h3
    obtain ⟨q, hq⟩ := hp
    have hsq : (3 : ℤ) ^ (n + 2) ∣ (3 * q) ^ 2 := by simpa [hq] using h
    have h9 : (3 * q) ^ 2 = 9 * q ^ 2 := by ring
    have hpow : (3 : ℤ) ^ (n + 2) = 9 * (3 : ℤ) ^ n := by
      rw [pow_add, pow_two]
      ring
    have hq2 : (3 : ℤ) ^ n ∣ q ^ 2 := by
      have : 9 * (3 : ℤ) ^ n ∣ 9 * q ^ 2 := by
        simpa [hpow, h9] using hsq
      have hnz : (9 : ℤ) ≠ 0 := by decide
      exact (mul_dvd_mul_iff_left hnz).mp this
    have ih := three_pow_dvd_sq n q hq2
    have hsucc : (n + 3) / 2 = (n + 1) / 2 + 1 := by omega
    have : (3 : ℤ) ^ ((n + 3) / 2) ∣ 3 * q := by
      rw [hsucc, pow_succ']
      exact mul_dvd_mul_left _ ih
    simpa [hq, show (n + 2 + 1) / 2 = (n + 3) / 2 from rfl] using this

lemma three_pow_dvd_cube : ∀ (n : ℕ) (p : ℤ),
    (3 : ℤ) ^ n ∣ p ^ 3 → (3 : ℤ) ^ ((n + 2) / 3) ∣ p
  | 0, p, _ => by simp
  | 1, p, h => by
    have : (3 : ℤ) ∣ p ^ 3 := by simpa using h
    exact three_prime.dvd_of_dvd_pow this
  | 2, p, h => by
    have : (3 : ℤ) ∣ p ^ 3 :=
      dvd_trans (pow_dvd_pow (3 : ℤ) (by decide : 1 ≤ 2)) h
    exact three_prime.dvd_of_dvd_pow this
  | n + 3, p, h => by
    have h3 : (3 : ℤ) ∣ p ^ 3 :=
      dvd_trans (pow_dvd_pow (3 : ℤ) (by omega : 1 ≤ n + 3)) h
    have hp := three_prime.dvd_of_dvd_pow h3
    obtain ⟨q, hq⟩ := hp
    have hcu : (3 : ℤ) ^ (n + 3) ∣ (3 * q) ^ 3 := by simpa [hq] using h
    have h27 : (3 * q) ^ 3 = 27 * q ^ 3 := by ring
    have hpow : (3 : ℤ) ^ (n + 3) = 27 * (3 : ℤ) ^ n := by
      rw [pow_add]
      ring
    have hq3 : (3 : ℤ) ^ n ∣ q ^ 3 := by
      have : 27 * (3 : ℤ) ^ n ∣ 27 * q ^ 3 := by
        simpa [hpow, h27] using hcu
      have hnz : (27 : ℤ) ≠ 0 := by decide
      exact (mul_dvd_mul_iff_left hnz).mp this
    have ih := three_pow_dvd_cube n q hq3
    have hsucc : (n + 5) / 3 = (n + 2) / 3 + 1 := by omega
    have : (3 : ℤ) ^ ((n + 5) / 3) ∣ 3 * q := by
      rw [hsucc, pow_succ']
      exact mul_dvd_mul_left _ ih
    simpa [hq, show (n + 3 + 2) / 3 = (n + 5) / 3 from rfl] using this

theorem zeroExp_sq {k : ℕ} (hk : 1 ≤ k) :
    k - 1 ≤ 2 * zeroExp k := by
  unfold zeroExp
  omega

theorem zeroExp_cu {k : ℕ} :
    2 * k - 1 ≤ 3 * zeroExp k := by
  unfold zeroExp
  omega

theorem n1Resid_zero (m : ℕ) :
    n1Resid m 0 = (3 : ℤ) ^ (2 * m) := by
  unfold n1Resid
  simp

theorem n0Resid_zero (m : ℕ) : n0Resid m 0 = 0 := by
  unfold n0Resid
  induction m with
  | zero => simp [iterDZ]
  | succ m ih =>
    have hlsd : lsdZ 0 = 0 := by simp [lsdZ]
    have hdz : DZ 0 = 0 := by simp [DZ, hlsd]
    simpa [iterDZ, hdz] using ih

theorem deepest_n1_zero {k : ℕ} (hk : 2 ≤ k) :
    (3 : ℤ) ^ k ∣ n1Resid (k - 1) 0 := by
  rw [n1Resid_zero]
  have hle : k ≤ 2 * (k - 1) := by omega
  exact pow_dvd_pow _ hle

theorem zero_fibre_of {k : ℕ} {p : ℤ} (hk : 2 ≤ k)
    (hp : (3 : ℤ) ^ zeroExp k ∣ p) :
    (3 : ℤ) ^ k ∣ n1Resid (k - 1) p ∧
      (3 : ℤ) ^ k ∣ n0Resid (k - 1) p := by
  have hk1 : 1 ≤ k := by omega
  have hsq : (3 : ℤ) ^ (k - 1) ∣ p ^ 2 := by
    have : (3 : ℤ) ^ (2 * zeroExp k) ∣ p ^ 2 := by
      have h2 := pow_dvd_pow_of_dvd hp 2
      rw [← pow_mul] at h2
      simpa [mul_comm] using h2
    exact dvd_trans (pow_dvd_pow (3 : ℤ) (zeroExp_sq hk1)) this
  have hN1 : (3 : ℤ) ^ k ∣ n1Resid (k - 1) p - n1Resid (k - 1) 0 :=
    (deepest_n1_iff hk1 p 0).2 (by simpa using hsq)
  have hN10 := deepest_n1_zero hk
  have h1 : (3 : ℤ) ^ k ∣ n1Resid (k - 1) p := by
    have : n1Resid (k - 1) p =
        (n1Resid (k - 1) p - n1Resid (k - 1) 0) + n1Resid (k - 1) 0 := by
      ring
    rw [this]
    exact hN1.add hN10
  have hcu : (3 : ℤ) ^ (3 * zeroExp k) ∣ p ^ 3 := by
    have h3 := pow_dvd_pow_of_dvd hp 3
    rw [← pow_mul] at h3
    simpa [mul_comm] using h3
  have hlow : (3 : ℤ) ^ (k - 1) ∣ p ^ 3 :=
    dvd_trans (pow_dvd_pow (3 : ℤ) (by
      have := zeroExp_cu (k := k)
      omega)) hcu
  have hde' := (iterDZ_of_dvd hlow).2
  have hhi : (3 : ℤ) ^ (2 * k - 1) ∣ p ^ 3 :=
    dvd_trans (pow_dvd_pow (3 : ℤ) (zeroExp_cu (k := k))) hcu
  have hN0 : (3 : ℤ) ^ k ∣ n0Resid (k - 1) p := by
    unfold n0Resid
    have hshape : (3 : ℤ) ^ (2 * k - 1) =
        (3 : ℤ) ^ (k - 1) * (3 : ℤ) ^ k := by
      have : 2 * k - 1 = (k - 1) + k := by omega
      rw [this, pow_add]
    obtain ⟨t, ht⟩ := hhi
    have : iterDZ (k - 1) (p ^ 3) = (3 : ℤ) ^ k * t := by
      have hpos : (3 : ℤ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by decide)
      apply mul_left_cancel₀ hpos
      rw [← hde', ht, hshape]
      ring
    rw [this]
    exact dvd_mul_right _ _
  exact ⟨h1, hN0⟩

theorem zero_fibre_imp {k : ℕ} {p : ℤ} (hk : 2 ≤ k)
    (hN1 : (3 : ℤ) ^ k ∣ n1Resid (k - 1) p)
    (hN0 : (3 : ℤ) ^ k ∣ n0Resid (k - 1) p) :
    (3 : ℤ) ^ zeroExp k ∣ p := by
  have hk1 : 1 ≤ k := by omega
  have hN10 := deepest_n1_zero hk
  have hdiff : (3 : ℤ) ^ k ∣ n1Resid (k - 1) p - n1Resid (k - 1) 0 :=
    hN1.sub hN10
  have hsq : (3 : ℤ) ^ (k - 1) ∣ p ^ 2 := by
    simpa using (deepest_n1_iff hk1 p 0).1 hdiff
  have hs0 := three_pow_dvd_sq (k - 1) p hsq
  have hs0' : (3 : ℤ) ^ (k / 2) ∣ p := by
    have : (k - 1 + 1) / 2 = k / 2 := by omega
    simpa [this] using hs0
  have h3s : (3 : ℤ) ^ (k - 1) ∣ p ^ 3 := by
    have hmul : (3 : ℤ) ^ (3 * (k / 2)) ∣ p ^ 3 := by
      have h3 := pow_dvd_pow_of_dvd hs0' 3
      rw [← pow_mul] at h3
      simpa [mul_comm] using h3
    refine dvd_trans (pow_dvd_pow (3 : ℤ) ?_) hmul
    omega
  have hde' := (iterDZ_of_dvd h3s).2
  obtain ⟨t, ht⟩ := hN0
  have hprod : p ^ 3 = (3 : ℤ) ^ (2 * k - 1) * t := by
    have hshape : (3 : ℤ) ^ (k - 1) * (3 : ℤ) ^ k = (3 : ℤ) ^ (2 * k - 1) := by
      have : (k - 1) + k = 2 * k - 1 := by omega
      rw [← pow_add, this]
    have : p ^ 3 = (3 : ℤ) ^ (k - 1) * n0Resid (k - 1) p := by
      simpa [n0Resid] using hde'
    rw [this, ht, ← mul_assoc, hshape]
  have : (3 : ℤ) ^ (2 * k - 1) ∣ p ^ 3 := ⟨t, hprod⟩
  have hcu := three_pow_dvd_cube (2 * k - 1) p this
  have : (2 * k - 1 + 2) / 3 = zeroExp k := by
    unfold zeroExp
    omega
  simpa [this] using hcu

theorem deepest_equiv_iff {k : ℕ} (hk : 1 ≤ k) (p q : ℤ) :
    ((3 : ℤ) ^ k ∣ n1Resid (k - 1) p - n1Resid (k - 1) q) ∧
        ((3 : ℤ) ^ k ∣ n0Resid (k - 1) p - n0Resid (k - 1) q) ↔
      ((3 : ℤ) ^ (k - 1) ∣ p ^ 2 - q ^ 2) ∧
        ((3 : ℤ) ^ k ∣ n0Resid (k - 1) p - n0Resid (k - 1) q) := by
  constructor
  · intro ⟨h1, h0⟩
    exact ⟨(deepest_n1_iff hk p q).1 h1, h0⟩
  · intro ⟨h1, h0⟩
    exact ⟨(deepest_n1_iff hk p q).2 h1, h0⟩

theorem sign_deepest {k : ℕ} (hk : 1 ≤ k) (p : ℤ) :
    ((3 : ℤ) ^ k ∣ n1Resid (k - 1) p - n1Resid (k - 1) (-p)) ∧
        ((3 : ℤ) ^ k ∣ n0Resid (k - 1) p - n0Resid (k - 1) (-p)) ↔
      (3 : ℤ) ^ k ∣ n0Resid (k - 1) p := by
  constructor
  · intro ⟨_, h0⟩
    exact (sign_n0 (k := k) (m := k - 1) (p := p)).1 h0
  · intro h0
    refine ⟨?_, (sign_n0 (k := k) (m := k - 1) (p := p)).2 h0⟩
    refine (deepest_n1_iff hk p (-p)).2 ?_
    simp [sq_factor]

end BTCalculus
