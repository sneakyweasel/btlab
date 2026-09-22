import Problems.Engine.ControlObstruction
import Problems.Engine.ControlWord
import Problems.Engine.ParameterDomain

namespace Problems.Engine

/-!
Generic accelerated (mx+r) identities. These are KNOWN integer
arithmetic specializations of the Engine lemmas. They are not map
theorems on the odd positives and not Collatz convergence results.
-/

/-- Exact exponent selection for the cleared relation ``2^k y = m x + r``. -/
theorem mxPlusR_parameter_iff
    {m r x : ℤ} {k : ℕ} (hq : m * x + r ≠ 0) :
    (∃ y : ℤ, (2 : ℤ) ^ k * y = m * x + r ∧ ¬ (2 : ℤ) ∣ y) ↔
      padicValInt 2 (m * x + r) = k :=
  mul_pow_eq_iff_padicValInt (b := 2) hq

/-- Two certified one-step clearing relations compose. -/
theorem mxPlusR_compose_two
    {m r : ℤ} {k0 k1 : ℕ} {x0 x1 x2 : ℤ}
    (h0 : (2 : ℤ) ^ k0 * x1 = m * x0 + r)
    (h1 : (2 : ℤ) ^ k1 * x2 = m * x1 + r) :
    (2 : ℤ) ^ k0 * (2 : ℤ) ^ k1 * x2 =
      m * m * x0 + (m * r + (2 : ℤ) ^ k0 * r) :=
  compose_two_affine h0 h1

/-- Length-one cycle constraint implies a divisibility condition. -/
theorem mxPlusR_len_one_cycle_dvd {m r : ℤ} {k : ℕ} {x : ℤ}
    (h : (2 : ℤ) ^ k * x = m * x + r) :
    ((2 : ℤ) ^ k - m) ∣ r :=
  cycle_constraint_dvd h

/-!
7-specific image arithmetic for the cleared relation ``2^k y = 7 x + 1``.
These identities are elementary. They are not a basin theorem for
reaching 1 and not a divergence theorem.
-/

/-- The odd part of ``7x+1`` is never divisible by 7. -/
theorem mxPlusR_seven_not_dvd_image {x y : ℤ} {k : ℕ}
    (h : (2 : ℤ) ^ k * y = 7 * x + 1) :
    ¬ (7 : ℤ) ∣ y := by
  intro hd
  have hmul : (7 : ℤ) ∣ (2 : ℤ) ^ k * y := dvd_mul_of_dvd_right hd _
  have h71 : (7 : ℤ) ∣ 7 * x + 1 := by rwa [h] at hmul
  have hone : (7 : ℤ) ∣ 1 := (dvd_add_right (dvd_mul_right (7 : ℤ) x)).1 h71
  exact (by decide : ¬ (7 : ℤ) ∣ (1 : ℤ)) hone

/-- The cleared relation is ``2^k y ≡ 1 (mod 7)``. -/
theorem mxPlusR_seven_two_pow_mul_modEq_one {x y : ℤ} {k : ℕ}
    (h : (2 : ℤ) ^ k * y = 7 * x + 1) :
    (2 : ℤ) ^ k * y ≡ 1 [ZMOD 7] := by
  refine (Int.modEq_iff_dvd).2 ?_
  have hxeq : (1 : ℤ) - (2 : ℤ) ^ k * y = 7 * (-x) := by linarith
  exact ⟨-x, hxeq⟩

lemma two_pow_three_modEq_one_mod_seven : (2 : ℤ) ^ 3 ≡ 1 [ZMOD 7] := by
  decide

lemma two_pow_modEq_mod_three_mod_seven (k : ℕ) :
    (2 : ℤ) ^ k ≡ (2 : ℤ) ^ (k % 3) [ZMOD 7] := by
  nth_rw 1 [show k = 3 * (k / 3) + k % 3 from (Nat.div_add_mod k 3).symm]
  rw [pow_add, pow_mul]
  have hpow : ((2 : ℤ) ^ 3) ^ (k / 3) ≡ (1 : ℤ) ^ (k / 3) [ZMOD 7] :=
    two_pow_three_modEq_one_mod_seven.pow _
  have h1 : ((2 : ℤ) ^ 3) ^ (k / 3) ≡ 1 [ZMOD 7] := by
    simpa using hpow
  simpa using h1.mul (.refl ((2 : ℤ) ^ (k % 3)))

/-- Powers of 2 modulo 7 lie in the subgroup ``{1,2,4}``. -/
theorem two_pow_mod_seven (k : ℕ) :
    (2 : ℤ) ^ k ≡ 1 [ZMOD 7] ∨ (2 : ℤ) ^ k ≡ 2 [ZMOD 7] ∨
      (2 : ℤ) ^ k ≡ 4 [ZMOD 7] := by
  have h := two_pow_modEq_mod_three_mod_seven k
  have : k % 3 < 3 := Nat.mod_lt k (by decide : 0 < 3)
  interval_cases hrem : k % 3
  · left
    simpa [hrem] using h
  · right; left
    simpa [hrem] using h
  · right; right
    simpa [hrem] using h

private lemma eight_modEq_one_mod_seven : (8 : ℤ) ≡ 1 [ZMOD 7] := by
  decide

/-- After one accelerated 7x+1 step, the odd part is ``≡ 1, 2, or 4 (mod 7)``. -/
theorem mxPlusR_seven_image_residue {x y : ℤ} {k : ℕ}
    (h : (2 : ℤ) ^ k * y = 7 * x + 1) :
    y ≡ 1 [ZMOD 7] ∨ y ≡ 2 [ZMOD 7] ∨ y ≡ 4 [ZMOD 7] := by
  have hm : (2 : ℤ) ^ k * y ≡ 1 [ZMOD 7] := mxPlusR_seven_two_pow_mul_modEq_one h
  rcases two_pow_mod_seven k with h1 | h2 | h4
  · left
    have : (1 : ℤ) * y ≡ 1 [ZMOD 7] := (h1.symm.mul (.refl y)).trans hm
    simpa using this
  · right; right
    have h2y : (2 : ℤ) * y ≡ 1 [ZMOD 7] := (h2.symm.mul (.refl y)).trans hm
    have h8y : (8 : ℤ) * y ≡ 4 [ZMOD 7] := by
      have hmul := h2y.mul_left (4 : ℤ)
      have : (4 : ℤ) * (2 * y) = 8 * y := by ring
      rwa [this] at hmul
    have : (1 : ℤ) * y ≡ 4 [ZMOD 7] :=
      (eight_modEq_one_mod_seven.symm.mul (.refl y)).trans h8y
    simpa using this
  · right; left
    have h4y : (4 : ℤ) * y ≡ 1 [ZMOD 7] := (h4.symm.mul (.refl y)).trans hm
    have h8y : (8 : ℤ) * y ≡ 2 [ZMOD 7] := by
      have hmul := h4y.mul_left (2 : ℤ)
      have : (2 : ℤ) * (4 * y) = 8 * y := by ring
      rwa [this] at hmul
    have : (1 : ℤ) * y ≡ 2 [ZMOD 7] :=
      (eight_modEq_one_mod_seven.symm.mul (.refl y)).trans h8y
    simpa using this

/-- The only positive length-one cycle of ``T_{7,1}`` is the fixed point ``1``. -/
theorem mxPlusR_seven_len_one_cycle {k : ℕ} {x : ℤ}
    (hx : 0 < x) (h : (2 : ℤ) ^ k * x = 7 * x + 1) :
    k = 3 ∧ x = 1 := by
  have hmul : ((2 : ℤ) ^ k - 7) * x = 1 := by
    calc
      ((2 : ℤ) ^ k - 7) * x = (2 : ℤ) ^ k * x - 7 * x := by ring
      _ = 1 := by linarith
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with (⟨ha, hxx⟩ | ⟨ha, hxx⟩)
  · refine ⟨?_, hxx⟩
    have h8 : (2 : ℤ) ^ k = 8 := by linarith
    by_cases hk : k ≤ 3
    · interval_cases k
      · cases h8
      · cases h8
      · cases h8
      · rfl
    · have hk4 : 4 ≤ k := by omega
      have hle : (2 : ℤ) ^ 4 ≤ (2 : ℤ) ^ k :=
        pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) hk4
      have hle16 : (16 : ℤ) ≤ 8 := by
        have : (2 : ℤ) ^ 4 = 16 := by norm_num
        linarith
      have hfalse : ¬ (16 : ℤ) ≤ 8 := by decide
      exact absurd hle16 hfalse
  · have hxneg : x = -1 := hxx
    exact absurd hx (by linarith)

/-- ``73 ≡ 3 (mod 7)`` maps to 1 in one step. Not a basin obstruction. -/
theorem mxPlusR_seven_one_from_seventy_three :
    (2 : ℤ) ^ 9 * (1 : ℤ) = 7 * 73 + 1 := by
  decide

theorem mxPlusR_seventy_three_mod_seven : (73 : ℤ) % 7 = 3 := by
  decide

/-- ``299593 ≡ 0 (mod 7)`` maps to 1 in one step. Not a basin obstruction. -/
theorem mxPlusR_seven_one_from_multiple_of_seven :
    (2 : ℤ) ^ 21 * (1 : ℤ) = 7 * 299593 + 1 := by
  decide

theorem mxPlusR_multiple_of_seven_mod_seven : (299593 : ℤ) % 7 = 0 := by
  decide

end Problems.Engine
