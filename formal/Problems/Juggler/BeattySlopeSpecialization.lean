import Problems.Juggler.BeattySlopeWords
import Problems.Juggler.BeattySurvivorProfile

/-!
# Recovering the original counts from the real-boundary model

Logarithms identify the power comparison with the real linear boundary.
The general word sets therefore specialize exactly, at every finite length,
to the original survivor and minimal-certificate sets. Irrationality is
proved independently of the counting identity, so this bridge introduces
no circular dependency when the original identity uses its general version.
-/

namespace Problems.Juggler.BeattySlope

open Finset PaperBThreshold PaperBCertificates

private theorem power_gap_iff (n k : ℕ) :
    (3 : ℕ)^k < 2^n ↔ (k : ℝ) < n*beta := by
  have hcast : ((3 : ℕ)^k < 2^n) ↔ ((3 : ℝ)^k < 2^n) := by
    exact_mod_cast Iff.rfl
  rw [hcast, ← Real.log_lt_log_iff (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, PaperBThreshold.beta, ← mul_div_assoc,
    lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))]

/-- Being below the logarithmic boundary is exactly the original strict
comparison of powers of three and two. -/
theorem below_logarithmic_iff (w : List Branch) : Below beta w ↔ exponentGap w := by
  simpa [Below, exponentGap, mul_comm] using (power_gap_iff w.length (oddCount w)).symm

private theorem prefix_iff (w : List Branch) (k : ℕ) (hk : k ≤ w.length) :
    beta*k ≤ (oddCount (w.take k) : ℝ) ↔ ¬ exponentGap (w.take k) := by
  rw [← below_logarithmic_iff, Below, List.length_take, Nat.min_eq_left hk, not_lt]

/-- The real-boundary survivor predicate recovers the original prefix predicate. -/
theorem survives_logarithmic_iff (w : List Branch) :
    Survives beta w ↔ prefixNoncontracting w := by
  constructor
  · intro h k hk
    exact (prefix_iff w k hk).1 (h k hk)
  · intro h k hk
    exact (prefix_iff w k hk).2 (h k hk)

/-- The real-boundary first-passage predicate recovers minimal certificates. -/
theorem firstPassage_logarithmic_iff (w : List Branch) :
    FirstPassage beta w ↔ IsMinimalCertificate w := by
  constructor
  · rintro ⟨hw, hg, hp⟩
    exact ⟨hw, (below_logarithmic_iff w).1 hg,
      fun k hk hkl => (prefix_iff w k hkl.le).1 (hp k hk hkl)⟩
  · rintro ⟨hw, hg, hp⟩
    exact ⟨hw, (below_logarithmic_iff w).2 hg,
      fun k hk hkl => (prefix_iff w k hkl.le).2 (hp k hk hkl)⟩

/-- Equality of the actual finite survivor sets at the logarithmic parameter. -/
theorem survivorWords_logarithmic (n : ℕ) : survivorWords beta n = neverNegWords n := by
  classical
  ext w
  simp only [survivorWords, neverNegWords, mem_filter, survives_logarithmic_iff]

/-- Equality of the actual finite first-passage sets at the logarithmic parameter. -/
theorem passageWords_logarithmic (n : ℕ) : passageWords beta n = minimalCertWords n := by
  classical
  ext w
  simp only [passageWords, minimalCertWords, mem_filter, firstPassage_logarithmic_iff]

/-- The parameterized integer survivor count is exactly the existing count. -/
theorem survivorCount_logarithmic (n : ℕ) : survivorCount beta n = neverNegCount n := by
  rw [survivorCount, survivorWords_logarithmic, neverNegCount]

/-- The parameterized integer first-passage count is exactly the existing count. -/
theorem passageCount_logarithmic (n : ℕ) : passageCount beta n = minimalCertCount n := by
  rw [passageCount, passageWords_logarithmic, minimalCertCount]

/-- The parameterized strict endpoint count agrees with the old endpoint count. -/
theorem endpointCount_logarithmic (n : ℕ) : endpointCount beta n = BeattyPhase.endpointCount n := rfl

private theorem logarithmic_mul_ne_nat {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (n : ℝ)*beta ≠ k := by
  intro he
  have hl : Real.log ((2 : ℝ)^n) = Real.log ((3 : ℝ)^k) := by
    rw [Real.log_pow, Real.log_pow]
    have h3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    dsimp [PaperBThreshold.beta] at he
    field_simp at he
    simpa [mul_comm] using he
  have heq : (2 : ℕ)^n = 3^k := by
    exact_mod_cast (Real.log_injOn_pos (show (0 : ℝ) < 2^n by positivity)
      (show (0 : ℝ) < 3^k by positivity) hl)
  exact two_pow_ne_three_pow hn heq

/-- Irrationality of the logarithmic boundary, proved directly from distinct
powers of two and three, without the survivor counting theorem. -/
theorem logarithmic_irrational : Irrational beta := by
  rintro ⟨q, hq⟩
  have hq0 : (0 : ℚ) ≤ q := by
    exact_mod_cast (show (0 : ℝ) ≤ (q : ℝ) by rw [hq]; linarith [beta_gt_five_eighths])
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have he : (q.den : ℝ)*beta = (q.num.toNat : ℝ) := by
    rw [← hq, Rat.cast_def]
    have he' : (q.num.toNat : ℝ) = (q.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    rw [he']
    field_simp
  exact logarithmic_mul_ne_nat q.pos q.num.toNat he

end Problems.Juggler.BeattySlope
