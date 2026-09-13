import Problems.Juggler.FateTaoReduction

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# Corollary 8.4: the conjecture from a cylinder bound

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Corollary 8.4, as the composition
of two theorems already in the corpus.

`oddFailures_card_le_explicit` (Theorem 8.3, explicit form) says that under the cylinder
hypothesis `H(C, A)` at a scale `y`, the odd failures in `(y, 2y]` number at most
`y Λ^{-e(C)} + 2 Λ^C y (log y)^{-A}` with `Λ = log 2y / log N₀`. The Tao-type reduction
`tao_rate_implies_conjecture` (Theorem 7.2, with the contagion bound of Theorem 5.3 as its
hypothesis) needs `y (log y)^{-e}` for all large `y` with `e > 1 - λ`. The step between
them is the absorption the paper does in one line: for `A > C + e(C)` and any `e < e(C)`,
the explicit bound is below `y (log y)^{-e}` once `log y` is large, because
`Λ ≥ log y / log N₀` makes the first term `(log N₀)^{e(C)} y (log y)^{-e(C)}` and
`Λ ≤ 2 log y / log N₀` makes the second `2 (2/log N₀)^C y (log y)^{C - A}`, and both exponent
gaps `e(C) - e` and `A - C - e` are positive. `oddFailures_eventually_le` is that step, with
the threshold from `exists_rpow_gt`; `cylinder_bound_implies_conjecture` is Corollary 8.4.

What is kept as a hypothesis: the contagion bound (Theorem 5.3, the analytic core of the
paper) with an exponent `λ` satisfying `1 - λ < e(C)`. The paper's numerical form,
`C ≥ 19` because `e(19) = 0.527 > 0.5074 = 1 - λ**`, is a statement about the root `λ**`
and is not formalized; `paper_c_audit` checks it numerically. Not a halt theorem: nothing
here proves the cylinder bound.
-/

/-- The cylinder hypothesis `H(C, A)` at the scale `y`: every `O`-rooted `L(y)`-bad cylinder
of depth `d(y) = ⌈C L(y)⌉` holds at most `2^{-(d-1)} y/2 + y (log y)^{-A}` starts. -/
def CylinderBound (N₀ : ℕ) (C A : ℝ) (y : ℕ) : Prop :=
  ∀ w ∈ allWords (depth C N₀ y), w.head? = some .odd → LBad (scaleL N₀ y) w →
    ((cylinder y (depth C N₀ y) w).card : ℝ) ≤
      2 ^ (-((depth C N₀ y : ℝ) - 1)) * y / 2 + y / Real.log y ^ A

/-- The depth is positive as soon as `2y > N₀`. -/
theorem one_le_depth {N₀ y : ℕ} (hN : 2 ≤ N₀) (hy : N₀ < 2 * y) {C : ℝ} (hC : 0 < C) :
    1 ≤ depth C N₀ y := by
  unfold depth scaleL scaleRatio
  rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
  apply mul_pos hC
  apply Real.logb_pos (by norm_num)
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N₀))
  rw [one_lt_div hlogN]
  apply Real.log_lt_log (by positivity)
  exact_mod_cast hy

/-- `e(C) ≥ 0` for `C ≥ 5`. -/
theorem chernoffExponent_nonneg {C : ℝ} (hC : 5 ≤ C) : 0 ≤ chernoffExponent C := by
  unfold chernoffExponent
  have := klHalf_nonneg (pC C) (by linarith [half_le_pC C hC]) (pC_lt_one C hC)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- **The absorption.** Under `H(C, A)` at all large scales, with `A > C + e(C)`, the odd
failures in `(y, 2y]` number at most `y (log y)^{-e}` for every `e < e(C)` and all large `y`. -/
theorem oddFailures_eventually_le {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C A e : ℝ) (hC : 5 ≤ C)
    (hA : C + chernoffExponent C < A) (he : e < chernoffExponent C)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ C A y) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y → ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e) := by
  obtain ⟨y₁, hy₁⟩ := hcyl
  set eC := chernoffExponent C with heCdef
  have heC0 : 0 ≤ eC := chernoffExponent_nonneg hC
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N₀))
  have hδ₁ : 0 < eC - e := by linarith
  have hδ₂ : 0 < A - C - e := by linarith
  set LN := Real.log N₀ ^ eC with hLN
  set M := (2 / Real.log N₀) ^ C with hM
  have hLN0 : 0 < LN := Real.rpow_pos_of_pos hlogN _
  have hM0 : 0 < M := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨u₁, -, hu₁⟩ := exists_rpow_gt hδ₁ (2 * LN)
  obtain ⟨u₂, -, hu₂⟩ := exists_rpow_gt hδ₂ (4 * M)
  refine ⟨max (max y₁ N₀) (max 2 ⌈Real.exp (max u₁ u₂)⌉₊), ?_⟩
  intro y hy
  have hyy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyN : N₀ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy2 : 2 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hyexp : Real.exp (max u₁ u₂) ≤ y := by
    have h1 : ⌈Real.exp (max u₁ u₂)⌉₊ ≤ y :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlogy_ge : max u₁ u₂ ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]; exact hyexp
  have hK₁ : 2 * LN < Real.log y ^ (eC - e) :=
    hu₁ _ (le_trans (le_max_left _ _) hlogy_ge)
  have hK₂ : 4 * M < Real.log y ^ (A - C - e) :=
    hu₂ _ (le_trans (le_max_right _ _) hlogy_ge)
  -- the explicit bound of Theorem 8.3 at this scale
  have hd1 : 1 ≤ depth C N₀ y := one_le_depth hN (by omega) (by linarith)
  have hmain := oddFailures_card_le_explicit hN hfloor y hy2 C A hC hd1 (hy₁ y hyy₁)
  -- `log y / log N₀ ≤ Λ ≤ 2 log y / log N₀`
  set Λ := scaleRatio N₀ y with hΛ
  have hΛdef : Λ = Real.log (2 * y) / Real.log N₀ := rfl
  have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
    Real.log_mul (by norm_num) hy0.ne'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by exact_mod_cast hy2)
  have hΛlo : Real.log y / Real.log N₀ ≤ Λ := by
    rw [hΛdef, hlog2y]
    apply div_le_div_of_nonneg_right _ hlogN.le
    linarith
  have hΛhi : Λ ≤ 2 * Real.log y / Real.log N₀ := by
    rw [hΛdef, hlog2y]
    apply div_le_div_of_nonneg_right _ hlogN.le
    linarith
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛlo
  -- the atoms
  set P := Real.log y ^ (-e) with hP
  set Q₁ := Real.log y ^ (-(eC - e)) with hQ₁
  set Q₂ := Real.log y ^ (-(A - C - e)) with hQ₂
  have hP0 : 0 ≤ P := Real.rpow_nonneg hlogy.le _
  have hQ₁0 : 0 ≤ Q₁ := Real.rpow_nonneg hlogy.le _
  have hQ₂0 : 0 ≤ Q₂ := Real.rpow_nonneg hlogy.le _
  have hQ₁le : Q₁ ≤ 1 / (2 * LN) := by
    rw [hQ₁, Real.rpow_neg hlogy.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hK₁.le
  have hQ₂le : Q₂ ≤ 1 / (4 * M) := by
    rw [hQ₂, Real.rpow_neg hlogy.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hK₂.le
  -- term 1: `Λ^{-e(C)} ≤ LN · P · Q₁`
  have hT1 : Λ ^ (-eC) ≤ LN * (P * Q₁) := by
    have h1 : Λ ^ (-eC) ≤ (Real.log y / Real.log N₀) ^ (-eC) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hΛlo (by linarith)
    have h2 : (Real.log y / Real.log N₀) ^ (-eC) = Real.log y ^ (-eC) * LN := by
      rw [Real.div_rpow hlogy.le hlogN.le, Real.rpow_neg hlogN.le, div_inv_eq_mul]
    have h3 : Real.log y ^ (-eC) = P * Q₁ := by
      rw [hP, hQ₁, ← Real.rpow_add hlogy]
      congr 1
      ring
    rw [h2, h3] at h1
    linarith
  -- term 2: `Λ^C / (log y)^A ≤ M · P · Q₂`
  have hT2 : Λ ^ C / Real.log y ^ A ≤ M * (P * Q₂) := by
    have h1 : Λ ^ C ≤ (2 * Real.log y / Real.log N₀) ^ C :=
      Real.rpow_le_rpow hΛpos.le hΛhi (by linarith)
    have h2 : (2 * Real.log y / Real.log N₀) ^ C = M * Real.log y ^ C := by
      rw [show 2 * Real.log y / Real.log N₀ = (2 / Real.log N₀) * Real.log y by ring,
        Real.mul_rpow (by positivity) hlogy.le]
    have h3 : Real.log y ^ C / Real.log y ^ A = P * Q₂ := by
      rw [hP, hQ₂, ← Real.rpow_sub hlogy, ← Real.rpow_add hlogy]
      congr 1
      ring
    have hA0 : 0 < Real.log y ^ A := Real.rpow_pos_of_pos hlogy _
    calc Λ ^ C / Real.log y ^ A ≤ M * Real.log y ^ C / Real.log y ^ A := by
          rw [← h2]
          exact div_le_div_of_nonneg_right h1 hA0.le
      _ = M * (Real.log y ^ C / Real.log y ^ A) := by ring
      _ = M * (P * Q₂) := by rw [h3]
  -- assemble: each term is at most `y P / 2`
  have hterm1 : y * Λ ^ (-eC) ≤ y * P / 2 := by
    calc (y : ℝ) * Λ ^ (-eC) ≤ y * (LN * (P * Q₁)) :=
          mul_le_mul_of_nonneg_left hT1 hy0.le
      _ ≤ y * (LN * (P * (1 / (2 * LN)))) := by
          apply mul_le_mul_of_nonneg_left _ hy0.le
          apply mul_le_mul_of_nonneg_left _ hLN0.le
          exact mul_le_mul_of_nonneg_left hQ₁le hP0
      _ = y * P / 2 := by
          field_simp
  have hterm2 : 2 * Λ ^ C * y / Real.log y ^ A ≤ y * P / 2 := by
    calc 2 * Λ ^ C * y / Real.log y ^ A = 2 * y * (Λ ^ C / Real.log y ^ A) := by ring
      _ ≤ 2 * y * (M * (P * Q₂)) :=
          mul_le_mul_of_nonneg_left hT2 (by positivity)
      _ ≤ 2 * y * (M * (P * (1 / (4 * M)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hM0.le
          exact mul_le_mul_of_nonneg_left hQ₂le hP0
      _ = y * P / 2 := by
          field_simp
          ring
  calc ((oddFailures y).card : ℝ)
      ≤ y * Λ ^ (-eC) + 2 * Λ ^ C * y / Real.log y ^ A := hmain
    _ ≤ y * P / 2 + y * P / 2 := add_le_add hterm1 hterm2
    _ = y * Real.log y ^ (-e) := by rw [hP]; ring

/-- **Corollary 8.4.** If the cylinder hypothesis `H(C, A)` holds at all large scales with
`C ≥ 5` and `A > C + e(C)`, and the contagion bound of Theorem 5.3 holds for the failure
set with an exponent `λ` satisfying `1 - λ < e(C)`, then every positive integer reaches `1`. -/
theorem cylinder_bound_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C A : ℝ) (hC : 5 ≤ C)
    (hA : C + chernoffExponent C < A)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ C A y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < chernoffExponent C)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) → ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  set e := (1 - lam + chernoffExponent C) / 2 with he
  have he1 : 1 - lam < e := by rw [he]; linarith
  have he2 : e < chernoffExponent C := by rw [he]; linarith
  exact tao_rate_implies_conjecture hlam0 hlam1 he1 hlow
    (oddFailures_eventually_le hN hfloor C A e hC hA he2 hcyl)

end Problems.Juggler
