import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-!
# A mean constraint on the signed strict-grid certificate

The three fertile parent classes and the three lifts of each child
enumerate the same table. Averaging its inequalities therefore gives
a necessary rate constraint at every finite level, independently of
the numerical search for weights.
-/
namespace Problems.Collatz.PreimageBalance

open scoped BigOperators

def affine {N : ℕ} (hN : 0 < N) (a b : ℕ) (i : Fin N) : Fin N :=
  ⟨(a * i.val + b) % N, Nat.mod_lt _ hN⟩

theorem affine_bijective {N : ℕ} (hN : 0 < N) (a b : ℕ)
    (ha : Nat.Coprime N a) : Function.Bijective (affine hN a b) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, rfl⟩
  intro i j hij
  have hm : a * i.val + b ≡ a * j.val + b [MOD N] := congrArg Fin.val hij
  have hc := Nat.ModEq.cancel_left_of_coprime ha (hm.add_right_cancel' b)
  exact Fin.ext (hc.eq_of_lt_of_lt i.isLt j.isLt)

def parent {M : ℕ} (j : Fin M) (r : Fin 3) : Fin (M * 3) :=
  finProdFinEquiv (j, r)

def lift {M : ℕ} (j : Fin M) (r : Fin 3) : Fin (M * 3) :=
  Fin.cast (Nat.mul_comm 3 M) (finProdFinEquiv (r, j))

theorem parent_val {M : ℕ} (j : Fin M) (r : Fin 3) :
    (parent j r).val = r.val + 3 * j.val := rfl

theorem lift_val {M : ℕ} (j : Fin M) (r : Fin 3) :
    (lift j r).val = j.val + M * r.val := rfl

def childWeight {M : ℕ} (w : Fin (M * 3) → ℝ) (j : Fin M) : ℝ :=
  min (w (lift j 0)) (min (w (lift j 1)) (w (lift j 2)))

theorem sum_parent {M : ℕ} (w : Fin (M * 3) → ℝ) :
    ∑ j : Fin M, ∑ r : Fin 3, w (parent j r) = ∑ i, w i := by
  simpa only [Fintype.sum_prod_type, parent] using finProdFinEquiv.sum_comp w

theorem sum_lift {M : ℕ} (w : Fin (M * 3) → ℝ) :
    ∑ j : Fin M, ∑ r : Fin 3, w (lift j r) = ∑ i, w i := by
  rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type, lift, Equiv.trans_apply, finCongr_apply] using
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm 3 M))).sum_comp w

theorem three_sum_child_le {M : ℕ} (w : Fin (M * 3) → ℝ) :
    3 * ∑ j : Fin M, childWeight w j ≤ ∑ i, w i := by
  rw [Finset.mul_sum, ← sum_lift w]
  apply Finset.sum_le_sum
  intro j _
  have h0 := min_le_left (w (lift j 0)) (min (w (lift j 1)) (w (lift j 2)))
  have h1 := (min_le_right (w (lift j 0)) (min (w (lift j 1)) (w (lift j 2)))).trans
    (min_le_left _ _)
  have h2 := (min_le_right (w (lift j 0)) (min (w (lift j 1)) (w (lift j 2)))).trans
    (min_le_right _ _)
  simp only [Fin.sum_univ_three, childWeight]
  linarith

/-- The normalized signed rows, in fertile-residue index `i=(m-1)/3`.
Parent `3j+r` has class `m=3r+1 mod 9`. Its fourfold index is
`4i+1`; the odd child indices are `2j` and `4j+3`, modulo `M`.
The minimum takes all three lifts back to the full table. -/
def Rows {M : ℕ} (hM : 0 < M) (A B C : ℝ) (w : Fin (M * 3) → ℝ) : Prop :=
  ∀ j : Fin M,
    w (parent j 0) ≤ A * w (affine (by omega) 4 1 (parent j 0)) +
      B * childWeight w (affine hM 2 0 j) ∧
    w (parent j 1) ≤ A * w (affine (by omega) 4 1 (parent j 1)) ∧
    w (parent j 2) ≤ A * w (affine (by omega) 4 1 (parent j 2)) +
      C * childWeight w (affine hM 4 3 j)

/-- Averaging only needs the three production maps to permute their tables. -/
theorem balanced_mean_bound {M : ℕ} (hM : 0 < M)
    (F : Fin (M*3) → Fin (M*3)) (O D : Fin M → Fin M)
    (hF : Function.Bijective F) (hO : Function.Bijective O) (hD : Function.Bijective D)
    {A B C : ℝ} {w : Fin (M * 3) → ℝ}
    (hw : ∀ i, 0 < w i) (hBC : 0 ≤ B + C)
    (hrow : ∀ j : Fin M,
      w (parent j 0) ≤ A * w (F (parent j 0)) + B * childWeight w (O j) ∧
      w (parent j 1) ≤ A * w (F (parent j 1)) ∧
      w (parent j 2) ≤ A * w (F (parent j 2)) + C * childWeight w (D j)) :
    1 ≤ A + (B + C) / 3 := by
  let S := ∑ i, w i
  let L := ∑ j : Fin M, childWeight w j
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro i _; exact hw i
    · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hL : 3 * L ≤ S := three_sum_child_le w
  have hsum : S ≤ A * S + (B + C) * L := by
    have hp := Finset.sum_le_sum (s := Finset.univ) (fun j (_ : j ∈ Finset.univ) =>
      add_le_add (add_le_add (hrow j).1 (hrow j).2.1) (hrow j).2.2)
    have hpar := sum_parent w
    have hfour := sum_parent (fun i => w (F i))
    rw [hF.sum_comp w] at hfour
    have ho := hO.sum_comp (childWeight w)
    have hd := hD.sum_comp (childWeight w)
    simp only [Fin.sum_univ_three] at hpar hfour
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hp hpar hfour
    rw [ho, hd] at hp
    have hf := congrArg (fun x : ℝ => A * x) hfour
    dsimp [S, L]
    nlinarith only [hp, hpar, hf]
  have hmul := mul_le_mul_of_nonneg_left hL hBC
  nlinarith

/-- A necessary mean bound for every finite minus-map residue certificate. -/
theorem mean_bound {M : ℕ} (hM : 0 < M)
    (h4 : Nat.Coprime (M * 3) 4) (h2 : Nat.Coprime M 2) (h4' : Nat.Coprime M 4)
    {A B C : ℝ} {w : Fin (M * 3) → ℝ}
    (hw : ∀ i, 0 < w i) (hBC : 0 ≤ B + C) (hrow : Rows hM A B C w) :
    1 ≤ A + (B + C) / 3 :=
  balanced_mean_bound hM _ _ _ (affine_bijective _ 4 1 h4)
    (affine_bijective hM 2 0 h2) (affine_bijective hM 4 3 h4') hw hBC hrow

/-- The plus-map indices use `m=3i+2`: the two odd productions exchange
parent classes, and their offsets change, but they are still permutations. -/
def RowsPlus {M : ℕ} (hM : 0 < M) (A B C : ℝ) (w : Fin (M * 3) → ℝ) : Prop :=
  ∀ j : Fin M,
    w (parent j 0) ≤ A * w (affine (by omega) 4 2 (parent j 0)) +
      C * childWeight w (affine hM 4 0 j) ∧
    w (parent j 1) ≤ A * w (affine (by omega) 4 2 (parent j 1)) ∧
    w (parent j 2) ≤ A * w (affine (by omega) 4 2 (parent j 2)) +
      B * childWeight w (affine hM 2 1 j)

theorem plus_mean_bound {M : ℕ} (hM : 0 < M)
    (h4 : Nat.Coprime (M * 3) 4) (h2 : Nat.Coprime M 2) (h4' : Nat.Coprime M 4)
    {A B C : ℝ} {w : Fin (M * 3) → ℝ}
    (hw : ∀ i, 0 < w i) (hBC : 0 ≤ B + C) (hrow : RowsPlus hM A B C w) :
    1 ≤ A + (B + C) / 3 := by
  have h := balanced_mean_bound hM _ _ _ (affine_bijective _ 4 2 h4)
    (affine_bijective hM 4 0 h4') (affine_bijective hM 2 1 h2) hw
    (by simpa only [add_comm] using hBC) hrow
  simpa only [add_comm] using h

/-- One shared necessary inequality for all levels `k+2` of the grid. -/
theorem power_three_mean_bound (k : ℕ) {A B C : ℝ}
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i)
    (hBC : 0 ≤ B + C) (hrow : Rows (by positivity : 0 < 3^k) A B C w) :
    1 ≤ A + (B + C) / 3 := by
  apply mean_bound (by positivity) _ _ _ hw hBC hrow
  · rw [← pow_succ]
    exact (by decide : Nat.Coprime 3 4).pow_left _
  · exact (by decide : Nat.Coprime 3 2).pow_left _
  · exact (by decide : Nat.Coprime 3 4).pow_left _

theorem power_three_plus_mean_bound (k : ℕ) {A B C : ℝ}
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i)
    (hBC : 0 ≤ B + C) (hrow : RowsPlus (by positivity : 0 < 3^k) A B C w) :
    1 ≤ A + (B + C) / 3 := by
  apply plus_mean_bound (by positivity) _ _ _ hw hBC hrow
  · rw [← pow_succ]
    exact (by decide : Nat.Coprime 3 4).pow_left _
  · exact (by decide : Nat.Coprime 3 2).pow_left _
  · exact (by decide : Nat.Coprime 3 4).pow_left _

noncomputable def meanFactor (μ : ℝ) : ℝ := μ ^ (-100 : ℤ) +
  (μ ^ (-21 : ℤ) + μ ^ (29 : ℤ)) / 3

theorem strict_grid_mean (k : ℕ) {μ : ℝ} (hμ : 0 < μ)
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i)
    (hrow : Rows (by positivity : 0 < 3^k)
      (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w) :
    1 ≤ meanFactor μ := by
  have h := power_three_mean_bound k hw (by positivity) hrow
  simpa [meanFactor, add_comm] using h

theorem strict_grid_plus_mean (k : ℕ) {μ : ℝ} (hμ : 0 < μ)
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i)
    (hrow : RowsPlus (by positivity : 0 < 3^k)
      (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w) :
    1 ≤ meanFactor μ := by
  have h := power_three_plus_mean_bound k hw (by positivity) hrow
  simpa [meanFactor, add_comm] using h

theorem cleared_mean_bound {μ : ℝ} (hμ : 0 < μ) (h : 1 ≤ meanFactor μ) :
    3 * μ^100 ≤ 3 + μ^129 + μ^79 := by
  have he : meanFactor μ * (3 * μ^100) = 3 + μ^129 + μ^79 := by
    simp only [meanFactor, zpow_neg]
    field_simp
    ring
  have hm := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 3 * μ^100)
  simpa only [one_mul, he] using hm

theorem grid_rounding_gap : (2 : ℝ)^79 < (3 : ℝ)^50 := by norm_num

/-- At the harmonic rate, the mean condition would reverse precisely
the strict `79/50 < log₂ 3` slack used by this cap grid. -/
theorem harmonic_mean_lt {μ : ℝ} (hμ : 0 < μ) (hpow : μ^50 = 2) :
    meanFactor μ < 1 := by
  by_contra! hm
  have hc := cleared_mean_bound hμ hm
  have h100 : μ^100 = 4 := by
    calc μ^100 = (μ^50)^2 := by ring
      _ = 4 := by rw [hpow]; norm_num
  have h129 : μ^129 = 2 * μ^79 := by
    calc μ^129 = μ^79 * μ^50 := by ring
      _ = 2 * μ^79 := by rw [hpow]; ring
  have h79 : (3 : ℝ) ≤ μ^79 := by rw [h100, h129] at hc; linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h79 50
  have he : (μ^79)^50 = (2 : ℝ)^79 := by
    rw [← pow_mul, Nat.mul_comm 79 50, pow_mul, hpow]
  rw [he] at hp
  linarith [grid_rounding_gap]

theorem meanFactor_convex : ConvexOn ℝ (Set.Ioi 0) meanFactor := by
  have h : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ (-21 : ℤ) + x ^ (29 : ℤ)) :=
    (convexOn_zpow (-21)).add (convexOn_zpow 29)
  change ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x^(-100 : ℤ) +
    (x^(-21 : ℤ) + x^(29 : ℤ)) / 3)
  simpa only [Pi.add_def, div_eq_mul_inv, smul_eq_mul, mul_comm, one_mul] using
    (convexOn_zpow (-100)).add (ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 1 / 3) h)

theorem endpoint_bounds : meanFactor (5069/5000) < 1 ∧ meanFactor (507/500) < 1 := by
  norm_num [meanFactor]

theorem meanFactor_lt_of_mem_rate_interval {μ : ℝ}
    (hlo : 5069/5000 ≤ μ) (hhi : μ ≤ 507/500) : meanFactor μ < 1 := by
  have h := meanFactor_convex.le_max_of_mem_Icc
    (by norm_num : (0 : ℝ) < 5069/5000) (by norm_num : (0 : ℝ) < 507/500) ⟨hlo, hhi⟩
  exact h.trans_lt (max_lt endpoint_bounds.1 endpoint_bounds.2)

/-- A table of any size fails throughout this interval of rational-grid rates. -/
theorem no_rows_in_rate_interval (k : ℕ) {μ : ℝ}
    (hlo : 5069/5000 ≤ μ) (hhi : μ ≤ 507/500)
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i) :
    ¬ Rows (by positivity : 0 < 3^k)
      (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w := by
  intro hr
  have hlo' : (0 : ℝ) < 5069/5000 := by norm_num
  have hhi' : (0 : ℝ) < 507/500 := by norm_num
  have h := meanFactor_convex.le_max_of_mem_Icc hlo' hhi' ⟨hlo, hhi⟩
  have hg := strict_grid_mean k (lt_of_lt_of_le hlo' hlo) hw hr
  have he := endpoint_bounds
  exact (not_le_of_gt (h.trans_lt (max_lt he.1 he.2))) hg

theorem rate_upper_pow : (2 : ℝ) < (507/500 : ℝ)^50 := by norm_num

theorem rate_lower_pow : (5069/5000 : ℝ)^50 < 2 := by norm_num

set_option exponentiation.threshold 6000 in
theorem rate_power_ceiling : (5069/5000 : ℝ)^5000 < (2 : ℝ)^99 := by norm_num

theorem rate_lt_of_mean {μ : ℝ} (hlinear : μ^50 ≤ 2) (hmean : 1 ≤ meanFactor μ) :
    μ < 5069/5000 := by
  by_contra! hlo
  have hhi : μ ≤ 507/500 := by
    by_contra! hh
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 507/500) hh.le 50
    linarith [rate_upper_pow]
  exact (not_le_of_gt (meanFactor_lt_of_mem_rate_interval hlo hhi)) hmean

/-- Among rates compatible with at-most-linear counts, every finite level
has rate strictly below `5069/5000`, whose diagnostic exponent is 0.988653... . -/
theorem rate_lt_of_rows (k : ℕ) {μ : ℝ} (hlinear : μ^50 ≤ 2)
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i)
    (hrow : Rows (by positivity : 0 < 3^k)
      (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w) :
    μ < 5069/5000 := by
  by_contra! hlo
  have hhi : μ ≤ 507/500 := by
    by_contra! hh
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 507/500) hh.le 50
    linarith [rate_upper_pow]
  exact no_rows_in_rate_interval k hlo hhi hw hrow

theorem rate_lt_of_plus_rows (k : ℕ) {μ : ℝ} (hμ : 0 < μ) (hlinear : μ^50 ≤ 2)
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i)
    (hrow : RowsPlus (by positivity : 0 < 3^k)
      (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w) :
    μ < 5069/5000 :=
  rate_lt_of_mean hlinear (strict_grid_plus_mean k hμ hw hrow)

/-- Neither sign can reach the harmonic exponent with this fixed cap grid. -/
theorem harmonic_rate_excluded (k : ℕ) {μ : ℝ} (hμ : 0 < μ) (hpow : μ^50 = 2)
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i) :
    ¬ (Rows (by positivity : 0 < 3^k)
        (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w ∨
      RowsPlus (by positivity : 0 < 3^k)
        (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w) := by
  intro hr
  have hm : 1 ≤ meanFactor μ := by
    rcases hr with h | h
    · exact strict_grid_mean k hμ hw h
    · exact strict_grid_plus_mean k hμ hw h
  exact (not_le_of_gt (harmonic_mean_lt hμ hpow)) hm

/-- An exact rational-exponent version of the common sublinear ceiling. -/
theorem certificate_power_ceiling (k : ℕ) {μ : ℝ} (hμ : 0 < μ) (hlinear : μ^50 ≤ 2)
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i)
    (hr : Rows (by positivity : 0 < 3^k)
        (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w ∨
      RowsPlus (by positivity : 0 < 3^k)
        (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w) :
    μ^5000 < (2 : ℝ)^99 := by
  have hm : 1 ≤ meanFactor μ := by
    rcases hr with h | h
    · exact strict_grid_mean k hμ hw h
    · exact strict_grid_plus_mean k hμ hw h
  have hlt := rate_lt_of_mean hlinear hm
  exact (pow_le_pow_left₀ hμ.le hlt.le 5000).trans_lt rate_power_ceiling

/-- Exact numerator/index calculations for both signs, before reduction
modulo the table size. They identify the affine permutations used above. -/
theorem signed_index_formulas (i j : ℕ) :
    4*(3*i+1) = 3*(4*i+1)+1 ∧
    (2*(9*j+1)+1)/3 = 3*(2*j)+1 ∧
    (4*(9*j+7)+2)/3 = 3*(4*j+3)+1 ∧
    4*(3*i+2) = 3*(4*i+2)+2 ∧
    (4*(9*j+2)-2)/3 = 3*(4*j)+2 ∧
    (2*(9*j+8)-1)/3 = 3*(2*j+1)+2 := by omega

end Problems.Collatz.PreimageBalance
