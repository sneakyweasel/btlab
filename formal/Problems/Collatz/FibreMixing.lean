import Problems.Collatz.FibreHeightBudget

/-! # Fine-scale mixing does not force a lower bound at a chosen integer

This is an artificial coherent ternary density, not the signed Collatz operator.
Every unit cylinder has positive density, its unit mean is one, and refinement
errors decay uniformly and exponentially. Nevertheless the densities along any
chosen unit digit path form a summable geometric series. The missing arithmetic
input must therefore use more than coherence, positivity and averaged mixing.
-/

noncomputable section

namespace Problems.Collatz.FibreMixing

open Finset
open scoped Classical

/-- A ternary density which falls by one third along the chosen digit path,
and becomes constant as soon as the path is left. -/
def density (root : ℕ → Fin 3) : List (Fin 3) → ℝ
  | [] => 1
  | x :: xs => if x = root 0 then (1/3) * density (fun i => root (i+1)) xs else 4/3

/-- The first `d` digits of the chosen path, in least-significant-first order. -/
def rootPrefix (root : ℕ → Fin 3) : ℕ → List (Fin 3)
  | 0 => []
  | d+1 => root 0 :: rootPrefix (fun i => root (i+1)) d

/-- Every finite cylinder of the artificial density has positive weight. -/
theorem density_pos (root : ℕ → Fin 3) (w : List (Fin 3)) : 0 < density root w := by
  induction w generalizing root with
  | nil => norm_num [density]
  | cons x xs ih =>
      simp only [density]
      split_ifs
      · exact mul_pos (by norm_num) (ih _)
      · norm_num

/-- All artificial densities are bounded by four thirds. -/
theorem density_le (root : ℕ → Fin 3) (w : List (Fin 3)) : density root w ≤ 4/3 := by
  induction w generalizing root with
  | nil => norm_num [density]
  | cons x xs ih =>
      simp only [density]
      split_ifs
      · linarith [ih (fun i => root (i+1))]
      · rfl

/-- The three child densities average exactly to the parent density. -/
theorem density_children (root : ℕ → Fin 3) (w : List (Fin 3)) :
    (∑ i : Fin 3, density root (w ++ [i])) = 3 * density root w := by
  induction w generalizing root with
  | nil =>
      simp only [List.nil_append, density, mul_one]
      have he (i : Fin 3) : (if i = root 0 then (1/3:ℝ) else 4/3) =
          4/3 - if i = root 0 then 1 else 0 := by
        split_ifs <;> norm_num
      simp_rw [he]
      norm_num [sum_sub_distrib]
  | cons x xs ih =>
      by_cases hx : x = root 0
      · simp only [List.cons_append, density, hx, ↓reduceIte]
        rw [← mul_sum, ih]
        ring
      · simp [List.cons_append, density, hx]

/-- The selected path has the exact geometrically decreasing density. -/
theorem density_rootPrefix (root : ℕ → Fin 3) (d : ℕ) :
    density root (rootPrefix root d) = (1/3:ℝ)^d := by
  induction d generalizing root with
  | zero => simp [rootPrefix, density]
  | succ d ih => simp [rootPrefix, density, ih, pow_succ, mul_comm]

/-- Uniform refinement control holds on every cylinder, not only on average. -/
theorem density_append_error (root : ℕ → Fin 3) (w v : List (Fin 3)) :
    |density root (w ++ v) - density root w| ≤ (1/3:ℝ)^w.length := by
  induction w generalizing root with
  | nil =>
      simp only [List.nil_append, density, List.length_nil, pow_zero]
      exact abs_le.mpr ⟨by linarith [density_pos root v], by linarith [density_le root v]⟩
  | cons x xs ih =>
      by_cases hx : x = root 0
      · simp only [List.cons_append, density, hx, ↓reduceIte, List.length_cons]
        rw [← mul_sub, abs_mul]
        norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 1/3)]
        simpa only [pow_succ, mul_comm] using
          mul_le_mul_of_nonneg_left (ih (fun i => root (i+1))) (by norm_num : (0:ℝ) ≤ 1/3)
      · simp [List.cons_append, density, hx]

/-- Unit-supported version: the zero initial digit is sterile, the chosen unit
digit contains the density above, and the other unit digit has constant density one. -/
def unitDensity (root : ℕ → Fin 3) : List (Fin 3) → ℝ
  | [] => 2/3
  | x :: xs => if x = 0 then 0 else if x = root 0 then
      density (fun i => root (i+1)) xs else 1

/-- The initial three densities are exactly the unit indicator `(0,1,1)`. -/
theorem unitDensity_singleton (root : ℕ → Fin 3) (x : Fin 3) :
    unitDensity root [x] = if x = 0 then 0 else 1 := by
  simp [unitDensity, density]

/-- At every positive level, positivity is equivalent to a nonzero initial digit. -/
theorem unitDensity_pos_iff (root : ℕ → Fin 3) (x : Fin 3) (xs : List (Fin 3)) :
    0 < unitDensity root (x :: xs) ↔ x ≠ 0 := by
  simp only [unitDensity]
  split_ifs <;> simp_all [density_pos]

/-- The unit-supported model is coherent under every ternary refinement. -/
theorem unitDensity_children (root : ℕ → Fin 3) (hr : root 0 ≠ 0) (w : List (Fin 3)) :
    (∑ i : Fin 3, unitDensity root (w ++ [i])) = 3 * unitDensity root w := by
  cases w with
  | nil => norm_num [unitDensity, density, Fin.sum_univ_succ]
  | cons x xs =>
      by_cases hx : x = 0
      · simp [unitDensity, hx]
      · by_cases he : x = root 0
        · simpa only [List.cons_append, unitDensity, hx, he, hr, ↓reduceIte] using
            density_children (fun i => root (i+1)) xs
        · simp [unitDensity, hx, he]

/-- Sum of the densities of all descendants at one finite depth. -/
def levelSum (f : List (Fin 3) → ℝ) : ℕ → List (Fin 3) → ℝ
  | 0, w => f w
  | d+1, w => ∑ i : Fin 3, levelSum f d (w ++ [i])

private theorem levelSum_eq (f : List (Fin 3) → ℝ)
    (hf : ∀ w, (∑ i : Fin 3, f (w ++ [i])) = 3*f w) (d : ℕ) (w : List (Fin 3)) :
    levelSum f d w = 3^d*f w := by
  induction d generalizing w with
  | zero => simp [levelSum]
  | succ d ih => simp only [levelSum, ih, ← mul_sum, hf, pow_succ]; ring

/-- At level `d+1`, the sum is exactly the number of unit cylinders, so their mean is one. -/
theorem unitDensity_levelSum (root : ℕ → Fin 3) (hr : root 0 ≠ 0) (d : ℕ) :
    levelSum (unitDensity root) (d+1) [] = 2*3^d := by
  rw [levelSum_eq _ (unitDensity_children root hr)]
  simp only [unitDensity, pow_succ]
  ring

/-- Past the first digit, refinement errors decay uniformly at the rate `3^(-length)`. -/
theorem unitDensity_append_error (root : ℕ → Fin 3) (x : Fin 3) (xs v : List (Fin 3)) :
    |unitDensity root ((x :: xs) ++ v) - unitDensity root (x :: xs)| ≤ (1/3:ℝ)^xs.length := by
  by_cases hx : x = 0
  · simp [unitDensity, hx]
  · by_cases he : x = root 0
    · have hr : root 0 ≠ 0 := by simpa only [← he] using hx
      simpa only [List.cons_append, unitDensity, hx, he, hr, ↓reduceIte] using
        density_append_error (fun i => root (i+1)) xs v
    · simp [unitDensity, hx, he]

/-- The selected unit path still has geometrically decreasing density. -/
theorem unitDensity_rootPrefix (root : ℕ → Fin 3) (hr : root 0 ≠ 0) (d : ℕ) :
    unitDensity root (rootPrefix root (d+1)) = (1/3:ℝ)^d := by
  simp only [rootPrefix, unitDensity, hr, ↓reduceIte, density_rootPrefix]

/-- Despite positivity, coherence and exponential uniform refinement control,
the chosen unit path has a summable density series with exact sum three halves. -/
theorem root_series_hasSum (root : ℕ → Fin 3) (hr : root 0 ≠ 0) :
    HasSum (fun d => unitDensity root (rootPrefix root (d+1))) (3/2:ℝ) := by
  simp_rw [unitDensity_rootPrefix root hr]
  convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/3)
    (by norm_num : (1/3:ℝ) < 1) using 1
  norm_num

/-- The least-significant-first ternary digits of an ordinary natural integer. -/
def integerDigits (a : ℕ) (i : ℕ) : Fin 3 :=
  ⟨a / 3^i % 3, Nat.mod_lt _ (by decide)⟩

/-- The counterexample can be centered at any specified ordinary unit integer. -/
theorem integer_root_hasSum (a : ℕ) (ha : a % 3 ≠ 0) :
    HasSum (fun d => unitDensity (integerDigits a)
      (rootPrefix (integerDigits a) (d+1))) (3/2:ℝ) := by
  apply root_series_hasSum
  intro he
  have hv := congrArg Fin.val he
  simp only [integerDigits, pow_zero, Nat.div_one, Fin.val_zero] at hv
  exact ha hv

/-- Even on unit cylinders the artificial density never exceeds four thirds. -/
theorem unitDensity_le (root : ℕ → Fin 3) (w : List (Fin 3)) :
    unitDensity root w ≤ 4/3 := by
  cases w with
  | nil => norm_num [unitDensity]
  | cons x xs =>
      simp only [unitDensity]
      split_ifs
      · norm_num
      · exact density_le _ _
      · norm_num

/-- Each actual signed operator has a one-step coefficient at least three halves
at a positive odd target: seventeen for the plus sign, one for the minus sign. -/
theorem signed_kernel_spike_lower (plus : Bool) :
    (3/2:ℝ) ≤ FibreHeightBudget.kernel plus 1 (if plus then 17 else 1) := by
  have h := FibreMass.transfer_spike plus (r := 1) (by omega)
    (h := FibreGeneration.unitWeight) (fun b => by
      unfold FibreGeneration.unitWeight
      split_ifs <;> norm_num)
  cases plus <;> simpa [FibreHeightBudget.kernel, FibreMass.iterate,
    FibreGeneration.unitWeight, FibreMass.spike, FibreActual.residue] using h

/-- The model fails an exact arithmetic constraint of both signed operators;
its summability result is not a Collatz coefficient counterexample. -/
theorem model_lt_signed_kernel (root : ℕ → Fin 3) (w : List (Fin 3)) (plus : Bool) :
    unitDensity root w < FibreHeightBudget.kernel plus 1 (if plus then 17 else 1) := by
  linarith [unitDensity_le root w, signed_kernel_spike_lower plus]

/-- A second normalization with first row `(0,1,2)`, matching the first row
of Tao's coherent Syracuse density, but not its random affine stationarity. -/
def syracuseDensity (root : ℕ → Fin 3) : List (Fin 3) → ℝ
  | [] => 1
  | x :: xs => (x.val:ℝ) * unitDensity root (x :: xs)

/-- The second model has exactly the first Syracuse density row. -/
theorem syracuseDensity_singleton (root : ℕ → Fin 3) (x : Fin 3) :
    syracuseDensity root [x] = (x.val:ℝ) := by
  change (x.val:ℝ) * unitDensity root [x] = _
  rw [unitDensity_singleton]
  split_ifs with hx
  · subst x; norm_num
  · simp

/-- Multiplying by the initial digit preserves all ternary refinement identities. -/
theorem syracuseDensity_children (root : ℕ → Fin 3) (hr : root 0 ≠ 0)
    (w : List (Fin 3)) :
    (∑ i : Fin 3, syracuseDensity root (w ++ [i])) = 3 * syracuseDensity root w := by
  cases w with
  | nil =>
      change (∑ i : Fin 3, syracuseDensity root [i]) = 3 * 1
      simp_rw [syracuseDensity_singleton]
      norm_num [Fin.sum_univ_succ]
  | cons x xs =>
      have hh := unitDensity_children root hr (x :: xs)
      simp only [List.cons_append] at hh
      simp only [List.cons_append, syracuseDensity]
      rw [← mul_sum, hh]
      ring

/-- The second normalization has mean one over all cylinders at every level. -/
theorem syracuseDensity_levelSum (root : ℕ → Fin 3) (hr : root 0 ≠ 0) (d : ℕ) :
    levelSum (syracuseDensity root) d [] = 3^d := by
  rw [levelSum_eq _ (syracuseDensity_children root hr)]
  simp [syracuseDensity]

/-- Uniform exponential refinement control survives the Syracuse normalization. -/
theorem syracuseDensity_append_error (root : ℕ → Fin 3) (x : Fin 3)
    (xs v : List (Fin 3)) :
    |syracuseDensity root ((x :: xs) ++ v) - syracuseDensity root (x :: xs)| ≤
      2*(1/3:ℝ)^xs.length := by
  simp only [List.cons_append, syracuseDensity, ← mul_sub, abs_mul,
    abs_of_nonneg (show (0:ℝ) ≤ (x.val:ℝ) from Nat.cast_nonneg _)]
  have hx : (x.val:ℝ) ≤ 2 := by exact_mod_cast (show x.val ≤ 2 by omega)
  exact mul_le_mul hx (unitDensity_append_error root x xs v) (abs_nonneg _)
    (by norm_num)

/-- A prescribed unit path has a summable series even with the Syracuse first row. -/
theorem syracuse_root_hasSum (root : ℕ → Fin 3) (hr : root 0 ≠ 0) :
    HasSum (fun d => syracuseDensity root (rootPrefix root (d+1)))
      ((root 0).val * (3/2:ℝ)) := by
  simpa only [rootPrefix, syracuseDensity] using
    (root_series_hasSum root hr).mul_left ((root 0).val:ℝ)

end Problems.Collatz.FibreMixing
