import Problems.Collatz.BackwardMass

/-!
# Residue symmetry does not preserve the predecessor height comparison

The negative shortcut has odd predecessor `(2*a+1)/3`, above `2*a/3`.
The positive shortcut has odd predecessor `(2*a-1)/3`, below it. The
common homogeneous residue program therefore needs a separate justification
before it can bound actual negative-shortcut preimage counts.
-/

namespace Problems.Collatz.PreimageScale

def minusOddPreimage (a : ℕ) : ℕ := (2 * a + 1) / 3
def plusOddPreimage (a : ℕ) : ℕ := (2 * a - 1) / 3

theorem minus_preimage_exact {a : ℕ} (ha : a % 3 = 1) :
    3 * minusOddPreimage a = 2 * a + 1 ∧
    minusOddPreimage a % 2 = 1 ∧ negT (minusOddPreimage a) = a := by
  have he : 3 * minusOddPreimage a = 2 * a + 1 := by
    unfold minusOddPreimage
    omega
  have ho : minusOddPreimage a % 2 = 1 := by omega
  refine ⟨he, ho, ?_⟩
  simp only [negT, ho, Nat.one_ne_zero, ite_false]
  omega

theorem plus_preimage_exact {a : ℕ} (ha : a % 3 = 2) :
    3 * plusOddPreimage a + 1 = 2 * a ∧
    plusOddPreimage a % 2 = 1 ∧ shortcutC (plusOddPreimage a) = a := by
  have he : 3 * plusOddPreimage a + 1 = 2 * a := by
    unfold plusOddPreimage
    omega
  have ho : plusOddPreimage a % 2 = 1 := by omega
  refine ⟨he, ho, ?_⟩
  simp only [shortcutC, ho, Nat.one_ne_zero, ite_false]
  omega

theorem minus_preimage_above {a : ℕ} (ha : a % 3 = 1) :
    (2 : ℝ) * a / 3 < minusOddPreimage a := by
  have he : (3 : ℝ) * minusOddPreimage a = 2 * a + 1 := by
    exact_mod_cast (minus_preimage_exact ha).1
  linarith

theorem plus_preimage_below {a : ℕ} (ha : a % 3 = 2) :
    (plusOddPreimage a : ℝ) < 2 * a / 3 := by
  have he : (3 : ℝ) * plusOddPreimage a + 1 = 2 * a := by
    exact_mod_cast (plus_preimage_exact ha).1
  linarith

/-- Exact reduction in the available child scale, in multiplicative form. -/
theorem minus_scale_correction {a : ℕ} (ha : a % 3 = 1) (x : ℝ) :
    x / minusOddPreimage a =
      ((x / a) * (3 / 2)) / (1 + 1 / (2 * a)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hc0 : (0 : ℝ) < minusOddPreimage a := by
    have := (minus_preimage_exact ha).1
    exact_mod_cast (show 0 < minusOddPreimage a by omega)
  have he : (3 : ℝ) * minusOddPreimage a = 2 * a + 1 := by
    exact_mod_cast (minus_preimage_exact ha).1
  field_simp
  nlinarith [congrArg (fun t : ℝ => x * t) he]

/-- At a positive cutoff the nominal child budget is strictly too large. -/
theorem minus_nominal_budget_exceeds {a : ℕ} (ha : a % 3 = 1)
    {x : ℝ} (hx : 0 < x) :
    x < ((x / a) * (3 / 2)) * minusOddPreimage a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have h := mul_lt_mul_of_pos_left (minus_preimage_above ha)
    (show 0 < (x / a) * (3 / 2 : ℝ) by positivity)
  have he : ((x / a) * (3 / 2 : ℝ)) * (2 * a / 3) = x := by field_simp
  simpa only [he] using h

/-- For the positive shortcut the same nominal child budget is inside the cutoff. -/
theorem plus_nominal_budget_below {a : ℕ} (ha : a % 3 = 2)
    {x : ℝ} (hx : 0 < x) :
    ((x / a) * (3 / 2)) * plusOddPreimage a < x := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hp := plus_preimage_below ha
  have h := mul_lt_mul_of_pos_left hp (show 0 < (x / a) * (3 / 2 : ℝ) by positivity)
  have he : ((x / a) * (3 / 2 : ℝ)) * (2 * a / 3) = x := by field_simp
  simpa only [he] using h

/-- The excess contains actual ancestors, even at a nonperiodic target. -/
theorem excluded_ancestor :
    minusOddPreimage 19 = 13 ∧
    (negT^[3]) 104 = 13 ∧
    (∀ j ≤ 3, (negT^[j]) 104 ≤ 104) ∧
    (103 : ℕ) < 104 ∧ 4 * 19 ≤ (103 : ℕ) ∧
    (104 : ℝ) ≤ ((103 / 19) * (3 / 2)) * minusOddPreimage 19 := by
  refine ⟨by decide, by decide, ?_, by norm_num, by norm_num, ?_⟩
  · intro j hj
    interval_cases j <;> decide
  · norm_num [minusOddPreimage]

theorem nineteen_not_periodic : ∀ d : ℕ, 0 < d → (negT^[d]) 19 ≠ 19 := by
  let s : Finset ℕ := {28, 14, 7, 10, 5}
  have hclosed : ∀ n ∈ s, negT n ∈ s := by decide
  have hmem : ∀ d, (negT^[d + 1]) 19 ∈ s := by
    intro d
    induction d with
    | zero => decide
    | succ d ih =>
        rw [Function.iterate_succ_apply']
        exact hclosed _ ih
  intro d hd he
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have h := hmem k
  rw [he] at h
  norm_num [s] at h

end Problems.Collatz.PreimageScale
