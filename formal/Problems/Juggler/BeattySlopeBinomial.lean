import Problems.Juggler.BeattySlopeRenewal

/-!
# A uniform geometric bound for the tilted binomial tail

At every boundary strictly between zero and one, the chosen odd-letter tilt
makes each binomial term beyond the strict cutoff at most half its predecessor.
The whole endpoint tail is therefore between its first term and twice that
term. These finite inequalities require neither irrationality nor Stirling.
-/

namespace Problems.Juggler.BeattySlope

open Finset

/-- The first natural index strictly above the real terminal boundary. -/
noncomputable def endpointCutoff (β : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ)*β⌋₊+1

/-- The strict cutoff lies in the unit interval immediately above the boundary. -/
theorem endpointCutoff_bounds {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    (n : ℝ)*β < endpointCutoff β n ∧ (endpointCutoff β n : ℝ) ≤ n*β+1 := by
  constructor
  · simpa [endpointCutoff] using Nat.lt_floor_add_one ((n : ℝ)*β)
  · have h := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hβ)
    dsimp [endpointCutoff]
    push_cast
    linarith

/-- At positive depth and a boundary below one, the cutoff is a binomial index. -/
theorem endpointCutoff_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {n : ℕ} (hn : 0 < n) : endpointCutoff β n ≤ n := by
  apply Nat.succ_le_of_lt
  apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) hβ0)).2
  exact mul_lt_of_lt_one_right (by exact_mod_cast hn) hβ1

/-- The actual weighted endpoint sum is the tail starting at the strict cutoff. -/
theorem endpointWeight_eq_tail {β : ℝ} (hβ0 : 0 ≤ β) (z : ℝ) (n : ℕ) :
    endpointWeight β z n = ∑ k ∈ Ico (endpointCutoff β n) (n+1), (n.choose k : ℝ)*z^k := by
  have hh (k : ℕ) : (n : ℝ)*β < k ↔ endpointCutoff β n ≤ k := by
    rw [← Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) hβ0)]
    exact Nat.lt_iff_add_one_le
  simp only [endpointWeight, hh, ← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range, mem_Ico]
  exact and_comm

/-- Each tilted binomial term beyond the cutoff is at most half the previous
one. The constant is independent of the boundary and the depth. -/
theorem tilted_choose_step_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {n k : ℕ} (hk : endpointCutoff β n ≤ k) :
    (n.choose (k+1) : ℝ)*tiltedOddWeight β^(k+1) ≤
      (1/2 : ℝ)*((n.choose k : ℝ)*tiltedOddWeight β^k) := by
  have hz := tiltedOddWeight_pos hβ0 hβ1
  by_cases hkn : k ≤ n
  · have hkR : (n : ℝ)*β < k :=
      (endpointCutoff_bounds hβ0.le n).1.trans_le (by exact_mod_cast hk)
    have hratio : tiltedOddWeight β*(n-k : ℕ) ≤ (1/2 : ℝ)*(k+1 : ℕ) := by
      rw [Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one]
      unfold tiltedOddWeight
      have hq : 0 < 1-β := by linarith
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (show 0 < 2*(1-β) by positivity)).2
      nlinarith
    have he : (n.choose (k+1) : ℝ)*(k+1 : ℕ) =
        (n.choose k : ℝ)*(n-k : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq n k
    have hm := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg (n.choose k) : (0:ℝ) ≤ _)
    have hstep : (n.choose (k+1) : ℝ)*tiltedOddWeight β ≤ (1/2 : ℝ)*(n.choose k : ℝ) := by
      have hp : (0 : ℝ) < (k+1 : ℕ) := by positivity
      nlinarith
    have h := mul_le_mul_of_nonneg_right hstep (pow_nonneg hz.le k)
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < k+1)]
    simp only [Nat.cast_zero, zero_mul]
    positivity

/-- A geometric majorant with ratio one half holds for every tilted term
following the strict cutoff, including terms beyond the binomial support. -/
theorem tilted_choose_shift_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (n j : ℕ) :
    (n.choose (endpointCutoff β n+j) : ℝ)*tiltedOddWeight β^(endpointCutoff β n+j) ≤
      ((n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n)*(1/2 : ℝ)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs := tilted_choose_step_bound hβ0 hβ1 (n := n)
      (k := endpointCutoff β n+j) (by omega)
    calc
      _ ≤ (1/2 : ℝ)*((n.choose (endpointCutoff β n+j) : ℝ)*
          tiltedOddWeight β^(endpointCutoff β n+j)) := by simpa [Nat.add_assoc] using hs
      _ ≤ (1/2 : ℝ)*(((n.choose (endpointCutoff β n) : ℝ)*
          tiltedOddWeight β^endpointCutoff β n)*(1/2 : ℝ)^j) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- The full tilted endpoint sum lies between its first term and twice that
term, for every positive depth and every real boundary in `(0,1)`. -/
theorem tilted_endpoint_first_term_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {n : ℕ} (hn : 0 < n) :
    (n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n ≤
        endpointWeight β (tiltedOddWeight β) n ∧
      endpointWeight β (tiltedOddWeight β) n ≤
        2*((n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n) := by
  have hz := tiltedOddWeight_pos hβ0 hβ1
  rw [endpointWeight_eq_tail hβ0.le]
  constructor
  · apply single_le_sum (s := Ico (endpointCutoff β n) (n+1))
      (a := endpointCutoff β n)
      (f := fun k : ℕ => (n.choose k : ℝ)*tiltedOddWeight β^k)
    · intro k _
      positivity
    · exact mem_Ico.2 ⟨le_rfl, by
        have h := endpointCutoff_le hβ0.le hβ1 hn
        omega⟩
  · rw [sum_Ico_eq_sum_range]
    have hgeom (m : ℕ) : ∑ j ∈ range m, (1/2 : ℝ)^j ≤ 2 := by
      have h := geom_sum_mul (1/2 : ℝ) m
      have hp := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) m
      nlinarith
    calc
      _ ≤ ∑ j ∈ range (n+1-endpointCutoff β n),
          ((n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n)*
            (1/2 : ℝ)^j := sum_le_sum fun j _ => tilted_choose_shift_bound hβ0 hβ1 n j
      _ = ((n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n)*
          (∑ j ∈ range (n+1-endpointCutoff β n), (1/2 : ℝ)^j) := by rw [mul_sum]
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hgeom _) (by positivity)).trans_eq (mul_comm _ _)

end Problems.Juggler.BeattySlope
