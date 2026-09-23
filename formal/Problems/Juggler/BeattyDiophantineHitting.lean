import Problems.Juggler.BeattyRotationCover

/-!
# From Diophantine lower bounds to phase coverage

Dirichlet approximation and the reduced rational grid turn a uniform
Diophantine lower bound into positive-orbit hitting with the same exponent.
The arithmetic premise is explicit; no such constant is supplied for the
logarithmic certificate slope in this module.
-/

namespace Problems.Juggler.BeattyPhase

open Set

/-- A uniform lower bound on every nonzero-denominator approximation.
For positive `c` and `τ`, this states `|q*ξ-p| ≥ c*q^(-τ)` without division. -/
def DiophantineLowerBound (ξ c τ : ℝ) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ p : ℤ, c ≤ (q : ℝ)^τ * |(q : ℝ)*ξ-(p : ℝ)|

private theorem rat_den_lower {ξ c τ : ℝ}
    (hdio : DiophantineLowerBound ξ c τ) {N : ℕ} (r : ℚ)
    (he : |ξ-(r : ℝ)| ≤ 1/(((N : ℝ)+1)*r.den)) :
    c*((N : ℝ)+1) ≤ (r.den : ℝ)^τ := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have heq : (r.den : ℝ)*ξ-(r.num : ℝ) = (r.den : ℝ)*(ξ-(r : ℝ)) := by
    rw [Rat.cast_def]
    field_simp
  have hm : |(r.den : ℝ)*ξ-(r.num : ℝ)| ≤ 1/((N : ℝ)+1) := by
    rw [heq, abs_mul, abs_of_pos hd]
    calc
      _ ≤ (r.den : ℝ)*(1/(((N : ℝ)+1)*r.den)) :=
        mul_le_mul_of_nonneg_left he hd.le
      _ = _ := by field_simp
  have h := (hdio r.den r.pos r.num).trans
    (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hd.le _))
  exact (le_div_iff₀ (by positivity : 0 < (N : ℝ)+1)).1 (by simpa [div_eq_mul_inv] using h)

/-- A Diophantine bound of exponent `τ` gives interval hitting with that
same exponent and explicit constant `4^τ/c+1`, for the positive rotation
orbit. The conclusion does not assert that the arithmetic premise holds. -/
theorem phaseHittingBound_of_diophantineLowerBound {ξ c τ : ℝ}
    (hc : 0 < c) (hτ : 0 < τ) (hdio : DiophantineLowerBound ξ c τ) :
    PhaseHittingBound (fun n => Int.fract (((n+1 : ℕ) : ℝ)*ξ)) (4^τ/c+1) τ := by
  intro a b ha hab hb
  let h := b-a
  have hh : 0 < h := sub_pos.2 hab
  have hh1 : h ≤ 1 := by dsimp only [h]; linarith
  let S := (4/h)^τ/c
  let N := ⌈S⌉₊
  have hS : 0 < S := by dsimp only [S]; positivity
  have hSN : S ≤ (N : ℝ) := Nat.le_ceil S
  have hN0 : 0 < N := by
    exact_mod_cast (hS.trans_le hSN)
  have hNS : (N : ℝ) ≤ S+1 := (Nat.ceil_lt_add_one hS.le).le
  obtain ⟨r,hr,hrN⟩ := Real.exists_rat_abs_sub_le_and_den_le ξ hN0
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hden := rat_den_lower hdio r hr
  have hpow : (4/h)^τ < (r.den : ℝ)^τ := by
    have hs : (4/h)^τ ≤ c*(N : ℝ) := by
      have hs' := (div_le_iff₀ hc).1 hSN
      simpa only [mul_comm] using hs'
    nlinarith
  have hq : 4/h < (r.den : ℝ) :=
    (Real.rpow_lt_rpow_iff (by positivity) hd.le hτ).1 hpow
  have hwidth : 4 < (r.den : ℝ)*(b-a) := (div_lt_iff₀ hh).1 hq
  have he : |ξ-(r : ℝ)| ≤ 1/(r.den : ℝ)^2 := by
    apply hr.trans
    apply one_div_le_one_div_of_le (by positivity)
    have hqN : (r.den : ℝ) ≤ N := by exact_mod_cast hrN
    nlinarith
  obtain ⟨m,hm0,hmq,hm⟩ := rotation_hits_interval_of_rat_approx r ha hb hwidth he
  have hmN : m ≤ N := hmq.le.trans hrN
  refine ⟨m-1, ?_, ?_⟩
  · simpa only [Nat.sub_add_cancel hm0] using hm
  · have heq : (m-1 : ℕ)+1 = m := Nat.sub_add_cancel hm0
    have heq' : ((m-1 : ℕ) : ℝ)+1 = m := by exact_mod_cast heq
    rw [heq']
    have hsmall : h^τ ≤ 1 := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow hh.le hh1 hτ.le
    have hprod : (4/h)^τ*h^τ = (4 : ℝ)^τ := by
      rw [← Real.mul_rpow (by positivity) hh.le, div_mul_cancel₀ _ hh.ne']
    calc
      (m : ℝ)*(b-a)^τ ≤ (N : ℝ)*h^τ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hmN) (Real.rpow_nonneg hh.le _)
      _ ≤ (S+1)*h^τ := mul_le_mul_of_nonneg_right hNS (Real.rpow_nonneg hh.le _)
      _ = (4 : ℝ)^τ/c+h^τ := by dsimp only [S]; rw [add_mul]; rw [div_mul_eq_mul_div, hprod]; ring
      _ ≤ _ := by linarith

end Problems.Juggler.BeattyPhase
