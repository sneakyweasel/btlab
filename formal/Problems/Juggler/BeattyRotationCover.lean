import Problems.Juggler.BeattyPhaseHolder
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Rational grids covering positive rotation orbits

A reduced rational approximation with error at most the inverse square of
its denominator gives an explicit interval-hitting bound for the positive
rotation orbit. All endpoints and the exclusion of index zero are checked.
-/

namespace Problems.Juggler.BeattyPhase

open Set

private theorem rational_grid_point (r : ℚ) {j : ℤ}
    (hj0 : 0 < j) (hjq : j < r.den) :
    ∃ n : ℕ, 0 < n ∧ n < r.den ∧
      Int.fract ((n : ℝ)*(r : ℝ)) = (j : ℝ)/r.den := by
  obtain ⟨u,v,huv⟩ := r.isCoprime_num_den
  let k : ℤ := (j*u) % r.den
  have hd : (0 : ℤ) < r.den := by exact_mod_cast r.pos
  have hk0 : 0 ≤ k := Int.emod_nonneg _ (by omega)
  have hkd : k < r.den := Int.emod_lt_of_pos _ hd
  have hmod : (k*r.num) % r.den = j := by
    calc
      _ = ((j*u)*r.num) % r.den := by
        dsimp only [k]
        rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
      _ = (j*(u*r.num)) % r.den := by rw [mul_assoc]
      _ = (j*(1-v*r.den)) % r.den := by rw [← eq_sub_iff_add_eq.2 huv]
      _ = j % r.den := by ring_nf; simp
      _ = j := Int.emod_eq_of_lt hj0.le hjq
  have hkp : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz,zero_mul,Int.zero_emod] at hmod
    omega
  have hk : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
  refine ⟨k.toNat, by omega, by omega, ?_⟩
  rw [Rat.cast_def]
  have he : (k.toNat : ℝ)*((r.num : ℝ)/r.den) = ((k*r.num : ℤ) : ℝ)/r.den := by
    have hk' : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast hk
    rw [Int.cast_mul, hk']
    ring
  rw [he, Int.fract_div_intCast_eq_div_intCast_mod, hmod]

private theorem fract_stays_in_interval {x y a b η : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hx : Int.fract x ∈ Ioo (a+η) (b-η)) (hxy : |y-x| ≤ η) :
    Int.fract y ∈ Ioo a b := by
  have hdist := abs_le.1 hxy
  have hy : y-(⌊x⌋ : ℤ) ∈ Ioo a b := by
    simp only [Int.fract] at hx
    constructor <;> linarith [hx.1,hx.2]
  rw [← Int.fract_sub_intCast y ⌊x⌋,
    Int.fract_eq_self.2 ⟨ha.trans hy.1.le,hy.2.trans_le hb⟩]
  exact hy

/-- A rational approximation of inverse-square quality hits every phase
interval wider than four inverse denominators at a positive index strictly
below that denominator. The constants are explicit and not optimized. -/
theorem rotation_hits_interval_of_rat_approx {ξ a b : ℝ} (r : ℚ)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hwidth : 4 < (r.den : ℝ)*(b-a))
    (happrox : |ξ-(r : ℝ)| ≤ 1/(r.den : ℝ)^2) :
    ∃ n : ℕ, 0 < n ∧ n < r.den ∧ Int.fract ((n : ℝ)*ξ) ∈ Ioo a b := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  let j : ℤ := ⌊(r.den : ℝ)*a⌋+2
  have hjlower : (r.den : ℝ)*a+1 < j := by
    dsimp only [j]
    push_cast
    linarith [Int.lt_floor_add_one ((r.den : ℝ)*a)]
  have hjupper : (j : ℝ) ≤ (r.den : ℝ)*a+2 := by
    dsimp only [j]
    push_cast
    linarith [Int.floor_le ((r.den : ℝ)*a)]
  have hj0 : 0 < j := by
    exact_mod_cast (by nlinarith : (0 : ℝ) < j)
  have hjq : j < r.den := by
    exact_mod_cast (by nlinarith : (j : ℝ) < r.den)
  obtain ⟨n,hn0,hnq,hgrid⟩ := rational_grid_point r hj0 hjq
  refine ⟨n,hn0,hnq, ?_⟩
  apply fract_stays_in_interval ha hb (η := 1/(r.den : ℝ))
  · rw [hgrid]
    constructor
    · apply (lt_div_iff₀ hd).2
      have he : (a+1/(r.den : ℝ))*(r.den : ℝ) = (r.den : ℝ)*a+1 := by
        field_simp
      rw [he]
      exact hjlower
    · apply (div_lt_iff₀ hd).2
      have he : (b-1/(r.den : ℝ))*(r.den : ℝ) = (r.den : ℝ)*b-1 := by
        field_simp
      rw [he]
      nlinarith
  · rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    calc
      _ ≤ (n : ℝ)*(1/(r.den : ℝ)^2) :=
        mul_le_mul_of_nonneg_left happrox (Nat.cast_nonneg n)
      _ ≤ (r.den : ℝ)*(1/(r.den : ℝ)^2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hnq.le) (by positivity)
      _ = _ := by field_simp

end Problems.Juggler.BeattyPhase
