import Problems.Juggler.BeattySlopeHausdorff
import Mathlib.NumberTheory.Transcendental.Liouville.Measure
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Arithmetic slopes with exact Hausdorff geometry

Two arithmetic classes discharge the Diophantine premises of the family
Hausdorff theorems. Almost every real slope is not Liouville with any
exponent above two, which gives Diophantine bounds at every exponent above
one and hence Hausdorff dimension two-thirds. Every quadratic irrational is
badly approximable, which gives positive finite two-thirds Hausdorff measure.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

/-- Finitely many positive denominators admit a common positive Diophantine
constant, because an irrational multiple is never an integer. -/
theorem dio_const_below {x : ℝ} (hx : Irrational x) (τ : ℝ) (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, n < N → 0 < n → ∀ m : ℤ,
      c ≤ (n : ℝ)^τ*|(n : ℝ)*x-(m : ℝ)| := by
  induction N with
  | zero => exact ⟨1, one_pos, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ N ih =>
    obtain ⟨c,hc,h⟩ := ih
    by_cases hN : N = 0
    · subst hN
      exact ⟨c, hc, fun n hn hn0 => absurd hn (by omega)⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    set e := |(N : ℝ)*x-(round ((N : ℝ)*x) : ℝ)| with he
    have hepos : 0 < e := by
      apply abs_pos.2
      intro h0
      have hq : (N : ℝ)*x = (round ((N : ℝ)*x) : ℝ) := sub_eq_zero.1 h0
      have hr : Irrational ((N : ℝ)*x) := hx.natCast_mul (by exact_mod_cast hN)
      exact hr.ne_int _ hq
    refine ⟨min c ((N : ℝ)^τ*e), lt_min hc (mul_pos (Real.rpow_pos_of_pos hN0 _) hepos),
      fun n hn hn0 m => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hlt | heq
    · exact (min_le_left _ _).trans (h n hlt hn0 m)
    · subst heq
      refine (min_le_right _ _).trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _))
      exact round_le ((n : ℝ)*x) m

/-- An irrational number that is not Liouville with exponent `p` satisfies
a uniform Diophantine lower bound of exponent `p-1`. -/
theorem dio_of_not_liouvilleWith {x p : ℝ} (hx : Irrational x) (hL : ¬LiouvilleWith p x) :
    ∃ c : ℝ, 0 < c ∧ DiophantineLowerBound x c (p-1) := by
  unfold LiouvilleWith at hL
  push Not at hL
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hL 1)
  obtain ⟨c,hc,hsmall⟩ := dio_const_below hx (p-1) (N+1)
  refine ⟨min c 1, lt_min hc one_pos, fun n hn m => ?_⟩
  by_cases hnN : n < N+1
  · exact (min_le_left _ _).trans (hsmall n hnN hn m)
  have hn' : N ≤ n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : x ≠ (m : ℝ)/n := fun h => hx.ne_rat ((m : ℚ)/n) (by rw [h]; push_cast; ring)
  have hb := hN n hn' m hne
  have hpow : (n : ℝ)^(p-1)*|(n : ℝ)*x-(m : ℝ)| = (n : ℝ)^p*|x-(m : ℝ)/n| := by
    have h1 : (n : ℝ)*x-(m : ℝ) = n*(x-(m : ℝ)/n) := by field_simp
    rw [h1, abs_mul, abs_of_pos hnr, Real.rpow_sub hnr, Real.rpow_one]
    field_simp
  rw [hpow]
  have hp : 0 < (n : ℝ)^p := Real.rpow_pos_of_pos hnr _
  refine (min_le_right _ _).trans ?_
  rw [mul_comm]
  exact (div_le_iff₀ hp).1 hb

/-- Almost every real number is irrational. -/
theorem ae_irrational : ∀ᵐ x : ℝ, Irrational x := by
  have hc : (range ((↑) : ℚ → ℝ)).Countable := countable_range _
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (hc.measure_zero volume)
  simpa [Irrational] using hx

/-- Almost every real number satisfies a Diophantine lower bound at every
exponent strictly above one, with constants depending on the exponent. -/
theorem ae_dio_family :
    ∀ᵐ x : ℝ, ∀ τ : ℝ, 1 < τ → ∃ c : ℝ, 0 < c ∧ DiophantineLowerBound x c τ := by
  filter_upwards [ae_not_liouvilleWith, ae_irrational] with x hL hx τ hτ
  obtain ⟨c,hc,h⟩ := dio_of_not_liouvilleWith hx (hL (τ+1) (by linarith))
  exact ⟨c, hc, by simpa using h⟩

/-- For Lebesgue-almost every slope `α > 1`, the complete cluster set of the
actual normalized first-passage counts has Hausdorff dimension two-thirds. -/
theorem ae_passageCluster_dimH :
    ∀ᵐ α : ℝ, 1 < α → dimH (passageClusterSet (1/α)) = (2/3 : ℝ≥0∞) := by
  filter_upwards [ae_dio_family, ae_irrational] with α hdio hα hα1
  have hα0 : 0 < α := by linarith
  have hβ : Irrational (1/α) := by simpa using hα.inv
  apply passageCluster_dimH_eq (one_div_pos.mpr hα0) ((div_lt_one hα0).mpr hα1) hβ
  simpa only [one_div_one_div] using hdio

/-- A real root of an integer quadratic polynomial that is irrational is
badly approximable: `|q*x-p| ≥ c/q` for every positive denominator. -/
theorem dio_of_quadratic {x : ℝ} {a b c : ℤ} (ha : a ≠ 0)
    (hroot : (a : ℝ)*x^2+(b : ℝ)*x+(c : ℝ) = 0) (hx : Irrational x) :
    ∃ κ : ℝ, 0 < κ ∧ DiophantineLowerBound x κ 1 := by
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  set y := -(b : ℝ)/a-x with hy
  set d := |x-y|
  have hapos : (0 : ℝ) < |(a : ℝ)| := abs_pos.2 har
  refine ⟨min 1 (1/(|(a : ℝ)| *(1+d))), lt_min one_pos (by positivity), fun q hq p => ?_⟩
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [Real.rpow_one]
  -- The norm form is a nonzero integer.
  have hfac : (a : ℝ)*((p : ℝ)-q*x)*((p : ℝ)-q*y) =
      ((a*p^2+b*p*q+c*q^2 : ℤ) : ℝ) := by
    have hc' : (c : ℝ) = -(a : ℝ)*x^2-(b : ℝ)*x := by linarith
    push_cast
    rw [hy, hc']
    field_simp
    ring
  have hN : (a*p^2+b*p*q+c*q^2 : ℤ) ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hfac
    rcases mul_eq_zero.1 hfac with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact har h2
      · have hqx : x = (p : ℝ)/q := by
          field_simp
          linarith
        exact hx.ne_rat ((p : ℚ)/q) (by rw [hqx]; push_cast; ring)
    · have hqy : x = -(b : ℝ)/a-(p : ℝ)/q := by
        have : y = (p : ℝ)/q := by field_simp; linarith
        rw [← this, hy]
        ring
      exact hx.ne_rat (-(b : ℚ)/a-(p : ℚ)/q) (by rw [hqy]; push_cast; ring)
  have hone : (1 : ℝ) ≤ |(a : ℝ)| *|(p : ℝ)-q*x| *|(p : ℝ)-q*y| := by
    have h := Int.one_le_abs hN
    rw [← abs_mul, ← abs_mul, hfac]
    exact_mod_cast h
  have hsym : |(q : ℝ)*x-(p : ℝ)| = |(p : ℝ)-q*x| := abs_sub_comm _ _
  rw [hsym]
  by_cases hbig : 1 ≤ |(p : ℝ)-q*x|
  · refine (min_le_left _ _).trans ?_
    nlinarith
  push Not at hbig
  have hy_le : |(p : ℝ)-q*y| ≤ q*(1+d) := by
    have htri : |(p : ℝ)-q*y| ≤ |(p : ℝ)-q*x|+|(q : ℝ)| *d := by
      have : (p : ℝ)-q*y = ((p : ℝ)-q*x)+q*(x-y) := by ring
      rw [this]
      exact (abs_add_le _ _).trans (by rw [abs_mul])
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ q)] at htri
    nlinarith [abs_nonneg (x-y)]
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hpx := abs_nonneg ((p : ℝ)-q*x)
  calc
    (1 : ℝ) ≤ |(a : ℝ)| *|(p : ℝ)-q*x| *|(p : ℝ)-q*y| := hone
    _ ≤ |(a : ℝ)| *|(p : ℝ)-q*x| *(q*(1+d)) :=
        mul_le_mul_of_nonneg_left hy_le (by positivity)
    _ = _ := by ring

/-- Every quadratic irrational slope `α > 1` gives positive finite
two-thirds Hausdorff measure for the actual count cluster set. -/
theorem quadratic_cluster_hausdorff {α : ℝ} {a b c : ℤ} (ha : a ≠ 0)
    (hroot : (a : ℝ)*α^2+(b : ℝ)*α+(c : ℝ) = 0) (hα : Irrational α) (hα1 : 1 < α) :
    0 < Measure.hausdorffMeasure (2/3 : ℝ) (passageClusterSet (1/α)) ∧
    Measure.hausdorffMeasure (2/3 : ℝ) (passageClusterSet (1/α)) < ⊤ := by
  have hα0 : 0 < α := by linarith
  obtain ⟨κ,hκ,hdio⟩ := dio_of_quadratic ha hroot hα
  exact passageCluster_hausdorff_bad (one_div_pos.mpr hα0) ((div_lt_one hα0).mpr hα1)
    (by simpa using hα.inv) hκ (by simpa only [one_div_one_div] using hdio)

/-- The golden-ratio slope has positive finite two-thirds Hausdorff measure,
and hence Hausdorff dimension exactly two-thirds. -/
theorem golden_passageCluster_hausdorff :
    0 < Measure.hausdorffMeasure (2/3 : ℝ) (passageClusterSet (1/Real.goldenRatio)) ∧
    Measure.hausdorffMeasure (2/3 : ℝ) (passageClusterSet (1/Real.goldenRatio)) < ⊤ :=
  quadratic_cluster_hausdorff (a := 1) (b := -1) (c := -1) one_ne_zero
    (by push_cast; rw [Real.goldenRatio_sq]; ring) Real.goldenRatio_irrational Real.one_lt_goldenRatio

end Problems.Juggler.BeattySlope
