import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Monotone

/-!
# Null images and nonzero derivatives

The Jacobian covering lemmas imply that a real function with nonzero
derivative cannot map a set of positive measure to a null set. No global
injectivity or continuity hypothesis is needed. This will distinguish
the laws obtained from the jump profile and its exponentially tilted version.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

/-- A null image forces a null domain if a nonzero derivative exists at
every domain point. The domain need not be measurable or the map injective. -/
theorem volume_eq_zero_of_nonzero_deriv_image_null {f d : ℝ → ℝ} {s : Set ℝ}
    (hd : ∀ x ∈ s, HasDerivWithinAt f (d x) s x)
    (hne : ∀ x ∈ s, d x ≠ 0) (himage : volume (f '' s) = 0) :
    volume s = 0 := by
  classical
  have hlocal : ∀ A : ℝ →L[ℝ] ℝ, ∃ δ : ℝ≥0, 0 < δ ∧
      (A.det ≠ 0 → ∀ t : Set ℝ, ApproximatesLinearOn f A t δ →
        volume (f '' t) = 0 → volume t = 0) := by
    intro A
    by_cases hA : A.det = 0
    · exact ⟨1, by norm_num, fun h => (h hA).elim⟩
    let m : ℝ≥0 := ⟨|A.det|/2, by positivity⟩
    have hm : (0 : ℝ≥0) < m := by
      change 0 < |A.det|/2
      exact half_pos (abs_pos.mpr hA)
    have hlt : (m : ℝ≥0∞) < ENNReal.ofReal |A.det| := by
      rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (abs_pos.mpr hA)]
      exact half_lt_self (abs_pos.mpr hA)
    obtain ⟨δ, hδ, hδpos⟩ :=
      ((mul_le_addHaar_image_of_lt_det volume A hlt).and self_mem_nhdsWithin).exists
    refine ⟨δ, hδpos, fun _ t ht hnull => ?_⟩
    have h := hδ t f ht
    rw [hnull] at h
    have hz := le_antisymm h bot_le
    exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hm.ne')
  choose δ hδ using hlocal
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨t, A, _, hcover, happrox, hA⟩ :=
    exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f s
      (fun x => ContinuousLinearMap.toSpanSingleton ℝ (d x))
      (fun x hx => (hd x hx).hasFDerivWithinAt) δ (fun A => (hδ A).1.ne')
  have hnull (n : ℕ) : volume (s ∩ t n) = 0 := by
    obtain ⟨x, hx, he⟩ := hA hs n
    apply (hδ (A n)).2
    · simpa only [he, ContinuousLinearMap.det_toSpanSingleton] using hne x hx
    · exact happrox n
    · exact measure_mono_null (Set.image_mono inter_subset_left) himage
  apply measure_mono_null (show s ⊆ ⋃ n, s ∩ t n by
    simpa only [← inter_iUnion] using subset_inter (Subset.refl s) hcover)
  exact measure_iUnion_null hnull

/-- A monotone function whose complete range is null has derivative zero
almost everywhere. This applies to dense pure-jump profiles without
differentiating their series term by term. -/
theorem ae_hasDerivAt_zero_of_monotone_null_range {f : ℝ → ℝ}
    (hf : Monotone f) (hnull : volume (range f) = 0) :
    ∀ᵐ x ∂volume, HasDerivAt f 0 x := by
  let s := {x | DifferentiableAt ℝ f x ∧ deriv f x ≠ 0}
  have hs : volume s = 0 := volume_eq_zero_of_nonzero_deriv_image_null
    (fun _ hx => hx.1.hasDerivAt.hasDerivWithinAt) (fun _ hx => hx.2)
    (measure_mono_null (image_subset_range _ _) hnull)
  have ha : ∀ᵐ x ∂volume, x ∉ s := by simpa [ae_iff] using hs
  filter_upwards [hf.ae_differentiableAt, ha] with x hx hsx
  have he : deriv f x = 0 := by
    by_contra h
    exact hsx ⟨hx, h⟩
  simpa only [he] using hx.hasDerivAt

/-- A measurable real map with nonzero derivative almost everywhere on a
measurable domain sends restricted Lebesgue measure to an absolutely
continuous measure. Global injectivity is not required. -/
theorem map_restrict_absolutelyContinuous_of_ae_nonzero_deriv
    {f d : ℝ → ℝ} {s : Set ℝ} (hf : Measurable f) (hs : MeasurableSet s)
    (hd : ∀ᵐ x ∂volume.restrict s, HasDerivAt f (d x) x ∧ d x ≠ 0) :
    (volume.restrict s).map f ≪ volume := by
  classical
  let good := {x | HasDerivAt f (d x) x ∧ d x ≠ 0}
  have hbad : volume (s \ good) = 0 := by
    have h := (ae_restrict_iff' hs).mp hd
    change volume {x | x ∈ s ∧ ¬(HasDerivAt f (d x) x ∧ d x ≠ 0)} = 0
    simpa only [ae_iff, Classical.not_imp] using h
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hnull
  rw [Measure.map_apply hf hN, Measure.restrict_apply (hf hN)]
  have hg : volume ((f ⁻¹' N ∩ s) ∩ good) = 0 :=
    volume_eq_zero_of_nonzero_deriv_image_null
      (fun _ hx => hx.2.1.hasDerivWithinAt) (fun _ hx => hx.2.2)
      (measure_mono_null (by rintro _ ⟨x, hx, rfl⟩; exact hx.1.1) hnull)
  apply measure_mono_null (show f ⁻¹' N ∩ s ⊆ ((f ⁻¹' N ∩ s) ∩ good) ∪ (s \ good) by
    intro x hx
    by_cases h : x ∈ good
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx.2, h⟩)
  exact measure_union_null hg hbad

end Problems.Juggler.BeattyPhase
