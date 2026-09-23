import Problems.Juggler.BeattyWeakConvergence
import Mathlib.MeasureTheory.PiSystem

/-!
# Weak convergence from spatial tails

Half-open intervals form a convergence-determining family on the real line.
Convergence of every upper tail and of the total masses therefore identifies
a nonzero finite limiting measure, together with its probability normalization.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal

/-- Convergence of all real upper-tail probabilities implies weak convergence. -/
theorem tendsto_probabilityMeasure_of_tails {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {μ : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (h : ∀ y : ℝ, Tendsto (fun i => (μ i : Measure ℝ).real (Ioi y)) L
      (𝓝 ((ν : Measure ℝ).real (Ioi y)))) : Tendsto μ L (𝓝 ν) := by
  apply (isPiSystem_Ioc (id : ℝ → ℝ) (id : ℝ → ℝ)).tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a,b,hab,rfl⟩
    change a < b at hab
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨a,b,hxab,habu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hu.mem_nhds hx)
    let c := (x+b)/2
    have hxc : x < c := by dsimp [c]; linarith [hxab.2]
    have hcb : c < b := by dsimp [c]; linarith [hxab.2]
    refine ⟨Ioc a c, ⟨a,c,hxab.1.trans hxc,rfl⟩, Ioc_mem_nhds hxab.1 hxc, ?_⟩
    exact fun z hz => habu ⟨hz.1,hz.2.trans_lt hcb⟩
  · rintro s ⟨a,b,hab,rfl⟩
    have he (ρ : ProbabilityMeasure ℝ) : (ρ : Measure ℝ).real (Ioc a b) =
        (ρ : Measure ℝ).real (Ioi a)-(ρ : Measure ℝ).real (Ioi b) := by
      have hs : Ioi a \ Ioi b = Ioc a b := by ext x; simp
      have hab' : a ≤ b := hab.le
      rw [← hs, measureReal_sdiff (μ := (ρ : Measure ℝ)) (Ioi_subset_Ioi hab') measurableSet_Ioi]
    have hh := (h a).sub (h b)
    simp only [← he] at hh
    exact NNReal.tendsto_coe.1 hh

/-- Tail masses and total mass determine weak convergence of finite
measures whenever the proposed limiting measure is nonzero. -/
theorem tendsto_finiteMeasure_of_tails {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {μ : ι → FiniteMeasure ℝ} {ν : FiniteMeasure ℝ}
    (hν : ν ≠ 0)
    (hm : Tendsto (fun i => (μ i : Measure ℝ).real univ) L
      (𝓝 ((ν : Measure ℝ).real univ)))
    (ht : ∀ y : ℝ, Tendsto (fun i => (μ i : Measure ℝ).real (Ioi y)) L
      (𝓝 ((ν : Measure ℝ).real (Ioi y)))) : Tendsto μ L (𝓝 ν) := by
  have hv : (ν.mass : ℝ) ≠ 0 := by exact_mod_cast ν.mass_nonzero_iff.2 hν
  have hp : 0 < (ν.mass : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hv)
  have hm' : Tendsto (fun i => ((μ i).mass : ℝ)) L (𝓝 (ν.mass : ℝ)) := hm
  have hev : ∀ᶠ i in L, μ i ≠ 0 := by
    filter_upwards [(tendsto_order.1 hm').1 0 hp] with i hi
    apply (μ i).mass_nonzero_iff.1
    exact_mod_cast ne_of_gt hi
  have hn : Tendsto (fun i => (μ i).normalize) L (𝓝 ν.normalize) := by
    apply tendsto_probabilityMeasure_of_tails
    intro y
    have hh := (ht y).div hm' hv
    have he (ρ : FiniteMeasure ℝ) (hρ : ρ ≠ 0) :
        (ρ.normalize : Measure ℝ).real (Ioi y) =
          (ρ : Measure ℝ).real (Ioi y)/(ρ.mass : ℝ) := by
      change ((ρ.normalize (Ioi y) : ℝ≥0) : ℝ) = _
      rw [ρ.normalize_eq_of_nonzero hρ]
      simp only [NNReal.coe_mul, NNReal.coe_inv, div_eq_mul_inv, FiniteMeasure.measureReal_eq_coe_coeFn]
      ring
    rw [← he ν hν] at hh
    apply hh.congr'
    filter_upwards [hev] with i hi
    exact (he (μ i) hi).symm
  apply (FiniteMeasure.tendsto_normalize_iff_tendsto hν).1
  exact ⟨hn, NNReal.tendsto_coe.1 hm'⟩

end Problems.Juggler.BeattyPhase
