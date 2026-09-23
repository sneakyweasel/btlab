import Problems.Juggler.BeattyProfileGeometry
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Real

/-!
# Neighbourhood volume from complementary gaps

For a compact interval exhausted in measure by disjoint open gaps, the
neighbourhood volume of their complement is twice the radius plus the sum
of the gap lengths truncated at twice the radius. The theorem uses the
actual metric thickening, not a surrogate for neighbourhood volume.
-/

namespace Problems.Juggler.BeattyPhase

open Set MeasureTheory

private theorem thickening_gap_complement {K : Set ℝ} {a b : ℝ} {l w : ℕ → ℝ}
    (hK : K = Icc a b \ ⋃ n, Ioo (l n) (l n+w n))
    (ha : a ∈ K) (hb : b ∈ K)
    (he : ∀ n, l n ∈ K ∧ l n+w n ∈ K) {ε : ℝ} (hε : 0 < ε) :
    Metric.thickening ε K = Ioo (a-ε) (b+ε) \ ⋃ n, Icc (l n+ε) (l n+w n-ε) := by
  have hsub : K ⊆ Icc a b := by rw [hK]; exact sdiff_subset
  have hgap (n : ℕ) {z : ℝ} (hz : z ∈ K) : z ≤ l n ∨ l n+w n ≤ z := by
    have hz' := hz
    rw [hK] at hz'
    by_contra hh
    push Not at hh
    exact hz'.2 (mem_iUnion.2 ⟨n, hh⟩)
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.1 hx
    rw [Real.dist_eq, abs_lt] at hdist
    refine ⟨⟨by linarith [(hsub hz).1], by linarith [(hsub hz).2]⟩, ?_⟩
    intro hxcore
    obtain ⟨n, hn⟩ := mem_iUnion.1 hxcore
    rcases hgap n hz with hh | hh <;> linarith [hn.1, hn.2]
  · rintro ⟨hx, hcore⟩
    apply Metric.mem_thickening_iff.2
    by_cases hxa : x < a
    · exact ⟨a, ha, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1]⟩
    by_cases hxb : b < x
    · exact ⟨b, hb, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.2]⟩
    by_cases hxK : x ∈ K
    · exact ⟨x, hxK, by simpa using hε⟩
    have hg : x ∈ ⋃ n, Ioo (l n) (l n+w n) := by
      by_contra hh
      exact hxK (hK ▸ ⟨⟨le_of_not_gt hxa, le_of_not_gt hxb⟩, hh⟩)
    obtain ⟨n, hn⟩ := mem_iUnion.1 hg
    have hc : x ∉ Icc (l n+ε) (l n+w n-ε) := fun h => hcore (mem_iUnion.2 ⟨n,h⟩)
    by_cases hl : x < l n+ε
    · exact ⟨l n, (he n).1, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hn.1]⟩
    · have hr : l n+w n-ε < x := by
        by_contra hh
        exact hc ⟨le_of_not_gt hl, le_of_not_gt hh⟩
      exact ⟨l n+w n, (he n).2, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hn.2]⟩

/-- Exact real Lebesgue volume of the open metric neighbourhood of a gap
complement. The gaps exhaust the envelope length; all their endpoints
belong to the complement, and the open gaps are pairwise disjoint. -/
theorem volume_thickening_of_gap_lengths {K : Set ℝ} {a b : ℝ} {l w : ℕ → ℝ}
    (hK : K = Icc a b \ ⋃ n, Ioo (l n) (l n+w n))
    (ha : a ∈ K) (hb : b ∈ K)
    (he : ∀ n, l n ∈ K ∧ l n+w n ∈ K)
    (hd : Pairwise fun i j => Disjoint (Ioo (l i) (l i+w i)) (Ioo (l j) (l j+w j)))
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n) (hs : ∑' n, w n = b-a)
    {ε : ℝ} (hε : 0 < ε) :
    volume.real (Metric.thickening ε K) = 2*ε + ∑' n, min (w n) (2*ε) := by
  let core (n : ℕ) := Icc (l n+ε) (l n+w n-ε)
  have hsub : K ⊆ Icc a b := by rw [hK]; exact sdiff_subset
  have hcore (n : ℕ) : core n ⊆ Ioo (l n) (l n+w n) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hdc : Pairwise (fun i j => Disjoint (core i) (core j)) := fun i j hij =>
    (hd hij).mono (hcore i) (hcore j)
  have hca : (⋃ n, core n) ⊆ Ioo (a-ε) (b+ε) := by
    intro x hx
    obtain ⟨n, hnmem⟩ := mem_iUnion.1 hx
    have hl := hsub (he n).1
    have hr := hsub (he n).2
    constructor <;> linarith [hnmem.1, hnmem.2, hl.1, hr.2]
  have hmax : Summable (fun n => max (w n-2*ε) 0) :=
    Summable.of_nonneg_of_le (fun _ => le_max_right _ _) (fun n => max_le (by linarith) (hn n)) hw
  have hmin : Summable (fun n => min (w n) (2*ε)) :=
    Summable.of_nonneg_of_le (fun n => le_min (hn n) (by positivity)) (fun _ => min_le_left _ _) hw
  have hvol : volume.real (⋃ n, core n) = ∑' n, max (w n-2*ε) 0 := by
    rw [measureReal_def, measure_iUnion hdc (fun _ => measurableSet_Icc)]
    have hv (n : ℕ) : volume (core n) = ENNReal.ofReal (max (w n-2*ε) 0) := by
      simp only [core, Real.volume_Icc]
      rw [show l n+w n-ε-(l n+ε) = w n-2*ε by ring, ENNReal.ofReal_max]
      simp
    simp_rw [hv]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => le_max_right _ _) hmax,
      ENNReal.toReal_ofReal (tsum_nonneg fun _ => le_max_right _ _)]
  have hsum : (∑' n, max (w n-2*ε) 0) + (∑' n, min (w n) (2*ε)) = b-a := by
    rw [← hmax.tsum_add hmin, ← hs]
    apply tsum_congr
    intro n
    by_cases hh : w n ≤ 2*ε
    · rw [min_eq_left hh, max_eq_right (by linarith)]; ring
    · rw [min_eq_right (le_of_not_ge hh), max_eq_left (by linarith)]; ring
  rw [thickening_gap_complement hK ha hb he hε,
    measureReal_sdiff hca (MeasurableSet.iUnion fun _ => measurableSet_Icc)
      (by simp [Real.volume_Ioo]), hvol]
  rw [Real.volume_real_Ioo]
  have hab := (hsub ha).2
  rw [max_eq_left (by linarith : 0 ≤ b+ε-(a-ε))]
  linarith

end Problems.Juggler.BeattyPhase
