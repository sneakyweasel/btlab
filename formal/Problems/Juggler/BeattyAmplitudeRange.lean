import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Algebra.Order.Field

/-!
# Interval ranges for closed paths with upward jumps

A lower semicontinuous function that is continuous from the left cannot
skip a value while moving downward. If its two endpoint values agree, its
range on the interval is order connected. Positive continuous tilts of
left-continuous monotone profiles supply the relevant semicontinuity.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set

/-- Multiplying a left-continuous monotone real function by a positive
continuous function preserves lower semicontinuity. Upward jumps are allowed. -/
theorem lowerSemicontinuous_mul_monotone_of_tendsto_left
    {F g : ℝ → ℝ} (hF : Monotone F)
    (hleft : ∀ x, Tendsto F (𝓝[<] x) (𝓝 (F x)))
    (hg : Continuous g) (hpos : ∀ x, 0 < g x) :
    LowerSemicontinuous (fun x => g x * F x) := by
  intro x c hc
  have ht : ∀ᶠ z in 𝓝[<] x, c < g x * F z :=
    (tendsto_const_nhds.mul (hleft x)).eventually (Ioi_mem_nhds hc)
  have hx : ∀ᶠ z in 𝓝[<] x, z < x := self_mem_nhdsWithin
  obtain ⟨z, hz, hcz⟩ := (hx.and ht).exists
  have ht' := (hg.mul_const (F z)).continuousAt.eventually (Ioi_mem_nhds hcz)
  filter_upwards [ht', Ioi_mem_nhds hz] with t hct hzt
  exact hct.trans_le (mul_le_mul_of_nonneg_left (hF hzt.le) (hpos t).le)

/-- Lower semicontinuity and left continuity give the intermediate-value
property in the downward direction, even when upward jumps occur. -/
theorem intermediate_value_downward_of_lowerSemicontinuous
    {f : ℝ → ℝ} (hsemi : LowerSemicontinuous f)
    (hleft : ∀ x, Tendsto f (𝓝[<] x) (𝓝 (f x)))
    {a b y : ℝ} (hab : a ≤ b) (hby : f b ≤ y) (hya : y ≤ f a) :
    ∃ c ∈ Icc a b, f c = y := by
  let s := Icc a b ∩ f ⁻¹' Iic y
  have hs : IsCompact s := isCompact_Icc.inter_right (hsemi.isClosed_preimage y)
  obtain ⟨c, hc, hleast⟩ := hs.exists_isLeast ⟨b, ⟨⟨hab, le_rfl⟩, hby⟩⟩
  refine ⟨c, hc.1, le_antisymm hc.2 ?_⟩
  rcases eq_or_lt_of_le hc.1.1 with h | h
  · simpa only [← h] using hya
  · apply isClosed_Ici.mem_of_tendsto (hleft c)
    have ha : ∀ᶠ t in 𝓝[<] c, a < t :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds h)
    filter_upwards [self_mem_nhdsWithin, ha]
      with t htc hat
    change y ≤ f t
    by_contra ht
    have hts : t ∈ s := ⟨⟨hat.le, htc.le.trans hc.1.2⟩, (not_le.mp ht).le⟩
    exact (not_le_of_gt htc) (hleast hts)

/-- A closed real path with only upward jumps has an interval as its
range. Both endpoint values must agree; continuity across upward jumps is not assumed. -/
theorem ordConnected_image_Icc_of_equal_endpoints
    {f : ℝ → ℝ} (hsemi : LowerSemicontinuous f)
    (hleft : ∀ x, Tendsto f (𝓝[<] x) (𝓝 (f x)))
    {a b : ℝ} (hend : f a = f b) :
    OrdConnected (f '' Icc a b) := by
  refine ⟨?_⟩
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩ z hz
  rcases le_total v u with hvu | huv
  · obtain ⟨c, hc, he⟩ := intermediate_value_downward_of_lowerSemicontinuous
      hsemi hleft hvu hz.1 hz.2
    exact ⟨c, ⟨hv.1.trans hc.1, hc.2.trans hu.2⟩, he⟩
  · by_cases hza : z ≤ f a
    · obtain ⟨c, hc, he⟩ := intermediate_value_downward_of_lowerSemicontinuous
        hsemi hleft hu.1 hz.1 hza
      exact ⟨c, ⟨hc.1, hc.2.trans hu.2⟩, he⟩
    · obtain ⟨c, hc, he⟩ := intermediate_value_downward_of_lowerSemicontinuous
        hsemi hleft hv.2 (hend ▸ (not_le.mp hza).le) hz.2
      exact ⟨c, ⟨hv.1.trans hc.1, hc.2⟩, he⟩

end Problems.Juggler.BeattyPhase
