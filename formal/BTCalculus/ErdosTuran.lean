import BTCalculus.FejerBox

/-! # The Erdős–Turán inequality with main term `N/H`

For points `z 0, …, z (N-1)` on the unit circle and a cutoff `H ≥ 3`, every
half-open arc `[a, b)` of length at most one satisfies

`|#{n < N : z n ∈ [a, b)} - N (b - a)| ≤ 8 N / (H + 1) + 2 ∑_{0 < |k| ≤ H} |S_k| / |k|`,

where `S_k = ∑_{n<N} e(k z n)`. This is `arc_error_le`, and `arc_error_le_of_modes`
is the form with one-sided mode bounds `|S_{±h}| ≤ B h`.

The smoothing is the Fejér kernel of `BTCalculus.FejerKernel`. The main term is
`N/H`, not `N/√H` as in `BTCalculus.FejerWeighted`, because the smoothed count is
compared with the extreme discrepancy `extremeError` rather than with `N`: a
translate of the expanded arc still has count at least its length times `N`
minus the extreme discrepancy. With radius `δ = 2/(H+1)` the Fejér tail mass
is `1/4`, and the self-referential bound closes with a factor two.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace BTCalculus.ErdosTuran

open Finset Set MeasureTheory
open BTCalculus.FejerKernel BTCalculus.FejerArc BTCalculus.FejerBox

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The number of the first `N` samples that lie in `S`, as a real number. -/
def sampleCount (z : ℕ → UnitAddCircle) (N : ℕ) (S : Set UnitAddCircle) : ℝ :=
  ∑ n ∈ range N, if z n ∈ S then (1 : ℝ) else 0

/-- The signed discrepancy of the half-open arc `[a, b)`: count minus `N (b - a)`. -/
def arcError (z : ℕ → UnitAddCircle) (N : ℕ) (a b : ℝ) : ℝ :=
  sampleCount z N (arc a b) - N * (b - a)

/-- The extreme discrepancy: the supremum of `|arcError|` over arcs of length at most one. -/
def extremeError (z : ℕ → UnitAddCircle) (N : ℕ) : ℝ :=
  sSup {d | ∃ a b : ℝ, a ≤ b ∧ b ≤ a + 1 ∧ d = |arcError z N a b|}

/-- The weighted exponential-sum term `∑_{0 < |k| ≤ H} |S_k| / |k|`. -/
def modeSum (z : ℕ → UnitAddCircle) (N H : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(H : ℤ)) H,
    if k = 0 then 0 else ‖∑ n ∈ range N, fourier k (z n)‖ / |(k : ℝ)|

/-- A sample count is nonnegative. -/
theorem sampleCount_nonneg (z : ℕ → UnitAddCircle) (N : ℕ) (S : Set UnitAddCircle) :
    0 ≤ sampleCount z N S :=
  sum_nonneg (fun n _ => by split_ifs <;> norm_num)

/-- A sample count is at most the number `N` of samples. -/
theorem sampleCount_le (z : ℕ → UnitAddCircle) (N : ℕ) (S : Set UnitAddCircle) :
    sampleCount z N S ≤ N := by
  calc sampleCount z N S ≤ ∑ _n ∈ range N, (1 : ℝ) :=
        sum_le_sum (fun n _ => by split_ifs <;> norm_num)
    _ = N := by simp

/-- Counts are monotone under membership implication on the samples. -/
theorem sampleCount_mono (z : ℕ → UnitAddCircle) (N : ℕ) {S T : Set UnitAddCircle}
    (h : ∀ n, z n ∈ S → z n ∈ T) : sampleCount z N S ≤ sampleCount z N T :=
  sum_le_sum (fun n _ => by
    by_cases hs : z n ∈ S
    · simp [hs, h n hs]
    · simp only [hs, if_false]; split_ifs <;> norm_num)

/-- One arc discrepancy is at most `N` in size. -/
theorem abs_arcError_le (z : ℕ → UnitAddCircle) (N : ℕ) {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ a + 1) : |arcError z N a b| ≤ N := by
  have h0 := sampleCount_nonneg z N (arc a b)
  have h1 := sampleCount_le z N (arc a b)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl : 0 ≤ (N : ℝ) * (b - a) := mul_nonneg hN (by linarith)
  have hu : (N : ℝ) * (b - a) ≤ N := by nlinarith
  rw [arcError, abs_le]
  constructor <;> linarith

/-- The arc discrepancies are bounded by `N`, so their supremum exists. -/
theorem bddAbove_arcErrors (z : ℕ → UnitAddCircle) (N : ℕ) :
    BddAbove {d | ∃ a b : ℝ, a ≤ b ∧ b ≤ a + 1 ∧ d = |arcError z N a b|} := by
  refine ⟨N, ?_⟩
  rintro d ⟨a, b, hab, hb, rfl⟩
  exact abs_arcError_le z N hab hb

/-- Every arc discrepancy is bounded by the extreme discrepancy. -/
theorem abs_arcError_le_extremeError (z : ℕ → UnitAddCircle) (N : ℕ) {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ a + 1) : |arcError z N a b| ≤ extremeError z N :=
  le_csSup (bddAbove_arcErrors z N) ⟨a, b, hab, hb, rfl⟩

/-- A uniform bound on arc discrepancies bounds the extreme discrepancy. -/
theorem extremeError_le (z : ℕ → UnitAddCircle) (N : ℕ) {D : ℝ}
    (h : ∀ a b : ℝ, a ≤ b → b ≤ a + 1 → |arcError z N a b| ≤ D) :
    extremeError z N ≤ D := by
  refine csSup_le ?_ ?_
  · exact ⟨|arcError z N 0 0|, 0, 0, le_rfl, by norm_num, rfl⟩
  · rintro d ⟨a, b, hab, hb, rfl⟩
    exact h a b hab hb

/-- Translating the sample by `s` translates the arc by `s`. -/
theorem sub_coe_mem_arc_iff {x : UnitAddCircle} {a b s : ℝ} :
    x - (s : UnitAddCircle) ∈ arc a b ↔ x ∈ arc (a + s) (b + s) := by
  constructor
  · rintro ⟨u, hu, hux⟩
    refine ⟨u + s, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
    change ((u + s : ℝ) : UnitAddCircle) = x
    change (u : UnitAddCircle) = x - (s : UnitAddCircle) at hux
    rw [QuotientAddGroup.mk_add, hux, sub_add_cancel]
  · rintro ⟨v, hv, hvx⟩
    refine ⟨v - s, ⟨by linarith [hv.1], by linarith [hv.2]⟩, ?_⟩
    change ((v - s : ℝ) : UnitAddCircle) = x - (s : UnitAddCircle)
    change (v : UnitAddCircle) = x at hvx
    rw [QuotientAddGroup.mk_sub, hvx]

/-- The count in every translate of an arc is within the extreme discrepancy of its length. -/
theorem abs_translate_count_sub_le (z : ℕ → UnitAddCircle) (N : ℕ) {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ a + 1) (t : UnitAddCircle) :
    |sampleCount z N {x | x - t ∈ arc a b} - N * (b - a)| ≤ extremeError z N := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hset : {x | x - (s : UnitAddCircle) ∈ arc a b} = arc (a + s) (b + s) := by
    ext x
    exact sub_coe_mem_arc_iff
  have h := abs_arcError_le_extremeError z N (a := a + s) (b := b + s)
    (by linarith) (by linarith)
  rw [arcError, show b + s - (a + s) = b - a by ring] at h
  change |sampleCount z N {x | x - (s : UnitAddCircle) ∈ arc a b} - _| ≤ _
  rw [hset]
  exact h

/-- The sampled Fejér smoothing is the kernel integral of the translated counts. -/
theorem sum_smoothSet_eq_integral (z : ℕ → UnitAddCircle) (N H : ℕ)
    {S : Set UnitAddCircle} (hS : MeasurableSet S) :
    (∑ n ∈ range N, smoothSet H S (z n)) =
      ∫ t, ∑ n ∈ range N, {t | z n - t ∈ S}.indicator (kernel H) t := by
  have hU (n : ℕ) : MeasurableSet {t : UnitAddCircle | z n - t ∈ S} :=
    hS.preimage (continuous_const.sub continuous_id).measurable
  rw [integral_finsetSum _ (fun n _ => (integrable_kernel H).indicator (hU n))]
  apply sum_congr rfl
  intro n _
  rw [smoothSet, MeasureTheory.integral_indicator (hU n)]

/-- At one kernel point, the summed indicators are the kernel times the translated count. -/
theorem sum_indicator_kernel (z : ℕ → UnitAddCircle) (N H : ℕ)
    (S : Set UnitAddCircle) (t : UnitAddCircle) :
    (∑ n ∈ range N, {t | z n - t ∈ S}.indicator (kernel H) t) =
      kernel H t * sampleCount z N {x | x - t ∈ S} := by
  rw [sampleCount, mul_sum]
  apply sum_congr rfl
  intro n _
  by_cases h : z n - t ∈ S <;> simp [Set.indicator, h]

/-- One row of the Fejér coefficient square meets each frequency in `[-H, H]` at most once. -/
theorem sum_row_le_sum_Icc {H i : ℕ} (hi : i ≤ H) {φ : ℤ → ℝ} (hφ : ∀ k, 0 ≤ φ k) :
    ∑ j ∈ range (H + 1), φ ((i : ℤ) - j) ≤ ∑ k ∈ Finset.Icc (-(H : ℤ)) H, φ k := by
  let s := (range (H + 1)).image (fun j : ℕ => (i : ℤ) - j)
  have he : (∑ j ∈ range (H + 1), φ ((i : ℤ) - j)) = ∑ k ∈ s, φ k := by
    symm
    apply sum_image
    intro j _ l _ h
    exact_mod_cast (sub_right_injective h)
  have hs : s ⊆ Finset.Icc (-(H : ℤ)) H := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
    have hj' := mem_range.mp hj
    simp only [Finset.mem_Icc]
    constructor <;> omega
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => hφ k)

/-- The sampled Fejér smoothing of an arc differs from `N` times its length by at
most the weighted mode sum. Each nonzero mode keeps its own weight `1/|k|`. -/
theorem abs_smooth_sub_le_modeSum (z : ℕ → UnitAddCircle) {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ a + 1) (H N : ℕ) :
    |(∑ n ∈ range N, smoothSet H (arc a b) (z n)) - N * (b - a)| ≤ modeSum z N H := by
  set S : ℤ → ℂ := fun k => ∑ n ∈ range N, fourier k (z n) with hSdef
  let φ : ℤ → ℝ := fun k => if k = 0 then 0 else ‖S k‖ / |(k : ℝ)|
  have hφ : ∀ k, 0 ≤ φ k := fun k => by
    dsimp only [φ]
    split_ifs
    · exact le_rfl
    · positivity
  have hS0 : S 0 = N := by simp [S]
  have he : ((∑ n ∈ range N, smoothSet H (arc a b) (z n) : ℝ) : ℂ) =
      ∑ p ∈ indices H, coefficient H a b p * S (frequency p) := by
    push_cast
    simp_rw [smooth_expansion, S, mul_sum]
    exact sum_comm
  have hm : (((N : ℝ) * (b - a) : ℝ) : ℂ) =
      ∑ p ∈ indices H, coefficient H a b p * ((if frequency p = 0 then 1 else 0) * N) := by
    simp_rw [← mul_assoc, ← sum_mul]
    rw [coefficient_zero_sum hab hb H]
    push_cast
    ring
  have hd : ‖(H : ℂ) + 1‖ = (H : ℝ) + 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hg (p : ℕ × ℕ) :
      ‖coefficient H a b p * (S (frequency p) - (if frequency p = 0 then 1 else 0) * N)‖ ≤
        φ (frequency p) / ((H : ℝ) + 1) := by
    by_cases hk : frequency p = 0
    · simp [hk, hS0, φ]
    · have hc := norm_arcCoeff_le hab hb hk
      simp only [hk, if_false, zero_mul, sub_zero, norm_mul, coefficient, norm_div, hd, φ]
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      calc ‖arcCoeff a b (frequency p)‖ * ‖S (frequency p)‖
          ≤ 1 / |((frequency p : ℤ) : ℝ)| * ‖S (frequency p)‖ :=
            mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ = ‖S (frequency p)‖ / |((frequency p : ℤ) : ℝ)| := by ring
  have hsum : ∑ p ∈ indices H, φ (frequency p) ≤ ((H : ℝ) + 1) * modeSum z N H := by
    have hrow : ∑ p ∈ indices H, φ (frequency p) ≤
        ∑ _i ∈ range (H + 1), ∑ k ∈ Finset.Icc (-(H : ℤ)) H, φ k := by
      simp only [indices, Finset.sum_product, frequency]
      exact sum_le_sum (fun i hi => sum_row_le_sum_Icc (Nat.le_of_lt_succ (mem_range.mp hi)) hφ)
    refine hrow.trans (le_of_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul]
    push_cast
    rfl
  have habs : |(∑ n ∈ range N, smoothSet H (arc a b) (z n)) - N * (b - a)| =
      ‖((∑ n ∈ range N, smoothSet H (arc a b) (z n) : ℝ) : ℂ) -
        (((N : ℝ) * (b - a) : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, he, hm, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc _ ≤ ∑ p ∈ indices H, ‖coefficient H a b p *
        (S (frequency p) - (if frequency p = 0 then 1 else 0) * N)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ indices H, φ (frequency p) / ((H : ℝ) + 1) := sum_le_sum (fun p _ => hg p)
    _ = (∑ p ∈ indices H, φ (frequency p)) / ((H : ℝ) + 1) := by rw [sum_div]
    _ ≤ modeSum z N H := by
      rw [div_le_iff₀ (by positivity)]
      linarith


/-- Fejér integration of a pointwise lower bound for the translated counts. -/
theorem integral_lower_le_sum_smooth (z : ℕ → UnitAddCircle) (N H : ℕ)
    {S : Set UnitAddCircle} (hS : MeasurableSet S) {δ c e : ℝ}
    (hpt : ∀ t : UnitAddCircle,
      c * kernel H t - e * {t : UnitAddCircle | δ ≤ ‖t‖}.indicator (kernel H) t ≤
        ∑ n ∈ range N, {t | z n - t ∈ S}.indicator (kernel H) t) :
    c - e * ∫ t in {t : UnitAddCircle | δ ≤ ‖t‖}, kernel H t ≤
      ∑ n ∈ range N, smoothSet H S (z n) := by
  have hV : MeasurableSet {t : UnitAddCircle | δ ≤ ‖t‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hU (n : ℕ) : MeasurableSet {t : UnitAddCircle | z n - t ∈ S} :=
    hS.preimage (continuous_const.sub continuous_id).measurable
  have hl : Integrable (fun t => c * kernel H t -
      e * {t : UnitAddCircle | δ ≤ ‖t‖}.indicator (kernel H) t) :=
    ((integrable_kernel H).const_mul c).sub (((integrable_kernel H).indicator hV).const_mul e)
  have hr : Integrable (fun t => ∑ n ∈ range N, {t | z n - t ∈ S}.indicator (kernel H) t) :=
    integrable_finsetSum _ (fun n _ => (integrable_kernel H).indicator (hU n))
  have hm := integral_mono hl hr hpt
  rw [integral_sub ((integrable_kernel H).const_mul c)
      (((integrable_kernel H).indicator hV).const_mul e),
    integral_const_mul, integral_const_mul, integral_kernel,
    MeasureTheory.integral_indicator hV, ← sum_smoothSet_eq_integral z N H hS] at hm
  simpa using hm

/-- Fejér integration of a pointwise upper bound for the translated counts. -/
theorem sum_smooth_le_integral_upper (z : ℕ → UnitAddCircle) (N H : ℕ)
    {S : Set UnitAddCircle} (hS : MeasurableSet S) {δ c e : ℝ}
    (hpt : ∀ t : UnitAddCircle,
      ∑ n ∈ range N, {t | z n - t ∈ S}.indicator (kernel H) t ≤
        c * kernel H t + e * {t : UnitAddCircle | δ ≤ ‖t‖}.indicator (kernel H) t) :
    ∑ n ∈ range N, smoothSet H S (z n) ≤
      c + e * ∫ t in {t : UnitAddCircle | δ ≤ ‖t‖}, kernel H t := by
  have hV : MeasurableSet {t : UnitAddCircle | δ ≤ ‖t‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hU (n : ℕ) : MeasurableSet {t : UnitAddCircle | z n - t ∈ S} :=
    hS.preimage (continuous_const.sub continuous_id).measurable
  have hl : Integrable (fun t => c * kernel H t +
      e * {t : UnitAddCircle | δ ≤ ‖t‖}.indicator (kernel H) t) :=
    ((integrable_kernel H).const_mul c).add (((integrable_kernel H).indicator hV).const_mul e)
  have hr : Integrable (fun t => ∑ n ∈ range N, {t | z n - t ∈ S}.indicator (kernel H) t) :=
    integrable_finsetSum _ (fun n _ => (integrable_kernel H).indicator (hU n))
  have hm := integral_mono hr hl hpt
  rw [integral_add ((integrable_kernel H).const_mul c)
      (((integrable_kernel H).indicator hV).const_mul e),
    integral_const_mul, integral_const_mul, integral_kernel,
    MeasureTheory.integral_indicator hV, ← sum_smoothSet_eq_integral z N H hS] at hm
  simpa using hm

/-- Upper half of the one-arc estimate. The expanded arc is compared with its
translates: near zero they contain `[a, b)`, far from zero they lose at most the
extreme discrepancy, and the far Fejér mass is at most `τ = 1/(2(H+1)δ)`. -/
theorem arcError_mul_le (z : ℕ → UnitAddCircle) (N H : ℕ) {a b δ : ℝ}
    (hab : a ≤ b) (hb : b ≤ a + 1) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    arcError z N a b * (1 - 1 / (2 * ((H : ℝ) + 1) * δ)) ≤
      modeSum z N H + 2 * N * δ + 1 / (2 * ((H : ℝ) + 1) * δ) * extremeError z N := by
  set τ := 1 / (2 * ((H : ℝ) + 1) * δ) with hτ
  set D := extremeError z N with hD
  set E := arcError z N a b with hE
  have hED : |E| ≤ D := abs_arcError_le_extremeError z N hab hb
  obtain ⟨-, -, h1, h2, -, hlen⟩ := saturated_lengths hab hb hδ.le
  set lo := a - δ
  set hi := min (b + δ) (a - δ + 1)
  have hcount : sampleCount z N (arc a b) = E + N * (b - a) := by
    simp only [hE, arcError]; ring
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNδ : 0 ≤ (N : ℝ) * δ := mul_nonneg hN hδ.le
  have hL := (abs_le.mp hlen).2
  have hNL : (N : ℝ) * (hi - lo) ≤ N * (b - a) + 2 * N * δ := by nlinarith
  have hsmooth := integral_lower_le_sum_smooth z N H (measurableSet_arc lo hi)
    (δ := δ) (c := N * (hi - lo) + E - 2 * N * δ) (e := E + D) (fun t => by
      rw [sum_indicator_kernel]
      have hk := kernel_nonneg H t
      by_cases ht : δ ≤ ‖t‖
      · rw [Set.indicator_of_mem (show t ∈ {t : UnitAddCircle | δ ≤ ‖t‖} from ht)]
        have hc := (abs_le.mp (abs_translate_count_sub_le z N h1 h2 t)).1
        have key : N * (hi - lo) + E - 2 * N * δ - (E + D) ≤
            sampleCount z N {x | x - t ∈ arc lo hi} := by linarith
        nlinarith [mul_le_mul_of_nonneg_left key hk]
      · rw [Set.indicator_of_notMem (show t ∉ {t : UnitAddCircle | δ ≤ ‖t‖} from ht)]
        have hmono : sampleCount z N (arc a b) ≤ sampleCount z N {x | x - t ∈ arc lo hi} :=
          sampleCount_mono z N (fun n hn => sub_mem_expanded hn (not_le.mp ht))
        have key : N * (hi - lo) + E - 2 * N * δ ≤
            sampleCount z N {x | x - t ∈ arc lo hi} := by linarith
        nlinarith [mul_le_mul_of_nonneg_left key hk])
  have htail := circle_tail_le H hδ hδh
  have hED0 : 0 ≤ E + D := by linarith [(abs_le.mp hED).1]
  have hmul := mul_le_mul_of_nonneg_left htail hED0
  have hT := (abs_le.mp (abs_smooth_sub_le_modeSum z h1 h2 H N)).2
  nlinarith

/-- Lower half of the one-arc estimate, with the contracted arc. -/
theorem neg_arcError_mul_le (z : ℕ → UnitAddCircle) (N H : ℕ) {a b δ : ℝ}
    (hab : a ≤ b) (hb : b ≤ a + 1) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    -arcError z N a b * (1 - 1 / (2 * ((H : ℝ) + 1) * δ)) ≤
      modeSum z N H + 2 * N * δ + 1 / (2 * ((H : ℝ) + 1) * δ) * extremeError z N := by
  set τ := 1 / (2 * ((H : ℝ) + 1) * δ) with hτ
  set D := extremeError z N with hD
  set E := arcError z N a b with hE
  have hED : |E| ≤ D := abs_arcError_le_extremeError z N hab hb
  obtain ⟨h1, h2, -, -, hlen, -⟩ := saturated_lengths hab hb hδ.le
  set lo := a + δ
  set hi := max (a + δ) (b - δ)
  have hcount : sampleCount z N (arc a b) = E + N * (b - a) := by
    simp only [hE, arcError]; ring
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNδ : 0 ≤ (N : ℝ) * δ := mul_nonneg hN hδ.le
  have hL := (abs_le.mp hlen).1
  have hNL : (N : ℝ) * (b - a) ≤ N * (hi - lo) + 2 * N * δ := by nlinarith
  have hsmooth := sum_smooth_le_integral_upper z N H (measurableSet_arc lo hi)
    (δ := δ) (c := N * (hi - lo) + E + 2 * N * δ) (e := D - E) (fun t => by
      rw [sum_indicator_kernel]
      have hk := kernel_nonneg H t
      by_cases ht : δ ≤ ‖t‖
      · rw [Set.indicator_of_mem (show t ∈ {t : UnitAddCircle | δ ≤ ‖t‖} from ht)]
        have hc := (abs_le.mp (abs_translate_count_sub_le z N h1 h2 t)).2
        have key : sampleCount z N {x | x - t ∈ arc lo hi} ≤
            N * (hi - lo) + E + 2 * N * δ + (D - E) := by linarith
        nlinarith [mul_le_mul_of_nonneg_left key hk]
      · rw [Set.indicator_of_notMem (show t ∉ {t : UnitAddCircle | δ ≤ ‖t‖} from ht)]
        have hmono : sampleCount z N {x | x - t ∈ arc lo hi} ≤ sampleCount z N (arc a b) :=
          sampleCount_mono z N (fun n hn => mem_of_sub_mem_contracted hn (not_le.mp ht))
        have key : sampleCount z N {x | x - t ∈ arc lo hi} ≤
            N * (hi - lo) + E + 2 * N * δ := by linarith
        nlinarith [mul_le_mul_of_nonneg_left key hk])
  have htail := circle_tail_le H hδ hδh
  have hED0 : 0 ≤ D - E := by linarith [(abs_le.mp hED).2]
  have hmul := mul_le_mul_of_nonneg_left htail hED0
  have hT := (abs_le.mp (abs_smooth_sub_le_modeSum z h1 h2 H N)).1
  nlinarith


/-- **Erdős–Turán, extreme form.** For `H ≥ 3`, the extreme arc discrepancy of
`N` circle points is at most `8N/(H+1) + 2 ∑_{0<|k|≤H} |S_k|/|k|`. -/
theorem extremeError_le_modeSum (z : ℕ → UnitAddCircle) (N : ℕ) {H : ℕ} (hH : 3 ≤ H) :
    extremeError z N ≤ 8 * N / ((H : ℝ) + 1) + 2 * modeSum z N H := by
  have hH1 : (4 : ℝ) ≤ (H : ℝ) + 1 := by
    have : (3 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  set δ : ℝ := 2 / ((H : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδh : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hτ : 1 / (2 * ((H : ℝ) + 1) * δ) = 1 / 4 := by
    rw [hδdef]
    field_simp
    ring
  have hNδ : 2 * (N : ℝ) * δ = 4 * N / ((H : ℝ) + 1) := by
    rw [hδdef]
    ring
  set D := extremeError z N
  set T := modeSum z N H
  have harc : ∀ a b : ℝ, a ≤ b → b ≤ a + 1 →
      |arcError z N a b| ≤ (4 / 3) * (T + 4 * N / ((H : ℝ) + 1)) + D / 3 := by
    intro a b hab hb
    have hu := arcError_mul_le z N H hab hb hδ hδh
    have hl := neg_arcError_mul_le z N H hab hb hδ hδh
    rw [hτ, hNδ] at hu hl
    rw [abs_le]
    constructor <;> linarith
  have hD : D ≤ (4 / 3) * (T + 4 * N / ((H : ℝ) + 1)) + D / 3 := extremeError_le z N harc
  have h8 : 8 * (N : ℝ) / ((H : ℝ) + 1) = 2 * (4 * N / ((H : ℝ) + 1)) := by ring
  rw [h8]
  linarith

/-- **Erdős–Turán inequality with main term `N/H`.** For `H ≥ 3` and every
half-open arc `[a, b)` of length at most one,
`|#{n < N : z n ∈ [a, b)} - N (b - a)| ≤ 8N/(H+1) + 2 ∑_{0<|k|≤H} |S_k|/|k|`. -/
theorem abs_arcError_le_modeSum (z : ℕ → UnitAddCircle) (N : ℕ) {H : ℕ} (hH : 3 ≤ H)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a + 1) :
    |arcError z N a b| ≤ 8 * N / ((H : ℝ) + 1) + 2 * modeSum z N H :=
  (abs_arcError_le_extremeError z N hab hb).trans (extremeError_le_modeSum z N hH)

/-- A sum over `[-H, H]` splits into the zero term and symmetric pairs. -/
theorem sum_Icc_neg_eq (ψ : ℤ → ℝ) (H : ℕ) :
    ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ψ k =
      ψ 0 + ∑ h ∈ Finset.Icc 1 H, (ψ h + ψ (-(h : ℤ))) := by
  induction H with
  | zero => simp
  | succ H ih =>
    have he : Finset.Icc (-((H + 1 : ℕ) : ℤ)) ((H + 1 : ℕ) : ℤ) =
        insert (-((H + 1 : ℕ) : ℤ)) (insert ((H + 1 : ℕ) : ℤ) (Finset.Icc (-(H : ℤ)) H)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    have hn : ((H + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(H : ℤ)) H := by simp
    have hm : (-((H + 1 : ℕ) : ℤ)) ∉ insert ((H + 1 : ℕ) : ℤ) (Finset.Icc (-(H : ℤ)) H) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
      omega
    rw [he, sum_insert hm, sum_insert hn, ih, sum_Icc_succ_top (by omega : 1 ≤ H + 1)]
    ring

/-- One-sided mode bounds `|S_{±h}| ≤ B h` turn the weighted mode sum into `2 ∑ B h / h`. -/
theorem modeSum_le_of_bound (z : ℕ → UnitAddCircle) (N H : ℕ) (B : ℕ → ℝ)
    (hB : ∀ h ∈ Finset.Icc 1 H,
      ‖∑ n ∈ range N, fourier (h : ℤ) (z n)‖ ≤ B h ∧
        ‖∑ n ∈ range N, fourier (-(h : ℤ)) (z n)‖ ≤ B h) :
    modeSum z N H ≤ 2 * ∑ h ∈ Finset.Icc 1 H, B h / h := by
  rw [modeSum, sum_Icc_neg_eq, mul_sum]
  simp only [if_true, zero_add]
  apply sum_le_sum
  intro h hh
  have h1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
  have hz : (h : ℤ) ≠ 0 := by omega
  have hpos : (0 : ℝ) < h := by exact_mod_cast h1
  obtain ⟨hp, hn⟩ := hB h hh
  simp only [hz, if_false, neg_ne_zero.mpr hz, Int.cast_neg, abs_neg, Int.cast_natCast,
    abs_of_pos hpos]
  rw [← add_div, mul_div_assoc', div_le_div_iff_of_pos_right hpos]
  linarith

/-- **Erdős–Turán with mode bounds.** If `|S_{±h}| ≤ B h` for `1 ≤ h ≤ H` and `H ≥ 3`,
then every arc of length at most one has discrepancy at most
`8N/(H+1) + 4 ∑_{h=1}^H B h / h`. -/
theorem abs_arcError_le_of_modes (z : ℕ → UnitAddCircle) (N : ℕ) {H : ℕ} (hH : 3 ≤ H)
    (B : ℕ → ℝ)
    (hB : ∀ h ∈ Finset.Icc 1 H,
      ‖∑ n ∈ range N, fourier (h : ℤ) (z n)‖ ≤ B h ∧
        ‖∑ n ∈ range N, fourier (-(h : ℤ)) (z n)‖ ≤ B h)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a + 1) :
    |arcError z N a b| ≤ 8 * N / ((H : ℝ) + 1) + 4 * ∑ h ∈ Finset.Icc 1 H, B h / h := by
  have h1 := abs_arcError_le_modeSum z N hH hab hb
  have h2 := modeSum_le_of_bound z N H B hB
  linarith

end BTCalculus.ErdosTuran
