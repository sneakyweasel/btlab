import BTCalculus.ErdosTuran

/-! # The two-dimensional Erdős–Turán–Koksma inequality with main term `N/H`

For points `z 0, …, z (N-1)` on the torus and a cutoff `H ≥ 7`, every half-open box
`[a, b) × [c, d)` with sides of length at most one satisfies

`|#{n < N : z n ∈ box} - N (b - a)(d - c)| ≤ 32 N / (H + 1) + 2 ∑ w(k) w(l) |S_{k,l}|`,

summed over `(k, l) ≠ (0, 0)` with `|k|, |l| ≤ H`, where `S_{k,l} = ∑_{n<N} e(k x_n + l y_n)`
and `w(k) = 1/max(1,|k|)` is `FejerArc.frequencyWeight`. This is `abs_boxError_le_modeSum`.

The argument is `BTCalculus.ErdosTuran` in each coordinate. The product Fejér kernel at
radius `δ = 4/(H+1)` puts mass at most `1/8` outside the `δ`-strip of each coordinate, so
at most `1/4` off the `δ`-square. Near the origin a translate of the expanded box contains
the box; elsewhere its count is within the extreme box discrepancy of its area. The
self-referential bound closes with a factor two. The double kernel integral is written as
two nested one-dimensional integrals, so no product measure is used.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace BTCalculus.ErdosTuranBox

open Finset Set MeasureTheory
open BTCalculus.FejerKernel BTCalculus.FejerArc BTCalculus.FejerBox BTCalculus.ErdosTuran

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Box counts and the extreme box discrepancy -/

/-- The number of the first `N` samples in `A × B`, as a real number. -/
def boxCount (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ)
    (A B : Set UnitAddCircle) : ℝ :=
  ∑ n ∈ range N, if (z n).1 ∈ A ∧ (z n).2 ∈ B then (1 : ℝ) else 0

/-- The signed discrepancy of the box `[a, b) × [c, d)`: count minus `N` times its area. -/
def boxError (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ) (a b c d : ℝ) : ℝ :=
  boxCount z N (arc a b) (arc c d) - N * ((b - a) * (d - c))

/-- The extreme box discrepancy: the supremum of `|boxError|` over boxes whose sides have
length at most one. -/
def extremeBoxError (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ) : ℝ :=
  sSup {e | ∃ a b c d : ℝ, a ≤ b ∧ b ≤ a + 1 ∧ c ≤ d ∧ d ≤ c + 1 ∧
    e = |boxError z N a b c d|}

/-- The weighted exponential-sum term `∑_{(k,l) ≠ 0} w(k) w(l) |S_{k,l}|` over
`|k|, |l| ≤ H`. -/
def boxModeSum (z : ℕ → UnitAddCircle × UnitAddCircle) (N H : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ∑ l ∈ Finset.Icc (-(H : ℤ)) H,
    if k = 0 ∧ l = 0 then 0 else
      frequencyWeight k * frequencyWeight l * ‖∑ n ∈ range N, mode k l (z n)‖

/-- The far indicator `[δ ≤ ‖t‖]` as a real number. -/
def farIndicator (δ : ℝ) (t : UnitAddCircle) : ℝ := if δ ≤ ‖t‖ then 1 else 0

/-- A box count is nonnegative. -/
theorem boxCount_nonneg (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ)
    (A B : Set UnitAddCircle) : 0 ≤ boxCount z N A B :=
  sum_nonneg (fun n _ => by split_ifs <;> norm_num)

/-- A box count is at most the number `N` of samples. -/
theorem boxCount_le (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ)
    (A B : Set UnitAddCircle) : boxCount z N A B ≤ N := by
  calc boxCount z N A B ≤ ∑ _n ∈ range N, (1 : ℝ) :=
        sum_le_sum (fun n _ => by split_ifs <;> norm_num)
    _ = N := by simp

/-- Box counts are monotone under membership implication on the samples. -/
theorem boxCount_mono (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ)
    {A B A' B' : Set UnitAddCircle}
    (h : ∀ n, (z n).1 ∈ A ∧ (z n).2 ∈ B → (z n).1 ∈ A' ∧ (z n).2 ∈ B') :
    boxCount z N A B ≤ boxCount z N A' B' :=
  sum_le_sum (fun n _ => by
    by_cases hs : (z n).1 ∈ A ∧ (z n).2 ∈ B
    · rw [if_pos hs, if_pos (h n hs)]
    · rw [if_neg hs]
      split_ifs <;> norm_num)

/-- One box discrepancy is at most `N` in size. -/
theorem abs_boxError_le (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ) {a b c d : ℝ}
    (hab : a ≤ b) (hb : b ≤ a + 1) (hcd : c ≤ d) (hd : d ≤ c + 1) :
    |boxError z N a b c d| ≤ N := by
  have h0 := boxCount_nonneg z N (arc a b) (arc c d)
  have h1 := boxCount_le z N (arc a b) (arc c d)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hx0 : 0 ≤ b - a := by linarith
  have hy0 : 0 ≤ d - c := by linarith
  have ha0 : 0 ≤ (b - a) * (d - c) := mul_nonneg hx0 hy0
  have ha1 : (b - a) * (d - c) ≤ 1 := by nlinarith
  have hl : 0 ≤ (N : ℝ) * ((b - a) * (d - c)) := mul_nonneg hN ha0
  have hu : (N : ℝ) * ((b - a) * (d - c)) ≤ N := by nlinarith
  rw [boxError, abs_le]
  constructor <;> linarith

/-- The box discrepancies are bounded by `N`, so their supremum exists. -/
theorem bddAbove_boxErrors (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ) :
    BddAbove {e | ∃ a b c d : ℝ, a ≤ b ∧ b ≤ a + 1 ∧ c ≤ d ∧ d ≤ c + 1 ∧
      e = |boxError z N a b c d|} := by
  refine ⟨N, ?_⟩
  rintro e ⟨a, b, c, d, hab, hb, hcd, hd, rfl⟩
  exact abs_boxError_le z N hab hb hcd hd

/-- Every box discrepancy is bounded by the extreme box discrepancy. -/
theorem abs_boxError_le_extremeBoxError (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ)
    {a b c d : ℝ} (hab : a ≤ b) (hb : b ≤ a + 1) (hcd : c ≤ d) (hd : d ≤ c + 1) :
    |boxError z N a b c d| ≤ extremeBoxError z N :=
  le_csSup (bddAbove_boxErrors z N) ⟨a, b, c, d, hab, hb, hcd, hd, rfl⟩

/-- A uniform bound on box discrepancies bounds the extreme box discrepancy. -/
theorem extremeBoxError_le (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ) {D : ℝ}
    (h : ∀ a b c d : ℝ, a ≤ b → b ≤ a + 1 → c ≤ d → d ≤ c + 1 →
      |boxError z N a b c d| ≤ D) :
    extremeBoxError z N ≤ D := by
  refine csSup_le ?_ ?_
  · exact ⟨|boxError z N 0 0 0 0|, 0, 0, 0, 0, le_rfl, by norm_num, le_rfl, by norm_num, rfl⟩
  · rintro e ⟨a, b, c, d, hab, hb, hcd, hd, rfl⟩
    exact h a b c d hab hb hcd hd

/-- The count in every translate of a box is within the extreme box discrepancy of its
area. -/
theorem abs_translate_boxCount_sub_le (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ)
    {a b c d : ℝ} (hab : a ≤ b) (hb : b ≤ a + 1) (hcd : c ≤ d) (hd : d ≤ c + 1)
    (t u : UnitAddCircle) :
    |boxCount z N {x | x - t ∈ arc a b} {x | x - u ∈ arc c d} - N * ((b - a) * (d - c))| ≤
      extremeBoxError z N := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective u
  have h1 : {x | x - (s : UnitAddCircle) ∈ arc a b} = arc (a + s) (b + s) := by
    ext x
    exact sub_coe_mem_arc_iff
  have h2 : {x | x - (r : UnitAddCircle) ∈ arc c d} = arc (c + r) (d + r) := by
    ext x
    exact sub_coe_mem_arc_iff
  have h := abs_boxError_le_extremeBoxError z N (a := a + s) (b := b + s) (c := c + r)
    (d := d + r) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [boxError, show b + s - (a + s) = b - a by ring, show d + r - (c + r) = d - c by ring] at h
  change |boxCount z N {x | x - (s : UnitAddCircle) ∈ arc a b}
    {x | x - (r : UnitAddCircle) ∈ arc c d} - _| ≤ _
  rw [h1, h2]
  exact h

/-! ## Fejér integration against the kernel -/

/-- Kernel integration of a pointwise lower bound `c K - e [far] K ≤ f`. -/
theorem kernel_lower_le_integral (H : ℕ) {f : UnitAddCircle → ℝ} (hf : Integrable f)
    {δ c e : ℝ}
    (hpt : ∀ t, c * kernel H t - e * {t : UnitAddCircle | δ ≤ ‖t‖}.indicator (kernel H) t ≤
      f t) :
    c - e * ∫ t in {t : UnitAddCircle | δ ≤ ‖t‖}, kernel H t ≤ ∫ t, f t := by
  have hV : MeasurableSet {t : UnitAddCircle | δ ≤ ‖t‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hl : Integrable (fun t => c * kernel H t -
      e * {t : UnitAddCircle | δ ≤ ‖t‖}.indicator (kernel H) t) :=
    ((integrable_kernel H).const_mul c).sub (((integrable_kernel H).indicator hV).const_mul e)
  have hm := integral_mono hl hf hpt
  rw [integral_sub ((integrable_kernel H).const_mul c)
      (((integrable_kernel H).indicator hV).const_mul e),
    integral_const_mul, integral_const_mul, integral_kernel,
    MeasureTheory.integral_indicator hV] at hm
  simpa using hm

/-- Kernel integration of a pointwise upper bound `f ≤ c K + e [far] K`. -/
theorem integral_le_kernel_upper (H : ℕ) {f : UnitAddCircle → ℝ} (hf : Integrable f)
    {δ c e : ℝ}
    (hpt : ∀ t, f t ≤
      c * kernel H t + e * {t : UnitAddCircle | δ ≤ ‖t‖}.indicator (kernel H) t) :
    ∫ t, f t ≤ c + e * ∫ t in {t : UnitAddCircle | δ ≤ ‖t‖}, kernel H t := by
  have hV : MeasurableSet {t : UnitAddCircle | δ ≤ ‖t‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hl : Integrable (fun t => c * kernel H t +
      e * {t : UnitAddCircle | δ ≤ ‖t‖}.indicator (kernel H) t) :=
    ((integrable_kernel H).const_mul c).add (((integrable_kernel H).indicator hV).const_mul e)
  have hm := integral_mono hf hl hpt
  rw [integral_add ((integrable_kernel H).const_mul c)
      (((integrable_kernel H).indicator hV).const_mul e),
    integral_const_mul, integral_const_mul, integral_kernel,
    MeasureTheory.integral_indicator hV] at hm
  simpa using hm

/-- The far part of the kernel is the far indicator times the kernel. -/
theorem far_indicator_kernel (H : ℕ) (δ : ℝ) (t : UnitAddCircle) :
    {t : UnitAddCircle | δ ≤ ‖t‖}.indicator (kernel H) t = farIndicator δ t * kernel H t := by
  by_cases h : δ ≤ ‖t‖
  · simp [Set.indicator, farIndicator, h]
  · simp [Set.indicator, farIndicator, h]

/-- The sampled product smoothing, integrated over the first coordinate. -/
theorem sum_smooth_product_eq_integral (z : ℕ → UnitAddCircle × UnitAddCircle) (N H : ℕ)
    {A B : Set UnitAddCircle} (hA : MeasurableSet A) :
    (∑ n ∈ range N, smoothSet H A (z n).1 * smoothSet H B (z n).2) =
      ∫ t, ∑ n ∈ range N,
        {t | (z n).1 - t ∈ A}.indicator (kernel H) t * smoothSet H B (z n).2 := by
  have hU (n : ℕ) : MeasurableSet {t : UnitAddCircle | (z n).1 - t ∈ A} :=
    hA.preimage (continuous_const.sub continuous_id).measurable
  rw [integral_finsetSum _ (fun n _ => ((integrable_kernel H).indicator (hU n)).mul_const _)]
  apply sum_congr rfl
  intro n _
  rw [integral_mul_const, smoothSet, MeasureTheory.integral_indicator (hU n)]

/-- The weighted smoothing in the second coordinate, integrated. -/
theorem sum_weighted_smooth_eq_integral (z : ℕ → UnitAddCircle × UnitAddCircle) (N H : ℕ)
    {B : Set UnitAddCircle} (hB : MeasurableSet B) (w : ℕ → ℝ) :
    (∑ n ∈ range N, w n * smoothSet H B (z n).2) =
      ∫ u, ∑ n ∈ range N, w n * {u | (z n).2 - u ∈ B}.indicator (kernel H) u := by
  have hU (n : ℕ) : MeasurableSet {u : UnitAddCircle | (z n).2 - u ∈ B} :=
    hB.preimage (continuous_const.sub continuous_id).measurable
  rw [integral_finsetSum _ (fun n _ => ((integrable_kernel H).indicator (hU n)).const_mul _)]
  apply sum_congr rfl
  intro n _
  rw [integral_const_mul, smoothSet, MeasureTheory.integral_indicator (hU n)]

/-- At one pair of kernel points, the summed indicators are the two kernels times the
translated box count. -/
theorem sum_indicator_box (z : ℕ → UnitAddCircle × UnitAddCircle) (N H : ℕ)
    (A B : Set UnitAddCircle) (t u : UnitAddCircle) :
    (∑ n ∈ range N, (if (z n).1 - t ∈ A then (1 : ℝ) else 0) *
        {u | (z n).2 - u ∈ B}.indicator (kernel H) u) =
      kernel H u * boxCount z N {x | x - t ∈ A} {x | x - u ∈ B} := by
  rw [boxCount, mul_sum]
  apply sum_congr rfl
  intro n _
  by_cases h1 : (z n).1 - t ∈ A <;> by_cases h2 : (z n).2 - u ∈ B <;>
    simp [Set.indicator, h1, h2]

/-- The first-coordinate indicators times the second smoothing. -/
theorem sum_indicator_smooth (z : ℕ → UnitAddCircle × UnitAddCircle) (N H : ℕ)
    (A B : Set UnitAddCircle) (t : UnitAddCircle) :
    (∑ n ∈ range N, {t | (z n).1 - t ∈ A}.indicator (kernel H) t * smoothSet H B (z n).2) =
      kernel H t * ∑ n ∈ range N,
        (if (z n).1 - t ∈ A then (1 : ℝ) else 0) * smoothSet H B (z n).2 := by
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  by_cases h1 : (z n).1 - t ∈ A <;> simp [Set.indicator, h1]

/-- **Double Fejér integration, lower form.** A pointwise lower bound
`c - e ([t far] + [u far])` for the translated box counts integrates to
`c - 2 e ∫_far K`. -/
theorem smooth_product_lower (z : ℕ → UnitAddCircle × UnitAddCircle) (N H : ℕ)
    {A B : Set UnitAddCircle} (hA : MeasurableSet A) (hB : MeasurableSet B) {δ c e : ℝ}
    (hpt : ∀ t u : UnitAddCircle, c - e * (farIndicator δ t + farIndicator δ u) ≤
      boxCount z N {x | x - t ∈ A} {x | x - u ∈ B}) :
    c - 2 * e * ∫ t in {t : UnitAddCircle | δ ≤ ‖t‖}, kernel H t ≤
      ∑ n ∈ range N, smoothSet H A (z n).1 * smoothSet H B (z n).2 := by
  set τ := ∫ t in {t : UnitAddCircle | δ ≤ ‖t‖}, kernel H t with hτ
  have hUA (n : ℕ) : MeasurableSet {t : UnitAddCircle | (z n).1 - t ∈ A} :=
    hA.preimage (continuous_const.sub continuous_id).measurable
  have hUB (n : ℕ) : MeasurableSet {u : UnitAddCircle | (z n).2 - u ∈ B} :=
    hB.preimage (continuous_const.sub continuous_id).measurable
  have hinner : ∀ t : UnitAddCircle, c - e * farIndicator δ t - e * τ ≤
      ∑ n ∈ range N, (if (z n).1 - t ∈ A then (1 : ℝ) else 0) * smoothSet H B (z n).2 := by
    intro t
    rw [sum_weighted_smooth_eq_integral z N H hB]
    have hint : Integrable (fun u => ∑ n ∈ range N, (if (z n).1 - t ∈ A then (1 : ℝ) else 0) *
        {u | (z n).2 - u ∈ B}.indicator (kernel H) u) :=
      integrable_finsetSum _ (fun n _ => ((integrable_kernel H).indicator (hUB n)).const_mul _)
    have h := kernel_lower_le_integral H hint (δ := δ) (c := c - e * farIndicator δ t) (e := e)
      (fun u => by
        rw [sum_indicator_box, far_indicator_kernel]
        have hk := kernel_nonneg H u
        calc (c - e * farIndicator δ t) * kernel H u - e * (farIndicator δ u * kernel H u)
            = kernel H u * (c - e * (farIndicator δ t + farIndicator δ u)) := by ring
          _ ≤ kernel H u * boxCount z N {x | x - t ∈ A} {x | x - u ∈ B} :=
            mul_le_mul_of_nonneg_left (hpt t u) hk)
    linarith
  rw [sum_smooth_product_eq_integral z N H hA]
  have hint : Integrable (fun t => ∑ n ∈ range N,
      {t | (z n).1 - t ∈ A}.indicator (kernel H) t * smoothSet H B (z n).2) :=
    integrable_finsetSum _ (fun n _ => ((integrable_kernel H).indicator (hUA n)).mul_const _)
  have h := kernel_lower_le_integral H hint (δ := δ) (c := c - e * τ) (e := e) (fun t => by
    rw [sum_indicator_smooth, far_indicator_kernel]
    have hk := kernel_nonneg H t
    calc (c - e * τ) * kernel H t - e * (farIndicator δ t * kernel H t)
        = kernel H t * (c - e * farIndicator δ t - e * τ) := by ring
      _ ≤ kernel H t * ∑ n ∈ range N,
          (if (z n).1 - t ∈ A then (1 : ℝ) else 0) * smoothSet H B (z n).2 :=
        mul_le_mul_of_nonneg_left (hinner t) hk)
  linarith

/-- **Double Fejér integration, upper form.** A pointwise upper bound
`c + e ([t far] + [u far])` for the translated box counts integrates to
`c + 2 e ∫_far K`. -/
theorem smooth_product_upper (z : ℕ → UnitAddCircle × UnitAddCircle) (N H : ℕ)
    {A B : Set UnitAddCircle} (hA : MeasurableSet A) (hB : MeasurableSet B) {δ c e : ℝ}
    (hpt : ∀ t u : UnitAddCircle, boxCount z N {x | x - t ∈ A} {x | x - u ∈ B} ≤
      c + e * (farIndicator δ t + farIndicator δ u)) :
    ∑ n ∈ range N, smoothSet H A (z n).1 * smoothSet H B (z n).2 ≤
      c + 2 * e * ∫ t in {t : UnitAddCircle | δ ≤ ‖t‖}, kernel H t := by
  set τ := ∫ t in {t : UnitAddCircle | δ ≤ ‖t‖}, kernel H t with hτ
  have hUA (n : ℕ) : MeasurableSet {t : UnitAddCircle | (z n).1 - t ∈ A} :=
    hA.preimage (continuous_const.sub continuous_id).measurable
  have hUB (n : ℕ) : MeasurableSet {u : UnitAddCircle | (z n).2 - u ∈ B} :=
    hB.preimage (continuous_const.sub continuous_id).measurable
  have hinner : ∀ t : UnitAddCircle,
      ∑ n ∈ range N, (if (z n).1 - t ∈ A then (1 : ℝ) else 0) * smoothSet H B (z n).2 ≤
        c + e * farIndicator δ t + e * τ := by
    intro t
    rw [sum_weighted_smooth_eq_integral z N H hB]
    have hint : Integrable (fun u => ∑ n ∈ range N, (if (z n).1 - t ∈ A then (1 : ℝ) else 0) *
        {u | (z n).2 - u ∈ B}.indicator (kernel H) u) :=
      integrable_finsetSum _ (fun n _ => ((integrable_kernel H).indicator (hUB n)).const_mul _)
    have h := integral_le_kernel_upper H hint (δ := δ) (c := c + e * farIndicator δ t) (e := e)
      (fun u => by
        rw [sum_indicator_box, far_indicator_kernel]
        have hk := kernel_nonneg H u
        calc kernel H u * boxCount z N {x | x - t ∈ A} {x | x - u ∈ B}
            ≤ kernel H u * (c + e * (farIndicator δ t + farIndicator δ u)) :=
              mul_le_mul_of_nonneg_left (hpt t u) hk
          _ = (c + e * farIndicator δ t) * kernel H u + e * (farIndicator δ u * kernel H u) := by
              ring)
    linarith
  rw [sum_smooth_product_eq_integral z N H hA]
  have hint : Integrable (fun t => ∑ n ∈ range N,
      {t | (z n).1 - t ∈ A}.indicator (kernel H) t * smoothSet H B (z n).2) :=
    integrable_finsetSum _ (fun n _ => ((integrable_kernel H).indicator (hUA n)).mul_const _)
  have h := integral_le_kernel_upper H hint (δ := δ) (c := c + e * τ) (e := e) (fun t => by
    rw [sum_indicator_smooth, far_indicator_kernel]
    have hk := kernel_nonneg H t
    calc kernel H t * ∑ n ∈ range N,
          (if (z n).1 - t ∈ A then (1 : ℝ) else 0) * smoothSet H B (z n).2
        ≤ kernel H t * (c + e * farIndicator δ t + e * τ) :=
          mul_le_mul_of_nonneg_left (hinner t) hk
      _ = (c + e * τ) * kernel H t + e * (farIndicator δ t * kernel H t) := by ring)
  linarith

/-! ## The smoothed box against its Fourier modes -/

/-- A sum over the Fejér index square meets each frequency in `[-H, H]` at most `H + 1`
times. -/
theorem sum_indices_le {H : ℕ} {φ : ℤ → ℝ} (hφ : ∀ k, 0 ≤ φ k) :
    ∑ p ∈ indices H, φ (frequency p) ≤ ((H : ℝ) + 1) * ∑ k ∈ Finset.Icc (-(H : ℤ)) H, φ k := by
  have hrow : ∑ p ∈ indices H, φ (frequency p) ≤
      ∑ _i ∈ range (H + 1), ∑ k ∈ Finset.Icc (-(H : ℤ)) H, φ k := by
    simp only [indices, Finset.sum_product, frequency]
    exact sum_le_sum (fun i hi => sum_row_le_sum_Icc (Nat.le_of_lt_succ (mem_range.mp hi)) hφ)
  refine hrow.trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  rfl

/-- The double version of `sum_indices_le`. -/
theorem sum_indices_sq_le {H : ℕ} {G : ℤ → ℤ → ℝ} (hG : ∀ k l, 0 ≤ G k l) :
    ∑ p ∈ indices H, ∑ q ∈ indices H, G (frequency p) (frequency q) ≤
      ((H : ℝ) + 1) ^ 2 *
        ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ∑ l ∈ Finset.Icc (-(H : ℤ)) H, G k l := by
  have hH : (0 : ℝ) ≤ (H : ℝ) + 1 := by positivity
  calc ∑ p ∈ indices H, ∑ q ∈ indices H, G (frequency p) (frequency q)
      ≤ ∑ p ∈ indices H, ((H : ℝ) + 1) *
          ∑ l ∈ Finset.Icc (-(H : ℤ)) H, G (frequency p) l :=
        sum_le_sum (fun p _ => sum_indices_le (fun l => hG _ l))
    _ = ((H : ℝ) + 1) * ∑ l ∈ Finset.Icc (-(H : ℤ)) H,
          ∑ p ∈ indices H, G (frequency p) l := by
        rw [← mul_sum, sum_comm]
    _ ≤ ((H : ℝ) + 1) * ∑ l ∈ Finset.Icc (-(H : ℤ)) H,
          ((H : ℝ) + 1) * ∑ k ∈ Finset.Icc (-(H : ℤ)) H, G k l :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum (fun l _ => sum_indices_le (fun k => hG k l))) hH
    _ = ((H : ℝ) + 1) ^ 2 *
          ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ∑ l ∈ Finset.Icc (-(H : ℤ)) H, G k l := by
        rw [← mul_sum, sum_comm, ← mul_assoc, sq]

/-- One Fejér coefficient is at most the frequency weight divided by `H + 1`. -/
theorem norm_coefficient_le {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a + 1) (H : ℕ)
    (p : ℕ × ℕ) :
    ‖coefficient H a b p‖ ≤ frequencyWeight (frequency p) / ((H : ℝ) + 1) := by
  have hd : ‖(H : ℂ) + 1‖ = (H : ℝ) + 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [coefficient, norm_div, hd]
  exact div_le_div_of_nonneg_right (norm_arcCoeff_le_weight hab hb _) (by positivity)

/-- A frequency weight is nonnegative. -/
theorem frequencyWeight_nonneg (k : ℤ) : 0 ≤ frequencyWeight k := by
  unfold frequencyWeight
  split_ifs
  · norm_num
  · positivity

/-- The sampled Fejér smoothing of a box differs from `N` times its area by at most the
weighted box mode sum. -/
theorem abs_smooth_box_sub_le (z : ℕ → UnitAddCircle × UnitAddCircle) {a b c d : ℝ}
    (hab : a ≤ b) (hb : b ≤ a + 1) (hcd : c ≤ d) (hd : d ≤ c + 1) (H N : ℕ) :
    |(∑ n ∈ range N, smoothSet H (arc a b) (z n).1 * smoothSet H (arc c d) (z n).2) -
        N * ((b - a) * (d - c))| ≤ boxModeSum z N H := by
  set S : ℤ → ℤ → ℂ := fun k l => ∑ n ∈ range N, mode k l (z n) with hSdef
  let main : ℤ → ℤ → ℂ := fun k l => (if k = 0 ∧ l = 0 then 1 else 0) * N
  let G : ℤ → ℤ → ℝ := fun k l =>
    if k = 0 ∧ l = 0 then 0 else frequencyWeight k * frequencyWeight l * ‖S k l‖
  have hG : ∀ k l, 0 ≤ G k l := fun k l => by
    dsimp only [G]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (frequencyWeight_nonneg k) (frequencyWeight_nonneg l))
        (norm_nonneg _)
  have hS0 : S 0 0 = N := by simp [S, mode]
  have he : ((∑ n ∈ range N, smoothSet H (arc a b) (z n).1 * smoothSet H (arc c d) (z n).2 :
        ℝ) : ℂ) =
      ∑ p ∈ indices H, ∑ q ∈ indices H,
        coefficient H a b p * coefficient H c d q * S (frequency p) (frequency q) := by
    have hbox (n : ℕ) : ((smoothSet H (arc a b) (z n).1 * smoothSet H (arc c d) (z n).2 : ℝ) :
        ℂ) = ∑ r ∈ indices H ×ˢ indices H,
          (coefficient H a b r.1 * coefficient H c d r.2) *
            mode (frequency r.1) (frequency r.2) (z n) :=
      boxSmooth_expansion H a b c d (z n)
    rw [Complex.ofReal_sum]
    simp_rw [hbox, Finset.sum_product, S, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl (fun p _ => ?_)
    rw [sum_comm]
  have hm : (((N : ℝ) * ((b - a) * (d - c)) : ℝ) : ℂ) =
      ∑ p ∈ indices H, ∑ q ∈ indices H,
        coefficient H a b p * coefficient H c d q * main (frequency p) (frequency q) := by
    have hsplit (p q : ℕ × ℕ) :
        coefficient H a b p * coefficient H c d q * main (frequency p) (frequency q) =
          (coefficient H a b p * (if frequency p = 0 then 1 else 0)) *
            (coefficient H c d q * (if frequency q = 0 then 1 else 0)) * N := by
      simp only [main]
      by_cases h1 : frequency p = 0 <;> by_cases h2 : frequency q = 0 <;> simp [h1, h2]
    simp_rw [hsplit, ← sum_mul, ← mul_sum, ← sum_mul]
    rw [coefficient_zero_sum hab hb H, coefficient_zero_sum hcd hd H]
    push_cast
    ring
  have hterm (p q : ℕ × ℕ) :
      ‖coefficient H a b p * coefficient H c d q *
          (S (frequency p) (frequency q) - main (frequency p) (frequency q))‖ ≤
        G (frequency p) (frequency q) / ((H : ℝ) + 1) ^ 2 := by
    by_cases h0 : frequency p = 0 ∧ frequency q = 0
    · simp only [G, main, h0, and_self, if_true, one_mul]
      rw [hS0, sub_self, mul_zero, norm_zero]
      simp
    · have hmain : main (frequency p) (frequency q) = 0 := by simp [main, h0]
      rw [hmain, sub_zero, norm_mul, norm_mul]
      simp only [G, h0, if_false]
      have h1 := norm_coefficient_le hab hb H p
      have h2 := norm_coefficient_le hcd hd H q
      have hw1 := frequencyWeight_nonneg (frequency p)
      have hw2 := frequencyWeight_nonneg (frequency q)
      have hHp : (0 : ℝ) < (H : ℝ) + 1 := by positivity
      calc ‖coefficient H a b p‖ * ‖coefficient H c d q‖ * ‖S (frequency p) (frequency q)‖
          ≤ (frequencyWeight (frequency p) / ((H : ℝ) + 1)) *
              (frequencyWeight (frequency q) / ((H : ℝ) + 1)) *
                ‖S (frequency p) (frequency q)‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (norm_nonneg _)
        _ = frequencyWeight (frequency p) * frequencyWeight (frequency q) *
              ‖S (frequency p) (frequency q)‖ / ((H : ℝ) + 1) ^ 2 := by
            field_simp
  have habs : |(∑ n ∈ range N, smoothSet H (arc a b) (z n).1 * smoothSet H (arc c d) (z n).2) -
      N * ((b - a) * (d - c))| =
      ‖((∑ n ∈ range N, smoothSet H (arc a b) (z n).1 * smoothSet H (arc c d) (z n).2 : ℝ) :
          ℂ) - (((N : ℝ) * ((b - a) * (d - c)) : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, he, hm, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib, ← mul_sub]
  have hHp : (0 : ℝ) < ((H : ℝ) + 1) ^ 2 := by positivity
  calc _ ≤ ∑ p ∈ indices H, ‖∑ q ∈ indices H, coefficient H a b p * coefficient H c d q *
          (S (frequency p) (frequency q) - main (frequency p) (frequency q))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ indices H, ∑ q ∈ indices H, ‖coefficient H a b p * coefficient H c d q *
          (S (frequency p) (frequency q) - main (frequency p) (frequency q))‖ :=
        sum_le_sum (fun p _ => norm_sum_le _ _)
    _ ≤ ∑ p ∈ indices H, ∑ q ∈ indices H,
          G (frequency p) (frequency q) / ((H : ℝ) + 1) ^ 2 :=
        sum_le_sum (fun p _ => sum_le_sum (fun q _ => hterm p q))
    _ = (∑ p ∈ indices H, ∑ q ∈ indices H, G (frequency p) (frequency q)) /
          ((H : ℝ) + 1) ^ 2 := by
        rw [sum_div]
        simp_rw [sum_div]
    _ ≤ boxModeSum z N H := by
        rw [div_le_iff₀ hHp]
        have h := sum_indices_sq_le (H := H) hG
        have hbm : boxModeSum z N H =
            ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ∑ l ∈ Finset.Icc (-(H : ℤ)) H, G k l := rfl
        rw [hbm]
        linarith

/-! ## The two halves and the inequality -/

/-- Upper half of the one-box estimate, with the expanded box. -/
theorem boxError_mul_le (z : ℕ → UnitAddCircle × UnitAddCircle) (N H : ℕ) {a b c d δ : ℝ}
    (hab : a ≤ b) (hb : b ≤ a + 1) (hcd : c ≤ d) (hd : d ≤ c + 1)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    boxError z N a b c d * (1 - 2 * (1 / (2 * ((H : ℝ) + 1) * δ))) ≤
      boxModeSum z N H + 4 * N * δ +
        2 * (1 / (2 * ((H : ℝ) + 1) * δ)) * extremeBoxError z N := by
  set τ := 1 / (2 * ((H : ℝ) + 1) * δ) with hτ
  set D := extremeBoxError z N with hD
  set E := boxError z N a b c d with hE
  have hED : |E| ≤ D := abs_boxError_le_extremeBoxError z N hab hb hcd hd
  obtain ⟨-, -, h1, h2, -, hlen1⟩ := saturated_lengths hab hb hδ.le
  obtain ⟨-, -, h3, h4, -, hlen2⟩ := saturated_lengths hcd hd hδ.le
  set lo1 := a - δ
  set hi1 := min (b + δ) (a - δ + 1)
  set lo2 := c - δ
  set hi2 := min (d + δ) (c - δ + 1)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNδ : 0 ≤ (N : ℝ) * δ := mul_nonneg hN hδ.le
  have harea : |(hi1 - lo1) * (hi2 - lo2) - (b - a) * (d - c)| ≤ 2 * (2 * δ) :=
    product_volume_error ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hlen1 hlen2
  have hNa : (N : ℝ) * ((hi1 - lo1) * (hi2 - lo2)) ≤ N * ((b - a) * (d - c)) + 4 * N * δ := by
    nlinarith [(abs_le.mp harea).2]
  have hcount : boxCount z N (arc a b) (arc c d) = E + N * ((b - a) * (d - c)) := by
    simp only [hE, boxError]
    ring
  have hsm := smooth_product_lower z N H (measurableSet_arc lo1 hi1) (measurableSet_arc lo2 hi2)
    (δ := δ) (c := N * ((hi1 - lo1) * (hi2 - lo2)) + E - 4 * N * δ) (e := E + D)
    (fun t u => by
      have hED0 : 0 ≤ E + D := by linarith [(abs_le.mp hED).1]
      by_cases ht : δ ≤ ‖t‖
      · have hc := (abs_le.mp (abs_translate_boxCount_sub_le z N h1 h2 h3 h4 t u)).1
        have hf : 1 ≤ farIndicator δ t + farIndicator δ u := by
          have hu0 : 0 ≤ farIndicator δ u := by
            unfold farIndicator
            split_ifs <;> norm_num
          have ht1 : farIndicator δ t = 1 := by simp [farIndicator, ht]
          linarith
        have hmulf := mul_le_mul_of_nonneg_left hf hED0
        linarith
      · by_cases hu : δ ≤ ‖u‖
        · have hc := (abs_le.mp (abs_translate_boxCount_sub_le z N h1 h2 h3 h4 t u)).1
          have hf : 1 ≤ farIndicator δ t + farIndicator δ u := by
            simp only [farIndicator, if_pos hu, if_neg ht]
            norm_num
          have hmulf := mul_le_mul_of_nonneg_left hf hED0
          linarith
        · have hf : farIndicator δ t + farIndicator δ u = 0 := by
            simp only [farIndicator, if_neg hu, if_neg ht]
            norm_num
          have hmono : boxCount z N (arc a b) (arc c d) ≤
              boxCount z N {x | x - t ∈ arc lo1 hi1} {x | x - u ∈ arc lo2 hi2} :=
            boxCount_mono z N (fun n hn =>
              ⟨sub_mem_expanded hn.1 (not_le.mp ht), sub_mem_expanded hn.2 (not_le.mp hu)⟩)
          rw [hf, mul_zero, sub_zero]
          linarith)
  have htail := circle_tail_le H hδ hδh
  have hED0 : 0 ≤ E + D := by linarith [(abs_le.mp hED).1]
  have hmul := mul_le_mul_of_nonneg_left htail hED0
  have hT := (abs_le.mp (abs_smooth_box_sub_le z (a := lo1) (b := hi1) (c := lo2) (d := hi2)
    h1 h2 h3 h4 H N)).2
  nlinarith

/-- Lower half of the one-box estimate, with the contracted box. -/
theorem neg_boxError_mul_le (z : ℕ → UnitAddCircle × UnitAddCircle) (N H : ℕ)
    {a b c d δ : ℝ} (hab : a ≤ b) (hb : b ≤ a + 1) (hcd : c ≤ d) (hd : d ≤ c + 1)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    -boxError z N a b c d * (1 - 2 * (1 / (2 * ((H : ℝ) + 1) * δ))) ≤
      boxModeSum z N H + 4 * N * δ +
        2 * (1 / (2 * ((H : ℝ) + 1) * δ)) * extremeBoxError z N := by
  set τ := 1 / (2 * ((H : ℝ) + 1) * δ) with hτ
  set D := extremeBoxError z N with hD
  set E := boxError z N a b c d with hE
  have hED : |E| ≤ D := abs_boxError_le_extremeBoxError z N hab hb hcd hd
  obtain ⟨h1, h2, -, -, hlen1, -⟩ := saturated_lengths hab hb hδ.le
  obtain ⟨h3, h4, -, -, hlen2, -⟩ := saturated_lengths hcd hd hδ.le
  set lo1 := a + δ
  set hi1 := max (a + δ) (b - δ)
  set lo2 := c + δ
  set hi2 := max (c + δ) (d - δ)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNδ : 0 ≤ (N : ℝ) * δ := mul_nonneg hN hδ.le
  have harea : |(hi1 - lo1) * (hi2 - lo2) - (b - a) * (d - c)| ≤ 2 * (2 * δ) :=
    product_volume_error ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hlen1 hlen2
  have hNa : (N : ℝ) * ((b - a) * (d - c)) ≤ N * ((hi1 - lo1) * (hi2 - lo2)) + 4 * N * δ := by
    nlinarith [(abs_le.mp harea).1]
  have hcount : boxCount z N (arc a b) (arc c d) = E + N * ((b - a) * (d - c)) := by
    simp only [hE, boxError]
    ring
  have hsm := smooth_product_upper z N H (measurableSet_arc lo1 hi1) (measurableSet_arc lo2 hi2)
    (δ := δ) (c := N * ((hi1 - lo1) * (hi2 - lo2)) + E + 4 * N * δ) (e := D - E)
    (fun t u => by
      have hED0 : 0 ≤ D - E := by linarith [(abs_le.mp hED).2]
      by_cases ht : δ ≤ ‖t‖
      · have hc := (abs_le.mp (abs_translate_boxCount_sub_le z N h1 h2 h3 h4 t u)).2
        have hf : 1 ≤ farIndicator δ t + farIndicator δ u := by
          have hu0 : 0 ≤ farIndicator δ u := by
            unfold farIndicator
            split_ifs <;> norm_num
          have ht1 : farIndicator δ t = 1 := by simp [farIndicator, ht]
          linarith
        have hmulf := mul_le_mul_of_nonneg_left hf hED0
        linarith
      · by_cases hu : δ ≤ ‖u‖
        · have hc := (abs_le.mp (abs_translate_boxCount_sub_le z N h1 h2 h3 h4 t u)).2
          have hf : 1 ≤ farIndicator δ t + farIndicator δ u := by
            simp only [farIndicator, if_pos hu, if_neg ht]
            norm_num
          have hmulf := mul_le_mul_of_nonneg_left hf hED0
          linarith
        · have hf : farIndicator δ t + farIndicator δ u = 0 := by
            simp only [farIndicator, if_neg hu, if_neg ht]
            norm_num
          have hmono : boxCount z N {x | x - t ∈ arc lo1 hi1} {x | x - u ∈ arc lo2 hi2} ≤
              boxCount z N (arc a b) (arc c d) :=
            boxCount_mono z N (fun n hn =>
              ⟨mem_of_sub_mem_contracted hn.1 (not_le.mp ht),
                mem_of_sub_mem_contracted hn.2 (not_le.mp hu)⟩)
          rw [hf, mul_zero, add_zero]
          linarith)
  have htail := circle_tail_le H hδ hδh
  have hED0 : 0 ≤ D - E := by linarith [(abs_le.mp hED).2]
  have hmul := mul_le_mul_of_nonneg_left htail hED0
  have hT := (abs_le.mp (abs_smooth_box_sub_le z (a := lo1) (b := hi1) (c := lo2) (d := hi2)
    h1 h2 h3 h4 H N)).1
  nlinarith

/-- **Erdős–Turán–Koksma, extreme form.** For `H ≥ 7`, the extreme box discrepancy of `N`
torus points is at most `32N/(H+1) + 2 ∑_{(k,l) ≠ 0} w(k) w(l) |S_{k,l}|`. -/
theorem extremeBoxError_le_modeSum (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ) {H : ℕ}
    (hH : 7 ≤ H) :
    extremeBoxError z N ≤ 32 * N / ((H : ℝ) + 1) + 2 * boxModeSum z N H := by
  have hH1 : (8 : ℝ) ≤ (H : ℝ) + 1 := by
    have : (7 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  set δ : ℝ := 4 / ((H : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδh : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hτ : 2 * (1 / (2 * ((H : ℝ) + 1) * δ)) = 1 / 4 := by
    rw [hδdef]
    field_simp
  have hNδ : 4 * (N : ℝ) * δ = 16 * N / ((H : ℝ) + 1) := by
    rw [hδdef]
    ring
  set D := extremeBoxError z N
  set T := boxModeSum z N H
  have hbox : ∀ a b c d : ℝ, a ≤ b → b ≤ a + 1 → c ≤ d → d ≤ c + 1 →
      |boxError z N a b c d| ≤ (4 / 3) * (T + 16 * N / ((H : ℝ) + 1)) + D / 3 := by
    intro a b c d hab hb hcd hd
    have hu := boxError_mul_le z N H hab hb hcd hd hδ hδh
    have hl := neg_boxError_mul_le z N H hab hb hcd hd hδ hδh
    rw [hτ, hNδ] at hu hl
    rw [abs_le]
    constructor <;> linarith
  have hD : D ≤ (4 / 3) * (T + 16 * N / ((H : ℝ) + 1)) + D / 3 :=
    extremeBoxError_le z N hbox
  have h32 : 32 * (N : ℝ) / ((H : ℝ) + 1) = 2 * (16 * N / ((H : ℝ) + 1)) := by ring
  rw [h32]
  linarith

/-- **Erdős–Turán–Koksma inequality with main term `N/H`.** For `H ≥ 7` and every box
`[a, b) × [c, d)` with sides of length at most one,
`|#{n < N : z n ∈ box} - N (b - a)(d - c)| ≤ 32N/(H+1) + 2 ∑_{(k,l) ≠ 0} w(k) w(l) |S_{k,l}|`. -/
theorem abs_boxError_le_modeSum (z : ℕ → UnitAddCircle × UnitAddCircle) (N : ℕ) {H : ℕ}
    (hH : 7 ≤ H) {a b c d : ℝ} (hab : a ≤ b) (hb : b ≤ a + 1) (hcd : c ≤ d)
    (hd : d ≤ c + 1) :
    |boxError z N a b c d| ≤ 32 * N / ((H : ℝ) + 1) + 2 * boxModeSum z N H :=
  (abs_boxError_le_extremeBoxError z N hab hb hcd hd).trans
    (extremeBoxError_le_modeSum z N hH)

end BTCalculus.ErdosTuranBox
