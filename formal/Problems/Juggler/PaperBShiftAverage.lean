/-
# Paper B, Proposition 7.4: the shift average

`docs/theory/juggler_parity_discrepancy_note.md`, Proposition 7.4. For frequencies
`A_1, …, A_L` with `|A_t - A_s| ≥ a |t - s|` and reals `x_t`, the sum
`S_λ = ∑_t e(A_t {x_t + λ})` satisfies
`|∫_0^1 |S_λ|^2 dλ - L| ≤ (4/π)(L/a)(1 + log L)`, and outside a set of shifts of measure at
most `η` its size is at most `[(L/η)(1 + (4/(π a))(1 + log L))]^{1/2}`.

* `norm_integral_phase_affine`: an affine phase `e(c λ + d)` integrates over any interval to
  at most `1/(π |c|)`;
* `norm_integral_pair_le`: one off-diagonal term, `e(A {p + λ} - B {q + λ})`, integrates over a
  period to at most `2/(π |A - B|)`: over the period starting at the breakpoint of `{p + λ}`
  the phase is affine with slope `A - B` on at most two intervals;
* `abs_integral_normSq_sub_le`: the bound (7.3);
* `volume_large_shift_le`: the exceptional set of shifts, by Markov's inequality.

The indices run over `0 ≤ t < L` rather than `1 ≤ t ≤ L`. Only the separation
`|A_t - A_s| ≥ a |t - s|` is used, not the ordering of the `A_t`.
-/

import BTCalculus.ErdosTuran
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor

namespace Problems.Juggler

namespace PaperBShiftAverage

open Finset Real MeasureTheory
open scoped ComplexConjugate
open BTCalculus.WeylDifferencing

/-! ## One affine phase -/

/-- `e(c λ + d)` integrates over any interval to at most `1/(π |c|)` for `c ≠ 0`. -/
theorem norm_integral_phase_affine {c : ℝ} (hc : c ≠ 0) (d u v : ℝ) :
    ‖∫ x in u..v, phase (c * x + d)‖ ≤ 1 / (π * |c|) := by
  set κ : ℂ := ((2 * π * c : ℝ) : ℂ) * Complex.I with hκ
  have h2pc : (2 * π * c : ℝ) ≠ 0 := mul_ne_zero (by positivity) hc
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact mul_ne_zero (by exact_mod_cast h2pc) Complex.I_ne_zero
  have hform : ∀ x : ℝ, phase (c * x + d) =
      Complex.exp (((2 * π * d : ℝ) : ℂ) * Complex.I) * Complex.exp (κ * x) := by
    intro x
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    rw [hκ]
    push_cast
    ring
  simp_rw [hform]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hκ0, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul, norm_div]
  have hv : ‖Complex.exp (κ * v)‖ = 1 := by
    rw [hκ, show ((2 * π * c : ℝ) : ℂ) * Complex.I * v = ((2 * π * c * v : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hu : ‖Complex.exp (κ * u)‖ = 1 := by
    rw [hκ, show ((2 * π * c : ℝ) : ℂ) * Complex.I * u = ((2 * π * c * u : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnκ : ‖κ‖ = 2 * π * |c| := by
    rw [hκ, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hnum : ‖Complex.exp (κ * v) - Complex.exp (κ * u)‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (κ * v)‖ + ‖Complex.exp (κ * u)‖ := norm_sub_le _ _
      _ = 2 := by rw [hv, hu]; norm_num
  have hc' : 0 < |c| := abs_pos.mpr hc
  rw [hnκ, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ π * |c|)
  linarith

/-! ## One pair of fractional parts -/

/-- A bounded measurable function is interval integrable. -/
theorem intervalIntegrable_of_norm_le {f : ℝ → ℂ} (hf : Measurable f) {M : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ M) (u v : ℝ) : IntervalIntegrable f volume u v :=
  ⟨Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hb),
    Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)⟩

/-- The pair integrand `e(A {p + λ} - B {q + λ})` is measurable. -/
theorem measurable_pair (A B p q : ℝ) :
    Measurable (fun x : ℝ => phase (A * Int.fract (p + x) - B * Int.fract (q + x))) := by
  have hp : Measurable (fun x : ℝ => Int.fract (p + x)) :=
    measurable_fract.comp (measurable_const.add measurable_id)
  have hq : Measurable (fun x : ℝ => Int.fract (q + x)) :=
    measurable_fract.comp (measurable_const.add measurable_id)
  have hphase : Continuous phase := by
    unfold phase
    fun_prop
  exact hphase.measurable.comp ((measurable_const.mul hp).sub (measurable_const.mul hq))

/-- **One off-diagonal term.** For `A ≠ B`,
`|∫_0^1 e(A {p + λ} - B {q + λ}) dλ| ≤ 2/(π |A - B|)`. -/
theorem norm_integral_pair_le {A B : ℝ} (hAB : A ≠ B) (p q : ℝ) :
    ‖∫ x in (0 : ℝ)..1, phase (A * Int.fract (p + x) - B * Int.fract (q + x))‖ ≤
      2 / (π * |A - B|) := by
  set F : ℝ → ℂ := fun x => phase (A * Int.fract (p + x) - B * Int.fract (q + x)) with hF
  have hc : A - B ≠ 0 := sub_ne_zero.mpr hAB
  have hper : Function.Periodic F 1 := by
    intro x
    simp only [hF, ← add_assoc, Int.fract_add_one]
  have hint (u v : ℝ) : IntervalIntegrable F volume u v :=
    intervalIntegrable_of_norm_le (M := 1) (measurable_pair A B p q)
      (fun x => by simp [phase_norm]) u v
  set b := -p with hb
  set f0 := Int.fract (q + b) with hf0
  have hf00 := Int.fract_nonneg (q + b)
  have hf01 := Int.fract_lt_one (q + b)
  set c' := b + (1 - f0) with hc'
  have hshift : ∫ x in (0 : ℝ)..1, F x = ∫ x in b..b + 1, F x := by
    have h := hper.intervalIntegral_add_eq 0 b
    rw [zero_add] at h
    exact h
  have hsplit : ∫ x in b..b + 1, F x = (∫ x in b..c', F x) + ∫ x in c'..b + 1, F x :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have hfq : q + b = ⌊q + b⌋ + f0 := (Int.floor_add_fract (q + b)).symm
  have hpiece1 : ∫ x in b..c', F x =
      ∫ x in b..c', phase ((A - B) * x + (-A * b - B * f0 + B * b)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by rw [hc']; linarith)
    intro x hx
    have hpx : Int.fract (p + x) = x - b := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [hx.1], by linarith [hx.2], 0, ?_⟩
      rw [hb]
      push_cast
      ring
    have hqx : Int.fract (q + x) = f0 + (x - b) := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [hx.1], by linarith [hx.2], ⌊q + b⌋, ?_⟩
      linarith
    simp only [hF, hpx, hqx]
    congr 1
    ring
  have hpiece2 : ∫ x in c'..b + 1, F x =
      ∫ x in c'..b + 1, phase ((A - B) * x + (-A * b - B * f0 + B * b + B)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by rw [hc']; linarith)
    intro x hx
    have hpx : Int.fract (p + x) = x - b := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [hx.1], by linarith [hx.2], 0, ?_⟩
      rw [hb]
      push_cast
      ring
    have hqx : Int.fract (q + x) = f0 + (x - b) - 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [hx.1], by linarith [hx.2], ⌊q + b⌋ + 1, ?_⟩
      push_cast
      linarith
    simp only [hF, hpx, hqx]
    congr 1
    ring
  rw [hshift, hsplit, hpiece1, hpiece2]
  calc _ ≤ ‖∫ x in b..c', phase ((A - B) * x + (-A * b - B * f0 + B * b))‖ +
        ‖∫ x in c'..b + 1, phase ((A - B) * x + (-A * b - B * f0 + B * b + B))‖ :=
        norm_add_le _ _
    _ ≤ 1 / (π * |A - B|) + 1 / (π * |A - B|) :=
        add_le_add (norm_integral_phase_affine hc _ _ _) (norm_integral_phase_affine hc _ _ _)
    _ = 2 / (π * |A - B|) := by ring

/-! ## The mean square -/

/-- `S_λ = ∑_{t < L} e(A_t {x_t + λ})`. -/
noncomputable def shiftSum (L : ℕ) (A x : ℕ → ℝ) (lam : ℝ) : ℂ :=
  ∑ t ∈ range L, phase (A t * Int.fract (x t + lam))

/-- `|S_λ|^2 = ∑_{t,s} e(A_t {x_t + λ} - A_s {x_s + λ})`. -/
theorem normSq_shiftSum (L : ℕ) (A x : ℕ → ℝ) (lam : ℝ) :
    ((‖shiftSum L A x lam‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ range L, ∑ s ∈ range L,
        phase (A t * Int.fract (x t + lam) - A s * Int.fract (x s + lam)) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, shiftSum, map_sum, sum_mul_sum]
  simp_rw [phase_mul_conj]

/-- The diagonal terms integrate to one each. -/
theorem integral_diag (A x : ℝ) :
    ∫ lam in (0 : ℝ)..1, phase (A * Int.fract (x + lam) - A * Int.fract (x + lam)) = 1 := by
  simp [phase]

/-- The off-diagonal row sum `∑_{s ≠ t} 1/|t - s|` over `s < L` is at most `2 H_{L-1}`. -/
theorem sum_row_inv_le {L t : ℕ} (ht : t < L) :
    ∑ s ∈ range L, (if s = t then (0 : ℝ) else 1 / |(t : ℝ) - s|) ≤
      2 * (harmonic (L - 1) : ℝ) := by
  set φ : ℤ → ℝ := fun k => if k = 0 then 0 else 1 / |(k : ℝ)| with hφ
  have hφ0 : ∀ k, 0 ≤ φ k := fun k => by
    simp only [hφ]
    split_ifs <;> positivity
  have hrow := BTCalculus.ErdosTuran.sum_row_le_sum_Icc (H := L - 1) (i := t) (by omega) hφ0
  have hL : L - 1 + 1 = L := by omega
  rw [hL] at hrow
  have hterm : ∀ s ∈ range L, (if s = t then (0 : ℝ) else 1 / |(t : ℝ) - s|) =
      φ ((t : ℤ) - s) := by
    intro s _
    simp only [hφ, sub_eq_zero, Nat.cast_inj]
    by_cases h : s = t
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]
      push_cast
      rfl
  rw [sum_congr rfl hterm]
  refine hrow.trans (le_of_eq ?_)
  have hw := BTCalculus.FejerArc.sum_frequencyWeight (L - 1)
  have hsplit : ∀ k ∈ Finset.Icc (-((L - 1 : ℕ) : ℤ)) (L - 1 : ℕ),
      φ k = BTCalculus.FejerArc.frequencyWeight k - if k = 0 then 1 else 0 := by
    intro k _
    simp only [hφ, BTCalculus.FejerArc.frequencyWeight]
    split_ifs <;> ring
  rw [sum_congr rfl hsplit, sum_sub_distrib, hw, sum_ite_eq']
  simp

/-- `2 H_{L-1} ≤ 2 (1 + log L)` for `L ≥ 1`. -/
theorem harmonic_pred_le {L : ℕ} (hL : 1 ≤ L) : (harmonic (L - 1) : ℝ) ≤ 1 + log L := by
  have h := harmonic_le_one_add_log (L - 1)
  have hl : log ((L - 1 : ℕ) : ℝ) ≤ log L := by
    rcases Nat.eq_zero_or_pos (L - 1) with h0 | hpos
    · rw [h0, Nat.cast_zero, log_zero]
      exact log_nonneg (by exact_mod_cast hL)
    · exact log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.sub_le L 1)
  linarith

/-- **Proposition 7.4, the mean square (7.3).** If `|A_t - A_s| ≥ a |t - s|` for `t, s < L`
with `a > 0`, then `|∫_0^1 |S_λ|^2 dλ - L| ≤ (4/π)(L/a)(1 + log L)`. -/
theorem abs_integral_normSq_sub_le {L : ℕ} (hL : 1 ≤ L) (A x : ℕ → ℝ) {a : ℝ} (ha : 0 < a)
    (hA : ∀ t < L, ∀ s < L, a * |(t : ℝ) - s| ≤ |A t - A s|) :
    |(∫ lam in (0 : ℝ)..1, ‖shiftSum L A x lam‖ ^ 2) - L| ≤ 4 / π * (L / a) * (1 + log L) := by
  set I : ℕ → ℕ → ℂ := fun t s => ∫ lam in (0 : ℝ)..1,
    phase (A t * Int.fract (x t + lam) - A s * Int.fract (x s + lam)) with hI
  have hint : ∀ t s, IntervalIntegrable
      (fun lam => phase (A t * Int.fract (x t + lam) - A s * Int.fract (x s + lam))) volume 0 1 :=
    fun t s => intervalIntegrable_of_norm_le (M := 1) (measurable_pair _ _ _ _)
      (fun _ => by simp [phase_norm]) 0 1
  have hC : (((∫ lam in (0 : ℝ)..1, ‖shiftSum L A x lam‖ ^ 2) : ℝ) : ℂ) =
      ∑ t ∈ range L, ∑ s ∈ range L, I t s := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [normSq_shiftSum]
    have hrow : ∀ t ∈ range L, IntervalIntegrable (fun lam => ∑ s ∈ range L,
        phase (A t * Int.fract (x t + lam) - A s * Int.fract (x s + lam))) volume 0 1 :=
      fun t _ => intervalIntegrable_of_norm_le (M := L)
        (Finset.measurable_sum _ (fun s _ => measurable_pair _ _ _ _))
        (fun lam => (norm_sum_le _ _).trans (by simp [phase_norm])) 0 1
    rw [intervalIntegral.integral_finsetSum hrow]
    apply sum_congr rfl
    intro t _
    rw [intervalIntegral.integral_finsetSum (fun s _ => hint t s)]
  have hdiag : ∀ t, I t t = 1 := fun t => integral_diag (A t) (x t)
  have hsub : ∑ t ∈ range L, ∑ s ∈ range L, I t s - (L : ℂ) =
      ∑ t ∈ range L, ∑ s ∈ range L, (if s = t then 0 else I t s) := by
    have : ∀ t ∈ range L, ∑ s ∈ range L, I t s =
        1 + ∑ s ∈ range L, (if s = t then 0 else I t s) := by
      intro t ht
      rw [← sum_erase_add _ _ ht, hdiag, add_comm]
      congr 1
      rw [← sum_erase_add _ _ ht, if_pos rfl, add_zero]
      apply sum_congr rfl
      intro s hs
      rw [if_neg (ne_of_mem_erase hs)]
    rw [sum_congr rfl this, sum_add_distrib]
    simp
  have hpair : ∀ t ∈ range L, ∀ s ∈ range L,
      ‖(if s = t then (0 : ℂ) else I t s)‖ ≤
        2 / (π * a) * (if s = t then (0 : ℝ) else 1 / |(t : ℝ) - s|) := by
    intro t ht s hs
    by_cases h : s = t
    · simp [h]
    · rw [if_neg h, if_neg h]
      have hts : (0 : ℝ) < |(t : ℝ) - s| := by
        rw [abs_pos, sub_ne_zero]
        exact_mod_cast Ne.symm h
      have hsep := hA t (mem_range.mp ht) s (mem_range.mp hs)
      have hAB : 0 < |A t - A s| := lt_of_lt_of_le (by positivity) hsep
      have hne : A t ≠ A s := by
        intro heq
        rw [heq, sub_self, abs_zero] at hAB
        exact lt_irrefl 0 hAB
      calc ‖I t s‖ ≤ 2 / (π * |A t - A s|) := norm_integral_pair_le hne _ _
        _ ≤ 2 / (π * (a * |(t : ℝ) - s|)) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact mul_le_mul_of_nonneg_left hsep pi_pos.le
        _ = 2 / (π * a) * (1 / |(t : ℝ) - s|) := by field_simp
  have hbound : ‖∑ t ∈ range L, ∑ s ∈ range L, (if s = t then (0 : ℂ) else I t s)‖ ≤
      2 / (π * a) * (L * (2 * (harmonic (L - 1) : ℝ))) := by
    calc _ ≤ ∑ t ∈ range L, ‖∑ s ∈ range L, (if s = t then (0 : ℂ) else I t s)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ t ∈ range L, ∑ s ∈ range L, ‖(if s = t then (0 : ℂ) else I t s)‖ :=
          sum_le_sum (fun t _ => norm_sum_le _ _)
      _ ≤ ∑ t ∈ range L, ∑ s ∈ range L,
            2 / (π * a) * (if s = t then (0 : ℝ) else 1 / |(t : ℝ) - s|) :=
          sum_le_sum (fun t ht => sum_le_sum (fun s hs => hpair t ht s hs))
      _ = ∑ t ∈ range L, 2 / (π * a) *
            ∑ s ∈ range L, (if s = t then (0 : ℝ) else 1 / |(t : ℝ) - s|) := by
          simp_rw [mul_sum]
      _ ≤ ∑ _t ∈ range L, 2 / (π * a) * (2 * (harmonic (L - 1) : ℝ)) :=
          sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left
            (sum_row_inv_le (mem_range.mp ht)) (by positivity))
      _ = 2 / (π * a) * (L * (2 * (harmonic (L - 1) : ℝ))) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          ring
  have habs : |(∫ lam in (0 : ℝ)..1, ‖shiftSum L A x lam‖ ^ 2) - L| =
      ‖∑ t ∈ range L, ∑ s ∈ range L, I t s - (L : ℂ)‖ := by
    rw [← hC, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  rw [habs, hsub]
  have hH := harmonic_pred_le hL
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  calc _ ≤ 2 / (π * a) * (L * (2 * (harmonic (L - 1) : ℝ))) := hbound
    _ ≤ 2 / (π * a) * (L * (2 * (1 + log L))) := by gcongr
    _ = 4 / π * (L / a) * (1 + log L) := by field_simp; norm_num

/-- `|S_λ| ≤ L`. -/
theorem norm_shiftSum_le (L : ℕ) (A x : ℕ → ℝ) (lam : ℝ) : ‖shiftSum L A x lam‖ ≤ L := by
  calc ‖shiftSum L A x lam‖ ≤ ∑ t ∈ range L, ‖phase (A t * Int.fract (x t + lam))‖ :=
        norm_sum_le _ _
    _ = L := by simp [phase_norm]

/-- `λ ↦ S_λ` is measurable. -/
theorem measurable_shiftSum (L : ℕ) (A x : ℕ → ℝ) : Measurable (shiftSum L A x) := by
  have hphase : Continuous phase := by
    unfold phase
    fun_prop
  unfold shiftSum
  refine Finset.measurable_sum _ (fun t _ => ?_)
  exact hphase.measurable.comp
    (measurable_const.mul (measurable_fract.comp (measurable_const.add measurable_id)))

/-- **Proposition 7.4, the exceptional shifts.** Under the hypotheses of
`abs_integral_normSq_sub_le`, for every `η > 0` the shifts `λ ∈ (0, 1]` with
`|S_λ| > [(L/η)(1 + (4/(π a))(1 + log L))]^{1/2}` have measure at most `η`. -/
theorem volume_large_shift_le {L : ℕ} (hL : 1 ≤ L) (A x : ℕ → ℝ) {a : ℝ} (ha : 0 < a)
    (hA : ∀ t < L, ∀ s < L, a * |(t : ℝ) - s| ≤ |A t - A s|) {η : ℝ} (hη : 0 < η) :
    volume (Set.Ioc (0 : ℝ) 1 ∩
        {lam | √((L / η) * (1 + 4 / (π * a) * (1 + log L))) < ‖shiftSum L A x lam‖}) ≤
      ENNReal.ofReal η := by
  set T2 := (L / η) * (1 + 4 / (π * a) * (1 + log L)) with hT2
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : 0 ≤ log (L : ℝ) := log_nonneg hL1
  have hT2pos : 0 < T2 := by positivity
  set f : ℝ → ℝ := fun lam => ‖shiftSum L A x lam‖ ^ 2 with hf
  set μ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  have hfm : Measurable f := (measurable_shiftSum L A x).norm.pow_const 2
  have hfint : Integrable f μ := by
    refine Measure.integrableOn_of_bounded (M := (L : ℝ) ^ 2) measure_Ioc_lt_top.ne
      hfm.aestronglyMeasurable (Filter.Eventually.of_forall (fun lam => ?_))
    rw [hf, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_shiftSum_le L A x lam) 2
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall (fun lam => by simp only [hf]; positivity)) hfint T2
  have hint : ∫ lam, f lam ∂μ ≤ T2 * η := by
    have h := abs_integral_normSq_sub_le hL A x ha hA
    rw [intervalIntegral.integral_of_le zero_le_one] at h
    have hup := (abs_le.mp h).2
    have : T2 * η = L + 4 / π * (L / a) * (1 + log L) := by
      rw [hT2]
      field_simp
    rw [this]
    linarith
  have hreal : μ.real {lam | T2 ≤ f lam} ≤ η := by
    have h := hmark.trans hint
    have := le_of_mul_le_mul_left (by linarith : T2 * μ.real {lam | T2 ≤ f lam} ≤ T2 * η) hT2pos
    exact this
  have hsub : Set.Ioc (0 : ℝ) 1 ∩ {lam | √T2 < ‖shiftSum L A x lam‖} ⊆
      Set.Ioc (0 : ℝ) 1 ∩ {lam | T2 ≤ f lam} := by
    rintro lam ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    change √T2 < ‖shiftSum L A x lam‖ at h2
    change T2 ≤ ‖shiftSum L A x lam‖ ^ 2
    have h3 : (√T2) ^ 2 ≤ ‖shiftSum L A x lam‖ ^ 2 :=
      pow_le_pow_left₀ (sqrt_nonneg _) h2.le 2
    rwa [sq_sqrt hT2pos.le] at h3
  have hμset : μ {lam | T2 ≤ f lam} = volume (Set.Ioc (0 : ℝ) 1 ∩ {lam | T2 ≤ f lam}) := by
    rw [hμ, Measure.restrict_apply' measurableSet_Ioc, Set.inter_comm]
  have hfin : μ {lam | T2 ≤ f lam} ≠ ⊤ := by
    rw [hμset]
    exact ((measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top).ne
  calc volume (Set.Ioc (0 : ℝ) 1 ∩ {lam | √T2 < ‖shiftSum L A x lam‖})
      ≤ volume (Set.Ioc (0 : ℝ) 1 ∩ {lam | T2 ≤ f lam}) := measure_mono hsub
    _ = μ {lam | T2 ≤ f lam} := hμset.symm
    _ ≤ ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal hreal

end PaperBShiftAverage

end Problems.Juggler
