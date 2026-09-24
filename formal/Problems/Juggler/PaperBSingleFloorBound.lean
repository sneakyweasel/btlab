/-
# Paper B, Theorem 3.1: `S_O(N) = O(N^{5/6})`

`docs/theory/juggler_parity_discrepancy_note.md`, Theorem 3.1. This module
finishes the analytic half left open by `Problems.Juggler.PaperBSingleFloor`:

* the odd start `2r+1` has an even image exactly when `g(r) = (1/2)(2r+1)^{3/2}`
  lies in the arc `[0, 1/2)` modulo one (`imageSign_eq_arc`);
* on one block `[a, a+M)` with `M ≤ a`, the Erdős–Turán inequality
  `BTCalculus.ErdosTuran.abs_arcError_le_of_modes` at `H = ⌊a^{1/6}⌋`, fed with
  `block_exponential_sum`, bounds the block sign sum by `528 a^{5/6}`
  (`abs_block_sign_sum_le`);
* halving the range and summing the blocks gives `|S_O(N)| ≤ 2112 N^{5/6}`
  (`abs_singleFloorSum_le`);
* the exact bridges turn this into `#OO = N/4 + O(N^{5/6})` and
  `#C_2 = 3N/4 + O(N^{5/6})` with explicit constant `1057`.
-/

import BTCalculus.ErdosTuran
import Problems.Juggler.PaperBSingleFloor

attribute [local instance] Classical.propDecidable

namespace Problems.Juggler

namespace PaperBSingleFloor

open Finset Real
open BTCalculus.ErdosTuran BTCalculus.FejerArc BTCalculus.WeylDifferencing
open BTCalculus.SecondDerivative

/-- The circle point of the odd start `2r+1`: the phase `g(r)` modulo one. -/
noncomputable def oddPoint (r : ℝ) : UnitAddCircle := (phaseG r : UnitAddCircle)

private theorem fourier_coe_eq_phase (k : ℤ) (x : ℝ) :
    fourier k (x : UnitAddCircle) = phase ((k : ℝ) * x) := by
  rw [fourier_coe_apply]
  unfold phase
  congr 1
  push_cast
  simp only [div_one]
  ring

/-- `2 g(r) = (2r+1)^{3/2}` at a natural `r`, written with the natural odd start. -/
theorem two_mul_phaseG_natCast (r : ℕ) :
    2 * phaseG (r : ℝ) = ((2 * r + 1 : ℕ) : ℝ) * sqrt ((2 * r + 1 : ℕ) : ℝ) := by
  simp only [phaseG, Problems.Juggler.pow32]
  push_cast
  ring

/-- The fractional part of `y` is below `1/2` exactly when `⌊2y⌋` is even. -/
theorem fract_lt_half_iff (y : ℝ) : Int.fract y < 1 / 2 ↔ ⌊2 * y⌋ % 2 = 0 := by
  set q := ⌊y⌋ with hq
  have h1 : (q : ℝ) ≤ y := Int.floor_le y
  have h2 : y < q + 1 := Int.lt_floor_add_one y
  have hlo : 2 * q ≤ ⌊2 * y⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  have hhi : ⌊2 * y⌋ < 2 * q + 2 := by
    rw [Int.floor_lt]
    push_cast
    linarith
  have hiff : Int.fract y < 1 / 2 ↔ ⌊2 * y⌋ < 2 * q + 1 := by
    rw [Int.fract, Int.floor_lt]
    push_cast
    constructor <;> intro h <;> linarith
  rw [hiff]
  omega

/-- **Parity as arc membership.** The odd start `2r+1` has sign `+1` exactly when
`g(r)` lies in `[0, 1/2)` modulo one. -/
theorem imageSign_eq_arc (r : ℕ) :
    (imageSign (2 * r + 1) : ℝ) =
      2 * (if oddPoint r ∈ arc 0 (1 / 2) then (1 : ℝ) else 0) - 1 := by
  set y := phaseG (r : ℝ)
  have hfloor : ⌊2 * y⌋ = ((Nat.sqrt ((2 * r + 1) ^ 3) : ℕ) : ℤ) := by
    rw [two_mul_phaseG_natCast, floor_pow32]
  have hmem : oddPoint r ∈ arc 0 (1 / 2) ↔ Int.fract y < 1 / 2 := by
    have hcoe : oddPoint r = ((Int.fract y : ℝ) : UnitAddCircle) := by
      have hz : ((⌊y⌋ : ℝ) : UnitAddCircle) = 0 := by
        rw [QuotientAddGroup.eq_zero_iff]
        exact ⟨⌊y⌋, by simp⟩
      rw [oddPoint, Int.fract, QuotientAddGroup.mk_sub, hz, sub_zero]
    rw [hcoe, coe_mem_arc_iff (by norm_num)
      ⟨Int.fract_nonneg y, by simpa using Int.fract_lt_one y⟩]
    simp [Int.fract_nonneg y]
  rw [fract_lt_half_iff, hfloor] at hmem
  by_cases h : Nat.sqrt ((2 * r + 1) ^ 3) % 2 = 0
  · have hin : oddPoint r ∈ arc 0 (1 / 2) := hmem.mpr (by omega)
    rw [imageSign_even h, if_pos hin]
    norm_num
  · have h' : Nat.sqrt ((2 * r + 1) ^ 3) % 2 = 1 := by omega
    have hout : oddPoint r ∉ arc 0 (1 / 2) := fun hin => h (by have := hmem.mp hin; omega)
    rw [imageSign_odd h', if_neg hout]
    norm_num

/-- A block sign sum is twice one arc discrepancy of the shifted points. -/
theorem block_sign_sum_eq (a M : ℕ) :
    (∑ n ∈ range M, (imageSign (2 * (a + n) + 1) : ℝ)) =
      2 * arcError (fun n => oddPoint ((a : ℝ) + n)) M 0 (1 / 2) := by
  rw [arcError, sampleCount, mul_sub, mul_sum]
  have hpt (n : ℕ) : (imageSign (2 * (a + n) + 1) : ℝ) =
      2 * (if oddPoint ((a : ℝ) + n) ∈ arc 0 (1 / 2) then (1 : ℝ) else 0) - 1 := by
    rw [imageSign_eq_arc]
    push_cast
    rfl
  rw [sum_congr rfl (fun n _ => hpt n), sum_sub_distrib]
  simp
  ring

/-- The two-sided mode bound on one block, from the second-derivative test. -/
theorem block_mode_bound {a : ℝ} {M h : ℕ} (ha : 1 ≤ a) (hM : (M : ℝ) ≤ a) (hh : 1 ≤ h) :
    ‖∑ n ∈ range M, fourier (h : ℤ) (oddPoint (a + n))‖ ≤
        8 * M * sqrt ((h : ℝ) * (3 / 2) / sqrt (2 * (a + M) + 1)) +
          8 / sqrt ((h : ℝ) * (3 / 2) / sqrt (2 * (a + M) + 1)) ∧
      ‖∑ n ∈ range M, fourier (-(h : ℤ)) (oddPoint (a + n))‖ ≤
        8 * M * sqrt ((h : ℝ) * (3 / 2) / sqrt (2 * (a + M) + 1)) +
          8 / sqrt ((h : ℝ) * (3 / 2) / sqrt (2 * (a + M) + 1)) := by
  have hb := block_exponential_sum (h := h) (N := M) ha hM hh
  have hpos : (∑ n ∈ range M, fourier (h : ℤ) (oddPoint (a + n))) =
      ∑ n ∈ range M, phase ((h : ℝ) * phaseG (a + n)) := by
    simp only [oddPoint, fourier_coe_eq_phase, Int.cast_natCast]
  have hneg : (∑ n ∈ range M, fourier (-(h : ℤ)) (oddPoint (a + n))) =
      (starRingEnd ℂ) (∑ n ∈ range M, phase ((h : ℝ) * phaseG (a + n))) := by
    rw [map_sum]
    apply sum_congr rfl
    intro n _
    rw [oddPoint, fourier_coe_eq_phase, ← phase_neg]
    congr 1
    push_cast
    ring
  refine ⟨by rw [hpos]; exact hb, ?_⟩
  rw [hneg, Complex.norm_conj]
  exact hb


/-- Two-sided control of the curvature parameter gives both square-root factors. -/
theorem sqrt_curvature_bounds {h u lam : ℝ} (hh : 1 ≤ h) (hu : 1 ≤ u)
    (hlo : h / (4 * u ^ 6) ≤ lam) (hhi : lam ≤ 4 * h / u ^ 6) :
    sqrt lam ≤ 2 * sqrt h / u ^ 3 ∧ 1 / sqrt lam ≤ 2 * u ^ 3 / sqrt h := by
  have hu3 : 0 < u ^ 3 := by positivity
  have hsh : 0 < sqrt h := sqrt_pos.mpr (by linarith)
  have hhs : sqrt h ^ 2 = h := sq_sqrt (by linarith)
  have e1 : sqrt (4 * h / u ^ 6) = 2 * sqrt h / u ^ 3 := by
    have : 4 * h / u ^ 6 = (2 * sqrt h / u ^ 3) ^ 2 := by
      rw [div_pow, mul_pow, hhs, ← pow_mul]
      norm_num
    rw [this, sqrt_sq (by positivity)]
  have e2 : sqrt (h / (4 * u ^ 6)) = sqrt h / (2 * u ^ 3) := by
    have : h / (4 * u ^ 6) = (sqrt h / (2 * u ^ 3)) ^ 2 := by
      rw [div_pow, mul_pow, hhs, ← pow_mul]
      norm_num
    rw [this, sqrt_sq (by positivity)]
  refine ⟨?_, ?_⟩
  · rw [← e1]
    exact sqrt_le_sqrt hhi
  · have hl : sqrt h / (2 * u ^ 3) ≤ sqrt lam := by
      rw [← e2]
      exact sqrt_le_sqrt hlo
    have hpos : 0 < sqrt h / (2 * u ^ 3) := by positivity
    calc 1 / sqrt lam ≤ 1 / (sqrt h / (2 * u ^ 3)) := one_div_le_one_div_of_le hpos hl
      _ = 2 * u ^ 3 / sqrt h := by field_simp

/-- One weighted mode term of a block at scale `u^{12}` is at most `32 u^9 / √h`. -/
theorem mode_term_le {h u lam M : ℝ} (hh : 1 ≤ h) (hu : 1 ≤ u) (hM : M ≤ u ^ 12)
    (hlo : h / (4 * u ^ 6) ≤ lam) (hhi : lam ≤ 4 * h / u ^ 6) :
    (8 * M * sqrt lam + 8 / sqrt lam) / h ≤ 32 * u ^ 9 / sqrt h := by
  obtain ⟨h1, h2⟩ := sqrt_curvature_bounds hh hu hlo hhi
  have hu3 : 0 < u ^ 3 := by positivity
  set s := sqrt h with hs
  have hs1 : 1 ≤ s := by rw [hs, show (1 : ℝ) = sqrt 1 by simp]; exact sqrt_le_sqrt hh
  have hss : s * s = h := mul_self_sqrt (by linarith)
  have hu39 : u ^ 3 ≤ u ^ 9 := pow_le_pow_right₀ hu (by norm_num)
  have ha : M * sqrt lam ≤ 2 * u ^ 9 * s := by
    calc M * sqrt lam ≤ u ^ 12 * (2 * s / u ^ 3) :=
          mul_le_mul hM h1 (sqrt_nonneg _) (by positivity)
      _ = 2 * u ^ 9 * s := by field_simp
  have hb : 8 / sqrt lam ≤ 16 * u ^ 9 * s := by
    have : 8 / sqrt lam = 8 * (1 / sqrt lam) := by ring
    rw [this]
    calc 8 * (1 / sqrt lam) ≤ 8 * (2 * u ^ 3 / s) := by linarith
      _ ≤ 16 * u ^ 9 * s := by
        rw [show 8 * (2 * u ^ 3 / s) = 16 * u ^ 3 / s by ring,
          div_le_iff₀ (by linarith)]
        nlinarith
  rw [div_le_div_iff₀ (by linarith) (by linarith), ← hss]
  nlinarith

/-- The curvature parameter of a block `[a, a+M)` with `M ≤ a = u^{12}`. -/
theorem curvature_bounds {a M h u : ℝ} (ha : 1 ≤ a) (hM0 : 0 ≤ M) (hM : M ≤ a)
    (hh : 1 ≤ h) (hua : u ^ 12 = a) :
    h / (4 * u ^ 6) ≤ h * (3 / 2) / sqrt (2 * (a + M) + 1) ∧
      h * (3 / 2) / sqrt (2 * (a + M) + 1) ≤ 4 * h / u ^ 6 := by
  have hsa : sqrt a = u ^ 6 := by
    rw [← hua, show u ^ 12 = (u ^ 6) ^ 2 by ring, sqrt_sq (by positivity)]
  have hu6 : 0 < u ^ 6 := by rw [← hsa]; exact sqrt_pos.mpr (by linarith)
  have hs1 : u ^ 6 ≤ sqrt (2 * (a + M) + 1) := by
    rw [← hsa]; exact sqrt_le_sqrt (by linarith)
  have hs2 : sqrt (2 * (a + M) + 1) ≤ 3 * u ^ 6 := by
    have h9 : sqrt (9 * a) = 3 * u ^ 6 := by
      rw [sqrt_mul (by norm_num), hsa, show (9 : ℝ) = 3 ^ 2 by norm_num,
        sqrt_sq (by norm_num)]
    rw [← h9]
    exact sqrt_le_sqrt (by linarith)
  have hspos : 0 < sqrt (2 * (a + M) + 1) := hu6.trans_le hs1
  constructor
  · rw [div_le_div_iff₀ (by positivity) hspos]
    nlinarith
  · rw [div_le_div_iff₀ hspos hu6]
    nlinarith

/-- `∑_{h=1}^H 1/√h ≤ 2 √H`, the reciprocal-root form of `sum_inv_sqrt`. -/
theorem sum_one_div_sqrt_le (H : ℕ) :
    ∑ h ∈ Finset.Icc 1 H, 1 / sqrt (h : ℝ) ≤ 2 * sqrt (H : ℝ) := by
  refine le_of_eq_of_le (sum_congr rfl (fun h hh => ?_)) (sum_inv_sqrt H)
  have hpos : (0 : ℝ) < h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
  rw [Real.rpow_neg hpos.le, Real.sqrt_eq_rpow, one_div]

/-- The integer sign has absolute value one. -/
theorem abs_imageSign (n : ℕ) : |(imageSign n : ℝ)| = 1 := by
  unfold imageSign
  split_ifs <;> simp

/-- **One block.** A block `[a, a+M)` of odd-start parameters with `1 ≤ a` and
`M ≤ a` has sign sum at most `528 a^{5/6}` in size. -/
theorem abs_block_sign_sum_le (a M : ℕ) (ha : 1 ≤ a) (hM : M ≤ a) :
    |∑ n ∈ range M, (imageSign (2 * (a + n) + 1) : ℝ)| ≤ 528 * (a : ℝ) ^ (5 / 6 : ℝ) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hMa : (M : ℝ) ≤ a := by exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set u : ℝ := (a : ℝ) ^ (1 / 12 : ℝ) with hudef
  have hu0 : 0 ≤ u := by positivity
  have hu1 : 1 ≤ u := Real.one_le_rpow ha1 (by norm_num)
  have hpow (k : ℕ) : u ^ k = (a : ℝ) ^ ((k : ℝ) / 12) := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    ring
  have hua : u ^ 12 = a := by rw [hpow]; norm_num
  have h56 : (a : ℝ) ^ (5 / 6 : ℝ) = u ^ 10 := by rw [hpow]; norm_num
  rw [h56]
  have hu10 : 0 ≤ u ^ 10 := by positivity
  set H := ⌊u ^ 2⌋₊ with hHdef
  have hHle : (H : ℝ) ≤ u ^ 2 := Nat.floor_le (by positivity)
  have hHlt : u ^ 2 < H + 1 := Nat.lt_floor_add_one _
  by_cases hH : 3 ≤ H
  · rw [block_sign_sum_eq, abs_mul, abs_two]
    let lam : ℕ → ℝ := fun h => (h : ℝ) * (3 / 2) / sqrt (2 * ((a : ℝ) + M) + 1)
    let B : ℕ → ℝ := fun h => 8 * M * sqrt (lam h) + 8 / sqrt (lam h)
    have hB : ∀ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ range M, fourier (h : ℤ) (oddPoint ((a : ℝ) + n))‖ ≤ B h ∧
          ‖∑ n ∈ range M, fourier (-(h : ℤ)) (oddPoint ((a : ℝ) + n))‖ ≤ B h :=
      fun h hh => block_mode_bound ha1 hMa (Finset.mem_Icc.mp hh).1
    have het := abs_arcError_le_of_modes (fun n => oddPoint ((a : ℝ) + n)) M hH B hB
      (a := 0) (b := 1 / 2) (by norm_num) (by norm_num)
    have hterm : ∀ h ∈ Finset.Icc 1 H, B h / h ≤ 32 * u ^ 9 * (1 / sqrt (h : ℝ)) := by
      intro h hh
      have h1 : (1 : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
      obtain ⟨hlo, hhi⟩ := curvature_bounds ha1 hM0 hMa h1 hua
      have := mode_term_le h1 hu1 (hMa.trans_eq hua.symm) hlo hhi
      calc B h / h ≤ 32 * u ^ 9 / sqrt h := this
        _ = 32 * u ^ 9 * (1 / sqrt (h : ℝ)) := by ring
    have hsum : ∑ h ∈ Finset.Icc 1 H, B h / h ≤ 64 * u ^ 10 := by
      have hsH : sqrt (H : ℝ) ≤ u := by
        rw [show u = sqrt (u ^ 2) by rw [sqrt_sq hu0]]
        exact sqrt_le_sqrt hHle
      calc ∑ h ∈ Finset.Icc 1 H, B h / h
          ≤ ∑ h ∈ Finset.Icc 1 H, 32 * u ^ 9 * (1 / sqrt (h : ℝ)) := sum_le_sum hterm
        _ = 32 * u ^ 9 * ∑ h ∈ Finset.Icc 1 H, 1 / sqrt (h : ℝ) := by rw [mul_sum]
        _ ≤ 32 * u ^ 9 * (2 * sqrt (H : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le H) (by positivity)
        _ ≤ 32 * u ^ 9 * (2 * u) := by gcongr
        _ = 64 * u ^ 10 := by ring
    have hmain : 8 * (M : ℝ) / ((H : ℝ) + 1) ≤ 8 * u ^ 10 := by
      have hu2 : 0 < u ^ 2 := by positivity
      rw [div_le_iff₀ (by positivity)]
      have : (M : ℝ) ≤ u ^ 10 * u ^ 2 := by
        rw [show u ^ 10 * u ^ 2 = u ^ 12 by ring]; linarith
      nlinarith
    linarith
  · have hH2 : (H : ℝ) ≤ 2 := by exact_mod_cast (show H ≤ 2 by omega)
    have hu2 : u ^ 2 ≤ 3 := by linarith
    calc |∑ n ∈ range M, (imageSign (2 * (a + n) + 1) : ℝ)|
        ≤ ∑ n ∈ range M, |(imageSign (2 * (a + n) + 1) : ℝ)| := abs_sum_le_sum_abs _ _
      _ = M := by simp [abs_imageSign]
      _ ≤ u ^ 12 := hMa.trans_eq hua.symm
      _ = u ^ 2 * u ^ 10 := by ring
      _ ≤ 3 * u ^ 10 := mul_le_mul_of_nonneg_right hu2 hu10
      _ ≤ 528 * u ^ 10 := by linarith

/-- `(3/4)^{5/6} ≤ 4/5`, the contraction factor of one halving step. -/
theorem three_quarters_rpow_le : (3 / 4 : ℝ) ^ (5 / 6 : ℝ) ≤ 4 / 5 := by
  have e1 : (3 / 4 : ℝ) ^ (5 / 6 : ℝ) = ((3 / 4 : ℝ) ^ (5 : ℕ)) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have e2 : (4 / 5 : ℝ) = ((4 / 5 : ℝ) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [e1, e2]
  exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)

/-- **All odd starts below `2R`.** `|∑_{r<R} ψ((2r+1)^{3/2})| ≤ 2112 R^{5/6}`,
by splitting `[0, R)` at `⌈R/2⌉` and recursing on the lower half. -/
theorem abs_odd_sign_sum_le (R : ℕ) :
    |∑ r ∈ range R, (imageSign (2 * r + 1) : ℝ)| ≤ 2112 * (R : ℝ) ^ (5 / 6 : ℝ) := by
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    rcases Nat.lt_or_ge R 2 with hR | hR
    · interval_cases R
      · simp
      · simp [abs_imageSign]
    · set a := (R + 1) / 2 with hadef
      set M := R / 2 with hMdef
      have hsplit : a + M = R := by omega
      have ha : 1 ≤ a := by omega
      have hMa : M ≤ a := by omega
      have haR : a < R := by omega
      rw [← hsplit, sum_range_add, hsplit]
      have h1 := ih a haR
      have h2 := abs_block_sign_sum_le a M ha hMa
      have hscale : (a : ℝ) ^ (5 / 6 : ℝ) ≤ 4 / 5 * (R : ℝ) ^ (5 / 6 : ℝ) := by
        have hle : (a : ℝ) ≤ 3 / 4 * R := by
          have : 4 * a ≤ 3 * R := by omega
          have : (4 * a : ℝ) ≤ 3 * R := by exact_mod_cast this
          linarith
        calc (a : ℝ) ^ (5 / 6 : ℝ) ≤ (3 / 4 * (R : ℝ)) ^ (5 / 6 : ℝ) :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by norm_num)
          _ = (3 / 4 : ℝ) ^ (5 / 6 : ℝ) * (R : ℝ) ^ (5 / 6 : ℝ) :=
              Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
          _ ≤ 4 / 5 * (R : ℝ) ^ (5 / 6 : ℝ) :=
              mul_le_mul_of_nonneg_right three_quarters_rpow_le (by positivity)
      calc _ ≤ |∑ r ∈ range a, (imageSign (2 * r + 1) : ℝ)| +
            |∑ n ∈ range M, (imageSign (2 * (a + n) + 1) : ℝ)| := abs_add_le _ _
        _ ≤ 2112 * (a : ℝ) ^ (5 / 6 : ℝ) + 528 * (a : ℝ) ^ (5 / 6 : ℝ) := add_le_add h1 h2
        _ ≤ 2112 * (R : ℝ) ^ (5 / 6 : ℝ) := by linarith

/-- Odd starts in `{1, …, N}` are `2r+1` for `r < ⌈N/2⌉`. -/
theorem sum_oddStarts_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ oddStarts N, f n = ∑ r ∈ range ((N + 1) / 2), f (2 * r + 1) := by
  symm
  apply Finset.sum_nbij' (fun r => 2 * r + 1) (fun n => n / 2)
  · intro r hr
    simp only [mem_range] at hr
    simp only [oddStarts, mem_filter, mem_Icc]
    omega
  · intro n hn
    simp only [oddStarts, mem_filter, mem_Icc] at hn
    simp only [mem_range]
    omega
  · intro r _
    omega
  · intro n hn
    simp only [oddStarts, mem_filter, mem_Icc] at hn
    omega
  · intro r _
    rfl

/-- There are `⌈N/2⌉` odd starts in `{1, …, N}`. -/
theorem card_oddStarts (N : ℕ) : (oddStarts N).card = (N + 1) / 2 := by
  have h := sum_oddStarts_eq N (fun _ => 1)
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- **Paper B, Theorem 3.1, first assertion.** `|S_O(N)| ≤ 2112 N^{5/6}`. -/
theorem abs_singleFloorSum_le (N : ℕ) :
    |(singleFloorSum N : ℝ)| ≤ 2112 * (N : ℝ) ^ (5 / 6 : ℝ) := by
  have he : (singleFloorSum N : ℝ) =
      ∑ r ∈ range ((N + 1) / 2), (imageSign (2 * r + 1) : ℝ) := by
    rw [singleFloorSum, Int.cast_sum]
    exact sum_oddStarts_eq N (fun n => (imageSign n : ℝ))
  rw [he]
  refine (abs_odd_sign_sum_le _).trans ?_
  have hle : (((N + 1) / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (show (N + 1) / 2 ≤ N by omega)
  gcongr

/-- **Paper B, Theorem 3.1, `OO` count.** `|#{n ≤ N : word_2 = OO} - N/4| ≤ 1057 N^{5/6}`. -/
theorem abs_ooCount_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |(ooCount N : ℝ) - N / 4| ≤ 1057 * (N : ℝ) ^ (5 / 6 : ℝ) := by
  have hS := abs_singleFloorSum_le N
  have hb : (singleFloorSum N : ℝ) = (((N + 1) / 2 : ℕ) : ℝ) - 2 * (ooCount N : ℝ) := by
    have := singleFloor_bridge N
    rw [card_oddStarts] at this
    exact_mod_cast this
  have hpar : |2 * (((N + 1) / 2 : ℕ) : ℝ) - N| ≤ 1 := by
    rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
    · have : (N + 1) / 2 = k := by omega
      rw [this, abs_le]; constructor <;> push_cast [hk] <;> linarith
    · have : (N + 1) / 2 = k + 1 := by omega
      rw [this, abs_le]; constructor <;> push_cast [hk] <;> linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (5 / 6 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have he : (ooCount N : ℝ) - N / 4 =
      (2 * (((N + 1) / 2 : ℕ) : ℝ) - N) / 4 - (singleFloorSum N : ℝ) / 2 := by
    rw [hb]; ring
  rw [he]
  calc _ ≤ |(2 * (((N + 1) / 2 : ℕ) : ℝ) - N) / 4| + |(singleFloorSum N : ℝ) / 2| :=
        abs_sub _ _
    _ = |2 * (((N + 1) / 2 : ℕ) : ℝ) - N| / 4 + |(singleFloorSum N : ℝ)| / 2 := by
        rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 1057 * (N : ℝ) ^ (5 / 6 : ℝ) := by linarith

/-- **Paper B, Theorem 3.1, certificate count.**
`|#(C_2 ∩ [1, N]) - 3N/4| ≤ 1057 N^{5/6}`. -/
theorem abs_c2Count_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |(c2Count N : ℝ) - 3 * N / 4| ≤ 1057 * (N : ℝ) ^ (5 / 6 : ℝ) := by
  have hc : (c2Count N : ℝ) + ooCount N = N := by exact_mod_cast c2_compl N
  have he : (c2Count N : ℝ) - 3 * N / 4 = -((ooCount N : ℝ) - N / 4) := by linarith
  rw [he, abs_neg]
  exact abs_ooCount_sub_le N hN

end PaperBSingleFloor

end Problems.Juggler
