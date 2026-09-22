import Problems.Juggler.OOEEffectiveModes
import Problems.Juggler.PaperECorollaries
import BTCalculus.FejerBox

/-! # Effective counts and bounded witnesses for OOE modular returns -/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Problems.Juggler.OOEEffectiveReturn

open Finset
open BTCalculus.WeylDifferencing BTCalculus.FourierBoxCounting
open BTCalculus.FejerArc PaperEModularReturn PaperECorollaries

/-- Exact residue selection, including both half-open endpoints. -/
theorem floor_mod_box_iff {x : ℝ} (hx : 0 ≤ x) {m r : ℕ} (hm : 0 < m) (hr : r < m) :
    ⌊x⌋₊ % m = r ↔ (r : ℝ)/m ≤ Int.fract (x/m) ∧
      Int.fract (x/m) < ((r : ℝ)+1)/m := by
  constructor
  · intro h
    have hmp : (0 : ℝ) < m := by exact_mod_cast hm
    have he : Int.fract (x/(m : ℝ))*(m : ℝ) = x-(⌊x⌋₊/m : ℕ)*(m : ℝ) := by
      rw [Int.fract, ← natCast_floor_eq_intCast_floor (div_nonneg hx hmp.le),
        Nat.floor_div_natCast]
      field_simp
    have hdecomp : (⌊x⌋₊/m : ℕ)*m+r = ⌊x⌋₊ := by
      rw [← h]
      simpa only [mul_comm] using Nat.div_add_mod ⌊x⌋₊ m
    have hdecomp' : (⌊x⌋₊/m : ℕ)*(m : ℝ)+(r : ℝ) = (⌊x⌋₊ : ℝ) := by
      exact_mod_cast hdecomp
    constructor
    · apply (div_le_iff₀ hmp).2
      linarith [Nat.floor_le hx]
    · apply (lt_div_iff₀ hmp).2
      linarith [Nat.lt_floor_add_one x]
  · exact fun h => floor_mod_of_box hx hm hr h.1 h.2

/-- The existing parameter predicate is exactly the integer-floor count in the theorem. -/
theorem return_parameter_iff {M : ℕ} (hM : 0 < M) (t : ℕ) :
    ReturnParameter 2 1 M t ↔ 16 ≤ 1+2*M*t ∧
      ⌊((1+2*M*t : ℕ) : ℝ)^(9/2 : ℝ)⌋₊ % 2 = 0 ∧
      ⌊((1+2*M*t : ℕ) : ℝ)^(9/4 : ℝ)⌋₊ % (2*M) = 1 := by
  have h0 := floor_mod_box_iff (x := powerValue (1+2*M*t) 2 0)
    (by unfold powerValue; positivity) (by norm_num : 0 < 2) (by norm_num : 0 < 2)
  have h1 := floor_mod_box_iff (x := powerValue (1+2*M*t) 2 1)
    (by unfold powerValue; positivity) (by omega : 0 < 2*M) (by omega : 1 < 2*M)
  norm_num only [Nat.cast_zero, zero_div, zero_add, Int.fract_nonneg, true_and,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, powerValue] at h0 h1
  simp only [ReturnParameter, ReturnBox, Nat.lt_one_iff, forall_eq, powerValue]
  norm_num only
  tauto

/-- The two actual power coordinates that encode the OOE residue guards. -/
def sample (M t : ℕ) : UnitAddCircle × UnitAddCircle :=
  ((powerValue (1+2*M*t) 2 0 / 2 : ℝ),
    (powerValue (1+2*M*t) 2 1 / (2*M) : ℝ))

theorem sample_mem_box {M : ℕ} (hM : 0 < M) (t : ℕ) :
    ((sample M t).1 ∈ arc 0 (1/2) ∧
      (sample M t).2 ∈ arc (1/(2*M)) (2/(2*M))) ↔ ReturnBox 2 1 M t := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by positivity
  have hab : (1 : ℝ)/(2*M) < 2/(2*M) := by
    apply (div_lt_div_iff_of_pos_right (by positivity)).2
    norm_num
  have hb : (2 : ℝ)/(2*M) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  simp only [sample, arc_eq_circleArc (by norm_num : (0 : ℝ) < 1/2),
    arc_eq_circleArc hab,
    mem_circleArc_iff (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (1/2 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 1/2),
    mem_circleArc_iff (by positivity : (0 : ℝ) ≤ 1/(2*M)) hb hab,
    ReturnBox, Nat.lt_one_iff, forall_eq, Int.fract_nonneg, true_and]
  tauto

theorem sample_mode (M t : ℕ) (k l : ℤ) :
    BTCalculus.FejerBox.mode k l (sample M t) =
      phase (OOEEffectiveModes.mode M k l t) := by
  simp only [BTCalculus.FejerBox.mode, sample, fourier_coe_apply, powerValue,
    OOEEffectiveModes.mode, phase]
  push_cast
  norm_num only
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The finite box estimate specialized to the actual OOE sample, before choosing H. -/
theorem box_discrepancy {M H T : ℕ} (hM : 0 < M) (hH : 1 ≤ H) (hT : 1 ≤ T)
    (hHT : (H : ℝ) ≤ (T : ℝ)^(1/4 : ℝ)) :
    |(count (ReturnBox 2 1 M) T : ℝ)/T - 1/(4*M)| ≤
      5 / Real.sqrt ((H : ℝ)+1) + (3+2*Real.log H)^2 *
        (128*(M : ℝ)^(1/4 : ℝ)*(H : ℝ)^(1/30 : ℝ)*(T : ℝ)^(-1/60 : ℝ)) := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hMp : (0 : ℝ) < M := by positivity
  have hcd : (1 : ℝ)/(2*M) ≤ 2/(2*M) := by
    apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hd : (2 : ℝ)/(2*M) ≤ 1/(2*M)+1 := by
    have h : (2 : ℝ)/(2*M) ≤ 1 := (div_le_iff₀ (by positivity)).2 (by linarith)
    linarith [show (0 : ℝ) ≤ 1/(2*M) by positivity]
  have hmodes (k l : ℤ) (hk : |k| ≤ H) (hl : |l| ≤ H) (hne : k ≠ 0 ∨ l ≠ 0) :
      ‖average (fun t => BTCalculus.FejerBox.mode k l (sample M t)) T‖ ≤
        128*(M : ℝ)^(1/4 : ℝ)*(H : ℝ)^(1/30 : ℝ)*(T : ℝ)^(-1/60 : ℝ) := by
    simp_rw [sample_mode]
    rw [norm_average]
    have hk' : |(k : ℝ)| ≤ (H : ℝ) := by exact_mod_cast hk
    have hl' : |(l : ℝ)| ≤ (H : ℝ) := by exact_mod_cast hl
    exact OOEEffectiveModes.normalized_mode_bound k l hMr hHr hk' hl' hne T hT hHT
  have h := BTCalculus.FejerBox.finite_box_discrepancy (sample M)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 0+1)
    hcd hd hH (by omega) (by positivity) hmodes
  have he : (fun t => (sample M t).1 ∈ arc 0 (1/2) ∧
      (sample M t).2 ∈ arc (1/(2*M)) (2/(2*M))) = ReturnBox 2 1 M := by
    funext t
    exact propext (sample_mem_box hM t)
  have hv : ((1/2 : ℝ)-0)*(2/(2*M)-1/(2*M)) = 1/(4*M) := by ring
  simpa only [he, hv] using h

/-- Imposing the orbit threshold removes at most eight parameter indices. -/
theorem threshold_count_bound {M : ℕ} (hM : 0 < M) (T : ℕ) :
    |(count (ReturnParameter 2 1 M) T : ℝ) - count (ReturnBox 2 1 M) T| ≤ 8 := by
  have hlo : count (ReturnParameter 2 1 M) T ≤ count (ReturnBox 2 1 M) T := by
    apply card_le_card
    intro t ht
    exact mem_filter.mpr ⟨(mem_filter.mp ht).1, (mem_filter.mp ht).2.1⟩
  have hsub : (range T).filter (ReturnBox 2 1 M) ⊆
      (range T).filter (ReturnParameter 2 1 M) ∪ range 8 := by
    intro t ht
    obtain ⟨htT, htbox⟩ := mem_filter.mp ht
    by_cases ht8 : t < 8
    · exact mem_union_right _ (mem_range.mpr ht8)
    · apply mem_union_left
      refine mem_filter.mpr ⟨htT, htbox, ?_⟩
      have htM : t ≤ M*t := Nat.le_mul_of_pos_left t hM
      norm_num
      nlinarith
  have hhi : count (ReturnBox 2 1 M) T ≤ count (ReturnParameter 2 1 M) T + 8 := by
    exact (card_le_card hsub).trans (by simpa only [count, card_range] using
      (card_union_le ((range T).filter (ReturnParameter 2 1 M)) (range 8)))
  have hlo' : (count (ReturnParameter 2 1 M) T : ℝ) ≤ count (ReturnBox 2 1 M) T :=
    by exact_mod_cast hlo
  have hhi' : (count (ReturnBox 2 1 M) T : ℝ) ≤ count (ReturnParameter 2 1 M) T + 8 :=
    by exact_mod_cast hhi
  rw [abs_of_nonpos (sub_nonpos.mpr hlo')]
  linarith

/-- The explicit Fourier cutoff used for every positive sample length. -/
def cutoff (T : ℕ) : ℕ := ⌊(T : ℝ)^(1/32 : ℝ)⌋₊

theorem cutoff_pos {T : ℕ} (hT : 1 ≤ T) : 1 ≤ cutoff T := by
  change 1 ≤ ⌊(T : ℝ)^(1/32 : ℝ)⌋₊
  apply Nat.le_floor
  norm_num only [Nat.cast_one]
  exact Real.one_le_rpow (by exact_mod_cast hT) (by norm_num)

theorem cutoff_le {T : ℕ} (hT : 1 ≤ T) :
    (cutoff T : ℝ) ≤ (T : ℝ)^(1/4 : ℝ) := by
  exact (Nat.floor_le (by positivity)).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hT) (by norm_num))

theorem cutoff_sqrt_bound {T : ℕ} (hT : 1 ≤ T) :
    5 / Real.sqrt ((cutoff T : ℝ)+1) ≤ 5*(T : ℝ)^(-1/64 : ℝ) := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have he : Real.sqrt ((T : ℝ)^(1/32 : ℝ)) = (T : ℝ)^(1/64 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTp.le]
    norm_num
  have h := Real.sqrt_le_sqrt (Nat.lt_floor_add_one ((T : ℝ)^(1/32 : ℝ))).le
  rw [he] at h
  have hb := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 5)
    (Real.rpow_pos_of_pos hTp (1/64)) h
  have hn : (T : ℝ)^(-1/64 : ℝ) = ((T : ℝ)^(1/64 : ℝ))⁻¹ := by
    simpa only [neg_div] using Real.rpow_neg hTp.le (1/64)
  rw [hn]
  simpa only [cutoff, div_eq_mul_inv] using hb

theorem cutoff_rate_bound {T : ℕ} (hT : 1 ≤ T) :
    (cutoff T : ℝ)^(1/30 : ℝ)*(T : ℝ)^(-1/60 : ℝ) ≤ (T : ℝ)^(-1/64 : ℝ) := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  calc
    _ ≤ ((T : ℝ)^(1/32 : ℝ))^(1/30 : ℝ)*(T : ℝ)^(-1/60 : ℝ) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity)
        (Nat.floor_le (by positivity)) (by norm_num)) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul hTp.le, ← Real.rpow_add hTp]
      norm_num

theorem cutoff_log_bound {T : ℕ} (hT : 1 ≤ T) :
    (3+2*Real.log (cutoff T))^2 ≤ (3+Real.log T/16)^2 := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hH : (1 : ℝ) ≤ cutoff T := by exact_mod_cast cutoff_pos hT
  have hl := Real.log_le_log (by linarith : (0 : ℝ) < cutoff T)
    (show (cutoff T : ℝ) ≤ (T : ℝ)^(1/32 : ℝ) from Nat.floor_le (by positivity))
  rw [Real.log_rpow hTp] at hl
  have hlo := Real.log_nonneg hH
  nlinarith

/-- Q4's normalized box bound, with no lower threshold on M or T beyond positivity. -/
theorem box_discrepancy_power {M T : ℕ} (hM : 0 < M) (hT : 1 ≤ T) :
    |(count (ReturnBox 2 1 M) T : ℝ)/T - 1/(4*M)| ≤
      (5+128*(M : ℝ)^(1/4 : ℝ)*(3+Real.log T/16)^2)*(T : ℝ)^(-1/64 : ℝ) := by
  have h := box_discrepancy hM (cutoff_pos hT) hT (cutoff_le hT)
  have hs := cutoff_sqrt_bound hT
  have hr := cutoff_rate_bound hT
  have hl := cutoff_log_bound hT
  have hprod := mul_le_mul hl hr (by positivity)
    (by positivity : 0 ≤ (3+Real.log T/16)^2)
  have hprod' := mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ 128*(M : ℝ)^(1/4 : ℝ))
  nlinarith

/-- The first error bound for the exact thresholded parameter count.
Here `count P T = ((Finset.range T).filter P).card`, counting natural indices
`0 <= t < T`. The preceding `return_parameter_iff` expands the predicate
`ReturnParameter 2 1 M t` into the three explicit floor and threshold guards.
All displayed fractional powers are real powers and `Real.log` is the natural logarithm. -/
theorem count_error {M T : ℕ} (hM : 0 < M) (hT : 1 ≤ T) :
    |(count (ReturnParameter 2 1 M) T : ℝ) - T/(4*M)| ≤
      (5+128*(M : ℝ)^(1/4 : ℝ)*(3+Real.log T/16)^2)*(T : ℝ)^(63/64 : ℝ)+8 := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have h := mul_le_mul_of_nonneg_right (box_discrepancy_power hM hT) hTp.le
  have he : |(count (ReturnBox 2 1 M) T : ℝ)/T - 1/(4*M)| * (T : ℝ) =
      |(count (ReturnBox 2 1 M) T : ℝ)-T/(4*M)| := by
    calc
      _ = |(count (ReturnBox 2 1 M) T : ℝ)/T - 1/(4*M)| * |(T : ℝ)| := by
        rw [abs_of_pos hTp]
      _ = |((count (ReturnBox 2 1 M) T : ℝ)/T - 1/(4*M))*(T : ℝ)| :=
        (abs_mul _ _).symm
      _ = _ := by congr 1; field_simp
  have hp : (T : ℝ)^(-1/64 : ℝ)*(T : ℝ) = (T : ℝ)^(63/64 : ℝ) := by
    convert (Real.rpow_add hTp (-1/64) 1).symm using 1 <;> norm_num
  rw [he, mul_assoc, hp] at h
  have htri := abs_sub_le (count (ReturnParameter 2 1 M) T : ℝ)
    (count (ReturnBox 2 1 M) T : ℝ) ((T : ℝ)/(4*M))
  have hcut := threshold_count_bound hM T
  linarith

/-- A cubic exponential lower bound absorbs the logarithm with the constant 64. -/
theorem log_square_bound {x : ℝ} (hx : 1 ≤ x) :
    (3+Real.log x/16)^2 ≤ 64*x^(1/128 : ℝ) := by
  have hxp : 0 < x := by linarith
  let u := Real.log x/128
  have hu : 0 ≤ u := div_nonneg (Real.log_nonneg hx) (by norm_num)
  have he := Real.sum_le_exp_of_nonneg hu 4
  norm_num [sum_range_succ] at he
  have hp : (3+8*u)^2 ≤ 64*Real.exp u := by
    nlinarith [mul_nonneg hu (sq_nonneg (u-2)), sq_nonneg (u-5/4)]
  have hex : Real.exp u = x^(1/128 : ℝ) := by
    rw [Real.rpow_def_of_pos hxp]
    congr 1
    dsimp [u]
    ring
  rw [hex] at hp
  convert hp using 1
  dsimp [u]
  ring

/-- The displayed first error is bounded by the simpler power error. -/
theorem error_power_bound {M T : ℕ} (hM : 0 < M) (hT : 1 ≤ T) :
    (5+128*(M : ℝ)^(1/4 : ℝ)*(3+Real.log T/16)^2)*(T : ℝ)^(63/64 : ℝ)+8 ≤
      2^14*(M : ℝ)^(1/4 : ℝ)*(T : ℝ)^(127/128 : ℝ) := by
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hTp : (0 : ℝ) < T := by linarith
  have hMpow : 1 ≤ (M : ℝ)^(1/4 : ℝ) := Real.one_le_rpow hMr (by norm_num)
  have hTpow : 1 ≤ (T : ℝ)^(127/128 : ℝ) := Real.one_le_rpow hTr (by norm_num)
  have hpow := Real.rpow_le_rpow_of_exponent_le hTr (by norm_num : (63/64 : ℝ) ≤ 127/128)
  have hprod : 1 ≤ (M : ℝ)^(1/4 : ℝ)*(T : ℝ)^(127/128 : ℝ) :=
    one_le_mul_of_one_le_of_one_le hMpow hTpow
  have hsmall : (T : ℝ)^(63/64 : ℝ) ≤ (M : ℝ)^(1/4 : ℝ)*(T : ℝ)^(127/128 : ℝ) :=
    hpow.trans (le_mul_of_one_le_left (by positivity) hMpow)
  have hlog := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (log_square_bound hTr)
      (by positivity : 0 ≤ 128*(M : ℝ)^(1/4 : ℝ)))
    (by positivity : 0 ≤ (T : ℝ)^(63/64 : ℝ))
  have he : (T : ℝ)^(1/128 : ℝ)*(T : ℝ)^(63/64 : ℝ) = (T : ℝ)^(127/128 : ℝ) := by
    rw [← Real.rpow_add hTp]
    norm_num
  have hlog' : 128*(M : ℝ)^(1/4 : ℝ)*(3+Real.log T/16)^2*(T : ℝ)^(63/64 : ℝ) ≤
      8192*((M : ℝ)^(1/4 : ℝ)*(T : ℝ)^(127/128 : ℝ)) := by
    calc
      _ ≤ 128*(M : ℝ)^(1/4 : ℝ)*(64*(T : ℝ)^(1/128 : ℝ))*(T : ℝ)^(63/64 : ℝ) := hlog
      _ = _ := by rw [show 128*(M : ℝ)^(1/4 : ℝ)*(64*(T : ℝ)^(1/128 : ℝ))*
        (T : ℝ)^(63/64 : ℝ) = 8192*(M : ℝ)^(1/4 : ℝ)*
          ((T : ℝ)^(1/128 : ℝ)*(T : ℝ)^(63/64 : ℝ)) by ring, he]; ring
  norm_num only at ⊢
  nlinarith

/-- Q4: the all-modulus, all-length quantitative return count. -/
theorem count_error_power {M T : ℕ} (hM : 0 < M) (hT : 1 ≤ T) :
    |(count (ReturnParameter 2 1 M) T : ℝ) - T/(4*M)| ≤
      2^14*(M : ℝ)^(1/4 : ℝ)*(T : ℝ)^(127/128 : ℝ) :=
  (count_error hM hT).trans (error_power_bound hM hT)

/-- The explicit finite search length is `witnessCutoff M = 2^2176*M^160`.
This is the definition's value, uniform in the positive natural modulus M. -/
def witnessCutoff (M : ℕ) : ℕ := 2^2176*M^160

theorem witnessCutoff_pos {M : ℕ} (hM : 0 < M) : 0 < witnessCutoff M := by
  unfold witnessCutoff
  positivity

theorem witnessCutoff_root {M : ℕ} (hM : 0 < M) :
    (witnessCutoff M : ℝ)^(1/128 : ℝ) = 131072*(M : ℝ)^(5/4 : ℝ) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  simp only [witnessCutoff, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast (2 : ℝ) 2176, ← Real.rpow_natCast (M : ℝ) 160,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hMp.le]
  norm_num

theorem error_at_witnessCutoff {M : ℕ} (hM : 0 < M) :
    2^14*(M : ℝ)^(1/4 : ℝ)*(witnessCutoff M : ℝ)^(127/128 : ℝ) =
      (witnessCutoff M : ℝ)/(8*M) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hTp : (0 : ℝ) < witnessCutoff M := by exact_mod_cast witnessCutoff_pos hM
  have hMsplit : (M : ℝ)^(1/4 : ℝ)*(M : ℝ) = (M : ℝ)^(5/4 : ℝ) := by
    convert (Real.rpow_add hMp (1/4) 1).symm using 1 <;> norm_num
  apply (eq_div_iff (by positivity : (8*(M : ℝ)) ≠ 0)).2
  calc
    _ = (131072*((M : ℝ)^(1/4 : ℝ)*(M : ℝ)))*
        (witnessCutoff M : ℝ)^(127/128 : ℝ) := by norm_num; ring
    _ = (witnessCutoff M : ℝ)^(1/128 : ℝ)*
        (witnessCutoff M : ℝ)^(127/128 : ℝ) := by rw [hMsplit, witnessCutoff_root hM]
    _ = _ := by rw [← Real.rpow_add hTp]; norm_num

/-- At the explicit cutoff the actual return count is at least T/(8M), hence positive. -/
theorem count_at_witnessCutoff {M : ℕ} (hM : 0 < M) :
    (witnessCutoff M : ℝ)/(8*M) ≤ count (ReturnParameter 2 1 M) (witnessCutoff M) ∧
      0 < count (ReturnParameter 2 1 M) (witnessCutoff M) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hTp : (0 : ℝ) < witnessCutoff M := by exact_mod_cast witnessCutoff_pos hM
  have h := count_error_power hM (witnessCutoff_pos hM)
  rw [error_at_witnessCutoff hM] at h
  have hlo := (abs_le.mp h).1
  have he : (witnessCutoff M : ℝ)/(4*M) =
      (witnessCutoff M : ℝ)/(8*M) + (witnessCutoff M : ℝ)/(8*M) := by ring
  have hcount : (witnessCutoff M : ℝ)/(8*M) ≤
      count (ReturnParameter 2 1 M) (witnessCutoff M) := by linarith
  refine ⟨hcount, ?_⟩
  exact_mod_cast (lt_of_lt_of_le (div_pos hTp (by positivity)) hcount)

/-- A successful thresholded parameter exists strictly before the displayed cutoff. -/
theorem exists_bounded_parameter {M : ℕ} (hM : 0 < M) :
    ∃ t < 2^2176*M^160, ReturnParameter 2 1 M t := by
  have h := (count_at_witnessCutoff hM).2
  obtain ⟨t, ht⟩ := card_pos.mp h
  obtain ⟨htT, hp⟩ := mem_filter.mp ht
  exact ⟨t, mem_range.mp htT, hp⟩

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 5000 in
/-- The parameter cutoff gives the strict bound on the actual natural starting value. -/
theorem start_bound {M t : ℕ} (hM : 0 < M) (ht : t < 2^2176*M^160) :
    (1+2*M*t)^2 < 2^4354*M^322 := by
  have hs : 1+2*M*t < 2*M*(2^2176*M^160) := by
    have h := Nat.mul_le_mul_left (2*M) (Nat.succ_le_of_lt ht)
    rw [Nat.mul_succ] at h
    omega
  have hp := Nat.pow_lt_pow_left hs (by norm_num : 2 ≠ 0)
  have he : (2*M*(2^2176*M^160))^2 = 2^4354*M^322 := by
    calc
      _ = (2^2177*M^161)^2 := by
        congr 1
        rw [show 2177 = 2176+1 by omega, show 161 = 160+1 by omega,
          pow_succ 2 2176, pow_succ M 160]
        ac_rfl
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]
  rwa [he] at hp

/-- Here `ModularReturn 2 1 M n` means
`n % 2 = 1` and `itinerary n 3 = [Branch.odd, Branch.odd, Branch.even]`,
`(forall j <= 3, n <= floorPower^[j] n)`, `n < floorPower^[3] n`,
and `n % (2*M) = 1` and `floorPower^[3] n % (2*M) = 1`.
The Juggler map is `floorPower n = if n % 2 = 0 then Nat.sqrt n else Nat.sqrt (n^3)`.
`itinerary n 3` lists the source parities of n and its first two iterates;
`floorPower^[j]` denotes j-fold iteration. Thus this is an actual OOE orbit. -/
theorem exists_bounded_modular_return {M : ℕ} (hM : 0 < M) :
    ∃ t < 2^2176*M^160, ReturnParameter 2 1 M t ∧
      (1+2*M*t)^2 < 2^4354*M^322 ∧ ModularReturn 2 1 M ((1+2*M*t)^2) := by
  obtain ⟨t, ht, hbox, hsize⟩ := exists_bounded_parameter hM
  refine ⟨t, ht, ⟨hbox, hsize⟩, start_bound hM ht, ?_⟩
  exact modular_return_of_box (k := 1) hM (by norm_num) hsize hbox

end Problems.Juggler.OOEEffectiveReturn
