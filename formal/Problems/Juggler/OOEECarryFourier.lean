import Problems.Juggler.OOEEFourierModes
import BTCalculus.FejerWeighted

/-! # The remaining fractional-part carry contribution on actual OOEE cells -/

noncomputable section

namespace Problems.Juggler.OOEECarryFourier

open Finset
open BTCalculus.WeylDifferencing BTCalculus.FejerWeighted BTCalculus.SecondDerivative
open Problems.Juggler.OOEECurvature Problems.Juggler.OOEECarryCells
open Problems.Juggler.OOEEFourierModes

def modeBound (P L : ℝ) : ℝ := (64*L+16)*P^(5/16:ℝ)+1

theorem fourier_phase (k : ℤ) (x : ℝ) :
    fourier k (x : UnitAddCircle) = phase ((k:ℝ)*x) := by
  rw [fourier_coe_apply]
  unfold phase
  congr 1
  push_cast
  simp only [div_one]
  ring

theorem phase_add (a b : ℝ) : phase a * phase b = phase (a+b) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fractional_cell_bound {P a h u v w eps t L : ℝ} {G : ℤ} (N H : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcell : ∀ n < N, ⌊gap h (a+2*n)⌋ = G)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (ht : 0 ≤ t ∧ t ≤ 2*P)
    (hH : 3 ≤ H) (hHP : (H:ℝ) ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, ((Int.fract ((a+2*n+t)^(3/2:ℝ))-1/2:ℝ):ℂ)*
      phase (cellPhase (2*h) u v w (G+eps) (a+2*n))‖ ≤
      3*mass H*modeBound P L+5*N/Real.sqrt ((H:ℝ)+1) := by
  have hP0 : 0 < P := by linarith
  have hB : 0 ≤ modeBound P L := by dsimp [modeBound]; positivity
  have hkR (k : ℤ) (hk : k ≠ 0) : 1 ≤ |(k:ℝ)| := by
    exact_mod_cast (show (1:ℤ) ≤ |k| by have := abs_pos.mpr hk; omega)
  have hkP (k : ℤ) (hk : |k| ≤ H) : |(k:ℝ)| ≤ P^(1/4:ℝ) := by
    have hi : |(k:ℝ)| ≤ H := by exact_mod_cast hk
    exact hi.trans hHP
  have hp : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, fourier k (((a+2*(n:ℝ)+t)^(3/2:ℝ):ℝ) : UnitAddCircle)‖ ≤ modeBound P L := by
    intro k hk hk0
    simp_rw [fourier_phase]
    exact (power_mode_sum N hP ha hb ht (hkR k hk0) (hkP k hk) hL hN).trans (by dsimp [modeBound]; linarith)
  have hw : ∀ k : ℤ, |k| ≤ H → k ≠ 0 →
      ‖∑ n ∈ range N, phase (cellPhase (2*h) u v w (G+eps) (a+2*n))*
        fourier k (((a+2*(n:ℝ)+t)^(3/2:ℝ):ℝ) : UnitAddCircle)‖ ≤ modeBound P L := by
    intro k hk hk0
    simp_rw [fourier_phase, phase_add]
    exact perturbed_samples_bound N hP ha hb hh hhP hsize hu hfreq hcell heps ht
      (hkR k hk0) (hkP k hk) hdom hL hN
  have hs := weighted_centered_fract_bound (fun n => (a+2*n+t)^(3/2:ℝ))
    (fun n => phase (cellPhase (2*h) u v w (G+eps) (a+2*n))) H N hH hB hB
    (fun n _ => (phase_norm _).le) hp hw
  nlinarith

def carryTerm (h u v w x : ℝ) : ℂ :=
  ((Int.fract (x^(3/2:ℝ))-Int.fract ((x+2*h)^(3/2:ℝ)):ℝ):ℂ)*
    (phase (cellPhase (2*h) u v w ((⌊gap h x⌋:ℝ)+1) x)-
     phase (cellPhase (2*h) u v w (⌊gap h x⌋:ℝ) x))

theorem carry_cell_bound {P a h u v w L : ℝ} {G : ℤ} (N H : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcell : ∀ n < N, ⌊gap h (a+2*n)⌋ = G)
    (hH : 3 ≤ H) (hHP : (H:ℝ) ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, carryTerm h u v w (a+2*n)‖ ≤
      12*mass H*modeBound P L+20*N/Real.sqrt ((H:ℝ)+1) := by
  have hh0 : 0 ≤ h := by linarith
  have hhP' : h ≤ P := hhP.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hP (by norm_num : (1/16:ℝ) ≤ 1))
  let Z (t eps : ℝ) := ∑ n ∈ range N, ((Int.fract ((a+2*n+t)^(3/2:ℝ))-1/2:ℝ):ℂ)*
    phase (cellPhase (2*h) u v w (G+eps) (a+2*n))
  have hz (t eps : ℝ) (ht : 0 ≤ t ∧ t ≤ 2*P) (heps : 0 ≤ eps ∧ eps ≤ 1) :=
    fractional_cell_bound N H hP ha hb hh hhP hsize hu hfreq hcell heps ht hH hHP hdom hL hN
  have h00 := hz 0 0 ⟨le_refl 0, by linarith⟩ ⟨le_refl 0, by norm_num⟩
  have h01 := hz 0 1 ⟨le_refl 0, by linarith⟩ ⟨by norm_num, le_refl 1⟩
  have ht0 := hz (2*h) 0 ⟨by positivity, by linarith⟩ ⟨le_refl 0, by norm_num⟩
  have ht1 := hz (2*h) 1 ⟨by positivity, by linarith⟩ ⟨by norm_num, le_refl 1⟩
  have he : (∑ n ∈ range N, carryTerm h u v w (a+2*n)) =
      (Z 0 1-Z 0 0)-(Z (2*h) 1-Z (2*h) 0) := by
    dsimp [Z]
    simp only [← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    rw [carryTerm, hcell n (mem_range.mp hn)]
    simp only [add_zero, Complex.ofReal_sub]
    ring
  have hn := norm_sub_le (Z 0 1-Z 0 0) (Z (2*h) 1-Z (2*h) 0)
  have hn0 := norm_sub_le (Z 0 1) (Z 0 0)
  have hn1 := norm_sub_le (Z (2*h) 1) (Z (2*h) 0)
  rw [he]
  change ‖Z 0 0‖ ≤ _ at h00
  change ‖Z 0 1‖ ≤ _ at h01
  change ‖Z (2*h) 0‖ ≤ _ at ht0
  change ‖Z (2*h) 1‖ ≤ _ at ht1
  have heq : 4*(5*(N:ℝ)/Real.sqrt ((H:ℝ)+1)) = 20*N/Real.sqrt ((H:ℝ)+1) := by ring
  nlinarith

theorem carry_floor_fibre_sum {P a h u v w L : ℝ} (N H : ℕ) (G : ℤ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hH : 3 ≤ H) (hHP : (H:ℝ) ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ {n ∈ range N | ⌊gap h (a+2*(n:ℕ))⌋ = G}, carryTerm h u v w (a+2*n)‖ ≤
      12*mass H*modeBound P L+20*N/Real.sqrt ((H:ℝ)+1) := by
  classical
  let S : Finset ℕ := {n ∈ range N | ⌊gap h (a+2*(n:ℕ))⌋ = G}
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hB : 0 ≤ modeBound P L := by unfold modeBound; positivity
  have hmass : 0 ≤ mass H := by
    unfold mass
    have hharm : (0:ℝ) ≤ harmonic H := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact sum_nonneg (fun _ _ => by positivity)
    linarith
  have hm (i j : ℕ) (hij : i ≤ j) : gap h (a+2*i) ≤ gap h (a+2*j) := by
    have hc : (i:ℝ) ≤ j := by exact_mod_cast hij
    exact gap_mono hP0 (by linarith [Nat.cast_nonneg (α := ℝ) i]) (by linarith) hh0
  have hconv : ∀ i ∈ S, ∀ j ∈ S, ∀ n, i ≤ n → n ≤ j → n ∈ S := by
    intro i hi j hj n hin hnj
    have hi' := mem_filter.mp hi
    have hj' := mem_filter.mp hj
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by have := mem_range.mp hj'.1; omega), ?_⟩
    have hl := Int.floor_mono (hm i n hin)
    have hr := Int.floor_mono (hm n j hnj)
    rw [hi'.2] at hl
    rw [hj'.2] at hr
    exact le_antisymm hr hl
  change ‖∑ n ∈ S, carryTerm h u v w (a+2*n)‖ ≤ _
  by_cases hs : S.Nonempty
  · let start := S.min' hs
    let len := S.max' hs+1-start
    have hmin : start ≤ S.max' hs := S.min'_le _ (S.max'_mem hs)
    have hmax : S.max' hs < N := mem_range.mp (mem_filter.mp (S.max'_mem hs)).1
    have hlen : start+len ≤ N := by dsimp [len]; omega
    have hlenR : (start:ℝ)+len ≤ N := by exact_mod_cast hlen
    have hlenN : (len:ℝ) ≤ N := by exact_mod_cast (show len ≤ N by omega)
    have hmem (n : ℕ) (hn : n < len) : start+n ∈ S := by
      apply hconv _ (S.min'_mem hs) _ (S.max'_mem hs) <;> dsimp [start, len] at * <;> omega
    have hshift (n : ℕ) : a+2*(start+n:ℕ) = (a+2*start)+2*n := by push_cast; ring
    have hcell : ∀ n < len, ⌊gap h ((a+2*start)+2*n)⌋ = G := by
      intro n hn
      have hg := (mem_filter.mp (hmem n hn)).2
      simpa only [hshift] using hg
    have hw := carry_cell_bound len H hP
      (show P ≤ a+2*start by linarith [Nat.cast_nonneg (α := ℝ) start])
      (show (a+2*start)+2*len ≤ 2*P by linarith)
      hh hhP hsize hu hfreq hcell hH hHP hdom hL (hlenN.trans hN)
    rw [interval_sum S hs hconv]
    have hweight : 20*(len:ℝ)/Real.sqrt ((H:ℝ)+1) ≤ 20*N/Real.sqrt ((H:ℝ)+1) := by gcongr
    have hw' := hw.trans (add_le_add le_rfl hweight)
    simpa only [hshift, start, len] using hw'
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp only [sum_empty, norm_zero]
    positivity

theorem carry_contribution_bound {P a h u v w L : ℝ} (N H : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hH : 3 ≤ H) (hHP : (H:ℝ) ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, carryTerm h u v w (a+2*n)‖ ≤
      (3*L+2)*(12*mass H*modeBound P L+20*N/Real.sqrt ((H:ℝ)+1)) := by
  classical
  let K := Icc ⌊gap h a⌋ ⌊gap h (a+2*N)⌋
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hB : 0 ≤ (12*mass H*modeBound P L+20*N/Real.sqrt ((H:ℝ)+1)) := by
    have hm : 0 ≤ mass H := by
      unfold mass
      have hharm : (0:ℝ) ≤ harmonic H := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        exact sum_nonneg (fun _ _ => by positivity)
      linarith
    have hb : 0 ≤ modeBound P L := by unfold modeBound; positivity
    positivity
  have hmap (n : ℕ) (hn : n ∈ range N) : ⌊gap h (a+2*n)⌋ ∈ K := by
    have hnR : (n:ℝ) ≤ N := by exact_mod_cast (mem_range.mp hn).le
    apply mem_Icc.mpr
    exact ⟨Int.floor_mono (gap_mono hP0 ha (by linarith [Nat.cast_nonneg (α := ℝ) n]) hh0),
      Int.floor_mono (gap_mono hP0 (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith) hh0)⟩
  rw [← sum_fiberwise_of_maps_to hmap (fun n => carryTerm h u v w (a+2*n))]
  calc ‖∑ G ∈ K, ∑ n ∈ {n ∈ range N | ⌊gap h (a+2*(n:ℕ))⌋ = G}, carryTerm h u v w (a+2*n)‖
      ≤ ∑ G ∈ K, ‖∑ n ∈ {n ∈ range N | ⌊gap h (a+2*(n:ℕ))⌋ = G}, carryTerm h u v w (a+2*n)‖ := norm_sum_le _ _
    _ ≤ ∑ _G ∈ K, (12*mass H*modeBound P L+20*N/Real.sqrt ((H:ℝ)+1)) := sum_le_sum (fun G _ =>
      carry_floor_fibre_sum N H G hP ha hb hh hhP hsize hu hfreq hH hHP hdom hL hN)
    _ = (K.card:ℝ)*((12*mass H*modeBound P L+20*N/Real.sqrt ((H:ℝ)+1))) := by simp; ring
    _ ≤ (3*L+2)*(12*mass H*modeBound P L+20*N/Real.sqrt ((H:ℝ)+1)) := by
      have hc := mul_le_mul_of_nonneg_right (carry_level_count N hP ha hh hhP hL hN) hB
      simpa only [K, mul_assoc] using hc

theorem carry_scale_log_bound {P L : ℝ} (N H : ℕ) (hP : 1 ≤ P) (hL : 0 ≤ L)
    (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) (hH : 3 ≤ H)
    (hHP : (H:ℝ) ≤ P^(1/4:ℝ)) (hPH : P^(1/4:ℝ) ≤ (H:ℝ)+1) :
    12*mass H*modeBound P L+20*N/Real.sqrt ((H:ℝ)+1) ≤
      (12*(3+2*Real.log P)*(64*L+17)+20*L)*P^(5/16:ℝ) := by
  have hP0 : 0 < P := by linarith
  have hH0 : (0:ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hHP' : (H:ℝ) ≤ P := hHP.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hP (by norm_num : (1/4:ℝ) ≤ 1))
  have hm : mass H ≤ 3+2*Real.log P := by
    have hharm := harmonic_le_one_add_log H
    have hlog := Real.log_le_log hH0 hHP'
    dsimp [mass]
    linarith
  have hB : modeBound P L ≤ (64*L+17)*P^(5/16:ℝ) := by
    have hp := Real.one_le_rpow hP (by norm_num : (0:ℝ) ≤ 5/16)
    dsimp [modeBound]
    nlinarith
  have hsqrt : P^(1/8:ℝ) ≤ Real.sqrt ((H:ℝ)+1) := by
    have hs := Real.sqrt_le_sqrt hPH
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP0.le] at hs
    convert hs using 1
    norm_num
  have hterm : 20*N/Real.sqrt ((H:ℝ)+1) ≤ 20*L*P^(5/16:ℝ) := by
    have hratio : P^(7/16:ℝ)/P^(1/8:ℝ) = P^(5/16:ℝ) := by
      rw [← Real.rpow_sub hP0]
      norm_num
    calc _ ≤ 20*(L*P^(7/16:ℝ))/P^(1/8:ℝ) := by gcongr
         _ = 20*L*(P^(7/16:ℝ)/P^(1/8:ℝ)) := by ring
         _ = _ := by rw [hratio]
  have hnonneg : 0 ≤ 3+2*Real.log P := by linarith [Real.log_nonneg hP]
  have hB0 : 0 ≤ modeBound P L := by dsimp [modeBound]; positivity
  have hmain : 12*mass H*modeBound P L ≤
      12*(3+2*Real.log P)*((64*L+17)*P^(5/16:ℝ)) := by gcongr
  nlinarith

theorem carry_scale_power_bound {P L : ℝ} (N H : ℕ) (hP : 1 ≤ P) (hL : 0 ≤ L)
    (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) (hH : 3 ≤ H)
    (hHP : (H:ℝ) ≤ P^(1/4:ℝ)) (hPH : P^(1/4:ℝ) ≤ (H:ℝ)+1) :
    12*mass H*modeBound P L+20*N/Real.sqrt ((H:ℝ)+1) ≤
      (420*(64*L+17)+20*L)*P^(3/8:ℝ) := by
  have hP0 : 0 < P := by linarith
  have hlog := Real.log_le_rpow_div hP0.le (by norm_num : (0:ℝ) < 1/16)
  have hp1 := Real.one_le_rpow hP (by norm_num : (0:ℝ) ≤ 1/16)
  have hm : 3+2*Real.log P ≤ 35*P^(1/16:ℝ) := by norm_num at hlog; linarith
  have hp : P^(1/16:ℝ)*P^(5/16:ℝ) = P^(3/8:ℝ) := by
    rw [← Real.rpow_add hP0]
    norm_num
  have hl : P^(5/16:ℝ) ≤ P^(3/8:ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  calc _ ≤ (12*(3+2*Real.log P)*(64*L+17)+20*L)*P^(5/16:ℝ) :=
         carry_scale_log_bound N H hP hL hN hH hHP hPH
       _ = 12*(3+2*Real.log P)*(64*L+17)*P^(5/16:ℝ)+20*L*P^(5/16:ℝ) := by ring
       _ ≤ 12*(35*P^(1/16:ℝ))*(64*L+17)*P^(5/16:ℝ)+20*L*P^(3/8:ℝ) := by gcongr
       _ = _ := by rw [← hp]; ring

/-- The full fractional-part carry term has a smaller power than the smooth contribution. -/
theorem carry_contribution_log_bound {P a h u v w L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcut : 3 ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, carryTerm h u v w (a+2*n)‖ ≤
      (3*L+2)*(12*(3+2*Real.log P)*(64*L+17)+20*L)*P^(5/16:ℝ) := by
  let H := ⌊P^(1/4:ℝ)⌋₊
  have hH : 3 ≤ H := Nat.le_floor hcut
  have hHP : (H:ℝ) ≤ P^(1/4:ℝ) := Nat.floor_le (by positivity)
  have hPH : P^(1/4:ℝ) ≤ (H:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hs := carry_contribution_bound N H hP ha hb hh hhP hsize hu hfreq hH hHP hdom hL hN
  have hb' := mul_le_mul_of_nonneg_left (carry_scale_log_bound N H hP hL hN hH hHP hPH)
    (show 0 ≤ 3*L+2 by positivity)
  exact hs.trans (by simpa only [mul_assoc] using hb')

def retainedPhase (h u v w x : ℝ) : ℝ :=
  cellPhase (2*h) u v w ((⌊(x+2*h)^(3/2:ℝ)⌋-⌊x^(3/2:ℝ)⌋:ℤ):ℝ) x

/-- The retained carry correlation is bounded after all its actual cells are assembled. -/
theorem retained_correlation_bound {P a h u v w L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcut : 3 ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, phase (retainedPhase h u v w (a+2*n))‖ ≤
      (3*L+2)*(4*(64*L*Real.sqrt u+16/Real.sqrt u+1)+420*(64*L+17)+20*L)*P^(3/8:ℝ) := by
  let H := ⌊P^(1/4:ℝ)⌋₊
  have hH : 3 ≤ H := Nat.le_floor hcut
  have hHP : (H:ℝ) ≤ P^(1/4:ℝ) := Nat.floor_le (by positivity)
  have hPH : P^(1/4:ℝ) ≤ (H:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hs := smooth_contribution_power_bound N hP ha hb hh hhP hsize hu hfreq hL hN
  have hc := carry_contribution_bound N H hP ha hb hh hhP hsize hu hfreq hH hHP hdom hL hN
  have hm := mul_le_mul_of_nonneg_left (carry_scale_power_bound N H hP hL hN hH hHP hPH)
    (show 0 ≤ 3*L+2 by positivity)
  have he : (∑ n ∈ range N, phase (retainedPhase h u v w (a+2*n))) =
      (∑ n ∈ range N, smoothTerm h u v w (a+2*n)) +
      ∑ n ∈ range N, carryTerm h u v w (a+2*n) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    exact carry_decomposition h u v w (a+2*n)
  rw [he]
  exact (norm_add_le _ _).trans (by nlinarith)

/-- Every extra cutoff and dominance requirement is eventually valid for fixed coefficients. -/
theorem carry_size_conditions_eventually {u : ℝ} (hu : 0 < u) (v w : ℝ) :
    ∃ P0 : ℝ, ∀ P : ℝ, P0 ≤ P → 1 ≤ P ∧ 1024 ≤ P^(15/16:ℝ) ∧
      |v| + |w| ≤ u*P^(3/4:ℝ)/1024 ∧ 3 ≤ P^(1/4:ℝ) ∧ 32*u ≤ P^(3/16:ℝ) := by
  obtain ⟨P0, hP0⟩ := size_conditions_eventually hu v w
  have hcut := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_ge_atTop 3
  have hdom := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/16)).eventually_ge_atTop (32*u)
  apply Filter.eventually_atTop.1
  filter_upwards [Filter.eventually_ge_atTop P0, hcut, hdom] with P hP hcut hdom
  exact ⟨(hP0 P hP).1, (hP0 P hP).2.1, (hP0 P hP).2.2, hcut, hdom⟩

end Problems.Juggler.OOEECarryFourier
