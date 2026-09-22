import Problems.Juggler.OOEECurvature
import Problems.Juggler.GapCells
import BTCalculus.PartialSummation

/-! # The weighted smooth contribution on actual OOEE carry cells

The cells and weights are read from the actual smooth gap. Floor boundaries
are retained by removing at most one final term from each derivative-test
application.
-/

noncomputable section

namespace Problems.Juggler.OOEECarryCells

open Finset
open BTCalculus.WeylDifferencing BTCalculus.SecondDerivative BTCalculus.PartialSummation
open Problems.Juggler.OOEECurvature

def gap (h x : ℝ) : ℝ := powerDiff (2*h) (3/2) x

theorem gap_derivative {h x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    HasDerivAt (gap h) ((3/2:ℝ)*powerDiff (2*h) (1/2) x) x := by
  have hd := deriv_powerDiff hx (show 0 < x+2*h by linarith) (3/2)
  norm_num at hd
  exact hd

theorem gap_derivative_bounds {P x h : ℝ} (hP : 0 < P) (hPx : P ≤ x) (hh : 0 ≤ h) :
    0 ≤ (3/2:ℝ)*powerDiff (2*h) (1/2) x ∧
      (3/2:ℝ)*powerDiff (2*h) (1/2) x ≤ (3/2:ℝ)*h*P^(-1/2:ℝ) := by
  have hx : 0 < x := hP.trans_le hPx
  have hd : ∀ y ∈ Set.Icc x (x+2*h),
      HasDerivAt (fun z : ℝ => z^(1/2:ℝ)) ((1/2:ℝ)*y^(-1/2:ℝ)) y := by
    intro y hy
    have hp := deriv_power (hx.trans_le hy.1) (1/2)
    norm_num at hp ⊢
    exact hp
  have hb := secant_bounds _ _ (lo := 0) (hi := (1/2:ℝ)*P^(-1/2:ℝ))
    (show x ≤ x+2*h by linarith) hd (fun y hy => by
      constructor
      · have hy0 : 0 ≤ y := (hx.trans_le hy.1).le
        positivity
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hP (hPx.trans hy.1) (by norm_num)) (by norm_num))
  dsimp [powerDiff]
  constructor <;> nlinarith [hb.1, hb.2]

/-- Quantitative monotonicity controls both the occupied floors and the cell weights. -/
theorem gap_increment_bounds {P a b h : ℝ} (hP : 0 < P) (hPa : P ≤ a)
    (hab : a ≤ b) (hh : 0 ≤ h) :
    0 ≤ gap h b-gap h a ∧ gap h b-gap h a ≤ (3/2:ℝ)*h*P^(-1/2:ℝ)*(b-a) := by
  have hs := secant_bounds (gap h) (fun x => (3/2:ℝ)*powerDiff (2*h) (1/2) x)
    hab (fun x hx => gap_derivative (hP.trans_le (hPa.trans hx.1)) hh)
    (fun x hx => gap_derivative_bounds hP (hPa.trans hx.1) hh)
  simpa only [zero_mul] using hs

theorem gap_mono {P a b h : ℝ} (hP : 0 < P) (hPa : P ≤ a)
    (hab : a ≤ b) (hh : 0 ≤ h) : gap h a ≤ gap h b :=
  sub_nonneg.mp (gap_increment_bounds hP hPa hab hh).1

def cellBound (P u L : ℝ) : ℝ :=
  (64*L*Real.sqrt u+16/Real.sqrt u)*P^(3/8:ℝ)

theorem cellBound_nonneg {P u L : ℝ} (hP : 0 ≤ P) (hu : 0 < u) (hL : 0 ≤ L) :
    0 ≤ cellBound P u L := by unfold cellBound; positivity

/-- Sampled floor conditions suffice: only the final term can cross the closed support. -/
theorem cell_sum_of_samples {P a h u v w eps L : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcell : ∀ n < N, ⌊gap h (a+2*n)⌋ = G)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, phase (cellPhase (2*h) u v w (G+eps) (a+2*n))‖ ≤
      cellBound P u L+1 := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hB := cellBound_nonneg hP0.le hu hL
  cases N with
  | zero => simpa using (show 0 ≤ cellBound P u L+1 by linarith)
  | succ N =>
    have hn : (N:ℝ) ≤ N+1 := by linarith
    have h0 := floor_cell_bounds (hcell 0 (by omega))
    have hlast := floor_cell_bounds (hcell N (by omega))
    simp only [Nat.cast_zero, mul_zero, add_zero] at h0
    have hclosed : ∀ x ∈ Set.Icc a (a+2*N),
        (G:ℝ) ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ (G:ℝ)+1 := by
      intro x hx
      have hl := gap_mono hP0 ha hx.1 hh0
      have hr := gap_mono hP0 (ha.trans hx.1) hx.2 hh0
      exact ⟨h0.1.trans hl, hr.trans hlast.2⟩
    have hs := cell_sum_power_bound N hP ha (by push_cast at hb; linarith)
      hh hhP hsize hu hfreq hclosed heps hL (by push_cast at hN; linarith)
    rw [sum_range_succ]
    calc ‖_+_‖ ≤ ‖∑ n ∈ range N, phase (cellPhase (2*h) u v w (G+eps) (a+2*n))‖ +
        ‖phase (cellPhase (2*h) u v w (G+eps) (a+2*N))‖ := norm_add_le _ _
      _ ≤ cellBound P u L+1 := by
        rw [phase_norm]
        exact add_le_add hs (le_refl 1)

def smoothTerm (h u v w x : ℝ) : ℂ :=
  ((1-Int.fract (gap h x):ℝ):ℂ)*phase (cellPhase (2*h) u v w (⌊gap h x⌋:ℝ) x) +
  ((Int.fract (gap h x):ℝ):ℂ)*phase (cellPhase (2*h) u v w ((⌊gap h x⌋:ℝ)+1) x)

/-- The two monotone weights on one actual sampled cell cost a factor of at most four. -/
theorem weighted_cell_sum {P a h u v w L : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcell : ∀ n < N, ⌊gap h (a+2*n)⌋ = G)
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, smoothTerm h u v w (a+2*n)‖ ≤ 4*(cellBound P u L+1) := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  let z : ℕ → ℝ := fun n => Int.fract (gap h (a+2*n))
  have hz (n : ℕ) : 0 ≤ z n ∧ z n ≤ 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hm (n : ℕ) (hn : n+1 < N) : z n ≤ z (n+1) := by
    have hg := gap_mono hP0 (show P ≤ a+2*n by linarith [Nat.cast_nonneg (α := ℝ) n])
      (show a+2*n ≤ a+2*(n+1:ℕ) by push_cast; linarith) hh0
    dsimp [z]
    rw [Int.fract, Int.fract, hcell n (by omega), hcell (n+1) hn]
    exact sub_le_sub_right hg _
  have hB : 0 ≤ cellBound P u L+1 := by have := cellBound_nonneg hP0.le hu hL; linarith
  have hprefix (eps : ℝ) (heps : 0 ≤ eps ∧ eps ≤ 1) (k : ℕ) (hk : k ≤ N) :
      ‖∑ n ∈ range k, phase (cellPhase (2*h) u v w (G+eps) (a+2*n))‖ ≤ cellBound P u L+1 := by
    have hkR : (k:ℝ) ≤ N := by exact_mod_cast hk
    exact cell_sum_of_samples k hP ha (by linarith) hh hhP hsize hu hfreq
      (fun n hn => hcell n (lt_of_lt_of_le hn hk)) heps hL (hkR.trans hN)
  have hleft := monotone_weighted_sum_bound
    (fun n => phase (cellPhase (2*h) u v w (G+(0:ℝ)) (a+2*n))) (fun n => 1-z n) N hB
    (fun n _ => ⟨by linarith [(hz n).2], by linarith [(hz n).1]⟩)
    (Or.inr (fun n hn => by linarith [hm n hn])) (hprefix 0 (by norm_num))
  have hright := monotone_weighted_sum_bound
    (fun n => phase (cellPhase (2*h) u v w (G+(1:ℝ)) (a+2*n))) z N hB
    (fun n _ => hz n) (Or.inl hm) (hprefix 1 (by norm_num))
  have he : (∑ n ∈ range N, smoothTerm h u v w (a+2*n)) =
      (∑ n ∈ range N, ((1-z n:ℝ):ℂ)*phase (cellPhase (2*h) u v w (G+0) (a+2*n))) +
      ∑ n ∈ range N, (z n:ℂ)*phase (cellPhase (2*h) u v w (G+1) (a+2*n)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    simp only [smoothTerm, hcell n (mem_range.mp hn), add_zero, z]
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

/-- There are uniformly boundedly many possible integer carry levels on the short interval. -/
theorem carry_level_count {P a h L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ))
    (_hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ((Icc ⌊gap h a⌋ ⌊gap h (a+2*N)⌋).card:ℝ) ≤ 3*L+2 := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hg := gap_increment_bounds hP0 ha (show a ≤ a+2*N by linarith [Nat.cast_nonneg (α := ℝ) N]) hh0
  have hmono : ⌊gap h a⌋ ≤ ⌊gap h (a+2*N)⌋ := Int.floor_mono (by linarith [hg.1])
  have he : ((Icc ⌊gap h a⌋ ⌊gap h (a+2*N)⌋).card:ℝ) =
      (⌊gap h (a+2*N)⌋:ℝ)+1-(⌊gap h a⌋:ℝ) := by
    exact_mod_cast Int.card_Icc_of_le _ _ (show ⌊gap h a⌋ ≤ ⌊gap h (a+2*N)⌋+1 by omega)
  have hp : P^(1/16:ℝ)*P^(7/16:ℝ)*P^(-1/2:ℝ) = 1 := by
    rw [← Real.rpow_add hP0, ← Real.rpow_add hP0]
    norm_num
  have hspan : (3/2:ℝ)*h*P^(-1/2:ℝ)*((a+2*N)-a) ≤ 3*L := by
    calc _ = 3*h*N*P^(-1/2:ℝ) := by ring
         _ ≤ 3*P^(1/16:ℝ)*(L*P^(7/16:ℝ))*P^(-1/2:ℝ) := by gcongr
         _ = 3*L*(P^(1/16:ℝ)*P^(7/16:ℝ)*P^(-1/2:ℝ)) := by ring
         _ = 3*L := by rw [hp, mul_one]
  have hflo := Int.lt_floor_add_one (gap h a)
  have hfhi := Int.floor_le (gap h (a+2*N))
  rw [he]
  linarith [hg.2]

/-- Every occupied floor fibre is a consecutive block of actual sample indices. -/
theorem weighted_floor_fibre_sum {P a h u v w L : ℝ} (N : ℕ) (G : ℤ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ {n ∈ range N | ⌊gap h (a+2*(n:ℕ))⌋ = G}, smoothTerm h u v w (a+2*n)‖ ≤
      4*(cellBound P u L+1) := by
  classical
  let S : Finset ℕ := {n ∈ range N | ⌊gap h (a+2*(n:ℕ))⌋ = G}
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hB := cellBound_nonneg hP0.le hu hL
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
  change ‖∑ n ∈ S, smoothTerm h u v w (a+2*n)‖ ≤ _
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
    have hw := weighted_cell_sum len hP
      (show P ≤ a+2*start by linarith [Nat.cast_nonneg (α := ℝ) start])
      (show (a+2*start)+2*len ≤ 2*P by linarith)
      hh hhP hsize hu hfreq hcell hL (hlenN.trans hN)
    rw [interval_sum S hs hconv]
    simpa only [hshift, start, len] using hw
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp only [sum_empty, norm_zero]
    positivity

/-- The actual smooth part of the carry decomposition, summed over every cell. -/
theorem smooth_contribution_bound {P a h u v w L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, smoothTerm h u v w (a+2*n)‖ ≤
      (3*L+2)*4*(cellBound P u L+1) := by
  classical
  let K := Icc ⌊gap h a⌋ ⌊gap h (a+2*N)⌋
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hB : 0 ≤ 4*(cellBound P u L+1) := by
    have := cellBound_nonneg hP0.le hu hL
    positivity
  have hmap (n : ℕ) (hn : n ∈ range N) : ⌊gap h (a+2*n)⌋ ∈ K := by
    have hnR : (n:ℝ) ≤ N := by exact_mod_cast (mem_range.mp hn).le
    apply mem_Icc.mpr
    exact ⟨Int.floor_mono (gap_mono hP0 ha (by linarith [Nat.cast_nonneg (α := ℝ) n]) hh0),
      Int.floor_mono (gap_mono hP0 (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith) hh0)⟩
  rw [← sum_fiberwise_of_maps_to hmap (fun n => smoothTerm h u v w (a+2*n))]
  calc ‖∑ G ∈ K, ∑ n ∈ {n ∈ range N | ⌊gap h (a+2*(n:ℕ))⌋ = G}, smoothTerm h u v w (a+2*n)‖
      ≤ ∑ G ∈ K, ‖∑ n ∈ {n ∈ range N | ⌊gap h (a+2*(n:ℕ))⌋ = G}, smoothTerm h u v w (a+2*n)‖ := norm_sum_le _ _
    _ ≤ ∑ _G ∈ K, 4*(cellBound P u L+1) := sum_le_sum (fun G _ =>
      weighted_floor_fibre_sum N G hP ha hb hh hhP hsize hu hfreq hL hN)
    _ = (K.card:ℝ)*(4*(cellBound P u L+1)) := by simp
    _ ≤ (3*L+2)*4*(cellBound P u L+1) := by
      have hc := mul_le_mul_of_nonneg_right (carry_level_count N hP ha hh hhP hL hN) hB
      simpa only [K, mul_assoc] using hc

/-- A single explicit constant gives the written power bound for the weighted smooth part. -/
theorem smooth_contribution_power_bound {P a h u v w L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, smoothTerm h u v w (a+2*n)‖ ≤
      4*(3*L+2)*(64*L*Real.sqrt u+16/Real.sqrt u+1)*P^(3/8:ℝ) := by
  have hp := Real.one_le_rpow hP (by norm_num : (0:ℝ) ≤ 3/8)
  have hi : cellBound P u L+1 ≤ (64*L*Real.sqrt u+16/Real.sqrt u+1)*P^(3/8:ℝ) := by
    unfold cellBound
    nlinarith
  have hs := smooth_contribution_bound N hP ha hb hh hhP hsize hu hfreq hL hN
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ (3*L+2)*4 by positivity)
  exact hs.trans (by nlinarith [hm])

/-- Exact equation (12): the omitted term is precisely the difference of the two sawtooths. -/
theorem carry_decomposition (h u v w x : ℝ) :
    phase (cellPhase (2*h) u v w
      ((⌊(x+2*h)^(3/2:ℝ)⌋-⌊x^(3/2:ℝ)⌋:ℤ):ℝ) x) =
    smoothTerm h u v w x +
      ((Int.fract (x^(3/2:ℝ))-Int.fract ((x+2*h)^(3/2:ℝ)):ℝ):ℂ)*
        (phase (cellPhase (2*h) u v w ((⌊gap h x⌋:ℝ)+1) x)-
         phase (cellPhase (2*h) u v w (⌊gap h x⌋:ℝ) x)) := by
  let X := x^(3/2:ℝ)
  let Y := (x+2*h)^(3/2:ℝ)
  have hadd : X+gap h x = Y := by dsimp [X,Y,gap,powerDiff]; ring
  have hfloor := floor_add_eq_add_carry X (gap h x)
  have hfract := carry_eq_fract_add_sub_fract X (gap h x)
  rw [hadd] at hfloor hfract
  change phase (cellPhase (2*h) u v w ((⌊Y⌋-⌊X⌋:ℤ):ℝ) x) = _
  unfold smoothTerm
  by_cases hc : 1 ≤ Int.fract X+Int.fract (gap h x)
  · rw [if_pos hc] at hfloor hfract
    have hg : ((⌊Y⌋-⌊X⌋:ℤ):ℝ) = (⌊gap h x⌋:ℝ)+1 := by rw [hfloor]; push_cast; ring
    have hf : Int.fract X-Int.fract Y = 1-Int.fract (gap h x) := by linarith
    change phase (cellPhase (2*h) u v w ((⌊Y⌋-⌊X⌋:ℤ):ℝ) x) =
      _ + ((Int.fract X-Int.fract Y:ℝ):ℂ)*_
    rw [hg, hf]
    push_cast
    ring
  · rw [if_neg hc] at hfloor hfract
    have hg : ((⌊Y⌋-⌊X⌋:ℤ):ℝ) = (⌊gap h x⌋:ℝ) := by rw [hfloor]; push_cast; ring
    have hf : Int.fract X-Int.fract Y = -Int.fract (gap h x) := by linarith
    change phase (cellPhase (2*h) u v w ((⌊Y⌋-⌊X⌋:ℤ):ℝ) x) =
      _ + ((Int.fract X-Int.fract Y:ℝ):ℂ)*_
    rw [hg, hf]
    push_cast
    ring

end Problems.Juggler.OOEECarryCells
