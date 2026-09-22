import BTCalculus.KusminLandau
import Mathlib.Data.Int.Interval

/-! # A quantitative second-derivative estimate

The proof splits monotone phase increments into integer bands. Near an
integer, separation bounds the number of terms; away from integers,
Kusmin--Landau bounds the entire consecutive block.
-/

noncomputable section

namespace BTCalculus.SecondDerivative

open Finset
open scoped ComplexConjugate
open BTCalculus.WeylDifferencing BTCalculus.KusminLandau

theorem phase_int (k : ℤ) : phase (k : ℝ) = 1 := by
  unfold phase
  have he : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [he]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem phase_sub_int (x : ℝ) (k : ℤ) : phase (x - k) = phase x := by
  rw [← phase_mul_conj, phase_int]
  simp

theorem phase_sub_int_mul (x : ℝ) (k : ℤ) (n : ℕ) :
    phase (x - k * n) = phase x := by
  simpa using phase_sub_int x (k * n)

theorem card_le_span (s : Finset ℕ) (hs : s.Nonempty) :
    (s.card : ℝ) ≤ (s.max' hs : ℝ) - s.min' hs + 1 := by
  have hsub : s ⊆ Icc (s.min' hs) (s.max' hs) := by
    intro n hn
    exact mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
  have hcard := card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hle : s.min' hs ≤ s.max' hs := s.min'_le _ (s.max'_mem hs)
  have hc : (s.card : ℝ) ≤ ((s.max' hs + 1 - s.min' hs : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at hc
  linarith

theorem separated_card (s : Finset ℕ) (g : ℕ → ℝ) {lam lo hi : ℝ}
    (hlam : 0 < lam) (hwidth : lo ≤ hi)
    (hbound : ∀ n ∈ s, lo ≤ g n ∧ g n ≤ hi)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → lam * ((j : ℝ) - i) ≤ g j - g i) :
    (s.card : ℝ) ≤ (hi - lo) / lam + 1 := by
  by_cases hs : s.Nonempty
  · have hspan := card_le_span s hs
    have hlo := hbound _ (s.min'_mem hs)
    have hhi := hbound _ (s.max'_mem hs)
    have hgap := hsep _ (s.min'_mem hs) _ (s.max'_mem hs)
      (s.min'_le _ (s.max'_mem hs))
    have h : (s.max' hs : ℝ) - s.min' hs ≤ (hi - lo) / lam := by
      apply (le_div_iff₀ hlam).mpr
      nlinarith
    linarith
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    rw [he]
    simp only [card_empty, Nat.cast_zero]
    positivity

theorem interval_sum (s : Finset ℕ) (hs : s.Nonempty)
    (hconv : ∀ i ∈ s, ∀ j ∈ s, ∀ n, i ≤ n → n ≤ j → n ∈ s)
    (z : ℕ → ℂ) :
    ∑ n ∈ s, z n = ∑ n ∈ range (s.max' hs + 1 - s.min' hs), z (s.min' hs + n) := by
  symm
  refine sum_bij (fun n _ => s.min' hs + n) ?_ ?_ ?_ ?_
  · intro n hn
    have hn' := mem_range.mp hn
    apply hconv _ (s.min'_mem hs) _ (s.max'_mem hs) <;> omega
  · intro a _ b _ hab
    omega
  · intro n hn
    refine ⟨n - s.min' hs, ?_, ?_⟩
    · have hl := s.min'_le n hn
      have hu := s.le_max' n hn
      simp only [mem_range]
      omega
    · have := s.min'_le n hn
      omega
  · intros
    rfl

theorem good_interval_sum (f : ℕ → ℝ) (s : Finset ℕ) (k : ℤ) {δ : ℝ}
    (hδ : 0 < δ)
    (hconv : ∀ i ∈ s, ∀ j ∈ s, ∀ n, i ≤ n → n ≤ j → n ∈ s)
    (hband : ∀ n ∈ s, (k : ℝ) + δ ≤ f (n + 1) - f n ∧
      f (n + 1) - f n ≤ k + 1 - δ)
    (hmono : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → f (i+1)-f i ≤ f (j+1)-f j) :
    ‖∑ n ∈ s, phase (f n)‖ ≤ 1 / δ := by
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let L := s.max' hs + 1 - a
    have hmem (n : ℕ) (hn : n < L) : a + n ∈ s := by
      apply hconv _ (s.min'_mem hs) _ (s.max'_mem hs) <;> dsimp [a, L] at * <;> omega
    let F := fun n : ℕ => f (a+n) - (k : ℝ) * ((a+n : ℕ) : ℝ)
    have hd (n : ℕ) : F (n+1) - F n = f (a+n+1)-f (a+n) - k := by
      simp only [F, Nat.add_assoc, Nat.cast_add, Nat.cast_one]
      ring
    have h := kusmin_landau_sum_range F L hδ
      (fun n hn => by have hb := hband _ (hmem n hn); rw [hd]; constructor <;> linarith)
      (Or.inl (fun n hn => by
        rw [hd, hd]
        have hm := hmono _ (hmem n (by omega)) _ (hmem (n+1) hn) (by omega)
        simpa only [Nat.add_assoc] using sub_le_sub_right hm (k : ℝ)))
    rw [interval_sum s hs hconv]
    simpa only [F, phase_sub_int_mul, L, a] using h
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp only [sum_empty, norm_zero]
    positivity

theorem norm_phase_sum_le_card (f : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ n ∈ s, phase (f n)‖ ≤ s.card := by
  simpa only [phase_norm, sum_const, nsmul_eq_mul, mul_one] using
    norm_sum_le s (fun n => phase (f n))

/-- Each integer band has two short resonant ends and one consecutive good block. -/
theorem increment_band_sum (f : ℕ → ℝ) (N : ℕ) (k : ℤ) {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hsep : ∀ i, i < N → ∀ j, j < N → i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j+1)-f j) - (f (i+1)-f i)) :
    ‖∑ n ∈ {n ∈ range N | ⌊f (n+1)-f n⌋ = k}, phase (f n)‖ ≤
      2 * δ / lam + 2 + 1 / δ := by
  classical
  let d := fun n => f (n+1)-f n
  let s := {n ∈ range N | ⌊d n⌋ = k}
  let l := s.filter (fun n => d n < k + δ)
  let r := s.filter (fun n => k + 1 - δ < d n)
  let g := s.filter (fun n => k + δ ≤ d n ∧ d n ≤ k + 1 - δ)
  have hs (n : ℕ) (hn : n ∈ s) : n < N ∧ (k : ℝ) ≤ d n ∧ d n < k + 1 := by
    obtain ⟨hn, hk⟩ := mem_filter.mp hn
    exact ⟨mem_range.mp hn, Int.floor_eq_iff.mp hk⟩
  have hm (i j : ℕ) (hi : i < N) (hj : j < N) (hij : i ≤ j) : d i ≤ d j := by
    have h := hsep i hi j hj hij
    have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp [d]
    nlinarith
  have hsub_l : l ⊆ s := filter_subset _ _
  have hsub_r : r ⊆ s := filter_subset _ _
  have hsub_g : g ⊆ s := filter_subset _ _
  have hlcard : (l.card : ℝ) ≤ δ / lam + 1 := by
    have h := separated_card l d hlam (show (k : ℝ) ≤ k + δ by linarith)
      (fun n hn => ⟨(hs n (hsub_l hn)).2.1, (mem_filter.mp hn).2.le⟩)
      (fun i hi j hj hij => hsep i (hs i (hsub_l hi)).1 j (hs j (hsub_l hj)).1 hij)
    simpa only [add_sub_cancel_left] using h
  have hrcard : (r.card : ℝ) ≤ δ / lam + 1 := by
    have h := separated_card r d hlam (show (k : ℝ)+1-δ ≤ k+1 by linarith)
      (fun n hn => ⟨(mem_filter.mp hn).2.le, (hs n (hsub_r hn)).2.2.le⟩)
      (fun i hi j hj hij => hsep i (hs i (hsub_r hi)).1 j (hs j (hsub_r hj)).1 hij)
    convert h using 1
    ring
  have hg : ‖∑ n ∈ g, phase (f n)‖ ≤ 1 / δ := by
    apply good_interval_sum f g k hδ
    · intro i hi j hj n hin hnj
      have hiN := (hs i (hsub_g hi)).1
      have hjN := (hs j (hsub_g hj)).1
      have hnN : n < N := by omega
      have hlow := (mem_filter.mp hi).2.1.trans (hm i n hiN hnN hin)
      have hupp := (hm n j hnN hjN hnj).trans (mem_filter.mp hj).2.2
      have hsn : n ∈ s := mem_filter.mpr ⟨mem_range.mpr hnN,
        Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩⟩
      exact mem_filter.mpr ⟨hsn, hlow, hupp⟩
    · exact fun n hn => (mem_filter.mp hn).2
    · exact fun i hi j hj hij => hm i j (hs i (hsub_g hi)).1 (hs j (hsub_g hj)).1 hij
  have hid : (∑ n ∈ s, phase (f n)) =
      (∑ n ∈ l, phase (f n)) + (∑ n ∈ g, phase (f n)) + ∑ n ∈ r, phase (f n) := by
    dsimp [l, g, r]
    rw [sum_filter (s := s), sum_filter (s := s), sum_filter (s := s),
      ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    by_cases hl : d n < k + δ
    · have hr : ¬ k + 1 - δ < d n := by linarith
      simp [hl, hr, not_le.mpr hl]
    · by_cases hr : k + 1 - δ < d n
      · simp [hl, hr, not_le.mpr hr]
      · simp [hl, hr, not_lt.mp hl, not_lt.mp hr]
  change ‖∑ n ∈ s, phase (f n)‖ ≤ _
  rw [hid]
  have hh := norm_add_le ((∑ n ∈ l, phase (f n)) + ∑ n ∈ g, phase (f n))
    (∑ n ∈ r, phase (f n))
  have hh2 := norm_add_le (∑ n ∈ l, phase (f n)) (∑ n ∈ g, phase (f n))
  have hl := (norm_phase_sum_le_card f l).trans hlcard
  have hr := (norm_phase_sum_le_card f r).trans hrcard
  rw [mul_div_assoc]
  linarith

/-- Integer-band decomposition with a freely chosen distance from resonance. -/
theorem increment_gap_sum_bound (f : ℕ → ℝ) (N : ℕ) {lam upper δ : ℝ}
    (hlam : 0 < lam) (hupper : 0 ≤ upper) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hcurv : ∀ i, i < N → ∀ j, j < N → i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j+1)-f j) - (f (i+1)-f i) ∧
      (f (j+1)-f j) - (f (i+1)-f i) ≤ upper * ((j : ℝ) - i)) :
    ‖∑ n ∈ range N, phase (f n)‖ ≤
      (upper * N + 2) * (2 * δ / lam + 2 + 1 / δ) := by
  classical
  by_cases hN : 0 < N
  · let d := fun n => f (n+1)-f n
    let K := Icc ⌊d 0⌋ ⌊d (N-1)⌋
    let B := 2 * δ / lam + 2 + 1 / δ
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hm (i j : ℕ) (hi : i < N) (hj : j < N) (hij : i ≤ j) : d i ≤ d j := by
      have h := (hcurv i hi j hj hij).1
      have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
      dsimp [d]
      nlinarith
    have hmap (n : ℕ) (hn : n ∈ range N) : ⌊d n⌋ ∈ K := by
      have hnN := mem_range.mp hn
      exact mem_Icc.mpr ⟨Int.floor_mono (hm 0 n hN hnN (by omega)),
        Int.floor_mono (hm n (N-1) hnN (by omega) (by omega))⟩
    have hcard : (K.card : ℝ) ≤ upper * N + 2 := by
      have hfloor := Int.floor_mono (hm 0 (N-1) hN (by omega) (by omega))
      have he : (K.card : ℝ) = (⌊d (N-1)⌋ : ℝ) + 1 - ⌊d 0⌋ := by
        exact_mod_cast Int.card_Icc_of_le _ _ (show ⌊d 0⌋ ≤ ⌊d (N-1)⌋ + 1 by omega)
      have hlo := Int.lt_floor_add_one (d 0)
      have hhi := Int.floor_le (d (N-1))
      have hspan := (hcurv 0 hN (N-1) (by omega) (by omega)).2
      have hcast : ((N-1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
      simp only [Nat.cast_zero, sub_zero] at hspan
      change d (N-1) - d 0 ≤ upper * ((N-1 : ℕ) : ℝ) at hspan
      rw [he]
      nlinarith
    rw [← sum_fiberwise_of_maps_to hmap (fun n => phase (f n))]
    calc ‖∑ k ∈ K, ∑ n ∈ {n ∈ range N | ⌊d n⌋ = k}, phase (f n)‖
        ≤ ∑ k ∈ K, ‖∑ n ∈ {n ∈ range N | ⌊d n⌋ = k}, phase (f n)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ K, B := sum_le_sum (fun k _ =>
        increment_band_sum f N k hlam hδ hδhalf (fun i hi j hj hij => (hcurv i hi j hj hij).1))
      _ = K.card * B := by simp
      _ ≤ (upper * N + 2) * B := mul_le_mul_of_nonneg_right hcard hB
  · have he : N = 0 := by omega
    subst N
    simp only [range_zero, sum_empty, norm_zero, Nat.cast_zero, mul_zero, zero_add]
    positivity

/-- A finite second-derivative estimate stated directly for separated increments. -/
theorem second_difference_sum_bound (f : ℕ → ℝ) (N : ℕ) {lam C : ℝ}
    (hlam : 0 < lam) (hC : 1 ≤ C)
    (hcurv : ∀ i, i < N → ∀ j, j < N → i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j+1)-f j) - (f (i+1)-f i) ∧
      (f (j+1)-f j) - (f (i+1)-f i) ≤ C * lam * ((j : ℝ) - i)) :
    ‖∑ n ∈ range N, phase (f n)‖ ≤ 4 * C * N * Real.sqrt lam + 8 / Real.sqrt lam := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hs2 := Real.sq_sqrt hlam.le
  have hC0 : 0 ≤ C := by linarith
  by_cases hsmall : Real.sqrt lam ≤ 1 / 2
  · have h := increment_gap_sum_bound f N hlam (mul_nonneg hC0 hlam.le) hs hsmall hcurv
    have hb : 2 * Real.sqrt lam / lam + 2 + 1 / Real.sqrt lam ≤ 4 / Real.sqrt lam := by
      apply (le_div_iff₀ hs).mpr
      have hid : (2 * Real.sqrt lam / lam + 2 + 1 / Real.sqrt lam) * Real.sqrt lam =
          3 + 2 * Real.sqrt lam := by field_simp; nlinarith
      rw [hid]
      linarith
    apply h.trans
    calc (C * lam * N + 2) * (2 * Real.sqrt lam / lam + 2 + 1 / Real.sqrt lam)
        ≤ (C * lam * N + 2) * (4 / Real.sqrt lam) := by gcongr
      _ = _ := by field_simp; linear_combination -(4 * C * (N : ℝ)) * hs2
  · have h := norm_phase_sum_le_card f (range N)
    simp only [card_range] at h
    apply h.trans
    have hNs : (N : ℝ) ≤ 2 * N * Real.sqrt lam := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hCN : 0 ≤ (C - 1) * N * Real.sqrt lam := by positivity
    have hpos : 0 < 8 / Real.sqrt lam := by positivity
    nlinarith

/-- Derivative bounds control every secant, including a degenerate interval. -/
theorem secant_bounds (f g : ℝ → ℝ) {a b lo hi : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a b, lo ≤ g x ∧ g x ≤ hi) :
    lo * (b-a) ≤ f b-f a ∧ f b-f a ≤ hi * (b-a) := by
  rcases eq_or_lt_of_le hab with he | hlt
  · subst b
    simp
  · have hc : ContinuousOn f (Set.Icc a b) :=
      fun x hx => (hd x hx).continuousAt.continuousWithinAt
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f g hlt hc
      (fun x hx => hd x ⟨hx.1.le, hx.2.le⟩)
    have hgb := hg x ⟨hx.1.le, hx.2.le⟩
    have hid : g x * (b-a) = f b-f a := (eq_div_iff (by linarith)).mp he
    constructor <;> nlinarith

/-- Positive continuous curvature separates the actual discrete phase increments. -/
theorem increment_curvature (f g q : ℝ → ℝ) (a : ℝ) (N : ℕ) {lam upper : ℝ}
    (hf : ∀ x ∈ Set.Icc a (a+N), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a (a+N), HasDerivAt g (q x) x)
    (hq : ∀ x ∈ Set.Icc a (a+N), lam ≤ q x ∧ q x ≤ upper)
    (i : ℕ) (_hi : i < N) (j : ℕ) (hj : j < N) (hij : i ≤ j) :
    lam * ((j : ℝ)-i) ≤
      (f (a+(j+1 : ℕ))-f (a+j)) - (f (a+(i+1 : ℕ))-f (a+i)) ∧
    (f (a+(j+1 : ℕ))-f (a+j)) - (f (a+(i+1 : ℕ))-f (a+i)) ≤
      upper * ((j : ℝ)-i) := by
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hsub (x : ℝ) (hx : x ∈ Set.Icc (a+i) (a+j)) :
      x ∈ Set.Icc a (a+N) ∧ x+1 ∈ Set.Icc a (a+N) := by
    constructor <;> constructor <;> linarith [hx.1, hx.2]
  have hF (x : ℝ) (hx : x ∈ Set.Icc (a+i) (a+j)) :
      HasDerivAt (fun y => f (y+1)-f y) (g (x+1)-g x) x := by
    have h := ((hf (x+1) (hsub x hx).2).comp x ((hasDerivAt_id x).add_const 1)).fun_sub
      (hf x (hsub x hx).1)
    simpa only [mul_one, Function.comp_def, id_eq, Pi.sub_apply] using h
  have hG (x : ℝ) (hx : x ∈ Set.Icc (a+i) (a+j)) :
      lam ≤ g (x+1)-g x ∧ g (x+1)-g x ≤ upper := by
    have hsub' (y : ℝ) (hy : y ∈ Set.Icc x (x+1)) : y ∈ Set.Icc a (a+N) := by
      have hh := hsub x hx
      constructor <;> linarith [hy.1, hy.2, hh.1.1, hh.2.2]
    have h := secant_bounds g q (show x ≤ x+1 by linarith)
      (fun y hy => hg y (hsub' y hy)) (fun y hy => hq y (hsub' y hy))
    simpa only [add_sub_cancel_left, mul_one] using h
  have h := secant_bounds (fun x => f (x+1)-f x) (fun x => g (x+1)-g x)
    (show a+(i : ℝ) ≤ a+j by linarith) hF hG
  simpa only [add_sub_add_left_eq_sub, Nat.cast_add, Nat.cast_one, add_assoc] using h

/-- The quantitative second-derivative test on a translated lattice interval. -/
theorem second_derivative_sum_bound (f g q : ℝ → ℝ) (a : ℝ) (N : ℕ) {lam C : ℝ}
    (hlam : 0 < lam) (hC : 1 ≤ C)
    (hf : ∀ x ∈ Set.Icc a (a+N), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a (a+N), HasDerivAt g (q x) x)
    (hq : ∀ x ∈ Set.Icc a (a+N), lam ≤ q x ∧ q x ≤ C * lam) :
    ‖∑ n ∈ range N, phase (f (a+n))‖ ≤
      4 * C * N * Real.sqrt lam + 8 / Real.sqrt lam := by
  apply second_difference_sum_bound (fun n => f (a+n)) N hlam hC
  exact increment_curvature f g q a N hf hg hq

theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  simpa [phase] using (phase_mul_conj 0 x).symm

/-- Either sign of curvature is allowed, with one sign throughout the interval. -/
theorem signed_second_derivative_sum_bound (f g q : ℝ → ℝ) (a : ℝ) (N : ℕ)
    {lam C : ℝ} (hlam : 0 < lam) (hC : 1 ≤ C)
    (hf : ∀ x ∈ Set.Icc a (a+N), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a (a+N), HasDerivAt g (q x) x)
    (hq : (∀ x ∈ Set.Icc a (a+N), lam ≤ q x ∧ q x ≤ C * lam) ∨
      (∀ x ∈ Set.Icc a (a+N), -C * lam ≤ q x ∧ q x ≤ -lam)) :
    ‖∑ n ∈ range N, phase (f (a+n))‖ ≤
      4 * C * N * Real.sqrt lam + 8 / Real.sqrt lam := by
  rcases hq with hp | hn
  · exact second_derivative_sum_bound f g q a N hlam hC hf hg hp
  · have h := second_derivative_sum_bound (fun x => -f x) (fun x => -g x)
      (fun x => -q x) a N hlam hC
      (fun x hx => (hf x hx).neg) (fun x hx => (hg x hx).neg)
      (fun x hx => by have hh := hn x hx; constructor <;> linarith)
    simpa only [phase_neg, ← map_sum, Complex.norm_conj] using h

/-- The same quantitative test on the lattice of spacing two used by OOEE. -/
theorem odd_lattice_second_derivative_sum_bound (f g q : ℝ → ℝ) (a : ℝ) (N : ℕ)
    {lam C : ℝ} (hlam : 0 < lam) (hC : 1 ≤ C)
    (hf : ∀ x ∈ Set.Icc a (a+2*N), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a (a+2*N), HasDerivAt g (q x) x)
    (hq : (∀ x ∈ Set.Icc a (a+2*N), lam ≤ q x ∧ q x ≤ C * lam) ∨
      (∀ x ∈ Set.Icc a (a+2*N), -C * lam ≤ q x ∧ q x ≤ -lam)) :
    ‖∑ n ∈ range N, phase (f (a+2*n))‖ ≤
      8 * C * N * Real.sqrt lam + 4 / Real.sqrt lam := by
  have hmap (x : ℝ) (hx : x ∈ Set.Icc 0 (0+(N : ℝ))) :
      a+2*x ∈ Set.Icc a (a+2*N) := by constructor <;> linarith [hx.1, hx.2]
  have hd (x : ℝ) : HasDerivAt (fun y => a+2*y) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).const_add a
  have hF (x : ℝ) (hx : x ∈ Set.Icc 0 (0+(N : ℝ))) :
      HasDerivAt (fun y => f (a+2*y)) (2*g (a+2*x)) x := by
    simpa [Function.comp_def, mul_comm] using (hf _ (hmap x hx)).comp x (hd x)
  have hG (x : ℝ) (hx : x ∈ Set.Icc 0 (0+(N : ℝ))) :
      HasDerivAt (fun y => 2*g (a+2*y)) (4*q (a+2*x)) x := by
    have h : HasDerivAt (fun y => 2*g (a+2*y)) (2*(q (a+2*x)*2)) x := by
      simpa only [Function.comp_def] using ((hg _ (hmap x hx)).comp x (hd x)).const_mul 2
    convert h using 1
    ring
  have hQ : (∀ x ∈ Set.Icc 0 (0+(N : ℝ)), 4*lam ≤ 4*q (a+2*x) ∧
      4*q (a+2*x) ≤ C*(4*lam)) ∨
      (∀ x ∈ Set.Icc 0 (0+(N : ℝ)), -C*(4*lam) ≤ 4*q (a+2*x) ∧
      4*q (a+2*x) ≤ -(4*lam)) := by
    rcases hq with hp | hn
    · left
      intro x hx
      have hh := hp _ (hmap x hx)
      constructor <;> nlinarith
    · right
      intro x hx
      have hh := hn _ (hmap x hx)
      constructor <;> nlinarith
  have h := signed_second_derivative_sum_bound (fun x => f (a+2*x))
    (fun x => 2*g (a+2*x)) (fun x => 4*q (a+2*x)) 0 N (by positivity) hC hF hG hQ
  have hs : Real.sqrt (4*lam) = 2*Real.sqrt lam := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [zero_add, hs] at h
  convert h using 1
  ring

end BTCalculus.SecondDerivative
