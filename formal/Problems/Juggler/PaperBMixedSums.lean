/-
# Paper B, Theorem 4.5: restricted mixed exponential sums

`docs/theory/juggler_parity_discrepancy_note.md`, Theorem 4.5. For fixed `C` and a nonzero
integer triple `(i, j, k)` with `max(|i|, |j|, |k|) ≤ C P^{1/24}`, the sum of
`e((i/2) n^{3/2} + (j/2) m(n)^{3/2} + (k/2) n^{9/8})` over the odd `n ∈ (P, 2P]`, where
`m(n) = ⌊n^{3/2}⌋`, is `O_C(P^{23/24})`.

* `differenced_window_sum`: for `j ≠ 0`, van der Corput on the odd lattice with
  `H = ⌊P^{1/12}⌋` and Lemma 4.4 (`PaperBSmallShift.small_shift_window_sum`) for every shift;
* `smooth_window_sum`: for `j = 0 ≠ i`, the second-derivative test with curvature
  `|i| P^{-1/2}` (`OOEESmoothModes.smooth_sum_positive`);
* `slow_window_sum`: for `i = j = 0 ≠ k`, the second-derivative test with curvature
  `|k| P^{-7/8}`;
* `mixed_sum`: **Theorem 4.5**, in the printed form.
-/

import Problems.Juggler.PaperBSmallShift
import Problems.Juggler.OOEESmoothModes

noncomputable section

namespace Problems.Juggler

namespace PaperBMixedSums

open Finset Real
open BTCalculus.WeylDifferencing BTCalculus.SecondDerivative
open PaperBSmallShift

/-- The phase of (4.11): `(i/2) x^{3/2} + (j/2) ⌊x^{3/2}⌋^{3/2} + (k/2) x^{9/8}`. -/
def mixedPhase (i j k : ℤ) (x : ℝ) : ℝ :=
  (i / 2 : ℝ) * x ^ (3 / 2 : ℝ) + (j / 2 : ℝ) * ((⌊x ^ (3 / 2 : ℝ)⌋ : ℤ) : ℝ) ^ (3 / 2 : ℝ) +
    (k / 2 : ℝ) * x ^ (9 / 8 : ℝ)

/-- The summand of (4.4) is `Δ_h` of the phase of (4.11). -/
theorem smallShiftPhase_eq_sub (i j k : ℤ) (h x : ℝ) :
    smallShiftPhase i j k h x = mixedPhase i j k (x + 2 * h) - mixedPhase i j k x := by
  unfold smallShiftPhase mixedPhase
  ring

/-- Negating the triple negates the phase. -/
theorem mixedPhase_neg (i j k : ℤ) (x : ℝ) :
    mixedPhase (-i) (-j) (-k) x = -mixedPhase i j k x := by
  unfold mixedPhase
  push_cast
  ring

/-- With `j = 0` the phase is Paper C's `originalPhase 0 i k`. -/
theorem mixedPhase_zero (i k : ℤ) (x : ℝ) :
    mixedPhase i 0 k x = OOEEPhaseComparison.originalPhase 0 i k x := by
  unfold mixedPhase OOEEPhaseComparison.originalPhase
  push_cast
  ring

/-- `x/2 ≤ ⌊x⌋₊` for `x ≥ 1`. -/
theorem half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (by simpa using hx)
  have h2 := Nat.lt_floor_add_one x
  linarith

/-- Dropping the last term of a unimodular sum costs at most one. -/
theorem norm_window_succ (f : ℕ → ℝ) (M : ℕ) :
    ‖∑ m ∈ range (M + 1), phase (f m)‖ ≤ ‖∑ m ∈ range M, phase (f m)‖ + 1 := by
  rw [sum_range_succ]
  refine (norm_add_le _ _).trans ?_
  rw [phase_norm]

/-- Conjugation for sums over a range. -/
theorem norm_range_phase_neg (f : ℕ → ℝ) (N : ℕ) :
    ‖∑ m ∈ range N, phase (-f m)‖ = ‖∑ m ∈ range N, phase (f m)‖ :=
  norm_sum_phase_neg (range N) f

/-! ## `j ≠ 0`: van der Corput and Lemma 4.4 -/

/-- **Theorem 4.5 for `j ≠ 0`, on an odd window.** -/
theorem differenced_window_sum (C : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ P : ℝ, 1 ≤ P →
    ∀ i j k : ℤ, j ≠ 0 →
    |(i : ℝ)| ≤ C * P ^ (1 / 24 : ℝ) → |(j : ℝ)| ≤ C * P ^ (1 / 24 : ℝ) →
    |(k : ℝ)| ≤ C * P ^ (1 / 24 : ℝ) → ∀ r₀ N : ℕ, P < ((2 * r₀ + 1 : ℕ) : ℝ) →
    (1 ≤ N → ((2 * r₀ + 1 : ℕ) : ℝ) + 2 * ((N - 1 : ℕ) : ℝ) ≤ 2 * P) →
    ‖∑ m ∈ range N, phase (mixedPhase i j k ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ))‖ ≤
      K * P ^ (23 / 24 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := small_shift_window_sum C
  refine ⟨√(36 + 24 * K) + 1, by positivity, ?_⟩
  intro P hP i j k hj0 hi hj hk r₀ N ha hb
  have hP0 : 0 ≤ P := by linarith
  set T := P ^ (1 / 24 : ℝ) with hTdef
  have hT24 : T ^ 24 = P := by rw [rpow_24_pow hP0 24 1 (by norm_num), rpow_one]
  have hT23 : T ^ 23 = P ^ (23 / 24 : ℝ) := rpow_24_pow hP0 23 _ (by norm_num)
  have hT21 : T ^ 21 = P ^ (7 / 8 : ℝ) := rpow_24_pow hP0 21 _ (by norm_num)
  have hT2 : T ^ 2 = P ^ (1 / 12 : ℝ) := rpow_24_pow hP0 2 _ (by norm_num)
  have hT1 : 1 ≤ T := one_le_rpow hP (by norm_num)
  rw [← hT23]
  have hN3 := window_card_le r₀ N hP ha hb
  rw [← hT24] at hN3
  have hT2_1 : (1 : ℝ) ≤ T ^ 2 := one_le_pow₀ hT1
  have hT2_23 : T ^ 2 ≤ T ^ 23 := pow_le_pow_right₀ hT1 (by norm_num)
  set H := ⌊T ^ 2⌋₊ with hHdef
  have hHlo : T ^ 2 / 2 ≤ (H : ℝ) := half_le_floor hT2_1
  have hHhi : (H : ℝ) ≤ T ^ 2 := Nat.floor_le (by positivity)
  have hH1 : 1 ≤ H := Nat.le_floor (by simpa using hT2_1)
  have hKT : 0 ≤ (√(36 + 24 * K) + 1) * T ^ 23 := by positivity
  rcases lt_or_ge N H with hNH | hHN
  · -- a short window
    refine (norm_window_le _ N).trans ?_
    have : (N : ℝ) ≤ H := by exact_mod_cast hNH.le
    have : T ^ 23 ≤ √(36 + 24 * K) * T ^ 23 + T ^ 23 := by
      have : 0 ≤ √(36 + 24 * K) * T ^ 23 := by positivity
      linarith
    nlinarith
  have hvdc := odd_lattice_van_der_corput (fun n : ℕ => mixedPhase i j k n) (2 * r₀ + 1)
    hH1 hHN
  have hsum : ∀ d ∈ Ico 1 H, ‖∑ n ∈ range (N - d), phase
      ((fun n : ℕ => mixedPhase i j k n) (2 * r₀ + 1 + 2 * (n + d)) -
        (fun n : ℕ => mixedPhase i j k n) (2 * r₀ + 1 + 2 * n))‖ ≤ K * T ^ 21 * (2 * T) := by
    intro d hd
    rw [mem_Ico] at hd
    have hdH : d < H := hd.2
    have hdr : (d : ℝ) ≤ T ^ 2 := by
      have : (d : ℝ) ≤ H := by exact_mod_cast hdH.le
      linarith
    have he : ∀ n ∈ range (N - d), phase
        ((fun n : ℕ => mixedPhase i j k n) (2 * r₀ + 1 + 2 * (n + d)) -
          (fun n : ℕ => mixedPhase i j k n) (2 * r₀ + 1 + 2 * n)) =
        phase (smallShiftPhase i j k d ((2 * r₀ + 1 + 2 * n : ℕ) : ℝ)) := by
      intro n _
      rw [smallShiftPhase_eq_sub]
      congr 3
      push_cast
      ring_nf
    rw [sum_congr rfl he]
    have hb' : 1 ≤ N - d →
        ((2 * r₀ + 1 : ℕ) : ℝ) + 2 * ((N - d - 1 : ℕ) : ℝ) ≤ 2 * P - 2 * d := by
      intro _
      have h1 := hb (by omega)
      have e : ((N - d - 1 : ℕ) : ℝ) + d = ((N - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : N - d - 1 + d = N - 1)
      linarith
    have hbnd := hK P hP d hd.1 (by rw [← hT2]; exact hdr) i j k hj0 hi hj hk r₀ (N - d) ha hb'
    rw [← hT21] at hbnd
    have hsd : √(d : ℝ) ≤ T := by
      rw [sqrt_le_left (by linarith)]
      exact hdr
    have hKT21 : 0 ≤ K * T ^ 21 := by positivity
    calc _ ≤ K * T ^ 21 * (1 + √(d : ℝ)) := hbnd
      _ ≤ K * T ^ 21 * (2 * T) := by gcongr; linarith
  have hcsum : ∑ d ∈ Ico 1 H, ‖∑ n ∈ range (N - d), phase
      ((fun n : ℕ => mixedPhase i j k n) (2 * r₀ + 1 + 2 * (n + d)) -
        (fun n : ℕ => mixedPhase i j k n) (2 * r₀ + 1 + 2 * n))‖ ≤
      H * (K * T ^ 21 * (2 * T)) := by
    refine (sum_le_sum hsum).trans ?_
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : ((H - 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le H 1
    have : 0 ≤ K * T ^ 21 * (2 * T) := by positivity
    nlinarith
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- the two terms of van der Corput
  have t1 : 2 * (N : ℝ) ^ 2 / H ≤ 36 * T ^ 46 := by
    rw [div_le_iff₀ hHpos]
    have hNsq : (N : ℝ) ^ 2 ≤ (3 * T ^ 24) ^ 2 := pow_le_pow_left₀ hN0 hN3 2
    have : 36 * T ^ 46 * (T ^ 2 / 2) ≤ 36 * T ^ 46 * H := by gcongr
    have e : 36 * T ^ 46 * (T ^ 2 / 2) = 2 * (3 * T ^ 24) ^ 2 := by ring
    linarith
  have t2 : (4 * N / H) * (H * (K * T ^ 21 * (2 * T))) ≤ 24 * K * T ^ 46 := by
    have e : (4 * N / H) * (H * (K * T ^ 21 * (2 * T))) = 8 * K * N * T ^ 22 := by
      field_simp
      ring
    rw [e]
    have : 8 * K * N * T ^ 22 ≤ 8 * K * (3 * T ^ 24) * T ^ 22 := by gcongr
    linarith [show 8 * K * (3 * T ^ 24) * T ^ 22 = 24 * K * T ^ 46 by ring]
  have hcoef : 0 ≤ 4 * (N : ℝ) / H := by positivity
  have hsq : ‖∑ m ∈ range N, phase (mixedPhase i j k ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ))‖ ^ 2 ≤
      (36 + 24 * K) * T ^ 46 := by
    have := mul_le_mul_of_nonneg_left hcsum hcoef
    have h := hvdc
    nlinarith
  have hB : (√(36 + 24 * K) * T ^ 23) ^ 2 = (36 + 24 * K) * T ^ 46 := by
    rw [mul_pow, sq_sqrt (by positivity)]
    ring
  have hB0 : 0 ≤ √(36 + 24 * K) * T ^ 23 := by positivity
  have hle : ‖∑ m ∈ range N, phase (mixedPhase i j k ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ))‖ ≤
      √(36 + 24 * K) * T ^ 23 := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg (∑ m ∈ range N,
      phase (mixedPhase i j k ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ)))]
  have : 0 ≤ T ^ 23 := by positivity
  linarith

/-! ## `j = 0 ≠ i`: curvature `|i| P^{-1/2}` -/

/-- **Theorem 4.5 for `j = 0 ≠ i`, on an odd window.** -/
theorem smooth_window_sum (C : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ P : ℝ, 1 ≤ P → ∀ i k : ℤ, i ≠ 0 →
    |(i : ℝ)| ≤ C * P ^ (1 / 24 : ℝ) → |(k : ℝ)| ≤ C * P ^ (1 / 24 : ℝ) →
    ∀ r₀ N : ℕ, P < ((2 * r₀ + 1 : ℕ) : ℝ) →
    (1 ≤ N → ((2 * r₀ + 1 : ℕ) : ℝ) + 2 * ((N - 1 : ℕ) : ℝ) ≤ 2 * P) →
    ‖∑ m ∈ range N, phase (mixedPhase i 0 k ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ))‖ ≤
      K * P ^ (23 / 24 : ℝ) := by
  set C' := max C 1 with hC'
  have hC1 : 1 ≤ C' := le_max_right _ _
  have hCC : C ≤ C' := le_max_left _ _
  refine ⟨48 * C' + 81, by positivity, ?_⟩
  intro P hP i k hi0 hi hk r₀ N ha hb
  have hP0 : 0 ≤ P := by linarith
  set T := P ^ (1 / 24 : ℝ) with hTdef
  have hT24 : T ^ 24 = P := by rw [rpow_24_pow hP0 24 1 (by norm_num), rpow_one]
  have hT23 : T ^ 23 = P ^ (23 / 24 : ℝ) := rpow_24_pow hP0 23 _ (by norm_num)
  have hT6 : T ^ 6 = P ^ (1 / 4 : ℝ) := rpow_24_pow hP0 6 _ (by norm_num)
  have hT9 : T ^ 9 = P ^ (3 / 8 : ℝ) := rpow_24_pow hP0 9 _ (by norm_num)
  have hT1 : 1 ≤ T := one_le_rpow hP (by norm_num)
  have hT23' : 0 ≤ T ^ 23 := by positivity
  rw [← hT23]
  have hCT : C * T ≤ C' * T := mul_le_mul_of_nonneg_right hCC (by linarith)
  by_cases hsmall : T < 16 * C'
  · have hN3 := window_card_le r₀ N hP ha hb
    refine (norm_window_le _ N).trans ?_
    have : T ^ 24 ≤ 16 * C' * T ^ 23 := by
      have e : T ^ 24 = T * T ^ 23 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hsmall.le hT23'
    have : 0 ≤ C' * T ^ 23 := by positivity
    nlinarith
  push Not at hsmall
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [range_zero, sum_empty, norm_zero]
    positivity
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hb' := hb (by omega)
  simp only [Nat.add_sub_cancel] at hb'
  refine (norm_window_succ _ M).trans ?_
  set a : ℝ := ((2 * r₀ + 1 : ℕ) : ℝ) with hadef
  have hM : (M : ℝ) ≤ P ^ (9 / 16 : ℝ) * P ^ (7 / 16 : ℝ) := by
    rw [← rpow_add (by linarith)]
    norm_num
    linarith
  -- the positive case, for `v = |i|`
  have hpos : ∀ v w : ℤ, 1 ≤ v → (v : ℝ) ≤ C' * T → |(w : ℝ)| ≤ C' * T →
      ‖∑ m ∈ range M, phase (mixedPhase v 0 w ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ))‖ ≤
        80 * T ^ 23 := by
    intro v w hv hvC hwC
    have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
    have he : ∀ m ∈ range M, phase (mixedPhase v 0 w ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ)) =
        phase (OOEEPhaseComparison.originalPhase 0 v w (a + 2 * m)) := by
      intro m _
      rw [mixedPhase_zero, hadef]
      congr 2
      push_cast
      ring
    rw [sum_congr rfl he]
    have hvP : (v : ℝ) ≤ P ^ (1 / 4 : ℝ) := by
      rw [← hT6]
      have : T ≤ T ^ 5 := by
        calc T = T ^ 1 := (pow_one T).symm
          _ ≤ T ^ 5 := pow_le_pow_right₀ hT1 (by norm_num)
      have : C' * T ≤ T ^ 6 := by
        calc C' * T ≤ T * T := by gcongr; linarith
          _ ≤ T ^ 5 * T := by gcongr
          _ = T ^ 6 := by ring
      linarith
    have hwP : |(w : ℝ)| ≤ v * P ^ (3 / 8 : ℝ) / 16 := by
      rw [← hT9]
      have h8 : T ≤ T ^ 8 := by
        calc T = T ^ 1 := (pow_one T).symm
          _ ≤ T ^ 8 := pow_le_pow_right₀ hT1 (by norm_num)
      have : 16 * (C' * T) ≤ T ^ 9 := by
        calc 16 * (C' * T) = (16 * C') * T := by ring
          _ ≤ T * T := by gcongr
          _ ≤ T ^ 8 * T := by gcongr
          _ = T ^ 9 := by ring
      have : T ^ 9 ≤ v * T ^ 9 := by
        have : 0 ≤ T ^ 9 := by positivity
        nlinarith
      linarith
    have hs := OOEESmoothModes.smooth_sum_positive (a := a) M hP ha.le (by linarith) hv1 hvP hwP
      (by positivity) hM
    have hexp : (64 * P ^ (9 / 16 : ℝ) + 16) * P ^ (5 / 16 : ℝ) ≤ 80 * P ^ (23 / 24 : ℝ) := by
      have e : P ^ (9 / 16 : ℝ) * P ^ (5 / 16 : ℝ) = P ^ (7 / 8 : ℝ) := by
        rw [← rpow_add (by linarith)]
        norm_num
      have h1 : P ^ (7 / 8 : ℝ) ≤ P ^ (23 / 24 : ℝ) := rpow_le_rpow_of_exponent_le hP (by norm_num)
      have h2 : P ^ (5 / 16 : ℝ) ≤ P ^ (23 / 24 : ℝ) := rpow_le_rpow_of_exponent_le hP (by norm_num)
      nlinarith
    rw [hT23]
    linarith
  have hfin : 80 * T ^ 23 + 1 ≤ (48 * C' + 81) * T ^ 23 := by
    have : 1 ≤ T ^ 23 := one_le_pow₀ hT1
    have : 0 ≤ C' * T ^ 23 := by positivity
    nlinarith
  rcases lt_or_gt_of_ne hi0 with hin | hip
  · have he : ∀ m ∈ range M, phase (mixedPhase i 0 k ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ)) =
        phase (-mixedPhase (-i) 0 (-k) ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ)) := by
      intro m _
      rw [← mixedPhase_neg, neg_neg, neg_neg, neg_zero]
    rw [sum_congr rfl he, norm_range_phase_neg]
    have h := hpos (-i) (-k) (by omega)
      (by push_cast; rw [abs_le] at hi; linarith)
      (by push_cast; rw [abs_neg]; linarith)
    linarith
  · have h := hpos i k (by omega)
      (by have := le_abs_self (i : ℝ); linarith) (by linarith)
    linarith

/-! ## `i = j = 0 ≠ k`: curvature `|k| P^{-7/8}` -/

/-- The second-derivative test for `(w/2) x^{9/8}` on odd samples in `[P, 2P]`, `w ≥ 1`. -/
theorem slow_sum_positive {P a w : ℝ} (N : ℕ) (hP : 1 ≤ P) (ha : P ≤ a)
    (hb : a + 2 * N ≤ 2 * P) (hw : 1 ≤ w) :
    ‖∑ n ∈ range N, phase ((w / 2) * (a + 2 * n) ^ (9 / 8 : ℝ))‖ ≤
      16 * N * √((9 / 256) * w * P ^ (-7 / 8 : ℝ)) +
        4 / √((9 / 256) * w * P ^ (-7 / 8 : ℝ)) := by
  have hP0 : 0 < P := by linarith
  let f : ℝ → ℝ := fun x => (w / 2) * x ^ (9 / 8 : ℝ)
  let g : ℝ → ℝ := fun x => (9 / 16) * w * x ^ (1 / 8 : ℝ)
  let q : ℝ → ℝ := fun x => (9 / 128) * w * x ^ (-7 / 8 : ℝ)
  have hx0 (x : ℝ) (hx : x ∈ Set.Icc a (a + 2 * N)) : 0 < x := by linarith [hx.1]
  have hf (x : ℝ) (hx : x ∈ Set.Icc a (a + 2 * N)) : HasDerivAt f (g x) x := by
    have hd := (OOEECurvature.deriv_power (hx0 x hx) (9 / 8)).const_mul (w / 2)
    apply hd.congr_deriv
    norm_num [g]
    ring
  have hg (x : ℝ) (hx : x ∈ Set.Icc a (a + 2 * N)) : HasDerivAt g (q x) x := by
    have hd := (OOEECurvature.deriv_power (hx0 x hx) (1 / 8)).const_mul ((9 / 16) * w)
    apply hd.congr_deriv
    norm_num [q]
    ring
  have htwo : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-7 / 8 : ℝ) := by
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (-1 : ℝ) ≤ -7 / 8)
    rw [rpow_neg_one] at h
    linarith
  have hcurv (x : ℝ) (hx : x ∈ Set.Icc a (a + 2 * N)) :
      (9 / 256) * w * P ^ (-7 / 8 : ℝ) ≤ q x ∧ q x ≤ 2 * ((9 / 256) * w * P ^ (-7 / 8 : ℝ)) := by
    have hPx : P ≤ x := by linarith [hx.1]
    have hx2 : x ≤ 2 * P := by linarith [hx.2]
    have hup := rpow_le_rpow_of_nonpos hP0 hPx (by norm_num : (-7 / 8 : ℝ) ≤ 0)
    have hlo := rpow_le_rpow_of_nonpos (hx0 x hx) hx2 (by norm_num : (-7 / 8 : ℝ) ≤ 0)
    rw [mul_rpow (by norm_num) hP0.le] at hlo
    have hPp : 0 ≤ P ^ (-7 / 8 : ℝ) := by positivity
    have hlo' : P ^ (-7 / 8 : ℝ) / 2 ≤ x ^ (-7 / 8 : ℝ) := by nlinarith
    have hw0 : 0 ≤ w := by linarith
    dsimp [q]
    constructor
    · have := mul_le_mul_of_nonneg_left hlo' (show 0 ≤ (9 / 128) * w by positivity)
      linarith
    · have := mul_le_mul_of_nonneg_left hup (show 0 ≤ (9 / 128) * w by positivity)
      linarith
  have hs := odd_lattice_second_derivative_sum_bound f g q a N
    (lam := (9 / 256) * w * P ^ (-7 / 8 : ℝ)) (C := 2) (by positivity) (by norm_num)
    hf hg (Or.inl hcurv)
  have e : 8 * 2 * (N : ℝ) = 16 * N := by ring
  simpa only [f, e] using hs

/-- **Theorem 4.5 for `i = j = 0 ≠ k`, on an odd window.** -/
theorem slow_window_sum (C : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ P : ℝ, 1 ≤ P → ∀ k : ℤ, k ≠ 0 →
    |(k : ℝ)| ≤ C * P ^ (1 / 24 : ℝ) →
    ∀ r₀ N : ℕ, P < ((2 * r₀ + 1 : ℕ) : ℝ) →
    (1 ≤ N → ((2 * r₀ + 1 : ℕ) : ℝ) + 2 * ((N - 1 : ℕ) : ℝ) ≤ 2 * P) →
    ‖∑ m ∈ range N, phase (mixedPhase 0 0 k ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ))‖ ≤
      K * P ^ (23 / 24 : ℝ) := by
  set C' := max C 1 with hC'
  have hC1 : 1 ≤ C' := le_max_right _ _
  have hCC : C ≤ C' := le_max_left _ _
  refine ⟨16 * C' + 23, by positivity, ?_⟩
  intro P hP k hk0 hk r₀ N ha hb
  have hP0 : 0 ≤ P := by linarith
  set T := P ^ (1 / 24 : ℝ) with hTdef
  have hT24 : T ^ 24 = P := by rw [rpow_24_pow hP0 24 1 (by norm_num), rpow_one]
  have hT23 : T ^ 23 = P ^ (23 / 24 : ℝ) := rpow_24_pow hP0 23 _ (by norm_num)
  have hT1 : 1 ≤ T := one_le_rpow hP (by norm_num)
  have hT0 : 0 < T := by linarith
  rw [← hT23]
  have hCT : C * T ≤ C' * T := mul_le_mul_of_nonneg_right hCC (by linarith)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [range_zero, sum_empty, norm_zero]
    positivity
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hb' := hb (by omega)
  simp only [Nat.add_sub_cancel] at hb'
  refine (norm_window_succ _ M).trans ?_
  set a : ℝ := ((2 * r₀ + 1 : ℕ) : ℝ) with hadef
  have hM : (M : ℝ) ≤ T ^ 24 := by rw [hT24]; linarith
  have hpos : ∀ w : ℤ, 1 ≤ w → (w : ℝ) ≤ C' * T →
      ‖∑ m ∈ range M, phase (mixedPhase 0 0 w ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ))‖ ≤
        16 * C' * T ^ 14 + 22 * T ^ 11 := by
    intro w hw hwC
    have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have he : ∀ m ∈ range M, phase (mixedPhase 0 0 w ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ)) =
        phase (((w : ℝ) / 2) * (a + 2 * m) ^ (9 / 8 : ℝ)) := by
      intro m _
      unfold mixedPhase
      rw [hadef]
      push_cast
      ring_nf
    rw [sum_congr rfl he]
    have hs := slow_sum_positive (a := a) M hP ha.le (by linarith) hw1
    rw [← hT24, pow24_rpow_neg hT0 (m := 21) (by norm_num)] at hs
    set lam := (9 / 256) * (w : ℝ) * (1 / T ^ 21) with hlam
    have hlam_hi : lam ≤ (C' / T ^ 10) ^ 2 := by
      rw [hlam, div_pow, ← pow_mul]
      have h1 : (9 / 256) * (w : ℝ) * (1 / T ^ 21) ≤ C' * T / T ^ 21 := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      have h2 : C' * T / T ^ 21 = C' / T ^ 20 := by field_simp
      have h3 : C' / T ^ 20 ≤ C' ^ 2 / T ^ (10 * 2) := by
        norm_num
        gcongr
        nlinarith
      linarith
    have hlam_lo : ((3 / 16) / T ^ 11) ^ 2 ≤ lam := by
      rw [hlam, div_pow, ← pow_mul]
      have h1 : (9 / 256) * (1 / T ^ 22) ≤ (9 / 256) * (w : ℝ) * (1 / T ^ 21) := by
        have : 1 / T ^ 22 ≤ 1 / T ^ 21 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hT1 (by norm_num))
        have : 0 ≤ 1 / T ^ 21 := by positivity
        nlinarith
      have e : (3 / 16 : ℝ) ^ 2 / T ^ (11 * 2) = (9 / 256) * (1 / T ^ 22) := by
        norm_num
        ring
      linarith
    have hsq_hi : √lam ≤ C' / T ^ 10 := by
      rw [sqrt_le_left (by positivity)]
      exact hlam_hi
    have hsq_lo : (3 / 16) / T ^ 11 ≤ √lam := by
      rw [le_sqrt (by positivity) (by positivity)]
      exact hlam_lo
    have hsq_pos : 0 < √lam := lt_of_lt_of_le (by positivity) hsq_lo
    have t1 : 16 * (M : ℝ) * √lam ≤ 16 * C' * T ^ 14 := by
      calc 16 * (M : ℝ) * √lam ≤ 16 * T ^ 24 * (C' / T ^ 10) := by gcongr
        _ = 16 * C' * T ^ 14 := by field_simp
    have t2 : 4 / √lam ≤ 22 * T ^ 11 := by
      rw [div_le_iff₀ hsq_pos]
      have : 22 * T ^ 11 * ((3 / 16) / T ^ 11) = 66 / 16 := by field_simp; ring
      have : 0 ≤ 22 * T ^ 11 := by positivity
      nlinarith
    linarith
  have hfin : 16 * C' * T ^ 14 + 22 * T ^ 11 + 1 ≤ (16 * C' + 23) * T ^ 23 := by
    have h14 : T ^ 14 ≤ T ^ 23 := pow_le_pow_right₀ hT1 (by norm_num)
    have h11 : T ^ 11 ≤ T ^ 23 := pow_le_pow_right₀ hT1 (by norm_num)
    have : 1 ≤ T ^ 23 := one_le_pow₀ hT1
    have : 16 * C' * T ^ 14 ≤ 16 * C' * T ^ 23 := by gcongr
    nlinarith
  rcases lt_or_gt_of_ne hk0 with hkn | hkp
  · have he : ∀ m ∈ range M, phase (mixedPhase 0 0 k ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ)) =
        phase (-mixedPhase 0 0 (-k) ((2 * r₀ + 1 + 2 * m : ℕ) : ℝ)) := by
      intro m _
      rw [← mixedPhase_neg]; simp only [neg_neg, neg_zero]
    rw [sum_congr rfl he, norm_range_phase_neg]
    have h := hpos (-k) (by omega) (by push_cast; rw [abs_le] at hk; linarith)
    linarith
  · have h := hpos k (by omega) (by have := le_abs_self (k : ℝ); linarith)
    linarith

/-! ## The theorem -/

/-- **Paper B, Theorem 4.5.** For every `C` there is `K` such that for `P ≥ 1` and every
nonzero integer triple `(i, j, k)` with `|i|, |j|, |k| ≤ C P^{1/24}`, the sum of
`e((i/2) n^{3/2} + (j/2) m(n)^{3/2} + (k/2) n^{9/8})`, `m(n) = ⌊n^{3/2}⌋`, over the odd
`n ∈ (P, 2P]` has modulus at most `K P^{23/24}`. -/
theorem mixed_sum (C : ℝ) : ∃ K : ℝ, ∀ P : ℝ, 1 ≤ P → ∀ i j k : ℤ,
    (i, j, k) ≠ (0, 0, 0) →
    |(i : ℝ)| ≤ C * P ^ (1 / 24 : ℝ) → |(j : ℝ)| ≤ C * P ^ (1 / 24 : ℝ) →
    |(k : ℝ)| ≤ C * P ^ (1 / 24 : ℝ) →
    ‖∑ n ∈ (range (⌊2 * P⌋₊ + 1)).filter
        (fun n : ℕ => P < (n : ℝ) ∧ (n : ℝ) ≤ 2 * P ∧ Odd n),
        phase (mixedPhase i j k n)‖ ≤ K * P ^ (23 / 24 : ℝ) := by
  obtain ⟨K₁, hK₁, h₁⟩ := differenced_window_sum C
  obtain ⟨K₂, hK₂, h₂⟩ := smooth_window_sum C
  obtain ⟨K₃, hK₃, h₃⟩ := slow_window_sum C
  refine ⟨K₁ + K₂ + K₃, ?_⟩
  intro P hP i j k hne hi hj hk
  obtain ⟨r₀, N, ha, hb, hsum⟩ := odd_window_sum hP (L := 2 * P) le_rfl
    (fun n => phase (mixedPhase i j k n))
  rw [hsum]
  have hPp : 0 ≤ P ^ (23 / 24 : ℝ) := by positivity
  by_cases hj0 : j = 0
  · subst hj0
    by_cases hi0 : i = 0
    · subst hi0
      have hk0 : k ≠ 0 := by rintro rfl; exact hne rfl
      have := h₃ P hP k hk0 hk r₀ N ha hb
      nlinarith
    · have := h₂ P hP i k hi0 hi hk r₀ N ha hb
      nlinarith
  · have := h₁ P hP i j k hj0 hi hj hk r₀ N ha hb
    nlinarith

end PaperBMixedSums

end Problems.Juggler
