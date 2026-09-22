import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Dist

/-!
# Finite Weyl differencing with actual overlap correlations
-/

noncomputable section

namespace BTCalculus.WeylDifferencing

open Finset
open scoped ComplexConjugate

def pad (z : ℕ → ℂ) (N h n : ℕ) : ℂ :=
  if n ∈ Ico h (h + N) then z (n - h) else 0

def correlation (z : ℕ → ℂ) (N d : ℕ) : ℂ :=
  ∑ n ∈ range (N - d), z (n + d) * conj (z n)

theorem sum_pad (z : ℕ → ℂ) (N H h : ℕ) (hh : h < H) :
    ∑ n ∈ range (N + H), pad z N h n = ∑ n ∈ range N, z n := by
  unfold pad
  rw [← sum_filter]
  have hs : {n ∈ range (N + H) | n ∈ Ico h (h + N)} = Ico h (h + N) := by
    ext n
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hs]
  refine sum_bij (fun n _ => n - h) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_Ico] at hn
    simp only [mem_range]
    omega
  · intro a ha b hb hab
    simp only [mem_Ico] at ha hb
    omega
  · intro n hn
    simp only [mem_range] at hn
    refine ⟨n + h, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intros
    rfl

theorem sum_norm_sq_le (s : Finset ℕ) (v : ℕ → ℂ) :
    ‖∑ n ∈ s, v n‖ ^ 2 ≤ (s.card : ℝ) * ∑ n ∈ s, ‖v n‖ ^ 2 := by
  have hn := norm_sum_le s v
  have hp := sq_sum_le_card_mul_sum_sq (s := s) (f := fun n => ‖v n‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hp

theorem pad_overlap (z : ℕ → ℂ) (N H h k : ℕ) (_hh : h < H) (hk : k < H)
    (hle : h ≤ k) :
    ∑ n ∈ range (N + H), pad z N h n * conj (pad z N k n) =
      correlation z N (k - h) := by
  have hp (n : ℕ) : pad z N h n * conj (pad z N k n) =
      if n ∈ Ico k (h + N) then z (n - h) * conj (z (n - k)) else 0 := by
    have hiff : n ∈ Ico k (h + N) ↔
        n ∈ Ico h (h + N) ∧ n ∈ Ico k (k + N) := by
      simp only [mem_Ico]
      omega
    by_cases h1 : n ∈ Ico h (h + N) <;> by_cases h2 : n ∈ Ico k (k + N) <;>
      simp [pad, h1, h2, hiff]
  simp_rw [hp]
  rw [← sum_filter]
  have hs : {n ∈ range (N + H) | n ∈ Ico k (h + N)} = Ico k (h + N) := by
    ext n
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hs]
  unfold correlation
  refine sum_bij (fun n _ => n - k) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_Ico] at hn
    simp only [mem_range]
    omega
  · intro a ha b hb hab
    simp only [mem_Ico] at ha hb
    omega
  · intro n hn
    simp only [mem_range] at hn
    refine ⟨n + k, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro n hn
    have he : n - h = (n - k) + (k - h) := by
      have := (mem_Ico.mp hn).1
      omega
    rw [he]

theorem sq_norm_sum (s : Finset ℕ) (v : ℕ → ℂ) :
    ‖∑ h ∈ s, v h‖ ^ 2 = ∑ h ∈ s, ∑ k ∈ s, (v h * conj (v k)).re := by
  have hs (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
    simpa only [Complex.mul_conj, Complex.ofReal_re] using (Complex.normSq_eq_norm_sq z).symm
  rw [hs]
  simp [sum_mul, mul_sum, map_sum, mul_comm]

theorem overlap_real_symmetric (z : ℕ → ℂ) (N H h k : ℕ) :
    (∑ n ∈ range (N + H), pad z N h n * conj (pad z N k n)).re =
      (∑ n ∈ range (N + H), pad z N k n * conj (pad z N h n)).re := by
  simp [Complex.mul_re, mul_comm]

theorem correlation_zero_norm_le {z : ℕ → ℂ} {N : ℕ}
    (hz : ∀ n, n < N → ‖z n‖ ≤ 1) : ‖correlation z N 0‖ ≤ N := by
  simp only [correlation, Nat.sub_zero, Nat.add_zero]
  calc ‖∑ n ∈ range N, z n * conj (z n)‖
      ≤ ∑ n ∈ range N, ‖z n * conj (z n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range N, (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_conj]
      have h := hz n (mem_range.mp hn)
      nlinarith [norm_nonneg (z n)]
    _ = N := by simp

theorem overlap_real_le {z : ℕ → ℂ} {N H h k : ℕ}
    (hz : ∀ n, n < N → ‖z n‖ ≤ 1) (hh : h < H) (hk : k < H) :
    (∑ n ∈ range (N + H), pad z N h n * conj (pad z N k n)).re ≤
      if h = k then (N : ℝ) else ‖correlation z N (Nat.dist h k)‖ := by
  by_cases he : h = k
  · subst k
    rw [pad_overlap z N H h h hh hh le_rfl]
    simpa using (Complex.re_le_norm (correlation z N 0)).trans (correlation_zero_norm_le hz)
  · simp only [he, ite_false]
    rcases le_total h k with hle | hle
    · rw [pad_overlap z N H h k hh hk hle, Nat.dist_eq_sub_of_le hle]
      exact Complex.re_le_norm _
    · rw [overlap_real_symmetric, pad_overlap z N H k h hk hh hle,
        Nat.dist_eq_sub_of_le_right hle]
      exact Complex.re_le_norm _

theorem sum_injection_le (s t : Finset ℕ) (f : ℕ → ℕ) (g : ℕ → ℝ)
    (hinj : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b)
    (hmap : ∀ a ∈ s, f a ∈ t) (hg : ∀ b ∈ t, 0 ≤ g b) :
    ∑ a ∈ s, g (f a) ≤ ∑ b ∈ t, g b := by
  rw [← sum_image hinj]
  apply sum_le_sum_of_subset_of_nonneg _ (fun b hb _ => hg b hb)
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
  exact hmap a ha

theorem row_distance_bound (g : ℕ → ℝ) (H k : ℕ) (hk : k < H)
    (hg : ∀ d, 0 ≤ g d) (B : ℝ) :
    ∑ h ∈ range H, (if h = k then B else g (Nat.dist h k)) ≤
      B + 2 * ∑ d ∈ Ico 1 H, g d := by
  have hl : ∑ h ∈ {h ∈ range H | h < k}, g (k - h) ≤ ∑ d ∈ Ico 1 H, g d := by
    apply sum_injection_le _ _ (fun h => k - h) g
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb
      omega
    · intro h hh
      simp only [mem_filter, mem_range] at hh
      simp only [mem_Ico]
      omega
    · exact fun d _ => hg d
  have hr : ∑ h ∈ {h ∈ range H | k < h}, g (h - k) ≤ ∑ d ∈ Ico 1 H, g d := by
    apply sum_injection_le _ _ (fun h => h - k) g
    · intro a ha b hb hab
      simp only [mem_filter, mem_range] at ha hb
      omega
    · intro h hh
      simp only [mem_filter, mem_range] at hh
      simp only [mem_Ico]
      omega
    · exact fun d _ => hg d
  have hid : (∑ h ∈ range H, if h = k then B else g (Nat.dist h k)) =
      (∑ h ∈ range H, if h = k then B else 0) +
      (∑ h ∈ {h ∈ range H | h < k}, g (k - h)) +
      ∑ h ∈ {h ∈ range H | k < h}, g (h - k) := by
    rw [sum_filter, sum_filter, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro h _
    rcases lt_trichotomy h k with hlt | he | hgt
    · simp [hlt, ne_of_lt hlt, not_lt_of_ge hlt.le, Nat.dist_eq_sub_of_le hlt.le]
    · subst h
      simp
    · simp [hgt, ne_of_gt hgt, not_lt_of_ge hgt.le, Nat.dist_eq_sub_of_le_right hgt.le]
  rw [hid]
  have hd : (∑ h ∈ range H, if h = k then B else 0) = B := by simp [hk]
  rw [hd]
  linarith

theorem column_energy_bound {z : ℕ → ℂ} {N H : ℕ}
    (hz : ∀ n, n < N → ‖z n‖ ≤ 1) :
    ∑ n ∈ range (N + H), ‖∑ h ∈ range H, pad z N h n‖ ^ 2 ≤
      H * (N + 2 * ∑ d ∈ Ico 1 H, ‖correlation z N d‖) := by
  simp_rw [sq_norm_sum]
  rw [sum_comm]
  simp_rw [sum_comm (s := range (N + H)) (t := range H)]
  have he : (∑ h ∈ range H, ∑ k ∈ range H, ∑ n ∈ range (N + H),
      (pad z N h n * conj (pad z N k n)).re) ≤
      ∑ h ∈ range H, ∑ k ∈ range H,
        if h = k then (N : ℝ) else ‖correlation z N (Nat.dist h k)‖ := by
    apply sum_le_sum
    intro h hh
    apply sum_le_sum
    intro k hk
    simpa using overlap_real_le hz (mem_range.mp hh) (mem_range.mp hk)
  apply he.trans
  rw [sum_comm]
  calc (∑ k ∈ range H, ∑ h ∈ range H,
      if h = k then (N : ℝ) else ‖correlation z N (Nat.dist h k)‖)
      ≤ ∑ _k ∈ range H, ((N : ℝ) + 2 * ∑ d ∈ Ico 1 H, ‖correlation z N d‖) := by
        apply sum_le_sum
        intro k hk
        exact row_distance_bound (fun d => ‖correlation z N d‖) H k (mem_range.mp hk)
          (fun d => norm_nonneg _) N
    _ = _ := by simp; ring

theorem differencing_energy {z : ℕ → ℂ} {N H : ℕ}
    (hz : ∀ n, n < N → ‖z n‖ ≤ 1) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ range N, z n‖ ^ 2 ≤
      (N + H) * H * (N + 2 * ∑ d ∈ Ico 1 H, ‖correlation z N d‖) := by
  have havg : (∑ n ∈ range (N + H), ∑ h ∈ range H, pad z N h n) =
      (H : ℂ) * ∑ n ∈ range N, z n := by
    rw [sum_comm]
    calc (∑ h ∈ range H, ∑ n ∈ range (N + H), pad z N h n)
        = ∑ _h ∈ range H, ∑ n ∈ range N, z n := by
          apply sum_congr rfl
          intro h hh
          exact sum_pad z N H h (mem_range.mp hh)
      _ = _ := by simp
  have hs := sum_norm_sq_le (range (N + H)) (fun n => ∑ h ∈ range H, pad z N h n)
  rw [havg, norm_mul, Complex.norm_natCast, mul_pow] at hs
  simp only [card_range, Nat.cast_add] at hs
  have he := mul_le_mul_of_nonneg_left (column_energy_bound (H := H) hz)
    (show (0 : ℝ) ≤ N + H by positivity)
  exact hs.trans (by simpa only [mul_assoc] using he)

/-- Finite van der Corput, with the overlap and both endpoint constants explicit. -/
theorem van_der_corput {z : ℕ → ℂ} {N H : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (hz : ∀ n, n < N → ‖z n‖ ≤ 1) :
    ‖∑ n ∈ range N, z n‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / H + (4 * N / H) * ∑ d ∈ Ico 1 H, ‖correlation z N d‖ := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hHN' : (H : ℝ) ≤ N := by exact_mod_cast hHN
  let C := ∑ d ∈ Ico 1 H, ‖correlation z N d‖
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => norm_nonneg _)
  have he := differencing_energy (H := H) hz
  have hu : ((N : ℝ) + H) * H * (N + 2 * C) ≤
      (2 * N) * H * (N + 2 * C) := by gcongr; linarith
  have hm : (H : ℝ) * (H * ‖∑ n ∈ range N, z n‖ ^ 2) ≤
      H * (2 * N * (N + 2 * C)) := by
    calc (H : ℝ) * (H * ‖∑ n ∈ range N, z n‖ ^ 2)
        = H ^ 2 * ‖∑ n ∈ range N, z n‖ ^ 2 := by ring
      _ ≤ (2 * N) * H * (N + 2 * C) := he.trans hu
      _ = _ := by ring
  have hc := (mul_le_mul_iff_right₀ hHp).mp hm
  calc ‖∑ n ∈ range N, z n‖ ^ 2 ≤ (2 * N * (N + 2 * C)) / H :=
      (le_div_iff₀ hHp).mpr (by nlinarith [hc])
    _ = _ := by dsimp [C]; ring

def phase (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem phase_mul_conj (a b : ℝ) : phase a * conj (phase b) = phase (a - b) := by
  unfold phase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Odd-lattice coordinates keep the overlap length exactly `N - d`. -/
theorem odd_lattice_van_der_corput (f : ℕ → ℝ) (a : ℕ) {N H : ℕ}
    (hH : 1 ≤ H) (hHN : H ≤ N) :
    ‖∑ n ∈ range N, phase (f (a + 2 * n))‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / H + (4 * N / H) *
        ∑ d ∈ Ico 1 H, ‖∑ n ∈ range (N - d),
          phase (f (a + 2 * (n + d)) - f (a + 2 * n))‖ := by
  simpa only [correlation, phase_mul_conj] using
    van_der_corput (z := fun n => phase (f (a + 2 * n))) hH hHN
      (fun n _ => (phase_norm _).le)

end BTCalculus.WeylDifferencing
