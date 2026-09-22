import Problems.Juggler.CodeMassTransport
import Problems.Juggler.FatePoorProduction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Three actual productions and the exponent 5/8

The two odd-production inequalities are explicit inputs. The weighted
partition, even cutoff, seed, recurrence, rational certificate, and Tao
implication below are kernel-checked. The new analytic OOEE estimate
remains a written result and is not supplied by this module.
-/

noncomputable section

namespace Problems.Juggler.FateOOEEAssembly

open Finset Filter CodeMassTransport
open scoped Classical Topology

def oeGuard (n : ℕ) : Prop := n % 2 = 1 ∧ floorPower n % 2 = 0

def ooeeGuard (n : ℕ) : Prop :=
  n % 2 = 1 ∧ floorPower n % 2 = 1 ∧
    floorPower (floorPower n) % 2 = 0 ∧
    floorPower (floorPower (floorPower n)) % 2 = 0

def sourceMass (A B : ℕ → Prop) (X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X, if A n ∧ B n then weight n else 0

def cutoff (t : ℝ) : ℕ := ⌊Real.exp t⌋₊

def fullMass (A : ℕ → Prop) (t : ℝ) : ℝ := mass A (cutoff t)

/-- The actual source cutoffs are part of the analytic input. -/
def OddProductionBounds (A : ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℝ, ∀ t, T ≤ t →
    (33 / 100) * fullMass A (3 * t / 4 - 4) ≤
      sourceMass A oeGuard (cutoff t) + C ∧
    (11 / 100) * fullMass A (9 * t / 16 - 4) ≤
      sourceMass A ooeeGuard (cutoff t) + C

theorem weight_reciprocal_bounds {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) / n ≤ weight n ∧ weight n ≤ 4 / n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (2 : ℝ) ≤ paired n := by exact_mod_cast paired_ge_two hn
  have hen : (n : ℝ) ≤ paired n := by
    exact_mod_cast (show n ≤ paired n by unfold paired; omega)
  have he2 : (paired n : ℝ) ≤ 2 * n := by
    exact_mod_cast (show paired n ≤ 2 * n by unfold paired; omega)
  have hd : (0 : ℝ) < (paired n : ℝ) - 1 := by linarith
  have hw : weight n = Real.log (1 + 2 / ((paired n : ℝ) - 1)) := by
    rw [weight_log_ratio hn]
    congr 1
    field_simp
    ring
  rw [hw]
  constructor
  · have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 2 / ((paired n : ℝ) - 1) by positivity)
    have hr : (2 : ℝ) * (2 / ((paired n : ℝ) - 1)) /
        (2 / ((paired n : ℝ) - 1) + 2) = 2 / paired n := by
      field_simp
      ring
    rw [hr] at h
    apply le_trans _ h
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < n) (by linarith)).mpr
    nlinarith
  · have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 2 / ((paired n : ℝ) - 1) by positivity)
    have hr : (2 : ℝ) / ((paired n : ℝ) - 1) ≤ 4 / n := by
      apply (div_le_div_iff₀ hd (by positivity : (0 : ℝ) < n)).mpr
      nlinarith
    linarith

theorem mass_bounds (A : ℕ → Prop) (X : ℕ) :
    logMass A X ≤ mass A X ∧ mass A X ≤ 4 * logMass A X := by
  rw [logMass, sum_filter, mass, mul_sum]
  constructor <;> apply sum_le_sum <;> intro n hn
  · by_cases h : A n
    · simpa [h] using (weight_reciprocal_bounds (mem_Icc.mp hn).1).1
    · simp [h]
  · by_cases h : A n
    · simpa [h, div_eq_mul_inv] using (weight_reciprocal_bounds (mem_Icc.mp hn).1).2
    · simp [h]

theorem mass_monotone (A : ℕ → Prop) : Monotone (mass A) := by
  intro X Y h
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h)
  intro n _ _
  split_ifs <;> simp [weight_nonneg]

theorem cutoff_monotone : Monotone cutoff := by
  intro s t h
  exact Nat.floor_mono (Real.exp_le_exp.mpr h)

theorem fullMass_monotone (A : ℕ → Prop) : Monotone (fullMass A) :=
  (mass_monotone A).comp cutoff_monotone

theorem source_partition (A : ℕ → Prop) (X : ℕ) :
    sourceMass A (fun n => n % 2 = 0) X + sourceMass A oeGuard X +
      sourceMass A ooeeGuard X ≤ mass A X := by
  unfold sourceMass mass
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro n _
  have hw := weight_nonneg n
  by_cases hA : A n
  · by_cases hE : n % 2 = 0
    · simp [hA, hE, oeGuard, ooeeGuard]
    · have hO : n % 2 = 1 := by omega
      by_cases hJ : floorPower n % 2 = 0
      · simp [hA, hO, hJ, oeGuard, ooeeGuard]
      · by_cases hg : ooeeGuard n <;> simp [hA, hO, hJ, oeGuard, hg, hw]
  · simp [hA]

theorem even_cutoff_bound {t : ℝ} (ht : 8 ≤ t) :
    cutoff (t / 2 - 4) ≤ Nat.sqrt (cutoff t) - 1 := by
  let N := cutoff (t / 2 - 4)
  have hz : 1 ≤ Real.exp (t / 2 - 4) := Real.one_le_exp_iff.mpr (by linarith)
  have hN : (N : ℝ) ≤ Real.exp (t / 2 - 4) := Nat.floor_le (Real.exp_pos _).le
  have hN2 : ((N + 1 : ℕ) : ℝ) ≤ 2 * Real.exp (t / 2 - 4) := by push_cast; linarith
  have h4 : (4 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hs : ((N + 1 : ℕ) : ℝ) ^ 2 ≤ Real.exp t := calc
    ((N + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * Real.exp (t / 2 - 4)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hN2 2
    _ = 4 * Real.exp (t - 8) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
      ring
    _ ≤ Real.exp 8 * Real.exp (t - 8) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = Real.exp t := by rw [← Real.exp_add]; congr 1; ring
  have hsq : (N + 1) * (N + 1) ≤ cutoff t := by
    apply Nat.le_floor
    push_cast
    simpa only [Nat.cast_add, Nat.cast_one, pow_two] using hs
  have hr := Nat.le_sqrt.mpr hsq
  dsimp [N] at hr
  omega

theorem even_source_lower {A : ℕ → Prop} (hA : BackwardClosed A) {t : ℝ} (ht : 8 ≤ t) :
    fullMass A (t / 2 - 4) ≤ sourceMass A (fun n => n % 2 = 0) (cutoff t) := by
  have hX : 1 ≤ cutoff t := Nat.le_floor (by
    simpa using (Real.one_le_exp_iff.mpr (show 0 ≤ t by linarith)))
  have hsplit := even_pullback_cutoff A hX
  have hb : mass A (Nat.sqrt (cutoff t) - 1) ≤
      ∑ n ∈ evenSources (cutoff t), if A (floorPower n) then weight n else 0 := by
    rw [hsplit]
    have hp := partialMass_nonneg (cutoff t) (Nat.sqrt (cutoff t))
    split_ifs <;> linarith
  apply (mass_monotone A (even_cutoff_bound ht)).trans (hb.trans _)
  unfold evenSources sourceMass
  rw [sum_filter]
  apply sum_le_sum
  intro n _
  by_cases he : n % 2 = 0
  · by_cases hp : A (floorPower n)
    · simp [he, hp, hA n hp]
    · simp only [he, hp, ite_true, ite_false, and_true]
      split_ifs <;> simp [weight_nonneg]
  · simp [he]

theorem production_recurrence {A : ℕ → Prop} (hA : BackwardClosed A)
    (hp : OddProductionBounds A) : ∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℝ, ∀ t, T ≤ t →
    fullMass A (t / 2 - 4) + (33 / 100) * fullMass A (3 * t / 4 - 4) +
      (11 / 100) * fullMass A (9 * t / 16 - 4) - 2 * C ≤ fullMass A t := by
  obtain ⟨C, hC, T, hp⟩ := hp
  refine ⟨C, hC, max T 8, ?_⟩
  intro t ht
  obtain ⟨h1, h2⟩ := hp t ((le_max_left _ _).trans ht)
  have h0 := even_source_lower hA ((le_max_right _ _).trans ht)
  have hsum := source_partition A (cutoff t)
  change _ ≤ mass A (cutoff t)
  linarith

def rate : Fin 3 → ℝ | 0 => 1 / 2 | 1 => 3 / 4 | 2 => 9 / 16
def coeff : Fin 3 → ℝ | 0 => 1 | 1 => 33 / 100 | 2 => 11 / 100

theorem rate_bounds (i : Fin 3) : 1 / 2 ≤ rate i ∧ rate i ≤ 3 / 4 := by
  fin_cases i <;> norm_num [rate]

theorem coeff_nonneg (i : Fin 3) : 0 ≤ coeff i := by
  fin_cases i <;> norm_num [coeff]

theorem certificate_five_eighths : 0 < ∑ i, coeff i * rate i ^ ((5 : ℝ) / 8) - 1 := by
  have h0 : (648 / 1000 : ℝ) ≤ (1 / 2 : ℝ) ^ ((5 : ℝ) / 8) :=
    le_rpow_div_of_pow_le (p := 5) (q := 8) (by norm_num) (by norm_num) (by norm_num)
  have h1 : (835 / 1000 : ℝ) ≤ (3 / 4 : ℝ) ^ ((5 : ℝ) / 8) :=
    le_rpow_div_of_pow_le (p := 5) (q := 8) (by norm_num) (by norm_num) (by norm_num)
  have h2 : (697 / 1000 : ℝ) ≤ (9 / 16 : ℝ) ^ ((5 : ℝ) / 8) :=
    le_rpow_div_of_pow_le (p := 5) (q := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [Fin.sum_univ_three, rate, coeff]
  linarith

theorem mass_exists_ge {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (B : ℝ) : ∃ N : ℕ, B ≤ mass A N := by
  obtain ⟨K, hK, N₀, hlow⟩ := Production.logMass_contagion_averaged hA ha hAa
    (lam := 1 / 4) (by norm_num) (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlog
  have hlim := hp.const_mul_atTop hK
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop B)
  refine ⟨max N N₀, ?_⟩
  exact (hN _ (le_max_left _ _)).trans
    ((hlow _ (le_max_right _ _)).trans (mass_bounds A _).1)

theorem fullMass_eventually_ge {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (B : ℝ) :
    ∃ T : ℝ, ∀ t, T ≤ t → B ≤ fullMass A t := by
  obtain ⟨N, hN⟩ := mass_exists_ge hA ha hAa B
  refine ⟨Real.log (N + 1), ?_⟩
  intro t ht
  have he : (N : ℝ) + 1 ≤ Real.exp t := by
    rw [← Real.exp_log (show (0 : ℝ) < N + 1 by positivity)]
    exact Real.exp_le_exp.mpr ht
  have hc : N ≤ cutoff t := Nat.le_floor (by linarith)
  exact hN.trans (mass_monotone A hc)

/-- Translate the argument and subtract a constant to remove both losses. -/
theorem shifted_recurrence {F : ℝ → ℝ} (hF : Monotone F) {C T : ℝ} (hC : 0 ≤ C)
    (hrec : ∀ t, T ≤ t → F (t / 2 - 4) + (33 / 100) * F (3 * t / 4 - 4) +
      (11 / 100) * F (9 * t / 16 - 4) - 2 * C ≤ F t) :
    ∀ t, T + 16 ≤ t →
      ∑ i, coeff i * (F (rate i * t - 16) - 5 * C) ≤ F (t - 16) - 5 * C := by
  intro t ht
  have h := hrec (t - 16) (by linarith)
  have h0 := hF (show t / 2 - 16 ≤ (t - 16) / 2 - 4 by linarith)
  have h1 := hF (show 3 * t / 4 - 16 ≤ 3 * (t - 16) / 4 - 4 by linarith)
  have h2 := hF (show 9 * t / 16 - 16 ≤ 9 * (t - 16) / 16 - 4 by linarith)
  simp only [Fin.sum_univ_three, coeff, rate]
  have he0 : (1 / 2 : ℝ) * t = t / 2 := by ring
  have he1 : (3 / 4 : ℝ) * t = 3 * t / 4 := by ring
  have he2 : (9 / 16 : ℝ) * t = 9 * t / 16 := by ring
  rw [he0, he1, he2]
  linarith

theorem fullMass_growth {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (hp : OddProductionBounds A) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t →
      K * t ^ ((5 : ℝ) / 8) ≤ fullMass A t := by
  obtain ⟨C, hC, T, hrec⟩ := production_recurrence hA hp
  obtain ⟨S, hS⟩ := fullMass_eventually_ge hA ha hAa (5 * C + 1)
  let T₁ := max 1 (max (T + 16) (2 * (S + 16)))
  have hT₁ : 0 < T₁ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hTT : T + 16 ≤ T₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hST : 2 * (S + 16) ≤ T₁ := (le_max_right _ _).trans (le_max_right _ _)
  let g : ℝ → ℝ := fun t => fullMass A (t - 16) - 5 * C
  have hseed : ∀ t, (1 / 2 : ℝ) * T₁ ≤ t → t ≤ T₁ → 1 ≤ g t := by
    intro t ht _
    have hs := hS (t - 16) (by linarith)
    dsimp [g]
    linarith
  have hr := shifted_recurrence (fullMass_monotone A) hC hrec
  have hmain := recursion_lemma rate coeff (fun _ _ => 0) (fun _ => 0) g
    (5 / 8) T₁ 1 (1 / 2) (3 / 4)
    (by norm_num) hT₁ (by norm_num) (by norm_num) (by norm_num)
    (fun i => (rate_bounds i).1) (fun i => (rate_bounds i).2)
    certificate_five_eighths
    (by intros; norm_num)
    (fun _ _ i => coeff_nonneg i)
    (by intros; nlinarith [certificate_five_eighths])
    (by intros; simp only [zero_mul, sum_const_zero]; linarith [certificate_five_eighths])
    hseed (by
      intro t ht
      simpa only [sub_zero, g] using hr t (hTT.trans ht))
  refine ⟨T₁ ^ (-(5 / 8 : ℝ)), by positivity, T₁, hT₁, ?_⟩
  intro t ht
  have hm := hmain t (by linarith)
  have hmono := fullMass_monotone A (show t - 16 ≤ t by linarith)
  dsimp [g] at hm
  simp only [one_mul] at hm
  linarith

/-- Conditional only on the two displayed actual odd-production bounds. -/
theorem logMass_growth {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (hp : OddProductionBounds A) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      K * Real.log x ^ ((5 : ℝ) / 8) ≤ logMass A x := by
  obtain ⟨K, hK, T, hT, h⟩ := fullMass_growth hA ha hAa hp
  refine ⟨K / 4, by positivity, ⌈Real.exp T⌉₊ + 1, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := by omega
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have hExp : Real.exp T ≤ x := by
    have h1 := Nat.le_ceil (Real.exp T)
    have h2 : ((⌈Real.exp T⌉₊ + 1 : ℕ) : ℝ) ≤ x := by exact_mod_cast hx
    push_cast at h2
    linarith
  have hlog : T ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hExp
  have hm := h (Real.log x) hlog
  have hc : cutoff (Real.log x) = x := by simp [cutoff, Real.exp_log hxpos]
  rw [fullMass, hc] at hm
  have hu := (mass_bounds A x).2
  linarith

theorem conjecture_of_tao_rate {e : ℝ} (he : 3 / 8 < e)
    (hp : OddProductionBounds (fun n => ¬ ReachesOne n))
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  apply tao_rate_implies_conjecture (lam := 5 / 8) (by norm_num) (by norm_num)
    (by linarith) _ htao
  rintro ⟨a, ha, hfail⟩
  exact logMass_growth not_reachesOne_backwardClosed ha hfail hp

end Problems.Juggler.FateOOEEAssembly
