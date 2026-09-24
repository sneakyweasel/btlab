import Problems.Juggler.FateOOOEEAssembly

/-!
# Five actual productions and the exponent 37/50

The productions `E`, `OE` and `OOEE` are unconditional (`FateOOEEWeighted`).
This module adds both depth-five words, `OOOEE` and `OOEOE` (rate `27/32` each),
as explicit inputs with coefficient `1/28`. The five-way source partition, the
recurrence with shift `16 + 32b/5` and loss multiplier `8`, the rational
certificate at `37/50`, and the Tao and pressure implications at `13/50` are
kernel-checked. The two productions themselves are the written, AI-audited and
unreviewed Lemmas E1-E8 of `docs/problems/juggler_depth_five_production.md`;
they are not supplied here.
-/

noncomputable section

namespace Problems.Juggler.FateDepthFiveAssembly

open Finset Filter CodeMassTransport FateOOEEAssembly Pressure
open FateOOOEEAssembly (OOOEEGuard)
open scoped Classical Topology

/-- The actual depth-five parity word `OOEOE`: `n`, `J n` odd, `J^2 n` even,
`J^3 n` odd and `J^4 n` even. -/
def OOEOEGuard (n : ℕ) : Prop :=
  n % 2 = 1 ∧ floorPower n % 2 = 1 ∧
    floorPower (floorPower n) % 2 = 0 ∧
    floorPower (floorPower (floorPower n)) % 2 = 1 ∧
    floorPower (floorPower (floorPower (floorPower n))) % 2 = 0

/-- Both written depth-five productions at coefficient `1/28`, with a common
fixed loss `b` and constant `C`. -/
def DepthFiveProductionBounds (A : ℕ → Prop) : Prop :=
  ∃ b C : ℝ, 0 ≤ b ∧ 0 ≤ C ∧ ∃ T : ℝ, ∀ t, T ≤ t →
    (1 / 28) * fullMass A (27 * t / 32 - b) ≤ sourceMass A OOOEEGuard (cutoff t) + C ∧
    (1 / 28) * fullMass A (27 * t / 32 - b) ≤ sourceMass A OOEOEGuard (cutoff t) + C

/-- The even, `OE`, `OOEE`, `OOOEE` and `OOEOE` sources are disjoint, so their
masses add up to at most the full mass. -/
theorem source_partition (A : ℕ → Prop) (X : ℕ) :
    sourceMass A (fun n => n % 2 = 0) X + sourceMass A oeGuard X +
      sourceMass A ooeeGuard X + sourceMass A OOOEEGuard X +
      sourceMass A OOEOEGuard X ≤ mass A X := by
  unfold sourceMass mass
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro n _
  have hw := weight_nonneg n
  by_cases hA : A n
  · by_cases hE : n % 2 = 0
    · simp [hA, hE, oeGuard, ooeeGuard, OOOEEGuard, OOEOEGuard]
    · have hO : n % 2 = 1 := by omega
      by_cases hJ : floorPower n % 2 = 0
      · simp [hA, hO, hJ, oeGuard, ooeeGuard, OOOEEGuard, OOEOEGuard]
      · have hJ1 : floorPower n % 2 = 1 := by omega
        have hoe : ¬ oeGuard n := fun h => by rw [h.2] at hJ1; omega
        by_cases hJ2 : floorPower (floorPower n) % 2 = 0
        · have hq : ¬ OOOEEGuard n := fun h => by rw [h.2.2.1] at hJ2; omega
          by_cases hJ3 : floorPower (floorPower (floorPower n)) % 2 = 0
          · have hr : ¬ OOEOEGuard n := fun h => by rw [h.2.2.2.1] at hJ3; omega
            by_cases hg : ooeeGuard n <;> simp [hA, hO, hoe, hq, hr, hg, hw]
          · have hg : ¬ ooeeGuard n := fun h => hJ3 h.2.2.2
            by_cases hr : OOEOEGuard n <;> simp [hA, hO, hoe, hq, hr, hg, hw]
        · have hg : ¬ ooeeGuard n := fun h => hJ2 h.2.2.1
          have hr : ¬ OOEOEGuard n := fun h => hJ2 h.2.2.1
          by_cases hq : OOOEEGuard n <;> simp [hA, hO, hoe, hq, hr, hg, hw]
  · simp [hA]

/-- The five productions give one functional inequality for `fullMass`, with a
common depth-five loss `b` and a single constant `C`. -/
theorem production_recurrence {A : ℕ → Prop} (hA : BackwardClosed A)
    (hq : DepthFiveProductionBounds A) : ∃ b C : ℝ, 0 ≤ b ∧ 0 ≤ C ∧ ∃ T : ℝ,
      ∀ t, T ≤ t →
      fullMass A (t / 2 - 4) + (33 / 100) * fullMass A (3 * t / 4 - 4) +
        (11 / 100) * fullMass A (9 * t / 16 - 4) +
        (1 / 14) * fullMass A (27 * t / 32 - b) - 4 * C ≤ fullMass A t := by
  obtain ⟨C₁, hC₁, T₁, hp⟩ :=
    FateOEWeighted.oddProductionBounds_of_ooee hA (FateOOEEWeighted.ooee_production hA)
  obtain ⟨b, C₂, hb, hC₂, T₂, hq⟩ := hq
  refine ⟨b, C₁ + C₂, hb, by positivity, max (max T₁ T₂) 8, ?_⟩
  intro t ht
  have hT₁ : T₁ ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have hT₂ : T₂ ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  obtain ⟨h1, h2⟩ := hp t hT₁
  obtain ⟨h3, h4⟩ := hq t hT₂
  have h0 := even_source_lower hA ((le_max_right _ _).trans ht)
  have hsum := source_partition A (cutoff t)
  change _ ≤ mass A (cutoff t)
  linarith

/-- The rates `1/2`, `3/4`, `9/16` and `27/32`; both depth-five words share the last. -/
def rate : Fin 4 → ℝ | 0 => 1 / 2 | 1 => 3 / 4 | 2 => 9 / 16 | 3 => 27 / 32

/-- The coefficients `1`, `33/100`, `11/100` and `1/14 = 2 * (1/28)`. -/
def coeff : Fin 4 → ℝ | 0 => 1 | 1 => 33 / 100 | 2 => 11 / 100 | 3 => 1 / 14

/-- Every rate lies in `[1/2, 27/32]`. -/
theorem rate_bounds (i : Fin 4) : 1 / 2 ≤ rate i ∧ rate i ≤ 27 / 32 := by
  fin_cases i <;> norm_num [rate]

/-- Every coefficient is nonnegative. -/
theorem coeff_nonneg (i : Fin 4) : 0 ≤ coeff i := by
  fin_cases i <;> norm_num [coeff]

/-- The five-production root exceeds `37/50`; Arb encloses it as
`0.740571591021 ± 8e-13`. -/
theorem certificate_37_50 : 0 < ∑ i, coeff i * rate i ^ ((37 : ℝ) / 50) - 1 := by
  have h0 : (59873 / 100000 : ℝ) ≤ (1 / 2 : ℝ) ^ ((37 : ℝ) / 50) :=
    le_rpow_div_of_pow_le (p := 37) (q := 50) (by norm_num) (by norm_num) (by norm_num)
  have h1 : (10103 / 12500 : ℝ) ≤ (3 / 4 : ℝ) ^ ((37 : ℝ) / 50) :=
    le_rpow_div_of_pow_le (p := 37) (q := 50) (by norm_num) (by norm_num) (by norm_num)
  have h2 : (32663 / 50000 : ℝ) ≤ (9 / 16 : ℝ) ^ ((37 : ℝ) / 50) :=
    le_rpow_div_of_pow_le (p := 37) (q := 50) (by norm_num) (by norm_num) (by norm_num)
  have h3 : (17637 / 20000 : ℝ) ≤ (27 / 32 : ℝ) ^ ((37 : ℝ) / 50) :=
    le_rpow_div_of_pow_le (p := 37) (q := 50) (by norm_num) (by norm_num) (by norm_num)
  simp only [Fin.sum_univ_four, rate, coeff]
  linarith

/-- Translate by `16 + 32b/5` and subtract `8C` to remove all five losses. -/
theorem shifted_recurrence {F : ℝ → ℝ} (hF : Monotone F) {b C T : ℝ} (hb : 0 ≤ b)
    (hC : 0 ≤ C)
    (hrec : ∀ t, T ≤ t → F (t / 2 - 4) + (33 / 100) * F (3 * t / 4 - 4) +
      (11 / 100) * F (9 * t / 16 - 4) + (1 / 14) * F (27 * t / 32 - b) - 4 * C ≤ F t) :
    ∀ t, T + (16 + 32 * b / 5) ≤ t →
      ∑ i, coeff i * (F (rate i * t - (16 + 32 * b / 5)) - 8 * C) ≤
        F (t - (16 + 32 * b / 5)) - 8 * C := by
  intro t ht
  set s := 16 + 32 * b / 5 with hs
  have h := hrec (t - s) (by linarith)
  have h0 := hF (show t / 2 - s ≤ (t - s) / 2 - 4 by linarith)
  have h1 := hF (show 3 * t / 4 - s ≤ 3 * (t - s) / 4 - 4 by linarith)
  have h2 := hF (show 9 * t / 16 - s ≤ 9 * (t - s) / 16 - 4 by linarith)
  have h3 := hF (show 27 * t / 32 - s ≤ 27 * (t - s) / 32 - b by linarith)
  simp only [Fin.sum_univ_four, coeff, rate]
  have he0 : (1 / 2 : ℝ) * t = t / 2 := by ring
  have he1 : (3 / 4 : ℝ) * t = 3 * t / 4 := by ring
  have he2 : (9 / 16 : ℝ) * t = 9 * t / 16 := by ring
  have he3 : (27 / 32 : ℝ) * t = 27 * t / 32 := by ring
  rw [he0, he1, he2, he3]
  linarith

/-- Power growth of `fullMass` at `37/50` for a nonempty backward-closed class,
conditional on both depth-five productions. -/
theorem fullMass_growth {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (hq : DepthFiveProductionBounds A) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t →
      K * t ^ ((37 : ℝ) / 50) ≤ fullMass A t := by
  obtain ⟨b, C, hb, hC, T, hrec⟩ := production_recurrence hA hq
  set s := 16 + 32 * b / 5 with hs
  have hs0 : 0 ≤ s := by positivity
  obtain ⟨S, hS⟩ := fullMass_eventually_ge hA ha hAa (8 * C + 1)
  let T₁ := max 1 (max (T + s) (2 * (S + s)))
  have hT₁ : 0 < T₁ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hTT : T + s ≤ T₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hST : 2 * (S + s) ≤ T₁ := (le_max_right _ _).trans (le_max_right _ _)
  let g : ℝ → ℝ := fun t => fullMass A (t - s) - 8 * C
  have hseed : ∀ t, (1 / 2 : ℝ) * T₁ ≤ t → t ≤ T₁ → 1 ≤ g t := by
    intro t ht _
    have hs' := hS (t - s) (by linarith)
    dsimp [g]
    linarith
  have hr := shifted_recurrence (fullMass_monotone A) hb hC hrec
  have hmain := recursion_lemma rate coeff (fun _ _ => 0) (fun _ => 0) g
    (37 / 50) T₁ 1 (1 / 2) (27 / 32)
    (by norm_num) hT₁ (by norm_num) (by norm_num) (by norm_num)
    (fun i => (rate_bounds i).1) (fun i => (rate_bounds i).2)
    certificate_37_50
    (by intros; norm_num)
    (fun _ _ i => coeff_nonneg i)
    (by intros; nlinarith [certificate_37_50])
    (by intros; simp only [zero_mul, sum_const_zero]; linarith [certificate_37_50])
    hseed (by
      intro t ht
      simpa only [sub_zero, g] using hr t (hTT.trans ht))
  refine ⟨T₁ ^ (-(37 / 50 : ℝ)), by positivity, T₁, hT₁, ?_⟩
  intro t ht
  have hm := hmain t (by linarith)
  have hmono := fullMass_monotone A (show t - s ≤ t by linarith)
  dsimp [g] at hm
  simp only [one_mul] at hm
  linarith

/-- Contagion at `37/50`, conditional only on the two depth-five productions. -/
theorem logMass_growth_of_depth_five {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (hq : DepthFiveProductionBounds A) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      K * Real.log x ^ ((37 : ℝ) / 50) ≤ logMass A x := by
  obtain ⟨K, hK, T, hT, h⟩ := fullMass_growth hA ha hAa hq
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

private theorem failures_growth_depth_five
    (hq : DepthFiveProductionBounds (fun n => ¬ReachesOne n)) :
    (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ ((37 : ℝ) / 50) ≤ logMass (fun n => ¬ReachesOne n) x :=
  fun ⟨_a, ha, hfail⟩ =>
    logMass_growth_of_depth_five not_reachesOne_backwardClosed ha hfail hq

/-- Tao-rate implication at `13/50`, conditional on both depth-five productions. -/
theorem conjecture_of_tao_rate {e : ℝ} (he : 13 / 50 < e)
    (hq : DepthFiveProductionBounds (fun n => ¬ReachesOne n))
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  tao_rate_implies_conjecture (lam := 37 / 50) (by norm_num) (by norm_num)
    (by linarith) (failures_growth_depth_five hq) htao

/-- Theorem 9.2's corollary at `13/50`, conditional on both depth-five productions. -/
theorem pressure_conjecture_depth_five {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε) (he13 : 13 / 50 < e)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y)
    (hq : DepthFiveProductionBounds (fun n => ¬ReachesOne n)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Pressure.pressure_conj_of_contagion hN hfloor C ε e hC he hP
    (lam := 37 / 50) (by norm_num) (by norm_num) (by linarith)
    (failures_growth_depth_five hq)

/-- Proposition 9.3's corollary at `13/50`, conditional on both depth-five
productions. -/
theorem noMomentum_conjecture_depth_five {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he : e < momentumExponent C q δ)
    (he13 : 13 / 50 < e)
    (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y)
    (hq : DepthFiveProductionBounds (fun n => ¬ReachesOne n)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Pressure.noMomentum_conj_of_contagion hN hfloor C q δ e hC hq0 hqp he hM
    (lam := 37 / 50) (by norm_num) (by norm_num) (by linarith)
    (failures_growth_depth_five hq)

end Problems.Juggler.FateDepthFiveAssembly
