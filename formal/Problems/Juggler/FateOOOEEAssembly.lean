import Problems.Juggler.FateOOEEWeighted
import Problems.Juggler.FatePressureCorollary

/-!
# Four actual productions and the exponent 2/3

The productions `E`, `OE` and `OOEE` are unconditional (`FateOOEEWeighted`).
This module adds the depth-five word `OOOEE` (odd, odd, odd, even, even; rate
`27/32`) as the single explicit input `OOOEEProductionBound`, with coefficient
`1/30` and an arbitrary fixed loss `b` in the argument. The four-way source
partition, the recurrence, its shift `16 + 32b/5` and loss multiplier `7`, the
rational certificate at `2/3`, and the Tao and pressure implications at `1/3` are
kernel-checked. The OOOEE production itself is the written, unreviewed
reduction of `docs/problems/juggler_depth_five_production.md` (Results 7-17)
and is not supplied here.
-/

noncomputable section

namespace Problems.Juggler.FateOOOEEAssembly

open Finset Filter CodeMassTransport FateOOEEAssembly Pressure
open scoped Classical Topology

/-- The actual depth-five parity word `OOOEE`: `n`, `J n`, `J^2 n` odd and
`J^3 n`, `J^4 n` even. -/
def OOOEEGuard (n : ℕ) : Prop :=
  n % 2 = 1 ∧ floorPower n % 2 = 1 ∧
    floorPower (floorPower n) % 2 = 1 ∧
    floorPower (floorPower (floorPower n)) % 2 = 0 ∧
    floorPower (floorPower (floorPower (floorPower n))) % 2 = 0

/-- The written `OOOEE` production, with its source cutoff and a fixed loss `b`. -/
def OOOEEProductionBound (A : ℕ → Prop) : Prop :=
  ∃ b C : ℝ, 0 ≤ b ∧ 0 ≤ C ∧ ∃ T : ℝ, ∀ t, T ≤ t →
    (1 / 30) * fullMass A (27 * t / 32 - b) ≤ sourceMass A OOOEEGuard (cutoff t) + C

/-- The even, `OE`, `OOEE` and `OOOEE` sources are disjoint, so their masses add
up to at most the full mass. -/
theorem source_partition (A : ℕ → Prop) (X : ℕ) :
    sourceMass A (fun n => n % 2 = 0) X + sourceMass A oeGuard X +
      sourceMass A ooeeGuard X + sourceMass A OOOEEGuard X ≤ mass A X := by
  unfold sourceMass mass
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro n _
  have hw := weight_nonneg n
  by_cases hA : A n
  · by_cases hE : n % 2 = 0
    · simp [hA, hE, oeGuard, ooeeGuard, OOOEEGuard]
    · have hO : n % 2 = 1 := by omega
      by_cases hJ : floorPower n % 2 = 0
      · simp [hA, hO, hJ, oeGuard, ooeeGuard, OOOEEGuard]
      · have hJ1 : floorPower n % 2 = 1 := by omega
        by_cases hJ2 : floorPower (floorPower n) % 2 = 0
        · by_cases hg : ooeeGuard n
          · have hq : ¬ OOOEEGuard n := fun h => by rw [h.2.2.1] at hJ2; omega
            simp [hA, hO, hJ1, oeGuard, hg, hq]
          · have hq : ¬ OOOEEGuard n := fun h => by rw [h.2.2.1] at hJ2; omega
            simp [hA, hO, hJ1, oeGuard, hg, hq, hw]
        · have hg : ¬ ooeeGuard n := fun h => hJ2 h.2.2.1
          by_cases hq : OOOEEGuard n <;> simp [hA, hO, hJ1, oeGuard, hg, hq, hw]
  · simp [hA]

/-- The four productions give one functional inequality for `fullMass`, with the
`OOOEE` loss `b` and a single constant `C`. -/
theorem production_recurrence {A : ℕ → Prop} (hA : BackwardClosed A)
    (hq : OOOEEProductionBound A) : ∃ b C : ℝ, 0 ≤ b ∧ 0 ≤ C ∧ ∃ T : ℝ, ∀ t, T ≤ t →
      fullMass A (t / 2 - 4) + (33 / 100) * fullMass A (3 * t / 4 - 4) +
        (11 / 100) * fullMass A (9 * t / 16 - 4) +
        (1 / 30) * fullMass A (27 * t / 32 - b) - 3 * C ≤ fullMass A t := by
  obtain ⟨C₁, hC₁, T₁, hp⟩ :=
    FateOEWeighted.oddProductionBounds_of_ooee hA (FateOOEEWeighted.ooee_production hA)
  obtain ⟨b, C₂, hb, hC₂, T₂, hq⟩ := hq
  refine ⟨b, C₁ + C₂, hb, by positivity, max (max T₁ T₂) 8, ?_⟩
  intro t ht
  have hT₁ : T₁ ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have hT₂ : T₂ ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  obtain ⟨h1, h2⟩ := hp t hT₁
  have h3 := hq t hT₂
  have h0 := even_source_lower hA ((le_max_right _ _).trans ht)
  have hsum := source_partition A (cutoff t)
  change _ ≤ mass A (cutoff t)
  linarith

/-- The rates `1/2`, `3/4`, `9/16` and `27/32` of the four productions. -/
def rate : Fin 4 → ℝ | 0 => 1 / 2 | 1 => 3 / 4 | 2 => 9 / 16 | 3 => 27 / 32
/-- The coefficients `1`, `33/100`, `11/100` and `1/30` of the four productions. -/
def coeff : Fin 4 → ℝ | 0 => 1 | 1 => 33 / 100 | 2 => 11 / 100 | 3 => 1 / 30

/-- Every rate lies in `[1/2, 27/32]`. -/
theorem rate_bounds (i : Fin 4) : 1 / 2 ≤ rate i ∧ rate i ≤ 27 / 32 := by
  fin_cases i <;> norm_num [rate]

/-- Every coefficient is nonnegative. -/
theorem coeff_nonneg (i : Fin 4) : 0 ≤ coeff i := by
  fin_cases i <;> norm_num [coeff]

/-- The four-production root exceeds `2/3`; Arb encloses it as `0.679304053427 ± 6e-13`. -/
theorem certificate_two_thirds : 0 < ∑ i, coeff i * rate i ^ ((2 : ℝ) / 3) - 1 := by
  have h0 : (6299 / 10000 : ℝ) ≤ (1 / 2 : ℝ) ^ ((2 : ℝ) / 3) :=
    le_rpow_div_of_pow_le (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)
  have h1 : (8254 / 10000 : ℝ) ≤ (3 / 4 : ℝ) ^ ((2 : ℝ) / 3) :=
    le_rpow_div_of_pow_le (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)
  have h2 : (6814 / 10000 : ℝ) ≤ (9 / 16 : ℝ) ^ ((2 : ℝ) / 3) :=
    le_rpow_div_of_pow_le (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)
  have h3 : (8928 / 10000 : ℝ) ≤ (27 / 32 : ℝ) ^ ((2 : ℝ) / 3) :=
    le_rpow_div_of_pow_le (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)
  simp only [Fin.sum_univ_four, rate, coeff]
  linarith

/-- Translate by `16 + 32b/5` and subtract `7C` to remove all four losses. -/
theorem shifted_recurrence {F : ℝ → ℝ} (hF : Monotone F) {b C T : ℝ} (hb : 0 ≤ b)
    (hC : 0 ≤ C)
    (hrec : ∀ t, T ≤ t → F (t / 2 - 4) + (33 / 100) * F (3 * t / 4 - 4) +
      (11 / 100) * F (9 * t / 16 - 4) + (1 / 30) * F (27 * t / 32 - b) - 3 * C ≤ F t) :
    ∀ t, T + (16 + 32 * b / 5) ≤ t →
      ∑ i, coeff i * (F (rate i * t - (16 + 32 * b / 5)) - 7 * C) ≤
        F (t - (16 + 32 * b / 5)) - 7 * C := by
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

/-- Power growth of `fullMass` at `2/3` for a nonempty backward-closed class,
conditional on the `OOOEE` production. -/
theorem fullMass_growth {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (hq : OOOEEProductionBound A) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t →
      K * t ^ ((2 : ℝ) / 3) ≤ fullMass A t := by
  obtain ⟨b, C, hb, hC, T, hrec⟩ := production_recurrence hA hq
  set s := 16 + 32 * b / 5 with hs
  have hs0 : 0 ≤ s := by positivity
  obtain ⟨S, hS⟩ := fullMass_eventually_ge hA ha hAa (7 * C + 1)
  let T₁ := max 1 (max (T + s) (2 * (S + s)))
  have hT₁ : 0 < T₁ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hTT : T + s ≤ T₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hST : 2 * (S + s) ≤ T₁ := (le_max_right _ _).trans (le_max_right _ _)
  let g : ℝ → ℝ := fun t => fullMass A (t - s) - 7 * C
  have hseed : ∀ t, (1 / 2 : ℝ) * T₁ ≤ t → t ≤ T₁ → 1 ≤ g t := by
    intro t ht _
    have hs' := hS (t - s) (by linarith)
    dsimp [g]
    linarith
  have hr := shifted_recurrence (fullMass_monotone A) hb hC hrec
  have hmain := recursion_lemma rate coeff (fun _ _ => 0) (fun _ => 0) g
    (2 / 3) T₁ 1 (1 / 2) (27 / 32)
    (by norm_num) hT₁ (by norm_num) (by norm_num) (by norm_num)
    (fun i => (rate_bounds i).1) (fun i => (rate_bounds i).2)
    certificate_two_thirds
    (by intros; norm_num)
    (fun _ _ i => coeff_nonneg i)
    (by intros; nlinarith [certificate_two_thirds])
    (by intros; simp only [zero_mul, sum_const_zero]; linarith [certificate_two_thirds])
    hseed (by
      intro t ht
      simpa only [sub_zero, g] using hr t (hTT.trans ht))
  refine ⟨T₁ ^ (-(2 / 3 : ℝ)), by positivity, T₁, hT₁, ?_⟩
  intro t ht
  have hm := hmain t (by linarith)
  have hmono := fullMass_monotone A (show t - s ≤ t by linarith)
  dsimp [g] at hm
  simp only [one_mul] at hm
  linarith

/-- Contagion at `2/3`, conditional only on the displayed `OOOEE` production. -/
theorem logMass_growth_of_oooee {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (hq : OOOEEProductionBound A) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      K * Real.log x ^ ((2 : ℝ) / 3) ≤ logMass A x := by
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

private theorem failures_growth_oooee
    (hq : OOOEEProductionBound (fun n => ¬ReachesOne n)) :
    (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ ((2 : ℝ) / 3) ≤ logMass (fun n => ¬ReachesOne n) x :=
  fun ⟨_a, ha, hfail⟩ => logMass_growth_of_oooee not_reachesOne_backwardClosed ha hfail hq

/-- Tao-rate implication at `1/3`, conditional on the `OOOEE` production. -/
theorem conjecture_of_tao_rate {e : ℝ} (he : 1 / 3 < e)
    (hq : OOOEEProductionBound (fun n => ¬ReachesOne n))
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  tao_rate_implies_conjecture (lam := 2 / 3) (by norm_num) (by norm_num)
    (by linarith) (failures_growth_oooee hq) htao

/-- Theorem 9.2's corollary at `1/3`, conditional on the `OOOEE` production. -/
theorem pressure_conjecture_oooee {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε) (he13 : 1 / 3 < e)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y)
    (hq : OOOEEProductionBound (fun n => ¬ReachesOne n)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Pressure.pressure_conj_of_contagion hN hfloor C ε e hC he hP
    (lam := 2 / 3) (by norm_num) (by norm_num) (by linarith) (failures_growth_oooee hq)

/-- Proposition 9.3's corollary at `1/3`, conditional on the `OOOEE` production. -/
theorem noMomentum_conjecture_oooee {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he : e < momentumExponent C q δ)
    (he13 : 1 / 3 < e)
    (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y)
    (hq : OOOEEProductionBound (fun n => ¬ReachesOne n)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Pressure.noMomentum_conj_of_contagion hN hfloor C q δ e hC hq0 hqp he hM
    (lam := 2 / 3) (by norm_num) (by norm_num) (by linarith) (failures_growth_oooee hq)

end Problems.Juggler.FateOOOEEAssembly
