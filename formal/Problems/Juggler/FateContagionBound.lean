import Problems.Juggler.FateRecursion
import Problems.Juggler.FateSeed
import Problems.Juggler.FateCylinderCorollary

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The contagion theorem from the production inequality

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Theorem 5.3 given the production
inequality (5.2), Theorem 7.3, and the composite of Corollary 8.4 with Theorem 5.3.

Theorem 5.3 has three inputs: the recursion lemma (Lemma 5.1, `recursion_lemma`), the seed
(Lemma 5.2, `seed_lemma`), and the production inequality (5.2) with the `V`-ladder terms of
Section 5.7,

  `g_A(t) ≥ Σ_{i<8} (c_i - η_i(t)) g_A(e_i t) - η₀(t)`   for `t ≥ t₀`, errors `η → 0`,

with `(e_i, c_i) = (1/2, 1), (3/8, 1/9), (3/4, 2/9), (9/32, 1/27), (27/128, 1/81),
(81/512, 1/243), (243/2048, 1/729), (729/8192, 1/2187)`. The first two are Lean already; the
third is the analytic content of Sections 4 and 5.7 (the block average, the fiber lemmas
and the audited productions) and stays a human proof. This module takes (5.2) as a
hypothesis and proves the rest of Theorem 5.3 exactly:

* `zeta lam = Σ c_i e_i^λ - 1` is antitone in `λ` (`zeta_antitone`) and positive at
  `λ = 0.49` (`zeta_pos_49`), by eight rational lower bounds `r_i ≤ e_i^{49/100}` each
  checked as `r_i^100 ≤ e_i^49` in exact arithmetic (`le_rpow_div_of_pow_le`); the paper's
  root is `λ** = 0.4926…`, and `0.49` is what this file certifies.
* `gA A t = halfLogMass A ⌊e^t⌋₊` is the paper's `g_A(t)`, the log-mass on `(√x, x]` at
  `x = e^t` (`gA_seed` is Lemma 5.2 in that form; `logMass_ge_gA` compares it with the
  full log-mass up to `x`).
* `contagion_of_production_inequality`: for a backward-closed class with a positive member,
  every `0 < λ ≤ 0.49`, and the production inequality with vanishing errors,
  `g_A(t) ≥ K t^λ` for all large `t`, some `K > 0`; `logMass_contagion_of_production` is the
  same in the form `Σ_{n ≤ x, n ∈ A} 1/n ≥ K (log x)^λ` that Theorem 7.2 consumes.
* `tao_rate_iff_conjecture` is Theorem 7.3 with the contagion bound as a hypothesis, and
  `conjecture_of_cylinder_bound_of_production` is Corollary 8.4 with Theorem 5.3 discharged
  through (5.2): the cylinder hypothesis `H(C, A)` at all large scales, `1 - λ < e(C)` for
  some `λ ≤ 0.49`, and the production inequality for the failure set give that every
  positive integer reaches `1`.

Not a halt theorem: the production inequality is a hypothesis here, and so is the cylinder
bound. The paper's "for every `λ < λ**`" is not formalized; `λ ≤ 0.49` is.
-/

/-! ### The production data of (5.2) -/

/-- The contraction factors `e_i` of the eight productions: `E`, the pairing at depth two,
the rest at depth two, `OEOEE`, and the ladder `V_3` to `V_6`. -/
noncomputable def productionRate : Fin 8 → ℝ
  | 0 => 1 / 2
  | 1 => 3 / 8
  | 2 => 3 / 4
  | 3 => 9 / 32
  | 4 => 27 / 128
  | 5 => 81 / 512
  | 6 => 243 / 2048
  | 7 => 729 / 8192

/-- The coefficients `c_i` of the eight productions. -/
noncomputable def productionCoeff : Fin 8 → ℝ
  | 0 => 1
  | 1 => 1 / 9
  | 2 => 2 / 9
  | 3 => 1 / 27
  | 4 => 1 / 81
  | 5 => 1 / 243
  | 6 => 1 / 729
  | 7 => 1 / 2187

theorem productionRate_pos (i : Fin 8) : 0 < productionRate i := by
  fin_cases i <;> norm_num [productionRate]

theorem productionRate_ge (i : Fin 8) : 729 / 8192 ≤ productionRate i := by
  fin_cases i <;> norm_num [productionRate]

theorem productionRate_le (i : Fin 8) : productionRate i ≤ 3 / 4 := by
  fin_cases i <;> norm_num [productionRate]

theorem productionRate_le_one (i : Fin 8) : productionRate i ≤ 1 :=
  le_trans (productionRate_le i) (by norm_num)

theorem productionCoeff_ge (i : Fin 8) : 1 / 2187 ≤ productionCoeff i := by
  fin_cases i <;> norm_num [productionCoeff]

theorem productionCoeff_nonneg (i : Fin 8) : 0 ≤ productionCoeff i :=
  le_trans (by norm_num) (productionCoeff_ge i)

/-! ### The ladder constants are the paper's, not eight arbitrary numerals

The five ladder entries are indexed by `k = 2, …, 6`, the word `V_k = (OE)^(k-1) OEE` of
`FateProductionWords`, at `Fin 8` position `k + 1`. Paper C fixes them by two formulas rather
than by listing: the contraction factor is `ρ_k = (1/2)(3/4)^k`, and the coefficient is the
*increment* `c_k - (2/9) c_{k-1}` with `c_k = 3^{-k}` the word's own logarithmic coefficient --
inclusion-exclusion removing the `V_k`-starts the depth-two `OE` family has already counted.
That increment collapses to `3^{-(k+1)}`, which is (5.9).

These two theorems tie the enumerated definitions above to those formulas, so a numeral cannot
drift from the derivation without the build noticing. -/

/-- **The ladder rates are `ρ_k = (1/2)(3/4)^k`**, `k = 2, …, 6`. -/
theorem productionRate_ladder :
    productionRate 3 = 1 / 2 * (3 / 4) ^ 2 ∧ productionRate 4 = 1 / 2 * (3 / 4) ^ 3 ∧
      productionRate 5 = 1 / 2 * (3 / 4) ^ 4 ∧ productionRate 6 = 1 / 2 * (3 / 4) ^ 5 ∧
      productionRate 7 = 1 / 2 * (3 / 4) ^ 6 := by
  norm_num [productionRate]

/-- **The ladder coefficients are the increments of (5.9)**: `c_k - (2/9) c_{k-1} = 3^{-(k+1)}`
with `c_k = 3^{-k}`. The `2/9` is the depth-two `OE` coefficient, so each ladder term is what
the word contributes *beyond* what that family already counts. -/
theorem productionCoeff_ladder :
    productionCoeff 3 = (3 : ℝ) ^ (-2 : ℤ) - 2 / 9 * (3 : ℝ) ^ (-1 : ℤ) ∧
      productionCoeff 4 = (3 : ℝ) ^ (-3 : ℤ) - 2 / 9 * (3 : ℝ) ^ (-2 : ℤ) ∧
      productionCoeff 5 = (3 : ℝ) ^ (-4 : ℤ) - 2 / 9 * (3 : ℝ) ^ (-3 : ℤ) ∧
      productionCoeff 6 = (3 : ℝ) ^ (-5 : ℤ) - 2 / 9 * (3 : ℝ) ^ (-4 : ℤ) ∧
      productionCoeff 7 = (3 : ℝ) ^ (-6 : ℤ) - 2 / 9 * (3 : ℝ) ^ (-5 : ℤ) := by
  norm_num [productionCoeff]

/-- The same coefficients in closed form, `3^{-(k+1)}`: the increment collapses. -/
theorem productionCoeff_ladder_closed :
    productionCoeff 3 = (3 : ℝ) ^ (-3 : ℤ) ∧ productionCoeff 4 = (3 : ℝ) ^ (-4 : ℤ) ∧
      productionCoeff 5 = (3 : ℝ) ^ (-5 : ℤ) ∧ productionCoeff 6 = (3 : ℝ) ^ (-6 : ℤ) ∧
      productionCoeff 7 = (3 : ℝ) ^ (-7 : ℤ) := by
  norm_num [productionCoeff]

/-- The paper's `ζ(λ) = Σ_i c_i e_i^λ - 1`; Theorem 5.3 holds for every `λ` with `ζ(λ) > 0`. -/
noncomputable def zeta (lam : ℝ) : ℝ :=
  ∑ i, productionCoeff i * productionRate i ^ lam - 1

/-- `ζ` is antitone: every `e_i ≤ 1`. -/
theorem zeta_antitone {lam lam' : ℝ} (h : lam ≤ lam') : zeta lam' ≤ zeta lam := by
  unfold zeta
  apply sub_le_sub_right
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (productionCoeff_nonneg i)
  exact Real.rpow_le_rpow_of_exponent_ge (productionRate_pos i) (productionRate_le_one i) h

/-- A rational lower bound for a rational power: `r ≤ x^{p/q}` from `r^q ≤ x^p`. -/
theorem le_rpow_div_of_pow_le {x r : ℝ} (hx : 0 < x) {p q : ℕ} (hq : 0 < q)
    (h : r ^ q ≤ x ^ p) : r ≤ x ^ ((p : ℝ) / q) := by
  have hxq : (x ^ ((p : ℝ) / q)) ^ q = x ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, div_mul_cancel₀ _ (by positivity),
      Real.rpow_natCast]
  have hpos : 0 ≤ x ^ ((p : ℝ) / q) := Real.rpow_nonneg hx.le _
  exact le_of_pow_le_pow_left₀ hq.ne' hpos (by rw [hxq]; exact h)

/-- `ζ(0.49) > 0`: the eight production terms at `λ = 49/100` sum to more than `1`, by exact
rational lower bounds (`e_i^{49} ≥ r_i^{100}`). The paper's root is `λ** = 0.4926…`. -/
theorem zeta_pos_49 : 0 < zeta (49 / 100) := by
  have h0 : (35601 / 50000 : ℝ) ≤ (1 / 2 : ℝ) ^ ((49 : ℝ) / 100) := by
    have := le_rpow_div_of_pow_le (x := (1 / 2 : ℝ)) (r := 35601 / 50000) (p := 49) (q := 100)
      (by norm_num) (by norm_num) (by norm_num)
    exact_mod_cast this
  have h1 : (773 / 1250 : ℝ) ≤ (3 / 8 : ℝ) ^ ((49 : ℝ) / 100) := by
    have := le_rpow_div_of_pow_le (x := (3 / 8 : ℝ)) (r := 773 / 1250) (p := 49) (q := 100)
      (by norm_num) (by norm_num) (by norm_num)
    exact_mod_cast this
  have h2 : (21713 / 25000 : ℝ) ≤ (3 / 4 : ℝ) ^ ((49 : ℝ) / 100) := by
    have := le_rpow_div_of_pow_le (x := (3 / 4 : ℝ)) (r := 21713 / 25000) (p := 49) (q := 100)
      (by norm_num) (by norm_num) (by norm_num)
    exact_mod_cast this
  have h3 : (5371 / 10000 : ℝ) ≤ (9 / 32 : ℝ) ^ ((49 : ℝ) / 100) := by
    have := le_rpow_div_of_pow_le (x := (9 / 32 : ℝ)) (r := 5371 / 10000) (p := 49) (q := 100)
      (by norm_num) (by norm_num) (by norm_num)
    exact_mod_cast this
  have h4 : (5831 / 12500 : ℝ) ≤ (27 / 128 : ℝ) ^ ((49 : ℝ) / 100) := by
    have := le_rpow_div_of_pow_le (x := (27 / 128 : ℝ)) (r := 5831 / 12500) (p := 49) (q := 100)
      (by norm_num) (by norm_num) (by norm_num)
    exact_mod_cast this
  have h5 : (20257 / 50000 : ℝ) ≤ (81 / 512 : ℝ) ^ ((49 : ℝ) / 100) := by
    have := le_rpow_div_of_pow_le (x := (81 / 512 : ℝ)) (r := 20257 / 50000) (p := 49) (q := 100)
      (by norm_num) (by norm_num) (by norm_num)
    exact_mod_cast this
  have h6 : (8797 / 25000 : ℝ) ≤ (243 / 2048 : ℝ) ^ ((49 : ℝ) / 100) := by
    have := le_rpow_div_of_pow_le (x := (243 / 2048 : ℝ)) (r := 8797 / 25000) (p := 49) (q := 100)
      (by norm_num) (by norm_num) (by norm_num)
    exact_mod_cast this
  have h7 : (30561 / 100000 : ℝ) ≤ (729 / 8192 : ℝ) ^ ((49 : ℝ) / 100) := by
    have := le_rpow_div_of_pow_le (x := (729 / 8192 : ℝ)) (r := 30561 / 100000) (p := 49)
      (q := 100) (by norm_num) (by norm_num) (by norm_num)
    exact_mod_cast this
  have e0 : productionRate 0 = 1 / 2 := rfl
  have e1 : productionRate 1 = 3 / 8 := rfl
  have e2 : productionRate 2 = 3 / 4 := rfl
  have e3 : productionRate 3 = 9 / 32 := rfl
  have e4 : productionRate 4 = 27 / 128 := rfl
  have e5 : productionRate 5 = 81 / 512 := rfl
  have e6 : productionRate 6 = 243 / 2048 := rfl
  have e7 : productionRate 7 = 729 / 8192 := rfl
  have c0 : productionCoeff 0 = 1 := rfl
  have c1 : productionCoeff 1 = 1 / 9 := rfl
  have c2 : productionCoeff 2 = 2 / 9 := rfl
  have c3 : productionCoeff 3 = 1 / 27 := rfl
  have c4 : productionCoeff 4 = 1 / 81 := rfl
  have c5 : productionCoeff 5 = 1 / 243 := rfl
  have c6 : productionCoeff 6 = 1 / 729 := rfl
  have c7 : productionCoeff 7 = 1 / 2187 := rfl
  unfold zeta
  rw [Fin.sum_univ_eight, e0, e1, e2, e3, e4, e5, e6, e7, c0, c1, c2, c3, c4, c5, c6, c7]
  linarith

/-! ### The paper's `g_A` -/

/-- The seed constant `c_A` of Lemma 5.2. -/
noncomputable def seedConst (m : ℕ) : ℝ :=
  (1 - 2 / (m : ℝ) ^ 4) * (3 / 8 / ((m : ℝ) + 1) - 1 / (((m : ℝ) + 1) ^ 2 - 1))

/-- The paper's `g_A(t)`: the log-mass of `A` on `(√x, x]` at `x = e^t`, on the integers of
`(⌊√⌊x⌋⌋, ⌊x⌋]`. -/
noncomputable def gA (A : ℕ → Prop) (t : ℝ) : ℝ :=
  halfLogMass A ⌊Real.exp t⌋₊

/-- Lemma 5.2 in the form `g_A(t) ≥ c_A` for `t ≥ 4 log(m+1)`. -/
theorem gA_seed {A : ℕ → Prop} (hA : BackwardClosed A) {m : ℕ} (hm : 3 ≤ m) (hmA : A m)
    {t : ℝ} (ht : 4 * Real.log ((m : ℝ) + 1) ≤ t) : seedConst m ≤ gA A t := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hpow : (((m + 1) ^ 4 : ℕ) : ℝ) ≤ Real.exp t := by
    have : ((m : ℝ) + 1) ^ 4 = Real.exp (Real.log ((m : ℝ) + 1) * 4) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hm1]
      norm_num
    push_cast
    rw [this]
    exact Real.exp_le_exp.mpr (by linarith)
  have hy : (m + 1) ^ 4 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor hpow
  exact seed_lemma hA hm hmA hy

/-- `g_A(log x)` is at most the full log-mass up to `x`. -/
theorem logMass_ge_gA (A : ℕ → Prop) {x : ℕ} (hx : 1 ≤ x) : gA A (Real.log x) ≤ logMass A x := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  unfold gA
  rw [Real.exp_log hxpos, Nat.floor_natCast]
  unfold halfLogMass logMass
  apply sum_le_sum_of_subset_of_nonneg _ (fun n _ _ => by positivity)
  intro n hn
  simp only [mem_filter, mem_Ioc, mem_Icc] at hn ⊢
  exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩

/-! ### Theorem 5.3 given the production inequality -/

/-- **Paper C Theorem 5.3, given the production inequality (5.2).** Let `A` be
backward-closed with a positive member, `0 < λ ≤ 0.49`, and suppose

  `g_A(t) ≥ Σ_i (c_i - η_i(t)) g_A(e_i t) - η₀(t)`   for all `t ≥ t₀`,

with errors `η_i(t), η₀(t) ≥ 0` that tend to `0`. Then `g_A(t) ≥ K t^λ` for all large `t`,
some `K > 0`. The proof is the paper's: the seed of Lemma 5.2 on `[e_min t₁, t₁]`, the
recursion lemma with `ζ(λ) ≥ ζ(0.49) > 0`, and `t₁` large enough that the errors are below
`ζ/24` and `(2ζ/3) c_A`. -/
theorem contagion_of_production_inequality {A : ℕ → Prop} (hA : BackwardClosed A)
    {a : ℕ} (ha : 1 ≤ a) (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 49 / 100)
    (η : Fin 8 → ℝ → ℝ) (η₀ : ℝ → ℝ) (t₀ : ℝ)
    (hη_lo : ∀ t, t₀ ≤ t → ∀ i, 0 ≤ η i t)
    (hvanish : ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → (∀ i, η i t ≤ ε) ∧ η₀ t ≤ ε)
    (hrec : ∀ t, t₀ ≤ t →
      ∑ i, (productionCoeff i - η i t) * gA A (productionRate i * t) - η₀ t ≤ gA A t) :
    ∃ K : ℝ, 0 < K ∧ ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t, t₁ ≤ t → K * t ^ lam ≤ gA A t := by
  obtain ⟨m, hm, hmA⟩ := exists_ge_three_of_backwardClosed hA ha hAa
  have hc₀ : 0 < seedConst m := seed_constant_pos hm
  have hζ : 0 < ∑ i, productionCoeff i * productionRate i ^ lam - 1 :=
    lt_of_lt_of_le zeta_pos_49 (zeta_antitone hlam)
  -- the error budget
  obtain ⟨ε, hε, hε1, hε2, hε3⟩ : ∃ ε : ℝ, 0 < ε ∧
      ε ≤ (∑ i, productionCoeff i * productionRate i ^ lam - 1) / 24 ∧
      ε ≤ 2 * (∑ i, productionCoeff i * productionRate i ^ lam - 1) / 3 * seedConst m ∧
      ε ≤ 1 / 2187 :=
    ⟨min ((∑ i, productionCoeff i * productionRate i ^ lam - 1) / 24)
      (min (2 * (∑ i, productionCoeff i * productionRate i ^ lam - 1) / 3 * seedConst m)
        (1 / 2187)),
      lt_min (by positivity) (lt_min (by positivity) (by norm_num)), min_le_left _ _,
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  obtain ⟨T, hT⟩ := hvanish ε hε
  -- the scale `t₁`
  obtain ⟨t₁, ht₁T, ht₁0, ht₁1, ht₁seed⟩ : ∃ t₁ : ℝ, T ≤ t₁ ∧ t₀ ≤ t₁ ∧ 1 ≤ t₁ ∧
      4 * Real.log ((m : ℝ) + 1) ≤ 729 / 8192 * t₁ :=
    ⟨max (max T t₀) (max 1 (4 * Real.log ((m : ℝ) + 1) / (729 / 8192))),
      le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _),
      le_trans (le_max_left _ _) (le_max_right _ _), by
        have h := le_trans (le_max_right _ _)
          (le_max_right (max T t₀) (max 1 (4 * Real.log ((m : ℝ) + 1) / (729 / 8192))))
        rw [div_le_iff₀ (by norm_num)] at h
        linarith⟩
  have ht₁pos : 0 < t₁ := by linarith
  have hrate_le_one : ∀ i, productionRate i ^ lam ≤ 1 := fun i =>
    Real.rpow_le_one (productionRate_pos i).le (productionRate_le_one i) hlam0.le
  have hmain := recursion_lemma productionRate productionCoeff η η₀ (gA A) lam t₁ (seedConst m)
    (729 / 8192) (3 / 4) hlam0 ht₁pos hc₀ (by norm_num) (by norm_num) productionRate_ge
    productionRate_le hζ
    (fun t ht i => hη_lo t (le_trans ht₁0 ht) i)
    (fun t ht i => le_trans ((hT t (le_trans ht₁T ht)).1 i)
      (le_trans hε3 (productionCoeff_ge i)))
    (fun t ht => le_trans (hT t (le_trans ht₁T ht)).2 hε2)
    (fun t ht => by
      calc ∑ i, η i t * productionRate i ^ lam ≤ ∑ _i : Fin 8, ε := by
            apply sum_le_sum
            intro i _
            calc η i t * productionRate i ^ lam ≤ ε * 1 := by
                  apply mul_le_mul ((hT t (le_trans ht₁T ht)).1 i) (hrate_le_one i)
                    (Real.rpow_nonneg (productionRate_pos i).le _) hε.le
              _ = ε := mul_one ε
        _ = 8 * ε := by simp
        _ ≤ (∑ i, productionCoeff i * productionRate i ^ lam - 1) / 3 := by linarith)
    (fun t ht _ => gA_seed hA hm hmA (le_trans ht₁seed ht))
    (fun t ht => hrec t (le_trans ht₁0 ht))
  refine ⟨seedConst m * t₁ ^ (-lam), by positivity, t₁, ht₁pos, ?_⟩
  intro t ht
  exact hmain t (le_trans (by nlinarith) ht)

/-- Theorem 5.3 given (5.2), in the form Theorem 7.2 consumes:
`Σ_{n ≤ x, n ∈ A} 1/n ≥ K (log x)^λ` for all large `x`. -/
theorem logMass_contagion_of_production {A : ℕ → Prop} (hA : BackwardClosed A)
    {a : ℕ} (ha : 1 ≤ a) (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 49 / 100)
    (η : Fin 8 → ℝ → ℝ) (η₀ : ℝ → ℝ) (t₀ : ℝ)
    (hη_lo : ∀ t, t₀ ≤ t → ∀ i, 0 ≤ η i t)
    (hvanish : ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → (∀ i, η i t ≤ ε) ∧ η₀ t ≤ ε)
    (hrec : ∀ t, t₀ ≤ t →
      ∑ i, (productionCoeff i - η i t) * gA A (productionRate i * t) - η₀ t ≤ gA A t) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → K * Real.log x ^ lam ≤ logMass A x := by
  obtain ⟨K, hK, t₁, ht₁, h⟩ :=
    contagion_of_production_inequality hA ha hAa hlam0 hlam η η₀ t₀ hη_lo hvanish hrec
  refine ⟨K, hK, ⌈Real.exp t₁⌉₊ + 1, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := by omega
  have hxR : Real.exp t₁ ≤ x := by
    have h1 := Nat.le_ceil (Real.exp t₁)
    have h2 : ((⌈Real.exp t₁⌉₊ + 1 : ℕ) : ℝ) ≤ x := by exact_mod_cast hx
    push_cast at h2
    linarith
  have hlog : t₁ ≤ Real.log x := (Real.le_log_iff_exp_le (by positivity)).mpr hxR
  exact le_trans (h _ hlog) (logMass_ge_gA A hx1)

/-! ### Theorem 7.3 and the composite with Corollary 8.4 -/

/-- Every positive integer reaching `1` empties the odd failures of every block. -/
theorem oddFailures_eq_empty (h : ∀ n, 1 ≤ n → ReachesOne n) (y : ℕ) : oddFailures y = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro n hn
  simp only [oddFailures, mem_filter, mem_Ioc] at hn
  exact hn.2.2 (h n (by omega))

/-- **Paper C Theorem 7.3 (equivalence), with the contagion bound of Theorem 5.3 as a
hypothesis.** Every positive integer reaches `1` iff the odd failures satisfy a Tao-type rate
`y (log y)^{-e}` with some `e > 1 - λ` at all large scales. -/
theorem tao_rate_iff_conjecture {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) → ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    (∀ n, 1 ≤ n → ReachesOne n) ↔
      ∃ e : ℝ, 1 - lam < e ∧ ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
        ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e) := by
  constructor
  · intro h
    refine ⟨2 - lam, by linarith, 1, ?_⟩
    intro y hy
    rw [oddFailures_eq_empty h, card_empty]
    have : (0 : ℝ) ≤ Real.log y ^ (-(2 - lam)) := Real.rpow_nonneg (Real.log_natCast_nonneg y) _
    push_cast
    positivity
  · rintro ⟨e, he, htao⟩
    exact tao_rate_implies_conjecture hlam0 hlam1 he hlow htao

/-- **Corollary 8.4 with Theorem 5.3 discharged through the production inequality.** If the
cylinder hypothesis `H(C, A)` holds at all large scales with `C ≥ 5`, `A > C + e(C)` and
`1 - λ < e(C)` for some `0 < λ ≤ 0.49`, and the failure set (if nonempty) satisfies the
production inequality (5.2) with vanishing errors, then every positive integer reaches `1`. -/
theorem conjecture_of_cylinder_bound_of_production {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C A : ℝ) (hC : 5 ≤ C)
    (hA : C + chernoffExponent C < A)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ C A y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 49 / 100) (hlamC : 1 - lam < chernoffExponent C)
    (η : Fin 8 → ℝ → ℝ) (η₀ : ℝ → ℝ) (t₀ : ℝ)
    (hη_lo : ∀ t, t₀ ≤ t → ∀ i, 0 ≤ η i t)
    (hvanish : ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → (∀ i, η i t ≤ ε) ∧ η₀ t ≤ ε)
    (hrec : ∀ t, t₀ ≤ t →
      ∑ i, (productionCoeff i - η i t) * gA (fun n => ¬ReachesOne n) (productionRate i * t) -
        η₀ t ≤ gA (fun n => ¬ReachesOne n) t) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  refine cylinder_bound_implies_conjecture hN hfloor C A hC hA hcyl hlam0 (by linarith) hlamC ?_
  rintro ⟨a, ha, hAa⟩
  exact logMass_contagion_of_production not_reachesOne_backwardClosed ha hAa hlam0 hlam η η₀ t₀
    hη_lo hvanish hrec

end Problems.Juggler
