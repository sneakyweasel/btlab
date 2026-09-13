import Problems.Juggler.FateContagionBound
import Problems.Juggler.FateThinFibers
import Problems.Juggler.FateRecursion
import Problems.Juggler.FateCylinderCorollary

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The production inequality, the part that needs no analysis

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Section 5.1 builds the production
inequality (5.2) from three families of members of `A` on `(√x, x]`: the `E`-images of the
members at scale `t/2` (Lemma 3.1), the `OE`-images of `E`-blocks at scale `3t/8`
(Proposition 4.4, the block average), and the `OE`-images of the remaining members at scale
`3t/4` (Lemmas 4.2 and 4.3). The second family is the one that needs the exponential sums.

This file proves the inequality made of the first and third families, with explicit errors and
no hypothesis:

`g_A(t) ≥ (1 - 4e^{-t/4}) g_A(t/2) + (2/9 - (50/9)e^{-t/8}) g_A(3t/4) - η₀(t)`

for `t ≥ 40` (`production_two`), and runs the recursion lemma on it: **every nonempty
backward-closed set has log-mass at least `K (log x)^{3/10}` up to `x`, for all large `x`**
(`logMass_contagion_elementary`). The exponent is the root of
`2^{-λ} + (2/9)(3/4)^λ = 1`, about `0.325`, certified at `λ = 3/10` by two rational bounds;
the paper's `λ ≤ 0.49` needs in addition the block-average family, whose two exponential-sum
bounds are hypotheses in `FateBlockAverage`, and the five ladder productions of Section 5.7,
whose Appendix D estimates are human. Nothing here is a density theorem in the paper's sense,
and nothing here is a halt theorem.
-/

namespace Production

/-! ### Floors of exponentials -/

/-- `⌊√⌊e^t⌋⌋ = ⌊e^{t/2}⌋`: the integer half-scale is what the paper's `√x` means. -/
theorem sqrt_floor_exp (t : ℝ) : Nat.sqrt ⌊Real.exp t⌋₊ = ⌊Real.exp (t / 2)⌋₊ := by
  have he : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos (t / 2)
  apply le_antisymm
  · rw [Nat.le_floor_iff hpos.le]
    set k := Nat.sqrt ⌊Real.exp t⌋₊ with hk
    have h1 : ((k * k : ℕ) : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ) := by exact_mod_cast Nat.sqrt_le _
    have h2 : (⌊Real.exp t⌋₊ : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
    push_cast at h1
    by_contra hlt
    push Not at hlt
    have : Real.exp (t / 2) * Real.exp (t / 2) < (k : ℝ) * k :=
      mul_lt_mul'' hlt hlt hpos.le hpos.le
    linarith
  · rw [Nat.le_sqrt]
    apply Nat.le_floor
    have h1 : ((⌊Real.exp (t / 2)⌋₊ : ℕ) : ℝ) ≤ Real.exp (t / 2) := Nat.floor_le hpos.le
    have h0 : (0 : ℝ) ≤ (⌊Real.exp (t / 2)⌋₊ : ℕ) := Nat.cast_nonneg _
    push_cast
    calc ((⌊Real.exp (t / 2)⌋₊ : ℕ) : ℝ) * ⌊Real.exp (t / 2)⌋₊
        ≤ Real.exp (t / 2) * Real.exp (t / 2) := mul_le_mul h1 h1 h0 hpos.le
      _ = Real.exp t := he

/-- The floor of an exponential is at least half the exponential once the latter is `≥ 2`. -/
theorem floor_exp_ge_half {u : ℝ} (hu : 2 ≤ Real.exp u) :
    Real.exp u / 2 ≤ (⌊Real.exp u⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one (Real.exp u)
  linarith

/-! ### Family 1: the `E`-images of the members at scale `t/2` -/

/-- **Family 1.** For `s₁ = ⌊√y⌋` and `s₂ = ⌊√s₁⌋`, the `E`-blocks of the members of `A` in
`(s₂, s₁ - 1]` lie in `(s₁, y]`, are disjoint, and carry log-mass at least
`(1 - 2/s₂) Σ_{m ∈ A ∩ (s₂, s₁-1]} 1/m`. -/
theorem family_E {A : ℕ → Prop} (hA : BackwardClosed A) {y : ℕ} (hs₂ : 1 ≤ Nat.sqrt (Nat.sqrt y)) :
    (1 - 2 / (Nat.sqrt (Nat.sqrt y) : ℝ)) *
        ∑ m ∈ {m ∈ Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y - 1) | A m}, (1 : ℝ) / m
      ≤ ∑ n ∈ {n ∈ Ioc (Nat.sqrt y) y | A n ∧ n % 2 = 0}, (1 : ℝ) / n := by
  set s₁ := Nat.sqrt y with hs₁
  set s₂ := Nat.sqrt s₁ with hs₂d
  set M := {m ∈ Ioc s₂ (s₁ - 1) | A m} with hM
  -- the blocks sit inside the target set
  have hsub : M.biUnion evenBlock ⊆ {n ∈ Ioc s₁ y | A n ∧ n % 2 = 0} := by
    intro n hn
    rw [mem_biUnion] at hn
    obtain ⟨m, hm, hnm⟩ := hn
    rw [hM, mem_filter, mem_Ioc] at hm
    simp only [evenBlock, mem_filter, mem_Ico] at hnm
    rw [mem_filter, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, even_block_mem hA hm.2 hnm.2 hnm.1.1 hnm.1.2, hnm.2⟩
    · -- `s₁ < m*m ≤ n`: `m > s₂ = ⌊√s₁⌋` gives `m*m > s₁`
      have h := Nat.sqrt_lt'.mp hm.1.1
      rw [pow_two] at h
      omega
    · -- `n < (m+1)² ≤ s₁² ≤ y`
      have h1 : (m + 1) * (m + 1) ≤ s₁ * s₁ := Nat.mul_le_mul (by omega) (by omega)
      have h2 : s₁ * s₁ ≤ y := Nat.sqrt_le y
      omega
  have hdisj : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → Disjoint (evenBlock m) (evenBlock m') :=
    fun _ _ _ _ h => evenBlock_disjoint h
  calc (1 - 2 / (s₂ : ℝ)) * ∑ m ∈ M, (1 : ℝ) / m
      = ∑ m ∈ M, (1 - 2 / (s₂ : ℝ)) / m := by
        rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
    _ ≤ ∑ m ∈ M, ∑ n ∈ evenBlock m, (1 : ℝ) / n := by
        apply sum_le_sum
        intro m hm
        rw [hM, mem_filter, mem_Ioc] at hm
        have hs0 : (0 : ℝ) < s₂ := by exact_mod_cast hs₂
        have hsm : (s₂ : ℝ) ≤ m := by exact_mod_cast hm.1.1.le
        have hm0 : (0 : ℝ) < m := by linarith
        calc (1 - 2 / (s₂ : ℝ)) / m = (1 - 2 / (s₂ : ℝ)) * (1 / m) := by ring
          _ ≤ (1 - 2 / (m : ℝ)) * (1 / m) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hs0 hsm
              linarith
          _ ≤ ∑ n ∈ evenBlock m, (1 : ℝ) / n := evenBlock_logMass_ge' (by omega)
    _ = ∑ n ∈ M.biUnion evenBlock, (1 : ℝ) / n := (sum_biUnion hdisj).symm
    _ ≤ ∑ n ∈ {n ∈ Ioc s₁ y | A n ∧ n % 2 = 0}, (1 : ℝ) / n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-! ### Family 3: the `OE`-images of the members at scale `3t/4` -/

open FiberParity

/-- A good fiber `Φ(m)`, `m ≥ 10⁶`, carries even-image log-mass at least
`(2/9)(1 - (25/2) m^{-1/3})/m`: at least `H_m/3 - 2 ≥ (2/9)m^{1/3} - 7/3` even images
(Lemmas 4.2 and 4.2's fiber bound), each above `1/(u⁴ + 2u)` for `u = m^{1/3}`. -/
theorem good_fiber_logMass_ge {m : ℕ} (hm : 10 ^ 6 ≤ m) (hg : Good m) :
    2 / 9 * (1 - 25 / 2 * eps m) / m
      ≤ ∑ n ∈ {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}, (1 : ℝ) / n := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  set u := (m : ℝ) ^ ((1 : ℝ) / 3) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hm0 _
  have hu3 : u ^ 3 = m := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
  have hu100 : (100 : ℝ) ≤ u := by
    rw [hu, Numerics.le_rpow_iff_pow (n := 3) hm0.le (by norm_num) (by norm_num)]
    have : ((10 ^ 6 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    norm_num at this ⊢
    linarith
  have heps : eps m * u = 1 := eps_mul_cbrt hm1
  have he : eps m = 1 / u := by
    field_simp; linarith
  -- the count of even images
  have hH := oeFiber_card_ge hm1
  have hC := (fiber_parity_good hm hg).1
  rw [← hu] at hH
  -- every member lies below `u⁴ + 2u`
  have hbound : ∀ n ∈ oeFiber m, (n : ℝ) < u ^ 4 + 2 * u := by
    intro n hn
    have h1 := fiber_lt_rpow hn
    have h2 := rpow_four_thirds_succ_le m
    have h3 : (m : ℝ) ^ ((4 : ℝ) / 3) = u ^ 4 := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
    have h4 : ((m : ℝ) + 1) ^ ((1 : ℝ) / 3) ≤ u + 1 := by
      rw [Numerics.rpow_le_iff_pow (n := 3) (by positivity) (by positivity) (by norm_num)]
      norm_num
      nlinarith [hu3, hu0]
    rw [h3] at h2
    linarith
  set P := {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0} with hP
  have hPcard : (P.card : ℝ) = evenImageCount m := by rw [evenImageCount]
  have hden : 0 < u ^ 4 + 2 * u := by positivity
  have hsum : (P.card : ℝ) * (1 / (u ^ 4 + 2 * u)) ≤ ∑ n ∈ P, (1 : ℝ) / n := by
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro n hn
    have hnf : n ∈ oeFiber m := (mem_filter.mp hn).1
    have hn1 : 1 ≤ n := by have := (mem_oeFiber.mp hnf).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    exact one_div_le_one_div_of_le hn0 (hbound n hnf).le
  -- the arithmetic in `u`
  have hkey : 2 / 9 * (1 - 25 / 2 * eps m) / m ≤ (2 / 9 * u - 7 / 3) / (u ^ 4 + 2 * u) := by
    rw [he, ← hu3, div_le_div_iff₀ (by positivity) hden]
    have hu' : u ≠ 0 := hu0.ne'
    field_simp
    nlinarith [hu100, mul_nonneg hu0.le (show (0 : ℝ) ≤ u ^ 2 - 1 by nlinarith [hu100])]
  calc 2 / 9 * (1 - 25 / 2 * eps m) / m ≤ (2 / 9 * u - 7 / 3) / (u ^ 4 + 2 * u) := hkey
    _ ≤ (P.card : ℝ) * (1 / (u ^ 4 + 2 * u)) := by
        rw [div_eq_mul_one_div]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hPcard]; linarith
    _ ≤ ∑ n ∈ P, (1 : ℝ) / n := hsum

/-- **Family 3.** For `U = ⌊√y''⌋ ≥ 10⁶` and any shell `(s, y]` that contains every fiber
`Φ(m)` with `U < m ≤ y'' - 1`, the even-image parts of the good fibers of the members of `A`
in `(U, y'' - 1]` are disjoint odd members of `A` in the shell, of total log-mass at least
`(2/9)(1 - (25/2) U^{-1/3}) (Σ_{m ∈ A ∩ (U, y''-1]} 1/m - 306 U^{-1/3})`: Lemma 4.2 on the
good fibers, Lemma 4.3 for the bad ones. -/
theorem family_OE {A : ℕ → Prop} (hA : BackwardClosed A) {y'' s y : ℕ}
    (hU : 10 ^ 6 ≤ Nat.sqrt y'')
    (hfib : ∀ m, Nat.sqrt y'' < m → m ≤ y'' - 1 → ∀ n ∈ oeFiber m, s < n ∧ n ≤ y) :
    2 / 9 * (1 - 25 / 2 * eps (Nat.sqrt y'')) *
        (∑ m ∈ {m ∈ Ioc (Nat.sqrt y'') (y'' - 1) | A m}, (1 : ℝ) / m
          - 306 * eps (Nat.sqrt y''))
      ≤ ∑ n ∈ {n ∈ Ioc s y | A n ∧ n % 2 = 1}, (1 : ℝ) / n := by
  set U := Nat.sqrt y'' with hU_def
  set G := {m ∈ Ioc U (y'' - 1) | A m ∧ Good m} with hG
  have hU1 : 1 ≤ U := by omega
  have hεU : eps U ≤ 1 / 100 := eps_le hU
  have hεpos : 0 < eps U := eps_pos hU1
  -- the even-image parts of the good fibers sit inside the target set, disjointly
  have hsub : G.biUnion (fun m => {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0})
      ⊆ {n ∈ Ioc s y | A n ∧ n % 2 = 1} := by
    intro n hn
    rw [mem_biUnion] at hn
    obtain ⟨m, hm, hnm⟩ := hn
    rw [hG, mem_filter, mem_Ioc] at hm
    rw [mem_filter] at hnm
    obtain ⟨hnf, heven⟩ := hnm
    have hodd := (mem_oeFiber.mp hnf).1
    obtain ⟨h1, h2⟩ := (mem_oeFiber.mp hnf).2
    rw [mem_filter, mem_Ioc]
    exact ⟨hfib m hm.1.1 hm.1.2 n hnf, oe_fiber_mem hA hm.2.1 hodd heven h1 h2, hodd⟩
  have hdisj : ∀ m ∈ G, ∀ m' ∈ G, m ≠ m' →
      Disjoint {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}
        {n ∈ oeFiber m' | (n ^ 3).sqrt % 2 = 0} := by
    intro m _ m' _ hne
    rw [Finset.disjoint_left]
    intro n hn hn'
    rw [mem_filter] at hn hn'
    exact oe_fiber_disjoint hne (mem_oeFiber.mp hn.1).2.1 (mem_oeFiber.mp hn.1).2.2
      (mem_oeFiber.mp hn'.1).2.1 (mem_oeFiber.mp hn'.1).2.2
  -- the per-fiber bound, summed over the good members
  have hgood : ∑ m ∈ G, 2 / 9 * (1 - 25 / 2 * eps U) / m
      ≤ ∑ n ∈ G.biUnion (fun m => {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}), (1 : ℝ) / n := by
    rw [sum_biUnion hdisj]
    apply sum_le_sum
    intro m hm
    rw [hG, mem_filter, mem_Ioc] at hm
    have hm6 : 10 ^ 6 ≤ m := by omega
    have hmU : U ≤ m := by omega
    calc 2 / 9 * (1 - 25 / 2 * eps U) / m ≤ 2 / 9 * (1 - 25 / 2 * eps m) / m := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have := eps_antitone hU1 hmU
          nlinarith
      _ ≤ _ := good_fiber_logMass_ge hm6 hm.2.2
  -- the good members carry at least the total minus the bad
  have hsplit : ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m}, (1 : ℝ) / m - 306 * eps U
      ≤ ∑ m ∈ G, (1 : ℝ) / m := by
    have hbad := bad_logMass_le (U := U) (N := y'' - 1) hU
    have h1 : ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m}, (1 : ℝ) / m
        = ∑ m ∈ G, (1 : ℝ) / m
          + ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m ∧ ¬ Good m}, (1 : ℝ) / m := by
      rw [← sum_filter_add_sum_filter_not {m ∈ Ioc U (y'' - 1) | A m} (fun m => Good m),
        filter_filter, filter_filter]
    have h2 : ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m ∧ ¬ Good m}, (1 : ℝ) / m ≤ 306 * eps U := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)) hbad
      intro m hm
      rw [mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.2⟩
    linarith
  have hcoef : 0 ≤ 2 / 9 * (1 - 25 / 2 * eps U) := by linarith
  have step1 := mul_le_mul_of_nonneg_left hsplit hcoef
  have step2 : 2 / 9 * (1 - 25 / 2 * eps U) * ∑ m ∈ G, (1 : ℝ) / m
      = ∑ m ∈ G, 2 / 9 * (1 - 25 / 2 * eps U) / m := by
    rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
  have step4 : ∑ n ∈ G.biUnion (fun m => {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}), (1 : ℝ) / n
      ≤ ∑ n ∈ {n ∈ Ioc s y | A n ∧ n % 2 = 1}, (1 : ℝ) / n :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  linarith

/-! ### The two-production inequality -/

/-- The loss on the `E`-family's coefficient, `4e^{-t/4}`. -/
noncomputable def errE (t : ℝ) : ℝ := 4 * Real.exp (-(t / 4))

/-- The loss on the `OE`-family's coefficient, `(50/9)e^{-t/8}`. -/
noncomputable def errOE (t : ℝ) : ℝ := 50 / 9 * Real.exp (-(t / 8))

/-- The additive error, `2e^{-t/2} + (4/9)e^{-3t/4} + 136e^{-t/8}`. -/
noncomputable def errAdd (t : ℝ) : ℝ :=
  2 * Real.exp (-(t / 2)) + 4 / 9 * Real.exp (-(3 * t / 4)) + 136 * Real.exp (-(t / 8))

theorem two_le_exp {u : ℝ} (hu : 1 ≤ u) : 2 ≤ Real.exp u := by
  linarith [Real.add_one_le_exp u]

/-- The reciprocal of a floored exponential is at most twice the reciprocal exponential. -/
theorem one_div_floor_exp_le {u : ℝ} (hu : 1 ≤ u) :
    1 / (⌊Real.exp u⌋₊ : ℝ) ≤ 2 * Real.exp (-u) := by
  have h := floor_exp_ge_half (two_le_exp hu)
  have hpos : 0 < Real.exp u := Real.exp_pos u
  calc 1 / (⌊Real.exp u⌋₊ : ℝ) ≤ 1 / (Real.exp u / 2) := one_div_le_one_div_of_le (by positivity) h
    _ = 2 * Real.exp (-u) := by rw [Real.exp_neg]; field_simp

/-- Dropping the top element of a half-shell costs at most its reciprocal. -/
theorem sum_Ioc_le_sum_Ioc_pred (A : ℕ → Prop) (a : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    ∑ n ∈ {n ∈ Ioc a b | A n}, (1 : ℝ) / n
      ≤ ∑ n ∈ {n ∈ Ioc a (b - 1) | A n}, (1 : ℝ) / n + 1 / b := by
  have hsub : {n ∈ Ioc a b | A n} ⊆ insert b {n ∈ Ioc a (b - 1) | A n} := by
    intro n hn
    rw [mem_filter, mem_Ioc] at hn
    rw [mem_insert, mem_filter, mem_Ioc]
    by_cases h : n = b
    · exact Or.inl h
    · exact Or.inr ⟨⟨hn.1.1, by omega⟩, hn.2⟩
  have hnot : b ∉ {n ∈ Ioc a (b - 1) | A n} := by
    rw [mem_filter, mem_Ioc]
    intro h
    have := h.1.2
    omega
  calc ∑ n ∈ {n ∈ Ioc a b | A n}, (1 : ℝ) / n
      ≤ ∑ n ∈ insert b {n ∈ Ioc a (b - 1) | A n}, (1 : ℝ) / n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 1 / b + ∑ n ∈ {n ∈ Ioc a (b - 1) | A n}, (1 : ℝ) / n := sum_insert hnot
    _ = _ := by ring

/-- The half-shell log-mass splits by parity. -/
theorem halfLogMass_split (A : ℕ → Prop) (y : ℕ) :
    halfLogMass A y = ∑ n ∈ {n ∈ Ioc (Nat.sqrt y) y | A n ∧ n % 2 = 0}, (1 : ℝ) / n
      + ∑ n ∈ {n ∈ Ioc (Nat.sqrt y) y | A n ∧ n % 2 = 1}, (1 : ℝ) / n := by
  rw [halfLogMass,
    ← sum_filter_add_sum_filter_not {n ∈ Ioc (Nat.sqrt y) y | A n} (fun n => n % 2 = 0),
    filter_filter, filter_filter]
  congr 2
  ext n
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩

/-- **The production inequality with two productions.** For `t ≥ 40`,
`(1 - 4e^{-t/4}) g_A(t/2) + (2/9 - (50/9)e^{-t/8}) g_A(3t/4) - errAdd t ≤ g_A(t)`:
family 1 through Lemma 3.1, family 3 through Lemmas 4.2 and 4.3, with every error explicit and
no hypothesis. -/
theorem production_two {A : ℕ → Prop} (hA : BackwardClosed A) {t : ℝ} (ht : 40 ≤ t) :
    (1 - errE t) * gA A (t / 2) + (2 / 9 - errOE t) * gA A (3 * t / 4) - errAdd t ≤ gA A t := by
  obtain ⟨y, hy⟩ : ∃ y : ℕ, ⌊Real.exp t⌋₊ = y := ⟨_, rfl⟩
  obtain ⟨y'', hy''⟩ : ∃ y'' : ℕ, ⌊Real.exp (3 * t / 4)⌋₊ = y'' := ⟨_, rfl⟩
  have hs₁ : Nat.sqrt y = ⌊Real.exp (t / 2)⌋₊ := by rw [← hy]; exact sqrt_floor_exp t
  have hs₂ : Nat.sqrt (Nat.sqrt y) = ⌊Real.exp (t / 4)⌋₊ := by
    rw [hs₁, sqrt_floor_exp, show t / 2 / 2 = t / 4 by ring]
  have hU : Nat.sqrt y'' = ⌊Real.exp (3 * t / 8)⌋₊ := by
    rw [← hy'', sqrt_floor_exp, show 3 * t / 4 / 2 = 3 * t / 8 by ring]
  -- the scales are large
  have hs₂R : Real.exp (t / 4) / 2 ≤ (Nat.sqrt (Nat.sqrt y) : ℝ) := by
    rw [hs₂]; exact floor_exp_ge_half (two_le_exp (by linarith))
  have hs₁R : Real.exp (t / 2) / 2 ≤ (Nat.sqrt y : ℝ) := by
    rw [hs₁]; exact floor_exp_ge_half (two_le_exp (by linarith))
  have hy''R : Real.exp (3 * t / 4) / 2 ≤ (y'' : ℝ) := by
    rw [← hy'']; exact floor_exp_ge_half (two_le_exp (by linarith))
  have hUR : Real.exp (3 * t / 8) / 2 ≤ (Nat.sqrt y'' : ℝ) := by
    rw [hU]; exact floor_exp_ge_half (two_le_exp (by linarith))
  have hs₂1 : 1 ≤ Nat.sqrt (Nat.sqrt y) := by
    have : (1 : ℝ) ≤ Nat.sqrt (Nat.sqrt y) := by
      linarith [two_le_exp (show (1:ℝ) ≤ t / 4 by linarith)]
    exact_mod_cast this
  have hs₁1 : 1 ≤ Nat.sqrt y := by
    have : (1 : ℝ) ≤ Nat.sqrt y := by linarith [two_le_exp (show (1:ℝ) ≤ t / 2 by linarith)]
    exact_mod_cast this
  have hy''1 : 1 ≤ y'' := by
    have : (1 : ℝ) ≤ y'' := by linarith [two_le_exp (show (1:ℝ) ≤ 3 * t / 4 by linarith)]
    exact_mod_cast this
  have hU6 : 10 ^ 6 ≤ Nat.sqrt y'' := by
    have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h15 : (2 * 10 ^ 6 : ℝ) ≤ Real.exp 15 := by
      calc (2 * 10 ^ 6 : ℝ) ≤ (2.7 : ℝ) ^ 15 := by norm_num
        _ ≤ Real.exp 1 ^ 15 := pow_le_pow_left₀ (by norm_num) h27 15
        _ = Real.exp 15 := by rw [Real.exp_one_pow]; norm_num
    have h38 : Real.exp 15 ≤ Real.exp (3 * t / 8) := Real.exp_le_exp.mpr (by linarith)
    have : (10 ^ 6 : ℝ) ≤ (Nat.sqrt y'' : ℝ) := by linarith
    exact_mod_cast this
  have hU0 : (0 : ℝ) < Nat.sqrt y'' := by
    have : (0 : ℝ) < Real.exp (3 * t / 8) / 2 := by positivity
    linarith
  -- the fibers of the `3t/4` scale land in the shell
  have hfib : ∀ m, Nat.sqrt y'' < m → m ≤ y'' - 1 → ∀ n ∈ oeFiber m, Nat.sqrt y < n ∧ n ≤ y := by
    intro m hUm hmy n hn
    have hm1 : m + 1 ≤ y'' := by omega
    have hmR : (m : ℝ) + 1 ≤ Real.exp (3 * t / 4) := by
      have h1 : ((m + 1 : ℕ) : ℝ) ≤ (y'' : ℝ) := by exact_mod_cast hm1
      have h2 : (y'' : ℝ) ≤ Real.exp (3 * t / 4) := by
        rw [← hy'']; exact Nat.floor_le (Real.exp_pos _).le
      push_cast at h1; linarith
    constructor
    · have hm2 : y'' < m ^ 2 := Nat.sqrt_lt'.mp hUm
      have hm2R : Real.exp (3 * t / 4) < (m : ℝ) ^ 2 := by
        have h1 : Real.exp (3 * t / 4) < (y'' : ℝ) + 1 := by
          rw [← hy'']; exact Nat.lt_floor_add_one _
        have h2 : ((y'' + 1 : ℕ) : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) := by exact_mod_cast hm2
        push_cast at h2; linarith
      have hn1 : (m : ℝ) ^ ((4 : ℝ) / 3) ≤ n := fiber_ge_rpow hn
      have h43 : Real.exp (t / 2) < (m : ℝ) ^ ((4 : ℝ) / 3) := by
        have e1 : Real.exp (t / 2) = Real.exp (3 * t / 4) ^ ((2 : ℝ) / 3) := by
          rw [← Real.exp_mul]; ring_nf
        have e2 : (m : ℝ) ^ ((4 : ℝ) / 3) = ((m : ℝ) ^ 2) ^ ((2 : ℝ) / 3) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        rw [e1, e2]
        exact Real.rpow_lt_rpow (Real.exp_pos _).le hm2R (by norm_num)
      have hs₁le : (Nat.sqrt y : ℝ) ≤ Real.exp (t / 2) := by
        rw [hs₁]; exact Nat.floor_le (Real.exp_pos _).le
      have : (Nat.sqrt y : ℝ) < n := by linarith
      exact_mod_cast this
    · have hn2 : (n : ℝ) < ((m : ℝ) + 1) ^ ((4 : ℝ) / 3) := fiber_lt_rpow hn
      have h43 : ((m : ℝ) + 1) ^ ((4 : ℝ) / 3) ≤ Real.exp t := by
        calc ((m : ℝ) + 1) ^ ((4 : ℝ) / 3) ≤ Real.exp (3 * t / 4) ^ ((4 : ℝ) / 3) :=
              Real.rpow_le_rpow (by positivity) hmR (by norm_num)
          _ = Real.exp t := by rw [← Real.exp_mul]; ring_nf
      rw [← hy]
      exact Nat.le_floor (by linarith)
  -- the errors in exponential form
  have hεU : eps (Nat.sqrt y'') ≤ 2 * Real.exp (-(t / 8)) := by
    have hcbrt : Real.exp (t / 8) / 2 ≤ (Nat.sqrt y'' : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [Numerics.le_rpow_iff_pow (n := 3) hU0.le (by positivity) (by norm_num)]
      norm_num
      have e : Real.exp (t / 8) ^ 3 = Real.exp (3 * t / 8) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      calc (Real.exp (t / 8) / 2) ^ 3 = Real.exp (3 * t / 8) / 8 := by rw [div_pow, e]; norm_num
        _ ≤ (Nat.sqrt y'' : ℝ) := by linarith [Real.exp_pos (3 * t / 8)]
    rw [eps, Real.rpow_neg hU0.le]
    calc ((Nat.sqrt y'' : ℝ) ^ ((1 : ℝ) / 3))⁻¹ ≤ (Real.exp (t / 8) / 2)⁻¹ :=
          inv_anti₀ (by positivity) hcbrt
      _ = 2 * Real.exp (-(t / 8)) := by rw [Real.exp_neg]; field_simp
  have h2s₂ : 2 / (Nat.sqrt (Nat.sqrt y) : ℝ) ≤ errE t := by
    unfold errE
    have h := one_div_floor_exp_le (u := t / 4) (by linarith)
    rw [← hs₂] at h
    have e : 2 / (Nat.sqrt (Nat.sqrt y) : ℝ) = 2 * (1 / (Nat.sqrt (Nat.sqrt y) : ℝ)) := by ring
    linarith
  have h1s₁ : 1 / (Nat.sqrt y : ℝ) ≤ 2 * Real.exp (-(t / 2)) := by
    have h := one_div_floor_exp_le (u := t / 2) (by linarith)
    rwa [← hs₁] at h
  have h1y'' : 1 / (y'' : ℝ) ≤ 2 * Real.exp (-(3 * t / 4)) := by
    have h := one_div_floor_exp_le (u := 3 * t / 4) (by linarith)
    rwa [hy''] at h
  -- the two families and the two drops
  have hE := family_E hA (y := y) hs₂1
  have hO := family_OE hA (y'' := y'') (s := Nat.sqrt y) (y := y) hU6 hfib
  have hdrop₁ := sum_Ioc_le_sum_Ioc_pred A (Nat.sqrt (Nat.sqrt y)) hs₁1
  have hdrop₃ := sum_Ioc_le_sum_Ioc_pred A (Nat.sqrt y'') hy''1
  -- the three values of `g_A`
  have hg : gA A t = halfLogMass A y := by rw [gA, hy]
  have hg1 : gA A (t / 2)
      = ∑ m ∈ {m ∈ Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y) | A m}, (1 : ℝ) / m := by
    rw [gA, halfLogMass, ← hs₁]
  have hg3 : gA A (3 * t / 4) = ∑ m ∈ {m ∈ Ioc (Nat.sqrt y'') y'' | A m}, (1 : ℝ) / m := by
    rw [gA, halfLogMass, hy'']
  rw [hg, halfLogMass_split, hg1, hg3]
  -- nonnegativity and the coefficient windows
  have hG1 : 0 ≤ ∑ m ∈ {m ∈ Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y) | A m}, (1 : ℝ) / m :=
    sum_nonneg (fun _ _ => by positivity)
  have hG3 : 0 ≤ ∑ m ∈ {m ∈ Ioc (Nat.sqrt y'') y'' | A m}, (1 : ℝ) / m :=
    sum_nonneg (fun _ _ => by positivity)
  have hS1 : 0 ≤ ∑ m ∈ {m ∈ Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y - 1) | A m}, (1 : ℝ) / m :=
    sum_nonneg (fun _ _ => by positivity)
  have hεpos : 0 ≤ eps (Nat.sqrt y'') := (eps_pos (by omega)).le
  have hεsmall : eps (Nat.sqrt y'') ≤ 1 / 100 := eps_le hU6
  have h2s₂nn : 0 ≤ 2 / (Nat.sqrt (Nat.sqrt y) : ℝ) := by positivity
  have h2s₂le : 2 / (Nat.sqrt (Nat.sqrt y) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Real.add_one_le_exp (t / 4)]
  have hinvs₁ : 0 ≤ 1 / (Nat.sqrt y : ℝ) := by positivity
  have hinvy'' : 0 ≤ 1 / (y'' : ℝ) := by positivity
  -- the products
  have p1 := mul_le_mul_of_nonneg_right (show 1 - errE t ≤ 1 - 2 / (Nat.sqrt (Nat.sqrt y) : ℝ) by
    linarith) hG1
  have p2 := mul_le_mul_of_nonneg_left hdrop₁ (show (0 : ℝ) ≤ 1 - 2 / (Nat.sqrt (Nat.sqrt y) : ℝ) by
    linarith)
  have p3 : (1 - 2 / (Nat.sqrt (Nat.sqrt y) : ℝ)) * (1 / (Nat.sqrt y : ℝ)) ≤ 1 / (Nat.sqrt y : ℝ) :=
    mul_le_of_le_one_left hinvs₁ (by linarith)
  have q1 := mul_le_mul_of_nonneg_right
    (show 2 / 9 - errOE t ≤ 2 / 9 * (1 - 25 / 2 * eps (Nat.sqrt y'')) by unfold errOE; linarith) hG3
  have q2 := mul_le_mul_of_nonneg_left hdrop₃
    (show (0 : ℝ) ≤ 2 / 9 * (1 - 25 / 2 * eps (Nat.sqrt y'')) by linarith)
  have q3 : 2 / 9 * (1 - 25 / 2 * eps (Nat.sqrt y'')) * (1 / (y'' : ℝ) + 306 * eps (Nat.sqrt y''))
      ≤ 2 / 9 * (1 / (y'' : ℝ) + 306 * eps (Nat.sqrt y'')) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  unfold errAdd
  linarith [p1, p2, p3, q1, q2, q3, hE, hO, h1s₁, h1y'', hεU]

/-! ### The recursion on two productions -/

/-- The two productions: `E` at rate `1/2`, `OE` at rate `3/4`. -/
noncomputable def rate2 : Fin 2 → ℝ := ![1 / 2, 3 / 4]

/-- Their coefficients, `1` and `2/9`. -/
noncomputable def coef2 : Fin 2 → ℝ := ![1, 2 / 9]

/-- Their errors, `errE` and `errOE`. -/
noncomputable def err2 : Fin 2 → ℝ → ℝ := ![errE, errOE]

theorem rate2_ge (i : Fin 2) : 1 / 2 ≤ rate2 i := by
  fin_cases i <;> norm_num [rate2]

theorem rate2_le (i : Fin 2) : rate2 i ≤ 3 / 4 := by
  fin_cases i <;> norm_num [rate2]

theorem rate2_pos (i : Fin 2) : 0 < rate2 i := lt_of_lt_of_le (by norm_num) (rate2_ge i)

theorem coef2_ge (i : Fin 2) : 2 / 9 ≤ coef2 i := by
  fin_cases i <;> norm_num [coef2]

theorem err2_nonneg (i : Fin 2) (t : ℝ) : 0 ≤ err2 i t := by
  fin_cases i
  · show 0 ≤ errE t
    unfold errE; positivity
  · show 0 ≤ errOE t
    unfold errOE; positivity

theorem err2_le {t ε : ℝ} (h : errE t ≤ ε ∧ errOE t ≤ ε ∧ errAdd t ≤ ε) (i : Fin 2) :
    err2 i t ≤ ε := by
  fin_cases i
  · simpa [err2] using h.1
  · simpa [err2] using h.2.1

/-- The production inequality in the form the recursion lemma consumes. -/
theorem production_two_sum {A : ℕ → Prop} (hA : BackwardClosed A) {t : ℝ} (ht : 40 ≤ t) :
    ∑ i, (coef2 i - err2 i t) * gA A (rate2 i * t) - errAdd t ≤ gA A t := by
  have h := production_two hA ht
  rw [Fin.sum_univ_two]
  simp only [rate2, coef2, err2, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (1 / 2 : ℝ) * t = t / 2 by ring, show (3 / 4 : ℝ) * t = 3 * t / 4 by ring]
  exact h

/-- `ζ(3/10) = 2^{-3/10} + (2/9)(3/4)^{3/10} - 1 > 0`, by two rational bounds:
`0.81 ≤ (1/2)^{3/10}` since `0.81^{10} ≤ 1/8`, and `0.91 ≤ (3/4)^{3/10}` since
`0.91^{10} ≤ 27/64`; then `0.81 + (2/9)(0.91) > 1`. -/
theorem zeta2_pos : 0 < ∑ i, coef2 i * rate2 i ^ ((3 : ℝ) / 10) - 1 := by
  rw [Fin.sum_univ_two]
  simp only [rate2, coef2, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : (81 / 100 : ℝ) ≤ (1 / 2 : ℝ) ^ ((3 : ℝ) / 10) := by
    rw [Numerics.le_rpow_iff_pow (n := 10) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have h2 : (91 / 100 : ℝ) ≤ (3 / 4 : ℝ) ^ ((3 : ℝ) / 10) := by
    rw [Numerics.le_rpow_iff_pow (n := 10) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- `ζ` is antitone in `λ`: both rates lie below `1`. -/
theorem zeta2_antitone {lam lam' : ℝ} (h : lam ≤ lam') :
    ∑ i, coef2 i * rate2 i ^ lam' - 1 ≤ ∑ i, coef2 i * rate2 i ^ lam - 1 := by
  have hi : ∀ i, coef2 i * rate2 i ^ lam' ≤ coef2 i * rate2 i ^ lam := by
    intro i
    apply mul_le_mul_of_nonneg_left _ (by linarith [coef2_ge i])
    exact Real.rpow_le_rpow_of_exponent_ge (rate2_pos i) (by linarith [rate2_le i]) h
  have hsum : ∑ i, coef2 i * rate2 i ^ lam' ≤ ∑ i, coef2 i * rate2 i ^ lam :=
    sum_le_sum (fun i _ => hi i)
  linarith

/-- Every error is at most `139 e^{-t/8}` for `t ≥ 0`. -/
theorem errors_le {t : ℝ} (ht : 0 ≤ t) :
    errE t ≤ 139 * Real.exp (-(t / 8)) ∧ errOE t ≤ 139 * Real.exp (-(t / 8)) ∧
      errAdd t ≤ 139 * Real.exp (-(t / 8)) := by
  have h8 : 0 < Real.exp (-(t / 8)) := Real.exp_pos _
  have h4 : Real.exp (-(t / 4)) ≤ Real.exp (-(t / 8)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(t / 2)) ≤ Real.exp (-(t / 8)) := Real.exp_le_exp.mpr (by linarith)
  have h34 : Real.exp (-(3 * t / 4)) ≤ Real.exp (-(t / 8)) := Real.exp_le_exp.mpr (by linarith)
  unfold errE errOE errAdd
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The errors vanish: past `T = max 0 (8 log(139/ε))` all three are at most `ε`. -/
theorem errors_vanish {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → errE t ≤ ε ∧ errOE t ≤ ε ∧ errAdd t ≤ ε := by
  refine ⟨max 0 (8 * Real.log (139 / ε)), le_max_left _ _, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans (le_max_left _ _) ht
  have hlog : 8 * Real.log (139 / ε) ≤ t := le_trans (le_max_right _ _) ht
  have hexp : Real.exp (-(t / 8)) ≤ ε / 139 := by
    have h : Real.exp (-(t / 8)) ≤ Real.exp (-Real.log (139 / ε)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg (Real.log (139 / ε)), Real.exp_log (by positivity), inv_div] at h
    exact h
  obtain ⟨h1, h2, h3⟩ := errors_le ht0
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **Elementary contagion.** For every nonempty backward-closed `A` and `0 < λ ≤ 3/10` there
are `K > 0` and `t₁` with `g_A(t) ≥ K t^λ` for all `t ≥ t₁`. No hypothesis: the seed is
Lemma 5.2, the recursion is Lemma 5.1 on the two productions `E` and `OE`, and the production
inequality is `production_two`, whose inputs are Lemmas 3.1, 4.2 and 4.3. -/
theorem contagion_elementary {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ} (ha : 1 ≤ a)
    (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 3 / 10) :
    ∃ K : ℝ, 0 < K ∧ ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t, t₁ ≤ t → K * t ^ lam ≤ gA A t := by
  obtain ⟨m, hm, hmA⟩ := exists_ge_three_of_backwardClosed hA ha hAa
  have hc₀ : 0 < seedConst m := seed_constant_pos hm
  have hζ : 0 < ∑ i, coef2 i * rate2 i ^ lam - 1 :=
    lt_of_lt_of_le zeta2_pos (zeta2_antitone hlam)
  -- the error budget
  obtain ⟨ε, hε, hε1, hε2, hε3⟩ : ∃ ε : ℝ, 0 < ε ∧
      ε ≤ (∑ i, coef2 i * rate2 i ^ lam - 1) / 6 ∧
      ε ≤ 2 * (∑ i, coef2 i * rate2 i ^ lam - 1) / 3 * seedConst m ∧ ε ≤ 2 / 9 :=
    ⟨min ((∑ i, coef2 i * rate2 i ^ lam - 1) / 6)
      (min (2 * (∑ i, coef2 i * rate2 i ^ lam - 1) / 3 * seedConst m) (2 / 9)),
      lt_min (by positivity) (lt_min (by positivity) (by norm_num)), min_le_left _ _,
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  obtain ⟨T, _, hT⟩ := errors_vanish hε
  -- the scale `t₁`
  obtain ⟨t₁, ht₁T, ht₁40, ht₁seed⟩ :
      ∃ t₁ : ℝ, T ≤ t₁ ∧ 40 ≤ t₁ ∧ 8 * Real.log ((m : ℝ) + 1) ≤ t₁ :=
    ⟨max T (max 40 (8 * Real.log ((m : ℝ) + 1))), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have ht₁pos : 0 < t₁ := by linarith
  have hrate_le_one : ∀ i, rate2 i ^ lam ≤ 1 := fun i =>
    Real.rpow_le_one (rate2_pos i).le (by linarith [rate2_le i]) hlam0.le
  have hmain := recursion_lemma rate2 coef2 err2 errAdd (gA A) lam t₁ (seedConst m)
    (1 / 2) (3 / 4) hlam0 ht₁pos hc₀ (by norm_num) (by norm_num) rate2_ge rate2_le hζ
    (fun t _ i => err2_nonneg i t)
    (fun t ht i => le_trans (err2_le (hT t (le_trans ht₁T ht)) i)
      (le_trans hε3 (coef2_ge i)))
    (fun t ht => le_trans (hT t (le_trans ht₁T ht)).2.2 hε2)
    (fun t ht => by
      have hi : ∀ i, err2 i t * rate2 i ^ lam ≤ ε := by
        intro i
        calc err2 i t * rate2 i ^ lam ≤ ε * 1 :=
              mul_le_mul (err2_le (hT t (le_trans ht₁T ht)) i) (hrate_le_one i)
                (Real.rpow_nonneg (rate2_pos i).le _) hε.le
          _ = ε := mul_one ε
      calc ∑ i, err2 i t * rate2 i ^ lam ≤ ∑ _i : Fin 2, ε := sum_le_sum (fun i _ => hi i)
        _ = 2 * ε := by simp
        _ ≤ (∑ i, coef2 i * rate2 i ^ lam - 1) / 3 := by linarith)
    (fun t ht _ => gA_seed hA hm hmA (by linarith))
    (fun t ht => production_two_sum hA (by linarith))
  refine ⟨seedConst m * t₁ ^ (-lam), by positivity, t₁, ht₁pos, ?_⟩
  intro t ht
  exact hmain t (by linarith)

/-- **Elementary contagion, as a log-mass bound.** For every nonempty backward-closed `A` and
`0 < λ ≤ 3/10` there are `K > 0` and `x₀` with `Σ_{n ∈ A, n ≤ x} 1/n ≥ K (log x)^λ` for all
`x ≥ x₀`. This is Theorem 5.3 of the paper with `3/10` in place of `λ** ≈ 0.4926`, and with
no hypothesis: the block-average family and the ladder, which need the exponential sums, are
what lift the exponent. -/
theorem logMass_contagion_elementary {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 3 / 10) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → K * Real.log x ^ lam ≤ logMass A x := by
  obtain ⟨K, hK, t₁, ht₁, h⟩ := contagion_elementary hA ha hAa hlam0 hlam
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

/-- **Corollary 5.5(2) at exponent `3/10`, unconditional.** If some positive integer does not
reach `1`, the failures have log-mass at least `K (log x)^{3/10}` up to `x` for all large `x`:
the failure set is backward-closed (Lemma 2.1) and nonempty. -/
theorem failures_logMass_ge {a : ℕ} (ha : 1 ≤ a) (hfail : ¬ReachesOne a) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 3 / 10) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x :=
  logMass_contagion_elementary not_reachesOne_backwardClosed ha hfail hlam0 hlam

/-! ### The conjecture from a rate, with no other hypothesis -/

/-- **Theorem 7.2 with its contagion hypothesis discharged.** If the odd failures in `(y, 2y]`
number at most `y (log y)^{-e}` for all large `y`, for some `e > 7/10`, then every positive
integer reaches `1`. The contagion bound at exponent `3/10` is `failures_logMass_ge`, so
nothing is assumed beyond the rate; the paper's conditional form needs `e > 0.51` and the
production inequality (5.2). -/
theorem conjecture_of_tao_rate {e : ℝ} (he : 7 / 10 < e)
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  tao_rate_implies_conjecture (lam := 3 / 10) (by norm_num) (by norm_num) (by linarith)
    (fun ⟨a, ha, hfail⟩ => failures_logMass_ge ha hfail (by norm_num) le_rfl) htao

/-- **Corollary 8.4 with its contagion hypothesis discharged.** A cylinder bound `H(C, A)` at
all large scales with `A > C + e(C)` and `e(C) > 7/10`, above a certified floor `N₀`, gives
the conjecture; nothing else is assumed. -/
theorem conjecture_of_cylinder_bound {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C A : ℝ) (hC : 5 ≤ C)
    (hA : C + chernoffExponent C < A)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ C A y)
    (he : 7 / 10 < chernoffExponent C) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  cylinder_bound_implies_conjecture hN hfloor C A hC hA hcyl (lam := 3 / 10) (by norm_num)
    (by norm_num) (by linarith)
    (fun ⟨a, ha, hfail⟩ => failures_logMass_ge ha hfail (by norm_num) le_rfl)

end Production

end Problems.Juggler
