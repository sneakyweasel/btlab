import Problems.Juggler.FatePoorTail
import Problems.Juggler.FateContagion
import Problems.Juggler.FateProduction

namespace Problems.Juggler

open Finset
open scoped Classical
open FiberParity

namespace Production

/-!
# The `OE` family at the averaged coefficient

`docs/theory/juggler_oe_poor_fiber_tail_note.md`, §5: the poor-fiber tail replaces the
pointwise `2/9` of Paper C's Family 3 by `(2/3)(1/2 - η₀)`, which is the note's `c`.

This is `FateProduction.family_OE` with two inputs swapped and nothing else changed:

* the per-fiber bound is `nonpoor_fiber_logMass_ge` in place of `good_fiber_logMass_ge`,
  so the hypothesis on a fiber is `¬ Poor η₀ m` rather than `Good m`;
* the exceptional set is bounded by `poor_logMass_le` in place of `bad_logMass_le`, so the
  subtracted mass is `2100 ε_U/η₀²` rather than `306 ε_U`.

Everything structural is the original's: the even-image parts of the accepted fibers are
disjoint (`oe_fiber_disjoint`), they are odd members of `A` in the shell
(`oe_fiber_mem`, backward closure), and the accepted members carry the range's mass minus
the exceptional set's.

`FateProduction` itself is not touched. It is a Paper C input, and the `2/9` chain it
carries remains exactly as the manuscript cites it; this is a parallel statement at a
different coefficient, valid on a different range of `m`. Both are true, and they are not
the same theorem: the `2/9` chain holds for every `m ≥ 10^6`, while this one needs the
block hypotheses of Lemma 2, which bite only past `u₀(η₀)`.

Not a halt theorem. What this file does NOT do is run the recursion: turning the family
bound into an exponent needs `production_two`, `zeta`, `recursion_lemma` and the seed, all
of which are stated in `FateProduction` and `FateContagionBound` against the literal `2/9`
and `13/40`. Those would have to be restated at the new coefficient, which is arithmetic
over this file rather than mathematics.
-/

/-- **Family 3 at the averaged coefficient.** For `U = ⌊√y''⌋ ≥ 10^6` satisfying Lemma 2's
block hypotheses, and any shell `(s, y]` containing every fiber `Φ(m)` with
`U < m ≤ y'' - 1`, the even-image parts of the non-poor fibers of the members of `A` in
`(U, y'' - 1]` are disjoint odd members of `A` in the shell, of total log-mass at least
`(c - ε_U)(Σ_{m ∈ A ∩ (U, y''-1]} 1/m - 2100 ε_U/η₀²)` with `c = (2/3)(1/2 - η₀)`. -/
theorem family_OE_averaged {A : ℕ → Prop} (hA : BackwardClosed A) {y'' s y : ℕ}
    (hU : 10 ^ 6 ≤ Nat.sqrt y'') {η₀ : ℝ} (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 4)
    (hB : 1280 / η₀ ^ 2 ≤ 2 / 3 * ((Nat.sqrt y'' : ℕ) : ℝ) ^ ((1 : ℝ) / 3) - 1)
    (hδ2 : 32 / (η₀ * (2 / 3 * ((Nat.sqrt y'' : ℕ) : ℝ) ^ ((1 : ℝ) / 3) - 1)) < 1 / 2)
    (hfib : ∀ m, Nat.sqrt y'' < m → m ≤ y'' - 1 → ∀ n ∈ oeFiber m, s < n ∧ n ≤ y) :
    (2 / 3 * (1 / 2 - η₀) - eps (Nat.sqrt y'')) *
        (∑ m ∈ {m ∈ Ioc (Nat.sqrt y'') (y'' - 1) | A m}, (1 : ℝ) / m
          - 2100 * eps (Nat.sqrt y'') / η₀ ^ 2)
      ≤ ∑ n ∈ {n ∈ Ioc s y | A n ∧ n % 2 = 1}, (1 : ℝ) / n := by
  set U := Nat.sqrt y'' with hU_def
  set c : ℝ := 2 / 3 * (1 / 2 - η₀) with hc
  set G := {m ∈ Ioc U (y'' - 1) | A m ∧ ¬ Poor η₀ m} with hG
  have hU1 : 1 ≤ U := by omega
  have hεU : eps U ≤ 1 / 100 := eps_le hU
  have hεpos : 0 < eps U := eps_pos hU1
  -- the even-image parts sit inside the target set, disjointly
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
  -- the per-fiber bound, summed over the accepted members
  have hgood : ∑ m ∈ G, (c - eps U) / m
      ≤ ∑ n ∈ G.biUnion (fun m => {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}), (1 : ℝ) / n := by
    rw [sum_biUnion hdisj]
    apply sum_le_sum
    intro m hm
    rw [hG, mem_filter, mem_Ioc] at hm
    have hm6 : 10 ^ 6 ≤ m := by omega
    have hmU : U ≤ m := by omega
    calc (c - eps U) / m ≤ (c - eps m) / m := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have := eps_antitone hU1 hmU
          linarith
      _ ≤ _ := nonpoor_fiber_logMass_ge hm6 hη0 (by linarith) hm.2.2
  -- the accepted members carry the range's mass minus the poor set's
  have hsplit : ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m}, (1 : ℝ) / m - 2100 * eps U / η₀ ^ 2
      ≤ ∑ m ∈ G, (1 : ℝ) / m := by
    have hpoor := poor_logMass_le (U := U) (N := y'' - 1) hU hη0 (by linarith) hB hδ2
    have h1 : ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m}, (1 : ℝ) / m
        = ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m ∧ Poor η₀ m}, (1 : ℝ) / m
          + ∑ m ∈ G, (1 : ℝ) / m := by
      rw [← sum_filter_add_sum_filter_not {m ∈ Ioc U (y'' - 1) | A m}
        (fun m => Poor η₀ m), filter_filter, filter_filter]
    have h2 : ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m ∧ Poor η₀ m}, (1 : ℝ) / m
        ≤ 2100 * eps U / η₀ ^ 2 := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)) hpoor
      intro m hm
      rw [mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.2⟩
    linarith
  -- `η₀ ≤ 1/4` puts `c ≥ 1/6`, and `ε_U ≤ 1/100`
  have hcoef : 0 ≤ c - eps U := by rw [hc]; linarith
  have step1 := mul_le_mul_of_nonneg_left hsplit hcoef
  have step2 : (c - eps U) * ∑ m ∈ G, (1 : ℝ) / m = ∑ m ∈ G, (c - eps U) / m := by
    rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
  have step4 : ∑ n ∈ G.biUnion (fun m => {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}), (1 : ℝ) / n
      ≤ ∑ n ∈ {n ∈ Ioc s y | A n ∧ n % 2 = 1}, (1 : ℝ) / n :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  linarith

/-! ### The production inequality at the averaged coefficient -/

/-- The `OE` coefficient's error at the averaged constant. The coefficient `(2/3)(1/2 - η₀)` is
exact, so the only loss is the fibre's own `ε_U ≤ 2e^{-t/8}` on the `3t/4` scale. Compare
`errOE`, which carries `25/2` times the same `ε_U` because Paper C's pointwise Lemma 4.2 has to
pay for goodness at every `m`. -/
noncomputable def errOEavg (t : ℝ) : ℝ := 2 * Real.exp (-(t / 8))

/-- The additive error at the averaged coefficient. The first two terms are the boundary terms
of the two drops, as in `errAdd`. The third is the poor-fibre tail `2100 ε_U/η₀²` carried
through a coefficient of at most `1/3`; it is the only place `η₀` enters an error, and it is why
the recursion's starting scale grows like `16 log(1/η₀)`. -/
noncomputable def errAddAvg (η₀ t : ℝ) : ℝ :=
  2 * Real.exp (-(t / 2)) + 2 / 3 * Real.exp (-(3 * t / 4))
    + 1400 * Real.exp (-(t / 8)) / η₀ ^ 2

/-- **The production inequality with two productions, at the averaged coefficient.** For
`0 < η₀ ≤ 1/4`, `t ≥ 40` and `t` past the scale where Lemma 2's block hypotheses bite,

`(1 - errE t) g_A(t/2) + ((2/3)(1/2 - η₀) - errOEavg t) g_A(3t/4) - errAddAvg η₀ t ≤ g_A(t)`.

Family 1 is Paper C's Lemma 3.1 unchanged; family 3 is `family_OE_averaged`, so the `2/9` of
`production_two` is replaced by `(2/3)(1/2 - η₀)`, which exceeds `1/3 - 10^{-4}`. The shell
geometry -- the three scales `t/2`, `3t/4`, `t`, the fibres landing in the shell, the two
boundary drops -- is `production_two`'s, step for step.

`hT` is the one new hypothesis, and it is exactly Lemma 2's two block conditions rewritten at
`U = ⌊e^{3t/8}⌋`: `3(1280/η₀² + 1) ≤ e^{t/8}` gives `1280/η₀² ≤ (2/3)U^{1/3} - 1`, and that in
turn gives `32/(η₀((2/3)U^{1/3} - 1)) ≤ 32/5120 < 1/2`. It is the whole cost of the averaging:
it forces `t ≳ 16 log(1/η₀)`, and nothing else in the statement depends on `η₀`. -/
theorem production_two_averaged {A : ℕ → Prop} (hA : BackwardClosed A) {η₀ t : ℝ}
    (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 4) (ht : 40 ≤ t)
    (hT : 3 * (1280 / η₀ ^ 2 + 1) ≤ Real.exp (t / 8)) :
    (1 - errE t) * gA A (t / 2)
        + (2 / 3 * (1 / 2 - η₀) - errOEavg t) * gA A (3 * t / 4)
      - errAddAvg η₀ t ≤ gA A t := by
  have hne : η₀ ≠ 0 := ne_of_gt hη0
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
  -- the cube root of the `3t/4` scale, and the errors in exponential form
  have hcbrt : Real.exp (t / 8) / 2 ≤ (Nat.sqrt y'' : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Numerics.le_rpow_iff_pow (n := 3) hU0.le (by positivity) (by norm_num)]
    norm_num
    have e : Real.exp (t / 8) ^ 3 = Real.exp (3 * t / 8) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc (Real.exp (t / 8) / 2) ^ 3 = Real.exp (3 * t / 8) / 8 := by rw [div_pow, e]; norm_num
      _ ≤ (Nat.sqrt y'' : ℝ) := by linarith [Real.exp_pos (3 * t / 8)]
  have hεU : eps (Nat.sqrt y'') ≤ 2 * Real.exp (-(t / 8)) := by
    rw [eps, Real.rpow_neg hU0.le]
    calc ((Nat.sqrt y'' : ℝ) ^ ((1 : ℝ) / 3))⁻¹ ≤ (Real.exp (t / 8) / 2)⁻¹ :=
          inv_anti₀ (by positivity) hcbrt
      _ = 2 * Real.exp (-(t / 8)) := by rw [Real.exp_neg]; field_simp
  -- Lemma 2's two block hypotheses, from `hT`
  have hB : 1280 / η₀ ^ 2 ≤ 2 / 3 * ((Nat.sqrt y'' : ℕ) : ℝ) ^ ((1 : ℝ) / 3) - 1 := by
    linarith [hcbrt, hT]
  have hδ2 : 32 / (η₀ * (2 / 3 * ((Nat.sqrt y'' : ℕ) : ℝ) ^ ((1 : ℝ) / 3) - 1)) < 1 / 2 := by
    have hid : η₀ * (1280 / η₀ ^ 2) = 1280 / η₀ := by field_simp
    have h5120 : (5120 : ℝ) ≤ 1280 / η₀ := by rw [le_div_iff₀ hη0]; linarith
    have hden : (64 : ℝ) < η₀ * (2 / 3 * ((Nat.sqrt y'' : ℕ) : ℝ) ^ ((1 : ℝ) / 3) - 1) := by
      have h := mul_le_mul_of_nonneg_left hB hη0.le
      rw [hid] at h
      linarith
    rw [div_lt_iff₀ (by linarith)]
    linarith
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
  have hO := family_OE_averaged hA (y'' := y'') (s := Nat.sqrt y) (y := y) hU6 hη0 hη1 hB hδ2 hfib
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
  -- the `E` products, verbatim from `production_two`
  have p1 := mul_le_mul_of_nonneg_right (show 1 - errE t ≤ 1 - 2 / (Nat.sqrt (Nat.sqrt y) : ℝ) by
    linarith) hG1
  have p2 := mul_le_mul_of_nonneg_left hdrop₁ (show (0 : ℝ) ≤ 1 - 2 / (Nat.sqrt (Nat.sqrt y) : ℝ) by
    linarith)
  have p3 : (1 - 2 / (Nat.sqrt (Nat.sqrt y) : ℝ)) * (1 / (Nat.sqrt y : ℝ)) ≤ 1 / (Nat.sqrt y : ℝ) :=
    mul_le_of_le_one_left hinvs₁ (by linarith)
  -- the `OE` products, at the averaged coefficient `K` with exceptional mass `M`
  set K : ℝ := 2 / 3 * (1 / 2 - η₀) - eps (Nat.sqrt y'') with hKdef
  set M : ℝ := 2100 * eps (Nat.sqrt y'') / η₀ ^ 2 with hMdef
  clear_value K M
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith
  have hKle : K ≤ 1 / 3 := by rw [hKdef]; linarith
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  -- stated already divided by three: `linarith` reads `c * e / η₀ ^ 2` as an opaque atom, so
  -- the bound has to carry the very constant the goal carries
  have hMle : (1 : ℝ) / 3 * M ≤ 1400 * Real.exp (-(t / 8)) / η₀ ^ 2 := by
    have h : (700 : ℝ) * eps (Nat.sqrt y'') ≤ 1400 * Real.exp (-(t / 8)) := by linarith
    calc (1 : ℝ) / 3 * M = 700 * eps (Nat.sqrt y'') / η₀ ^ 2 := by rw [hMdef]; ring
      _ ≤ 1400 * Real.exp (-(t / 8)) / η₀ ^ 2 := div_le_div_of_nonneg_right h (by positivity)
  have q1 := mul_le_mul_of_nonneg_right
    (show 2 / 3 * (1 / 2 - η₀) - errOEavg t ≤ K by rw [hKdef]; unfold errOEavg; linarith) hG3
  have q2 := mul_le_mul_of_nonneg_left hdrop₃ hKnn
  have q3 : K * (∑ n ∈ {n ∈ Ioc (Nat.sqrt y'') (y'' - 1) | A n}, (1 : ℝ) / n + 1 / (y'' : ℝ))
      = K * (∑ n ∈ {n ∈ Ioc (Nat.sqrt y'') (y'' - 1) | A n}, (1 : ℝ) / n - M)
        + K * (M + 1 / (y'' : ℝ)) := by ring
  have q4 : K * (M + 1 / (y'' : ℝ)) ≤ 1 / 3 * (M + 1 / (y'' : ℝ)) :=
    mul_le_mul_of_nonneg_right hKle (by linarith)
  have hEside : (1 - errE t) *
        ∑ m ∈ {m ∈ Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y) | A m}, (1 : ℝ) / m
      ≤ (∑ n ∈ {n ∈ Ioc (Nat.sqrt y) y | A n ∧ n % 2 = 0}, (1 : ℝ) / n)
        + 2 * Real.exp (-(t / 2)) := by
    linarith only [p1, p2, p3, hE, h1s₁]
  have hOstep : K * (∑ n ∈ {n ∈ Ioc (Nat.sqrt y'') (y'' - 1) | A n}, (1 : ℝ) / n - M)
        + K * (M + 1 / (y'' : ℝ))
      ≤ (∑ n ∈ {n ∈ Ioc (Nat.sqrt y) y | A n ∧ n % 2 = 1}, (1 : ℝ) / n)
        + 2 / 3 * Real.exp (-(3 * t / 4)) + 1400 * Real.exp (-(t / 8)) / η₀ ^ 2 := by
    linarith only [hO, q4, hMle, h1y'']
  have hOside := q1.trans (q2.trans (q3.le.trans hOstep))
  unfold errAddAvg
  linarith only [hEside, hOside]

end Production

end Problems.Juggler
