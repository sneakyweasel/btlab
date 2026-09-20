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

/-! ### The recursion at the averaged coefficient

Everything below is `FateProduction`'s recursion section with `2/9` replaced by
`(2/3)(1/2 - η₀)`. `recursion_lemma` itself is already generic in the coefficients, the rates
and the errors, so nothing about Lemma 5.1 is restated -- only its inputs change. -/

/-- The two coefficients at the averaged constant: `1` for `E`, `(2/3)(1/2 - η₀)` for `OE`. -/
noncomputable def coef2avg (η₀ : ℝ) : Fin 2 → ℝ := ![1, 2 / 3 * (1 / 2 - η₀)]

/-- Their errors, `errE` and `errOEavg`. -/
noncomputable def err2avg : Fin 2 → ℝ → ℝ := ![errE, errOEavg]

theorem coef2avg_ge {η₀ : ℝ} (hη1 : η₀ ≤ 1 / 4) (i : Fin 2) : 1 / 6 ≤ coef2avg η₀ i := by
  fin_cases i
  · show (1 : ℝ) / 6 ≤ 1
    norm_num
  · show (1 : ℝ) / 6 ≤ 2 / 3 * (1 / 2 - η₀)
    linarith

theorem coef2avg_nonneg {η₀ : ℝ} (hη1 : η₀ ≤ 1 / 4) (i : Fin 2) : 0 ≤ coef2avg η₀ i :=
  le_trans (by norm_num) (coef2avg_ge hη1 i)

theorem err2avg_nonneg (i : Fin 2) (t : ℝ) : 0 ≤ err2avg i t := by
  fin_cases i
  · show 0 ≤ errE t
    unfold errE; positivity
  · show 0 ≤ errOEavg t
    unfold errOEavg; positivity

theorem err2avg_le {η₀ t ε : ℝ}
    (h : errE t ≤ ε ∧ errOEavg t ≤ ε ∧ errAddAvg η₀ t ≤ ε) (i : Fin 2) : err2avg i t ≤ ε := by
  fin_cases i
  · simpa [err2avg] using h.1
  · simpa [err2avg] using h.2.1

/-- The production inequality in the form the recursion lemma consumes. -/
theorem production_two_averaged_sum {A : ℕ → Prop} (hA : BackwardClosed A) {η₀ t : ℝ}
    (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 4) (ht : 40 ≤ t)
    (hT : 3 * (1280 / η₀ ^ 2 + 1) ≤ Real.exp (t / 8)) :
    ∑ i, (coef2avg η₀ i - err2avg i t) * gA A (rate2 i * t) - errAddAvg η₀ t ≤ gA A t := by
  have h := production_two_averaged hA hη0 hη1 ht hT
  rw [Fin.sum_univ_two]
  simp only [rate2, coef2avg, err2avg, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (1 / 2 : ℝ) * t = t / 2 by ring, show (3 / 4 : ℝ) * t = 3 * t / 4 by ring]
  exact h

/-- Every error at the averaged coefficient is at most `(4 + 1400/η₀²) e^{-t/8}` for `t ≥ 0`.
The `1/η₀²` is the poor-fibre tail and nothing else; `errE` and `errOEavg` do not see `η₀`. -/
theorem errorsAvg_le {η₀ t : ℝ} (hη0 : 0 < η₀) (ht : 0 ≤ t) :
    errE t ≤ (4 + 1400 / η₀ ^ 2) * Real.exp (-(t / 8)) ∧
      errOEavg t ≤ (4 + 1400 / η₀ ^ 2) * Real.exp (-(t / 8)) ∧
      errAddAvg η₀ t ≤ (4 + 1400 / η₀ ^ 2) * Real.exp (-(t / 8)) := by
  have h8 : 0 < Real.exp (-(t / 8)) := Real.exp_pos _
  have h4 : Real.exp (-(t / 4)) ≤ Real.exp (-(t / 8)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(t / 2)) ≤ Real.exp (-(t / 8)) := Real.exp_le_exp.mpr (by linarith)
  have h34 : Real.exp (-(3 * t / 4)) ≤ Real.exp (-(t / 8)) := Real.exp_le_exp.mpr (by linarith)
  have hqe : 0 ≤ 1400 / η₀ ^ 2 * Real.exp (-(t / 8)) := by positivity
  have hid : 1400 * Real.exp (-(t / 8)) / η₀ ^ 2 = 1400 / η₀ ^ 2 * Real.exp (-(t / 8)) := by
    ring
  unfold errE errOEavg errAddAvg
  rw [hid]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The errors vanish: past `T = max 0 (8 log((4 + 1400/η₀²)/ε))` all three are at most `ε`. -/
theorem errorsAvg_vanish {η₀ ε : ℝ} (hη0 : 0 < η₀) (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t →
      errE t ≤ ε ∧ errOEavg t ≤ ε ∧ errAddAvg η₀ t ≤ ε := by
  have hC : (0 : ℝ) < 4 + 1400 / η₀ ^ 2 := by positivity
  refine ⟨max 0 (8 * Real.log ((4 + 1400 / η₀ ^ 2) / ε)), le_max_left _ _, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans (le_max_left _ _) ht
  have hlog : 8 * Real.log ((4 + 1400 / η₀ ^ 2) / ε) ≤ t := le_trans (le_max_right _ _) ht
  have hexp : (4 + 1400 / η₀ ^ 2) * Real.exp (-(t / 8)) ≤ ε := by
    have h : Real.exp (-(t / 8)) ≤ Real.exp (-Real.log ((4 + 1400 / η₀ ^ 2) / ε)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg (Real.log ((4 + 1400 / η₀ ^ 2) / ε)), Real.exp_log (by positivity),
      inv_div] at h
    calc (4 + 1400 / η₀ ^ 2) * Real.exp (-(t / 8))
        ≤ (4 + 1400 / η₀ ^ 2) * (ε / (4 + 1400 / η₀ ^ 2)) := mul_le_mul_of_nonneg_left h hC.le
      _ = ε := by field_simp
  obtain ⟨h1, h2, h3⟩ := errorsAvg_le hη0 ht0
  exact ⟨by linarith, by linarith, by linarith⟩

/-- `ζ` is antitone in `λ` at the averaged coefficient too: both rates lie below `1`. -/
theorem zeta2avg_antitone {η₀ : ℝ} (hη1 : η₀ ≤ 1 / 4) {lam lam' : ℝ} (h : lam ≤ lam') :
    ∑ i, coef2avg η₀ i * rate2 i ^ lam' - 1 ≤ ∑ i, coef2avg η₀ i * rate2 i ^ lam - 1 := by
  have hi : ∀ i, coef2avg η₀ i * rate2 i ^ lam' ≤ coef2avg η₀ i * rate2 i ^ lam := by
    intro i
    apply mul_le_mul_of_nonneg_left _ (coef2avg_nonneg hη1 i)
    exact Real.rpow_le_rpow_of_exponent_ge (rate2_pos i) (by linarith [rate2_le i]) h
  have hsum : ∑ i, coef2avg η₀ i * rate2 i ^ lam' ≤ ∑ i, coef2avg η₀ i * rate2 i ^ lam :=
    sum_le_sum (fun i _ => hi i)
  linarith

/-- **Contagion at the averaged coefficient.** For every nonempty backward-closed `A`, every
`0 < η₀ ≤ 1/4` and every `λ > 0` with `ζ(λ, η₀) = 2^{-λ} + (2/3)(1/2 - η₀)(3/4)^λ - 1 > 0`,
there are `K > 0` and `t₁` with `g_A(t) ≥ K t^λ` for all `t ≥ t₁`.

This is the statement the note actually proves, and it is the one worth reading: the exponent
is not a constant of the argument but whatever `ζ` allows, so the supremum over `η₀ → 0` is the
root of `2^{-λ} + (1/3)(3/4)^λ = 1`, `λ_ideal = 0.49265798…`. The supremum is approached and not
attained, `η₀` being fixed before `x` -- exactly as Paper C's published statement is.

The cost of a small `η₀` is entirely in `t₁`, which absorbs `8 log(3(1280/η₀² + 1))`: at the
`η₀` that beats Paper C's `λ** = 0.4925715…` the starting scale is around `250`, so the implied
`K` is tiny. Nothing else degrades. -/
theorem contagion_averaged {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ} (ha : 1 ≤ a)
    (hAa : A a) {η₀ lam : ℝ} (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 4) (hlam0 : 0 < lam)
    (hζ : 0 < ∑ i, coef2avg η₀ i * rate2 i ^ lam - 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t, t₁ ≤ t → K * t ^ lam ≤ gA A t := by
  obtain ⟨m, hm, hmA⟩ := exists_ge_three_of_backwardClosed hA ha hAa
  have hc₀ : 0 < seedConst m := seed_constant_pos hm
  obtain ⟨ε, hε, hε1, hε2, hε3⟩ : ∃ ε : ℝ, 0 < ε ∧
      ε ≤ (∑ i, coef2avg η₀ i * rate2 i ^ lam - 1) / 6 ∧
      ε ≤ 2 * (∑ i, coef2avg η₀ i * rate2 i ^ lam - 1) / 3 * seedConst m ∧ ε ≤ 1 / 6 :=
    ⟨min ((∑ i, coef2avg η₀ i * rate2 i ^ lam - 1) / 6)
      (min (2 * (∑ i, coef2avg η₀ i * rate2 i ^ lam - 1) / 3 * seedConst m) (1 / 6)),
      lt_min (by positivity) (lt_min (by positivity) (by norm_num)), min_le_left _ _,
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  obtain ⟨T, _, hTerr⟩ := errorsAvg_vanish hη0 hε
  obtain ⟨t₁, ht₁T, ht₁40, ht₁seed, ht₁blk⟩ :
      ∃ t₁ : ℝ, T ≤ t₁ ∧ 40 ≤ t₁ ∧ 8 * Real.log ((m : ℝ) + 1) ≤ t₁ ∧
        8 * Real.log (3 * (1280 / η₀ ^ 2 + 1)) ≤ t₁ :=
    ⟨max (max T 40) (max (8 * Real.log ((m : ℝ) + 1))
        (8 * Real.log (3 * (1280 / η₀ ^ 2 + 1)))),
      le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _),
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have ht₁pos : 0 < t₁ := by linarith
  have hrate_le_one : ∀ i, rate2 i ^ lam ≤ 1 := fun i =>
    Real.rpow_le_one (rate2_pos i).le (by linarith [rate2_le i]) hlam0.le
  -- Lemma 2's block hypothesis, uniform above `t₁`
  have hblk : ∀ t, t₁ ≤ t → 3 * (1280 / η₀ ^ 2 + 1) ≤ Real.exp (t / 8) := by
    intro t ht
    have hpos : (0 : ℝ) < 3 * (1280 / η₀ ^ 2 + 1) := by positivity
    calc 3 * (1280 / η₀ ^ 2 + 1) = Real.exp (Real.log (3 * (1280 / η₀ ^ 2 + 1))) :=
          (Real.exp_log hpos).symm
      _ ≤ Real.exp (t / 8) := Real.exp_le_exp.mpr (by linarith)
  have hmain := recursion_lemma rate2 (coef2avg η₀) err2avg (errAddAvg η₀) (gA A) lam t₁
    (seedConst m) (1 / 2) (3 / 4) hlam0 ht₁pos hc₀ (by norm_num) (by norm_num)
    rate2_ge rate2_le hζ
    (fun t _ i => err2avg_nonneg i t)
    (fun t ht i => le_trans (err2avg_le (hTerr t (le_trans ht₁T ht)) i)
      (le_trans hε3 (coef2avg_ge hη1 i)))
    (fun t ht => le_trans (hTerr t (le_trans ht₁T ht)).2.2 hε2)
    (fun t ht => by
      have hi : ∀ i, err2avg i t * rate2 i ^ lam ≤ ε := by
        intro i
        calc err2avg i t * rate2 i ^ lam ≤ ε * 1 :=
              mul_le_mul (err2avg_le (hTerr t (le_trans ht₁T ht)) i) (hrate_le_one i)
                (Real.rpow_nonneg (rate2_pos i).le _) hε.le
          _ = ε := mul_one ε
      calc ∑ i, err2avg i t * rate2 i ^ lam ≤ ∑ _i : Fin 2, ε := sum_le_sum (fun i _ => hi i)
        _ = 2 * ε := by simp
        _ ≤ (∑ i, coef2avg η₀ i * rate2 i ^ lam - 1) / 3 := by linarith)
    (fun t ht _ => gA_seed hA hm hmA (by linarith))
    (fun t ht => production_two_averaged_sum hA hη0 hη1 (by linarith) (hblk t ht))
  refine ⟨seedConst m * t₁ ^ (-lam), by positivity, t₁, ht₁pos, ?_⟩
  intro t ht
  exact hmain t (by linarith)

/-! ### A certificate above Paper C's published exponent -/

/-- `ζ(100/203) > 0` at `η₀ = 10^{-5}`, by two rational bounds at the 203rd power:
`0.710737 ≤ 2^{-100/203}` since `0.710737^{203} ≤ 2^{-100}`, and
`0.867868 ≤ (3/4)^{100/203}` since `0.867868^{203} ≤ (3/4)^{100}`; then
`0.710737 + (49999/150000)(0.867868) = 1.0000205 > 1`.

`100/203 = 0.4926108…`, against the true root `λ_ideal = 0.4926579801…` of
`2^{-λ} + (1/3)(3/4)^λ = 1`, and above Paper C's published `λ** = 0.4925715447…`, which is what
this certificate exists to clear. `100/203` is the smallest-denominator rational in the window
`(λ**, λ_ideal)`: `33/67` falls just short of `λ**` and `67/136` leaves only `6.3·10^{-6}` of
slack, so this is the cheapest certificate that beats the manuscript's number. The margin
`2.05·10^{-5}` is what `η₀ = 10^{-5}` leaves of the `2.71·10^{-5}` available at `η₀ = 0`;
break-even is `η₀ = 4.69·10^{-5}`. -/
theorem zeta2avg_pos :
    0 < ∑ i, coef2avg (1 / 100000) i * rate2 i ^ ((100 : ℝ) / 203) - 1 := by
  rw [Fin.sum_univ_two]
  simp only [rate2, coef2avg, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : (710737 / 1000000 : ℝ) ≤ (1 / 2 : ℝ) ^ ((100 : ℝ) / 203) := by
    rw [Numerics.le_rpow_iff_pow (n := 203) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have h2 : (216967 / 250000 : ℝ) ≤ (3 / 4 : ℝ) ^ ((100 : ℝ) / 203) := by
    rw [Numerics.le_rpow_iff_pow (n := 203) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- **Contagion above Paper C's published exponent, as a log-mass bound, unconditionally.**
For every nonempty backward-closed `A` and `0 < λ ≤ 100/203 = 0.4926108…` there are `K > 0` and
`x₀` with `Σ_{n ∈ A, n ≤ x} 1/n ≥ K (log x)^λ` for all `x ≥ x₀`.

This is Theorem 5.3 of Paper C at an exponent above its `λ** ≈ 0.4925715`, and with the
hypothesis removed. What leaves the critical path is Proposition 4.4 and its two exponential-sum
bounds -- the manuscript's largest unformalized gap -- together with the six-word ladder and
Appendix D. Compare `logMass_contagion_elementary`, which is unconditional at `13/40 = 0.325`
because it pays Lemma 4.2's pointwise `2/9`; the whole gain is that the poor fibres have finite
total logarithmic mass, so the coefficient may be averaged instead. -/
theorem logMass_contagion_averaged {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → K * Real.log x ^ lam ≤ logMass A x := by
  obtain ⟨K, hK, t₁, ht₁, h⟩ := contagion_averaged hA ha hAa (η₀ := 1 / 100000) (by norm_num)
    (by norm_num) hlam0 (lt_of_lt_of_le zeta2avg_pos (zeta2avg_antitone (by norm_num) hlam))
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

/-- **Corollary 5.5(2) at exponent `100/203`, unconditional.** -/
theorem failures_logMass_averaged {a : ℕ} (ha : 1 ≤ a) (hfail : ¬ReachesOne a) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x :=
  logMass_contagion_averaged not_reachesOne_backwardClosed ha hfail hlam0 hlam

/-- **Theorem 7.2 with its contagion hypothesis discharged at the averaged exponent.** If the
odd failures in `(y, 2y]` number at most `y (log y)^{-e}` for all large `y`, for some
`e > 103/203 = 0.50739…`, then every positive integer reaches `1`.

The threshold is `1 - λ`, so this is what the exponent buys: `conjecture_of_tao_rate` needs
`e > 27/40 = 0.675` and Paper C's *conditional* form needs `e > 0.51`. The averaged coefficient
puts the unconditional threshold below the manuscript's conditional one. -/
theorem conjecture_of_tao_rate_averaged {e : ℝ} (he : 103 / 203 < e)
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  tao_rate_implies_conjecture (lam := 100 / 203) (by norm_num) (by norm_num) (by linarith)
    (fun ⟨a, ha, hfail⟩ => failures_logMass_averaged ha hfail (by norm_num) le_rfl) htao

/-- **Corollary 8.4 at the averaged exponent.** A cylinder bound `H(C, A)` at all large scales
with `A > C + e(C)` and `e(C) > 103/203`, above a certified floor `N₀`, gives the conjecture. -/
theorem conjecture_of_cylinder_bound_averaged {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C A : ℝ) (hC : 5 ≤ C)
    (hA : C + chernoffExponent C < A)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ C A y)
    (he : 103 / 203 < chernoffExponent C) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  cylinder_bound_implies_conjecture hN hfloor C A hC hA hcyl (lam := 100 / 203) (by norm_num)
    (by norm_num) (by linarith)
    (fun ⟨a, ha, hfail⟩ => failures_logMass_averaged ha hfail (by norm_num) le_rfl)

end Production

end Problems.Juggler
