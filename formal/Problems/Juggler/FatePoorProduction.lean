import Problems.Juggler.FatePoorTail
import Problems.Juggler.FateContagion

namespace Problems.Juggler

open Finset
open scoped Classical
open FiberParity

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
        = ∑ m ∈ G, (1 : ℝ) / m
          + ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m ∧ Poor η₀ m}, (1 : ℝ) / m := by
      rw [← sum_filter_add_sum_filter_not {m ∈ Ioc U (y'' - 1) | A m}
        (fun m => ¬ Poor η₀ m), filter_filter, filter_filter]
      simp only [not_not]
      rw [hG]
    have h2 : ∑ m ∈ {m ∈ Ioc U (y'' - 1) | A m ∧ Poor η₀ m}, (1 : ℝ) / m
        ≤ 2100 * eps U / η₀ ^ 2 := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)) hpoor
      intro m hm
      rw [mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.2⟩
    linarith
  -- `hB` forces `U` large enough that `ε_U` is far below `c`
  have hcoef : 0 ≤ c - eps U := by
    have hXpos : (0 : ℝ) < (U : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < U)) _
    have hX : eps U * (U : ℝ) ^ ((1 : ℝ) / 3) = 1 := eps_mul_cbrt hU1
    have hsq : (0 : ℝ) < η₀ ^ 2 := by positivity
    have hBmul : (1280 : ℝ) ≤ (2 / 3 * (U : ℝ) ^ ((1 : ℝ) / 3) - 1) * η₀ ^ 2 := by
      rw [← div_le_iff₀ hsq]; exact hB
    have hXge : (1920 : ℝ) / η₀ ^ 2 ≤ (U : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [div_le_iff₀ hsq]
      nlinarith [hBmul, hsq]
    have hstep := mul_le_mul_of_nonneg_left hXge hεpos.le
    have hepsle : eps U * 1920 ≤ η₀ ^ 2 := by
      have hdiv : eps U * ((1920 : ℝ) / η₀ ^ 2) ≤ 1 := by
        rw [hX] at hstep; linarith [hstep]
      rw [mul_div_assoc'] at hdiv
      rw [div_le_one hsq] at hdiv
      linarith
    rw [hc]
    nlinarith [hepsle, hη1, hη0, hεpos, hsq]
  have step1 := mul_le_mul_of_nonneg_left hsplit hcoef
  have step2 : (c - eps U) * ∑ m ∈ G, (1 : ℝ) / m = ∑ m ∈ G, (c - eps U) / m := by
    rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
  have step4 : ∑ n ∈ G.biUnion (fun m => {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}), (1 : ℝ) / n
      ≤ ∑ n ∈ {n ∈ Ioc s y | A n ∧ n % 2 = 1}, (1 : ℝ) / n :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  linarith

end Problems.Juggler
