import Problems.Juggler.DepthFiveFibreGeometry
import Problems.Juggler.FateOEWeighted

/-! # Depth-five productions from summable count-poor tails

For each depth-five word, a target is count-poor when its actual fibre's share of
odd candidates differs from `1/16` by at least `eta = 1/1000`. If the poor targets
of both words have bounded reciprocal mass, then both depth-five productions hold
at coefficient `1/28`. With `FateDepthFiveAssembly` this gives contagion `37/50`.
The tail bounds themselves are the written, AI-audited Lemmas E6' and E8' of
`docs/problems/juggler_depth_five_production.md` and are not supplied here.
-/

noncomputable section

namespace Problems.Juggler.FateDepthFiveWeighted

open Finset DepthFiveFibreGeometry FateOOEEAssembly CodeMassTransport
open FateOOOEEAssembly (OOOEEGuard)
open FateDepthFiveAssembly (OOEOEGuard DepthFiveProductionBounds)
open scoped Classical

/-- The count-poor tolerance. -/
def eta : ℝ := 1/1000

/-- The threshold above which the count-to-weight conversion is uniform. -/
def threshold : ℕ := 10^15

/-- A target whose `OOOEE` fibre share differs from `1/16` by at least `η`. -/
def CountPoorA (η : ℝ) (t : ℕ) : Prop :=
  η ≤ |((fibreA t).card:ℝ) / candidateCount endpointA t - 1/16|

/-- A target whose `OOEOE` fibre share differs from `1/16` by at least `η`. -/
def CountPoorB (η : ℝ) (t : ℕ) : Prop :=
  η ≤ |((fibreB t).card:ℝ) / candidateCount endpointB t - 1/16|

/-- Bounded reciprocal mass of the targets satisfying `Poor`. -/
def TailBounded (Poor : ℕ → Prop) : Prop :=
  ∃ E : ℝ, ∀ N, (∑ m ∈ (Icc 1 N).filter Poor, (1:ℝ)/m) ≤ E

/-- Above the threshold `10^15` the window scale is at least `500`. -/
theorem scale_large {t : ℕ} (ht : threshold ≤ t) : 500 ≤ scale t := by
  have hs : (500:ℝ) ≤ ((10:ℝ)^15)^(5/27:ℝ) := by
    rw [Numerics.le_rpow_iff_pow (n := 27) (by positivity) (by norm_num) (by norm_num)]
    norm_num
  exact hs.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast ht) (by norm_num))

/-- The window scale `t^(5/27)` is at most `t`. -/
theorem scale_le_self {t : ℕ} (ht : 1 ≤ t) : scale t ≤ t := by
  have h1 : (1:ℝ) ≤ t := by exact_mod_cast ht
  calc scale t = (t:ℝ)^(5/27:ℝ) := rfl
    _ ≤ (t:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = t := Real.rpow_one _

/-- A fibre inside a depth-five window with at least `(1/16 - eta)` of its
candidates carries reciprocal mass at least `1/(28 t)`. -/
theorem fibre_mass_lower {F : Finset ℕ} {H : ℕ} {t : ℕ} (ht : threshold ≤ t)
    (hH : |(H:ℝ) - (16/27) * scale t| ≤ 4)
    (hwin : ∀ n ∈ F, base t ≤ n ∧ (n:ℝ) ≤ base t + (32/27) * scale t + 6)
    (hcard : (1/16 - eta) * H ≤ (F.card:ℝ)) :
    (1/28:ℝ)/t ≤ ∑ n ∈ F, (1:ℝ)/n := by
  have hs := scale_large ht
  have ht1 : 1 ≤ t := le_trans (by norm_num [threshold]) ht
  have hst := scale_le_self ht1
  have htR : (10:ℝ)^15 ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) < t := by linarith [show (0:ℝ) < 10^15 by positivity]
  have hHl := (abs_le.mp hH).1
  have hc : (1/16 - eta) * ((16/27) * scale t - 4) ≤ (F.card:ℝ) := by
    have := mul_le_mul_of_nonneg_left (show (16/27) * scale t - 4 ≤ (H:ℝ) by linarith)
      (by norm_num [eta] : (0:ℝ) ≤ 1/16 - eta)
    linarith
  have hd : 0 < base t + (32/27) * scale t + 6 := by
    rw [base_eq_mul_scale]; positivity
  calc (1/28:ℝ)/t ≤ (F.card:ℝ) / (base t + (32/27) * scale t + 6) := by
        rw [div_le_div_iff₀ ht0 hd, base_eq_mul_scale]
        dsimp [eta] at hc
        nlinarith [mul_le_mul_of_nonneg_left hc ht0.le]
    _ = ∑ _n ∈ F, (1:ℝ) / (base t + (32/27) * scale t + 6) := by simp [div_eq_mul_inv]
    _ ≤ ∑ n ∈ F, (1:ℝ)/n := by
      apply sum_le_sum
      intro n hn
      have hw := hwin n hn
      have hb : 0 < base t := by rw [base_eq_mul_scale]; positivity
      exact one_div_le_one_div_of_le (by linarith [hw.1]) hw.2

/-- Sources of targets up to `cutoff (27τ/32 - 4)` lie below `cutoff τ`. -/
theorem window_cutoff {τ : ℝ} {t n : ℕ} (ht : threshold ≤ t)
    (htc : t ≤ cutoff (27*τ/32 - 4))
    (hn : base t ≤ n ∧ (n:ℝ) ≤ base t + (32/27) * scale t + 6) : n ≤ cutoff τ := by
  have hs := scale_large ht
  have htR : (10:ℝ)^15 ≤ t := by exact_mod_cast ht
  have hte : (t:ℝ) ≤ Real.exp (27*τ/32 - 4) :=
    (Nat.cast_le.mpr htc).trans (Nat.floor_le (Real.exp_pos _).le)
  have hb : base t ≤ Real.exp (τ - 128/27) := calc
    base t ≤ (Real.exp (27*τ/32 - 4))^(32/27:ℝ) :=
      Real.rpow_le_rpow (by positivity) hte (by norm_num)
    _ = Real.exp (τ - 128/27) := by rw [← Real.exp_mul]; congr 1; ring
  have he : (2:ℝ) ≤ Real.exp (128/27:ℝ) := by linarith [Real.add_one_le_exp (128/27:ℝ)]
  have hsmall : (32/27) * scale t + 6 ≤ base t := by
    rw [base_eq_mul_scale]; nlinarith
  apply Nat.le_floor
  calc (n:ℝ) ≤ 2 * base t := by linarith [hn.2]
    _ ≤ 2 * Real.exp (τ - 128/27) := by linarith
    _ ≤ Real.exp (128/27:ℝ) * Real.exp (τ - 128/27) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp τ := by rw [← Real.exp_add]; congr 1; ring

/-- A generic depth-five production from a summable poor tail. -/
theorem production_of_tail {G : ℕ → Prop} {F : ℕ → Finset ℕ} {Poor : ℕ → Prop}
    (hmem : ∀ t n, n ∈ F t → G n ∧ floorPower^[5] n = t)
    (hwin : ∀ t, threshold ≤ t → ∀ n ∈ F t, base t ≤ n ∧
      (n:ℝ) ≤ base t + (32/27) * scale t + 6)
    (hmass : ∀ t, threshold ≤ t → ¬ Poor t → (1/28:ℝ)/t ≤ ∑ n ∈ F t, (1:ℝ)/n)
    (htail : TailBounded Poor) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ → Prop, BackwardClosed A → ∀ τ : ℝ,
      (1/28) * fullMass A (27*τ/32 - 4) ≤ sourceMass A G (cutoff τ) + C := by
  obtain ⟨E, hE⟩ := htail
  have hE0 : 0 ≤ E := le_trans (by simp) (hE 0)
  let U := threshold
  let B := logMass (fun _ => True) U + E
  have hB : 0 ≤ B := by dsimp [B]; unfold logMass; positivity
  refine ⟨B/14 + 7, by positivity, ?_⟩
  intro A hA τ
  let M := cutoff (27*τ/32 - 4)
  let acc := (Icc 1 M).filter (fun m => A m ∧ U < m ∧ ¬ Poor m)
  -- targets: discard those up to U and the poor ones
  have htarget : logMass A M - B ≤ ∑ m ∈ acc, (1:ℝ)/m := by
    have hsplit : logMass A M ≤ (∑ m ∈ acc, (1:ℝ)/m) +
        (∑ m ∈ (Icc 1 M).filter (fun m => m ≤ U), (1:ℝ)/m) +
        ∑ m ∈ (Icc 1 M).filter Poor, (1:ℝ)/m := by
      unfold logMass
      simp only [acc, sum_filter]
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_le_sum
      intro m _
      by_cases hu : m ≤ U
      · have hu' : ¬ U < m := by omega
        by_cases ha : A m <;> by_cases hp : Poor m <;> simp [ha, hu, hu', hp]
      · have hu' : U < m := by omega
        by_cases ha : A m <;> by_cases hp : Poor m <;> simp [ha, hu, hu', hp]
    have hs : ∑ m ∈ (Icc 1 M).filter (fun m => m ≤ U), (1:ℝ)/m ≤
        logMass (fun _ => True) U := by
      simp only [logMass, filter_true]
      apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
      intro m hm
      obtain ⟨hm, hU⟩ := mem_filter.mp hm
      exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hU⟩
    have hp := hE M
    dsimp [B]
    linarith
  -- sources: disjoint fibres below the physical cutoff, inside A by backward closure
  have hdisj : ∀ m ∈ acc, ∀ m' ∈ acc, m ≠ m' → Disjoint (F m) (F m') := by
    intro m _ m' _ hne
    rw [Finset.disjoint_left]
    intro n hn hn'
    exact hne ((hmem m n hn).2.symm.trans (hmem m' n hn').2)
  have hsub : acc.biUnion F ⊆ (Icc 1 (cutoff τ)).filter (fun n => A n ∧ G n) := by
    intro n hn
    obtain ⟨m, hm, hn⟩ := mem_biUnion.mp hn
    obtain ⟨hmr, hmA, hmU, _⟩ := mem_filter.mp hm
    have hf := hmem m n hn
    have hw := hwin m hmU.le n hn
    have hb1 : (1:ℝ) ≤ base m := Real.one_le_rpow
      (by exact_mod_cast (mem_Icc.mp hmr).1) (by norm_num)
    have hn1 : 1 ≤ n := by
      have : (1:ℝ) ≤ n := hb1.trans hw.1
      exact_mod_cast this
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hn1,
      window_cutoff hmU.le (mem_Icc.mp hmr).2 hw⟩, ?_, hf.1⟩
    exact backwardClosed_iterate hA 5 n (hf.2.symm ▸ hmA)
  have hfib : (1/28:ℝ) * (∑ m ∈ acc, (1:ℝ)/m) ≤ ∑ n ∈ acc.biUnion F, (1:ℝ)/n := by
    rw [mul_sum, sum_biUnion hdisj]
    apply sum_le_sum
    intro m hm
    obtain ⟨_, _, hmU, hgood⟩ := mem_filter.mp hm
    have := hmass m hmU.le hgood
    rw [mul_one_div]; exact this
  have hsrc : ∑ n ∈ acc.biUnion F, (1:ℝ)/n ≤ logMass (fun n => A n ∧ G n) (cutoff τ) := by
    unfold logMass
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    simpa using hsub
  -- reciprocal to conserved weight
  have ht := (abs_le.mp (FateOEWeighted.mass_reciprocal_error A M)).2
  have hs := (abs_le.mp
    (FateOEWeighted.mass_reciprocal_error (fun n => A n ∧ G n) (cutoff τ))).1
  have hid : mass (fun n => A n ∧ G n) (cutoff τ) = sourceMass A G (cutoff τ) := by
    unfold mass sourceMass
    apply sum_congr rfl
    intro n _
    by_cases hn : A n ∧ G n <;> simp [hn]
  rw [hid] at hs
  unfold fullMass
  dsimp [M] at htarget hfib ht
  linarith

/-- Both depth-five productions follow from bounded count-poor tails. -/
theorem depth_five_productions (hA : TailBounded (CountPoorA eta))
    (hB : TailBounded (CountPoorB eta)) :
    ∀ A : ℕ → Prop, BackwardClosed A → DepthFiveProductionBounds A := by
  have hcardA : ∀ t, threshold ≤ t → ¬ CountPoorA eta t →
      (1/16 - eta) * (candidateCount endpointA t:ℝ) ≤ ((fibreA t).card:ℝ) := by
    intro t ht hg
    have ht1 : 1 ≤ t := le_trans (by norm_num [threshold]) ht
    have hs := scale_large ht
    have hH := (abs_le.mp (windowA ht1).1).1
    have hpos : (0:ℝ) < candidateCount endpointA t := by linarith
    have hl := (abs_lt.mp (lt_of_not_ge hg)).1
    have := (le_div_iff₀ hpos).mp (by linarith : 1/16 - eta ≤ ((fibreA t).card:ℝ) /
      candidateCount endpointA t)
    linarith
  have hcardB : ∀ t, threshold ≤ t → ¬ CountPoorB eta t →
      (1/16 - eta) * (candidateCount endpointB t:ℝ) ≤ ((fibreB t).card:ℝ) := by
    intro t ht hg
    have ht1 : 1 ≤ t := le_trans (by norm_num [threshold]) ht
    have hs := scale_large ht
    have hH := (abs_le.mp (windowB ht1).1).1
    have hpos : (0:ℝ) < candidateCount endpointB t := by linarith
    have hl := (abs_lt.mp (lt_of_not_ge hg)).1
    have := (le_div_iff₀ hpos).mp (by linarith : 1/16 - eta ≤ ((fibreB t).card:ℝ) /
      candidateCount endpointB t)
    linarith
  obtain ⟨CA, hCA, prodA⟩ := production_of_tail (G := OOOEEGuard) (F := fibreA)
    (fun t n hn => mem_fibreA.mp hn)
    (fun t ht n hn => (windowA (le_trans (by norm_num [threshold]) ht)).2 n
      (mem_filter.mp hn).1)
    (fun t ht hg => fibre_mass_lower ht (windowA (le_trans (by norm_num [threshold]) ht)).1
      (fun n hn => (windowA (le_trans (by norm_num [threshold]) ht)).2 n (mem_filter.mp hn).1)
      (hcardA t ht hg)) hA
  obtain ⟨CB, hCB, prodB⟩ := production_of_tail (G := OOEOEGuard) (F := fibreB)
    (fun t n hn => mem_fibreB.mp hn)
    (fun t ht n hn => (windowB (le_trans (by norm_num [threshold]) ht)).2 n
      (mem_filter.mp hn).1)
    (fun t ht hg => fibre_mass_lower ht (windowB (le_trans (by norm_num [threshold]) ht)).1
      (fun n hn => (windowB (le_trans (by norm_num [threshold]) ht)).2 n (mem_filter.mp hn).1)
      (hcardB t ht hg)) hB
  intro A hAc
  refine ⟨4, CA + CB, by norm_num, by positivity, 0, ?_⟩
  intro t _
  exact ⟨(prodA A hAc t).trans (by linarith), (prodB A hAc t).trans (by linarith)⟩

/-- Contagion at `37/50`, conditional only on the two bounded count-poor tails. -/
theorem logMass_growth_of_tails {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (hTA : TailBounded (CountPoorA eta))
    (hTB : TailBounded (CountPoorB eta)) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      K * Real.log x ^ ((37 : ℝ) / 50) ≤ logMass A x :=
  FateDepthFiveAssembly.logMass_growth_of_depth_five hA ha hAa
    (depth_five_productions hTA hTB A hA)

end Problems.Juggler.FateDepthFiveWeighted
