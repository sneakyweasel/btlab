import Problems.Juggler.FateOOEEAssembly

/-!
# The actual OE production for the conserved weight

The established poor-fibre theorem supplies the OE analytic input.
The new OOEE input is not proved here.
-/

noncomputable section

namespace Problems.Juggler.FateOEWeighted

open Finset Filter CodeMassTransport FateOOEEAssembly FiberParity
open scoped Classical Topology

theorem weight_paired_bounds {n : ℕ} (hn : 1 ≤ n) :
    2 / (paired n : ℝ) ≤ weight n ∧
      weight n ≤ 2 / ((paired n : ℝ) - 1) := by
  have he : (2 : ℝ) ≤ paired n := by exact_mod_cast paired_ge_two hn
  have hd : (0 : ℝ) < (paired n : ℝ) - 1 := by linarith
  have hw : weight n = Real.log (1 + 2 / ((paired n : ℝ) - 1)) := by
    rw [weight_log_ratio hn]
    congr 1
    field_simp
    ring
  rw [hw]
  constructor
  · have h := Real.le_log_one_add_of_nonneg
      (show (0 : ℝ) ≤ 2 / ((paired n : ℝ) - 1) by positivity)
    convert h using 1
    field_simp
    ring
  · have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 2 / ((paired n : ℝ) - 1) by positivity)
    linarith

theorem weight_reciprocal_error {n : ℕ} (hn : 1 ≤ n) :
    |weight n - 2 / (n : ℝ)| ≤
      6 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := weight_paired_bounds hn
  have hen : (n : ℝ) ≤ paired n := by
    exact_mod_cast (show n ≤ paired n by unfold paired; omega)
  have he1 : (paired n : ℝ) ≤ n + 1 := by
    exact_mod_cast (show paired n ≤ n + 1 by unfold paired; omega)
  have hlo : 2 / ((n : ℝ) + 1) ≤ weight n :=
    (div_le_div_of_nonneg_left (by norm_num) (by linarith [paired_ge_two hn]) he1).trans hp.1
  rw [abs_le]
  constructor
  · have h : 2 / (n : ℝ) - 6 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) ≤
        2 / ((n : ℝ) + 1) := by
      field_simp
      nlinarith
    linarith
  · by_cases h1 : n = 1
    · subst n
      have hw := (weight_reciprocal_bounds (by omega : 1 ≤ 1)).2
      norm_num at hw ⊢
      linarith
    · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      have hu : weight n ≤ 2 / ((n : ℝ) - 1) := hp.2.trans
        (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))
      have h : 2 / ((n : ℝ) - 1) - 2 / (n : ℝ) ≤
          6 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
        have hd : (0 : ℝ) < (n : ℝ) - 1 := by linarith
        field_simp [hd.ne']
        nlinarith
      linarith

theorem reciprocal_telescoping (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((1 : ℝ) / n - 1 / ((n : ℝ) + 1)) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- A uniform error for every source predicate, with no density assumption. -/
theorem mass_reciprocal_error (A : ℕ → Prop) (N : ℕ) :
    |mass A N - 2 * logMass A N| ≤ 6 := by
  have hid : mass A N - 2 * logMass A N =
      ∑ n ∈ Icc 1 N, if A n then weight n - 2 / (n : ℝ) else 0 := by
    rw [mass, logMass, sum_filter, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    split_ifs <;> ring
  rw [hid]
  calc |∑ n ∈ Icc 1 N, if A n then weight n - 2 / (n : ℝ) else 0|
      ≤ ∑ n ∈ Icc 1 N, |if A n then weight n - 2 / (n : ℝ) else 0| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 N, 6 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      apply sum_le_sum
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      split_ifs
      · exact weight_reciprocal_error hn1
      · rw [abs_zero]
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have h := one_div_le_one_div_of_le hn0 (by linarith : (n : ℝ) ≤ n + 1)
        linarith
    _ = 6 * (1 - 1 / ((N : ℝ) + 1)) := by rw [← mul_sum, reciprocal_telescoping]
    _ ≤ 6 := by
      have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith

theorem oe_fibre_cutoff {t : ℝ} {m n : ℕ} (hm : 1 ≤ m)
    (hmt : m ≤ cutoff (3 * t / 4 - 4)) (hn : n ∈ oeFiber m) : n ≤ cutoff t := by
  have hn3 : (n : ℝ) ^ 3 < ((m : ℝ) + 1) ^ 4 := by
    exact_mod_cast (mem_oeFiber.mp hn).2.2
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hme : (m : ℝ) ≤ Real.exp (3 * t / 4 - 4) :=
    (Nat.cast_le.mpr hmt).trans (Nat.floor_le (Real.exp_pos _).le)
  have hm2 : (m : ℝ) + 1 ≤ 2 * Real.exp (3 * t / 4 - 4) := by linarith
  have he16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hp : ((m : ℝ) + 1) ^ 4 ≤ (Real.exp t) ^ 3 := calc
    ((m : ℝ) + 1) ^ 4 ≤ (2 * Real.exp (3 * t / 4 - 4)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hm2 4
    _ = 16 * Real.exp (3 * t - 16) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
      ring
    _ ≤ Real.exp 16 * Real.exp (3 * t - 16) :=
      mul_le_mul_of_nonneg_right he16 (Real.exp_pos _).le
    _ = (Real.exp t) ^ 3 := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
  apply Nat.le_floor
  exact (lt_of_pow_lt_pow_left₀ 3 (Real.exp_pos t).le (hn3.trans_le hp)).le

def baseCutoff : ℕ := 10 ^ 36
def eta : ℝ := 1 / 1000

theorem base_parameters : 10 ^ 6 ≤ baseCutoff ∧ eps baseCutoff ≤ 1 / 1000 ∧
    1280 / eta ^ 2 ≤ 2 / 3 * (baseCutoff : ℝ) ^ ((1 : ℝ) / 3) - 1 ∧
    32 / (eta * (2 / 3 * (baseCutoff : ℝ) ^ ((1 : ℝ) / 3) - 1)) < 1 / 2 := by
  have hu : 1 ≤ baseCutoff := by norm_num [baseCutoff]
  have hr : (10 ^ 12 : ℝ) ≤ (baseCutoff : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Numerics.le_rpow_iff_pow (n := 3) (Nat.cast_nonneg _) (by norm_num) (by norm_num)]
    norm_num [baseCutoff]
  have he := eps_mul_cbrt hu
  have hep := eps_pos hu
  have hem := mul_le_mul_of_nonneg_left hr hep.le
  refine ⟨by norm_num [baseCutoff], by nlinarith, ?_, ?_⟩
  · norm_num [eta]
    nlinarith
  · apply (div_lt_iff₀ (by dsimp [eta]; nlinarith :
        0 < eta * (2 / 3 * (baseCutoff : ℝ) ^ ((1 : ℝ) / 3) - 1))).mpr
    dsimp [eta]
    nlinarith

def accepted (A : ℕ → Prop) (M : ℕ) : Finset ℕ :=
  {m ∈ Icc 1 M | A m ∧ baseCutoff < m ∧ ¬ Poor eta m}

def exceptionalMass : ℝ :=
  logMass (fun _ => True) baseCutoff + 2100 * eps baseCutoff / eta ^ 2

theorem exceptionalMass_nonneg : 0 ≤ exceptionalMass := by
  unfold exceptionalMass logMass
  have he := (eps_pos (show 1 ≤ baseCutoff by norm_num [baseCutoff])).le
  positivity

theorem accepted_mass_lower (A : ℕ → Prop) (M : ℕ) :
    logMass A M - exceptionalMass ≤ ∑ m ∈ accepted A M, (1 : ℝ) / m := by
  let S := {m ∈ Icc 1 M | m ≤ baseCutoff}
  let P := {m ∈ Icc 1 M | baseCutoff < m ∧ Poor eta m}
  have hs : ∑ m ∈ S, (1 : ℝ) / m ≤ logMass (fun _ => True) baseCutoff := by
    simp only [logMass, filter_true]
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    intro m hm
    obtain ⟨hm, hU⟩ := mem_filter.mp hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hU⟩
  have hp : ∑ m ∈ P, (1 : ℝ) / m ≤ 2100 * eps baseCutoff / eta ^ 2 := by
    apply le_trans _ (poor_logMass_le base_parameters.1 (by norm_num [eta])
      (by norm_num [eta]) base_parameters.2.2.1 base_parameters.2.2.2)
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    intro m hm
    obtain ⟨hm, hU, hp⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hU, (mem_Icc.mp hm).2⟩, hp⟩
  have hsplit : logMass A M ≤ (∑ m ∈ accepted A M, (1 : ℝ) / m) +
      (∑ m ∈ S, (1 : ℝ) / m) + ∑ m ∈ P, (1 : ℝ) / m := by
    unfold logMass accepted S P
    simp_rw [sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro m _
    have hsmall : m ≤ baseCutoff ↔ ¬ baseCutoff < m := by omega
    by_cases ha : A m <;> by_cases hU : baseCutoff < m <;>
      by_cases hp : Poor eta m <;> simp [ha, hU, hp, hsmall] <;> positivity
  unfold exceptionalMass
  linarith

theorem accepted_fibre_lower {A : ℕ → Prop} {M m : ℕ} (hm : m ∈ accepted A M) :
    (33 / 100 : ℝ) / m ≤
      ∑ n ∈ {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}, (1 : ℝ) / n := by
  obtain ⟨hm, hA, hU, hnp⟩ := mem_filter.mp hm
  have hm6 : 10 ^ 6 ≤ m := base_parameters.1.trans (by omega)
  have he : eps m ≤ 1 / 1000 :=
    (eps_antitone (by norm_num [baseCutoff]) hU.le).trans base_parameters.2.1
  apply le_trans _ (nonpoor_fiber_logMass_ge hm6 (by norm_num [eta])
    (by norm_num [eta]) hnp)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  dsimp [eta]
  linarith

theorem reciprocal_oe_production {A : ℕ → Prop} (hA : BackwardClosed A) (t : ℝ) :
    (33 / 100) * logMass A (cutoff (3 * t / 4 - 4)) ≤
      logMass (fun n => A n ∧ oeGuard n) (cutoff t) + exceptionalMass := by
  let M := cutoff (3 * t / 4 - 4)
  let G := accepted A M
  let B := fun m => {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}
  have hsub : G.biUnion B ⊆ {n ∈ Icc 1 (cutoff t) | A n ∧ oeGuard n} := by
    intro n hn
    obtain ⟨m, hm, hn⟩ := mem_biUnion.mp hn
    obtain ⟨hmrange, hmA, _, _⟩ := mem_filter.mp hm
    obtain ⟨hnf, heven⟩ := mem_filter.mp hn
    obtain ⟨hodd, hcell1, hcell2⟩ := mem_oeFiber.mp hnf
    have hnm := oe_fibre_cutoff (mem_Icc.mp hmrange).1 (mem_Icc.mp hmrange).2 hnf
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hnm⟩, ?_⟩
    refine ⟨oe_fiber_mem hA hmA hodd heven hcell1 hcell2, hodd, ?_⟩
    simpa only [floorPower_odd_eq hodd] using heven
  have hdisj : ∀ m ∈ G, ∀ m' ∈ G, m ≠ m' → Disjoint (B m) (B m') := by
    intro m _ m' _ hne
    rw [Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨hn, _⟩ := mem_filter.mp hn
    obtain ⟨hn', _⟩ := mem_filter.mp hn'
    exact oe_fiber_disjoint hne (mem_oeFiber.mp hn).2.1 (mem_oeFiber.mp hn).2.2
      (mem_oeFiber.mp hn').2.1 (mem_oeFiber.mp hn').2.2
  have hfib : (33 / 100 : ℝ) * (∑ m ∈ G, (1 : ℝ) / m) ≤
      ∑ n ∈ G.biUnion B, (1 : ℝ) / n := by
    rw [mul_sum, sum_biUnion hdisj]
    apply sum_le_sum
    intro m hm
    simpa only [mul_one_div] using accepted_fibre_lower hm
  have hsource : ∑ n ∈ G.biUnion B, (1 : ℝ) / n ≤
      logMass (fun n => A n ∧ oeGuard n) (cutoff t) :=
    sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have htarget := accepted_mass_lower A M
  have hc := exceptionalMass_nonneg
  dsimp [G, M] at hfib htarget
  linarith

/-- The exact OE input needed by the three-production assembly, unconditionally. -/
theorem oe_production {A : ℕ → Prop} (hA : BackwardClosed A) (t : ℝ) :
    (33 / 100) * fullMass A (3 * t / 4 - 4) ≤
      sourceMass A oeGuard (cutoff t) + (2 * exceptionalMass + 8) := by
  have h := reciprocal_oe_production hA t
  have ht := (abs_le.mp (mass_reciprocal_error A (cutoff (3 * t / 4 - 4)))).2
  have hs := (abs_le.mp
    (mass_reciprocal_error (fun n => A n ∧ oeGuard n) (cutoff t))).1
  change _ ≤ sourceMass A oeGuard (cutoff t) + (2 * exceptionalMass + 8)
  have hid : mass (fun n => A n ∧ oeGuard n) (cutoff t) =
      sourceMass A oeGuard (cutoff t) := rfl
  rw [hid] at hs
  unfold fullMass
  linarith

/-- Only the new two-consecutive-odd analytic production remains. -/
def OOEEProductionBound (A : ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℝ, ∀ t, T ≤ t →
    (11 / 100) * fullMass A (9 * t / 16 - 4) ≤
      sourceMass A ooeeGuard (cutoff t) + C

theorem oddProductionBounds_of_ooee {A : ℕ → Prop} (hA : BackwardClosed A)
    (hOOEE : OOEEProductionBound A) : OddProductionBounds A := by
  obtain ⟨C, hC, T, h⟩ := hOOEE
  refine ⟨max C (2 * exceptionalMass + 8), hC.trans (le_max_left _ _), T, ?_⟩
  intro t ht
  constructor
  · have ho := oe_production hA t
    linarith [le_max_right C (2 * exceptionalMass + 8)]
  · exact (h t ht).trans (add_le_add_left (le_max_left _ _) _)

theorem logMass_growth_of_ooee {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) (hOOEE : OOEEProductionBound A) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      K * Real.log x ^ ((5 : ℝ) / 8) ≤ logMass A x :=
  logMass_growth hA ha hAa (oddProductionBounds_of_ooee hA hOOEE)

theorem conjecture_of_tao_rate_of_ooee {e : ℝ} (he : 3 / 8 < e)
    (hOOEE : OOEEProductionBound (fun n => ¬ ReachesOne n))
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  conjecture_of_tao_rate he (oddProductionBounds_of_ooee not_reachesOne_backwardClosed hOOEE) htao

end Problems.Juggler.FateOEWeighted
