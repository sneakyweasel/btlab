import Problems.Juggler.OOEEResonanceTail
import Problems.Juggler.FateOEWeighted
import Problems.Juggler.FateScaleAverage

/-! # Actual OOEE production from the summable count-poor tail

The exact source window converts counts to reciprocal mass. Disjoint fibres
and the physical cutoff give the remaining conserved-weight production.
-/

noncomputable section

namespace Problems.Juggler.FateOOEEWeighted

open Finset OOEEFibreGeometry OOEEFibreResonance FateOOEEAssembly CodeMassTransport
open scoped Classical

def eta : ℝ := 1/10000

theorem scale_large {m : ℕ} (hm : 10^9 ≤ m) : 10000 ≤ scale m := by
  have hs : (10000:ℝ) ≤ (10^9:ℝ)^(7/9:ℝ) := by
    rw [Numerics.le_rpow_iff_pow (n := 9) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  exact hs.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hm) (by norm_num))

theorem nonpoor_card_lower {m : ℕ} (hm : 10^9 ≤ m) (hgood : ¬CountPoor eta m) :
    (1107/10000)*scale m ≤ ((fibre m).card:ℝ) := by
  have hS := scale_large hm
  have he := (abs_le.mp (candidate_count_error (show 1 ≤ m by omega))).1
  have hH : (887/1000)*scale m ≤ (candidateCount m:ℝ) := by linarith
  have hpos : (0:ℝ) < candidateCount m := by
    exact_mod_cast candidate_count_pos (show 64 ≤ m by omega)
  have hg := (abs_lt.mp (lt_of_not_ge hgood)).1
  have hc : (1/8-eta)*(candidateCount m:ℝ) ≤ ((fibre m).card:ℝ) := by
    apply (le_div_iff₀ hpos).mp
    linarith
  have hp := mul_le_mul_of_nonneg_left hH (by norm_num [eta] : (0:ℝ) ≤ 1/8-eta)
  dsimp [eta] at hc hp
  linarith

theorem nonpoor_fibre_mass_lower {m : ℕ} (hm : 10^9 ≤ m)
    (hgood : ¬CountPoor eta m) :
    (11/100:ℝ)/m ≤ ∑ n ∈ fibre m, (1:ℝ)/n := by
  have hc := nonpoor_card_lower hm hgood
  have hmR : (10000:ℝ) ≤ m := by exact_mod_cast (show 10000 ≤ m by omega)
  have hm0 : (0:ℝ) < m := by linarith
  have hS := scale_large hm
  have hd : 0 < base m+3*scale m := by rw [base_eq_mul_scale]; positivity
  calc (11/100:ℝ)/m ≤ ((fibre m).card:ℝ)/(base m+3*scale m) := by
         rw [div_le_div_iff₀ hm0 hd,base_eq_mul_scale]
         have hmul := mul_le_mul_of_nonneg_right hc hm0.le
         have hgap := mul_nonneg (show (0:ℝ) ≤ (7/10000)*(m:ℝ)-33/100 by linarith)
           (show 0 ≤ scale m by linarith)
         nlinarith
    _ = ∑ _n ∈ fibre m, (1:ℝ)/(base m+3*scale m) := by simp [div_eq_mul_inv]
    _ ≤ ∑ n ∈ fibre m, (1:ℝ)/n := by
      apply sum_le_sum
      intro n hn
      have hw := source_window (show 64 ≤ m by omega) (mem_filter.mp hn).1
      have hn0 : (0:ℝ) < n := by
        have hb : 0 < base m := by rw [base_eq_mul_scale]; positivity
        linarith [hw.1]
      exact one_div_le_one_div_of_le hn0 hw.2.2

theorem ooee_fibre_cutoff {t : ℝ} {m n : ℕ} (hm : 64 ≤ m)
    (hmt : m ≤ cutoff (9*t/16-4)) (hn : n ∈ fibre m) : n ≤ cutoff t := by
  have hw := source_window hm (mem_filter.mp hn).1
  have hme : (m:ℝ) ≤ Real.exp (9*t/16-4) :=
    (Nat.cast_le.mpr hmt).trans (Nat.floor_le (Real.exp_pos _).le)
  have hb : base m ≤ Real.exp (t-64/9) := calc
    base m ≤ (Real.exp (9*t/16-4))^(16/9:ℝ) :=
      Real.rpow_le_rpow (by positivity) hme (by norm_num)
    _ = Real.exp (t-64/9) := by rw [← Real.exp_mul]; congr 1; ring
  have he : (2:ℝ) ≤ Real.exp (64/9:ℝ) := by
    linarith [Real.add_one_le_exp (64/9:ℝ)]
  apply Nat.le_floor
  calc (n:ℝ) ≤ 2*base m := hw.2.1
    _ ≤ 2*Real.exp (t-64/9) := by linarith
    _ ≤ Real.exp (64/9:ℝ)*Real.exp (t-64/9) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp t := by rw [← Real.exp_add]; congr 1; ring

def accepted (A : ℕ → Prop) (U M : ℕ) : Finset ℕ :=
  {m ∈ Icc 1 M | A m ∧ U < m ∧ ¬CountPoor eta m}

theorem accepted_mass_lower (A : ℕ → Prop) {U : ℕ} {E : ℝ}
    (hE : ∀ N, (∑ m ∈ (Ioc U N).filter (CountPoor eta), (1:ℝ)/m) ≤ E) (M : ℕ) :
    logMass A M - (logMass (fun _ => True) U+E) ≤
      ∑ m ∈ accepted A U M, (1:ℝ)/m := by
  let S := {m ∈ Icc 1 M | m ≤ U}
  let P := {m ∈ Icc 1 M | U < m ∧ CountPoor eta m}
  have hs : ∑ m ∈ S, (1:ℝ)/m ≤ logMass (fun _ => True) U := by
    simp only [logMass,filter_true]
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    intro m hm
    obtain ⟨hm,hU⟩ := mem_filter.mp hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1,hU⟩
  have hp : ∑ m ∈ P, (1:ℝ)/m ≤ E := by
    apply le_trans _ (hE M)
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    intro m hm
    obtain ⟨hm,hU,hp⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hU,(mem_Icc.mp hm).2⟩,hp⟩
  have hsplit : logMass A M ≤ (∑ m ∈ accepted A U M, (1:ℝ)/m)+
      (∑ m ∈ S, (1:ℝ)/m)+∑ m ∈ P, (1:ℝ)/m := by
    unfold logMass accepted S P
    simp_rw [sum_filter]
    rw [← sum_add_distrib,← sum_add_distrib]
    apply sum_le_sum
    intro m _
    have hsmall : m ≤ U ↔ ¬U < m := by omega
    by_cases ha : A m <;> by_cases hu : U < m <;>
      by_cases hp : CountPoor eta m <;> simp [ha,hu,hp,hsmall]
  linarith

theorem reciprocal_ooee_production {U : ℕ} (hU : 10^9 ≤ U) {E : ℝ} (hEn : 0 ≤ E)
    (hE : ∀ N, (∑ m ∈ (Ioc U N).filter (CountPoor eta), (1:ℝ)/m) ≤ E)
    {A : ℕ → Prop} (hA : BackwardClosed A) (t : ℝ) :
    (11/100)*logMass A (cutoff (9*t/16-4)) ≤
      logMass (fun n => A n ∧ ooeeGuard n) (cutoff t)+
        (logMass (fun _ => True) U+E) := by
  let M := cutoff (9*t/16-4)
  let G := accepted A U M
  have hsub : G.biUnion fibre ⊆ {n ∈ Icc 1 (cutoff t) | A n ∧ ooeeGuard n} := by
    intro n hn
    obtain ⟨m,hm,hn⟩ := mem_biUnion.mp hn
    obtain ⟨hmrange,hmA,hmU,_⟩ := mem_filter.mp hm
    have hf := mem_fibre.mp hn
    have hn1 : 1 ≤ n := by have := hf.1.1; omega
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hn1,ooee_fibre_cutoff (by omega) (mem_Icc.mp hmrange).2 hn⟩,?_,hf.1⟩
    exact backwardClosed_iterate hA 4 n (hf.2.symm ▸ hmA)
  have hdisj : ∀ m ∈ G, ∀ m' ∈ G, m ≠ m' → Disjoint (fibre m) (fibre m') := by
    intro m _ m' _ hne
    rw [Finset.disjoint_left]
    intro n hn hn'
    exact hne ((mem_fibre.mp hn).2.symm.trans (mem_fibre.mp hn').2)
  have hfib : (11/100:ℝ)*(∑ m ∈ G, (1:ℝ)/m) ≤
      ∑ n ∈ G.biUnion fibre, (1:ℝ)/n := by
    rw [mul_sum,sum_biUnion hdisj]
    apply sum_le_sum
    intro m hm
    obtain ⟨_,_,hmU,hgood⟩ := mem_filter.mp hm
    simpa only [mul_one_div] using nonpoor_fibre_mass_lower (by omega) hgood
  have hsource : ∑ n ∈ G.biUnion fibre, (1:ℝ)/n ≤
      logMass (fun n => A n ∧ ooeeGuard n) (cutoff t) := by
    unfold logMass
    apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    simpa using hsub
  have htarget := accepted_mass_lower A hE M
  have hc : 0 ≤ logMass (fun _ => True) U+E := by unfold logMass; positivity
  dsimp [G,M] at hfib htarget
  linarith

theorem ooee_production_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ → Prop, BackwardClosed A → ∀ t : ℝ,
      (11/100)*fullMass A (9*t/16-4) ≤ sourceMass A ooeeGuard (cutoff t)+C := by
  obtain ⟨D,hD,M,_,htail⟩ := OOEEResonanceTail.count_poor_tail (by norm_num [eta] : 0 < eta)
  let U := max M (10^9)
  let E := D*(U:ℝ)^(-7/9:ℝ)
  let B := logMass (fun _ => True) U+E
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hB : 0 ≤ B := by dsimp [B]; unfold logMass; positivity
  refine ⟨2*B+8,by positivity,?_⟩
  intro A hA t
  have h := reciprocal_ooee_production (le_max_right M (10^9)) hE
    (fun N => htail U N (le_max_left M (10^9))) hA t
  have ht := (abs_le.mp (FateOEWeighted.mass_reciprocal_error A (cutoff (9*t/16-4)))).2
  have hs := (abs_le.mp
    (FateOEWeighted.mass_reciprocal_error (fun n => A n ∧ ooeeGuard n) (cutoff t))).1
  have hid : mass (fun n => A n ∧ ooeeGuard n) (cutoff t) =
      sourceMass A ooeeGuard (cutoff t) := by
    unfold mass sourceMass
    apply sum_congr rfl
    intro n _
    by_cases hn : A n ∧ ooeeGuard n <;> simp [hn]
  rw [hid] at hs
  unfold fullMass
  dsimp [B,U] at *
  linarith

theorem ooee_production {A : ℕ → Prop} (hA : BackwardClosed A) :
    FateOEWeighted.OOEEProductionBound A := by
  obtain ⟨C,hC,h⟩ := ooee_production_uniform
  exact ⟨C,hC,0,fun t _ => h A hA t⟩

theorem logMass_growth {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      K*Real.log x^((5:ℝ)/8) ≤ logMass A x :=
  FateOEWeighted.logMass_growth_of_ooee hA ha hAa (ooee_production hA)

theorem conjecture_of_tao_rate {e : ℝ} (he : 3/8 < e)
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((oddFailures y).card:ℝ) ≤ y*Real.log y^(-e)) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  FateOEWeighted.conjecture_of_tao_rate_of_ooee he
    (ooee_production not_reachesOne_backwardClosed) htao

theorem pressure_average_conjecture {N₀ k₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (hk₀ : N₀ < 2^(k₀+1))
    {C θ q η : ℝ} (hC : 1 < C) (hθ : 0 < θ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη : 0 ≤ η)
    (hgap : 3/8 < C*(θ*pC C-Real.log (1-q+q*Real.exp θ))/Real.log 2-η)
    (havg : ScaleAverage.Bound N₀ k₀ C θ (1-q+q*Real.exp θ) η) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  ScaleAverage.pressure_average_conjecture_of_ooee hN hfloor hk₀ hC hθ hq0 hq1 hη
    (ooee_production not_reachesOne_backwardClosed) hgap havg

end Problems.Juggler.FateOOEEWeighted
