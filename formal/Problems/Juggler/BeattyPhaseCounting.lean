import Problems.Juggler.BeattyPhaseEquidistribution
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Counting beneath an equidistributed phase profile

Finite phase partitions reduce a moving index cutoff to ordinary frequencies
at dilated prefixes. Monotone profiles are then controlled by their Darboux sums.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set Finset MeasureTheory Function
open BTCalculus.FourierBoxCounting

/-- A limiting prefix frequency remains valid at a nonnegative real dilation
of the cutoff, with normalization by the undilated real parameter. -/
theorem tendsto_count_floor_mul {P : ℕ → Prop} {d c : ℝ}
    (hP : Tendsto (fun N => (count P N : ℝ) / N) atTop (𝓝 d)) (hc : 0 ≤ c) :
    Tendsto (fun T : ℝ => (count P ⌊c*T⌋₊ : ℝ)/T) atTop (𝓝 (d*c)) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul, Nat.floor_zero, count, range_zero, filter_empty,
      Finset.card_empty, Nat.cast_zero, zero_div, mul_zero]
    exact tendsto_const_nhds
  have hf : Tendsto (fun T : ℝ => ⌊c*T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hc)
  have h := (hP.comp hf).mul (tendsto_nat_floor_mul_div_atTop hc.le)
  apply h.congr'
  filter_upwards [hf.eventually (eventually_ge_atTop 1)] with T hT
  have hn : (⌊c*T⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ⌊c*T⌋₊ ≠ 0)
  dsimp only [Function.comp_def]
  field_simp

/-- Number of positive indices lying below a varying, index-dependent ceiling.
The applications supply a uniform upper bound, which makes the set finite. -/
noncomputable def diagonalCount (u : ℕ → ℝ) (T : ℝ) : ℕ :=
  {n : ℕ | (n : ℝ)+1 ≤ T*u n}.ncard

private theorem index_le_floor {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    (n : ℝ)+1 ≤ x ↔ n < ⌊x⌋₊ := by
  rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.le_floor_iff hx]
  omega

/-- A bounded ceiling has only finitely many indices below it. -/
theorem finite_diagonalCount {u : ℕ → ℝ} {B T : ℝ}
    (hu : ∀ n, u n ≤ B) (hT : 0 ≤ T) :
    {n : ℕ | (n : ℝ)+1 ≤ T*u n}.Finite := by
  apply (finite_lt_nat ⌈T*B⌉₊).subset
  intro n hn
  have h := hn.trans ((mul_le_mul_of_nonneg_left (hu n) hT).trans (Nat.le_ceil _))
  have : (n : ℝ) < (⌈T*B⌉₊ : ℝ) := by linarith
  exact_mod_cast this

/-- The moving-cutoff count is monotone in its ceiling sequence. -/
theorem diagonalCount_mono {u v : ℕ → ℝ} {B T : ℝ}
    (huv : ∀ n, u n ≤ v n) (hv : ∀ n, v n ≤ B) (hT : 0 ≤ T) :
    diagonalCount u T ≤ diagonalCount v T := by
  apply Set.ncard_le_ncard _ (finite_diagonalCount hv hT)
  exact fun n hn => hn.trans (mul_le_mul_of_nonneg_left (huv n) hT)

/-- A finite-valued ceiling splits exactly into frequency counts at its
individual dilated cutoffs. -/
theorem diagonalCount_finite_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ → ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) {T : ℝ} (hT : 0 ≤ T) :
    diagonalCount (fun n => c (q n)) T = ∑ i, count (fun n => q n = i) ⌊c i*T⌋₊ := by
  classical
  let s (i : ι) : Set ℕ := {n | n < ⌊c i*T⌋₊ ∧ q n = i}
  have hs (i : ι) : (s i).Finite := (finite_lt_nat _).subset fun n hn => hn.1
  have hd : Pairwise (Disjoint on s) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro n hn hm
    exact hij (hn.2.symm.trans hm.2)
  have he : {n : ℕ | (n : ℝ)+1 ≤ T*c (q n)} = ⋃ i, s i := by
    ext n
    simp only [mem_ofPred_eq, mem_iUnion, s]
    constructor
    · intro hn
      exact ⟨q n, (index_le_floor (mul_nonneg (hc _) hT)).1 (by simpa [mul_comm] using hn), rfl⟩
    · rintro ⟨i, hn, hi⟩
      simpa [hi, mul_comm] using (index_le_floor (mul_nonneg (hc i) hT)).2 hn
  rw [diagonalCount, he, Set.ncard_iUnion_of_finite hs hd, finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [count]
  have he' : s i = ↑((range ⌊c i*T⌋₊).filter fun n => q n = i) := by
    ext n; simp [s]
  rw [he']
  rw [Set.ncard_coe_finset]
  congr 1
  ext n
  simp

/-- Frequencies of a finite partition determine the moving-cutoff limit
for every nonnegative ceiling constant on that partition. -/
theorem diagonalCount_finite_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ → ι) (c d : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hq : ∀ i, Tendsto (fun N => (count (fun n => q n = i) N : ℝ)/N)
      atTop (𝓝 (d i))) :
    Tendsto (fun T : ℝ => (diagonalCount (fun n => c (q n)) T : ℝ)/T)
      atTop (𝓝 (∑ i, d i*c i)) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ => tendsto_count_floor_mul (hq i) (hc i))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [diagonalCount_finite_eq q c hc hT, Nat.cast_sum, Finset.sum_div]

private noncomputable def phaseBin (θ : ℕ → ℝ) (hθ : ∀ n, θ n ∈ Ico (0 : ℝ) 1)
    (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k :=
  ⟨⌊(k : ℝ)*θ n⌋₊, by
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have hf := Nat.floor_le (mul_nonneg hkr.le (hθ n).1)
    have hx : (k : ℝ)*θ n < k := by nlinarith [(hθ n).2]
    exact_mod_cast hf.trans_lt hx⟩

private theorem phaseBin_bounds (θ : ℕ → ℝ) (hθ : ∀ n, θ n ∈ Ico (0 : ℝ) 1)
    (k : ℕ) (hk : 0 < k) (n : ℕ) :
    (phaseBin θ hθ k hk n : ℝ)/k ≤ θ n ∧
      θ n < ((phaseBin θ hθ k hk n : ℝ)+1)/k := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rw [div_le_iff₀ hkr]
    simpa [phaseBin, mul_comm] using Nat.floor_le (mul_nonneg hkr.le (hθ n).1)
  · rw [lt_div_iff₀ hkr]
    simpa [phaseBin, mul_comm] using Nat.lt_floor_add_one ((k : ℝ)*θ n)

private theorem phaseBin_eq_iff (θ : ℕ → ℝ) (hθ : ∀ n, θ n ∈ Ico (0 : ℝ) 1)
    (k : ℕ) (hk : 0 < k) (n : ℕ) (i : Fin k) :
    phaseBin θ hθ k hk n = i ↔ θ n ∈ Ico ((i : ℝ)/k) (((i : ℝ)+1)/k) := by
  constructor
  · intro he
    simpa [he] using phaseBin_bounds θ hθ k hk n
  · intro hi
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    apply Fin.ext
    apply le_antisymm
    · have hf := Nat.floor_le (mul_nonneg hkr.le (hθ n).1)
      have h := (lt_div_iff₀ hkr).1 hi.2
      have : (⌊(k : ℝ)*θ n⌋₊ : ℝ) < i.val+1 := by nlinarith
      have : ⌊(k : ℝ)*θ n⌋₊ < i.val+1 := by exact_mod_cast this
      exact Nat.le_of_lt_succ this
    · exact Nat.le_floor (by simpa [mul_comm] using (div_le_iff₀ hkr).1 hi.1)

private theorem darboux_bounds {g : ℝ → ℝ} (hg : Monotone g) {k : ℕ} (hk : 0 < k) :
    (∑ i : Fin k, g ((i : ℝ)/k)/k) ≤ ∫ x in (0 : ℝ)..1, g x ∧
    (∫ x in (0 : ℝ)..1, g x) ≤ ∑ i : Fin k, g (((i : ℝ)+1)/k)/k := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ)/k) (n := k) (μ := volume)
    (fun j _ => hg.intervalIntegrable)
  simp only [Nat.cast_zero, zero_div, div_self hkr.ne'] at he
  rw [← he, ← Fin.sum_univ_eq_sum_range]
  constructor
  · apply Finset.sum_le_sum
    intro i _
    have hab : (i : ℝ)/k ≤ ((i : ℝ)+1)/k := by gcongr; linarith
    have h := intervalIntegral.integral_mono_on (μ := volume) hab (intervalIntegrable_const)
      hg.intervalIntegrable (fun x hx => hg hx.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, Nat.cast_add, Nat.cast_one,
      add_div, add_sub_cancel_left, one_div, inv_mul_eq_div] using h
  · apply Finset.sum_le_sum
    intro i _
    have hab : (i : ℝ)/k ≤ ((i : ℝ)+1)/k := by gcongr; linarith
    have h := intervalIntegral.integral_mono_on (μ := volume) hab hg.intervalIntegrable
      (intervalIntegrable_const) (fun x hx => hg hx.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, Nat.cast_add, Nat.cast_one,
      add_div, add_sub_cancel_left, one_div, inv_mul_eq_div] using h

private theorem darboux_sub (g : ℝ → ℝ) {k : ℕ} (hk : 0 < k) :
    (∑ i : Fin k, g (((i : ℝ)+1)/k)/k) - (∑ i : Fin k, g ((i : ℝ)/k)/k) =
      (g 1-g 0)/k := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_div]
  rw [← Finset.sum_div]
  change (∑ i : Fin k, (fun j : ℕ => g (((j : ℝ)+1)/k)-g ((j : ℝ)/k)) i)/k = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => g (((j : ℝ)+1)/k)-g ((j : ℝ)/k)) k]
  have h (j : ℕ) : ∑ i ∈ range j, (g (((i : ℝ)+1)/k)-g ((i : ℝ)/k)) =
      g ((j : ℝ)/k)-g 0 := by
    induction j with
    | zero => simp
    | succ j ih => rw [sum_range_succ, ih]; push_cast; ring
  rw [h, div_self (by exact_mod_cast hk.ne' : (k : ℝ) ≠ 0)]

/-- An equidistributed sequence in the unit interval counts the region
`n+1 ≤ T*g(θ n)` with limiting density `∫₀¹ g`. The profile may have dense
jumps: monotonicity and nonnegativity suffice. -/
theorem diagonalCount_monotone_tendsto {θ : ℕ → ℝ}
    (hθ : ∀ n, θ n ∈ Ico (0 : ℝ) 1)
    (hfreq : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N => (count (fun n => θ n ∈ Ico a b) N : ℝ)/N)
        atTop (𝓝 (b-a)))
    {g : ℝ → ℝ} (hg : Monotone g) (hg0 : 0 ≤ g 0) :
    Tendsto (fun T : ℝ => (diagonalCount (fun n => g (θ n)) T : ℝ)/T)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, g x)) := by
  classical
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (2*(g 1-g 0)/ε))
  have hk1 : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk0 : 0 < k := by exact_mod_cast (zero_lt_one.trans hk1)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have hgap : (g 1-g 0)/(k : ℝ) < ε/2 := by
    have := (le_max_right _ _).trans_lt hk
    rw [div_lt_iff₀ hε] at this
    rw [div_lt_iff₀ hkr]
    nlinarith
  let q := phaseBin θ hθ k hk0
  let l (i : Fin k) := g ((i : ℝ)/k)
  let u (i : Fin k) := g (((i : ℝ)+1)/k)
  have hl (i : Fin k) : 0 ≤ l i := hg0.trans (hg (by positivity))
  have hu (i : Fin k) : 0 ≤ u i := hg0.trans (hg (by positivity))
  have hq (i : Fin k) : Tendsto (fun N => (count (fun n => q n = i) N : ℝ)/N)
      atTop (𝓝 ((k : ℝ)⁻¹)) := by
    have ha : 0 ≤ (i : ℝ)/k := by positivity
    have hab : (i : ℝ)/k < ((i : ℝ)+1)/k := by gcongr; linarith
    have hb : ((i : ℝ)+1)/k ≤ 1 := by
      rw [div_le_one hkr]
      exact_mod_cast (Nat.succ_le_of_lt i.isLt)
    have h := hfreq _ _ ha hab hb
    simp_rw [← phaseBin_eq_iff θ hθ k hk0] at h
    convert h using 1
    simp [add_div, one_div]
  have hL := diagonalCount_finite_tendsto q l (fun _ => (k : ℝ)⁻¹) hl hq
  have hU := diagonalCount_finite_tendsto q u (fun _ => (k : ℝ)⁻¹) hu hq
  have hD := darboux_bounds hg hk0
  have hE := darboux_sub g hk0
  simp only [inv_mul_eq_div] at hL hU
  filter_upwards [Metric.tendsto_nhds.1 hL (ε/2) (by positivity),
    Metric.tendsto_nhds.1 hU (ε/2) (by positivity), eventually_gt_atTop (0 : ℝ)] with T hLT hUT hT
  have hb (n : ℕ) : u (q n) ≤ g 1 := by
    apply hg
    rw [div_le_one hkr]
    exact_mod_cast Nat.succ_le_of_lt (q n).isLt
  have hnl (n : ℕ) : l (q n) ≤ g (θ n) := hg (phaseBin_bounds θ hθ k hk0 n).1
  have hnu (n : ℕ) : g (θ n) ≤ u (q n) := hg (phaseBin_bounds θ hθ k hk0 n).2.le
  have hcl := diagonalCount_mono hnl (fun n => (hnu n).trans (hb n)) hT.le
  have hcu := diagonalCount_mono hnu hb hT.le
  have hcl' : (diagonalCount (fun n => l (q n)) T : ℝ)/T ≤
      (diagonalCount (fun n => g (θ n)) T : ℝ)/T :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcl) hT.le
  have hcu' : (diagonalCount (fun n => g (θ n)) T : ℝ)/T ≤
      (diagonalCount (fun n => u (q n)) T : ℝ)/T :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcu) hT.le
  rw [Real.dist_eq, abs_lt] at hLT hUT ⊢
  dsimp only [l, u] at hLT hUT
  constructor <;> linarith

private theorem count_eq_sum (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    count P N = ∑ n ∈ range N, if P n then 1 else 0 := by
  rw [Finset.sum_boole]
  simp only [Nat.cast_id, count]
  congr 1
  ext n
  simp

private theorem count_shift (P : ℕ → Prop) (N : ℕ) :
    count P (N+1) = count (fun n => P (n+1)) N + count P 1 := by
  classical
  simp only [count_eq_sum, sum_range_one]
  exact Finset.sum_range_succ' (fun n => if P n then (1 : ℕ) else 0) N

/-- Deleting the first observation preserves a limiting prefix frequency. -/
theorem tendsto_count_shift {P : ℕ → Prop} {d : ℝ}
    (hP : Tendsto (fun N => (count P N : ℝ)/N) atTop (𝓝 d)) :
    Tendsto (fun N => (count (fun n => P (n+1)) N : ℝ)/N) atTop (𝓝 d) := by
  classical
  have h := hP.comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun N : ℕ => ((N : ℝ)+1)/N) atTop (𝓝 1) := by
    have h' := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    apply (show Tendsto (fun N : ℕ => 1+1/(N : ℝ)) atTop (𝓝 1) from by simpa using h').congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have hz := (h.mul hr).sub
    (tendsto_const_div_atTop_nhds_zero_nat (count P 1 : ℝ))
  simp only [mul_one, sub_zero] at hz
  apply hz.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  dsimp only [Function.comp_def]
  rw [count_shift, Nat.cast_add, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- Every half-open subinterval has its Euclidean length as the limiting
frequency of the positive certificate phases. -/
theorem certificatePhase_shift_interval_frequency {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N => (count (fun n => certificatePhase (n+1) ∈ Ico a b) N : ℝ)/N)
      atTop (𝓝 (b-a)) := by
  classical
  have hnull : (unitPhaseLaw : Measure ℝ) (frontier (Ico a b)) = 0 := by
    rw [frontier_Ico hab]
    change (volume.restrict (Ioc (0 : ℝ) 1)) {a, b} = 0
    rw [Measure.restrict_apply (by measurability)]
    exact measure_mono_null inter_subset_left
      (((Set.finite_singleton b).insert a).countable.measure_zero volume)
  have h := empiricalLaw_tendsto_count (u := certificatePhase) (mu := unitPhaseLaw)
    (S := Ico a b) certificatePhase_equidistributed measurableSet_Ico hnull
  have hm : (unitPhaseLaw : Measure ℝ).real (Ico a b) = b-a := by
    change (volume.restrict (Ioc (0 : ℝ) 1)).real (Ico a b) = _
    rw [← restrict_Ico_eq_restrict_Ioc, measureReal_restrict_apply measurableSet_Ico,
      inter_eq_left.2 (Ico_subset_Ico ha hb), Real.volume_real_Ico, max_eq_left (sub_nonneg.2 hab.le)]
  rw [hm] at h
  exact tendsto_count_shift (P := fun n => certificatePhase n ∈ Ico a b) h

/-- A finite exceptional prefix changes a moving-cutoff count by at most
the length of that prefix. -/
theorem diagonalCount_le_add {u v : ℕ → ℝ} {B T : ℝ} {N : ℕ}
    (huv : ∀ n, N ≤ n → u n ≤ v n) (hv : ∀ n, v n ≤ B) (hT : 0 ≤ T) :
    diagonalCount u T ≤ diagonalCount v T + N := by
  have hsub : {n : ℕ | (n : ℝ)+1 ≤ T*u n} ⊆
      {n : ℕ | (n : ℝ)+1 ≤ T*v n} ∪ ↑(range N) := by
    intro n hn
    by_cases hN : N ≤ n
    · exact Or.inl (hn.trans (mul_le_mul_of_nonneg_left (huv n hN) hT))
    · exact Or.inr (by simpa using lt_of_not_ge hN)
  have h := (Set.ncard_le_ncard hsub
    ((finite_diagonalCount hv hT).union (Finset.finite_toSet _))).trans (Set.ncard_union_le _ _)
  simpa only [Set.ncard_coe_finset, card_range, diagonalCount] using h

/-- The moving-cutoff limit is stable under a vanishing perturbation of a
positive monotone phase profile. The perturbed sequence need only be bounded
above; finitely many exceptional indices do not affect the limit. -/
theorem diagonalCount_tendsto_of_sub_tendsto_zero {θ u : ℕ → ℝ} {B : ℝ}
    (hθ : ∀ n, θ n ∈ Ico (0 : ℝ) 1)
    (hfreq : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N => (count (fun n => θ n ∈ Ico a b) N : ℝ)/N)
        atTop (𝓝 (b-a)))
    {g : ℝ → ℝ} (hg : Monotone g) (hg0 : 0 < g 0)
    (hu : ∀ n, u n ≤ B)
    (he : Tendsto (fun n => u n-g (θ n)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (diagonalCount u T : ℝ)/T)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, g x)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ := min (ε/3) (g 0/2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε/3 := min_le_left _ _
  have hδg : δ ≤ g 0/2 := min_le_right _ _
  have hlm : Monotone (fun x => g x-δ) := fun x y hxy => sub_le_sub_right (hg hxy) δ
  have hum : Monotone (fun x => g x+δ) := by
    intro x y hxy
    have := hg hxy
    dsimp only
    linarith
  have hL := diagonalCount_monotone_tendsto hθ hfreq hlm (by linarith : 0 ≤ g 0-δ)
  have hU := diagonalCount_monotone_tendsto hθ hfreq hum (by linarith : 0 ≤ g 0+δ)
  rw [intervalIntegral.integral_sub hg.intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_const] at hL
  rw [intervalIntegral.integral_add hg.intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_const] at hU
  norm_num only [sub_zero, one_smul] at hL hU
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 he δ hδ)
  have hnl (n : ℕ) (hn : N ≤ n) : g (θ n)-δ ≤ u n := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at h
    linarith
  have hnu (n : ℕ) (hn : N ≤ n) : u n ≤ g (θ n)+δ := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_lt] at h
    linarith
  have hnlim : Tendsto (fun T : ℝ => (N : ℝ)/T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hL' := hL.sub hnlim
  have hU' := hU.add hnlim
  simp only [sub_zero, add_zero] at hL' hU'
  filter_upwards [Metric.tendsto_nhds.1 hL' (ε/3) (by positivity),
    Metric.tendsto_nhds.1 hU' (ε/3) (by positivity), eventually_gt_atTop (0 : ℝ)] with T hLT hUT hT
  have hcl := diagonalCount_le_add hnl hu hT.le
  have hb (n : ℕ) : g (θ n)+δ ≤ g 1+δ := by linarith [hg (hθ n).2.le]
  have hcu := diagonalCount_le_add hnu hb hT.le
  have hcl' := div_le_div_of_nonneg_right (by exact_mod_cast hcl :
    (diagonalCount (fun n => g (θ n)-δ) T : ℝ) ≤ diagonalCount u T+N) hT.le
  have hcu' := div_le_div_of_nonneg_right (by exact_mod_cast hcu :
    (diagonalCount u T : ℝ) ≤ diagonalCount (fun n => g (θ n)+δ) T+N) hT.le
  rw [add_div] at hcl' hcu'
  rw [Real.dist_eq, abs_lt] at hLT hUT ⊢
  constructor <;> linarith

end Problems.Juggler.BeattyPhase
