import BTCalculus.SublinearPowerCancellation

/-! # Cancellation for noninteger mixed powers

Mean-value points stay inside the actual shifted interval. This supplies
the asymptotic step for an induction on the integer part of the exponent.
The final theorem treats every nonzero finite combination of distinct
positive noninteger powers along a positive affine progression. No
exponential-sum estimate or cancellation hypothesis is assumed.
-/

noncomputable section

namespace BTCalculus.PowerPhaseAsymptotics

open Finset Filter
open scoped Topology
open BTCalculus.WeylDifferencing BTCalculus.KusminLandau
open BTCalculus.SublinearPowerCancellation

/-- A bounded positive shift does not change the leading real-power scale. -/
theorem tendsto_intermediate_rpow_ratio {t : ℝ → ℝ} {h : ℝ}
    (ht : ∀ᶠ x in atTop, x ≤ t x ∧ t x ≤ x + h) (p : ℝ) :
    Tendsto (fun x => (t x) ^ p / x ^ p) atTop (𝓝 1) := by
  have hr : Tendsto (fun x => t x / x) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun x : ℝ => 1 + h / x) atTop (𝓝 1) by
        simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul h).const_add 1)
    · filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with x hx hx0
      exact (le_div_iff₀ hx0).2 (by simpa using hx.1)
    · filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with x hx hx0
      apply (div_le_iff₀ hx0).2
      simpa [add_mul, ne_of_gt hx0] using hx.2
  have hp := hr.rpow_const (p := p) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  simp only [Real.one_rpow] at hp
  apply hp.congr'
  filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  exact Real.div_rpow (hx0.le.trans hx.1) hx0.le p

/-- The leading asymptotic of a fixed difference follows from the actual derivative. -/
theorem tendsto_difference_div_rpow {f g : ℝ → ℝ} {p c h : ℝ}
    (hd : ∀ᶠ x in atTop, HasDerivAt f (g x) x)
    (hg : Tendsto (fun x => g x / x ^ p) atTop (𝓝 c)) (hh : 0 < h) :
    Tendsto (fun x => (f (x + h) - f x) / x ^ p) atTop (𝓝 (h * c)) := by
  obtain ⟨A, hA⟩ := eventually_atTop.1 hd
  have hex (x : ℝ) : ∃ t, A < x → x < t ∧ t < x + h ∧
      g t = (f (x + h) - f x) / h := by
    by_cases hx : A < x
    · obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope f g (by linarith : x < x + h)
        (fun y hy => (hA y (by linarith [hy.1])).continuousAt.continuousWithinAt)
        (fun y hy => hA y (by linarith [hy.1]))
      exact ⟨t, fun _ => ⟨ht.1, ht.2, by simpa using he⟩⟩
    · exact ⟨x, fun hx' => (hx hx').elim⟩
  choose t ht using hex
  have hloc : ∀ᶠ x in atTop, x ≤ t x ∧ t x ≤ x + h := by
    filter_upwards [eventually_gt_atTop A] with x hx
    exact ⟨(ht x hx).1.le, (ht x hx).2.1.le⟩
  have htop : Tendsto t atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    exact hloc.mono (fun x hx => hx.1)
  have hlim := ((hg.comp htop).mul (tendsto_intermediate_rpow_ratio hloc p)).const_mul h
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop A, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have ht0 : 0 < t x := hx0.trans (ht x hx).1
  have he := (ht x hx).2.2
  have hn : (t x) ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht0 p)
  dsimp only [Function.comp_apply]
  rw [he]
  field_simp

/-- A reciprocal first-derivative bound of sublinear power size is o(N). -/
theorem tendsto_normalized_reciprocal_power {A p C : ℝ}
    (hA : 0 < A) (hp : 0 < p) :
    Tendsto (fun N : ℕ => (1 / (C * (A + N) ^ (p - 1))) / (N : ℝ))
      atTop (𝓝 0) := by
  have htop : Tendsto (fun N : ℕ => A + (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop A tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_neg_atTop hp).comp htop
  have hratio : Tendsto (fun N : ℕ => (A + N) / (N : ℝ)) atTop (𝓝 1) := by
    have hlim := (tendsto_const_div_atTop_nhds_zero_nat A).add_const 1
    simp only [zero_add] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp [add_div, hn]
  have hlim := (hratio.mul hpow).div_const C
  simp only [one_mul, zero_div] at hlim
  apply hlim.congr'
  filter_upwards [] with N
  have hAN : 0 < A + (N : ℝ) := by positivity
  dsimp only [Function.comp_apply]
  rw [Real.rpow_sub hAN, Real.rpow_one, Real.rpow_neg hAN.le]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Eventual derivative bounds and monotonicity give sublinear cancellation. -/
theorem tendsto_average_zero_of_derivative_bounds {f g : ℝ → ℝ} {p C : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hC : 0 < C)
    (hd : ∀ᶠ x in atTop, HasDerivAt f (g x) x)
    (hb : ∀ᶠ x in atTop, C * x ^ (p - 1) ≤ g x ∧ g x ≤ 1 / 2)
    (hm : ∃ B, AntitoneOn g (Set.Ici B)) :
    Tendsto (average (fun n => phase (f n))) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hd.and hb)
  obtain ⟨B, hm⟩ := hm
  obtain ⟨A, hA⟩ := exists_nat_gt (max 0 (max K B))
  have hA0 : (0 : ℝ) < A := lt_of_le_of_lt (le_max_left _ _) hA
  have hAK : K ≤ (A : ℝ) := (le_max_left K B).trans ((le_max_right _ _).trans hA.le)
  have hAB : B ≤ (A : ℝ) := (le_max_right K B).trans ((le_max_right _ _).trans hA.le)
  apply tendsto_average_zero_of_shift _ A
  apply squeeze_zero_norm' (a := fun N : ℕ =>
    (1 / (C * ((A : ℝ) + N) ^ (p - 1))) / (N : ℝ))
  · filter_upwards [] with N
    have hAN : 0 < (A : ℝ) + N := by positivity
    have hδ : 0 < C * ((A : ℝ) + N) ^ (p - 1) := by positivity
    have hδsmall : C * ((A : ℝ) + N) ^ (p - 1) ≤ 1 / 2 :=
      (hK ((A : ℝ) + N) (by linarith [Nat.cast_nonneg (α := ℝ) N])).2.1.trans
        (hK ((A : ℝ) + N) (by linarith [Nat.cast_nonneg (α := ℝ) N])).2.2
    have hbound := first_derivative_sum_bound f g (A : ℝ) N hδ
      (fun x hx => (hK x (hAK.trans hx.1)).1.continuousAt.continuousWithinAt)
      (fun x hx => (hK x (hAK.trans hx.1.le)).1)
      (fun x hx => show C * ((A : ℝ) + N) ^ (p - 1) ≤ g x ∧
          g x ≤ 1 - C * ((A : ℝ) + N) ^ (p - 1) from
        ⟨(mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (hA0.trans hx.1) hx.2.le (by linarith)) hC.le).trans
            (hK x (hAK.trans hx.1.le)).2.1,
          by linarith [(hK x (hAK.trans hx.1.le)).2.2]⟩)
      (Or.inr (hm.mono (fun x hx => hAB.trans hx.1.le)))
    rw [norm_average]
    have he : (fun n : ℕ => phase (f ((n + A : ℕ) : ℝ))) =
        (fun n : ℕ => phase (f ((A : ℝ) + n))) := by
      funext n
      simp [Nat.cast_add, add_comm]
    change ‖∑ n ∈ range N, (fun n : ℕ => phase (f ((n + A : ℕ) : ℝ))) n‖ / (N : ℝ) ≤ _
    rw [he]
    exact div_le_div_of_nonneg_right hbound (by positivity)
  · exact tendsto_normalized_reciprocal_power hA0 hp

/-- The positive first-derivative asymptotic and negative second derivative suffice. -/
theorem tendsto_average_zero_of_two_derivatives {f g q : ℝ → ℝ} {p c : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hc : 0 < c)
    (hd : ∀ᶠ x in atTop, HasDerivAt f (g x) x)
    (hdg : ∀ᶠ x in atTop, HasDerivAt g (q x) x)
    (hg : Tendsto (fun x => g x / x ^ (p - 1)) atTop (𝓝 c))
    (hq : ∀ᶠ x in atTop, q x ≤ 0) :
    Tendsto (average (fun n => phase (f n))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ (p - 1)) atTop (𝓝 0) := by
    have he : p - 1 = -(1 - p) := by ring
    rw [he]
    exact tendsto_rpow_neg_atTop (by linarith)
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hlim := hg.mul hpow
    simp only [mul_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hx _))
  have hb : ∀ᶠ x in atTop, (c / 2) * x ^ (p - 1) ≤ g x ∧ g x ≤ 1 / 2 := by
    filter_upwards [hg.eventually (lt_mem_nhds (show c / 2 < c by linarith)),
      hg0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_gt_atTop (0 : ℝ)] with x hl hu hx
    exact ⟨((lt_div_iff₀ (Real.rpow_pos_of_pos hx _)).1 hl).le, hu.le⟩
  obtain ⟨B, hB⟩ := eventually_atTop.1 (hdg.and hq)
  apply tendsto_average_zero_of_derivative_bounds hp hp1 (show 0 < c / 2 by positivity) hd hb
  refine ⟨B, antitoneOn_of_hasDerivWithinAt_nonpos (f' := q) (convex_Ici B)
    (fun x hx => (hB x hx).1.continuousAt.continuousWithinAt) ?_ ?_⟩
  · intro x hx
    exact (hB x (interior_subset hx)).1.hasDerivWithinAt
  · intro x hx
    exact (hB x (interior_subset hx)).2

/-- A smooth derivative tower with the leading asymptotics of c*x^p.
Each derivative is only required eventually; no common tail over all orders is assumed. -/
def HasPowerAsymptotics (f : ℝ → ℝ) (p c : ℝ) : Prop :=
  ∃ (D : ℕ → ℝ → ℝ) (a : ℕ → ℝ), D 0 = f ∧ a 0 = c ∧
    (∀ k, a (k + 1) = a k * (p - k)) ∧
    (∀ k, ∀ᶠ x in atTop, HasDerivAt (D k) (D (k + 1) x) x) ∧
    (∀ k, Tendsto (fun x => D k x / x ^ (p - k)) atTop (𝓝 (a k)))

/-- Fixed positive differences lower the exponent by one, including every derivative. -/
theorem HasPowerAsymptotics.difference {f : ℝ → ℝ} {p c h : ℝ}
    (hf : HasPowerAsymptotics f p c) (hh : 0 < h) :
    HasPowerAsymptotics (fun x => f (x + h) - f x) (p - 1) (h * c * p) := by
  obtain ⟨D, a, hD, ha, har, hd, hl⟩ := hf
  refine ⟨fun k x => D k (x + h) - D k x, fun k => h * a (k + 1), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hD]
  · dsimp only
    rw [har, ha]
    norm_num
    ring
  · intro k
    dsimp only
    rw [har (k + 1)]
    push_cast
    ring
  · intro k
    filter_upwards [hd k, (tendsto_atTop_add_const_right atTop h tendsto_id).eventually (hd k)]
      with x hx hy
    have hs := hy.comp x ((hasDerivAt_id x).add_const h)
    simpa only [Function.comp_def, id_eq, mul_one] using hs.fun_sub hx
  · intro k
    have hs := tendsto_difference_div_rpow (hd k) (hl (k + 1)) hh
    have he : p - 1 - (k : ℝ) = p - ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    simpa only [he] using hs

/-- Negation changes the leading coefficient without changing the exponent. -/
theorem HasPowerAsymptotics.neg {f : ℝ → ℝ} {p c : ℝ}
    (hf : HasPowerAsymptotics f p c) : HasPowerAsymptotics (fun x => -f x) p (-c) := by
  obtain ⟨D, a, hD, ha, har, hd, hl⟩ := hf
  refine ⟨fun k x => -D k x, fun k => -a k, ?_, by simp [ha], ?_, ?_, ?_⟩
  · simp only [hD]
  · intro k
    simp only [har, neg_mul]
  · intro k
    exact (hd k).mono (fun x hx => hx.neg)
  · intro k
    simpa only [neg_div] using (hl k).neg

theorem HasPowerAsymptotics.cancellation_sublinear_pos {f : ℝ → ℝ} {p c : ℝ}
    (hf : HasPowerAsymptotics f p c) (hp : 0 < p) (hp1 : p < 1) (hc : 0 < c) :
    Tendsto (average (fun n => phase (f n))) atTop (𝓝 0) := by
  obtain ⟨D, a, hD, ha, har, hd, hl⟩ := hf
  have ha1 : a 1 = c * p := by simpa [ha] using har 0
  have ha2 : a 2 = c * p * (p - 1) := by simpa [ha1] using har 1
  have hneg : c * p * (p - 1) < 0 := mul_neg_of_pos_of_neg (mul_pos hc hp) (by linarith)
  have hq : ∀ᶠ x in atTop, D 2 x ≤ 0 := by
    have hlim := hl 2
    rw [ha2] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hneg), eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have := (div_lt_iff₀ (Real.rpow_pos_of_pos hx0 _)).1 hx
    simpa only [zero_mul] using this.le
  apply tendsto_average_zero_of_two_derivatives hp hp1 (mul_pos hc hp)
    (by simpa only [hD] using hd 0) (hd 1)
  · simpa only [ha1, Nat.cast_one] using hl 1
  · exact hq

/-- Complex conjugation preserves the zero limit of phase averages. -/
theorem tendsto_phase_average_zero_of_neg (f : ℕ → ℝ)
    (hf : Tendsto (average (fun n => phase (-f n))) atTop (𝓝 0)) :
    Tendsto (average (fun n => phase (f n))) atTop (𝓝 0) := by
  open scoped ComplexConjugate in
  have he (N : ℕ) : average (fun n => phase (-f n)) N =
      conj (average (fun n => phase (f n)) N) := by
    simp only [phase_neg, average, map_div₀, map_sum, map_natCast]
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simpa only [he, Complex.norm_conj, norm_zero] using hf.norm

/-- Qualitative cancellation at every noninteger derivative order. -/
theorem HasPowerAsymptotics.cancellation {f : ℝ → ℝ} {p c : ℝ}
    (hf : HasPowerAsymptotics f p c) (hc : c ≠ 0)
    (m : ℕ) (hlo : (m : ℝ) < p) (hhi : p < m + 1) :
    Tendsto (average (fun n => phase (f n))) atTop (𝓝 0) := by
  induction m generalizing f p c with
  | zero =>
    simp only [Nat.cast_zero, zero_add] at hlo hhi
    rcases lt_or_gt_of_ne hc with hc | hc
    · apply tendsto_phase_average_zero_of_neg
      exact hf.neg.cancellation_sublinear_pos hlo hhi (neg_pos.mpr hc)
    · exact hf.cancellation_sublinear_pos hlo hhi hc
  | succ m ih =>
    apply tendsto_phase_average_zero_of_differences
    intro d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hp : 0 < p := by have := Nat.cast_nonneg (α := ℝ) (m + 1); linarith
    have hlim := ih (hf.difference hdR)
      (mul_ne_zero (mul_ne_zero (ne_of_gt hdR) hc) (ne_of_gt hp))
      (by push_cast at hlo; linarith) (by push_cast at hhi; linarith)
    simpa only [Nat.cast_add] using hlim

/-- Coefficients of the successive derivatives of x^p. -/
def powerCoeff (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => powerCoeff p k * (p - k)

/-- Every real power has the stated derivative asymptotics, including negative orders. -/
theorem hasPowerAsymptotics_power (p c : ℝ) :
    HasPowerAsymptotics (fun x => c * x ^ p) p c := by
  refine ⟨fun k x => c * powerCoeff p k * x ^ (p - k),
    fun k => c * powerCoeff p k, ?_, by simp [powerCoeff], ?_, ?_, ?_⟩
  · simp [powerCoeff]
  · intro k
    simp only [powerCoeff]
    ring
  · intro k
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hd := (Real.hasDerivAt_rpow_const (p := p - k) (Or.inl (ne_of_gt hx))).const_mul
      (c * powerCoeff p k)
    have he : p - (k : ℝ) - 1 = p - ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    simpa only [he, powerCoeff, mul_assoc] using hd
  · intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (mul_div_cancel_right₀ _ (ne_of_gt (Real.rpow_pos_of_pos hx _))).symm

/-- Lower powers have zero coefficient when measured at a larger power scale. -/
theorem HasPowerAsymptotics.lower_order {f : ℝ → ℝ} {p q c : ℝ}
    (hf : HasPowerAsymptotics f p c) (hpq : p < q) :
    HasPowerAsymptotics f q 0 := by
  obtain ⟨D, a, hD, _, _, hd, hl⟩ := hf
  refine ⟨D, fun _ => 0, hD, rfl, by simp, hd, ?_⟩
  intro k
  have hpow : Tendsto (fun x : ℝ => x ^ (p - q)) atTop (𝓝 0) := by
    have he : p - q = -(q - p) := by ring
    rw [he]
    exact tendsto_rpow_neg_atTop (sub_pos.mpr hpq)
  have hlim := (hl k).mul hpow
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have he : p - q = (p - k) - (q - k) := by ring
  rw [he, Real.rpow_sub hx (p - k) (q - k)]
  have hn : x ^ (p - k) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  field_simp

/-- Sums at a common scale add their leading coefficients. -/
theorem HasPowerAsymptotics.add {f g : ℝ → ℝ} {p c d : ℝ}
    (hf : HasPowerAsymptotics f p c) (hg : HasPowerAsymptotics g p d) :
    HasPowerAsymptotics (fun x => f x + g x) p (c + d) := by
  obtain ⟨D, a, hD, ha, har, hd, hl⟩ := hf
  obtain ⟨E, b, hE, hb, hbr, he, hm⟩ := hg
  refine ⟨fun k x => D k x + E k x, fun k => a k + b k,
    by simp only [hD, hE], by simp only [ha, hb], ?_, ?_, ?_⟩
  · intro k
    simp only [har, hbr]
    ring
  · intro k
    filter_upwards [hd k, he k] with x hx hy
    exact hx.fun_add hy
  · intro k
    simpa only [add_div] using (hl k).add (hm k)

/-- A finite sum at a common scale has the sum of the leading coefficients. -/
theorem hasPowerAsymptotics_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (c : ι → ℝ) (p : ℝ)
    (hf : ∀ i ∈ s, HasPowerAsymptotics (f i) p (c i)) :
    HasPowerAsymptotics (fun x => ∑ i ∈ s, f i x) p (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasPowerAsymptotics_power p 0
  | @insert i s hi ih =>
    simpa only [sum_insert hi] using
      (hf i (mem_insert_self i s)).add (ih (fun j hj => hf j (mem_insert_of_mem hj)))

/-- Finite mixed powers have the derivative asymptotics of their unique top exponent. -/
theorem hasPowerAsymptotics_mixed {ι : Type*} (s : Finset ι) (c p : ι → ℝ)
    (j : ι) (hj : j ∈ s) (htop : ∀ i ∈ s, i ≠ j → p i < p j) :
    HasPowerAsymptotics (fun x => ∑ i ∈ s, c i * x ^ p i) (p j) (c j) := by
  classical
  have h := hasPowerAsymptotics_sum s (fun i x => c i * x ^ p i)
    (fun i => if i = j then c j else 0) (p j) (by
      intro i hi
      by_cases hij : i = j
      · subst i
        simpa using hasPowerAsymptotics_power (p j) (c j)
      · simpa only [if_neg hij] using
          (hasPowerAsymptotics_power (p i) (c i)).lower_order (htop i hi hij))
  simpa [hj] using h

/-- Affine arguments have their expected leading power scale. -/
theorem tendsto_affine_rpow_ratio {A B : ℝ} (hA : 0 < A) (p : ℝ) :
    Tendsto (fun x => (A * x + B) ^ p / x ^ p) atTop (𝓝 (A ^ p)) := by
  have hr : Tendsto (fun x : ℝ => (A * x + B) / x) atTop (𝓝 A) := by
    have hlim := (tendsto_inv_atTop_zero.const_mul B).const_add A
    simp only [mul_zero, add_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hp := hr.rpow_const (p := p) (Or.inl (ne_of_gt hA))
  have hpos : ∀ᶠ x in atTop, 0 < (A * x + B) / x := hr.eventually (lt_mem_nhds hA)
  apply hp.congr'
  filter_upwards [hpos, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hnum : 0 < A * x + B := (div_pos_iff_of_pos_right hx0).1 hx
  exact Real.div_rpow hnum.le hx0.le p

/-- Positive affine changes of variable preserve the full derivative tower. -/
theorem HasPowerAsymptotics.affine {f : ℝ → ℝ} {p c A : ℝ}
    (hf : HasPowerAsymptotics f p c) (hA : 0 < A) (B : ℝ) :
    HasPowerAsymptotics (fun x => f (A * x + B)) p (A ^ p * c) := by
  obtain ⟨D, a, hD, ha, har, hd, hl⟩ := hf
  have htop : Tendsto (fun x : ℝ => A * x + B) atTop atTop :=
    tendsto_atTop_add_const_right atTop B (Tendsto.const_mul_atTop hA tendsto_id)
  refine ⟨fun k x => A ^ k * D k (A * x + B), fun k => A ^ p * a k,
    by simp only [pow_zero, one_mul, hD], by simp only [ha], ?_, ?_, ?_⟩
  · intro k
    dsimp only
    rw [har]
    ring
  · intro k
    filter_upwards [htop.eventually (hd k)] with x hx
    have hs := (hx.comp x (((hasDerivAt_id x).const_mul A).add_const B)).const_mul (A ^ k)
    simpa only [Function.comp_def, id_eq, mul_one, pow_succ, mul_assoc, mul_comm,
      mul_left_comm] using hs
  · intro k
    have hlim := ((hl k).comp htop).mul (tendsto_affine_rpow_ratio (B := B) hA (p - k))
    have hlim' := hlim.const_mul (A ^ k)
    have hc : A ^ k * (a k * A ^ (p - k)) = A ^ p * a k := by
      rw [← Real.rpow_natCast A k, ← mul_assoc, mul_comm (A ^ (k : ℝ)) (a k), mul_assoc,
        ← Real.rpow_add hA]
      have he : (k : ℝ) + (p - k) = p := by ring
      rw [he]
      ring
    rw [hc] at hlim'
    apply hlim'.congr'
    filter_upwards [htop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    dsimp only [Function.comp_apply]
    have hn := ne_of_gt (Real.rpow_pos_of_pos hx (p - k))
    field_simp

/-- Unconditional mixed-power cancellation on every positive affine progression.
The top exponent is positive and noninteger, and its coefficient is nonzero. -/
theorem tendsto_mixed_power_average_affine {ι : Type*} (s : Finset ι) (c p : ι → ℝ)
    (j : ι) (hj : j ∈ s) (htop : ∀ i ∈ s, i ≠ j → p i < p j)
    (hc : c j ≠ 0) (m : ℕ) (hlo : (m : ℝ) < p j) (hhi : p j < m + 1)
    {A : ℝ} (hA : 0 < A) (B : ℝ) :
    Tendsto (average (fun n => phase (∑ i ∈ s, c i * (A * (n : ℝ) + B) ^ p i)))
      atTop (𝓝 0) := by
  exact ((hasPowerAsymptotics_mixed s c p j hj htop).affine hA B).cancellation
    (mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hA _)) hc) m hlo hhi

/-- Every nonzero combination of distinct positive noninteger powers cancels.
Zero coefficients are removed before selecting the largest exponent. -/
theorem tendsto_distinct_noninteger_power_average {ι : Type*} (s : Finset ι)
    (c p : ι → ℝ) (hinj : Set.InjOn p (↑s : Set ι))
    (hp : ∀ i ∈ s, 0 < p i ∧ ∀ m : ℕ, p i ≠ (m : ℝ))
    (hc : ∃ i ∈ s, c i ≠ 0) {A : ℝ} (hA : 0 < A) (B : ℝ) :
    Tendsto (average (fun n => phase (∑ i ∈ s, c i * (A * (n : ℝ) + B) ^ p i)))
      atTop (𝓝 0) := by
  classical
  let t := s.filter (fun i => c i ≠ 0)
  have ht : t.Nonempty := by
    obtain ⟨i, hi, hci⟩ := hc
    exact ⟨i, mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨j, hj, hmax⟩ := t.exists_max_image p ht
  have hj' := mem_filter.mp hj
  have htop : ∀ i ∈ t, i ≠ j → p i < p j := by
    intro i hi hij
    apply lt_of_le_of_ne (hmax i hi)
    exact fun he => hij (hinj (mem_filter.mp hi).1 hj'.1 he)
  have hpj := hp j hj'.1
  have hlo : (⌊p j⌋₊ : ℝ) < p j :=
    lt_of_le_of_ne (Nat.floor_le hpj.1.le) (hpj.2 ⌊p j⌋₊).symm
  have hlim := tendsto_mixed_power_average_affine t c p j hj htop hj'.2
    ⌊p j⌋₊ hlo (Nat.lt_floor_add_one (p j)) hA B
  have he (x : ℝ) : (∑ i ∈ t, c i * x ^ p i) = ∑ i ∈ s, c i * x ^ p i := by
    apply sum_subset (filter_subset _ _) (fun i _ hi => ?_)
    have hci : c i = 0 := by
      by_contra hn
      exact hi (mem_filter.mpr ⟨‹i ∈ s›, hn⟩)
    simp only [hci, zero_mul]
  simpa only [he] using hlim

end BTCalculus.PowerPhaseAsymptotics
