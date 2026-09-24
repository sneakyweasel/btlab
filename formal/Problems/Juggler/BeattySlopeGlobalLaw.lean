import Problems.Juggler.BeattySlopeWeakIdentification

/-!
# The empirical first-passage law exists at every real slope above one

At an irrational boundary the phases equidistribute and the existing theorem
gives the singular continuous law `passageLaw`. At a rational boundary `b/a`
the phases `((r*a) mod b)/b` are periodic, so by the rational phase theorem
the ratios are asymptotically periodic, and their empirical law converges to
the uniform law on the `b` right-trace values `F⁺(j/b) = F((j+1)/b)`. In both
cases the limit is the image of uniform phase measure under the left-continuous
profile, so one explicit formula `passageProfileLaw` covers every `α > 1`.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology Set MeasureTheory BeattyPhase
open scoped BoundedContinuousFunction

/-- The image of uniform phase measure under the jump profile, for every
boundary in `(0,1)`; outside that interval it is an unused default. -/
noncomputable def passageProfileLaw (β : ℝ) : ProbabilityMeasure ℝ :=
  if h : 0 < β ∧ β < 1 then
    unitPhaseLaw.map (passageProfile_monotone_all h.1 h.2).measurable.aemeasurable
  else unitPhaseLaw

/-- Integrals against the profile law are uniform phase averages of the profile. -/
theorem integral_passageProfileLaw {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (g : ℝ →ᵇ ℝ) :
    ∫ y, g y ∂(passageProfileLaw β : Measure ℝ) =
      ∫ t in Ioc (0 : ℝ) 1, g (passageProfile β t) := by
  rw [passageProfileLaw, dif_pos ⟨hβ0, hβ1⟩]
  exact integral_map_of_stronglyMeasurable (passageProfile_monotone_all hβ0 hβ1).measurable
    g.continuous.stronglyMeasurable

/-- At an irrational boundary the profile law is the singular law `passageLaw`. -/
theorem passageProfileLaw_irrational {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) : passageProfileLaw β = passageLaw hβ0 hβ1 hβ := by
  rw [passageProfileLaw, dif_pos ⟨hβ0, hβ1⟩]
  rfl

private theorem periodic_window {h : ℕ → ℝ} {b : ℕ} (hp : Function.Periodic h b) (N : ℕ) :
    ∑ i ∈ range b, h (N+i) = ∑ i ∈ range b, h i := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 := sum_range_succ' (fun i => h (N+i)) b
    have h2 := sum_range_succ (fun i => h (N+i)) b
    have h3 : h (N+b) = h N := hp N
    simp only [add_zero] at h1
    have he : ∑ i ∈ range b, h (N+1+i) = ∑ i ∈ range b, h (N+(i+1)) :=
      sum_congr rfl fun i _ => by rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [he, ← ih]
    linarith

private theorem periodic_cesaro {h : ℕ → ℝ} {b : ℕ} (hb : 0 < b)
    (hp : Function.Periodic h b) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, h n)/(N : ℝ)) atTop
      (𝓝 ((∑ n ∈ range b, h n)/(b : ℝ))) := by
  set c := (∑ n ∈ range b, h n)/(b : ℝ)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  let T : ℕ → ℝ := fun N => ∑ n ∈ range N, (h n - c)
  have hT : Function.Periodic T b := by
    intro N
    simp only [T]
    rw [sum_range_add, sum_sub_distrib (s := Finset.range b), periodic_window hp N, sum_const,
      card_range, nsmul_eq_mul]
    have hc : (b : ℝ)*c = ∑ n ∈ Finset.range b, h n := by
      simp only [c]
      field_simp
    rw [hc, sub_self, add_zero]
  set M := ∑ k ∈ range b, |T k|
  have hM (N : ℕ) : |T N| ≤ M := by
    rw [← hT.map_mod_nat N]
    exact single_le_sum (f := fun k => |T k|) (fun k _ => abs_nonneg _)
      (mem_range.2 (Nat.mod_lt N hb))
  have hz : Tendsto (fun N : ℕ => T N/(N : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => M/(N : ℝ)) (fun N => ?_)
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (hM N) (Nat.cast_nonneg N)
  have h := hz.const_add c
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [T, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  field_simp
  ring

/-- The empirical law of a real sequence with period `b > 0` converges
weakly to the empirical law of its first period, the uniform law on
`u 0, …, u (b-1)` counted with multiplicity. -/
theorem empiricalLaw_periodic_tendsto {u : ℕ → ℝ} {b : ℕ} (hb : 0 < b)
    (hu : Function.Periodic u b) :
    Tendsto (empiricalLaw u) atTop (𝓝 (empiricalLaw u (b-1))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  simp only [integral_empiricalLaw]
  rw [Nat.sub_add_cancel hb]
  have hh : Function.Periodic (fun n => g (u n)) b := fun n => by
    simp only [hu n]
  exact (periodic_cesaro hb hh).comp (tendsto_add_atTop_nat 1)

private theorem sum_mul_mod_perm {M : Type*} [AddCommMonoid M] {a b : ℕ} (hb : 0 < b)
    (hab : Nat.Coprime a b) (f : ℕ → M) :
    ∑ r ∈ Finset.range b, f (r*a % b) = ∑ j ∈ Finset.range b, f j := by
  have hinj : Set.InjOn (fun r => r*a % b) (Finset.range b) := by
    intro r hr s hs h
    have hm : r*a ≡ s*a [MOD b] := h
    have h' := Nat.ModEq.cancel_right_of_coprime hab.symm hm
    unfold Nat.ModEq at h'
    rwa [Nat.mod_eq_of_lt (mem_range.1 hr), Nat.mod_eq_of_lt (mem_range.1 hs)] at h'
  have himg : (Finset.range b).image (fun r => r*a % b) = Finset.range b := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨r, _, rfl⟩ := mem_image.1 hj
      exact mem_range.2 (Nat.mod_lt _ hb)
    · rw [card_image_of_injOn hinj]
  rw [← sum_image (f := f) hinj, himg]

/-- At a rational boundary `b/a` the right trace at `j/b` equals the
left-continuous profile at `(j+1)/b`, since all phases are multiples of `1/b`. -/
theorem passageProfileRight_rational {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    passageProfileRight ((b : ℝ)/a) ((j : ℝ)/b) =
      passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold passageProfileRight passageProfile BeattyPhase.jumpProfileRight BeattyPhase.jumpProfile
  congr 1
  apply tsum_congr
  intro r
  dsimp only
  simp only [passagePhase_rational ha hb]
  set q : ℕ := ((r+1)*a) % b
  have hiff : (q : ℝ)/b ≤ (j : ℝ)/b ↔ (q : ℝ)/b < (j+1 : ℝ)/b := by
    rw [div_le_div_iff_of_pos_right hbR, div_lt_div_iff_of_pos_right hbR]
    constructor
    · intro h
      linarith
    · intro h
      have h' : q < j+1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.mp h'
  simp only [hiff]

/-- Explicit rational law. For coprime `0 < b < a`, the empirical law of the
actual ratios at boundary `b/a` (slope `a/b`) converges weakly to the uniform
law on the `b` right-trace values `F⁺(j/b)`, `j < b`, i.e. the empirical law
of the first `b` of these values. -/
theorem passageRatio_law_rational {a b : ℕ} (hb : 0 < b) (hba : b < a)
    (hab : Nat.Coprime a b) :
    Tendsto (empiricalLaw (passageRatio ((b : ℝ)/a))) atTop
      (𝓝 (empiricalLaw (fun j : ℕ => passageProfileRight ((b : ℝ)/a) ((j : ℝ)/b)) (b-1))) := by
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ0 : 0 < (b : ℝ)/a := div_pos (by exact_mod_cast hb) haR
  have hβ1 : (b : ℝ)/a < 1 := (div_lt_one haR).2 (by exact_mod_cast hba)
  set w : ℕ → ℝ := fun j => passageProfileRight ((b : ℝ)/a) ((j : ℝ)/b)
  set v : ℕ → ℝ := fun r => w (r*a % b)
  have hv (r : ℕ) : passageProfileRight ((b : ℝ)/a) (passagePhase ((b : ℝ)/a) r) = v r := by
    simp only [v, w, passagePhase_rational ha hb]
  have hper : Function.Periodic v b := by
    intro r
    simp only [v, add_mul, Nat.add_mul_mod_self_left]
  have hlaw : empiricalLaw v (b-1) = empiricalLaw w (b-1) := by
    apply Subtype.ext
    simp only [empiricalLaw, Nat.sub_add_cancel hb]
    congr 1
    exact sum_mul_mod_perm hb hab (fun j => Measure.dirac (w j))
  rw [← hlaw]
  apply empiricalLaw_tendsto_of_sub_tendsto_zero (empiricalLaw_periodic_tendsto hb hper)
  simpa only [hv] using passageRatio_sub_right_tendsto hβ0 hβ1

/-- The rational limit law is the profile law: its bounded continuous
integrals are the uniform averages over the values `F((j+1)/b)`. -/
theorem passageProfileLaw_rational {a b : ℕ} (hb : 0 < b) (hba : b < a) (g : ℝ →ᵇ ℝ) :
    ∫ y, g y ∂(passageProfileLaw ((b : ℝ)/a) : Measure ℝ) =
      (1/(b : ℝ))*∑ j ∈ range b, g (passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b)) := by
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ0 : 0 < (b : ℝ)/a := div_pos (by exact_mod_cast hb) haR
  have hβ1 : (b : ℝ)/a < 1 := (div_lt_one haR).2 (by exact_mod_cast hba)
  rw [integral_passageProfileLaw hβ0 hβ1, passageLaw_rational_eq ha hb]

private theorem law_rational_profile {a b : ℕ} (hb : 0 < b) (hba : b < a)
    (hab : Nat.Coprime a b) :
    Tendsto (empiricalLaw (passageRatio ((b : ℝ)/a))) atTop
      (𝓝 (passageProfileLaw ((b : ℝ)/a))) := by
  have ha : 0 < a := hb.trans hba
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (passageRatio_law_rational hb hba hab)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have hg := h g
  rw [integral_empiricalLaw, Nat.sub_add_cancel hb] at hg
  rw [passageProfileLaw_rational hb hba]
  convert hg using 2
  simp only [passageProfileRight_rational ha hb]
  ring

/-- Every boundary `0 < β < 1`, rational or irrational: the empirical law
of the actual ratios converges weakly to the image of uniform phase measure
under the explicit left-continuous profile. -/
theorem passageRatio_law_tendsto {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (empiricalLaw (passageRatio β)) atTop (𝓝 (passageProfileLaw β)) := by
  by_cases hβ : Irrational β
  · rw [passageProfileLaw_irrational hβ0 hβ1 hβ]
    exact passageRatio_empiricalLaw_tendsto hβ0 hβ1 hβ
  · obtain ⟨q, rfl⟩ : ∃ q : ℚ, (q : ℝ) = β := by
      unfold Irrational at hβ
      simpa using hβ
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hβ0
    have hq1 : q < 1 := by exact_mod_cast hβ1
    have hnum : 0 < q.num := Rat.num_pos.2 hq0
    set b := q.num.natAbs
    set a := q.den
    have hb : 0 < b := Int.natAbs_pos.2 hnum.ne'
    have hbZ : (b : ℤ) = q.num := Int.natAbs_of_nonneg hnum.le
    have hq : (q : ℝ) = (b : ℝ)/a := by
      rw [Rat.cast_def]
      congr 1
      exact_mod_cast hbZ.symm
    have hba : b < a := by
      have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero q.den_nz
      have h1 : (b : ℝ)/a < 1 := hq ▸ hβ1
      exact_mod_cast (div_lt_one haR).1 h1
    have hab : Nat.Coprime a b := q.reduced.symm
    rw [hq]
    exact law_rational_profile hb hba hab

/-- The global law for every real slope `α > 1`, rational or irrational:
the empirical law of `passageRatio (1/α)` converges weakly to the explicit
profile law at boundary `1/α`. -/
theorem passageRatio_law_slope {α : ℝ} (hα : 1 < α) :
    Tendsto (empiricalLaw (passageRatio (1/α))) atTop (𝓝 (passageProfileLaw (1/α))) := by
  have hα0 : 0 < α := by linarith
  exact passageRatio_law_tendsto (one_div_pos.2 hα0) ((div_lt_one hα0).2 hα)

/-- Existence form: for every real `α > 1` the empirical law of the actual
first-passage ratios converges weakly to some probability measure. -/
theorem exists_passageRatio_law {α : ℝ} (hα : 1 < α) :
    ∃ μ : ProbabilityMeasure ℝ,
      Tendsto (empiricalLaw (passageRatio (1/α))) atTop (𝓝 μ) :=
  ⟨_, passageRatio_law_slope hα⟩

end Problems.Juggler.BeattySlope
