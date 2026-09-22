import BTCalculus.FourierBoxCounting
import BTCalculus.PowerPhaseAsymptotics

/-! # Frequencies of fixed boxes for distinct noninteger powers -/

noncomputable section

namespace BTCalculus.PowerBoxCounting

open Finset Filter
open scoped Topology
open BTCalculus.WeylDifferencing BTCalculus.PowerPhaseAsymptotics
open BTCalculus.FourierBoxCounting

/-- Every fixed half-open box has its volume as parameter density. -/
theorem tendsto_power_fract_box_count {d : Type*} [Fintype d]
    (p w : d → ℝ) (hinj : Function.Injective p)
    (hp : ∀ i, 0 < p i ∧ ∀ m : ℕ, p i ≠ (m : ℝ))
    (hw : ∀ i, w i ≠ 0) {A : ℝ} (hA : 0 < A) (B : ℝ)
    (a b : d → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i < b i) :
    Tendsto (fun N => (count (fun n => ∀ i,
      a i ≤ Int.fract (w i * (A * (n : ℝ) + B) ^ p i) ∧
      Int.fract (w i * (A * (n : ℝ) + B) ^ p i) < b i) N : ℝ) / N)
        atTop (𝓝 (∏ i, (b i - a i))) := by
  classical
  apply tendsto_fract_box_count _ _ a b ha hb hab
  intro k hk
  have hn : ∃ i ∈ (univ : Finset d), (k i : ℝ) * w i ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
    refine ⟨i, mem_univ i, mul_ne_zero ?_ (hw i)⟩
    exact_mod_cast hi
  simpa only [mul_assoc] using tendsto_distinct_noninteger_power_average univ
    (fun i => (k i : ℝ) * w i) p hinj.injOn (fun i _ => hp i) hn hA B

/-- Removing finitely many exceptional parameters preserves their frequency. -/
theorem density_congr_eventually {P Q : ℕ → Prop} {δ : ℝ}
    (hPQ : ∀ᶠ n in atTop, P n ↔ Q n)
    (hP : Tendsto (fun N => (count P N : ℝ) / N) atTop (𝓝 δ)) :
    Tendsto (fun N => (count Q N : ℝ) / N) atTop (𝓝 δ) := by
  classical
  have hzero : Tendsto (fun n => (if Q n then (1 : ℝ) else 0) -
      (if P n then (1 : ℝ) else 0)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hPQ.mono (fun n hn => by simp [hn]))
  have hsum (R : ℕ → Prop) (N : ℕ) :
      (∑ n ∈ range N, if R n then (1 : ℝ) else 0) = count R N := by
    simp [count, Finset.sum_boole]
  have h := hzero.cesaro.add hP
  simp only [sum_sub_distrib, hsum, zero_add] at h
  convert h using 1
  funext N
  ring

/-- Positive density supplies arbitrarily late parameters. -/
theorem exists_ge_of_density {P : ℕ → Prop} {δ : ℝ} (hδ : 0 < δ)
    (hP : Tendsto (fun N => (count P N : ℝ) / N) atTop (𝓝 δ)) (T : ℕ) :
    ∃ t, T ≤ t ∧ P t := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero : Tendsto (fun N => (count (fun _ => False) N : ℝ) / N) atTop (𝓝 0) := by
    simp [count]
  have h := density_congr_eventually (P := fun _ => False) (Q := P) ?_ hzero
  · exact hδ.ne' (tendsto_nhds_unique hP h)
  · filter_upwards [eventually_ge_atTop T] with t ht
    simp [hnone t ht]

/-- The number of parameter positions whose positive power start is at most X. -/
def powerCutoff (q d : ℕ) (X : ℝ) : ℕ :=
  ⌊(X ^ (d : ℝ)⁻¹ - 1) / q⌋₊ + 1

theorem lt_powerCutoff_iff {q d t : ℕ} (hq : 0 < q) (hd : 0 < d)
    {X : ℝ} (hX : 1 ≤ X) :
    t < powerCutoff q d X ↔ ((1 + q * t) ^ d : ℕ) ≤ X := by
  have hx : 0 ≤ X := by linarith
  have hroot : 1 ≤ X ^ (d : ℝ)⁻¹ := Real.one_le_rpow hX (by positivity)
  rw [powerCutoff, Nat.lt_succ_iff,
    Nat.le_floor_iff (div_nonneg (by linarith) (Nat.cast_nonneg q)),
    le_div_iff₀ (by positivity : (0 : ℝ) < q), le_sub_iff_add_le]
  have h := Real.le_rpow_inv_iff_of_pos (x := (1 + q * t : ℕ)) (y := X)
    (z := (d : ℝ)) (by positivity) hx (by positivity)
  rw [Real.rpow_natCast] at h
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow, mul_comm,
    add_comm] using h

theorem tendsto_powerCutoff (q d : ℕ) (hq : 0 < q) (hd : 0 < d) :
    Tendsto (powerCutoff q d) atTop atTop := by
  apply (tendsto_add_atTop_nat 1).comp
  apply tendsto_nat_floor_atTop.comp
  have hR := tendsto_rpow_atTop (by positivity : (0 : ℝ) < (d : ℝ)⁻¹)
  have hs : Tendsto (fun X : ℝ => X ^ (d : ℝ)⁻¹ - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [hR.eventually (eventually_ge_atTop (K + 1))] with X hX
    linarith
  exact hs.atTop_div_const (by positivity)

theorem tendsto_powerCutoff_div (q d : ℕ) (hq : 0 < q) (hd : 0 < d) :
    Tendsto (fun X : ℝ => (powerCutoff q d X : ℝ) / X ^ (d : ℝ)⁻¹)
      atTop (𝓝 (1 / (q : ℝ))) := by
  let R : ℝ → ℝ := fun X => X ^ (d : ℝ)⁻¹
  let Y : ℝ → ℝ := fun X => (R X - 1) / q
  have hR : Tendsto R atTop atTop := tendsto_rpow_atTop (by positivity)
  have hs : Tendsto (fun X => R X - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [hR.eventually (eventually_ge_atTop (K + 1))] with X hX
    linarith
  have hY : Tendsto Y atTop atTop := hs.atTop_div_const (by positivity)
  have hinv : Tendsto (fun X => 1 / R X) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hR
  have hydiv : Tendsto (fun X => Y X / R X) atTop (𝓝 (1 / (q : ℝ))) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hinv).div_const (q : ℝ)
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [hR.eventually (eventually_gt_atTop 0)] with X hX
    dsimp [Y]
    field_simp
  have hf := tendsto_nat_floor_div_atTop.comp hY
  have h := (hf.mul hydiv).add hinv
  simp only [one_mul, add_zero] at h
  apply h.congr'
  filter_upwards [hY.eventually (eventually_gt_atTop 0), hR.eventually (eventually_gt_atTop 0)] with X hy hx
  change (⌊Y X⌋₊ : ℝ) / Y X * (Y X / R X) + 1 / R X = _
  simp only [powerCutoff, Nat.cast_add, Nat.cast_one]
  change _ = ((⌊Y X⌋₊ : ℝ) + 1) / R X
  field_simp

/-- Distinct parameters give distinct starts. -/
theorem power_start_strictMono {q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    StrictMono (fun t : ℕ => (1 + q * t) ^ d) := by
  intro s t hst
  exact Nat.pow_lt_pow_left (by nlinarith) (by omega)

/-- The actual finite set of selected power starts. -/
def powerStarts (P : ℕ → Prop) (q d : ℕ) (X : ℝ) : Finset ℕ := by
  classical
  exact ((range (powerCutoff q d X)).filter P).image (fun t => (1 + q * t) ^ d)

theorem mem_powerStarts {P : ℕ → Prop} {q d n : ℕ} (hq : 0 < q) (hd : 0 < d)
    {X : ℝ} (hX : 1 ≤ X) :
    n ∈ powerStarts P q d X ↔ (n : ℝ) ≤ X ∧ ∃ t, P t ∧ n = (1 + q * t) ^ d := by
  classical
  simp only [powerStarts, Finset.mem_image, mem_filter, mem_range,
    lt_powerCutoff_iff hq hd hX]
  constructor
  · rintro ⟨t, ⟨ht, hP⟩, rfl⟩
    exact ⟨ht, t, hP, rfl⟩
  · rintro ⟨hn, t, hP, rfl⟩
    exact ⟨t, ⟨hn, hP⟩, rfl⟩

/-- A parameter density becomes the corresponding sparse-start asymptotic. -/
theorem tendsto_powerStarts_card {P : ℕ → Prop} {δ : ℝ} {q d : ℕ}
    (hq : 0 < q) (hd : 0 < d)
    (hP : Tendsto (fun N => (count P N : ℝ) / N) atTop (𝓝 δ)) :
    Tendsto (fun X : ℝ => ((powerStarts P q d X).card : ℝ) / X ^ (d : ℝ)⁻¹)
      atTop (𝓝 (δ / q)) := by
  classical
  have hc (X : ℝ) : (powerStarts P q d X).card = count P (powerCutoff q d X) := by
    exact Finset.card_image_of_injective _ (power_start_strictMono hq hd).injective
  have h := (hP.comp (tendsto_powerCutoff q d hq hd)).mul (tendsto_powerCutoff_div q d hq hd)
  simp only [mul_one_div] at h
  convert h using 1
  funext X
  rw [hc]
  have hn : (powerCutoff q d X : ℝ) ≠ 0 := by
    exact_mod_cast (by simp [powerCutoff] : powerCutoff q d X ≠ 0)
  simp only [Function.comp_def]
  field_simp

/-- Positive parameter density supplies a start in every sufficiently large relative interval. -/
theorem eventually_powerStarts_interval {P : ℕ → Prop} {δ c : ℝ} {q d : ℕ}
    (hq : 0 < q) (hd : 0 < d) (hδ : 0 < δ) (hc : 1 < c)
    (hP : Tendsto (fun N => (count P N : ℝ) / N) atTop (𝓝 δ)) :
    ∀ᶠ X : ℝ in atTop, ∃ n ∈ powerStarts P q d (c * X), X < (n : ℝ) := by
  have hc0 : 0 < c := by linarith
  have hp : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
  have hbase := tendsto_powerStarts_card hq hd hP
  have hscaled : Tendsto (fun X : ℝ => ((powerStarts P q d (c * X)).card : ℝ) /
      X ^ (d : ℝ)⁻¹) atTop (𝓝 ((δ / q) * c ^ (d : ℝ)⁻¹)) := by
    have h := (hbase.comp (tendsto_id.const_mul_atTop hc0)).mul_const (c ^ (d : ℝ)⁻¹)
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    simp only [Function.comp_def, id_eq, Real.mul_rpow hc0.le (by linarith : 0 ≤ X)]
    have hcp : c ^ (d : ℝ)⁻¹ ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
    field_simp
  have hpos : 0 < (δ / q) * c ^ (d : ℝ)⁻¹ - δ / q := by
    have hpow := Real.one_lt_rpow hc hp
    have hcoeff : 0 < δ / q := by positivity
    nlinarith
  have hdiff := (hscaled.sub hbase).eventually (Ioi_mem_nhds hpos)
  filter_upwards [hdiff, eventually_ge_atTop (1 : ℝ)] with X hdiff hX
  have hXp : 0 < X ^ (d : ℝ)⁻¹ := Real.rpow_pos_of_pos (by linarith) _
  have hcard : (powerStarts P q d X).card < (powerStarts P q d (c * X)).card := by
    have hh : ((powerStarts P q d X).card : ℝ) / X ^ (d : ℝ)⁻¹ <
        ((powerStarts P q d (c * X)).card : ℝ) / X ^ (d : ℝ)⁻¹ := by
      change 0 < _ - _ at hdiff
      linarith
    exact_mod_cast (div_lt_div_iff_of_pos_right hXp).1 hh
  have hnsub : ¬ powerStarts P q d (c * X) ⊆ powerStarts P q d X := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨n, hn, hn'⟩ := Finset.not_subset.mp hnsub
  refine ⟨n, hn, ?_⟩
  have hcX : 1 ≤ c * X := by nlinarith
  have hnmem := (mem_powerStarts hq hd hcX).1 hn
  by_contra hle
  exact hn' ((mem_powerStarts hq hd hX).2 ⟨by linarith, hnmem.2⟩)

end BTCalculus.PowerBoxCounting
