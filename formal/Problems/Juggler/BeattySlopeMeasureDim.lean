import Problems.Juggler.BeattySlopePacking
import Problems.Juggler.BeattySlopeCFExpansion

/-!
# The Hausdorff dimension of the limit law

The limit law `μ_α` of the normalized first-passage counts lives on the
cluster set `K_α`. Its lower Hausdorff dimension, the least Hausdorff
dimension of a set of positive `μ_α`-measure, is `2/(1+ω)` for every
irrational slope, where `ω` is the irrationality exponent of `α`.

The lower bound is the Hölder estimate for the distribution function. The
upper bound uses one good approximation `|qα - p| = |θ|` at a time: the first
`q` orbit points cut the circle into cells of length about `1/q`, and later
points march through each cell in steps `|θ|`. Half of every cell is not
reached before index `N ≈ 1/(2|θ|)`, and since a window of length `1/(2q)`
receives at most two atoms from every block of `q` consecutive indices, its
atom mass is at most `6B/(q√N)`. The `q` windows carry half of the phase
measure, and their images have length about `q⁻¹|θ|^(1/2)`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

/-- **Window mass.** A window of length at most `1/(2q)` that no index below
`N ≥ q` hits carries atom mass at most `6B/(q√N)`, when the weights are at
most `B(n+1)^(-3/2)` and the orbit is `1/(2q)`-separated along blocks of `q`
consecutive indices. -/
theorem window_mass_le {φ w : ℕ → ℝ} {α B : ℝ} (hn : ∀ n, 0 ≤ w n) (hB : 0 ≤ B)
    (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ))
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α)) {q : ℕ} (hq : 0 < q)
    (hsep : ∀ m : ℕ, 0 < m → m < q → ∀ p : ℤ, 1 / (2 * (q : ℝ)) ≤ |(m : ℝ) * α - p|)
    {N : ℕ} (hNq : q ≤ N) {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 1 / (2 * (q : ℝ)))
    (hearly : ∀ k, k < N → φ k ∉ Ioo a b) :
    ∑' n, (if φ n ∈ Ioo a b then w n else 0) ≤ 6 * B / q * (N : ℝ) ^ (-(1/2) : ℝ) := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : 0 < N := lt_of_lt_of_le hq hNq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  set v : ℕ → ℝ := fun n => B / ((n : ℝ) + 1) ^ (3/2 : ℝ) with hvdef
  have hv0 (n : ℕ) : 0 ≤ v n := div_nonneg hB (by positivity)
  have hvanti {m n : ℕ} (h : m ≤ n) : v n ≤ v m := by
    apply div_le_div_of_nonneg_left hB (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have : (m : ℝ) ≤ n := by exact_mod_cast h
    linarith
  have hvs : Summable v := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ (3/2 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.2 (by norm_num)
    have h2 := (summable_nat_add_iff 1).2 h1
    refine (h2.mul_left B).congr fun n => ?_
    simp only [hvdef, div_eq_mul_inv]
    push_cast
    ring_nf
  set f : ℕ → ℝ := fun n => if φ n ∈ Ioo a b then w n else 0 with hfdef
  have hf0 (n : ℕ) : 0 ≤ f n := by simp only [hfdef]; split_ifs <;> simp [hn n]
  -- one block of `q` consecutive indices
  have hblock (t : ℕ) : ∑ i ∈ Finset.range q, f (t + i) ≤ 2 * v t := by
    have hcount := block_count_le (δ := 1 / (2 * (q : ℝ))) (L := 1 / (2 * (q : ℝ)))
      (by positivity) hfr hsep hab hlen t
    have hc2 : (((Finset.range q).filter (fun j => φ (t + j) ∈ Ioo a b)).card : ℝ) ≤ 2 := by
      have : 1 / (2 * (q : ℝ)) / (1 / (2 * (q : ℝ))) = 1 := div_self (by positivity)
      linarith
    calc ∑ i ∈ Finset.range q, f (t + i)
        = ∑ i ∈ (Finset.range q).filter (fun j => φ (t + j) ∈ Ioo a b), w (t + i) := by
          rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ (Finset.range q).filter (fun j => φ (t + j) ∈ Ioo a b), v t := by
          exact Finset.sum_le_sum fun i _ => (hb _).trans (by
            have := hvanti (Nat.le_add_right t i)
            simp only [hvdef] at this ⊢
            push_cast at this ⊢
            exact this)
      _ = _ * v t := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * v t := mul_le_mul_of_nonneg_right hc2 (hv0 t)
  -- all blocks after `N`
  have hblocks (J : ℕ) : ∑ k ∈ Finset.range (J * q + q), f (N + k) ≤
      2 * v N + 2 / q * ∑ k ∈ Finset.range (J * q), v (N + k) := by
    induction J with
    | zero => simpa using hblock N
    | succ J ih =>
      have hL : ∑ k ∈ Finset.range ((J + 1) * q + q), f (N + k) =
          ∑ k ∈ Finset.range (J * q + q), f (N + k) +
            ∑ i ∈ Finset.range q, f (N + (J * q + q + i)) := by
        rw [show (J + 1) * q + q = (J * q + q) + q by ring, Finset.sum_range_add]
      have hR : ∑ k ∈ Finset.range ((J + 1) * q), v (N + k) =
          ∑ k ∈ Finset.range (J * q), v (N + k) +
            ∑ i ∈ Finset.range q, v (N + (J * q + i)) := by
        rw [show (J + 1) * q = J * q + q by ring, Finset.sum_range_add]
      have hb2 : ∑ i ∈ Finset.range q, f (N + (J * q + q + i)) ≤ 2 * v (N + (J * q + q)) := by
        simpa [add_assoc] using hblock (N + (J * q + q))
      have hcmp : 2 * v (N + (J * q + q)) ≤
          2 / q * ∑ i ∈ Finset.range q, v (N + (J * q + i)) := by
        have : (q : ℝ) * v (N + (J * q + q)) ≤ ∑ i ∈ Finset.range q, v (N + (J * q + i)) := by
          have := Finset.card_nsmul_le_sum (Finset.range q) (fun i => v (N + (J * q + i)))
            (v (N + (J * q + q))) fun i hi => hvanti (by
              have := Finset.mem_range.1 hi; omega)
          simpa using this
        rw [div_mul_eq_mul_div, le_div_iff₀ hqR]
        nlinarith
      rw [hL, hR, mul_add]
      linarith

  -- the tail of `v`
  have htail (M : ℕ) : ∑ k ∈ Finset.range M, v (N + k) ≤ 2 * B * (N : ℝ) ^ (-(1/2) : ℝ) := by
    have ht := tailMass_le hvs hv0 hB (fun n => le_rfl) hN0
    refine le_trans ?_ ht
    have hs : Summable (fun n => if N ≤ n then v n else 0) :=
      hvs.of_norm_bounded fun n => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hv0 n), hv0 n]
    calc ∑ k ∈ Finset.range M, v (N + k)
        = ∑ n ∈ Finset.range (N + M), if N ≤ n then v n else 0 := by
          rw [Finset.sum_range_add]
          have h0 : ∑ n ∈ Finset.range N, (if N ≤ n then v n else 0) = 0 :=
            Finset.sum_eq_zero fun n hn => by
              rw [if_neg (not_le.2 (Finset.mem_range.1 hn))]
          rw [h0, zero_add]
          exact Finset.sum_congr rfl fun k _ => by rw [if_pos (Nat.le_add_right N k)]
      _ ≤ tailMass v N :=
          hs.sum_le_tsum _ fun n _ => by split_ifs <;> simp [hv0 n]
  -- the head term
  have hhead : 2 * v N ≤ 2 * B / q * (N : ℝ) ^ (-(1/2) : ℝ) := by
    simp only [hvdef]
    have hNq' : (q : ℝ) ≤ N := by exact_mod_cast hNq
    have h1 : (N : ℝ) ^ (3/2 : ℝ) ≤ ((N : ℝ) + 1) ^ (3/2 : ℝ) :=
      Real.rpow_le_rpow hNR.le (by linarith) (by norm_num)
    have h2 : (N : ℝ) ^ (3/2 : ℝ) = N * (N : ℝ) ^ (1/2 : ℝ) := by
      rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hNR, Real.rpow_one]
    have h3 : (N : ℝ) ^ (-(1/2) : ℝ) = ((N : ℝ) ^ (1/2 : ℝ))⁻¹ := Real.rpow_neg hNR.le _
    have hsq : 0 < (N : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hNR _
    rw [h3]
    rw [show 2 * (B / ((N : ℝ) + 1) ^ (3/2 : ℝ)) = 2 * B / ((N : ℝ) + 1) ^ (3/2 : ℝ) by ring,
      show 2 * B / (q : ℝ) * ((N : ℝ) ^ (1/2 : ℝ))⁻¹ = 2 * B / (q * (N : ℝ) ^ (1/2 : ℝ)) by
        field_simp]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    calc (q : ℝ) * (N : ℝ) ^ (1/2 : ℝ) ≤ N * (N : ℝ) ^ (1/2 : ℝ) :=
          mul_le_mul_of_nonneg_right hNq' hsq.le
      _ = _ := h2.symm
      _ ≤ _ := h1
  -- assemble
  refine Real.tsum_le_of_sum_range_le hf0 fun M => ?_
  have hsub : ∑ n ∈ Finset.range M, f n ≤ ∑ n ∈ Finset.range (N + (M * q + q)), f n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 ?_)
      fun n _ _ => hf0 n
    nlinarith
  have hsplit : ∑ n ∈ Finset.range (N + (M * q + q)), f n =
      ∑ k ∈ Finset.range (M * q + q), f (N + k) := by
    rw [Finset.sum_range_add]
    have : ∑ n ∈ Finset.range N, f n = 0 := Finset.sum_eq_zero fun n hn => by
      simp only [hfdef, if_neg (hearly n (Finset.mem_range.1 hn))]
    rw [this, zero_add]
  have hB2 := hblocks M
  have hT := htail (M * q)
  have hfac : 0 ≤ 2 / (q : ℝ) := by positivity
  calc ∑ n ∈ Finset.range M, f n ≤ _ := hsub
    _ = _ := hsplit
    _ ≤ 2 * v N + 2 / q * ∑ k ∈ Finset.range (M * q), v (N + k) := hB2
    _ ≤ 2 * B / q * (N : ℝ) ^ (-(1/2) : ℝ) + 2 / q * (2 * B * (N : ℝ) ^ (-(1/2) : ℝ)) :=
        add_le_add hhead (mul_le_mul_of_nonneg_left hT hfac)
    _ = 6 * B / q * (N : ℝ) ^ (-(1/2) : ℝ) := by ring

/-! ### One approximation level -/

/-- The window offset: windows sit in the half of each cell that the orbit
reaches last. -/
noncomputable def levelShift (θ : ℝ) : ℝ := if 0 < θ then 1/2 else 0

/-- Left end of the `i`-th window at level `q` with signed error `θ`. -/
noncomputable def levelLeft (q : ℕ) (θ : ℝ) (i : ℕ) : ℝ := ((i : ℝ) + levelShift θ) / q

private theorem int_between {z : ℤ} {n : ℕ} (h1 : (n : ℝ) < z) (h2 : (z : ℝ) < n + 1) : False := by
  have a : (n : ℤ) < z := by exact_mod_cast h1
  have b : z < (n : ℤ) + 1 := by exact_mod_cast h2
  omega

/-- **Late windows.** Before the orbit index reaches `1/(2|θ|)`, no orbit
point enters any window. -/
theorem level_early_avoid {φ : ℕ → ℝ} {α : ℝ}
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α)) {q : ℕ} (hq : 0 < q) {p : ℤ}
    (hθ : (q : ℝ) * α - p ≠ 0) {k : ℕ} (hk : ((k : ℝ) + 1) * |(q : ℝ) * α - p| ≤ 1/2)
    (i : ℕ) : φ k ∉ Ioo (levelLeft q ((q : ℝ) * α - p) i)
      (levelLeft q ((q : ℝ) * α - p) i + 1 / (2 * (q : ℝ))) := by
  set θ := (q : ℝ) * α - p with hθdef
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set Z : ℤ := ((k : ℤ) + 1) * p - q * ⌊((k : ℝ) + 1) * α⌋
  have hZ : (q : ℝ) * φ k = Z + ((k : ℝ) + 1) * θ := by
    rw [hfr k, Int.fract, hθdef]
    push_cast [Z]
    ring
  rintro ⟨h1, h2⟩
  have e1 : (q : ℝ) * levelLeft q θ i = i + levelShift θ := by
    unfold levelLeft; field_simp
  have e2 : (q : ℝ) * (1 / (2 * (q : ℝ))) = 1/2 := by field_simp
  have g1 : (i : ℝ) + levelShift θ < Z + ((k : ℝ) + 1) * θ := by
    rw [← e1, ← hZ]; exact mul_lt_mul_of_pos_left h1 hqR
  have g2 : Z + ((k : ℝ) + 1) * θ < (i : ℝ) + levelShift θ + 1/2 := by
    rw [← e1, ← e2, ← mul_add, ← hZ]; exact mul_lt_mul_of_pos_left h2 hqR
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hs : levelShift θ = 0 := by simp [levelShift, not_lt.2 hneg.le]
    rw [hs] at g1 g2
    have ht : -(1/2) ≤ ((k : ℝ) + 1) * θ := by
      rw [abs_of_neg hneg] at hk; linarith
    have ht' : ((k : ℝ) + 1) * θ < 0 := mul_neg_of_pos_of_neg hk0 hneg
    exact int_between (n := i) (by linarith) (by linarith)
  · have hs : levelShift θ = 1/2 := by simp [levelShift, hpos]
    rw [hs] at g1 g2
    have ht : ((k : ℝ) + 1) * θ ≤ 1/2 := by
      rw [abs_of_pos hpos] at hk; linarith
    have ht' : 0 < ((k : ℝ) + 1) * θ := mul_pos hk0 hpos
    exact int_between (n := i) (by linarith) (by linarith)

/-- The windows of one level lie in consecutive cells of the unit interval. -/
theorem levelLeft_bounds {q : ℕ} (hq : 0 < q) (θ : ℝ) (i : ℕ) :
    (i : ℝ) / q ≤ levelLeft q θ i ∧ levelLeft q θ i + 1 / (2 * (q : ℝ)) ≤ ((i : ℝ) + 1) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : 0 ≤ levelShift θ := by unfold levelShift; split_ifs <;> norm_num
  have hs1 : levelShift θ ≤ 1/2 := by unfold levelShift; split_ifs <;> norm_num
  unfold levelLeft
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) hqR.le
  · rw [div_add_div _ _ hqR.ne' (by positivity), div_le_div_iff₀ (by positivity) hqR]
    nlinarith [mul_le_mul_of_nonneg_right hs1 (mul_nonneg hqR.le hqR.le)]

/-- **Good approximations are convergents.** If `|qα - p| ≤ q^(-ν)` for
arbitrarily large `q`, then arbitrarily large continued-fraction denominators
satisfy the same bound. -/
theorem good_cf_level {α ν : ℝ} (hα : Irrational α) (h0 : 0 < α) (hν : 0 < ν)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-ν))
    (Q₀ : ℕ) : ∃ n : ℕ, Q₀ < cfDen (cfDigits α) (n + 1) ∧
      |(cfDen (cfDigits α) (n + 1) : ℝ) * α - cfNum (cfDigits α) (n + 1)| ≤
        (cfDen (cfDigits α) (n + 1) : ℝ) ^ (-ν) := by
  classical
  set a := cfDigits α
  have ha : ∀ k, 1 ≤ a (k + 1) := cfDigits_succ_ge hα
  have hL : cfLim a = α := cfLim_cfDigits hα h0.le
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((cfDen_tendsto ha).eventually_gt_atTop Q₀)
  set η := (Finset.range (K + 1)).inf' ⟨0, by simp⟩ (cfErr a) with hηdef
  have hη : 0 < η := (Finset.lt_inf'_iff _).2 fun k _ => cfErr_pos ha k
  have hsmall : Tendsto (fun q : ℕ => (q : ℝ) ^ (-ν)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hν).comp tendsto_natCast_atTop_atTop
  obtain ⟨Q', hQ'⟩ := eventually_atTop.1 ((tendsto_order.1 hsmall).2 η hη)
  obtain ⟨q, hqQ, p, hqp⟩ := happ Q'
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hqQ
  have hlt : |(q : ℝ) * α - p| < η := hqp.trans_lt (hQ' q hqQ.le)
  have hex : ∃ j, q < cfDen a (j + 1) := by
    obtain ⟨j, hj⟩ := eventually_atTop.1 ((cfDen_tendsto ha).eventually_gt_atTop q)
    exact ⟨j, hj (j + 1) (Nat.le_succ j)⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀spec : q < cfDen a (j₀ + 1) := Nat.find_spec hex
  have hj₀pos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · rw [h] at hj₀spec
      simp [cfDen] at hj₀spec
      omega
    · exact h
  set k := j₀ - 1
  have hk1 : k + 1 = j₀ := by omega
  have hkle : cfDen a (k + 1) ≤ q := by
    have := Nat.find_min hex (show k < j₀ by omega)
    omega
  have hklt : q < cfDen a (k + 1 + 1) := by rw [hk1]; exact hj₀spec
  have hbest := cf_best_approx ha (k + 1) q hq hklt p
  rw [hL] at hbest
  have herr : |(cfDen a (k + 1) : ℝ) * α - cfNum a (k + 1)| = cfErr a (k + 1) := by
    rw [← hL]; exact abs_cf_err ha (k + 1)
  have hQpos : (0 : ℝ) < cfDen a (k + 1) := by exact_mod_cast cfDen_succ_pos ha k
  refine ⟨k, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    have hkK : k + 1 < K := by
      by_contra h'
      exact absurd (hK (k + 1) (not_lt.1 h')) (not_lt.2 hc)
    have hge : η ≤ cfErr a (k + 1) :=
      Finset.inf'_le _ (Finset.mem_range.2 (by omega))
    linarith
  · rw [herr]
    refine hbest.trans (hqp.trans ?_)
    exact Real.rpow_le_rpow_of_nonpos hQpos (by exact_mod_cast hkle) (by linarith)

section Passage

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- The distribution function spreads every set of positive law mass over a
set of positive Lebesgue measure. -/
theorem passageCdf_image_volume_pos {E : Set ℝ} (hE : MeasurableSet E)
    (hμ : 0 < (passageLaw hβ0 hβ1 hβ : Measure ℝ) E) :
    0 < volume (passageCdf hβ0 hβ1 hβ '' E) := by
  have hmeas := (passageProfile_monotone hβ0 hβ1 hβ).measurable
  have hmap : (passageLaw hβ0 hβ1 hβ : Measure ℝ) E =
      volume (passageProfile β ⁻¹' E ∩ Ioc 0 1) := by
    rw [passageLaw, ProbabilityMeasure.toMeasure_map, Measure.map_apply hmeas hE]
    exact Measure.restrict_apply (hmeas hE)
  rw [hmap] at hμ
  refine hμ.trans_le (measure_mono ?_)
  rintro t ⟨htE, ht⟩
  exact ⟨passageProfile β t, htE, passageCdf_profile hβ0 hβ1 hβ ⟨ht.1.le, ht.2⟩⟩

/-- **Lower bound for the law.** Under a Diophantine lower bound of exponent
`τ`, every measurable set of positive law mass has Hausdorff dimension at
least `2/(2+τ)`. -/
theorem passageLaw_dimH_ge {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hdio : DiophantineLowerBound (1/β) c τ) {E : Set ℝ} (hE : MeasurableSet E)
    (hμ : 0 < (passageLaw hβ0 hβ1 hβ : Measure ℝ) E) :
    ENNReal.ofReal ((2 : ℝ)/(2+τ)) ≤ dimH E := by
  obtain ⟨C, hC⟩ := passageCdf_holder_sharp hβ0 hβ1 hβ hc hτ hdio
  let r : ℝ≥0 := ⟨(2 : ℝ)/(2+τ), by positivity⟩
  have hr : 0 < r := by change (0 : ℝ) < (2 : ℝ)/(2+τ); positivity
  change HolderWith C r (passageCdf hβ0 hβ1 hβ) at hC
  have h := hC.dimH_image_le hr E
  have h1 : (1 : ℝ≥0∞) ≤ dimH (passageCdf hβ0 hβ1 hβ '' E) := by
    have hpos := passageCdf_image_volume_pos hβ0 hβ1 hβ hE hμ
    have hne : Measure.hausdorffMeasure ((1 : ℝ≥0) : ℝ) (passageCdf hβ0 hβ1 hβ '' E) ≠ 0 := by
      rw [NNReal.coe_one, hausdorffMeasure_real]
      exact hpos.ne'
    simpa using le_dimH_of_hausdorffMeasure_ne_zero hne
  have h2 := h1.trans h
  have hh' := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hr.ne'))
    (Or.inl ENNReal.coe_ne_top)).1 h2
  rw [one_mul, ← ENNReal.ofReal_coe_nnreal] at hh'
  exact hh'

omit hβ1 hβ in
/-- The phases of the passage profile are the rotation orbit of `1/β`. -/
theorem passagePhase_succ_fract (k : ℕ) :
    passagePhase β (k+1) = Int.fract (((k : ℝ) + 1) * (1/β)) := by
  rw [passagePhase_eq_fract hβ0]
  push_cast
  congr 1
  field_simp

/-- The image cover of one level: the profile images of the `q` windows. -/
noncomputable def levelSet (β : ℝ) (q : ℕ) (θ : ℝ) : Set ℝ :=
  ⋃ i ∈ Finset.range q, Icc
    (jumpProfileRight (fun r => passagePhase β (r+1)) (fun r => passageJumpWeight β (r+1))
      (levelLeft q θ i))
    (passageProfile β (levelLeft q θ i + 1 / (2 * (q : ℝ))))

omit hβ0 hβ1 hβ in
/-- The image cover of one level is a finite union of closed intervals. -/
theorem levelSet_measurable (q : ℕ) (θ : ℝ) : MeasurableSet (levelSet β q θ) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Icc

/-- **One level.** At a good approximation `|q/β - p| = |θ|` with
`q ≤ N = ⌊1/(2|θ|)⌋`, each window image has length at most `6B/(q√N)`, and the
windows carry law mass at least `1/2`. -/
theorem passage_level {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ n, passageJumpWeight β (n+1) ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ))
    {q : ℕ} (hq : 0 < q)
    (hsep : ∀ m : ℕ, 0 < m → m < q → ∀ p : ℤ, 1 / (2 * (q : ℝ)) ≤ |(m : ℝ) * (1/β) - p|)
    {p : ℤ} (hθ : (q : ℝ) * (1/β) - p ≠ 0)
    (hN : q ≤ ⌊1 / (2 * |(q : ℝ) * (1/β) - p|)⌋₊) :
    (∀ i, passageProfile β (levelLeft q ((q : ℝ) * (1/β) - p) i + 1 / (2 * (q : ℝ))) -
        jumpProfileRight (fun r => passagePhase β (r+1)) (fun r => passageJumpWeight β (r+1))
          (levelLeft q ((q : ℝ) * (1/β) - p) i) ≤
        6 * B / q * (⌊1 / (2 * |(q : ℝ) * (1/β) - p|)⌋₊ : ℝ) ^ (-(1/2) : ℝ)) ∧
    ENNReal.ofReal (1/2) ≤
      (passageLaw hβ0 hβ1 hβ : Measure ℝ) (levelSet β q ((q : ℝ) * (1/β) - p)) := by
  classical
  set θ := (q : ℝ) * (1/β) - p with hθdef
  set N := ⌊1 / (2 * |θ|)⌋₊ with hNdef
  set φ : ℕ → ℝ := fun r => passagePhase β (r+1)
  set w : ℕ → ℝ := fun r => passageJumpWeight β (r+1)
  have hw : Summable w := (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
  have hn : ∀ n, 0 ≤ w n := fun n => passageJumpWeight_nonneg hβ0 hβ1 _
  have hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * (1/β)) :=
    passagePhase_succ_fract hβ0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have habs : 0 < |θ| := abs_pos.2 hθ
  have hearly (i : ℕ) : ∀ k, k < N → φ k ∉ Ioo (levelLeft q θ i) (levelLeft q θ i + 1 / (2 * (q : ℝ))) := by
    intro k hk
    apply level_early_avoid hfr hq hθ _ i
    have h1 : ((k : ℝ) + 1) ≤ N := by exact_mod_cast hk
    have h2 : (N : ℝ) ≤ 1 / (2 * |θ|) := Nat.floor_le (by positivity)
    have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) habs.le
    rwa [show 1 / (2 * |θ|) * |θ| = 1/2 by field_simp] at h3
  refine ⟨fun i => ?_, ?_⟩
  · have hg := jumpGap_mass_le hw hn (phase := φ) (c := levelLeft q θ i)
      (d := levelLeft q θ i + 1 / (2 * (q : ℝ))) (fun n => φ n ∈ Ioo (levelLeft q θ i)
        (levelLeft q θ i + 1 / (2 * (q : ℝ)))) fun n h1 h2 => ⟨h1, h2⟩
    have hm := window_mass_le hn hB hb hfr hq hsep hN
      (by have : (0 : ℝ) ≤ 1 / (2 * (q : ℝ)) := by positivity
          linarith) (by linarith) (hearly i)
    exact hg.trans hm
  · -- the law mass of the windows
    have hmeas := (passageProfile_monotone hβ0 hβ1 hβ).measurable
    have hmap : (passageLaw hβ0 hβ1 hβ : Measure ℝ) (levelSet β q θ) =
        volume (passageProfile β ⁻¹' levelSet β q θ ∩ Ioc 0 1) := by
      rw [passageLaw, ProbabilityMeasure.toMeasure_map,
        Measure.map_apply hmeas (levelSet_measurable q θ)]
      exact Measure.restrict_apply (hmeas (levelSet_measurable q θ))
    rw [hmap]
    set W : ℕ → Set ℝ := fun i => Ioo (levelLeft q θ i) (levelLeft q θ i + 1 / (2 * (q : ℝ)))
    have hsub : (⋃ i ∈ Finset.range q, W i) ⊆ passageProfile β ⁻¹' levelSet β q θ ∩ Ioc 0 1 := by
      intro t ht
      obtain ⟨i, hi, htW⟩ := mem_iUnion₂.1 ht
      have hib := levelLeft_bounds hq θ i
      have hi' : (i : ℝ) + 1 ≤ q := by exact_mod_cast Finset.mem_range.1 hi
      have hi0 : (0 : ℝ) ≤ (i : ℝ) / q := by positivity
      have hi1 : ((i : ℝ) + 1) / q ≤ 1 := by rw [div_le_one hqR]; exact hi'
      refine ⟨mem_iUnion₂.2 ⟨i, hi, ?_, ?_⟩, by linarith [htW.1], by linarith [htW.2]⟩
      · exact jumpProfileRight_le_of_lt hw hn htW.1
      · exact passageProfile_monotone hβ0 hβ1 hβ htW.2.le
    refine le_trans ?_ (measure_mono hsub)
    have hdisj : (Finset.range q : Set ℕ).PairwiseDisjoint W := by
      intro i _ j _ hij
      have hbi := levelLeft_bounds hq θ i
      have hbj := levelLeft_bounds hq θ j
      rcases lt_or_gt_of_ne hij with h | h
      · have : ((i : ℝ) + 1) / q ≤ (j : ℝ) / q :=
          div_le_div_of_nonneg_right (by exact_mod_cast h) hqR.le
        exact disjoint_left.2 fun x hx hx' => by
          simp only [W, mem_Ioo] at hx hx'; linarith [hx.2, hx'.1]
      · have : ((j : ℝ) + 1) / q ≤ (i : ℝ) / q :=
          div_le_div_of_nonneg_right (by exact_mod_cast h) hqR.le
        exact disjoint_left.2 fun x hx hx' => by
          simp only [W, mem_Ioo] at hx hx'; linarith [hx.1, hx'.2]
    rw [measure_biUnion_finset hdisj (fun i _ => measurableSet_Ioo)]
    have hvol (i : ℕ) : volume (W i) = ENNReal.ofReal (1 / (2 * (q : ℝ))) := by
      simp only [W, Real.volume_Ioo]
      ring_nf
    simp only [hvol, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (q : ℝ) * (1 / (2 * (q : ℝ))) = 1/2 by field_simp]

/-- Arbitrarily fine good levels: for every `j` some continued-fraction level
has window images of length at most `2^(-j)` whose `s`-powers sum to at most
`2^(-j)`. -/
theorem exists_fine_level {B ν s : ℝ} (hB : 0 < B) (hν : 1 < ν) (hs : 2 / (2 + ν) < s)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * (1/β) - p| ≤ (q : ℝ) ^ (-ν))
    (j : ℕ) : ∃ n : ℕ,
      let Q := cfDen (cfDigits (1/β)) (n + 1)
      let θ := (Q : ℝ) * (1/β) - cfNum (cfDigits (1/β)) (n + 1)
      let N := ⌊1 / (2 * |θ|)⌋₊
      0 < Q ∧ θ ≠ 0 ∧ Q ≤ N ∧
        6 * B / Q * (N : ℝ) ^ (-(1/2) : ℝ) ≤ (1/2 : ℝ) ^ j ∧
        (Q : ℝ) * (6 * B / Q * (N : ℝ) ^ (-(1/2) : ℝ)) ^ s ≤ (1/2 : ℝ) ^ j := by
  have hα : Irrational (1/β) := by simpa using hβ.inv
  have h0 : 0 < 1/β := one_div_pos.2 hβ0
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  set e := 1 + ν/2 with hedef
  have he : 0 < e := by positivity
  have hse : 0 < s * e - 1 := by
    have : 2 < s * (2 + ν) := by rwa [div_lt_iff₀ (by positivity)] at hs
    rw [hedef]; linarith
  have tq : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have lim (y : ℝ) (hy : 0 < y) (C : ℝ) :
      Tendsto (fun q : ℕ => C * (q : ℝ) ^ (-y)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hy).comp tq).const_mul C
  have ev1 := (lim e he (12 * B)).eventually (ge_mem_nhds (by positivity : (0 : ℝ) < (1/2) ^ j))
  have ev2 := (lim (s * e - 1) hse ((12 * B) ^ s)).eventually
    (ge_mem_nhds (by positivity : (0 : ℝ) < (1/2) ^ j))
  have ev3 : ∀ᶠ q : ℕ in atTop, (4 : ℝ) ≤ (q : ℝ) ^ (ν - 1) :=
    ((tendsto_rpow_atTop (by linarith)).comp tq).eventually_ge_atTop 4
  have ev4 : ∀ᶠ q : ℕ in atTop, (1 : ℝ) ≤ q := tq.eventually_ge_atTop 1
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 (ev1.and (ev2.and (ev3.and ev4)))
  obtain ⟨n, hnQ, hn⟩ := good_cf_level hα h0 (by linarith) happ Q₀
  refine ⟨n, ?_⟩
  intro Q θ N
  obtain ⟨h1, h2, h3, h4⟩ := hQ₀ Q hnQ.le
  have hQR : (1 : ℝ) ≤ Q := h4
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQpos : 0 < Q := by exact_mod_cast hQ0
  have hθ : θ ≠ 0 := by
    intro h
    apply (hα.natCast_mul hQpos.ne').ne_nat (cfNum (cfDigits (1/β)) (n + 1))
    simp only [θ] at h
    linarith
  have habs : 0 < |θ| := abs_pos.2 hθ
  have hθle : |θ| ≤ (Q : ℝ) ^ (-ν) := hn
  have hQν : (Q : ℝ) ^ ν = Q * (Q : ℝ) ^ (ν - 1) := by
    rw [← Real.rpow_one_add' hQ0.le (by linarith)]; ring_nf
  have hQν4 : 4 * (Q : ℝ) ≤ (Q : ℝ) ^ ν := by rw [hQν]; nlinarith
  have hinv : (Q : ℝ) ^ ν / 2 ≤ 1 / (2 * |θ|) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity), one_mul]
    have : (Q : ℝ) ^ ν * |θ| ≤ 1 := by
      calc (Q : ℝ) ^ ν * |θ| ≤ (Q : ℝ) ^ ν * (Q : ℝ) ^ (-ν) :=
            mul_le_mul_of_nonneg_left hθle (by positivity)
        _ = 1 := by rw [← Real.rpow_add hQ0]; simp
    linarith
  have hNlow : (Q : ℝ) ^ ν / 4 ≤ N := by
    have hfl := Nat.lt_floor_add_one (1 / (2 * |θ|))
    have : (Q : ℝ) ^ ν / 2 - 1 < N := by simp only [N]; linarith
    linarith
  have hN4 : (0 : ℝ) < (Q : ℝ) ^ ν / 4 := by positivity
  have hNR : (0 : ℝ) < N := hN4.trans_le hNlow
  have hQN : Q ≤ N := by
    have : (Q : ℝ) ≤ N := by linarith
    exact_mod_cast this
  -- the window length
  have hNpow : (N : ℝ) ^ (-(1/2) : ℝ) ≤ 2 * (Q : ℝ) ^ (-(ν/2)) := by
    calc (N : ℝ) ^ (-(1/2) : ℝ) ≤ ((Q : ℝ) ^ ν / 4) ^ (-(1/2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hN4 hNlow (by norm_num)
      _ = 2 * (Q : ℝ) ^ (-(ν/2)) := by
          rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hQ0.le,
            show (4 : ℝ) ^ (-(1/2) : ℝ) = 1/2 by
              rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
              norm_num]
          ring_nf
  have hd : 6 * B / Q * (N : ℝ) ^ (-(1/2) : ℝ) ≤ 12 * B * (Q : ℝ) ^ (-e) := by
    have hQe : (Q : ℝ) ^ (-e) = (Q : ℝ)⁻¹ * (Q : ℝ) ^ (-(ν/2)) := by
      rw [hedef, neg_add, Real.rpow_add hQ0, Real.rpow_neg_one]
    rw [hQe]
    calc 6 * B / Q * (N : ℝ) ^ (-(1/2) : ℝ) ≤ 6 * B / Q * (2 * (Q : ℝ) ^ (-(ν/2))) :=
          mul_le_mul_of_nonneg_left hNpow (by positivity)
      _ = 12 * B * ((Q : ℝ)⁻¹ * (Q : ℝ) ^ (-(ν/2))) := by ring
  have hd0 : 0 ≤ 6 * B / Q * (N : ℝ) ^ (-(1/2) : ℝ) := by positivity
  refine ⟨hQpos, hθ, hQN, hd.trans h1, ?_⟩
  calc (Q : ℝ) * (6 * B / Q * (N : ℝ) ^ (-(1/2) : ℝ)) ^ s
      ≤ (Q : ℝ) * (12 * B * (Q : ℝ) ^ (-e)) ^ s :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd0 hd hs0.le) hQ0.le
    _ = (12 * B) ^ s * (Q : ℝ) ^ (-(s * e - 1)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hQ0.le]
        have : (Q : ℝ) * (Q : ℝ) ^ (-e * s) = (Q : ℝ) ^ (-(s * e - 1)) := by
          rw [show -(s * e - 1) = 1 + -e * s by ring, Real.rpow_add hQ0, Real.rpow_one]
        rw [← this]; ring
    _ ≤ _ := h2

omit hβ0 hβ1 hβ in
/-- Tail of the halving series. -/
theorem tsum_half_tail (K : ℕ) :
    ∑' j : ℕ, (if K ≤ j then (1/2 : ℝ) ^ j else 0) = 2 * (1/2 : ℝ) ^ K := by
  have hs : Summable (fun j : ℕ => if K ≤ j then (1/2 : ℝ) ^ j else 0) :=
    (summable_geometric_two).of_nonneg_of_le (fun j => by split_ifs <;> positivity)
      fun j => by split_ifs <;> simp
  rw [← hs.sum_add_tsum_nat_add K]
  have h0 : ∑ i ∈ Finset.range K, (if K ≤ i then (1/2 : ℝ) ^ i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => if_neg (not_le.2 (Finset.mem_range.1 hi))
  rw [h0, zero_add]
  have h1 : (fun i : ℕ => if K ≤ i + K then (1/2 : ℝ) ^ (i + K) else 0) =
      fun i => (1/2 : ℝ) ^ K * (1/2 : ℝ) ^ i := by
    funext i; rw [if_pos (Nat.le_add_left K i), pow_add]; ring
  rw [h1, tsum_mul_left, tsum_geometric_two]
  ring

/-- **A small set of large law mass.** If `|q/β - p| ≤ q^(-ν)` for arbitrarily
large `q`, with `ν > 1`, then for every `s > 2/(2+ν)` some measurable set of
law mass at least `1/2` has zero `s`-dimensional Hausdorff measure. -/
theorem passageLaw_null_set {ν s : ℝ} (hν : 1 < ν) (hs : 2 / (2 + ν) < s)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * (1/β) - p| ≤ (q : ℝ) ^ (-ν)) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      ENNReal.ofReal (1/2) ≤ (passageLaw hβ0 hβ1 hβ : Measure ℝ) E ∧
      Measure.hausdorffMeasure s E = 0 := by
  classical
  obtain ⟨A, B, hA, hB, hwB⟩ := passageWeight_three_halves hβ0 hβ1 hβ
  have hb : ∀ n, passageJumpWeight β (n+1) ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ) := fun n => (hwB n).2
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  have hα : Irrational (1/β) := by simpa using hβ.inv
  have h0 : 0 < 1/β := one_div_pos.2 hβ0
  have hG := irrational_goodConvergents hα h0.le
  choose lev hlev using fun j => exists_fine_level hβ0 hβ1 hβ hB hν hs happ j
  set a := cfDigits (1/β)
  set Qf : ℕ → ℕ := fun j => cfDen a (lev j + 1) with hQf
  set θf : ℕ → ℝ := fun j => (Qf j : ℝ) * (1/β) - ((cfNum a (lev j + 1) : ℤ) : ℝ) with hθf
  set Nf : ℕ → ℕ := fun j => ⌊1 / (2 * |θf j|)⌋₊ with hNf
  set d : ℕ → ℝ := fun j => 6 * B / Qf j * (Nf j : ℝ) ^ (-(1/2) : ℝ) with hd
  have hlev' (j : ℕ) : 0 < Qf j ∧ θf j ≠ 0 ∧ Qf j ≤ Nf j ∧ d j ≤ (1/2 : ℝ) ^ j ∧
      (Qf j : ℝ) * d j ^ s ≤ (1/2 : ℝ) ^ j := by
    have h := hlev j
    simp only at h ⊢
    exact h
  have hlevel (j : ℕ) := passage_level hβ0 hβ1 hβ hB.le hb (hlev' j).1 (hG.sep (lev j))
    (p := (cfNum a (lev j + 1) : ℤ)) (hlev' j).2.1 (hlev' j).2.2.1
  set L : ℕ → Set ℝ := fun j => levelSet β (Qf j) (θf j) with hL
  set U : ℕ → Set ℝ := fun K => ⋃ j, ⋃ (_ : K ≤ j), L j with hU
  have hLm (j : ℕ) : MeasurableSet (L j) := levelSet_measurable _ _
  have hUm (K : ℕ) : MeasurableSet (U K) :=
    MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hLm j
  have hUa : Antitone U := fun K K' h x hx => by
    obtain ⟨j, hj, hx⟩ := mem_iUnion₂.1 hx
    exact mem_iUnion₂.2 ⟨j, h.trans hj, hx⟩
  refine ⟨⋂ K, U K, MeasurableSet.iInter hUm, ?_, ?_⟩
  · rw [hUa.measure_iInter (fun K => (hUm K).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf fun K => (hlevel K).2.trans
      (measure_mono (subset_iUnion₂_of_subset K le_rfl subset_rfl))
  · refine le_antisymm ?_ bot_le
    set Pr := jumpProfileRight (fun r => passagePhase β (r+1))
      (fun r => passageJumpWeight β (r+1))
    set t : ℕ → ℕ × ℕ → Set ℝ := fun K ji =>
      if K ≤ ji.1 ∧ ji.2 < Qf ji.1 then
        Icc (Pr (levelLeft (Qf ji.1) (θf ji.1) ji.2))
          (passageProfile β (levelLeft (Qf ji.1) (θf ji.1) ji.2 + 1 / (2 * (Qf ji.1 : ℝ))))
      else ∅ with ht
    have hlen (j i : ℕ) : passageProfile β (levelLeft (Qf j) (θf j) i + 1 / (2 * (Qf j : ℝ))) -
        Pr (levelLeft (Qf j) (θf j) i) ≤ d j := (hlevel j).1 i
    have hr : Tendsto (fun K : ℕ => ENNReal.ofReal ((1/2 : ℝ) ^ K)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hdiam : ∀ᶠ K in atTop, ∀ ji, Metric.ediam (t K ji) ≤ ENNReal.ofReal ((1/2 : ℝ) ^ K) :=
      Eventually.of_forall fun K ji => by
        by_cases h : K ≤ ji.1 ∧ ji.2 < Qf ji.1
        · simp only [ht, if_pos h, Real.ediam_Icc]
          apply ENNReal.ofReal_le_ofReal
          exact (hlen ji.1 ji.2).trans ((hlev' ji.1).2.2.2.1.trans
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) h.1))
        · simp [ht, if_neg h]
    have hcov : ∀ᶠ K in atTop, (⋂ K, U K) ⊆ ⋃ ji, t K ji :=
      Eventually.of_forall fun K x hx => by
        obtain ⟨j, hj, hxL⟩ := mem_iUnion₂.1 (mem_iInter.1 hx K)
        simp only [hL, levelSet] at hxL
        obtain ⟨i, hi, hxI⟩ := mem_iUnion₂.1 hxL
        refine mem_iUnion.2 ⟨(j, i), ?_⟩
        simp only [ht, if_pos (And.intro hj (Finset.mem_range.1 hi))]
        exact hxI
    have hle := Measure.hausdorffMeasure_le_liminf_tsum s (⋂ K, U K) (l := atTop) _ hr t hdiam hcov
    have hbound (K : ℕ) : ∑' ji, Metric.ediam (t K ji) ^ s ≤
        ENNReal.ofReal (2 * (1/2 : ℝ) ^ K) := by
      rw [ENNReal.tsum_prod']
      have hinner (j : ℕ) : ∑' i, Metric.ediam (t K (j, i)) ^ s ≤
          ENNReal.ofReal (if K ≤ j then (1/2 : ℝ) ^ j else 0) := by
        by_cases hKj : K ≤ j
        · rw [if_pos hKj, tsum_eq_sum (s := Finset.range (Qf j)) fun i hi => by
            simp only [ht, if_neg (fun (h : K ≤ j ∧ i < Qf j) => hi (Finset.mem_range.2 h.2)), Metric.ediam_empty]
            exact ENNReal.zero_rpow_of_pos hs0]
          calc ∑ i ∈ Finset.range (Qf j), Metric.ediam (t K (j, i)) ^ s
              ≤ ∑ i ∈ Finset.range (Qf j), ENNReal.ofReal (d j) ^ s := by
                refine Finset.sum_le_sum fun i hi => ENNReal.rpow_le_rpow ?_ hs0.le
                simp only [ht, if_pos (And.intro hKj (Finset.mem_range.1 hi)), Real.ediam_Icc]
                exact ENNReal.ofReal_le_ofReal (hlen j i)
            _ = ENNReal.ofReal ((Qf j : ℝ) * d j ^ s) := by
                have hd0 : 0 ≤ d j := by simp only [hd]; positivity
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                  ENNReal.ofReal_rpow_of_nonneg hd0 hs0.le, ← ENNReal.ofReal_natCast,
                  ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            _ ≤ _ := ENNReal.ofReal_le_ofReal (hlev' j).2.2.2.2
        · rw [if_neg hKj, ENNReal.ofReal_zero]
          refine le_of_eq (ENNReal.tsum_eq_zero.2 fun i => ?_)
          simp only [ht, if_neg (fun (h : K ≤ j ∧ i < Qf j) => hKj h.1), Metric.ediam_empty]
          exact ENNReal.zero_rpow_of_pos hs0
      refine (ENNReal.tsum_le_tsum hinner).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by split_ifs <;> positivity)
        ((summable_geometric_two).of_nonneg_of_le (fun j => by split_ifs <;> positivity)
          fun j => by split_ifs <;> simp), tsum_half_tail]
    have hlim : Tendsto (fun K : ℕ => ENNReal.ofReal (2 * (1/2 : ℝ) ^ K)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      apply ENNReal.tendsto_ofReal
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num)).const_mul 2
    calc Measure.hausdorffMeasure s (⋂ K, U K)
        ≤ liminf (fun K => ∑' ji, Metric.ediam (t K ji) ^ s) atTop := hle
      _ ≤ liminf (fun K : ℕ => ENNReal.ofReal (2 * (1/2 : ℝ) ^ K)) atTop :=
          liminf_le_liminf (Eventually.of_forall hbound)
      _ = 0 := hlim.liminf_eq


/-- The law is carried by the cluster set. -/
theorem passageLaw_cluster : (passageLaw hβ0 hβ1 hβ : Measure ℝ) (passageClusterSet β) = 1 := by
  have hmeas := (passageProfile_monotone hβ0 hβ1 hβ).measurable
  have hK : MeasurableSet (passageClusterSet β) :=
    (isCompact_passageClusterSet hβ0 hβ1 hβ).isClosed.measurableSet
  rw [passageLaw, ProbabilityMeasure.toMeasure_map, Measure.map_apply hmeas hK]
  have hpre : passageProfile β ⁻¹' passageClusterSet β = univ := by
    ext t
    simp only [mem_preimage, mem_univ, iff_true]
    rw [passageClusterSet_eq_closure_range hβ0 hβ1 hβ]
    exact subset_closure (mem_range_self t)
  rw [hpre]
  exact measure_univ

end Passage

/-- The lower Hausdorff dimension of a measure on the line: the least
Hausdorff dimension of a measurable set of positive mass. -/
noncomputable def lawDimH (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (E : Set ℝ) (_ : MeasurableSet E) (_ : 0 < μ E), dimH E

/-- Any measurable set of positive mass bounds the dimension of the law. -/
theorem lawDimH_le_of {μ : Measure ℝ} {E : Set ℝ} (hE : MeasurableSet E) (hμ : 0 < μ E) :
    lawDimH μ ≤ dimH E :=
  iInf_le_of_le E (iInf_le_of_le hE (iInf_le _ hμ))

/-- Finitely many positive values have a positive lower bound. -/
theorem exists_pos_le_finset {s : Finset ℕ} {f : ℕ → ℝ} (hf : ∀ x ∈ s, 0 < f x) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ x ∈ s, c ≤ f x := by
  classical
  set T := insert (1 : ℝ) (s.image f)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.min' hT, (Finset.lt_min'_iff _ _).2 fun y hy => ?_, Finset.min'_le _ _
    (Finset.mem_insert_self _ _), fun x hx => Finset.min'_le _ _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hx))⟩
  rcases Finset.mem_insert.1 hy with rfl | hy
  · norm_num
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact hf x hx

/-- A Diophantine class `ν` gives a uniform lower bound of every exponent `τ > ν`. -/
theorem dioph_lower_of_class {α ν τ : ℝ} (hα : Irrational α) (hcls : DiophClass α ν)
    (hτ : ν < τ) : ∃ c : ℝ, 0 < c ∧ DiophantineLowerBound α c τ := by
  classical
  set μ := (ν + τ) / 2
  have hF := hcls.2 μ (by simp only [μ]; linarith)
  obtain ⟨c, hc, hc1, hcle⟩ := exists_pos_le_finset (s := hF.toFinset)
    (f := fun q : ℕ => (q : ℝ) ^ τ * |(q : ℝ) * α - round ((q : ℝ) * α)|) fun q hq => by
      have hq0 : 0 < q := (hF.mem_toFinset.1 hq).1
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
      refine mul_pos (Real.rpow_pos_of_pos hqR _) (abs_pos.2 (sub_ne_zero.2 ?_))
      exact (hα.natCast_mul hq0.ne').ne_int _
  refine ⟨c, hc, fun q hq p => ?_⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hmem : q ∈ approxDenoms α μ
  · calc c ≤ (q : ℝ) ^ τ * |(q : ℝ) * α - round ((q : ℝ) * α)| :=
          hcle q (hF.mem_toFinset.2 hmem)
      _ ≤ (q : ℝ) ^ τ * |(q : ℝ) * α - p| :=
          mul_le_mul_of_nonneg_left (round_le _ _) (by positivity)
  · have hge : (q : ℝ) ^ (-μ) ≤ |(q : ℝ) * α - p| := by
      by_contra h
      exact hmem ⟨hq, p, not_le.1 h⟩
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    calc c ≤ 1 := hc1
      _ ≤ (q : ℝ) ^ (τ - μ) := Real.one_le_rpow hq1 (by simp only [μ]; linarith)
      _ = (q : ℝ) ^ τ * (q : ℝ) ^ (-μ) := by rw [← Real.rpow_add hqR]; ring_nf
      _ ≤ (q : ℝ) ^ τ * |(q : ℝ) * α - p| := mul_le_mul_of_nonneg_left hge (by positivity)

/-- **Upper bound for the law.** If `|qα - p| ≤ q^(-ν)` for arbitrarily large
`q`, with `ν > 1`, the limit law has lower Hausdorff dimension at most
`2/(2+ν)`. -/
theorem passageLaw_lawDimH_le {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 < ν)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-ν)) :
    lawDimH (passageLaw (β := 1/α) (one_div_pos.2 (by linarith))
      ((div_lt_one (by linarith)).2 hα1) (by simpa using hα.inv) : Measure ℝ) ≤
      ENNReal.ofReal (2 / (2 + ν)) := by
  have hα0 : 0 < α := by linarith
  have hb0 : 0 < 1/α := one_div_pos.2 hα0
  have hb1 : 1/α < 1 := (div_lt_one hα0).2 hα1
  have hb : Irrational (1/α) := by simpa using hα.inv
  have hinv : 1 / (1/α) = α := one_div_one_div α
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  by_cases hct : c = ⊤
  · rw [hct]; exact le_top
  have hs : 2 / (2 + ν) < c.toReal := by
    rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), ENNReal.ofReal_toReal hct]
    exact hc
  have happ' : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ,
      |(q : ℝ) * (1 / (1/α)) - p| ≤ (q : ℝ) ^ (-ν) := by
    rw [hinv]; exact happ
  obtain ⟨E, hEm, hEμ, hEH⟩ := passageLaw_null_set hb0 hb1 hb hν hs happ'
  have hpos : 0 < (passageLaw hb0 hb1 hb : Measure ℝ) E := lt_of_lt_of_le (by norm_num) hEμ
  refine (lawDimH_le_of hEm hpos).trans ?_
  have hd : dimH E ≤ ((c.toReal).toNNReal : ℝ≥0∞) := by
    apply dimH_le_of_hausdorffMeasure_ne_top
    rw [Real.coe_toNNReal _ ENNReal.toReal_nonneg, hEH]
    exact ENNReal.zero_ne_top
  refine hd.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal, ENNReal.ofReal_toReal hct]

/-- **Liouville slopes.** At a Liouville slope the limit law has lower
Hausdorff dimension zero. -/
theorem passageLaw_lawDimH_liouville {α : ℝ} (hα1 : 1 < α) (hL : Liouville α) :
    lawDimH (passageLaw (β := 1/α) (one_div_pos.2 (by linarith))
      ((div_lt_one (by linarith)).2 hα1) (by simpa using hL.irrational.inv) : Measure ℝ) = 0 := by
  refine le_antisymm ?_ bot_le
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  by_cases hct : c = ⊤
  · rw [hct]; exact le_top
  have hc0 : 0 < c.toReal := ENNReal.toReal_pos (ne_of_gt hc) hct
  -- choose `ν > 1` with `2/(2+ν) < c`
  set ν := max 2 (2 / c.toReal) with hνdef
  have hν : 1 < ν := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlt : 2 / (2 + ν) < c.toReal := by
    rw [div_lt_iff₀ (by positivity)]
    have : 2 / c.toReal ≤ ν := le_max_right _ _
    rw [div_le_iff₀ hc0] at this
    nlinarith
  have happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-ν) := by
    intro Q
    set n := ⌈ν⌉₊ + 1
    obtain ⟨b, ⟨a, hne, hab⟩, hbQ⟩ :=
      ((hL.frequently_exists_num n).and_eventually (eventually_gt_atTop (max Q 1))).exists
    have hb1 : 1 < b := lt_of_le_of_lt (le_max_right _ _) hbQ
    have hbR : (1 : ℝ) < b := by exact_mod_cast hb1
    have hb0 : (0 : ℝ) < b := by linarith
    refine ⟨b, lt_of_le_of_lt (le_max_left _ _) hbQ, a, ?_⟩
    have h1 : |(b : ℝ) * α - a| = b * |α - a / b| := by
      rw [← abs_of_pos hb0, ← abs_mul, abs_of_pos hb0]
      congr 1
      field_simp
    rw [h1]
    have h2 : (b : ℝ) * (1 / (b : ℝ) ^ n) ≤ (b : ℝ) ^ (-ν) := by
      rw [← Real.rpow_natCast, one_div, ← Real.rpow_neg hb0.le, ← Real.rpow_one_add' hb0.le]
      · apply Real.rpow_le_rpow_of_exponent_le hbR.le
        have : ν ≤ ⌈ν⌉₊ := Nat.le_ceil ν
        push_cast [n]
        linarith
      · push_cast [n]
        have : ν ≤ ⌈ν⌉₊ := Nat.le_ceil ν
        linarith
    exact (mul_le_mul_of_nonneg_left hab.le hb0.le).trans h2
  refine (passageLaw_lawDimH_le hα1 hL.irrational hν happ).trans ?_
  calc ENNReal.ofReal (2 / (2 + ν)) ≤ ENNReal.ofReal c.toReal := ENNReal.ofReal_le_ofReal hlt.le
    _ = c := ENNReal.ofReal_toReal hct

/-- **The dimension of the limit law.** For every irrational slope `α > 1` of
Diophantine class `ν` (`|qα - p| < q^(-μ)` has infinitely many solutions for
`μ < ν` and finitely many for `μ > ν`), the limit law has lower Hausdorff
dimension exactly `2/(2+ν)`, that is `2/(1+ω)` for the irrationality
exponent `ω = 1 + ν`. -/
theorem passageLaw_lawDimH_eq {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 ≤ ν)
    (hcls : DiophClass α ν) :
    lawDimH (passageLaw (β := 1/α) (one_div_pos.2 (by linarith))
      ((div_lt_one (by linarith)).2 hα1) (by simpa using hα.inv) : Measure ℝ) =
      ENNReal.ofReal (2 / (2 + ν)) := by
  have hα0 : 0 < α := by linarith
  have hb0 : 0 < 1/α := one_div_pos.2 hα0
  have hb1 : 1/α < 1 := (div_lt_one hα0).2 hα1
  have hb : Irrational (1/α) := by simpa using hα.inv
  have hinv : 1 / (1/α) = α := one_div_one_div α
  apply le_antisymm
  · -- upper bound
    apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    by_cases hct : c = ⊤
    · rw [hct]; exact le_top
    have hs : 2 / (2 + ν) < c.toReal := by
      rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), ENNReal.ofReal_toReal hct]
      exact hc
    rcases hν.lt_or_eq with hν1 | hν1
    · -- pick an exponent `ν' ∈ (1, ν)` still below the threshold
      have hcont : ContinuousAt (fun x : ℝ => 2 / (2 + x)) ν :=
        continuousAt_const.div (continuousAt_const.add continuousAt_id) (by linarith)
      obtain ⟨δ, hδ, hδs⟩ := Metric.continuousAt_iff.1 hcont _ (sub_pos.2 hs)
      set ν' := max ((1 + ν) / 2) (ν - δ / 2)
      have hν'1 : 1 < ν' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hν'ν : ν' < ν := max_lt (by linarith) (by linarith)
      have hs' : 2 / (2 + ν') < c.toReal := by
        have h := hδs (x := ν') (by
          rw [Real.dist_eq, abs_lt]
          constructor
          · have := le_max_right ((1 + ν) / 2) (ν - δ / 2); linarith
          · linarith)
        rw [Real.dist_eq, abs_lt] at h
        linarith [h.2]
      have happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-ν') := by
        intro Q
        obtain ⟨q, ⟨hq0, p, hp⟩, hqQ⟩ := (hcls.1 ν' hν'ν).exists_gt Q
        exact ⟨q, hqQ, p, hp.le⟩
      refine (passageLaw_lawDimH_le hα1 hα hν'1 happ).trans ?_
      calc ENNReal.ofReal (2 / (2 + ν')) ≤ ENNReal.ofReal c.toReal :=
            ENNReal.ofReal_le_ofReal hs'.le
        _ = c := ENNReal.ofReal_toReal hct
    · -- class one: the cluster set carries the law
      subst hν1
      have hK := passageLaw_cluster hb0 hb1 hb
      have hKm : MeasurableSet (passageClusterSet (1/α)) :=
        (isCompact_passageClusterSet hb0 hb1 hb).isClosed.measurableSet
      refine (lawDimH_le_of hKm (by rw [hK]; norm_num)).trans
        ((passageCluster_dimH_le hb0 hb1 hb).trans ?_)
      have : (2/3 : ℝ≥0∞) = ENNReal.ofReal (2 / (2 + 1)) := by
        rw [show (2 : ℝ) / (2 + 1) = 2/3 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
        simp
      rw [this]
      exact le_of_lt hc
  · -- lower bound
    refine le_iInf fun E => le_iInf fun hE => le_iInf fun hμ => ?_
    apply le_of_forall_lt
    intro c hc
    have hc' : c < ENNReal.ofReal (2 / (2 + ν)) := hc
    -- choose `τ > ν` with `2/(2+τ)` above `c`
    have hcR : c ≠ ⊤ := ne_top_of_lt hc'
    have hlt : c.toReal < 2 / (2 + ν) := by
      rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hcR]
      exact hc'
    have hcont : ContinuousAt (fun x : ℝ => 2 / (2 + x)) ν :=
      continuousAt_const.div (continuousAt_const.add continuousAt_id) (by linarith)
    obtain ⟨δ, hδ, hδs⟩ := Metric.continuousAt_iff.1 hcont _ (sub_pos.2 hlt)
    set τ := ν + δ / 2
    have hτν : ν < τ := by simp only [τ]; linarith
    have hτc : c.toReal < 2 / (2 + τ) := by
      have h := hδs (x := τ) (by rw [Real.dist_eq, abs_lt]; constructor <;> simp only [τ] <;> linarith)
      rw [Real.dist_eq, abs_lt] at h
      linarith [h.1]
    obtain ⟨c₀, hc₀, hdio⟩ := dioph_lower_of_class hα hcls hτν
    have hdio' : DiophantineLowerBound (1 / (1/α)) c₀ τ := by rw [hinv]; exact hdio
    have hge := passageLaw_dimH_ge hb0 hb1 hb hc₀ (by linarith) hdio' hE hμ
    calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hcR).symm
      _ < ENNReal.ofReal (2 / (2 + τ)) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hτc
      _ ≤ dimH E := hge

end Problems.Juggler.BeattySlope
