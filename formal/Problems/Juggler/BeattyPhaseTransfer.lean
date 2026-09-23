import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.Tannery
import Problems.Juggler.PaperBCertificateRecursion

/-!
# Survivor profiles and the Beatty first-passage normalization

This module proves the phase coordinates, the cancellation of consecutive
survivor jump weights into a minimal-certificate count, and the one-sided
limits of a summable positive jump series. Analytic identification of that
series with the counting asymptotic is a separate written argument; it is not
assumed to have been proved by the finite count identities here.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology

/-- The two phases at a Beatty crossing. The hypotheses specify its integer
part without assuming any unproved property of the logarithmic slope. -/
theorem fract_crossing_pair {alpha delta : ℝ} {m r : ℕ}
    (ha : 1 < alpha) (hd0 : 0 < delta) (hd1 : delta < 1)
    (hdelta : delta = alpha * r - m) :
    Int.fract ((m : ℝ) / alpha) = 1 - delta / alpha ∧
      Int.fract (((m : ℝ) + 1) / alpha) = (1 - delta) / alpha := by
  have ha0 : 0 < alpha := by linarith
  have hane : alpha ≠ 0 := ne_of_gt ha0
  have hda : delta / alpha < 1 := (div_lt_one ha0).2 (by linarith)
  have hdpos : 0 < delta / alpha := div_pos hd0 ha0
  constructor
  · apply Int.fract_eq_iff.2
    refine ⟨by linarith, by linarith, (r : ℤ) - 1, ?_⟩
    push_cast
    rw [hdelta]
    field_simp
    ring
  · apply Int.fract_eq_iff.2
    refine ⟨div_nonneg (by linarith) ha0.le,
      (div_lt_one ha0).2 (by linarith), (r : ℤ), ?_⟩
    push_cast
    rw [hdelta]
    field_simp
    ring

/-- The exact first-passage identity over the reals, derived from the
combinatorial partition of the two extensions of every survivor. -/
theorem minimalCertCount_cast (m : ℕ) :
    (minimalCertCount (m + 1) : ℝ) =
      2 * (neverNegCount m : ℝ) - neverNegCount (m + 1) := by
  have h := neverNegCount_add_minimalCertCount m
  have hr : (neverNegCount (m + 1) : ℝ) + minimalCertCount (m + 1) =
      2 * neverNegCount m := by exact_mod_cast h
  linarith

/-- Consecutive downward survivor jumps combine into a nonnegative
first-passage weight. Here `v = 2 rho`; `a` is their common amplitude. -/
theorem survivor_jump_difference {v a : ℝ} (hv : v ≠ 0) (m : ℕ) :
    a * (neverNegCount m : ℝ) / v ^ m -
        (v / 2) * (a * (neverNegCount (m + 1) : ℝ) / v ^ (m + 1)) =
      a * (minimalCertCount (m + 1) : ℝ) / (2 * v ^ m) := by
  rw [minimalCertCount_cast, pow_succ]
  field_simp

/-- After applying the phase prefactor, the arbitrary amplitude cancels.
This is the jump formula before substituting the entropy constants. -/
theorem transferred_jump_eq {v a z : ℝ} (hv : v ≠ 0) (ha : a ≠ 0) (m : ℕ) :
    (2 / a * z) *
        (a * (neverNegCount m : ℝ) / v ^ m -
          (v / 2) * (a * (neverNegCount (m + 1) : ℝ) / v ^ (m + 1))) =
      z * (minimalCertCount (m + 1) : ℝ) / v ^ m := by
  rw [survivor_jump_difference hv]
  field_simp

/-- Every transferred jump weight is nonnegative for positive scaling. -/
theorem transferred_jump_nonneg {v z : ℝ} (hv : 0 < v) (hz : 0 ≤ z) (m : ℕ) :
    0 ≤ z * (minimalCertCount (m + 1) : ℝ) / v ^ m := by positivity

/-- A positive certificate count gives a strictly positive transferred jump. -/
theorem transferred_jump_pos {v z : ℝ} (hv : 0 < v) (hz : 0 < z) {m : ℕ}
    (hm : 0 < minimalCertCount (m + 1)) :
    0 < z * (minimalCertCount (m + 1) : ℝ) / v ^ m := by positivity

/-- A left-continuous cumulative jump series. The strict inequality fixes
the value on the countable orbit where jumps occur. -/
noncomputable def jumpProfile (phase weight : ℕ → ℝ) (x : ℝ) : ℝ :=
  1 + ∑' n, if phase n < x then weight n else 0

/-- The right-hand trace includes atoms at the evaluation point. -/
noncomputable def jumpProfileRight (phase weight : ℕ → ℝ) (x : ℝ) : ℝ :=
  1 + ∑' n, if phase n ≤ x then weight n else 0

private theorem summable_restrict {w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (p : ℕ → Prop) [DecidablePred p] :
    Summable (fun n => if p n then w n else 0) :=
  hw.of_norm_bounded fun n => by
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]

/-- Nonnegative summable weights give a nondecreasing profile. -/
theorem jumpProfile_monotone {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) : Monotone (jumpProfile phase w) := by
  intro x y hxy
  unfold jumpProfile
  apply add_le_add_right
  apply (summable_restrict hw hn _).tsum_le_tsum _ (summable_restrict hw hn _)
  intro n
  by_cases hx : phase n < x
  · simp [hx, lt_of_lt_of_le hx hxy]
  · simp only [hx, if_false]
    split_ifs <;> simp [hn n]

/-- The total atomic mass bounds the range of the profile. -/
theorem jumpProfile_bounds {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (x : ℝ) :
    1 ≤ jumpProfile phase w x ∧ jumpProfile phase w x ≤ 1 + ∑' n, w n := by
  constructor
  · have h : 0 ≤ ∑' n, if phase n < x then w n else 0 :=
      tsum_nonneg fun n => by split_ifs <;> simp [hn n]
    unfold jumpProfile
    linarith
  · unfold jumpProfile
    apply add_le_add_right
    exact (summable_restrict hw hn _).tsum_le_tsum
      (fun n => by split_ifs <;> simp [hn n]) hw

private theorem step_tendsto_left (a w x : ℝ) :
    Tendsto (fun y => if a < y then w else 0) (𝓝[<] x)
      (𝓝 (if a < x then w else 0)) := by
  apply (tendsto_congr' (show ∀ᶠ y in 𝓝[<] x,
    (if a < y then w else 0) = (if a < x then w else 0) from ?_)).2
  · exact tendsto_const_nhds
  · by_cases h : a < x
    · filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds h)] with y hy
      simp [h, hy]
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hyx : y < x := hy
      have hay : ¬ a < y := by linarith
      simp [h, hay]

private theorem step_tendsto_right (a w x : ℝ) :
    Tendsto (fun y => if a < y then w else 0) (𝓝[>] x)
      (𝓝 (if a ≤ x then w else 0)) := by
  apply (tendsto_congr' (show ∀ᶠ y in 𝓝[>] x,
    (if a < y then w else 0) = (if a ≤ x then w else 0) from ?_)).2
  · exact tendsto_const_nhds
  · by_cases h : a ≤ x
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hxy : x < y := hy
      simp [h, lt_of_le_of_lt h hxy]
    · have hxa : x < a := lt_of_not_ge h
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hxa)] with y hy
      simp [h, not_lt_of_ge hy.le]

/-- Summability justifies taking the left limit term by term even when
the jump locations are dense. No separation of neighboring jumps is needed. -/
theorem jumpProfile_tendsto_left {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (x : ℝ) :
    Tendsto (jumpProfile phase w) (𝓝[<] x) (𝓝 (jumpProfile phase w x)) := by
  apply Tendsto.const_add
  apply tendsto_tsum_of_dominated_convergence hw
  · intro n
    exact step_tendsto_left _ _ _
  · exact Eventually.of_forall fun y n => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]

/-- The right limit includes exactly the atoms at the evaluation point. -/
theorem jumpProfile_tendsto_right {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (x : ℝ) :
    Tendsto (jumpProfile phase w) (𝓝[>] x) (𝓝 (jumpProfileRight phase w x)) := by
  apply Tendsto.const_add
  apply tendsto_tsum_of_dominated_convergence hw
  · intro n
    exact step_tendsto_right _ _ _
  · exact Eventually.of_forall fun y n => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]

/-- At a distinct orbit point the right-minus-left jump is exactly its
weight, including in the presence of infinitely many nearby atoms. -/
theorem jumpProfile_jump {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective phase) (k : ℕ) :
    jumpProfileRight phase w (phase k) - jumpProfile phase w (phase k) = w k := by
  unfold jumpProfileRight jumpProfile
  rw [add_sub_add_left_eq_sub]
  rw [← (summable_restrict hw hn _).tsum_sub (summable_restrict hw hn _)]
  have heq : (fun n => (if phase n ≤ phase k then w n else 0) -
      (if phase n < phase k then w n else 0)) =
      (fun n => if n = k then w k else 0) := by
    funext n
    by_cases h : n = k
    · subst n
      simp
    · have hp : phase n ≠ phase k := fun hp => h (hi hp)
      rcases lt_or_gt_of_ne hp with hp | hp
      · simp [h, hp, hp.le]
      · simp [h, not_le_of_gt hp, not_lt_of_ge hp.le]
  rw [heq]
  simp

/-- Away from the listed atoms the two one-sided traces agree. -/
theorem jumpProfileRight_eq_of_not_mem_range {phase w : ℕ → ℝ} {x : ℝ}
    (hx : x ∉ Set.range phase) : jumpProfileRight phase w x = jumpProfile phase w x := by
  unfold jumpProfileRight jumpProfile
  congr 1
  apply tsum_congr
  intro n
  have hne : phase n ≠ x := fun h => hx ⟨n, h⟩
  simp [le_iff_lt_or_eq, hne]

/-- Finite-depth normalization before taking any asymptotic limit. The
nonzero denominator and exponential base are the only analytic hypotheses. -/
theorem normalized_count_identity {v C r : ℝ} (hv : v ≠ 0) (hC : C ≠ 0) (m : ℕ) :
    r * (minimalCertCount (m + 1) : ℝ) / C =
      (2 * r * v ^ m / C) *
        ((neverNegCount m : ℝ) / v ^ m -
          (v / 2) * ((neverNegCount (m + 1) : ℝ) / v ^ (m + 1))) := by
  rw [minimalCertCount_cast, pow_succ]
  field_simp

/-- The error identity keeps the finite-depth polynomial correction `t`.
Subtracting two relative asymptotics without controlling this term is unsafe. -/
theorem profile_transfer_error (rho t p q e f : ℝ) :
    ((p + e) - rho * t * (q + f)) - (p - rho * q) =
      e - rho * t * f + rho * (1 - t) * q := by ring

/-- Explicit error control for the two-profile transfer; no lower bound on
their difference is required because the conclusion is an additive error. -/
theorem profile_transfer_error_le (rho t p q e f : ℝ) :
    |((p + e) - rho * t * (q + f)) - (p - rho * q)| ≤
      |e| + |rho| * |t| * |f| + |rho| * |1 - t| * |q| := by
  rw [profile_transfer_error]
  calc
    _ ≤ |e - rho * t * f| + |rho * (1 - t) * q| := abs_add_le _ _
    _ ≤ (|e| + |rho * t * f|) + |rho * (1 - t) * q| :=
      add_le_add_left (abs_sub _ _) _
    _ = _ := by simp only [abs_mul]

/-- The atom written in the centered Bernoulli coordinates. It differs by
one factor of the even-step probability from the actual first-descent mass. -/
noncomputable def tiltedWeight (beta q : ℝ) (m r c : ℕ) : ℝ :=
  c * beta ^ r * q ^ (m - r)

/-- The first atom is exactly `beta`, with no fitted amplitude. -/
theorem tiltedWeight_first (beta q : ℝ) : tiltedWeight beta q 1 1 1 = beta := by
  simp [tiltedWeight]

/-- The two-letter first-descent word is unique, verified by exact reduction. -/
theorem minimalCertCount_two : minimalCertCount 2 = 1 := by decide +kernel

/-- Once the total jump mass is `1/s`, the two limiting envelopes follow
from positivity. This theorem does not establish the total-mass hypothesis. -/
theorem jumpProfile_envelope {phase w : ℕ → ℝ} {s : ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n) (hm : ∑' n, w n = 1 / s)
    (x : ℝ) : 1 ≤ jumpProfile phase w x ∧ jumpProfile phase w x ≤ 1 + 1 / s := by
  simpa [hm] using jumpProfile_bounds hw hn x

/-- The right endpoint at zero is exactly one when all atoms lie strictly
inside the unit interval. -/
theorem jumpProfile_tendsto_zero {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hp : ∀ n, 0 < phase n) :
    Tendsto (jumpProfile phase w) (𝓝[>] 0) (𝓝 1) := by
  have h := jumpProfile_tendsto_right (phase := phase) hw hn 0
  simpa [jumpProfileRight, fun n => not_le_of_gt (hp n)] using h

/-- The left endpoint at one is one plus the total atomic mass. -/
theorem jumpProfile_tendsto_one {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hp : ∀ n, phase n < 1) :
    Tendsto (jumpProfile phase w) (𝓝[<] 1) (𝓝 (1 + ∑' n, w n)) := by
  simpa [jumpProfile, hp] using jumpProfile_tendsto_left (phase := phase) hw hn 1

/-- A dominated moving-kernel transfer. The phase need not converge and the
profile need not be continuous. In a renewal application `near` is the
first-half kernel, `phi` the shifted phase kernel, and `remainder` the
second-half contribution. The kernel bounds and small remainder are explicit
hypotheses, not conclusions supplied for the concrete counting problem here. -/
theorem tendsto_weighted_moving_profile
    {u : ℕ → ℝ} {near phi : ℕ → ℕ → ℝ} {truth remainder : ℕ → ℝ}
    {K P : ℝ} (hu : Summable u) (hun : ∀ j, 0 ≤ u j)
    (hnear : ∀ n j, |near n j| ≤ K) (hphi : ∀ n j, |phi n j| ≤ P)
    (hlocal : ∀ j, Tendsto (fun n => near n j - phi n j) atTop (𝓝 0))
    (hrem : Tendsto remainder atTop (𝓝 0))
    (htruth : ∀ n, truth n = (∑' j, u j * near n j) + remainder n) :
    Tendsto (fun n => truth n - ∑' j, u j * phi n j) atTop (𝓝 0) := by
  have hns (n : ℕ) : Summable (fun j => u j * near n j) :=
    (hu.mul_left K).of_norm_bounded fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hun j)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hnear n j) (hun j)
  have hps (n : ℕ) : Summable (fun j => u j * phi n j) :=
    (hu.mul_left P).of_norm_bounded fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hun j)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hphi n j) (hun j)
  have hd : Tendsto (fun n => ∑' j, u j * (near n j - phi n j)) atTop (𝓝 0) := by
    have ht := tendsto_tsum_of_dominated_convergence (hu.mul_left (K + P))
      (fun j => by simpa using (hlocal j).const_mul (u j))
      (Eventually.of_forall (fun n j => show ‖u j * (near n j - phi n j)‖ ≤
          (K + P) * u j from by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hun j)]
        have he : |near n j - phi n j| ≤ K + P :=
          (abs_sub _ _).trans (add_le_add (hnear n j) (hphi n j))
        simpa [mul_comm] using mul_le_mul_of_nonneg_left he (hun j)))
    simpa using ht
  have hfinal := hd.add hrem
  simp only [add_zero] at hfinal
  convert hfinal using 1
  funext n
  rw [htruth, show (∑' j, u j * (near n j - phi n j)) =
      (∑' j, u j * near n j) - ∑' j, u j * phi n j from by
    simp_rw [mul_sub]
    exact (hns n).tsum_sub (hps n)]
  ring

end Problems.Juggler.BeattyPhase
