import Problems.Juggler.PaperBCertificateRecursion
import Problems.Juggler.PaperBSurvivorDecay
import Problems.Juggler.FateOneSided
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The coefficient shift and its stopping-time boundary

Fixed-depth fair words have multiplier moment one. Minimal descent certificates
are a prefix-free family with fair mass one, but their multiplier moment is at
most three quarters. Thus completeness alone does not preserve that moment at
an unbounded stopping time. These are word identities, not estimates for the
distribution of actual Juggler starts.
-/

namespace Problems.Juggler.CollatzMoments

open Finset PaperBCertificates Filter
open scoped Topology

noncomputable def fairWeight (w : List Branch) : ℝ := 1 / 2 ^ w.length
noncomputable def multiplier (w : List Branch) : ℝ :=
  3 ^ oddCount w / 2 ^ w.length
noncomputable def idealCoeff (w : List Branch) : ℝ := 1 / 3 ^ oddCount w

theorem multiplier_pos (w : List Branch) : 0 < multiplier w := by
  unfold multiplier
  positivity

theorem coefficient_shift (w : List Branch) (s : ℝ) :
    idealCoeff w * multiplier w ^ s =
      fairWeight w * multiplier w ^ (s - 1) := by
  rw [Real.rpow_sub (multiplier_pos w), Real.rpow_one]
  unfold idealCoeff fairWeight multiplier
  field_simp

theorem fair_children (w : List Branch) :
    fairWeight (w ++ [.even]) + fairWeight (w ++ [.odd]) = fairWeight w := by
  simp [fairWeight, pow_succ]
  ring

theorem tilted_children (w : List Branch) :
    fairWeight (w ++ [.even]) * multiplier (w ++ [.even]) +
      fairWeight (w ++ [.odd]) * multiplier (w ++ [.odd]) =
        fairWeight w * multiplier w := by
  simp [fairWeight, multiplier, oddCount_append, oddCount, pow_succ]
  ring

theorem fixed_depth_fair (d : ℕ) :
    ∑ w ∈ allWords d, fairWeight w = 1 := by
  induction d with
  | zero => simp [allWords, fairWeight]
  | succ d ih => simpa only [OneSided.sum_allWords_succ, fair_children] using ih

theorem fixed_depth_moment (d : ℕ) :
    ∑ w ∈ allWords d, fairWeight w * multiplier w = 1 := by
  induction d with
  | zero => simp [allWords, fairWeight, multiplier, oddCount]
  | succ d ih => simpa only [OneSided.sum_allWords_succ, tilted_children] using ih

theorem certificate_prefix_free {u v : List Branch}
    (hu : IsMinimalCertificate u) (hv : IsMinimalCertificate v)
    (h : u <+: v) : u = v := by
  by_contra hne
  have hlt : u.length < v.length :=
    lt_of_le_of_ne h.length_le (fun he => hne (h.eq_of_length he))
  have hp : 0 < u.length := List.length_pos_iff.mpr hu.1
  have hn := hv.2.2 u.length hp hlt
  obtain ⟨t, rfl⟩ := h
  simp only [List.take_left] at hn
  exact hn hu.2.1

noncomputable def certMass (d : ℕ) : ℝ :=
  (minimalCertCount (d + 1) : ℝ) / 2 ^ (d + 1)

noncomputable def tiltedCertMass (d : ℕ) : ℝ :=
  ∑ w ∈ minimalCertWords (d + 1), fairWeight w * multiplier w

theorem certMass_eq_sum (d : ℕ) :
    certMass d = ∑ w ∈ minimalCertWords (d + 1), fairWeight w := by
  unfold certMass minimalCertCount
  rw [show (∑ w ∈ minimalCertWords (d + 1), fairWeight w) =
      ∑ _w ∈ minimalCertWords (d + 1), (1 : ℝ) / 2 ^ (d + 1) from
    sum_congr rfl (fun w hw => by
      have hl := mem_allWords.mp (mem_filter.mp hw).1
      simp [fairWeight, hl])]
  simp [div_eq_mul_inv]

theorem certMass_nonneg (d : ℕ) : 0 ≤ certMass d := by
  unfold certMass
  positivity

theorem tiltedCertMass_nonneg (d : ℕ) : 0 ≤ tiltedCertMass d := by
  apply sum_nonneg
  intro w _
  exact mul_nonneg (by unfold fairWeight; positivity) (multiplier_pos w).le

theorem tiltedCertMass_le (d : ℕ) : tiltedCertMass d ≤ certMass d := by
  rw [certMass_eq_sum]
  apply sum_le_sum
  intro w hw
  have hg : (3 : ℝ) ^ oddCount w < 2 ^ w.length := by
    exact_mod_cast (mem_filter.mp hw).2.2.1
  have hm : multiplier w ≤ 1 :=
    le_of_lt ((div_lt_one (by positivity)).mpr hg)
  exact mul_le_of_le_one_right (by unfold fairWeight; positivity) hm

theorem certMass_zero : certMass 0 = 1 / 2 := by
  have h : minimalCertCount 1 = 1 := by decide
  norm_num [certMass, h]

theorem tiltedCertMass_zero : tiltedCertMass 0 = 1 / 4 := by
  have h : minimalCertWords 1 = { [.even] } := by decide
  norm_num [tiltedCertMass, h, fairWeight, multiplier, oddCount]

theorem certificate_mass_partition (D : ℕ) :
    (∑ d ∈ range D, certMass d) + (neverNegCount D : ℝ) / 2 ^ D = 1 := by
  induction D with
  | zero =>
    have h : neverNegCount 0 = 1 := by decide
    norm_num [h]
  | succ D ih =>
    have hc : (neverNegCount (D + 1) : ℝ) + minimalCertCount (D + 1) =
        2 * neverNegCount D := by
      exact_mod_cast neverNegCount_add_minimalCertCount D
    rw [sum_range_succ]
    unfold certMass
    rw [pow_succ]
    calc
      _ = (∑ d ∈ range D, (minimalCertCount (d + 1) : ℝ) / 2 ^ (d + 1)) +
          ((neverNegCount (D + 1) : ℝ) + minimalCertCount (D + 1)) / (2 ^ D * 2) := by ring
      _ = _ := by rw [hc]; unfold certMass at ih; convert ih using 1; ring

theorem certificate_hasSum : HasSum certMass 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg certMass_nonneg 1).mpr
  have he : (fun D => ∑ d ∈ range D, certMass d) =
      (fun D => 1 - (neverNegCount D : ℝ) / 2 ^ D) := by
    funext D
    linarith [certificate_mass_partition D]
  rw [he]
  simpa using tendsto_const_nhds.sub PaperBSurvivorDecay.neverNegCount_div_pow_tendsto_zero

theorem tilted_summable : Summable tiltedCertMass :=
  Summable.of_nonneg_of_le tiltedCertMass_nonneg tiltedCertMass_le certificate_hasSum.summable

theorem stopped_moment_le : (∑' d, tiltedCertMass d) ≤ 3 / 4 := by
  have hf := certificate_hasSum.summable.tsum_eq_zero_add
  have ht := tilted_summable.tsum_eq_zero_add
  have htail : (∑' d, tiltedCertMass (d + 1)) ≤ ∑' d, certMass (d + 1) :=
    Summable.tsum_le_tsum (fun d => tiltedCertMass_le (d + 1))
      (tilted_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h))
      (certificate_hasSum.summable.comp_injective (fun _ _ h => Nat.add_right_cancel h))
  rw [certificate_hasSum.tsum_eq, certMass_zero] at hf
  rw [tiltedCertMass_zero] at ht
  linarith

/-- A complete prefix-free certificate family can lose multiplier moment. -/
theorem complete_family_moment_loss :
    (∀ u v, IsMinimalCertificate u → IsMinimalCertificate v → u <+: v → u = v) ∧
    HasSum certMass 1 ∧ Summable tiltedCertMass ∧
    (∑' d, tiltedCertMass d) ≤ 3 / 4 ∧ (∑' d, tiltedCertMass d) ≠ 1 := by
  refine ⟨fun _ _ => certificate_prefix_free, certificate_hasSum, tilted_summable,
    stopped_moment_le, ?_⟩
  linarith [stopped_moment_le]

end Problems.Juggler.CollatzMoments
