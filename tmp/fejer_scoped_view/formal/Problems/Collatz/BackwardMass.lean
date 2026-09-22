import Problems.Collatz.Shortcut
import Problems.Collatz.NegativeMCycles
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The common finite-mass backward ray of the two signed shortcut maps

Every multiple of three has exactly one predecessor under either map:
its double. Thus the ray `3 * 2^k` is infinite and backward closed,
although its total reciprocal mass is only `2/3`.
-/

namespace Problems.Collatz.BackwardMass

open scoped BigOperators

/-- The positive dyadic ray based at three. -/
def ray : Set ℕ := {n | ∃ k : ℕ, n = 3 * 2 ^ k}

theorem three_mem_ray : 3 ∈ ray := ⟨0, by norm_num⟩

theorem ray_dvd_three {n : ℕ} (hn : n ∈ ray) : 3 ∣ n := by
  obtain ⟨k, rfl⟩ := hn
  exact dvd_mul_right _ _

theorem shortcut_preimage_iff {m n : ℕ} (hm : 3 ∣ m) :
    shortcutC n = m ↔ n = 2 * m := by
  obtain ⟨k, rfl⟩ := hm
  unfold shortcutC
  by_cases hn : n % 2 = 0
  · simp only [hn, ite_true]
    omega
  · simp only [hn, ite_false]
    have hp := Nat.mod_two_eq_zero_or_one n
    omega

theorem minus_preimage_iff {m n : ℕ} (hm : 3 ∣ m) :
    negT n = m ↔ n = 2 * m := by
  obtain ⟨k, rfl⟩ := hm
  unfold negT
  by_cases hn : n % 2 = 0
  · simp only [hn, ite_true]
    omega
  · simp only [hn, ite_false]
    have hp := Nat.mod_two_eq_zero_or_one n
    omega

theorem ray_backward_closed_plus (n : ℕ) (hn : shortcutC n ∈ ray) : n ∈ ray := by
  obtain ⟨k, hk⟩ := hn
  have h := (shortcut_preimage_iff (m := 3 * 2 ^ k) (by omega)).mp hk
  exact ⟨k + 1, by rw [h, pow_succ]; ring⟩

theorem ray_backward_closed_minus (n : ℕ) (hn : negT n ∈ ray) : n ∈ ray := by
  obtain ⟨k, hk⟩ := hn
  have h := (minus_preimage_iff (m := 3 * 2 ^ k) (by omega)).mp hk
  exact ⟨k + 1, by rw [h, pow_succ]; ring⟩

theorem ray_param_injective : Function.Injective (fun k : ℕ => 3 * 2 ^ k) := by
  intro a b h
  change 3 * 2 ^ a = 3 * 2 ^ b at h
  have hp : (2 : ℕ) ^ a = 2 ^ b := by omega
  exact (Nat.pow_right_injective (by norm_num : (2 : ℕ) ≤ 2)) hp

theorem ray_infinite : ray.Infinite := by
  have h : ray = Set.range (fun k : ℕ => 3 * 2 ^ k) := by
    ext n
    change (∃ k : ℕ, n = 3 * 2 ^ k) ↔ ∃ k : ℕ, 3 * 2 ^ k = n
    exact exists_congr (fun _ => eq_comm)
  rw [h]
  exact Set.infinite_range_of_injective ray_param_injective

theorem ray_reciprocal_hasSum :
    HasSum (fun k : ℕ => (1 : ℝ) / (3 * 2 ^ k)) (2 / 3 : ℝ) := by
  have h := (hasSum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left
    (1 / 3 : ℝ)
  have he : (fun k : ℕ => (1 : ℝ) / (3 * 2 ^ k)) =
      (fun k : ℕ => (1 / 3 : ℝ) * (1 / 2) ^ k) := by
    funext k
    rw [div_pow]
    simp only [one_pow]
    ring
  rw [he]
  norm_num at h ⊢
  exact h

/-- Every finite subset of the ray has mass at most its convergent geometric sum. -/
theorem finite_ray_mass_le (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ ray) :
    ∑ n ∈ s, (1 : ℝ) / n ≤ 2 / 3 := by
  classical
  choose k hk using hs
  let t : Finset ℕ := s.attach.image (fun n => k n.val n.property)
  have hi : Set.InjOn (fun n : {n // n ∈ s} => k n.val n.property) ↑s.attach := by
    intro a _ b _ hab
    change k a.val a.property = k b.val b.property at hab
    apply Subtype.ext
    rw [hk a.val a.property, hk b.val b.property, hab]
  have he : ∑ n ∈ s, (1 : ℝ) / n = ∑ j ∈ t, (1 : ℝ) / (3 * 2 ^ j) := by
    rw [Finset.sum_image hi, ← Finset.sum_attach s (fun n => (1 : ℝ) / n)]
    apply Finset.sum_congr rfl
    intro n _
    have he := congrArg (fun z : ℕ => (1 : ℝ) / z) (hk n.val n.property)
    simpa using he
  rw [he, ← ray_reciprocal_hasSum.tsum_eq]
  exact ray_reciprocal_hasSum.summable.sum_le_tsum t (fun _ _ => by positivity)

/-- The ray is not a fate class: its base point leaves it under the plus map. -/
theorem ray_not_forward_closed_plus : ¬∀ n, n ∈ ray → shortcutC n ∈ ray := by
  intro h
  have hd := ray_dvd_three (h 3 three_mem_ray)
  norm_num [shortcutC] at hd

/-- The same distinction between backward closure and a fate holds for the minus map. -/
theorem ray_not_forward_closed_minus : ¬∀ n, n ∈ ray → negT n ∈ ray := by
  intro h
  have hd := ray_dvd_three (h 3 three_mem_ray)
  norm_num [negT] at hd

/-- One explicit infinite backward-closed set defeats harmonic-mass divergence for both signs. -/
theorem backward_mass_counterexample :
    ray.Infinite ∧
    (∀ n, shortcutC n ∈ ray → n ∈ ray) ∧
    (∀ n, negT n ∈ ray → n ∈ ray) ∧
    HasSum (fun k : ℕ => (1 : ℝ) / (3 * 2 ^ k)) (2 / 3 : ℝ) ∧
    (∀ s : Finset ℕ, (∀ n ∈ s, n ∈ ray) → ∑ n ∈ s, (1 : ℝ) / n ≤ 2 / 3) :=
  ⟨ray_infinite, ray_backward_closed_plus, ray_backward_closed_minus,
    ray_reciprocal_hasSum, finite_ray_mass_le⟩

end Problems.Collatz.BackwardMass
