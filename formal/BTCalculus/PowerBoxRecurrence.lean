import BTCalculus.FourierBoxRecurrence
import BTCalculus.PowerPhaseAsymptotics

/-! # Simultaneous recurrence for distinct noninteger powers

All nonzero Fourier modes cancel by the derivative-asymptotic theorem.
The qualitative Weyl criterion then supplies arbitrarily late box visits.
-/

noncomputable section

namespace BTCalculus.PowerBoxRecurrence

open Finset Filter
open scoped Topology
open BTCalculus.WeylDifferencing BTCalculus.PowerPhaseAsymptotics
open BTCalculus.FourierBoxRecurrence

/-- Every positive box is visited by any fixed family of scaled distinct noninteger powers. -/
theorem exists_ge_power_fract_box {d : Type*} [Fintype d]
    (p w : d → ℝ) (hinj : Function.Injective p)
    (hp : ∀ i, 0 < p i ∧ ∀ m : ℕ, p i ≠ (m : ℝ))
    (hw : ∀ i, w i ≠ 0) {A : ℝ} (hA : 0 < A) (B : ℝ)
    (a b : d → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i < b i) (T : ℕ) :
    ∃ n : ℕ, T ≤ n ∧ ∀ i,
      a i < Int.fract (w i * (A * (n : ℝ) + B) ^ p i) ∧
      Int.fract (w i * (A * (n : ℝ) + B) ^ p i) < b i := by
  classical
  apply exists_ge_fract_box_of_phase (fun n i => w i * (A * (n : ℝ) + B) ^ p i)
    _ a b ha hb hab T
  intro k hk
  have hnonzero : ∃ i ∈ (univ : Finset d), (k i : ℝ) * w i ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
    refine ⟨i, mem_univ i, mul_ne_zero ?_ (hw i)⟩
    exact_mod_cast hi
  have hlim := tendsto_distinct_noninteger_power_average univ
    (fun i => (k i : ℝ) * w i) p (hinj.injOn)
    (fun i _ => hp i) hnonzero hA B
  simpa only [mul_assoc] using hlim

end BTCalculus.PowerBoxRecurrence
