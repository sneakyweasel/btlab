import Problems.Collatz.FibreSubsolutions
import Problems.Collatz.FibreLowerTransfer

/-! # Near-critical periodic weights already require global cell lower bounds

A single nonzero coordinate of a periodic subsolution supplies a geometric
lower bound at every ordinary positive odd unit root, after one inverse
step. The constant depends on the level and weight, but the rate does not.
Consequently a near-critical family implies a uniform subexponential floor.
This necessary condition does not prove that floor or coefficient divergence.
-/

noncomputable section

namespace Problems.Collatz.FibreRateBarrier

open FibreMass FibreActual FibreSubsolutions FibreLowerTransfer FibreUnitComparison Filter
open scoped Topology

private theorem cap_le_one (r : ℕ) (b : Level r) : unitCap r b ≤ 1 := by
  unfold unitCap
  split_ifs <;> norm_num

/-- Any coordinate of a bounded periodic subsolution gives a global
geometric minorant at the same rate. The explicit cost and single depth
shift are independent of the target integer and all later depths. -/
theorem global_lower_of_subsolution (plus : Bool) (r : ℕ) {q : ℝ}
    (hq : 0 ≤ q) {h : Level r → ℝ} (hh : Subsolution plus r q h)
    (b : Level r) (d : ℕ) {a : ℕ} (ha : 1 ≤ a) (ho : Odd a) (hu : a % 3 ≠ 0) :
    (stepCost r * h b) * q^d ≤ coarse plus (d+1) a := by
  obtain ⟨m, hm, _, hb, _, ht⟩ := exists_coarse_lower_transport plus r b ha ho hu
  have hl := FibreMinorants.coarse_geometric_lower plus r h hh.nonneg
    (fun x => (hh.le_cap x).trans (cap_le_one r x)) hq hh.reproduce d hm
  rw [hb] at hl
  have hc := (mul_le_mul_of_nonneg_left hl (stepCost_pos r).le).trans (ht d)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hc

/-- A nonzero coordinate therefore forces a positive global constant.
No positivity assumption at the other residue coordinates is necessary. -/
theorem exists_global_lower (plus : Bool) (r : ℕ) {q : ℝ} (hq : 0 ≤ q)
    {h : Level r → ℝ} (hh : Subsolution plus r q h)
    {b : Level r} (hb : 0 < h b) :
    ∃ c : ℝ, 0 < c ∧ ∀ d a : ℕ, 1 ≤ a → Odd a → a % 3 ≠ 0 →
      c*q^d ≤ coarse plus (d+1) a := by
  exact ⟨stepCost r * h b, mul_pos (stepCost_pos r) hb,
    fun d a ha ho hu => global_lower_of_subsolution plus r hq hh b d ha ho hu⟩

/-- Uniform subexponential lower decay in geometric form: every rate below
one admits a positive constant working at every depth and every ordinary
positive odd unit root. The constant may depend on the chosen rate. -/
def UniformSubcriticalLower (plus : Bool) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∃ c : ℝ, 0 < c ∧
    ∀ d a : ℕ, 1 ≤ a → Odd a → a % 3 ≠ 0 → c*t^d ≤ coarse plus (d+1) a

/-- Rates approaching one for nonzero periodic subsolutions imply uniform
subexponential lower decay. The positive coordinate may change with the
level. No fixed-root prefactor estimate or divergence is needed for this
necessary condition, and neither is produced by the conclusion. -/
theorem uniform_lower_of_nearcritical_weights (plus : Bool)
    (r : ℕ → ℕ) (q : ℕ → ℝ) (h : (i : ℕ) → Level (r i) → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hlim : Tendsto q atTop (𝓝 1))
    (hh : ∀ i, Subsolution plus (r i) (q i) (h i))
    (hnonzero : ∀ i, ∃ b, 0 < h i b) : UniformSubcriticalLower plus := by
  intro t ht ht1
  have hev : ∀ᶠ i in atTop, t < q i := (tendsto_order.mp hlim).1 t ht1
  obtain ⟨i, hi⟩ := hev.exists
  obtain ⟨b, hb⟩ := hnonzero i
  obtain ⟨c, hc, hl⟩ := exists_global_lower plus (r i) (hq i) (hh i) hb
  refine ⟨c, hc, fun d a ha ho hu => ?_⟩
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hi.le d) hc.le).trans
    (hl d a ha ho hu)

/-- Even without a quantitative root-to-deficit bound, nonzero greatest
tables at rates approaching one already force the global floor condition.
Thus using a fixed root to witness nonzeroness does not make the rate-family
existence problem purely local. -/
theorem uniform_lower_of_maximal_weights (plus : Bool) (r : ℕ → ℕ)
    (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) (hlim : Tendsto q atTop (𝓝 1))
    (a : ℕ) (ha : ∀ i, 0 < maximalWeight plus (r i) (q i) (residue (r i) a)) :
    UniformSubcriticalLower plus := by
  exact uniform_lower_of_nearcritical_weights plus r q
    (fun i => maximalWeight plus (r i) (q i)) hq hlim
    (fun i => maximalWeight_subsolution plus (r i) (hq i))
    (fun i => ⟨residue (r i) a, ha i⟩)

end Problems.Collatz.FibreRateBarrier
