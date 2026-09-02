import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Problems.Juggler.WalkTransport
import Problems.Juggler.WalkChargeItineraries

namespace Problems.Juggler

/-!
# Hug charge maximality (Paper A Theorem 5.4, analytic half)

The walk charge of a state at weight `W = 2^u` and reduced log-base
`ν = log n'` is

`stateCharge ν W = 1 / (e^{Wν} · W · ν) = 1 / (n'^{2^u} · 2^u · log n')`,

the paper's `g(u)` written through the rational weight `W = 3^a/2^k`.
Since `g` is antitone in the weight (`stateCharge_antitone`) and the
hug itinerary carries the pointwise-least admissible odd count
(`hugOdds_le_of_admissible`), the exact hug itinerary maximises the total
walk charge over **all** admissible exponent walks
(`hug_charge_maximal`) — the analytic half of Theorem 5.4, with no
charge integral needed.

Chaining with the transport inequality (`cycleMin_transport`) gives
the §5.2 consequence in full: on a minimum-based cycle with `n ≥ 400`
and positive reduced base, the cyclic defect sum is bounded by the
walk charge of the realized itinerary (`cycleMin_defect_le_charge`) and
hence by the hug charge (`cycleMin_defect_le_hug_charge`):

`Σ_k 1/(x_k log x_k) ≤ Σ_k g(w_k) ≤ Σ_k g(hugWeight k)`.

Uniqueness of the maximiser (the strict exchange within a fixed
`(L, o)` class) stays with the human proof; the rotation average
(Prop 5.5) and Denjoy–Koksma (Thm 5.7) remain analytic prose. Not a
cycle obstruction and not a halt theorem.
-/

/-!
## The state charge and its monotonicity
-/

/-- The per-state walk charge at reduced log-base `ν` and weight `W`:
`g = 1/(e^{Wν}·W·ν)`. With `W = 2^u` and `ν = log n'` this is the
paper's `g(u) = 1/(n'^{2^u}·2^u·log n')`. -/
noncomputable def stateCharge (ν W : ℝ) : ℝ :=
  1 / (Real.exp (W * ν) * W * ν)

theorem stateCharge_pos {ν W : ℝ} (hν : 0 < ν) (hW : 0 < W) :
    0 < stateCharge ν W := by
  rw [stateCharge]
  positivity

/-- The charge is antitone in the weight: heavier states are cheaper
to visit. This is the paper's "`g` is strictly decreasing in `u`"
in the (non-strict) form the envelope uses. -/
theorem stateCharge_antitone {ν W₁ W₂ : ℝ} (hν : 0 < ν)
    (hW₁ : 0 < W₁) (h : W₁ ≤ W₂) :
    stateCharge ν W₂ ≤ stateCharge ν W₁ := by
  rw [stateCharge, stateCharge]
  apply one_div_le_one_div_of_le
  · have := Real.exp_pos (W₁ * ν)
    positivity
  · have hexp : Real.exp (W₁ * ν) ≤ Real.exp (W₂ * ν) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h hν.le)
    have h1 : Real.exp (W₁ * ν) * W₁ ≤ Real.exp (W₂ * ν) * W₂ :=
      mul_le_mul hexp h hW₁.le (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right h1 hν.le

/-!
## The hug weight profile
-/

/-- The weight profile of the exact hug itinerary:
`hugWeight k = 3^{hugOdds k} / 2^k`, the pointwise-least admissible
walk weight. -/
noncomputable def hugWeight (k : ℕ) : ℝ :=
  3 ^ hugOdds k / 2 ^ k

theorem one_le_hugWeight (k : ℕ) : 1 ≤ hugWeight k := by
  rw [hugWeight, le_div_iff₀ (by positivity), one_mul]
  exact_mod_cast hugOdds_pow_ge k

theorem hugWeight_pos (k : ℕ) : 0 < hugWeight k :=
  lt_of_lt_of_le one_pos (one_le_hugWeight k)

/-- The hug weight is pointwise below every admissible weight
profile (real form of `hugOdds_le_of_admissible`). -/
theorem hugWeight_le_of_admissible {a : ℕ → ℕ} (k : ℕ)
    (ha : 2 ^ k ≤ 3 ^ a k) :
    hugWeight k ≤ (3 : ℝ) ^ a k / 2 ^ k := by
  rw [hugWeight]
  gcongr
  · norm_num
  · exact hugOdds_least ha

/-- On a minimum-based cycle, the hug weight is pointwise below the
realized walk weight (real form of `cycleMin_prefix_odds_ge_hug`). -/
theorem hugWeight_le_walkWeight {n : ℕ} {w : List Branch} (hn : 2 ≤ n)
    (h : CycleMin n w) {k : ℕ} (hk : k ≤ w.length) :
    hugWeight k ≤ walkWeight w k := by
  rw [hugWeight, walkWeight]
  gcongr
  · norm_num
  · exact cycleMin_prefix_odds_ge_hug hn h k hk

/-!
## Theorem 5.4, analytic half: the hug itinerary maximises the charge
-/

/-- **Hug charge maximality.** For any admissible odd-count profile
`a` (every prefix satisfies `2^k ≤ 3^{a k}`) and any reduced
log-base `ν > 0`, the total walk charge is at most the hug charge.
This is the analytic half of Paper A Theorem 5.4, strengthened from
the fixed-`(L,o)` class to all admissible walks. -/
theorem hug_charge_maximal {ν : ℝ} (hν : 0 < ν) (a : ℕ → ℕ)
    (ha : ∀ k, 2 ^ k ≤ 3 ^ a k) (L : ℕ) :
    ∑ k ∈ Finset.range L, stateCharge ν ((3 : ℝ) ^ a k / 2 ^ k) ≤
      ∑ k ∈ Finset.range L, stateCharge ν (hugWeight k) :=
  Finset.sum_le_sum fun k _ =>
    stateCharge_antitone hν (hugWeight_pos k)
      (hugWeight_le_of_admissible k (ha k))

/-!
## The §5.2 consequence: defect sum ≤ walk charge ≤ hug charge
-/

/-- **Defect sum is bounded by the walk charge at the reduced
base.** On a minimum-based cycle with `n ≥ 400` and positive reduced
log-base `ν = log n − D`, each cyclic defect `1/(x_k log x_k)` is
bounded by the charge of the realized weight: exponentiating the
transport inequality gives `x_k ≥ e^{w_k ν}` and
`log x_k ≥ w_k ν`. -/
theorem cycleMin_defect_le_charge {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w)
    (hν : 0 < Real.log n - transportDeficit n w) :
    ∑ k ∈ Finset.range w.length,
        1 / ((floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n)) ≤
      ∑ k ∈ Finset.range w.length,
        stateCharge (Real.log n - transportDeficit n w)
          (walkWeight w k) := by
  set ν := Real.log n - transportDeficit n w with hνdef
  refine Finset.sum_le_sum fun k hk => ?_
  have hkL : k ≤ w.length := (Finset.mem_range.mp hk).le
  have hW1 : 1 ≤ walkWeight w k := one_le_walkWeight (by omega) h hkL
  have hW0 : 0 < walkWeight w k := lt_of_lt_of_le one_pos hW1
  have hWν : 0 < walkWeight w k * ν := mul_pos hW0 hν
  have htr : walkWeight w k * ν ≤ Real.log (floorPower^[k] n) :=
    cycleMin_transport hn h hkL
  have hxnat : 0 < floorPower^[k] n :=
    lt_of_lt_of_le (by omega) (cycleMin_iterate_ge h k hkL)
  have hxpos : (0 : ℝ) < (floorPower^[k] n : ℝ) := by exact_mod_cast hxnat
  have hexp : Real.exp (walkWeight w k * ν) ≤ (floorPower^[k] n : ℝ) := by
    calc Real.exp (walkWeight w k * ν)
        ≤ Real.exp (Real.log (floorPower^[k] n)) := Real.exp_le_exp.mpr htr
      _ = (floorPower^[k] n : ℝ) := Real.exp_log hxpos
  rw [stateCharge]
  apply one_div_le_one_div_of_le
  · have := Real.exp_pos (walkWeight w k * ν)
    positivity
  · calc Real.exp (walkWeight w k * ν) * walkWeight w k * ν
        = Real.exp (walkWeight w k * ν) * (walkWeight w k * ν) := by ring
      _ ≤ (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) :=
          mul_le_mul hexp htr hWν.le hxpos.le

/-- **Defect sum is bounded by the hug charge at the reduced base**
(the §5.2 consequence composed with Theorem 5.4): on a minimum-based
cycle with `n ≥ 400` and positive reduced log-base, the cyclic
defect sum is at most the hug charge of the same length. This is the
full structural half of the walk-charge envelope; only the rotation
average and Denjoy–Koksma evaluation of the right-hand side remain
analytic. -/
theorem cycleMin_defect_le_hug_charge {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w)
    (hν : 0 < Real.log n - transportDeficit n w) :
    ∑ k ∈ Finset.range w.length,
        1 / ((floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n)) ≤
      ∑ k ∈ Finset.range w.length,
        stateCharge (Real.log n - transportDeficit n w) (hugWeight k) := by
  refine le_trans (cycleMin_defect_le_charge hn h hν)
    (Finset.sum_le_sum fun k hk => ?_)
  exact stateCharge_antitone hν (hugWeight_pos k)
    (hugWeight_le_walkWeight (by omega) h (Finset.mem_range.mp hk).le)

end Problems.Juggler
