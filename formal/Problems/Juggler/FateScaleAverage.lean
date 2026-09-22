import Mathlib.Algebra.BigOperators.Module
import Problems.Juggler.FatePressureCorollary
import Problems.Juggler.FatePoorProduction
import Problems.Juggler.FateOEWeighted

namespace Problems.Juggler

open Finset
open scoped Classical

namespace ScaleAverage

/-!
# Termination from a scale average of the actual stopped odd pressure

This checks the conditional implication in `juggler_pressure_external_average.md`.
The arithmetic bound on cumulative pressure remains an explicit hypothesis.
The reusable implication takes its contagion exponent as an explicit input.
The unconditional specialization uses `100/203`; the `5/8` specialization
retains the open actual OOEE production bound.
-/

/-- Prefix-sum domination is preserved by nonnegative decreasing weights. -/
theorem weighted_prefix_le {f g w : ℕ → ℝ}
    (hpre : ∀ K, ∑ k ∈ range K, f k ≤ ∑ k ∈ range K, g k)
    (hw : ∀ k, 0 ≤ w k) (hanti : Antitone w) (K : ℕ) :
    ∑ k ∈ range K, w k * f k ≤ ∑ k ∈ range K, w k * g k := by
  simp_rw [← smul_eq_mul]
  rw [sum_range_by_parts w f K, sum_range_by_parts w g K]
  simp only [smul_eq_mul]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (hpre K) (hw _)
  · apply sum_le_sum
    intro k _
    exact mul_le_mul_of_nonpos_left (hpre (k + 1))
      (sub_nonpos.mpr (hanti (Nat.le_succ k)))

/-- The discrete derivative of a convex power has its elementary upper bound. -/
theorem rpow_step_le {s : ℝ} (hs : 1 ≤ s) (k : ℕ) :
    ((k : ℝ) + 1) ^ s - (k : ℝ) ^ s ≤ s * ((k : ℝ) + 1) ^ (s - 1) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hu : -1 ≤ -(1 / ((k : ℝ) + 1)) := by
    have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := (div_le_one hk).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    linarith
  have hb := mul_le_mul_of_nonneg_left
    (one_add_mul_self_le_rpow_one_add hu hs) (Real.rpow_nonneg hk.le s)
  have heq : ((k : ℝ) + 1) * (1 + -(1 / ((k : ℝ) + 1))) = k := by
    field_simp
    ring
  rw [← Real.mul_rpow hk.le (by linarith : 0 ≤ 1 + -(1 / ((k : ℝ) + 1))), heq] at hb
  rw [Real.rpow_sub_one hk.ne']
  have he : ((k : ℝ) + 1) ^ s * (1 + s * -(1 / ((k : ℝ) + 1))) =
      ((k : ℝ) + 1) ^ s - s * (((k : ℝ) + 1) ^ s / ((k : ℝ) + 1)) := by ring
  rw [he] at hb
  linarith

/-- A power is bounded by the sum of its upper discrete derivatives. -/
theorem rpow_le_sum {s : ℝ} (hs : 1 ≤ s) (K : ℕ) :
    (K : ℝ) ^ s ≤ ∑ k ∈ range K, s * ((k : ℝ) + 1) ^ (s - 1) := by
  induction K with
  | zero => simp [Real.zero_rpow (by linarith : s ≠ 0)]
  | succ K ih =>
      rw [sum_range_succ]
      push_cast
      linarith [rpow_step_le hs K]

/-- Abel summation: a cumulative `K^s` bound gives the weighted `K^(1-e)` bound
when `r = s - 1 + e`. No pointwise bound on the individual terms is assumed. -/
theorem weighted_rpow_sum_le {ρ : ℕ → ℝ} {D s r e : ℝ}
    (hD : 0 ≤ D) (hs : 1 ≤ s) (hr : 0 ≤ r) (he0 : 0 < e) (he1 : e < 1)
    (hre : s - 1 - r = -e)
    (hpre : ∀ K, ∑ k ∈ range K, ρ k ≤ D * (K : ℝ) ^ s) (K : ℕ) :
    ∑ k ∈ range K, ρ k * ((k : ℝ) + 1) ^ (-r) ≤
      D * s * ((K : ℝ) ^ (1 - e) / (1 - e)) := by
  have hcmp : ∀ K, ∑ k ∈ range K, ρ k ≤
      ∑ k ∈ range K, D * (s * ((k : ℝ) + 1) ^ (s - 1)) := by
    intro K
    rw [← mul_sum]
    exact (hpre K).trans (mul_le_mul_of_nonneg_left (rpow_le_sum hs K) hD)
  have hanti : Antitone (fun k : ℕ => ((k : ℝ) + 1) ^ (-r)) := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hr)
    exact_mod_cast Nat.add_le_add_right hij 1
  have h := weighted_prefix_le hcmp (fun k => Real.rpow_nonneg (by positivity) _) hanti K
  have heq : ∀ k : ℕ,
      ((k : ℝ) + 1) ^ (-r) * (D * (s * ((k : ℝ) + 1) ^ (s - 1))) =
        D * s * ((k : ℝ) + 1) ^ (-e) := by
    intro k
    calc _ = D * s * (((k : ℝ) + 1) ^ (s - 1) * ((k : ℝ) + 1) ^ (-r)) := by ring
      _ = _ := by rw [← Real.rpow_add (by positivity), show s - 1 + -r = -e by linarith]
  simp_rw [heq] at h
  rw [← mul_sum] at h
  calc _ = ∑ k ∈ range K, ((k : ℝ) + 1) ^ (-r) * ρ k := by
          apply sum_congr rfl; intro k _; ring
    _ ≤ D * s * ∑ k ∈ range K, ((k : ℝ) + 1) ^ (-e) := h
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_rpow_neg_le he0 he1 K) (by positivity)

/-- The actual odd starts in one dyadic block, stopped at the certified floor. -/
noncomputable def liveOdds (N₀ y d : ℕ) : Finset ℕ :=
  (Ioc y (2 * y)).filter (fun n => n % 2 = 1 ∧ liveTo N₀ n d)

/-- The manuscript's `Z_d(y)`, using the actual Juggler itinerary. -/
noncomputable def oddPressure (N₀ y d : ℕ) (θ : ℝ) : ℝ :=
  ∑ n ∈ liveOdds N₀ y d, Real.exp (θ * oddCount (itinerary n d))

/-- Normalized pressure on `(2^k,2^(k+1)]`; `a` is the reference moment per step. -/
noncomputable def rho (N₀ : ℕ) (C θ a : ℝ) (k : ℕ) : ℝ :=
  oddPressure N₀ (2 ^ k) (depth C N₀ (2 ^ k)) θ /
    (((2 : ℝ) ^ k / 2) * a ^ depth C N₀ (2 ^ k))

/-- Global big-O form of `sum_{k=k₀}^{k₀+K-1} rho_k ≤ K^(1+η+o(1))`.
The arbitrary constant absorbs the finitely many initial scales. -/
def Bound (N₀ k₀ : ℕ) (C θ a η : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℕ,
    ∑ k ∈ range K, rho N₀ C θ a (k₀ + k) ≤ D * (K : ℝ) ^ (1 + η + ε)

theorem rho_nonneg (N₀ : ℕ) (C θ : ℝ) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 ≤ rho N₀ C θ a k := by
  unfold rho oddPressure
  positivity

/-- The envelope and exponential Markov inequality on the odd block itself. -/
theorem odd_block_le {N₀ y : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m)
    (hy : N₀ < 2 * y) {C θ : ℝ} (hC : 0 < C) (hθ : 0 ≤ θ) :
    ∑ n ∈ oddFailures y, (1 : ℝ) / n ≤
      oddPressure N₀ y (depth C N₀ y) θ *
        Real.exp (-(θ * pC C * depth C N₀ y)) / y := by
  let d := depth C N₀ y
  have hy1 : 1 ≤ y := by omega
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy1
  have hd1 : 1 ≤ d := one_le_depth hN hy hC
  have hd : C * Real.logb 2 (Real.log ((2 * y : ℕ) : ℝ) / Real.log N₀) ≤ d := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, scaleL, scaleRatio, depth, d] using
      (Nat.le_ceil (C * scaleL N₀ y))
  have hsub : oddFailures y ⊆ liveOdds N₀ y d := by
    intro n hn
    have hl := (mem_filter.mp (Pressure.oddFailures_subset_live hfloor y d hn)).2
    have hn' := mem_filter.mp hn
    exact mem_filter.mpr ⟨hn'.1, hn'.2.1, hl⟩
  have hcard : (oddFailures y).card * Real.exp (θ * pC C * d) ≤ oddPressure N₀ y d θ := by
    calc _ = ∑ n ∈ oddFailures y, Real.exp (θ * pC C * d) := by simp
      _ ≤ ∑ n ∈ oddFailures y, Real.exp (θ * oddCount (itinerary n d)) := by
        apply sum_le_sum
        intro n hn
        have hn' := mem_filter.mp (hsub hn)
        have hb := live_oddCount_ge hN (by omega) (mem_Ioc.mp hn'.1).2 hn'.2.2 C hC hd1 hd
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hb hθ]
      _ ≤ oddPressure N₀ y d θ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (Real.exp_pos _).le)
  have hc : ((oddFailures y).card : ℝ) ≤
      oddPressure N₀ y d θ * Real.exp (-(θ * pC C * d)) := by
    have h := mul_le_mul_of_nonneg_right hcard (Real.exp_pos (-(θ * pC C * d))).le
    simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using h
  calc _ = ∑ n ∈ oddMembers (fun n => ¬ReachesOne n) y, (1 : ℝ) / n := by
          rw [oddMembers_not_reachesOne]
    _ ≤ (oddFailures y).card / y := by
          simpa only [oddMembers_not_reachesOne] using oddMembers_sum_le (fun n => ¬ReachesOne n) hy1
    _ ≤ _ := div_le_div_of_nonneg_right hc hyR.le

/-- The dyadic change of variables, with its constant retained. -/
theorem block_le_rho {N₀ k₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (hk₀ : N₀ < 2 ^ (k₀ + 1))
    {C θ a : ℝ} (hC : 0 < C) (hθ : 0 ≤ θ) (ha : 0 < a)
    (hD : 0 ≤ θ * pC C - Real.log a) (k : ℕ) :
    ∑ n ∈ oddFailures (2 ^ (k₀ + k)), (1 : ℝ) / n ≤
      (1 / 2 * (Real.log 2 / Real.log N₀) ^ (-(C * (θ * pC C - Real.log a) / Real.log 2))) *
        (rho N₀ C θ a (k₀ + k) * ((k : ℝ) + 1) ^ (-(C * (θ * pC C - Real.log a) / Real.log 2))) := by
  let j := k₀ + k
  let y : ℕ := 2 ^ j
  let d := depth C N₀ y
  let r := C * (θ * pC C - Real.log a) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N₀))
  have hr : 0 ≤ r := div_nonneg (mul_nonneg hC.le hD) hlog2.le
  have hy : N₀ < 2 * y := by
    calc N₀ < 2 ^ (k₀ + 1) := hk₀
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by dsimp [j]; omega)
      _ = 2 * y := by dsimp [y]; rw [pow_succ]; omega
  have hyR : (0 : ℝ) < y := by dsimp [y]; positivity
  have hρ : 0 ≤ rho N₀ C θ a j := rho_nonneg N₀ C θ ha j
  have hnorm : oddPressure N₀ y d θ = rho N₀ C θ a j * ((y : ℝ) / 2 * a ^ d) := by
    dsimp [rho, y, d]
    push_cast
    rw [div_mul_cancel₀ _ (by positivity)]
  have hscale : scaleRatio N₀ y = ((j : ℝ) + 1) * (Real.log 2 / Real.log N₀) := by
    dsimp [scaleRatio, y]
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  have hΛ : 0 < scaleRatio N₀ y := by rw [hscale]; positivity
  have hdecay := OneSided.exp_le_rpow_scale hΛ hD (Nat.le_ceil (C * scaleL N₀ y))
  have hpow : a ^ d * Real.exp (-(θ * pC C * d)) =
      Real.exp (-(d * (θ * pC C - Real.log a))) := by
    rw [← Real.exp_log ha, ← Real.exp_nat_mul, ← Real.exp_add, Real.log_exp]
    congr 1
    ring
  have hshift : ((j : ℝ) + 1) ^ (-r) ≤ ((k : ℝ) + 1) ^ (-r) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    dsimp [j]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k₀]
  calc _ ≤ oddPressure N₀ y d θ * Real.exp (-(θ * pC C * d)) / y :=
          odd_block_le hN hfloor hy hC hθ
    _ = 1 / 2 * rho N₀ C θ a j * Real.exp (-(d * (θ * pC C - Real.log a))) := by
          rw [hnorm, ← hpow]
          field_simp
    _ ≤ 1 / 2 * rho N₀ C θ a j * (scaleRatio N₀ y) ^ (-r) :=
          mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = (1 / 2 * (Real.log 2 / Real.log N₀) ^ (-r)) *
          (rho N₀ C θ a j * ((j : ℝ) + 1) ^ (-r)) := by
          rw [hscale, Real.mul_rpow (by positivity) (by positivity)]
          ring
    _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hshift hρ)
          positivity

/-- Summing the actual dyadic odd blocks under a cumulative pressure bound. -/
theorem odd_mass_le {k₀ : ℕ} {ρ : ℕ → ℝ} {c D s r e : ℝ}
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hs : 1 ≤ s) (hr : 0 ≤ r)
    (he0 : 0 < e) (he1 : e < 1) (hre : s - 1 - r = -e)
    (hpre : ∀ K, ∑ k ∈ range K, ρ k ≤ D * (K : ℝ) ^ s)
    (hblock : ∀ k, ∑ n ∈ oddFailures (2 ^ (k₀ + k)), (1 : ℝ) / n ≤
      c * (ρ k * ((k : ℝ) + 1) ^ (-r))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ K : ℕ, k₀ ≤ K →
      oddLogMass (fun n => ¬ReachesOne n) (2 ^ K) ≤ B * ((K : ℝ) + 1) ^ (1 - e) := by
  let F := fun n => ¬ReachesOne n
  let B₀ := oddLogMass F (2 ^ k₀)
  have hB₀ : 0 ≤ B₀ := oddLogMass_nonneg F _
  have hsum : ∀ K, oddLogMass F (2 ^ (k₀ + K)) ≤
      B₀ + c * ∑ k ∈ range K, ρ k * ((k : ℝ) + 1) ^ (-r) := by
    intro K
    induction K with
    | zero => simp [B₀]
    | succ K ih =>
        have hpow : (2 : ℕ) ^ (k₀ + (K + 1)) = 2 * 2 ^ (k₀ + K) := by
          rw [← Nat.add_assoc, pow_succ, mul_comm]
        rw [hpow, oddLogMass_double, show oddMembers F (2 ^ (k₀ + K)) =
          oddFailures (2 ^ (k₀ + K)) from oddMembers_not_reachesOne _]
        rw [sum_range_succ, mul_add]
        linarith [hblock K]
  have hcoef : 0 ≤ c * D * s / (1 - e) := by positivity
  refine ⟨B₀ + c * D * s / (1 - e), by positivity, ?_⟩
  intro J hJ
  let K := J - k₀
  have hj : k₀ + K = J := by dsimp [K]; omega
  have hweighted := weighted_rpow_sum_le hD hs hr he0 he1 hre hpre K
  have hpow : (K : ℝ) ^ (1 - e) ≤ ((J : ℝ) + 1) ^ (1 - e) := by
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    have : K ≤ J := Nat.sub_le J k₀
    exact_mod_cast (show K ≤ J + 1 by omega)
  have hpow1 : 1 ≤ ((J : ℝ) + 1) ^ (1 - e) :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) J]) (by linarith)
  calc oddLogMass F (2 ^ J) = oddLogMass F (2 ^ (k₀ + K)) := by rw [hj]
    _ ≤ B₀ + c * ∑ k ∈ range K, ρ k * ((k : ℝ) + 1) ^ (-r) := hsum K
    _ ≤ B₀ + c * (D * s * ((K : ℝ) ^ (1 - e) / (1 - e))) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hweighted hc)
    _ = B₀ + (c * D * s / (1 - e)) * (K : ℝ) ^ (1 - e) := by ring
    _ ≤ (B₀ + c * D * s / (1 - e)) * ((J : ℝ) + 1) ^ (1 - e) := by
          nlinarith [mul_le_mul_of_nonneg_left hpow hcoef]

/-- The exact lower bound needed by the pressure reduction, for any positive failure. -/
def FailureMassLowerBound (lam : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ReachesOne n →
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      c * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x

/-- Any subcritical odd harmonic-mass bound contradicts a supplied contagion
bound. The even-tree logarithm is absorbed using the strict exponent gap. -/
theorem conjecture_of_odd_mass_of_contagion {lam : ℝ}
    (hcontagion : FailureMassLowerBound lam) {k₀ : ℕ} {B β : ℝ} (hB : 0 ≤ B)
    (hβ0 : 0 < β) (hβ : β < lam)
    (hodd : ∀ K : ℕ, k₀ ≤ K → oddLogMass (fun n => ¬ReachesOne n) (2 ^ K) ≤
      B * ((K : ℝ) + 1) ^ β) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  intro n hn
  by_contra hfail
  obtain ⟨c, hc, x₀, hlow⟩ := hcontagion n hn hfail
  let δ := (lam - β) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hsplit : lam = (δ + β) + δ := by dsimp [δ]; ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  let D := 3 / 2 * (2 / δ + 1) * B * (2 : ℝ) ^ β
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let c' := c * Real.log 2 ^ lam
  have hc' : 0 < c' := by dsimp [c']; positivity
  obtain ⟨u, hu1, hu⟩ := exists_rpow_gt hδ (D / c')
  let K : ℕ := max (max k₀ x₀) (max 1 ⌈u⌉₊)
  have hKk : k₀ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKx : x₀ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK1 : 1 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKu : u ≤ K := (Nat.le_ceil u).trans (by exact_mod_cast
    (le_trans (le_max_right 1 ⌈u⌉₊) (le_max_right (max k₀ x₀) (max 1 ⌈u⌉₊))))
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK1
  have hK1R : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hpowδ : 1 ≤ (K : ℝ) ^ δ := Real.one_le_rpow hK1R hδ.le
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_natCast_nonneg K
  have hnatlog := natLog_le_logb hK1
  rw [Real.logb] at hnatlog
  have hlogbound := log_le_rpow_div hKR hδ
  have hfactor : (Nat.log 2 K : ℝ) + 1 ≤ (2 / δ + 1) * (K : ℝ) ^ δ := by
    have hratio : Real.log (K : ℝ) / Real.log 2 ≤ 2 * Real.log K := by
      rw [div_le_iff₀ hlog2]
      nlinarith
    have heq : 2 * ((K : ℝ) ^ δ / δ) = (2 / δ) * (K : ℝ) ^ δ := by ring
    nlinarith
  have hKpow : ((K : ℝ) + 1) ^ β ≤ (2 : ℝ) ^ β * (K : ℝ) ^ β := by
    rw [← Real.mul_rpow (by norm_num) hKR.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hβ0.le
  have hupper : logMass (fun n => ¬ReachesOne n) (2 ^ K) ≤ D * (K : ℝ) ^ (δ + β) := by
    have hcover := logMass_le_oddLogMass not_reachesOne_forwardClosed
      (fun h => h reachesOne_one) (2 ^ K)
    rw [Nat.log_pow (by norm_num : 1 < 2)] at hcover
    calc _ ≤ 3 / 2 * ((Nat.log 2 K : ℝ) + 1) *
          oddLogMass (fun n => ¬ReachesOne n) (2 ^ K) := hcover
      _ ≤ 3 / 2 * ((2 / δ + 1) * (K : ℝ) ^ δ) *
          (B * ((2 : ℝ) ^ β * (K : ℝ) ^ β)) := by
            apply mul_le_mul _ ((hodd K hKk).trans (mul_le_mul_of_nonneg_left hKpow hB))
              (oddLogMass_nonneg _ _) (by positivity)
            exact mul_le_mul_of_nonneg_left hfactor (by norm_num)
      _ = D * ((K : ℝ) ^ δ * (K : ℝ) ^ β) := by dsimp [D]; ring
      _ = _ := by rw [← Real.rpow_add hKR]
  have hlower : c' * (K : ℝ) ^ lam ≤ logMass (fun n => ¬ReachesOne n) (2 ^ K) := by
    have hx : x₀ ≤ 2 ^ K := hKx.trans (show K ≤ 2 ^ K from Nat.lt_two_pow_self.le)
    have h := hlow (2 ^ K) hx
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Real.mul_rpow hKR.le hlog2.le] at h
    dsimp [c']
    nlinarith
  have hgt : D < c' * (K : ℝ) ^ δ := by
    have h := hu (K : ℝ) hKu
    rw [div_lt_iff₀ hc'] at h
    nlinarith
  rw [hsplit, Real.rpow_add hKR] at hlower
  have hpos : 0 < (K : ℝ) ^ (δ + β) := Real.rpow_pos_of_pos hKR _
  have hbad : c' * (K : ℝ) ^ δ ≤ D := by
    have hprod : (c' * (K : ℝ) ^ δ) * (K : ℝ) ^ (δ + β) ≤ D * (K : ℝ) ^ (δ + β) := by
      nlinarith
    exact le_of_mul_le_mul_right hprod hpos
  linarith

/-- Preserve the unconditional odd-mass interface at its established exponent. -/
theorem conjecture_of_odd_mass {k₀ : ℕ} {B β : ℝ} (hB : 0 ≤ B)
    (hβ0 : 0 < β) (hβ : β < 100 / 203)
    (hodd : ∀ K : ℕ, k₀ ≤ K → oddLogMass (fun n => ¬ReachesOne n) (2 ^ K) ≤
      B * ((K : ℝ) + 1) ^ β) : ∀ n, 1 ≤ n → ReachesOne n := by
  apply conjecture_of_odd_mass_of_contagion (lam := 100 / 203) _ hB hβ0 hβ hodd
  intro n hn hfail
  exact Production.failures_logMass_averaged hn hfail (by norm_num) le_rfl

/-- Scale-averaged pressure suffices above the complement of any supplied
contagion exponent. Both arithmetic inputs remain explicit. -/
theorem conjecture_of_bound_of_contagion {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hcontagion : FailureMassLowerBound lam) {N₀ k₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (hk₀ : N₀ < 2 ^ (k₀ + 1))
    {C θ a η : ℝ} (hC : 0 < C) (hθ : 0 ≤ θ) (ha : 0 < a) (hη : 0 ≤ η)
    (hgap : 1 - lam < C * (θ * pC C - Real.log a) / Real.log 2 - η)
    (havg : Bound N₀ k₀ C θ a η) : ∀ n, 1 ≤ n → ReachesOne n := by
  let r := C * (θ * pC C - Real.log a) / Real.log 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 ≤ θ * pC C - Real.log a := by
    have heq : r * Real.log 2 = C * (θ * pC C - Real.log a) := by
      dsimp [r]; exact div_mul_cancel₀ _ hlog2.ne'
    nlinarith [mul_pos hr hlog2]
  obtain ⟨e, helo, hehi⟩ := exists_between
    (lt_min hgap (by linarith : 1 - lam < 1))
  have he1 : e < 1 := lt_of_lt_of_le hehi (min_le_right _ _)
  have her : e < r - η := lt_of_lt_of_le hehi (min_le_left _ _)
  have he0 : 0 < e := by linarith
  let ε := r - η - e
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨D, hDn, hpre⟩ := havg ε hε
  have hs : 1 ≤ 1 + η + ε := by linarith
  have hre : (1 + η + ε) - 1 - r = -e := by dsimp [ε]; ring
  let c := 1 / 2 * (Real.log 2 / Real.log N₀) ^ (-r)
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N₀))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hblock : ∀ k, ∑ n ∈ oddFailures (2 ^ (k₀ + k)), (1 : ℝ) / n ≤
      c * (rho N₀ C θ a (k₀ + k) * ((k : ℝ) + 1) ^ (-r)) :=
    fun k => block_le_rho hN hfloor hk₀ hC hθ ha hD k
  obtain ⟨B, hB, hodd⟩ := odd_mass_le hc hDn hs hr.le he0 he1 hre hpre hblock
  exact conjecture_of_odd_mass_of_contagion hcontagion hB (by linarith) (by linarith) hodd

/-- The original pressure interface uses unconditional contagion at 100/203. -/
theorem conjecture_of_bound {N₀ k₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (hk₀ : N₀ < 2 ^ (k₀ + 1))
    {C θ a η : ℝ} (hC : 0 < C) (hθ : 0 ≤ θ) (ha : 0 < a) (hη : 0 ≤ η)
    (hgap : 103 / 203 < C * (θ * pC C - Real.log a) / Real.log 2 - η)
    (havg : Bound N₀ k₀ C θ a η) : ∀ n, 1 ≤ n → ReachesOne n := by
  apply conjecture_of_bound_of_contagion (lam := 100 / 203) (by norm_num)
    (by norm_num) _ hN hfloor hk₀ hC hθ ha hη (by norm_num; exact hgap) havg
  intro n hn hfail
  exact Production.failures_logMass_averaged hn hfail (by norm_num) le_rfl

/-- Manuscript parameters: `a = 1-q+q*exp θ`, positive tilt, and `C > 1`.
This is a conditional termination theorem; no estimate of `Bound` is proved here. -/
theorem pressure_average_conjecture {N₀ k₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (hk₀ : N₀ < 2 ^ (k₀ + 1))
    {C θ q η : ℝ} (hC : 1 < C) (hθ : 0 < θ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη : 0 ≤ η)
    (hgap : 103 / 203 < C * (θ * pC C - Real.log (1 - q + q * Real.exp θ)) / Real.log 2 - η)
    (havg : Bound N₀ k₀ C θ (1 - q + q * Real.exp θ) η) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  apply conjecture_of_bound hN hfloor hk₀ (by linarith) hθ.le _ hη hgap havg
  exact add_pos (by linarith) (mul_pos hq0 (Real.exp_pos θ))

/-- Combining the two existing inputs lowers the sufficient rate to 3/8.
Neither the cumulative pressure bound nor the OOEE production bound is discharged. -/
theorem pressure_average_conjecture_of_ooee {N₀ k₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (hk₀ : N₀ < 2 ^ (k₀ + 1))
    {C θ q η : ℝ} (hC : 1 < C) (hθ : 0 < θ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη : 0 ≤ η)
    (hOOEE : FateOEWeighted.OOEEProductionBound (fun n => ¬ReachesOne n))
    (hgap : 3 / 8 < C * (θ * pC C - Real.log (1 - q + q * Real.exp θ)) / Real.log 2 - η)
    (havg : Bound N₀ k₀ C θ (1 - q + q * Real.exp θ) η) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  apply conjecture_of_bound_of_contagion (lam := 5 / 8) (by norm_num) (by norm_num)
    _ hN hfloor hk₀ (by linarith) hθ.le _ hη (by norm_num; exact hgap) havg
  · intro n hn hfail
    exact FateOEWeighted.logMass_growth_of_ooee not_reachesOne_backwardClosed hn hfail hOOEE
  · exact add_pos (by linarith) (mul_pos hq0 (Real.exp_pos θ))

end ScaleAverage
end Problems.Juggler
