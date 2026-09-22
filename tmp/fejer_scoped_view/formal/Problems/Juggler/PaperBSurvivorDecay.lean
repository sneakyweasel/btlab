/-
# Paper B, Theorem 6.1's count: the never-contracting words are exponentially few

Paper B's density-one argument (Theorem 6.1, conditional on hypothesis FD) bounds the
uncertified starts at depth `d` by `N_d / 2^d` plus error terms, where `N_d` counts the
length-`d` parity words with no contracting prefix.  The laboratory already holds the two
ends of that estimate in Lean:

* `RateFreeDensity.neverNegWords` / `neverNegCount` — the exact combinatorial object
  `N_d`, with `neverNeg_endpoint`: a survivor of length `d` carries at least `β·d` odd
  letters, `β = log 2 / log 3`, since `2^d ≤ 3^o`;
* `PaperBMarkov.chernoff_density` — the exponential Markov bound on the binomial tail,
  and `tilt_gives_theta`: at the optimal tilt the bound is exactly `theta q ^ d`;
* `PaperBChernoff.theta_lt_one` — `theta q < 1` off the fair point, so the bound decays.

What was missing — `PaperBMarkov`'s own header lists it as still written mathematics —
is the middle: the identification of the survivor count with a binomial tail.  This file
supplies it, assembles the conditional density-one statement around it, and kernel-computes
the small-depth values the manuscripts quote.

* `count_oddCount_ge` — words of length `d` with at least `a` odd letters number exactly
  `∑ k ∈ Ico a (d+1), C(d,k)`.  Pascal induction on `d`; no choice, no measure theory.
* `oddCount_ge_of_mem_neverNeg` — the endpoint constraint as a real inequality:
  `⌈d·β⌉₊ ≤ oddCount w` for every survivor `w`.
* `neverNegCount_le_choose_tail` — hence `N_d` is at most the tail above `⌈d·β⌉₊`.
* `neverNegCount_div_pow_le_theta` — `N_d / 2^d ≤ theta β ^ d`, the tilt taken at the
  endpoint `q = β` itself; the upper bound needs no threshold admissibility.
* `neverNegCount_div_pow_tendsto_zero` — the upper-density bound of the rate-free
  reduction provably vanishes as `d → ∞`.
* `neverCertified_density_zero` — the assembled conditional Theorem 6.1: under
  per-class fairness (`FairClasses`, the manuscript's FD), the never-certified starts
  have natural density zero.  The limit order `N → ∞` before `d → ∞` is
  `PaperBDensity.exceptional_density_zero`.
* Kernel-computed values: `neverNegCount 5 = 4` with the explicit survivors
  `OOOOO, OOOOE, OOOEO, OOEOO` — Corollary 6.4's `7/8` by word counting — and
  `neverNegCount 6 = 8`, `neverNegCount 7 = 13`, `neverNegCount 8 = 19`, matching the
  dynamic-program values quoted in `docs/problems/juggler_k3_rate_free.md`.

What this does NOT do.  It does not prove `FairClasses` — per-class fairness remains the
open input, recorded as the active conjecture
`juggler_tower_rate_free_equidistribution`.  It is not a halt theorem and not an
unconditional density claim about the Juggler map; the only unconditional content is
combinatorics of parity words.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Problems.Juggler.RateFreeDensity
import Problems.Juggler.PaperBMarkov
import Problems.Juggler.PaperBThreshold
import Problems.Juggler.PaperBDensity

namespace Problems.Juggler

namespace PaperBSurvivorDecay

open Filter Topology Finset

/-- Pascal step for the tail sum, in the exact form the word-count induction consumes:
`S(d+1, a) = S(d, a) + S(d, a-1)`, with Nat truncation covering `a = 0`. -/
theorem choose_tail_succ (d a : ℕ) :
    ∑ k ∈ Ico a (d + 2), (d + 1).choose k =
      ∑ k ∈ Ico a (d + 1), d.choose k + ∑ k ∈ Ico a.pred (d + 1), d.choose k := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp only [Nat.pred_zero, Nat.Ico_zero_eq_range]
    show ∑ k ∈ Finset.range (d + 1 + 1), (d + 1).choose k = _
    rw [Nat.sum_range_choose, Nat.sum_range_choose, pow_succ, mul_two]
  · have hpp : ∀ k ∈ Ico a (d + 2), (d + 1).choose k = d.choose k + d.choose (k - 1) := by
      intro k hk
      have hk0 : 0 < k := lt_of_lt_of_le ha (mem_Ico.mp hk).1
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one.mpr hk0
      rw [Nat.add_sub_cancel, Nat.choose_succ_succ', add_comm]
    rw [Finset.sum_congr rfl hpp, Finset.sum_add_distrib]
    have htop : ∑ k ∈ Ico a (d + 2), d.choose k = ∑ k ∈ Ico a (d + 1), d.choose k := by
      by_cases had : a ≤ d + 1
      · rw [Finset.sum_Ico_succ_top had, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self d),
          add_zero]
      · rw [Finset.Ico_eq_empty_iff.mpr (by omega : ¬a < d + 2),
          Finset.Ico_eq_empty_iff.mpr (by omega : ¬a < d + 1)]
    have hshift : ∑ k ∈ Ico a (d + 2), d.choose (k - 1) =
        ∑ k ∈ Ico a.pred (d + 1), d.choose k := by
      rw [Nat.pred_eq_sub_one]
      conv_lhs => rw [Finset.sum_Ico_eq_sum_range]
      conv_rhs => rw [Finset.sum_Ico_eq_sum_range]
      have hlen : d + 1 - (a - 1) = d + 2 - a := by omega
      rw [hlen]
      apply Finset.sum_congr rfl
      intro i _
      have hsub : a + i - 1 = a - 1 + i := by omega
      rw [hsub]
    rw [htop, hshift]

/-- `a ≤ o + 1 ↔ a - 1 ≤ o`, uniformly in `a : ℕ`. -/
theorem le_add_one_iff_pred_le {a o : ℕ} : a ≤ o + 1 ↔ a.pred ≤ o := by
  cases a <;> simp

/-- The exact binomial tail count: length-`d` words with at least `a` odd letters
number `∑ k ∈ Ico a (d+1), C(d,k)`. -/
theorem count_oddCount_ge (d a : ℕ) :
    ((allWords d).filter fun w => a ≤ oddCount w).card =
      ∑ k ∈ Ico a (d + 1), d.choose k := by
  induction d generalizing a with
  | zero =>
      by_cases ha : a = 0
      · subst ha
        rw [show (allWords 0).filter (fun w => 0 ≤ oddCount w) = allWords 0 from
          Finset.filter_true_of_mem fun w _ => Nat.zero_le _]
        decide
      · have hpos : 0 < a := Nat.pos_of_ne_zero ha
        rw [show (allWords 0).filter (fun w => a ≤ oddCount w) = ∅ from
          Finset.filter_false_of_mem fun w hw => by
            have hw' : w = [] := List.length_eq_zero_iff.mp (mem_allWords.mp hw)
            simp [hw', Nat.not_le.mpr hpos]]
        rw [Finset.card_empty,
          Finset.Ico_eq_empty_iff.mpr (by omega : ¬a < 0 + 1), Finset.sum_empty]
  | succ d ih =>
      have hunion :
          (allWords (d + 1)).filter (fun v => a ≤ oddCount v) =
            (allWords d).biUnion fun w =>
              ({w ++ [.even], w ++ [.odd]} : Finset (List Branch)).filter
                (fun v => a ≤ oddCount v) := by
        ext v
        constructor
        · intro hv
          rw [mem_filter] at hv
          rw [allWords_succ] at hv
          rw [mem_biUnion] at hv ⊢
          obtain ⟨w, hw, hvw⟩ := hv.1
          exact ⟨w, hw, mem_filter.mpr ⟨hvw, hv.2⟩⟩
        · intro hv
          rw [mem_biUnion] at hv
          obtain ⟨w, hw, hvw⟩ := hv
          rw [mem_filter] at hvw
          rw [mem_filter, allWords_succ, mem_biUnion]
          exact ⟨⟨w, hw, hvw.1⟩, hvw.2⟩
      have hdisj :
          ∀ x ∈ allWords d, ∀ y ∈ allWords d, x ≠ y →
            Disjoint
              (({x ++ [.even], x ++ [.odd]} : Finset (List Branch)).filter
                (fun v => a ≤ oddCount v))
              (({y ++ [.even], y ++ [.odd]} : Finset (List Branch)).filter
                (fun v => a ≤ oddCount v)) := by
        intro x _ y _ hne
        exact Disjoint.mono (filter_subset _ _) (filter_subset _ _)
          (extend_fiber_disjoint hne)
      have hpair : ∀ w : List Branch,
          (({w ++ [.even], w ++ [.odd]} : Finset (List Branch)).filter
              (fun v => a ≤ oddCount v)).card =
            (if a ≤ oddCount w then 1 else 0) +
              (if a ≤ oddCount w + 1 then 1 else 0) := by
        intro w
        have hne : w ++ [.even] ≠ w ++ [.odd] := fun h =>
          Branch.noConfusion (append_singleton_inj h).2
        have hE : oddCount (w ++ [.even]) = oddCount w := by
          simp [oddCount_append, oddCount]
        have hO : oddCount (w ++ [.odd]) = oddCount w + 1 := by
          simp [oddCount_append, oddCount]
        rw [Finset.card_filter, Finset.sum_pair hne, hE, hO]
      have hpred :
          ((allWords d).filter fun w => a ≤ oddCount w + 1) =
            (allWords d).filter fun w => a.pred ≤ oddCount w := by
        apply Finset.filter_congr
        intro w _
        exact le_add_one_iff_pred_le
      calc ((allWords (d + 1)).filter fun v => a ≤ oddCount v).card
          = ∑ w ∈ allWords d,
              (({w ++ [.even], w ++ [.odd]} : Finset (List Branch)).filter
                (fun v => a ≤ oddCount v)).card := by
            rw [hunion]
            exact Finset.card_biUnion hdisj
        _ = ∑ w ∈ allWords d,
              ((if a ≤ oddCount w then 1 else 0) +
                (if a ≤ oddCount w + 1 then 1 else 0)) :=
            Finset.sum_congr rfl fun w _ => hpair w
        _ = (∑ w ∈ allWords d, if a ≤ oddCount w then 1 else 0) +
              ∑ w ∈ allWords d, if a ≤ oddCount w + 1 then 1 else 0 :=
            Finset.sum_add_distrib
        _ = ((allWords d).filter fun w => a ≤ oddCount w).card +
              ((allWords d).filter fun w => a ≤ oddCount w + 1).card := by
            rw [Finset.card_filter, Finset.card_filter]
        _ = ∑ k ∈ Ico a (d + 1), d.choose k +
              ∑ k ∈ Ico a.pred (d + 1), d.choose k := by
            rw [ih a, hpred, ih a.pred]
        _ = ∑ k ∈ Ico a (d + 2), (d + 1).choose k := (choose_tail_succ d a).symm

/-- The endpoint constraint as a real inequality: a length-`d` survivor carries at
least `⌈d·β⌉₊` odd letters.  This is `neverNeg_endpoint` after `Real.log`. -/
theorem oddCount_ge_of_mem_neverNeg {d : ℕ} {w : List Branch}
    (hw : w ∈ neverNegWords d) :
    ⌈(d : ℝ) * PaperBThreshold.beta⌉₊ ≤ oddCount w := by
  have h := neverNeg_endpoint hw
  have hle : (2 : ℝ) ^ d ≤ 3 ^ oddCount w := by exact_mod_cast h
  have hlog : (d : ℝ) * Real.log 2 ≤ oddCount w * Real.log 3 := by
    have h2 : (0 : ℝ) < 2 ^ d := by positivity
    have h3 : (0 : ℝ) < (3 : ℝ) ^ oddCount w := by positivity
    have hmono := (Real.log_le_log_iff h2 h3).mpr hle
    rwa [Real.log_pow, Real.log_pow] at hmono
  have h3pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hβ : (d : ℝ) * PaperBThreshold.beta ≤ oddCount w := by
    rw [PaperBThreshold.beta, ← mul_div_assoc, div_le_iff₀ h3pos]
    exact hlog
  exact Nat.ceil_le.mpr hβ

/-- `N_d` is at most the binomial tail above `⌈d·β⌉₊`. -/
theorem neverNegCount_le_choose_tail (d : ℕ) :
    neverNegCount d ≤ ∑ k ∈ Ico ⌈(d : ℝ) * PaperBThreshold.beta⌉₊ (d + 1), d.choose k := by
  have hsub : neverNegWords d ⊆
      (allWords d).filter fun w => ⌈(d : ℝ) * PaperBThreshold.beta⌉₊ ≤ oddCount w := by
    intro w hw
    exact mem_filter.mpr ⟨neverNegWords_subset d hw, oddCount_ge_of_mem_neverNeg hw⟩
  exact (card_le_card hsub).trans_eq (count_oddCount_ge d _)

/-- The manuscript's estimate with the endpoint tilt: `N_d / 2^d ≤ theta β ^ d`. -/
theorem neverNegCount_div_pow_le_theta (d : ℕ) :
    (neverNegCount d : ℝ) / 2 ^ d ≤ PaperBChernoff.theta PaperBThreshold.beta ^ d := by
  have hβ0 : (0 : ℝ) < PaperBThreshold.beta := by
    linarith [PaperBThreshold.beta_gt_five_eighths]
  have hβ1 : PaperBThreshold.beta < 1 := PaperBThreshold.beta_lt_one
  have ht : 0 < Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)) := by
    apply Real.log_pos
    rw [one_lt_div (by linarith : (0 : ℝ) < 1 - PaperBThreshold.beta)]
    linarith [PaperBThreshold.beta_gt_five_eighths]
  have hle : (neverNegCount d : ℝ) ≤
      ∑ k ∈ Ico ⌈(d : ℝ) * PaperBThreshold.beta⌉₊ (d + 1), (d.choose k : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast neverNegCount_le_choose_tail d
  have hA : (neverNegCount d : ℝ) / 2 ^ d ≤
      (∑ k ∈ Ico ⌈(d : ℝ) * PaperBThreshold.beta⌉₊ (d + 1), (d.choose k : ℝ)) /
        2 ^ d :=
    div_le_div_of_nonneg_right hle (by positivity)
  have hB := PaperBMarkov.chernoff_density ht d ⌈(d : ℝ) * PaperBThreshold.beta⌉₊
  have hceil : (d : ℝ) * PaperBThreshold.beta ≤
      (⌈(d : ℝ) * PaperBThreshold.beta⌉₊ : ℝ) := Nat.le_ceil _
  have hexp :
      Real.exp (-(Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)) *
          (⌈(d : ℝ) * PaperBThreshold.beta⌉₊ : ℝ))) ≤
        Real.exp (-(Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)) *
          ((d : ℝ) * PaperBThreshold.beta))) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hceil ht.le
    linarith
  have hC :
      Real.exp (-(Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)) *
          (⌈(d : ℝ) * PaperBThreshold.beta⌉₊ : ℝ))) *
          ((1 + Real.exp (Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)))) /
            2) ^ d ≤
        PaperBChernoff.theta PaperBThreshold.beta ^ d := by
    calc Real.exp (-(Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)) *
            (⌈(d : ℝ) * PaperBThreshold.beta⌉₊ : ℝ))) *
          ((1 + Real.exp (Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)))) /
            2) ^ d
        ≤ Real.exp (-(Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)) *
            ((d : ℝ) * PaperBThreshold.beta))) *
          ((1 + Real.exp (Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)))) /
            2) ^ d :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = Real.exp (-(Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)) *
            (PaperBThreshold.beta * (d : ℝ)))) *
          ((1 + Real.exp (Real.log (PaperBThreshold.beta / (1 - PaperBThreshold.beta)))) /
            2) ^ d := by
          rw [mul_comm (d : ℝ) PaperBThreshold.beta]
      _ = PaperBChernoff.theta PaperBThreshold.beta ^ d :=
          PaperBMarkov.tilt_gives_theta hβ0 hβ1 d
  exact hA.trans (hB.trans hC)

/-- The Chernoff factor at the endpoint is below one, so the survivor density bound
decays to zero. -/
theorem theta_beta_lt_one : PaperBChernoff.theta PaperBThreshold.beta < 1 := by
  have hβ0 : (0 : ℝ) < PaperBThreshold.beta := by
    linarith [PaperBThreshold.beta_gt_five_eighths]
  have hβhalf : PaperBThreshold.beta ≠ 1 / 2 := by
    linarith [PaperBThreshold.beta_gt_five_eighths]
  exact PaperBChernoff.theta_lt_one hβ0 PaperBThreshold.beta_lt_one hβhalf

theorem theta_beta_pos : 0 < PaperBChernoff.theta PaperBThreshold.beta := by
  have hβ0 : (0 : ℝ) < PaperBThreshold.beta := by
    linarith [PaperBThreshold.beta_gt_five_eighths]
  exact PaperBChernoff.theta_pos hβ0 PaperBThreshold.beta_lt_one

/-- **The decay half of the rate-free reduction, kernel-checked:**
`N_d / 2^d → 0` as `d → ∞`. -/
theorem neverNegCount_div_pow_tendsto_zero :
    Tendsto (fun d : ℕ => (neverNegCount d : ℝ) / 2 ^ d) atTop (𝓝 0) :=
  squeeze_zero
    (fun d => by positivity)
    (fun d => neverNegCount_div_pow_le_theta d)
    (tendsto_pow_atTop_nhds_zero_of_lt_one theta_beta_pos.le theta_beta_lt_one)

/-- The all-odd word survives at every depth, so `N_d ≥ 1`. -/
theorem one_le_neverNegCount (d : ℕ) : 1 ≤ neverNegCount d := by
  have hmem : List.replicate d Branch.odd ∈ neverNegWords d :=
    mem_filter.mpr
      ⟨mem_allWords.mpr (List.length_replicate ..), allOdd_prefixNoncontracting d⟩
  exact Finset.card_pos.mpr ⟨List.replicate d Branch.odd, hmem⟩

/-- Hypothesis FD, per class: every depth-`d` class count is asymptotic to
`2^{-d} N`.  This is the open input; nothing below proves it. -/
def FairClasses : Prop :=
  ∀ d : ℕ, ∀ w ∈ allWords d,
    Tendsto (fun N : ℕ => (classCount w N : ℝ) / N) atTop (𝓝 ((2 ^ d : ℝ)⁻¹))

/-- Under FD, the depth-`d` uncertified ratio tends to `N_d / 2^d`. -/
theorem uncertifiedCount_div_tendsto (h : FairClasses) (d : ℕ) :
    Tendsto (fun N : ℕ => (uncertifiedCount d N : ℝ) / N) atTop
      (𝓝 ((neverNegCount d : ℝ) / 2 ^ d)) := by
  have hsum : (fun N : ℕ => (uncertifiedCount d N : ℝ) / N) =
      fun N => ∑ w ∈ neverNegWords d, (classCount w N : ℝ) / N := by
    funext N
    rw [uncertifiedCount_eq_sum, Nat.cast_sum, Finset.sum_div]
  rw [hsum]
  have htend :=
    tendsto_finsetSum (neverNegWords d) (fun w hw => h d w (neverNegWords_subset d hw))
  have hshape : ∑ w ∈ neverNegWords d, ((2 ^ d : ℝ)⁻¹) =
      (neverNegCount d : ℝ) / 2 ^ d := by
    rw [Finset.sum_const, nsmul_eq_mul, div_eq_inv_mul]
    exact mul_comm _ _
  rw [← hshape]
  exact htend

open Classical in
/-- **The assembled conditional Theorem 6.1.**  Under per-class fairness, the
never-certified starts have natural density zero: at each fixed depth the uncertified
ratio tends to `N_d / 2^d`, and that bound itself tends to zero as `d → ∞`.  The
hypothesis `FairClasses` is exactly what remains open. -/
theorem neverCertified_density_zero (h : FairClasses) :
    Tendsto
      (fun N : ℕ =>
        (((Icc 1 N).filter fun n => ¬HasFiniteCoeffStop n).card : ℝ) / N)
      atTop (𝓝 0) := by
  classical
  apply PaperBDensity.exceptional_density_zero
    (bound := fun d => 2 * ((neverNegCount d : ℝ) / 2 ^ d))
  · intro N
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hmul := neverNegCount_div_pow_tendsto_zero.const_mul (2 : ℝ)
    simpa using hmul
  · intro d
    have h1 : 1 ≤ neverNegCount d := one_le_neverNegCount d
    have hL : (0 : ℝ) < (neverNegCount d : ℝ) / 2 ^ d := by
      have hpos : (0 : ℝ) < neverNegCount d := by exact_mod_cast h1
      positivity
    have ht := uncertifiedCount_div_tendsto h d
    rw [Metric.tendsto_atTop] at ht
    obtain ⟨N₀, hN₀⟩ := ht ((neverNegCount d : ℝ) / 2 ^ d) hL
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    have hdist := hN₀ N (le_trans (le_max_left N₀ 1) hN)
    rw [Real.dist_eq, abs_lt] at hdist
    have hcard :
        (((Icc 1 N).filter fun n => ¬HasFiniteCoeffStop n).card : ℝ) ≤
          (uncertifiedCount d N : ℝ) := by
      exact_mod_cast
        neverCertifiedCount_le_uncertified (d := d) (N := N)
          (filter_subset _ _) (fun n hn => (mem_filter.mp hn).2)
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast le_trans (le_max_right N₀ 1) hN
    calc (((Icc 1 N).filter fun n => ¬HasFiniteCoeffStop n).card : ℝ) / N
        ≤ (uncertifiedCount d N : ℝ) / N := div_le_div_of_nonneg_right hcard hNpos.le
      _ ≤ 2 * ((neverNegCount d : ℝ) / 2 ^ d) := by linarith [hdist.2]

/-! ### Kernel-computed values at small depths -/

theorem neverNegCount_one : neverNegCount 1 = 1 := by
  decide +kernel

theorem neverNegCount_two : neverNegCount 2 = 1 := by
  decide +kernel

theorem neverNegCount_three : neverNegCount 3 = 2 := by
  decide +kernel

theorem neverNegCount_four : neverNegCount 4 = 3 := by
  decide +kernel

/-- The depth-five survivors number four: this is the `4` behind Corollary 6.4's
certificate density `1 - 4/32 = 7/8`, reached by counting words. -/
theorem neverNegCount_five : neverNegCount 5 = 4 := by
  decide +kernel

/-- The depth-five survivors, explicitly: `OOOOO`, `OOOOE`, `OOOEO`, `OOEOO`. -/
theorem neverNegWords_five :
    neverNegWords 5 =
      {[.odd, .odd, .odd, .odd, .odd],
       [.odd, .odd, .odd, .odd, .even],
       [.odd, .odd, .odd, .even, .odd],
       [.odd, .odd, .even, .odd, .odd]} := by
  decide +kernel

/-- Depth six: all eight children survive, so the certificate density stays `7/8`. -/
theorem neverNegCount_six : neverNegCount 6 = 8 := by
  decide +kernel

theorem neverNegCount_seven : neverNegCount 7 = 13 := by
  decide +kernel

theorem neverNegCount_eight : neverNegCount 8 = 19 := by
  decide +kernel

/-- The uncertified fraction at depth five is exactly `1/8`, complementing
`DepthFourFive.cor64_density`'s `7/8`. -/
theorem uncertified_fraction_depth_five :
    (1 : ℚ) - (neverNegCount 5 : ℚ) / 2 ^ 5 = 7 / 8 := by
  rw [neverNegCount_five]
  norm_num

end PaperBSurvivorDecay

end Problems.Juggler
