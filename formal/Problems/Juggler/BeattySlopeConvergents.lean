import Problems.Juggler.BeattySlopeRegularDim
import Problems.Juggler.BeattySlopeArithmetic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# Regular slopes exist for every growth exponent

For partial quotients `a_0, a_1, …` with `a_k ≥ 1` for `k ≥ 1`, the continuants
`P_k, Q_k` satisfy the determinant identity, and the supremum `α` of the odd
convergents lies strictly between consecutive convergents. The signed errors
`s_k = (-1)^(k+1)(Q_k α - P_k)` are positive and satisfy
`Q_(k+1) s_k + Q_k s_(k+1) = 1` and `s_k = s_(k+2) + a_(k+1) s_(k+1)`. These give
`|Q_k α - P_k| ≤ 1/Q_(k+1)`, best approximation `|m α - r| ≥ s_k` for
`0 < m < Q_(k+1)`, the separation `s_k ≥ 1/(2Q_(k+1))`, coprimality and
irrationality: the convergents are `GoodConvergents`.

Choosing `a_k = ⌈Q_k^(ν-1)⌉ + 1` gives `q_n^ν ≤ q_(n+1) ≤ 4 q_n^ν`. Hence every
value `2/(2+ν)` with `ν > 1` is the Hausdorff dimension of a complete cluster
set; with a Liouville slope (dimension `0`) and the golden ratio (dimension
`2/3`) the dimensions over irrational slopes `α > 1` form exactly `[0, 2/3]`.
The explicit slope has Diophantine class exactly `ν`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set
open scoped NNReal ENNReal

/-- Continuant denominators of the partial quotients `a`:
`Q 0 = 0`, `Q 1 = 1`, `Q (k+2) = a (k+1) Q (k+1) + Q k`. -/
def cfDen (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => a (k + 1) * cfDen a (k + 1) + cfDen a k

/-- Continuant numerators of the partial quotients `a`:
`P 0 = 1`, `P 1 = a 0`, `P (k+2) = a (k+1) P (k+1) + P k`. -/
def cfNum (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 0
  | k + 2 => a (k + 1) * cfNum a (k + 1) + cfNum a k

variable {a : ℕ → ℕ}

/-- Unfolding the denominator recurrence. -/
theorem cfDen_add_two (a : ℕ → ℕ) (k : ℕ) :
    cfDen a (k + 2) = a (k + 1) * cfDen a (k + 1) + cfDen a k := rfl

/-- Unfolding the numerator recurrence. -/
theorem cfNum_add_two (a : ℕ → ℕ) (k : ℕ) :
    cfNum a (k + 2) = a (k + 1) * cfNum a (k + 1) + cfNum a k := rfl

/-- The determinant identity `P_(k+1) Q_k - P_k Q_(k+1) = (-1)^(k+1)`. -/
theorem cf_det (a : ℕ → ℕ) (k : ℕ) :
    (cfNum a (k + 1) : ℤ) * cfDen a k - cfNum a k * cfDen a (k + 1) = (-1) ^ (k + 1) := by
  induction k with
  | zero => simp [cfNum, cfDen]
  | succ k ih =>
    rw [cfNum_add_two, cfDen_add_two]
    push_cast
    rw [pow_succ]
    linear_combination (-1 : ℤ) * ih

/-- The two-step determinant `P_(k+2) Q_k - P_k Q_(k+2) = a_(k+1) (-1)^(k+1)`. -/
theorem cf_det_two (a : ℕ → ℕ) (k : ℕ) :
    (cfNum a (k + 2) : ℤ) * cfDen a k - cfNum a k * cfDen a (k + 2) =
      a (k + 1) * (-1) ^ (k + 1) := by
  rw [cfNum_add_two, cfDen_add_two]
  push_cast
  linear_combination (a (k + 1) : ℤ) * cf_det a k

/-- With partial quotients `a_(k+1) ≥ 1` the denominators are monotone. -/
theorem cfDen_le_succ (ha : ∀ k, 1 ≤ a (k + 1)) : ∀ k, cfDen a k ≤ cfDen a (k + 1)
  | 0 => by simp [cfDen]
  | k + 1 => by
    rw [cfDen_add_two]
    nlinarith [ha k]

/-- The denominators `Q_(k+1)` are positive. -/
theorem cfDen_succ_pos (ha : ∀ k, 1 ≤ a (k + 1)) : ∀ k, 0 < cfDen a (k + 1)
  | 0 => by simp [cfDen]
  | k + 1 => (cfDen_succ_pos ha k).trans_le (cfDen_le_succ ha (k + 1))

/-- Linear growth `k ≤ Q_(k+2)`. -/
theorem le_cfDen (ha : ∀ k, 1 ≤ a (k + 1)) : ∀ k, k ≤ cfDen a (k + 2)
  | 0 => Nat.zero_le _
  | k + 1 => by
    have h1 := le_cfDen ha k
    have h2 := cfDen_succ_pos ha k
    have h3 := ha (k + 1)
    rw [cfDen_add_two]
    nlinarith

/-- The denominators tend to infinity. -/
theorem cfDen_tendsto (ha : ∀ k, 1 ≤ a (k + 1)) : Tendsto (cfDen a) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨b + 2, fun n hn => ?_⟩
  exact (le_cfDen ha b).trans (monotone_nat_of_le_succ (cfDen_le_succ ha) hn)

/-- The convergent `P_k / Q_k`. -/
noncomputable def cfConv (a : ℕ → ℕ) (k : ℕ) : ℝ := cfNum a k / cfDen a k

/-- The odd-indexed convergents increase strictly. -/
theorem cfConv_odd_lt (ha : ∀ k, 1 ≤ a (k + 1)) (j : ℕ) :
    cfConv a (2 * j + 1) < cfConv a (2 * (j + 1) + 1) := by
  have h := cf_det_two a (2 * j + 1)
  have he : ((-1 : ℤ)) ^ (2 * j + 1 + 1) = 1 := Even.neg_one_pow ⟨j + 1, by ring⟩
  rw [he] at h
  have h1 := ha (2 * j + 1)
  have hz : (cfNum a (2 * j + 1) : ℤ) * cfDen a (2 * j + 1 + 2) <
      cfNum a (2 * j + 1 + 2) * cfDen a (2 * j + 1) := by
    have : (1 : ℤ) ≤ a (2 * j + 1 + 1) := by exact_mod_cast h1
    linarith
  have hr : (cfNum a (2 * j + 1) : ℝ) * cfDen a (2 * j + 1 + 2) <
      cfNum a (2 * j + 1 + 2) * cfDen a (2 * j + 1) := by exact_mod_cast hz
  have hq1 : (0 : ℝ) < cfDen a (2 * j + 1) := by exact_mod_cast cfDen_succ_pos ha (2 * j)
  have hq2 : (0 : ℝ) < cfDen a (2 * j + 1 + 2) := by
    exact_mod_cast cfDen_succ_pos ha (2 * j + 2)
  unfold cfConv
  rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, div_lt_div_iff₀ hq1 hq2]
  exact hr

/-- The even-indexed convergents `P_(2j+2)/Q_(2j+2)` decrease strictly. -/
theorem cfConv_even_lt (ha : ∀ k, 1 ≤ a (k + 1)) (j : ℕ) :
    cfConv a (2 * (j + 1) + 2) < cfConv a (2 * j + 2) := by
  have h := cf_det_two a (2 * j + 2)
  have he : ((-1 : ℤ)) ^ (2 * j + 2 + 1) = -1 := Odd.neg_one_pow ⟨j + 1, by ring⟩
  rw [he] at h
  have h1 := ha (2 * j + 2)
  have hz : (cfNum a (2 * j + 2 + 2) : ℤ) * cfDen a (2 * j + 2) <
      cfNum a (2 * j + 2) * cfDen a (2 * j + 2 + 2) := by
    have : (1 : ℤ) ≤ a (2 * j + 2 + 1) := by exact_mod_cast h1
    linarith
  have hr : (cfNum a (2 * j + 2 + 2) : ℝ) * cfDen a (2 * j + 2) <
      cfNum a (2 * j + 2) * cfDen a (2 * j + 2 + 2) := by exact_mod_cast hz
  have hq1 : (0 : ℝ) < cfDen a (2 * j + 2) := by exact_mod_cast cfDen_succ_pos ha (2 * j + 1)
  have hq2 : (0 : ℝ) < cfDen a (2 * j + 2 + 2) := by
    exact_mod_cast cfDen_succ_pos ha (2 * j + 3)
  unfold cfConv
  rw [show 2 * (j + 1) + 2 = 2 * j + 2 + 2 by ring, div_lt_div_iff₀ hq2 hq1]
  exact hr

/-- Each odd convergent lies below the next even one. -/
theorem cfConv_odd_lt_even (ha : ∀ k, 1 ≤ a (k + 1)) (j : ℕ) :
    cfConv a (2 * j + 1) < cfConv a (2 * j + 2) := by
  have h := cf_det a (2 * j + 1)
  have he : ((-1 : ℤ)) ^ (2 * j + 1 + 1) = 1 := Even.neg_one_pow ⟨j + 1, by ring⟩
  rw [he] at h
  have hz : (cfNum a (2 * j + 1) : ℤ) * cfDen a (2 * j + 1 + 1) <
      cfNum a (2 * j + 1 + 1) * cfDen a (2 * j + 1) := by linarith
  have hr : (cfNum a (2 * j + 1) : ℝ) * cfDen a (2 * j + 1 + 1) <
      cfNum a (2 * j + 1 + 1) * cfDen a (2 * j + 1) := by exact_mod_cast hz
  have hq1 : (0 : ℝ) < cfDen a (2 * j + 1) := by exact_mod_cast cfDen_succ_pos ha (2 * j)
  have hq2 : (0 : ℝ) < cfDen a (2 * j + 1 + 1) := by
    exact_mod_cast cfDen_succ_pos ha (2 * j + 1)
  unfold cfConv
  rw [div_lt_div_iff₀ hq1 hq2]
  exact hr

/-- Every odd convergent lies below every even convergent of index `≥ 2`. -/
theorem cfConv_odd_lt_even' (ha : ∀ k, 1 ≤ a (k + 1)) (i j : ℕ) :
    cfConv a (2 * i + 1) < cfConv a (2 * j + 2) := by
  have hu : StrictMono fun j => cfConv a (2 * j + 1) :=
    strictMono_nat_of_lt_succ (cfConv_odd_lt ha)
  have hv : StrictAnti fun j => cfConv a (2 * j + 2) :=
    strictAnti_nat_of_succ_lt (cfConv_even_lt ha)
  calc cfConv a (2 * i + 1) ≤ cfConv a (2 * max i j + 1) := hu.monotone (le_max_left _ _)
    _ < cfConv a (2 * max i j + 2) := cfConv_odd_lt_even ha _
    _ ≤ cfConv a (2 * j + 2) := hv.antitone (le_max_right _ _)

/-- The real number with partial quotients `a`: the supremum of the
odd-indexed convergents. -/
noncomputable def cfLim (a : ℕ → ℕ) : ℝ := ⨆ j : ℕ, cfConv a (2 * j + 1)

/-- The limit lies strictly above every odd convergent. -/
theorem cfConv_odd_lt_lim (ha : ∀ k, 1 ≤ a (k + 1)) (j : ℕ) :
    cfConv a (2 * j + 1) < cfLim a := by
  have hb : BddAbove (range fun j => cfConv a (2 * j + 1)) :=
    ⟨cfConv a 2, by rintro _ ⟨i, rfl⟩; exact (cfConv_odd_lt_even' ha i 0).le⟩
  exact (cfConv_odd_lt ha j).trans_le (le_ciSup hb (j + 1))

/-- The limit lies strictly below every even convergent of index `≥ 2`. -/
theorem cfLim_lt_conv_even (ha : ∀ k, 1 ≤ a (k + 1)) (j : ℕ) :
    cfLim a < cfConv a (2 * j + 2) := by
  have : cfLim a ≤ cfConv a (2 * (j + 1) + 2) :=
    ciSup_le fun i => (cfConv_odd_lt_even' ha i (j + 1)).le
  exact this.trans_lt (cfConv_even_lt ha j)

/-- The signed error `s_k = (-1)^(k+1) (Q_k α - P_k)` at the limit `α`. -/
noncomputable def cfErr (a : ℕ → ℕ) (k : ℕ) : ℝ :=
  (-1) ^ (k + 1) * ((cfDen a k : ℝ) * cfLim a - cfNum a k)

/-- The signed error `s_k` is positive: the errors alternate in sign. -/
theorem cfErr_pos (ha : ∀ k, 1 ≤ a (k + 1)) (k : ℕ) : 0 < cfErr a k := by
  unfold cfErr
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rcases j with _ | j
    · simp [cfDen, cfNum]
    · have h := cfLim_lt_conv_even ha j
      have hq : (0 : ℝ) < cfDen a (2 * j + 2) := by
        exact_mod_cast cfDen_succ_pos ha (2 * j + 1)
      have he : ((-1 : ℝ)) ^ (2 * (j + 1) + 1) = -1 := Odd.neg_one_pow ⟨j + 1, by ring⟩
      rw [he, show 2 * (j + 1) = 2 * j + 2 by ring]
      unfold cfConv at h
      rw [lt_div_iff₀ hq] at h
      nlinarith
  · have h := cfConv_odd_lt_lim ha j
    have hq : (0 : ℝ) < cfDen a (2 * j + 1) := by exact_mod_cast cfDen_succ_pos ha (2 * j)
    have he : ((-1 : ℝ)) ^ (2 * j + 1 + 1) = 1 := Even.neg_one_pow ⟨j + 1, by ring⟩
    rw [he]
    unfold cfConv at h
    rw [div_lt_iff₀ hq] at h
    nlinarith

/-- `((-1)^k)^2 = 1`. -/
theorem cf_sign_sq (k : ℕ) : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by
  rw [← mul_pow]; norm_num

/-- The absolute error is the signed error. -/
theorem abs_cf_err (ha : ∀ k, 1 ≤ a (k + 1)) (k : ℕ) :
    |(cfDen a k : ℝ) * cfLim a - cfNum a k| = cfErr a k := by
  have h : (cfDen a k : ℝ) * cfLim a - cfNum a k = (-1) ^ (k + 1) * cfErr a k := by
    unfold cfErr
    linear_combination (-((cfDen a k : ℝ) * cfLim a - cfNum a k)) * cf_sign_sq (k + 1)
  rw [h, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (cfErr_pos ha k)]

/-- `Q_(k+1) s_k + Q_k s_(k+1) = 1`. -/
theorem cfErr_identity (k : ℕ) :
    (cfDen a (k + 1) : ℝ) * cfErr a k + cfDen a k * cfErr a (k + 1) = 1 := by
  have h : (cfNum a (k + 1) : ℝ) * cfDen a k - cfNum a k * cfDen a (k + 1) =
      (-1) ^ (k + 1) := by exact_mod_cast cf_det a k
  unfold cfErr
  rw [pow_succ (-1 : ℝ) (k + 1)]
  linear_combination ((-1 : ℝ) ^ (k + 1)) * h + cf_sign_sq (k + 1)

/-- `s_k = s_(k+2) + a_(k+1) s_(k+1)`. -/
theorem cfErr_recurrence (k : ℕ) :
    cfErr a k = cfErr a (k + 2) + a (k + 1) * cfErr a (k + 1) := by
  unfold cfErr
  rw [cfDen_add_two, cfNum_add_two]
  push_cast
  rw [pow_succ (-1 : ℝ) (k + 2), pow_succ (-1 : ℝ) (k + 1)]
  ring

/-- The errors decrease: `s_(k+1) ≤ s_k`. -/
theorem cfErr_succ_le (ha : ∀ k, 1 ≤ a (k + 1)) (k : ℕ) : cfErr a (k + 1) ≤ cfErr a k := by
  have h := cfErr_recurrence (a := a) k
  have h1 : (1 : ℝ) ≤ a (k + 1) := by exact_mod_cast ha k
  have h2 := cfErr_pos ha (k + 2)
  have h3 := cfErr_pos ha (k + 1)
  nlinarith

/-- The upper bound `s_k ≤ 1/Q_(k+1)`. -/
theorem cfErr_le (ha : ∀ k, 1 ≤ a (k + 1)) (k : ℕ) :
    cfErr a k ≤ 1 / (cfDen a (k + 1) : ℝ) := by
  have h := cfErr_identity (a := a) k
  have hq : (0 : ℝ) < cfDen a (k + 1) := by exact_mod_cast cfDen_succ_pos ha k
  have h0 : (0 : ℝ) ≤ cfDen a k * cfErr a (k + 1) :=
    mul_nonneg (Nat.cast_nonneg _) (cfErr_pos ha _).le
  rw [le_div_iff₀ hq]
  linarith

/-- The lower bound `s_k ≥ 1/(2 Q_(k+1))`. -/
theorem cfErr_ge (ha : ∀ k, 1 ≤ a (k + 1)) (k : ℕ) :
    1 / (2 * (cfDen a (k + 1) : ℝ)) ≤ cfErr a k := by
  have h := cfErr_identity (a := a) k
  have hq : (0 : ℝ) < cfDen a (k + 1) := by exact_mod_cast cfDen_succ_pos ha k
  have hqq : (cfDen a k : ℝ) ≤ cfDen a (k + 1) := by exact_mod_cast cfDen_le_succ ha k
  have hs := cfErr_succ_le ha k
  have hs0 := (cfErr_pos ha (k + 1)).le
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Best approximation: for `0 < m < Q_(k+1)` and any integer `r`,
`|m α - r| ≥ s_k`. -/
theorem cf_best_approx (ha : ∀ k, 1 ≤ a (k + 1)) (k m : ℕ) (hm : 0 < m)
    (hmk : m < cfDen a (k + 1)) (r : ℤ) : cfErr a k ≤ |(m : ℝ) * cfLim a - r| := by
  set D : ℤ := (-1) ^ (k + 1) with hDdef
  have hD := cf_det a k
  have hD2 : D * D = 1 := by rw [hDdef, ← mul_pow]; norm_num
  set x : ℤ := D * (m * cfNum a (k + 1) - r * cfDen a (k + 1)) with hx
  set y : ℤ := D * (r * cfDen a k - m * cfNum a k) with hy
  have hm' : (m : ℤ) = x * cfDen a k + y * cfDen a (k + 1) := by
    rw [hx, hy]; linear_combination (-(m : ℤ) * D) * hD - (m : ℤ) * hD2
  have hr' : r = x * cfNum a k + y * cfNum a (k + 1) := by
    rw [hx, hy]; linear_combination (-r * D) * hD - r * hD2
  have hmR : (m : ℝ) = x * cfDen a k + y * cfDen a (k + 1) := by exact_mod_cast hm'
  have hrR : (r : ℝ) = x * cfNum a k + y * cfNum a (k + 1) := by exact_mod_cast hr'
  set e : ℝ := (-1) ^ (k + 1)
  have he : e * e = 1 := cf_sign_sq (k + 1)
  have hkey : (m : ℝ) * cfLim a - r = e * (x * cfErr a k - y * cfErr a (k + 1)) := by
    unfold cfErr
    rw [pow_succ (-1 : ℝ) (k + 1), hmR, hrR]
    linear_combination (-((x : ℝ) * ((cfDen a k : ℝ) * cfLim a - cfNum a k) +
      (y : ℝ) * ((cfDen a (k + 1) : ℝ) * cfLim a - cfNum a (k + 1)))) * he
  have habs : |(m : ℝ) * cfLim a - r| = |(x : ℝ) * cfErr a k - y * cfErr a (k + 1)| := by
    rw [hkey, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs]
  have hs := cfErr_pos ha k
  have hs1 := cfErr_pos ha (k + 1)
  have hq0 : (0 : ℤ) ≤ cfDen a k := Nat.cast_nonneg _
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hmkz : (m : ℤ) < cfDen a (k + 1) := by exact_mod_cast hmk
  rcases le_or_gt y 0 with hy0 | hy0
  · have hx1 : 1 ≤ x := by
      by_contra hc
      have := not_le.1 hc
      nlinarith
    have hx1R : (1 : ℝ) ≤ x := by exact_mod_cast hx1
    have hy0R : (y : ℝ) ≤ 0 := by exact_mod_cast hy0
    rw [le_abs]; left; nlinarith
  · have hx1 : x ≤ -1 := by
      by_contra hc
      have := not_le.1 hc
      nlinarith
    have hx1R : (x : ℝ) ≤ -1 := by exact_mod_cast hx1
    have hy0R : (0 : ℝ) < y := by exact_mod_cast hy0
    rw [le_abs]; right; nlinarith

/-- The convergents of `cfLim a`, indexed from `P_1/Q_1`, are good
convergents in the sense of `GoodConvergents`. -/
theorem cf_goodConvergents (ha : ∀ k, 1 ≤ a (k + 1)) :
    GoodConvergents (cfLim a) (fun n => (cfNum a (n + 1) : ℤ)) (fun n => cfDen a (n + 1)) where
  pos n := cfDen_succ_pos ha n
  coprime n := by
    have h := cf_det a (n + 1)
    have hD2 : ((-1 : ℤ) ^ (n + 1 + 1)) * (-1) ^ (n + 1 + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hc : IsCoprime (cfNum a (n + 1) : ℤ) (cfDen a (n + 1) : ℤ) :=
      ⟨-((-1) ^ (n + 1 + 1)) * cfDen a (n + 1 + 1), (-1) ^ (n + 1 + 1) * cfNum a (n + 1 + 1),
        by linear_combination ((-1 : ℤ) ^ (n + 1 + 1)) * h + hD2⟩
    simpa [Int.natAbs_natCast] using Nat.isCoprime_iff_coprime.1 hc
  approx n := by
    have := cfErr_le ha (n + 1)
    simpa [abs_cf_err ha (n + 1)] using this
  sep n m hm hmq r := (cfErr_ge ha n).trans (cf_best_approx ha n m hm hmq r)

/-- The limit exceeds its first convergent `a_0`. -/
theorem cfLim_gt (ha : ∀ k, 1 ≤ a (k + 1)) : (a 0 : ℝ) < cfLim a := by
  have h := cfConv_odd_lt_lim ha 0
  simpa [cfConv, cfNum, cfDen] using h

/-- The limit is irrational. -/
theorem cfLim_irrational (ha : ∀ k, 1 ≤ a (k + 1)) : Irrational (cfLim a) := by
  rw [irrational_iff_ne_rational]
  intro A B hB hα
  obtain ⟨k, hk⟩ := ((cfDen_tendsto ha).comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop
    B.natAbs |>.exists
  simp only [Function.comp] at hk
  set n : ℤ := cfDen a k * A - B * cfNum a k
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hB
  have hn : (n : ℝ) = B * ((cfDen a k : ℝ) * cfLim a - cfNum a k) := by
    simp only [n, hα]; push_cast; field_simp
  have hq : (0 : ℝ) < cfDen a (k + 1) := by exact_mod_cast cfDen_succ_pos ha k
  have habs : |(n : ℝ)| = |(B : ℝ)| * cfErr a k := by rw [hn, abs_mul, abs_cf_err ha]
  have hBq : |(B : ℝ)| < cfDen a (k + 1) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hk
  have hlt : |(n : ℝ)| < 1 := by
    rw [habs]
    calc |(B : ℝ)| * cfErr a k ≤ |(B : ℝ)| * (1 / (cfDen a (k + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left (cfErr_le ha k) (abs_nonneg _)
      _ < 1 := by rw [mul_one_div, div_lt_one hq]; exact hBq
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hlt
    have := abs_lt.1 this
    omega
  have hpos : 0 < |(n : ℝ)| := by
    rw [habs]; exact mul_pos (abs_pos.2 hBR) (cfErr_pos ha k)
  rw [hn0] at hpos
  simp at hpos

/-! ### Slopes of prescribed growth exponent -/

/-- Denominators of growth exponent `ν`: `Q 0 = 0`, `Q 1 = 1`,
`Q (k+2) = (⌈Q_(k+1)^(ν-1)⌉ + 1) Q_(k+1) + Q_k`. -/
noncomputable def expDen (ν : ℝ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => (⌈(expDen ν (k + 1) : ℝ) ^ (ν - 1)⌉₊ + 1) * expDen ν (k + 1) + expDen ν k

/-- Partial quotients of growth exponent `ν`: `a_0 = 1` and
`a_k = ⌈Q_k^(ν-1)⌉ + 1` for `k ≥ 1`. -/
noncomputable def expQuot (ν : ℝ) (k : ℕ) : ℕ :=
  if k = 0 then 1 else ⌈(expDen ν k : ℝ) ^ (ν - 1)⌉₊ + 1

/-- The partial quotients `expQuot ν (k+1)` are at least one. -/
theorem expQuot_succ_ge (ν : ℝ) (k : ℕ) : 1 ≤ expQuot ν (k + 1) := by
  simp [expQuot]

/-- The continuant denominators of `expQuot ν` are `expDen ν`. -/
theorem cfDen_expQuot (ν : ℝ) : ∀ k, cfDen (expQuot ν) k = expDen ν k
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    rw [cfDen_add_two, cfDen_expQuot ν (k + 1), cfDen_expQuot ν k]
    simp [expQuot, expDen]

/-- The slope of growth exponent `ν`: the real number with partial quotients
`expQuot ν`. -/
noncomputable def expSlope (ν : ℝ) : ℝ := cfLim (expQuot ν)

/-- The slope `expSlope ν` exceeds one. -/
theorem one_lt_expSlope (ν : ℝ) : 1 < expSlope ν := by
  have h := cfLim_gt (expQuot_succ_ge ν)
  simpa [expQuot, expSlope] using h

/-- The slope `expSlope ν` is irrational. -/
theorem expSlope_irrational (ν : ℝ) : Irrational (expSlope ν) :=
  cfLim_irrational (expQuot_succ_ge ν)

/-- Two-sided growth `Q_(n+1)^ν ≤ Q_(n+2) ≤ 4 Q_(n+1)^ν` for `ν ≥ 1`. -/
theorem expDen_growth {ν : ℝ} (hν : 1 ≤ ν) (n : ℕ) :
    (expDen ν (n + 1) : ℝ) ^ ν ≤ expDen ν (n + 2) ∧
      (expDen ν (n + 2) : ℝ) ≤ 4 * (expDen ν (n + 1) : ℝ) ^ ν := by
  have hx : (1 : ℝ) ≤ expDen ν (n + 1) := by
    have := cfDen_succ_pos (expQuot_succ_ge ν) n
    rw [cfDen_expQuot] at this
    exact_mod_cast this
  have hle : (expDen ν n : ℝ) ≤ expDen ν (n + 1) := by
    have := cfDen_le_succ (expQuot_succ_ge ν) n
    rw [cfDen_expQuot, cfDen_expQuot] at this
    exact_mod_cast this
  set x : ℝ := (expDen ν (n + 1) : ℝ)
  set t : ℝ := x ^ (ν - 1)
  have ht1 : 1 ≤ t := Real.one_le_rpow hx (by linarith)
  have hxν : x ^ ν = t * x := by
    rw [show t = x ^ (ν - 1) from rfl, ← Real.rpow_add_one (by linarith), sub_add_cancel]
  have hQ : (expDen ν (n + 2) : ℝ) = (⌈t⌉₊ + 1) * x + expDen ν n := by
    simp [expDen, x, t]
  have hc1 : t ≤ ⌈t⌉₊ := Nat.le_ceil t
  have hc2 : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
  have hn0 : (0 : ℝ) ≤ expDen ν n := Nat.cast_nonneg _
  rw [hQ, hxν]
  constructor <;> nlinarith

/-- The convergents of `expSlope ν` are good, with `q_n → ∞` and
`q_n^ν ≤ q_(n+1) ≤ 4 q_n^ν`. -/
theorem expSlope_good {ν : ℝ} (hν : 1 ≤ ν) :
    GoodConvergents (expSlope ν) (fun n => (cfNum (expQuot ν) (n + 1) : ℤ))
        (fun n => cfDen (expQuot ν) (n + 1)) ∧
      Tendsto (fun n => cfDen (expQuot ν) (n + 1)) atTop atTop ∧
      (∀ n, (cfDen (expQuot ν) (n + 1) : ℝ) ^ ν ≤ cfDen (expQuot ν) (n + 1 + 1)) ∧
      ∀ n, (cfDen (expQuot ν) (n + 1 + 1) : ℝ) ≤ 4 * (cfDen (expQuot ν) (n + 1) : ℝ) ^ ν := by
  refine ⟨cf_goodConvergents (expQuot_succ_ge ν),
    (cfDen_tendsto (expQuot_succ_ge ν)).comp (tendsto_add_atTop_nat 1),
    fun n => ?_, fun n => ?_⟩
  · simp only [cfDen_expQuot]; exact (expDen_growth hν n).1
  · simp only [cfDen_expQuot]; exact (expDen_growth hν n).2

/-- For every `ν > 1` the explicit slope `expSlope ν > 1` has complete
cluster set of Hausdorff dimension exactly `2/(2+ν)`. -/
theorem expSlope_cluster_dimH {ν : ℝ} (hν : 1 < ν) :
    dimH (passageClusterSet (1 / expSlope ν)) = ENNReal.ofReal (2 / (2 + ν)) := by
  obtain ⟨hG, hq, hlow, hup⟩ := expSlope_good hν.le
  exact regular_cluster_dimH_eq (one_lt_expSlope ν) (expSlope_irrational ν) hν hG hq
    one_pos (by norm_num : (0 : ℝ) < 4) (fun n => by simpa using hlow n) hup

/-- For every `ν > 1` there is an irrational slope `α > 1` whose complete
cluster set has Hausdorff dimension exactly `2/(2+ν)`. -/
theorem exists_slope_cluster_dimH {ν : ℝ} (hν : 1 < ν) :
    ∃ α : ℝ, 1 < α ∧ Irrational α ∧
      dimH (passageClusterSet (1 / α)) = ENNReal.ofReal (2 / (2 + ν)) :=
  ⟨expSlope ν, one_lt_expSlope ν, expSlope_irrational ν, expSlope_cluster_dimH hν⟩

/-! ### The dimension spectrum -/

/-- The Hausdorff dimensions of the complete cluster sets over all irrational
slopes `α > 1` fill exactly the interval `[0, 2/3]`. -/
theorem cluster_dimH_spectrum :
    range (fun α : {α : ℝ // 1 < α ∧ Irrational α} => dimH (passageClusterSet (1 / (α : ℝ))))
      = Icc 0 (2 / 3) := by
  ext d
  constructor
  · rintro ⟨⟨α, hα1, hα⟩, rfl⟩
    have hα0 : 0 < α := by linarith
    exact ⟨bot_le, passageCluster_dimH_le (one_div_pos.2 hα0) ((div_lt_one hα0).2 hα1)
      (by simpa using hα.inv)⟩
  · rintro ⟨-, hd⟩
    rcases eq_or_ne d 0 with rfl | hd0
    · have hL : Liouville (liouvilleNumber (10 : ℕ) + ((2 : ℕ) : ℝ)) :=
        forall_liouvilleWith_iff.1 fun p =>
          ((liouville_liouvilleNumber (by norm_num : 2 ≤ 10)).liouvilleWith p).add_nat 2
      have hn : 0 ≤ liouvilleNumber (10 : ℕ) := tsum_nonneg fun i => by positivity
      have h1 : 1 < liouvilleNumber (10 : ℕ) + ((2 : ℕ) : ℝ) := by
        rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]; linarith
      exact ⟨⟨_, h1, hL.irrational⟩, liouville_cluster_dimH h1 hL⟩
    rcases eq_or_ne d (2 / 3) with rfl | hd23
    · obtain ⟨h0, htop⟩ := golden_passageCluster_hausdorff
      refine ⟨⟨Real.goldenRatio, Real.one_lt_goldenRatio, Real.goldenRatio_irrational⟩, ?_⟩
      have h := dimH_of_hausdorffMeasure_ne_zero_ne_top (d := (2 / 3 : ℝ≥0))
        (s := passageClusterSet (1 / Real.goldenRatio))
        (by simpa using h0.ne') (by simpa using htop.ne)
      simpa using h
    · have hlt : d < 2 / 3 := lt_of_le_of_ne hd hd23
      have htop : d ≠ ⊤ := ne_top_of_lt hlt
      have ht0 : 0 < d.toReal := ENNReal.toReal_pos hd0 htop
      have ht23 : d.toReal < 2 / 3 := by
        have h23 : (2 / 3 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
        have := (ENNReal.toReal_lt_toReal htop h23).2 hlt
        simpa [ENNReal.toReal_div] using this
      set t := d.toReal
      have hν : 1 < 2 / t - 2 := by
        have : 3 < 2 / t := by rw [lt_div_iff₀ ht0]; linarith
        linarith
      have heq : 2 / (2 + (2 / t - 2)) = t := by
        rw [add_sub_cancel]; field_simp
      refine ⟨⟨expSlope (2 / t - 2), one_lt_expSlope _, expSlope_irrational _⟩, ?_⟩
      simp only
      rw [expSlope_cluster_dimH hν, heq, ENNReal.ofReal_toReal htop]

/-! ### Diophantine class -/

/-- Denominators `q ≥ 1` with an approximation `|q α - p| < q^(-μ)`. -/
def approxDenoms (α μ : ℝ) : Set ℕ :=
  {q : ℕ | 0 < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| < (q : ℝ) ^ (-μ)}

/-- `α` has Diophantine class exactly `ν`: for every `μ < ν` infinitely many
denominators `q ≥ 1` have some `p` with `|q α - p| < q^(-μ)`, and for every
`μ > ν` only finitely many do. -/
def DiophClass (α ν : ℝ) : Prop :=
  (∀ μ < ν, (approxDenoms α μ).Infinite) ∧ ∀ μ, ν < μ → (approxDenoms α μ).Finite

/-- Good convergents with regular growth `c q_n^ν ≤ q_(n+1) ≤ C q_n^ν` give
Diophantine class exactly `ν`. -/
theorem regular_diophClass {α ν c C : ℝ} (hν : 0 ≤ ν) {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hG : GoodConvergents α p q) (hq : Tendsto q atTop atTop) (hc : 0 < c) (hC : 0 < C)
    (hlow : ∀ n, c * (q n : ℝ) ^ ν ≤ q (n + 1))
    (hup : ∀ n, (q (n + 1) : ℝ) ≤ C * (q n : ℝ) ^ ν) : DiophClass α ν := by
  constructor
  · intro μ hμ
    have hqR : Tendsto (fun n => (q n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hq
    have hbig : Tendsto (fun n => c * (q n : ℝ) ^ (ν - μ)) atTop atTop :=
      ((tendsto_rpow_atTop (by linarith)).comp hqR).const_mul_atTop hc
    refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨n, hn1, hnN⟩ :=
      ((hbig.eventually_gt_atTop 1).and (hq.eventually_gt_atTop N)).exists
    have hq0 : (0 : ℝ) < q n := by exact_mod_cast hG.pos n
    refine ⟨q n, ⟨hG.pos n, p n, ?_⟩, hnN⟩
    have hden : (0 : ℝ) < c * (q n : ℝ) ^ ν := by positivity
    calc |(q n : ℝ) * α - p n| ≤ 1 / (q (n + 1) : ℝ) := hG.approx n
      _ ≤ 1 / (c * (q n : ℝ) ^ ν) := one_div_le_one_div_of_le hden (hlow n)
      _ < (q n : ℝ) ^ (-μ) := by
        rw [div_lt_iff₀ hden]
        have : (q n : ℝ) ^ (-μ) * (c * (q n : ℝ) ^ ν) = c * (q n : ℝ) ^ (ν - μ) := by
          rw [mul_left_comm, ← Real.rpow_add hq0]; ring_nf
        rw [this]; exact hn1
  · intro μ hμ
    obtain ⟨c', hc', hdio⟩ := regular_dio_lower hν hG hq hC hup
    have hsmall : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(μ - ν))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hsmall).2 c' hc')
    refine (Set.finite_Iio N).subset fun m hm => ?_
    obtain ⟨hm0, r, hr⟩ := hm
    by_contra hmN
    have hmN' : N ≤ m := not_lt.1 hmN
    have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
    have h1 := hdio m hm0 r
    have h2 : (m : ℝ) ^ ν * |(m : ℝ) * α - r| < (m : ℝ) ^ ν * (m : ℝ) ^ (-μ) :=
      mul_lt_mul_of_pos_left hr (by positivity)
    rw [← Real.rpow_add hm0R, show ν + -μ = -(μ - ν) by ring] at h2
    have := hN m hmN'
    linarith

/-- The explicit slope `expSlope ν` has Diophantine class exactly `ν`. -/
theorem expSlope_diophClass {ν : ℝ} (hν : 1 ≤ ν) : DiophClass (expSlope ν) ν := by
  obtain ⟨hG, hq, hlow, hup⟩ := expSlope_good hν
  exact regular_diophClass (by linarith) hG hq one_pos (by norm_num : (0 : ℝ) < 4)
    (fun n => by simpa using hlow n) hup

end Problems.Juggler.BeattySlope
