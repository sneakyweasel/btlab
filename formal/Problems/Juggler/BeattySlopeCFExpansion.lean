import Problems.Juggler.BeattySlopeConvergents

/-!
# The continued-fraction expansion of an irrational slope

For `α > 0` the Gauss map gives complete quotients `x_0 = α`,
`x_(k+1) = 1 / fract x_k` and partial quotients `a_k = ⌊x_k⌋`. When `α` is
irrational every `x_(k+1)` exceeds one, so `a_(k+1) ≥ 1`, and the continuants
satisfy `α (x_(k+1) Q_(k+1) + Q_k) = x_(k+1) P_(k+1) + P_k`. Hence
`|Q_(k+1) α - P_(k+1)| ≤ 1/Q_(k+1)`, and `α` is the limit `cfLim a` of its own
convergents. The convergents of every irrational `α > 0` are therefore
`GoodConvergents`. Since good convergents are stable under index shifts, the
regular-slope dimension `2/(2+ν)` holds for every irrational `α > 1` whose
continued-fraction denominators eventually grow like `q_n^ν`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set

/-- Complete quotients of `α` under the Gauss map: `x_0 = α`,
`x_(k+1) = (fract x_k)⁻¹`. -/
noncomputable def gaussQuot (α : ℝ) : ℕ → ℝ
  | 0 => α
  | k + 1 => (Int.fract (gaussQuot α k))⁻¹

/-- Partial quotients `a_k = ⌊x_k⌋` of `α`. -/
noncomputable def cfDigits (α : ℝ) (k : ℕ) : ℕ := ⌊gaussQuot α k⌋₊

variable {α : ℝ}

/-- Every complete quotient of an irrational number is irrational. -/
theorem gaussQuot_irrational (hα : Irrational α) : ∀ k, Irrational (gaussQuot α k)
  | 0 => hα
  | k + 1 => by
    have h := gaussQuot_irrational hα k
    have hf : Irrational (Int.fract (gaussQuot α k)) := by
      exact h.sub_intCast _
    exact hf.inv

/-- The fractional part of an irrational number lies strictly between `0` and `1`. -/
theorem fract_pos_of_irrational {x : ℝ} (hx : Irrational x) : 0 < Int.fract x := by
  rcases (Int.fract_nonneg x).lt_or_eq with h | h
  · exact h
  · exfalso
    have : x = ⌊x⌋ := by linarith [Int.floor_add_fract x]
    exact hx.ne_int _ this

/-- The complete quotients after the first exceed one. -/
theorem one_lt_gaussQuot (hα : Irrational α) (k : ℕ) : 1 < gaussQuot α (k + 1) := by
  show 1 < (Int.fract (gaussQuot α k))⁻¹
  exact one_lt_inv₀ (fract_pos_of_irrational (gaussQuot_irrational hα k)) |>.2
    (Int.fract_lt_one _)

/-- The partial quotients after the first are at least one. -/
theorem cfDigits_succ_ge (hα : Irrational α) (k : ℕ) : 1 ≤ cfDigits α (k + 1) :=
  Nat.le_floor (by simpa using (one_lt_gaussQuot hα k).le)

/-- The complete quotients are nonnegative when `α ≥ 0`. -/
theorem gaussQuot_nonneg (hα : Irrational α) (h0 : 0 ≤ α) : ∀ k, 0 ≤ gaussQuot α k
  | 0 => h0
  | k + 1 => zero_le_one.trans (one_lt_gaussQuot hα k).le

/-- One Gauss step: `x_k = a_k + 1/x_(k+1)`. -/
theorem gaussQuot_step (hα : Irrational α) (h0 : 0 ≤ α) (k : ℕ) :
    gaussQuot α k = cfDigits α k + (gaussQuot α (k + 1))⁻¹ := by
  have hn := gaussQuot_nonneg hα h0 k
  show gaussQuot α k = (⌊gaussQuot α k⌋₊ : ℝ) + ((Int.fract (gaussQuot α k))⁻¹)⁻¹
  rw [inv_inv, natCast_floor_eq_intCast_floor hn]
  exact (Int.floor_add_fract _).symm

/-- The complete-quotient identity
`α (x_(k+1) Q_(k+1) + Q_k) = x_(k+1) P_(k+1) + P_k`. -/
theorem cf_complete_identity (hα : Irrational α) (h0 : 0 ≤ α) : ∀ k,
    α * (gaussQuot α (k + 1) * cfDen (cfDigits α) (k + 1) + cfDen (cfDigits α) k) =
      gaussQuot α (k + 1) * cfNum (cfDigits α) (k + 1) + cfNum (cfDigits α) k
  | 0 => by
    have hs := gaussQuot_step hα h0 0
    have hx : gaussQuot α 1 ≠ 0 := (zero_lt_one.trans (one_lt_gaussQuot hα 0)).ne'
    simp only [cfDen, cfNum, Nat.cast_one, Nat.cast_zero, mul_one, add_zero]
    have : gaussQuot α 0 = α := rfl
    rw [this] at hs
    have hinv : gaussQuot α 1 * (gaussQuot α 1)⁻¹ = 1 := mul_inv_cancel₀ hx
    linear_combination gaussQuot α 1 * hs + hinv
  | k + 1 => by
    have ih := cf_complete_identity hα h0 k
    have hs := gaussQuot_step hα h0 (k + 1)
    have hx : gaussQuot α (k + 2) ≠ 0 := (zero_lt_one.trans (one_lt_gaussQuot hα (k + 1))).ne'
    have hstep : gaussQuot α (k + 1) * gaussQuot α (k + 2) =
        cfDigits α (k + 1) * gaussQuot α (k + 2) + 1 := by
      rw [hs]; field_simp
    rw [cfDen_add_two, cfNum_add_two]
    push_cast
    linear_combination gaussQuot α (k + 2) * ih -
      (α * cfDen (cfDigits α) (k + 1) - cfNum (cfDigits α) (k + 1)) * hstep

/-- The convergents of `α` approximate it: `|Q_(k+1) α - P_(k+1)| ≤ 1/Q_(k+1)`. -/
theorem cf_expansion_err_le (hα : Irrational α) (h0 : 0 ≤ α) (k : ℕ) :
    |(cfDen (cfDigits α) (k + 1) : ℝ) * α - cfNum (cfDigits α) (k + 1)| ≤
      1 / (cfDen (cfDigits α) (k + 1) : ℝ) := by
  set a := cfDigits α
  have ha : ∀ k, 1 ≤ a (k + 1) := cfDigits_succ_ge hα
  have hid := cf_complete_identity hα h0 k
  have hdet : (cfNum a (k + 1) : ℝ) * cfDen a k - cfNum a k * cfDen a (k + 1) =
      (-1) ^ (k + 1) := by exact_mod_cast cf_det a k
  set x := gaussQuot α (k + 1)
  have hx := one_lt_gaussQuot hα k
  have hq : (0 : ℝ) < cfDen a (k + 1) := by exact_mod_cast cfDen_succ_pos ha k
  have hq0 : (0 : ℝ) ≤ cfDen a k := Nat.cast_nonneg _
  set D := x * cfDen a (k + 1) + cfDen a k
  have hD : (cfDen a (k + 1) : ℝ) ≤ D := by nlinarith
  have hprod : ((cfDen a (k + 1) : ℝ) * α - cfNum a (k + 1)) * D = -(-1) ^ (k + 1) := by
    linear_combination (cfDen a (k + 1) : ℝ) * hid - hdet
  have habs : |(cfDen a (k + 1) : ℝ) * α - cfNum a (k + 1)| * D = 1 := by
    have := congrArg abs hprod
    rwa [abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (hq.trans_le hD)] at this
  rw [le_div_iff₀ hq]
  nlinarith [abs_nonneg ((cfDen a (k + 1) : ℝ) * α - cfNum a (k + 1))]

/-- An irrational `α ≥ 0` is the limit of its own continued-fraction convergents. -/
theorem cfLim_cfDigits (hα : Irrational α) (h0 : 0 ≤ α) : cfLim (cfDigits α) = α := by
  set a := cfDigits α
  have ha : ∀ k, 1 ≤ a (k + 1) := cfDigits_succ_ge hα
  by_contra hne
  set d := |α - cfLim a|
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  have hQ : Tendsto (fun k => (cfDen a (k + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((cfDen_tendsto ha).comp (tendsto_add_atTop_nat 1))
  obtain ⟨k, hk⟩ := (hQ.eventually_gt_atTop (2 / d)).exists
  have hq : (1 : ℝ) ≤ cfDen a (k + 1) := by exact_mod_cast cfDen_succ_pos ha k
  have hq2 : (1 : ℝ) ≤ cfDen a (k + 2) := by exact_mod_cast cfDen_succ_pos ha (k + 1)
  have e1 := cf_expansion_err_le hα h0 k
  have e2 : |(cfDen a (k + 1) : ℝ) * cfLim a - cfNum a (k + 1)| ≤ 1 / (cfDen a (k + 2) : ℝ) := by
    rw [abs_cf_err ha]; exact cfErr_le ha (k + 1)
  have i1 : 1 / (cfDen a (k + 1) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hq
  have i2 : 1 / (cfDen a (k + 2) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hq2
  have htri : d * cfDen a (k + 1) ≤ 2 := by
    have : d * cfDen a (k + 1) =
        |((cfDen a (k + 1) : ℝ) * α - cfNum a (k + 1)) -
          ((cfDen a (k + 1) : ℝ) * cfLim a - cfNum a (k + 1))| := by
      rw [show ((cfDen a (k + 1) : ℝ) * α - cfNum a (k + 1)) -
          ((cfDen a (k + 1) : ℝ) * cfLim a - cfNum a (k + 1)) =
          (α - cfLim a) * cfDen a (k + 1) by ring,
        abs_mul, abs_of_pos (by linarith : (0 : ℝ) < cfDen a (k + 1))]
    rw [this]
    linarith [abs_sub ((cfDen a (k + 1) : ℝ) * α - cfNum a (k + 1))
      ((cfDen a (k + 1) : ℝ) * cfLim a - cfNum a (k + 1))]
  have : 2 < d * cfDen a (k + 1) := by
    rw [div_lt_iff₀ hd] at hk; linarith
  linarith

/-- The continued-fraction convergents of an irrational `α ≥ 0`, indexed from
`P_1/Q_1`, are good convergents. -/
theorem irrational_goodConvergents (hα : Irrational α) (h0 : 0 ≤ α) :
    GoodConvergents α (fun n => (cfNum (cfDigits α) (n + 1) : ℤ))
      (fun n => cfDen (cfDigits α) (n + 1)) := by
  have h := cf_goodConvergents (cfDigits_succ_ge hα)
  rwa [cfLim_cfDigits hα h0] at h

/-- The continued-fraction denominators of an irrational number tend to infinity. -/
theorem cfDigits_den_tendsto (hα : Irrational α) :
    Tendsto (fun n => cfDen (cfDigits α) (n + 1)) atTop atTop :=
  (cfDen_tendsto (cfDigits_succ_ge hα)).comp (tendsto_add_atTop_nat 1)

/-- Good convergents are stable under a shift of index. -/
theorem GoodConvergents.shift {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q) (N : ℕ) :
    GoodConvergents α (fun n => p (n + N)) (fun n => q (n + N)) where
  pos n := hG.pos (n + N)
  coprime n := hG.coprime (n + N)
  approx n := by simpa [Nat.add_right_comm n 1 N] using hG.approx (n + N)
  sep n := hG.sep (n + N)

/-- **Theorem E 6 for continued fractions.** If the continued-fraction
denominators `q_n` of an irrational `α > 1` eventually satisfy
`c q_n^ν ≤ q_(n+1) ≤ C q_n^ν` with `ν > 1`, then `dim_H K_α = 2/(2+ν)`. -/
theorem cf_regular_dimH_eq {ν c C : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 < ν)
    (hc : 0 < c) (hC : 0 < C)
    (hgrow : ∀ᶠ n in atTop,
      c * (cfDen (cfDigits α) (n + 1) : ℝ) ^ ν ≤ cfDen (cfDigits α) (n + 2) ∧
        (cfDen (cfDigits α) (n + 2) : ℝ) ≤ C * (cfDen (cfDigits α) (n + 1) : ℝ) ^ ν) :
    dimH (passageClusterSet (1/α)) = ENNReal.ofReal (2 / (2 + ν)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgrow
  have hG := (irrational_goodConvergents hα (by linarith)).shift N
  have hq : Tendsto (fun n => cfDen (cfDigits α) (n + N + 1)) atTop atTop :=
    (cfDigits_den_tendsto hα).comp (tendsto_add_atTop_nat N)
  refine regular_cluster_dimH_eq hα1 hα hν hG hq hc hC (fun n => ?_) (fun n => ?_)
  · have := (hN (n + N) (Nat.le_add_left _ _)).1
    simpa [Nat.add_right_comm n 1 N, add_assoc] using this
  · have := (hN (n + N) (Nat.le_add_left _ _)).2
    simpa [Nat.add_right_comm n 1 N, add_assoc] using this

end Problems.Juggler.BeattySlope
