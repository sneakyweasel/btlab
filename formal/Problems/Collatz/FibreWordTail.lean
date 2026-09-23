import Problems.Collatz.FibreActual
import BTCalculus.GeometricMask

/-! # Repetitions of a fixed inverse block have summable fixed-root weight

Words are read from the target outward. One free initial exponent is followed
by a positive number of copies of one fixed nonempty positive-exponent block.
At a nonperiodic positive odd root, integrality forces geometric decay in
the number of blocks. Arbitrary mixtures of blocks are not covered.
-/

noncomputable section

namespace Problems.Collatz.FibreWordTail

open Finset FibreMass FibreActual
open scoped Classical

/-- Actual inverse words, with every positive odd intermediate state and
every positive halving exponent retained in the definition. -/
def RealizedWord (plus : Bool) : List ℕ → ℕ → ℕ → Prop
  | [], a, n => n = a ∧ 1 ≤ a ∧ Odd a
  | e::w, a, n => ∃ m, 1 ≤ e ∧ 1 ≤ a ∧ Odd a ∧ 1 ≤ m ∧ Odd m ∧
      numerator plus m = 2^e*a ∧ RealizedWord plus w m n

/-- Integer affine offset for an inverse word read from its target.
The recursion uses suffix exponents, not forward-orbit prefix exponents. -/
def wordOffset : List ℕ → ℕ
  | [] => 0
  | _::w => 2^w.sum + 3*wordOffset w

/-- Every realized inverse word has the exact signed affine endpoint equation. -/
theorem realizedWord_affine (plus : Bool) {w : List ℕ} {a n : ℕ}
    (h : RealizedWord plus w a n) :
    (3:ℤ)^w.length*n = (2:ℤ)^w.sum*a-sign plus*wordOffset w := by
  induction w generalizing a with
  | nil => obtain ⟨rfl, _, _⟩ := h; simp [wordOffset]
  | cons e w ih =>
      obtain ⟨m, he, ha, ho, hm, hmo, hfirst, hrest⟩ := h
      have hf := numerator_cast plus hm
      rw [hfirst] at hf
      push_cast at hf
      have ht := ih hrest
      simp only [List.length_cons, List.sum_cons, wordOffset, Nat.cast_add,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add, pow_succ]
      linear_combination 3*ht - (2:ℤ)^w.sum*hf

/-- Realized inverse words are literal ancestors under the signed odd return. -/
theorem realizedWord_returns (plus : Bool) {w : List ℕ} {a n : ℕ}
    (h : RealizedWord plus w a n) : (oddReturn plus)^[w.length] n = a := by
  induction w generalizing a with
  | nil => exact h.1
  | cons e w ih =>
      obtain ⟨m, he, ha, ho, hm, hmo, hfirst, hrest⟩ := h
      have hf := child_of_equation plus (e-1) ha hm (by simpa [Nat.sub_add_cancel he] using hfirst)
      have hr : oddReturn plus m = a := by
        rw [← hf.2]
        exact child_returns plus (e-1) ha ho hf.1
      rw [List.length_cons, Function.iterate_succ_apply', ih hrest, hr]

/-- One free exponent k+1 followed by d+1 copies of the same actual block. -/
def RealizedRepeat (plus : Bool) (w : List ℕ) (a k d : ℕ) : Prop :=
  1 ≤ a ∧ Odd a ∧ ∃ x : ℕ → ℕ, (1 ≤ x 0 ∧ Odd (x 0)) ∧
    numerator plus (x 0) = 2^(k+1)*a ∧
    ∀ j, j < d+1 → RealizedWord plus w (x j) (x (j+1))

private def gap (w : List ℕ) : ℤ := (2:ℤ)^w.sum-(3:ℤ)^w.length

private def anchor (plus : Bool) (w : List ℕ) (a k : ℕ) : ℤ :=
  gap w*(2:ℤ)^(k+1)*a-sign plus*(gap w+3*wordOffset w)

private theorem repeat_identity (plus : Bool) {w : List ℕ} {a k d : ℕ}
    (h : RealizedRepeat plus w a k d) :
    ∃ z : ℤ, ((3:ℤ)^w.length)^(d+1)*z =
      ((2:ℤ)^w.sum)^(d+1)*anchor plus w a k := by
  obtain ⟨ha, ho, x, hx, hfirst, hsteps⟩ := h
  have hf := numerator_cast plus hx.1
  rw [hfirst] at hf
  push_cast at hf
  have ht (j : ℕ) (hj : j ≤ d+1) :
      ((3:ℤ)^w.length)^j*(gap w*x j-sign plus*wordOffset w) =
        ((2:ℤ)^w.sum)^j*(gap w*x 0-sign plus*wordOffset w) := by
    induction j with
    | zero => simp
    | succ j ih =>
        have he := realizedWord_affine plus (hsteps j (by omega))
        have hi := ih (by omega)
        have hg : (3:ℤ)^w.length*(gap w*x (j+1)-sign plus*wordOffset w) =
            (2:ℤ)^w.sum*(gap w*x j-sign plus*wordOffset w) := by
          unfold gap
          linear_combination ((2:ℤ)^w.sum-(3:ℤ)^w.length)*he
        simp only [pow_succ]
        linear_combination ((3:ℤ)^w.length)^j*hg + (2:ℤ)^w.sum*hi
  refine ⟨3*(gap w*x (d+1)-sign plus*wordOffset w), ?_⟩
  have he := ht (d+1) le_rfl
  unfold anchor
  linear_combination 3*he - ((2:ℤ)^w.sum)^(d+1)*gap w*hf

/-- Repeated actual blocks force an exponentially growing ternary divisor
of one affine expression in the free first exponent. -/
theorem realizedRepeat_divisibility (plus : Bool) {w : List ℕ} {a k d : ℕ}
    (h : RealizedRepeat plus w a k d) :
    ((3:ℤ)^w.length)^(d+1) ∣
      ((2:ℤ)^w.sum-(3:ℤ)^w.length)*(2:ℤ)^(k+1)*a-
        sign plus*((2:ℤ)^w.sum-(3:ℤ)^w.length+3*wordOffset w) := by
  obtain ⟨z, hz⟩ := repeat_identity plus h
  have hd : ((3:ℤ)^w.length)^(d+1) ∣
      ((2:ℤ)^w.sum)^(d+1)*anchor plus w a k := ⟨z, hz.symm⟩
  have hc : IsCoprime (((3:ℤ)^w.length)^(d+1)) (((2:ℤ)^w.sum)^(d+1)) :=
    ((by norm_num : IsCoprime (3:ℤ) 2).pow).pow
  exact hc.dvd_of_dvd_mul_left hd

/-- A vanishing repeated-block anchor along an actual nonempty block forces
the root itself to be periodic. This is the precise resonance exception. -/
theorem zero_anchor_implies_periodic (plus : Bool) {w : List ℕ} (hw : w ≠ [])
    {a k d : ℕ} (h : RealizedRepeat plus w a k d)
    (hz : ((2:ℤ)^w.sum-(3:ℤ)^w.length)*(2:ℤ)^(k+1)*a-
      sign plus*((2:ℤ)^w.sum-(3:ℤ)^w.length+3*wordOffset w) = 0) :
    0 < w.length ∧ (oddReturn plus)^[w.length] a = a := by
  refine ⟨List.length_pos_iff_ne_nil.mpr hw, ?_⟩
  obtain ⟨ha, ho, x, hx, hfirst, hsteps⟩ := h
  have hf := numerator_cast plus hx.1
  rw [hfirst] at hf
  push_cast at hf
  have he := realizedWord_affine plus (hsteps 0 (by omega))
  have hg : ((2:ℤ)^w.sum-(3:ℤ)^w.length)*x 0-sign plus*wordOffset w = 0 := by
    have ht : 3*(((2:ℤ)^w.sum-(3:ℤ)^w.length)*x 0-sign plus*wordOffset w) = 0 := by
      linear_combination hz - ((2:ℤ)^w.sum-(3:ℤ)^w.length)*hf
    omega
  have hx1 : x 1 = x 0 := by
    have hB : (0:ℤ) < 3^w.length := by positivity
    have hi : (3:ℤ)^w.length*((x 1:ℤ)-x 0) = 0 := by linear_combination he + hg
    have hn : (x 1:ℤ) = x 0 := by nlinarith
    exact_mod_cast hn
  have hp := realizedWord_returns plus (hsteps 0 (by omega))
  rw [hx1] at hp
  have hc := child_of_equation plus k ha hx.1 hfirst
  have hr : oddReturn plus (x 0) = a := by
    rw [← hc.2]
    exact child_returns plus k ha ho hc.1
  rw [← hr, ← Function.iterate_succ_apply, Function.iterate_succ_apply', hp]

/-- An explicit fixed-root allowance for a repeated block. It depends on
the block and root, never on the free exponent or number of repetitions. -/
def wordAllowance (w : List ℕ) (a : ℕ) : ℝ :=
  |(2:ℝ)^w.sum-(3:ℝ)^w.length| * a +
    |(2:ℝ)^w.sum-(3:ℝ)^w.length+3*wordOffset w|

private def weight (w : List ℕ) (d k : ℕ) : ℝ :=
  (3/2:ℝ)*((3:ℝ)^w.length/(2:ℝ)^w.sum)^(d+1)*(1/2:ℝ)^k

/-- Complete coefficient of one arbitrary initial exponent followed by
d+1 copies of a fixed block. No exponent cutoff is imposed. -/
def repeatCoefficient (plus : Bool) (w : List ℕ) (a d : ℕ) : ℝ :=
  ∑' k : ℕ, if RealizedRepeat plus w a k d then weight w d k else 0

private theorem allowance_nonneg (w : List ℕ) (a : ℕ) : 0 ≤ wordAllowance w a := by
  unfold wordAllowance
  positivity

private theorem anchor_bound (plus : Bool) (w : List ℕ) (a k : ℕ) :
    |(anchor plus w a k : ℝ)| ≤ wordAllowance w a*(2:ℝ)^(k+1) := by
  have hs : |(sign plus : ℝ)| = 1 := by cases plus <;> norm_num [sign]
  have hp : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
  have he : (anchor plus w a k : ℝ) =
      ((2:ℝ)^w.sum-(3:ℝ)^w.length)*(2:ℝ)^(k+1)*a-
        (sign plus:ℝ)*((2:ℝ)^w.sum-(3:ℝ)^w.length+3*wordOffset w) := by
    unfold anchor gap
    push_cast
    rfl
  rw [he]
  calc
    _ ≤ |((2:ℝ)^w.sum-(3:ℝ)^w.length)*(2:ℝ)^(k+1)*a|+
        |(sign plus:ℝ)*((2:ℝ)^w.sum-(3:ℝ)^w.length+3*wordOffset w)| := by
          simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le
            (((2:ℝ)^w.sum-(3:ℝ)^w.length)*(2:ℝ)^(k+1)*a) 0
            ((sign plus:ℝ)*((2:ℝ)^w.sum-(3:ℝ)^w.length+3*wordOffset w)))
    _ = |(2:ℝ)^w.sum-(3:ℝ)^w.length| * (2:ℝ)^(k+1)*a+
        |(2:ℝ)^w.sum-(3:ℝ)^w.length+3*wordOffset w| := by
      simp [abs_mul, hs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2^(k+1))]
    _ ≤ _ := by
      unfold wordAllowance
      nlinarith [abs_nonneg ((2:ℝ)^w.sum-(3:ℝ)^w.length+3*wordOffset w)]

private theorem first_weight_bound (plus : Bool) {w : List ℕ} (hw : w ≠ [])
    {a k d : ℕ} (h : RealizedRepeat plus w a k d)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] a ≠ a) :
    2*weight w d k ≤ 6*wordAllowance w a / ((2:ℝ)^w.sum)^(d+1) := by
  have hd : ((3:ℤ)^w.length)^(d+1) ∣ anchor plus w a k :=
    realizedRepeat_divisibility plus h
  have hz : anchor plus w a k ≠ 0 := by
    intro hz
    have hp := zero_anchor_implies_periodic plus hw h hz
    exact hnp w.length hp.1 hp.2
  have hn := Int.natAbs_le_of_dvd_ne_zero hd hz
  have hnR : ((3:ℝ)^w.length)^(d+1) ≤ |(anchor plus w a k : ℝ)| := by
    have hc : ((((3:ℤ)^w.length)^(d+1)).natAbs : ℝ) ≤
        ((anchor plus w a k).natAbs : ℝ) := by exact_mod_cast hn
    simpa [Nat.cast_natAbs, abs_of_nonneg
      (by positivity : (0:ℝ) ≤ ((3:ℝ)^w.length)^(d+1))] using hc
  have hb := hnR.trans (anchor_bound plus w a k)
  have hA : (0:ℝ) < ((2:ℝ)^w.sum)^(d+1) := by positivity
  have hE : (0:ℝ) < 2^(k+1) := by positivity
  have he : weight w d k =
      3*((3:ℝ)^w.length)^(d+1)/((2:ℝ)^(k+1)*((2:ℝ)^w.sum)^(d+1)) := by
    unfold weight
    rw [div_pow, div_pow, one_pow, pow_succ]
    field_simp
    ring
  have ht : weight w d k ≤ 3*wordAllowance w a / ((2:ℝ)^w.sum)^(d+1) := by
    rw [he]
    apply (div_le_div_iff₀ (mul_pos hE hA) hA).mpr
    nlinarith [mul_le_mul_of_nonneg_right hb (show 0 ≤ 3*((2:ℝ)^w.sum)^(d+1) by positivity)]
  calc
    2*weight w d k ≤ 2*(3*wordAllowance w a / ((2:ℝ)^w.sum)^(d+1)) :=
      mul_le_mul_of_nonneg_left ht (by norm_num)
    _ = _ := by ring

/-- Any fixed nonempty inverse block has geometrically bounded complete
repeat mass at a nonperiodic root. Only realized positive odd words count;
the bound includes every first halving exponent. -/
theorem repeatCoefficient_bounds (plus : Bool) {w : List ℕ} (hw : w ≠ [])
    (a : ℕ) (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] a ≠ a) (d : ℕ) :
    0 ≤ repeatCoefficient plus w a d ∧ repeatCoefficient plus w a d ≤
      6*wordAllowance w a / ((2:ℝ)^w.sum)^(d+1) := by
  constructor
  · apply tsum_nonneg
    intro k
    split_ifs
    · unfold weight; positivity
    · norm_num
  · apply BTCalculus.GeometricMask.tsum_mask_le
      (RealizedRepeat plus w a · d) (by positivity)
      (div_nonneg (mul_nonneg (by norm_num) (allowance_nonneg w a)) (by positivity))
    intro k hk
    exact first_weight_bound plus hw hk hnp

private theorem sum_pos {w : List ℕ} (hw : w ≠ []) (he : ∀ e ∈ w, 1 ≤ e) : 1 ≤ w.sum := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons e w => have ht := he e (by simp); simp only [List.sum_cons]; omega

/-- Summing over all positive repetition counts of one fixed positive
block has finite total coefficient at a nonperiodic root. -/
theorem repeatCoefficient_summable (plus : Bool) {w : List ℕ} (hw : w ≠ [])
    (he : ∀ e ∈ w, 1 ≤ e) (a : ℕ)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] a ≠ a) :
    Summable (fun d => repeatCoefficient plus w a d) := by
  have hA : (1:ℝ) < 2^w.sum := one_lt_pow₀ (by norm_num) (by have := sum_pos hw he; omega)
  have hp : (0:ℝ) < 2^w.sum := by positivity
  have hq : (1 / (2:ℝ)^w.sum) < 1 := (div_lt_one hp).mpr hA
  have hg := (summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ 1/2^w.sum) hq)
  apply Summable.of_nonneg_of_le (fun d => (repeatCoefficient_bounds plus hw a hnp d).1)
    (fun d => (repeatCoefficient_bounds plus hw a hnp d).2)
  have hf : (fun d : ℕ => 6*wordAllowance w a / ((2:ℝ)^w.sum)^(d+1)) =
      (fun d : ℕ => (6*wordAllowance w a)*(1/(2:ℝ)^w.sum)^(d+1)) := by
    funext d
    rw [div_pow, one_pow]
    ring
  rw [hf]
  exact ((summable_nat_add_iff 1).mpr hg).mul_left (6*wordAllowance w a)

/-- The complete allowance over all positive repetition counts is explicit.
This is a bound for one fixed block, not for arbitrary concatenations. -/
theorem total_repeatCoefficient_le (plus : Bool) {w : List ℕ} (hw : w ≠ [])
    (he : ∀ e ∈ w, 1 ≤ e) (a : ℕ)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] a ≠ a) :
    (∑' d, repeatCoefficient plus w a d) ≤ 6*wordAllowance w a / ((2:ℝ)^w.sum-1) := by
  have hA : (1:ℝ) < 2^w.sum := one_lt_pow₀ (by norm_num) (by have := sum_pos hw he; omega)
  have hp : (0:ℝ) < 2^w.sum := by positivity
  have hq : (1 / (2:ℝ)^w.sum) < 1 := (div_lt_one hp).mpr hA
  have hg := summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ 1/2^w.sum) hq
  have hf (d : ℕ) : 6*wordAllowance w a / ((2:ℝ)^w.sum)^(d+1) =
      (6*wordAllowance w a / (2:ℝ)^w.sum)*(1/(2:ℝ)^w.sum)^d := by
    rw [div_pow, one_pow, pow_succ]
    ring
  have hl := Summable.tsum_le_tsum (fun d => (repeatCoefficient_bounds plus hw a hnp d).2)
    (repeatCoefficient_summable plus hw he a hnp)
    (by simp_rw [hf]; exact hg.mul_left _)
  apply hl.trans_eq
  simp_rw [hf]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hq]
  field_simp

/-- The negative cycle through five supplies a genuinely growing repeated
two-step block, so the nonperiodic-root restriction cannot be discarded. -/
theorem negative_five_cycle_lower (d : ℕ) :
    (3/4:ℝ)*(9/8:ℝ)^(d+1) ≤ repeatCoefficient false [1,2] 5 d := by
  have hblock : RealizedWord false [1,2] 7 7 := by
    refine ⟨5, by norm_num, by norm_num, by decide, by norm_num, by decide, ?_, ?_⟩
    · norm_num [numerator]
    · refine ⟨7, by norm_num, by norm_num, by decide, by norm_num, by decide, ?_, ?_⟩
      · norm_num [numerator]
      · exact ⟨rfl, by norm_num, by decide⟩
  have hr : RealizedRepeat false [1,2] 5 1 d := by
    refine ⟨by norm_num, by decide, fun _ => 7, ?_, ?_, ?_⟩
    · change 1 ≤ (7:ℕ) ∧ Odd (7:ℕ)
      decide
    · norm_num [numerator]
    · intro j hj
      exact hblock
  have hs := BTCalculus.GeometricMask.summable_mask
    (fun k => RealizedRepeat false [1,2] 5 k d)
    (show 0 ≤ (3/2:ℝ)*((3:ℝ)^([1,2]:List ℕ).length/
      (2:ℝ)^([1,2]:List ℕ).sum)^(d+1) by positivity)
  have ht := hs.le_tsum 1 (fun k _ => by split_ifs <;> positivity)
  change (if RealizedRepeat false [1,2] 5 1 d then weight [1,2] d 1 else 0) ≤
    repeatCoefficient false [1,2] 5 d at ht
  norm_num [hr, weight] at ht
  nlinarith

end Problems.Collatz.FibreWordTail
