import Problems.Collatz.FibreUnitComparison

/-! # Cross-sign pairing gains one generation but does not reproduce at depth two

All coefficients are complete sums with unit sources. Pairing both signs at
one generation has lower bound `9/7`; keeping each sign for two generations
has a simultaneous deficit on the class `4 mod 27`. Mixed-sign trajectories
are a different system. No assertion of fixed-root series convergence follows.
-/

noncomputable section

namespace Problems.Collatz.FibreSignCoupling

open Finset FibreMass FibreActual FibreGeneration
open scoped Classical ENNReal

private theorem oddPart_double {v : ℕ} (hv : v ≠ 0) :
    (2*v) / 2^padicValNat 2 (2*v) = v / 2^padicValNat 2 v := by
  rw [padicValNat.mul (by norm_num : (2:ℕ) ≠ 0) hv]
  norm_num [padicValNat_self]
  rw [pow_add, pow_one, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]

/-- A plus predecessor and its doubled, shifted minus counterpart have exactly
the same odd image. This does not identify their subsequent fixed-sign orbits. -/
theorem oddReturn_minus_two_mul_add_one (n : ℕ) :
    oddReturn false (2*n+1) = oddReturn true n := by
  have he : numerator false (2*n+1) = 2*(3*n+1) := by
    simp only [numerator, Bool.false_eq_true, ↓reduceIte]; omega
  simp only [oddReturn]
  rw [he]
  exact oddPart_double (v := 3*n+1) (by omega)

/-- The reverse cross-sign pairing, at positive inputs. -/
theorem oddReturn_plus_two_mul_sub_one {n : ℕ} (hn : 1 ≤ n) :
    oddReturn true (2*n-1) = oddReturn false n := by
  have he : numerator true (2*n-1) = 2*(3*n-1) := by
    simp only [numerator, ↓reduceIte]; omega
  simp only [oddReturn]
  rw [he]
  exact oddPart_double (v := 3*n-1) (by omega)

private def unitRow (plus : Bool) : Level 2 → ℝ :=
  fun a => if plus then
    match a.val with
    | 1 => 20/21 | 2 => 40/21 | 4 => 17/21 | 5 => 10/21
    | 7 => 5/21 | 8 => 34/21 | _ => 0
  else
    match a.val with
    | 1 => 34/21 | 2 => 5/21 | 4 => 10/21 | 5 => 17/21
    | 7 => 40/21 | 8 => 20/21 | _ => 0

set_option maxHeartbeats 2000000 in
private theorem transfer_unitRow (plus : Bool) (a : Level 2) :
    transfer plus 1 unitWeight a = unitRow plus a := by
  have hs := transfer_period_sum plus 1 6 (by norm_num [Nat.ModEq])
    (h := unitWeight) (fun b => by unfold unitWeight; split_ifs <;> norm_num) a
  have hr (k : ℕ) : row plus 1 k unitWeight a = coefficient k *
      ((if parent plus 1 k 0 = a then unitWeight 0 else 0) +
       (if parent plus 1 k 1 = a then unitWeight 1 else 0) +
       (if parent plus 1 k 2 = a then unitWeight 2 else 0)) := by
    unfold row
    congr 1
    change (∑ b : Fin 3, if parent plus 1 k b = a then unitWeight b else 0) = _
    simp only [Fin.sum_univ_succ]
    simp; ring
  simp only [sum_range_succ, sum_range_zero, hr, parent_iff] at hs
  cases plus <;> fin_cases a <;>
    norm_num [coefficient, unitWeight, offset, Nat.ModEq, unitRow] at hs ⊢ <;> linarith

/-- Pairing the two complete one-step unit coefficients gives at least `9/7`
at every unit target. The bound concerns one step, with a separate sign choice. -/
theorem paired_unit_lower (a : Level 2) (ha : a.val % 3 ≠ 0) :
    (9/7:ℝ) ≤ transfer true 1 unitWeight a + transfer false 1 unitWeight a := by
  rw [transfer_unitRow, transfer_unitRow]
  fin_cases a <;> norm_num [unitRow] at *

set_option maxHeartbeats 4000000 in
private theorem depth_two_at_four (plus : Bool) :
    iterate plus 1 unitWeight 2 (4 : Level 3) =
      if plus then (12076/29127:ℝ) else 7988/29127 := by
  change transfer plus 2 (transfer plus 1 unitWeight) 4 = _
  have he : transfer plus 1 unitWeight = unitRow plus := funext (transfer_unitRow plus)
  rw [he]
  have hn : ∀ b, 0 ≤ unitRow plus b := by
    intro b; cases plus <;> fin_cases b <;> norm_num [unitRow]
  have hs := transfer_period_sum plus 2 18 (by norm_num [Nat.ModEq]) hn (4 : Level 3)
  have hr (k : ℕ) : row plus 2 k (unitRow plus) (4 : Level 3) = coefficient k *
      ∑ b : Fin 9, if parent plus 2 k b = (4 : Level 3) then unitRow plus b else 0 := rfl
  simp only [sum_range_succ, sum_range_zero, hr, Fin.sum_univ_succ, Fin.sum_univ_zero,
    parent_iff] at hs
  cases plus <;> norm_num [coefficient, offset, Nat.ModEq, unitRow] at hs ⊢ <;> linarith

/-- Both signs have a deficit at every target in one infinite arithmetic class.
The sum itself is below one, even before dividing by two to form an average. -/
theorem paired_depth_two_deficit {m : ℕ} (hm : m % 27 = 4) :
    FibreHeightBudget.kernel true 2 m = (12076/29127:ℝ) ∧
    FibreHeightBudget.kernel false 2 m = (7988/29127:ℝ) ∧
    FibreHeightBudget.kernel true 2 m + FibreHeightBudget.kernel false 2 m < 1 := by
  have he : residue 3 m = (4 : Level 3) := by apply Fin.ext; exact hm
  have hp : FibreHeightBudget.kernel true 2 m = (12076/29127:ℝ) := by
    simpa only [FibreHeightBudget.kernel, he, ↓reduceIte] using depth_two_at_four true
  have hn : FibreHeightBudget.kernel false 2 m = (7988/29127:ℝ) := by
    simpa only [FibreHeightBudget.kernel, he, Bool.false_eq_true, ↓reduceIte] using depth_two_at_four false
  exact ⟨hp, hn, by rw [hp, hn]; norm_num⟩

/-- A common bound for the actual reciprocal correction of two inverse steps,
including both signs. Its hypotheses are real inequalities implied by the
cleared integer predecessor equations. -/
theorem two_step_reciprocal_upper {p q a b c : ℝ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (ha : 2 ≤ a) (hc : 0 < c)
    (hb : p*a-1 ≤ 3*b) (he : q*b-1 ≤ 3*c) :
    a/c ≤ (9/(p*q))*(a/(a-5/4)) := by
  have hpq : 0 < p*q := mul_pos (by linarith) (by linarith)
  have hqa : 0 ≤ q*(p-2) := mul_nonneg (by linarith) (by linarith)
  have hsmall : q+3 ≤ (5/4)*(p*q) := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ q)
  have hden : p*q*(a-5/4) ≤ 9*c := by nlinarith
  have had : 0 < a-5/4 := by linarith
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ hc (mul_pos hpq had)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden (by linarith : 0 ≤ a)]

/-- Actual reciprocal mass at exactly two fixed-sign odd returns, retaining
positive odd sources prime to three. Extended nonnegative sums do not assume
convergence; the bound below proves it. Each integer is counted once. -/
def twoStepMass (plus : Bool) (a : ℕ) : ℝ≥0∞ :=
  ∑' n : {n : ℕ // 1 ≤ n ∧ Odd n ∧ oddReturn plus (oddReturn plus n) = a},
    if n.val % 3 = 0 then 0 else 1/(n.val : ℝ≥0∞)

private abbrev InversePair (plus : Bool) (a : ℕ) :=
  Σ k : {k : ℕ // Admissible plus k a},
    {l : ℕ // Admissible plus l (child plus k.val a)}

private def inversePairEquiv (plus : Bool) {a : ℕ} (ha : 1 ≤ a) (ho : Odd a) :
    InversePair plus a ≃
      {n : ℕ // 1 ≤ n ∧ Odd n ∧ oddReturn plus (oddReturn plus n) = a} :=
  Equiv.ofBijective (fun x =>
    ⟨child plus x.2.val (child plus x.1.val a),
      child_pos plus x.2.val (child_pos plus x.1.val ha x.1.property) x.2.property,
      child_odd plus x.2.val (child_pos plus x.1.val ha x.1.property) x.2.property,
      by rw [child_returns plus x.2.val (child_pos plus x.1.val ha x.1.property)
        (child_odd plus x.1.val ha x.1.property) x.2.property,
        child_returns plus x.1.val ha ho x.1.property]⟩) (by
    constructor
    · rintro ⟨k,l⟩ ⟨k',l'⟩ he
      have hv := congrArg Subtype.val he
      have hb : child plus k.val a = child plus k'.val a := by
        have ht := congrArg (oddReturn plus) hv
        simpa only [child_returns plus l.val (child_pos plus k.val ha k.property)
          (child_odd plus k.val ha k.property) l.property,
          child_returns plus l'.val (child_pos plus k'.val ha k'.property)
          (child_odd plus k'.val ha k'.property) l'.property] using ht
      have hk : k = k' := Subtype.ext (child_injective plus ha ho k.property k'.property hb)
      subst k'
      have hl : l = l' := Subtype.ext (child_injective plus
        (child_pos plus k.val ha k.property) (child_odd plus k.val ha k.property)
        l.property l'.property hv)
      subst l'
      rfl
    · intro n
      have hb : 1 ≤ oddReturn plus n.val := Nat.succ_le_iff.mpr (oddReturn_pos plus n.property.1)
      have hbo := oddReturn_odd plus n.property.1
      obtain ⟨k,hk,hbEq⟩ := (predecessor_iff plus ha ho).mp ⟨hb,hbo,n.property.2.2⟩
      obtain ⟨l,hl,hnEq⟩ := (predecessor_iff plus (child_pos plus k ha hk)
        (child_odd plus k ha hk)).mp ⟨n.property.1,n.property.2.1,hbEq.symm⟩
      exact ⟨⟨⟨k,hk⟩,⟨l,hl⟩⟩,Subtype.ext hnEq⟩)

private theorem twoStepMass_eq_pairs (plus : Bool) {a : ℕ} (ha : 1 ≤ a) (ho : Odd a) :
    twoStepMass plus a =
      ∑' k : {k : ℕ // Admissible plus k a},
      ∑' l : {l : ℕ // Admissible plus l (child plus k.val a)},
        if (child plus l.val (child plus k.val a)) % 3 = 0 then 0
        else 1/(child plus l.val (child plus k.val a) : ℝ≥0∞) := by
  unfold twoStepMass
  rw [← (inversePairEquiv plus ha ho).tsum_eq]
  exact ENNReal.tsum_sigma' _

private theorem transfer_eq_admissible_sum (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) {a : ℕ} (ha : 1 ≤ a) :
    ENNReal.ofReal (transfer plus r h (residue (r+1) a)) =
      ∑' k : {k : ℕ // Admissible plus k a},
        ENNReal.ofReal (coefficient k.val * h (residue r (child plus k.val a))) := by
  unfold transfer
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => row_nonneg plus r k hh _)
    (row_summable plus r hh _)]
  simp_rw [row_eq_branchWeight plus r _ _ ha, branchWeight, mul_ite, mul_zero,
    apply_ite ENNReal.ofReal, ENNReal.ofReal_zero]
  simpa only [Set.coe_ofPred, Set.indicator_apply, Set.mem_ofPred_eq] using
    (_root_.tsum_subtype {k : ℕ | Admissible plus k a}
      (fun k => ENNReal.ofReal (coefficient k * h (residue r (child plus k a))))).symm

private theorem coefficient_nonneg (k : ℕ) : 0 ≤ coefficient k := by
  unfold coefficient; positivity

private theorem unit_nonneg (b : Level 1) : 0 ≤ unitWeight b := by
  unfold unitWeight; split_ifs <;> norm_num

private theorem kernel_eq_pairs (plus : Bool) {a : ℕ} (ha : 1 ≤ a) :
    ENNReal.ofReal (FibreHeightBudget.kernel plus 2 a) =
      ∑' k : {k : ℕ // Admissible plus k a},
      ∑' l : {l : ℕ // Admissible plus l (child plus k.val a)},
        ENNReal.ofReal (coefficient k.val * coefficient l.val *
          unitWeight (residue 1 (child plus l.val (child plus k.val a)))) := by
  change ENNReal.ofReal (transfer plus 2 (transfer plus 1 unitWeight) (residue 3 a)) = _
  rw [transfer_eq_admissible_sum plus 2 (fun b => transfer_nonneg plus 1 unit_nonneg b) ha]
  apply tsum_congr
  intro k
  rw [ENNReal.ofReal_mul (coefficient_nonneg k.val),
    transfer_eq_admissible_sum plus 1 unit_nonneg (child_pos plus k.val ha k.property),
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  rw [← ENNReal.ofReal_mul (coefficient_nonneg k.val)]
  congr 1
  ring

private theorem child_lower (plus : Bool) (k : ℕ) {a : ℕ} (ha : 1 ≤ a)
    (hk : Admissible plus k a) :
    (2:ℝ)^(k+1)*a-1 ≤ 3*(child plus k a : ℝ) := by
  have h : (3:ℤ)*child plus k a = (2:ℤ)^(k+1)*a-sign plus := by
    rw [← raw_cast plus k ha]
    exact_mod_cast child_mul plus k a hk
  have hr : (3:ℝ)*child plus k a = (2:ℝ)^(k+1)*a-(sign plus:ℝ) := by exact_mod_cast h
  cases plus <;> norm_num [sign] at hr ⊢ <;> linarith

private theorem pair_reciprocal_le (plus : Bool) {a : ℕ} (ha : 2 ≤ a)
    (k : {k : ℕ // Admissible plus k a})
    (l : {l : ℕ // Admissible plus l (child plus k.val a)}) :
    (if (child plus l.val (child plus k.val a)) % 3 = 0 then 0
      else 1/(child plus l.val (child plus k.val a) : ℝ≥0∞)) ≤
      ENNReal.ofReal (1/((a:ℝ)-5/4)) *
        ENNReal.ofReal (coefficient k.val * coefficient l.val *
          unitWeight (residue 1 (child plus l.val (child plus k.val a)))) := by
  let b := child plus k.val a
  let c := child plus l.val b
  have ha1 : 1 ≤ a := by omega
  have hb : 1 ≤ b := child_pos plus k.val ha1 k.property
  have hc : 0 < (c:ℝ) := by exact_mod_cast child_pos plus l.val hb l.property
  have har : 0 < (a:ℝ) := by exact_mod_cast (show 0 < a by omega)
  have had : 0 < (a:ℝ)-5/4 := by
    have : (2:ℝ) ≤ a := by exact_mod_cast ha
    linarith
  by_cases hu : c % 3 = 0
  · change (if c % 3 = 0 then _ else _) ≤ _
    simp only [hu, ↓reduceIte]
    exact zero_le
  have ht := two_step_reciprocal_upper
    (p := (2:ℝ)^(k.val+1)) (q := (2:ℝ)^(l.val+1))
    (a := a) (b := b) (c := c)
    (by exact_mod_cast pow_two_lower k.val) (by exact_mod_cast pow_two_lower l.val)
    (by exact_mod_cast ha) hc (child_lower plus k.val ha1 k.property)
    (child_lower plus l.val hb l.property)
  have hr : (1:ℝ)/c ≤ (1/((a:ℝ)-5/4)) * (coefficient k.val * coefficient l.val) := by
    have hs := div_le_div_of_nonneg_right ht har.le
    calc
      (1:ℝ)/c = ((a:ℝ)/c)/a := by field_simp
      _ ≤ _ := hs
      _ = _ := by rw [coefficient_eq, coefficient_eq]; field_simp; ring
  have he := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_one, ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/((a:ℝ)-5/4))] at he
  simpa [c, b, unitWeight, residue, hu] using he

/-- The complete actual two-generation mass is bounded by its full coefficient
with the explicit affine correction. No finite truncation or convergence
assumption occurs, and the sign is fixed for both returns. -/
theorem twoStepMass_le (plus : Bool) {a : ℕ} (ha : 2 ≤ a) (ho : Odd a) :
    twoStepMass plus a ≤ ENNReal.ofReal
      (FibreHeightBudget.kernel plus 2 a / ((a:ℝ)-5/4)) := by
  have ha1 : 1 ≤ a := by omega
  have had : 0 < (a:ℝ)-5/4 := by
    have : (2:ℝ) ≤ a := by exact_mod_cast ha
    linarith
  rw [twoStepMass_eq_pairs plus ha1 ho]
  calc
    _ ≤ ∑' k : {k : ℕ // Admissible plus k a},
        ∑' l : {l : ℕ // Admissible plus l (child plus k.val a)},
          ENNReal.ofReal (1/((a:ℝ)-5/4)) *
            ENNReal.ofReal (coefficient k.val * coefficient l.val *
              unitWeight (residue 1 (child plus l.val (child plus k.val a)))) :=
      ENNReal.tsum_le_tsum (fun k => ENNReal.tsum_le_tsum (fun l => pair_reciprocal_le plus ha k l))
    _ = ENNReal.ofReal (1/((a:ℝ)-5/4)) * ENNReal.ofReal (FibreHeightBudget.kernel plus 2 a) := by
      simp_rw [ENNReal.tsum_mul_left]
      rw [← kernel_eq_pairs plus ha1]
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/((a:ℝ)-5/4))]; congr 1; ring

/-- The actual reciprocal sum at depth two is finite under either sign. -/
theorem twoStepMass_lt_top (plus : Bool) {a : ℕ} (ha : 2 ≤ a) (ho : Odd a) :
    twoStepMass plus a < ∞ :=
  (twoStepMass_le plus ha ho).trans_lt ENNReal.ofReal_lt_top

/-- The corresponding ordinary real reciprocal series converges. Thus a real
sum cannot hide a divergent positive series behind the default tsum value. -/
theorem two_step_reciprocals_summable (plus : Bool) {a : ℕ} (ha : 2 ≤ a) (ho : Odd a) :
    Summable (fun n : {n : ℕ // 1 ≤ n ∧ Odd n ∧ oddReturn plus (oddReturn plus n) = a} =>
      if n.val % 3 = 0 then (0:ℝ) else 1/(n.val:ℝ)) := by
  have hs := ENNReal.summable_toReal (twoStepMass_lt_top plus ha ho).ne
  simpa only [twoStepMass, apply_ite, ENNReal.toReal_zero, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_natCast] using hs

/-- On the entire positive odd class 4 mod 27, even the sum of both actual
two-generation masses is strictly below three quarters of the root's weight. -/
theorem paired_twoStepMass_lt {a : ℕ} (ha : 31 ≤ a) (ho : Odd a) (hc : a % 27 = 4) :
    (a:ℝ≥0∞) * (twoStepMass true a + twoStepMass false a) < 3/4 := by
  have har : (31:ℝ) ≤ a := by exact_mod_cast ha
  have had : 0 < (a:ℝ)-5/4 := by linarith
  obtain ⟨hp,hn,_⟩ := paired_depth_two_deficit hc
  have hle := add_le_add (twoStepMass_le true (by omega : 2 ≤ a) ho)
    (twoStepMass_le false (by omega : 2 ≤ a) ho)
  rw [hp, hn, ← ENNReal.ofReal_add (by positivity) (by positivity)] at hle
  have he : (12076/29127:ℝ)/((a:ℝ)-5/4) + (7988/29127:ℝ)/((a:ℝ)-5/4) =
      (352/511:ℝ)/((a:ℝ)-5/4) := by ring
  rw [he] at hle
  have hr : (a:ℝ) * ((352/511:ℝ)/((a:ℝ)-5/4)) < 3/4 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ had).mpr
    nlinarith
  calc
    _ ≤ (a:ℝ≥0∞) * ENNReal.ofReal ((352/511:ℝ)/((a:ℝ)-5/4)) := mul_le_mul_right hle _
    _ = ENNReal.ofReal ((a:ℝ) * ((352/511:ℝ)/((a:ℝ)-5/4))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg a), ENNReal.ofReal_natCast]
    _ < _ := by
      have ht := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 3/4)).mpr hr
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)] at ht
      norm_num at ht ⊢
      exact ht

/-- An explicit infinite progression of actual joint deficits, requiring no
periodicity hypothesis, numerical search or cutoff. -/
theorem paired_twoStepMass_progression (t : ℕ) :
    ((31+54*t:ℕ):ℝ≥0∞) *
      (twoStepMass true (31+54*t) + twoStepMass false (31+54*t)) < 3/4 := by
  apply paired_twoStepMass_lt (by omega)
  · rw [Nat.odd_iff]; omega
  · omega

end Problems.Collatz.FibreSignCoupling
