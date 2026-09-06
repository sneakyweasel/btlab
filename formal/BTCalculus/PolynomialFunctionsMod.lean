import BTCalculus.Quadratic

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Polynomial functions modulo ``3^k``.

Finite-horizon residual equivalence of ordinary ``ℤ[X]`` polynomials is
function congruence on ``ℤ``:

  ``f ≡_k g ↔ ∀ n, 3^k ∣ f(n) - g(n)``.

Degree ``≤ 2`` recovers coefficient residues because ``2`` is a unit.
Degree ``3`` is strictly larger: ``X^3 - X`` vanishes modulo ``3`` without
coefficientwise divisibility. The first residual merges of ``X^3`` and
``X^4`` are instances of this kernel.
-/

/-- ``f`` and ``g`` agree as functions ``ℤ → ℤ/3^kℤ``. -/
def functionCongr (k : ℕ) (f g : ℤ[X]) : Prop :=
  ∀ n : ℤ, (3 : ℤ) ^ k ∣ eval n f - eval n g

/-- ``h`` is the zero function modulo ``3^k``. -/
def vanishesMod (k : ℕ) (h : ℤ[X]) : Prop :=
  ∀ n : ℤ, (3 : ℤ) ^ k ∣ eval n h

/-- `f` and `g` agree as functions mod `3^k` exactly when `f - g` vanishes mod `3^k`. -/
theorem functionCongr_iff_vanishesMod (k : ℕ) (f g : ℤ[X]) :
    functionCongr k f g ↔ vanishesMod k (f - g) := by
  constructor
  · intro h n
    simpa [eval_sub] using h n
  · intro h n
    simpa [eval_sub] using h n

/-- Evaluation respects congruence: `a = b [ZMOD m]` gives `eval a f = eval b f [ZMOD m]`. -/
lemma eval_modEq (f : ℤ[X]) {a b m : ℤ} (h : a ≡ b [ZMOD m]) :
    eval a f ≡ eval b f [ZMOD m] := by
  refine f.induction_on' (fun p q hp hq => ?_) (fun n c => ?_)
  · simpa [eval_add] using hp.add hq
  · simpa [eval_monomial] using (Int.ModEq.refl c).mul (h.pow n)

/-- `n = packWord (integerJet k n) + 3^k * iterDZ k n` -- jet plus tail. -/
lemma packWord_integerJet_decomp (k : ℕ) (n : ℤ) :
    n = packWord (integerJet k n) + (3 : ℤ) ^ k * iterDZ k n := by
  have h := packTrits_integerJet k n
  rw [packTrits_eq, integerJet_length] at h
  linarith

/-- `n` is congruent to its packed jet modulo `3^k`. -/
lemma packWord_integerJet_modEq (k : ℕ) (n : ℤ) :
    n ≡ packWord (integerJet k n) [ZMOD (3 : ℤ) ^ k] := by
  refine Int.modEq_iff_dvd.mpr ⟨-iterDZ k n, ?_⟩
  have h := packWord_integerJet_decomp k n
  linarith

/-- Prefix locality plus congruence preservation: ``≡_k`` is function
congruence on all of ``ℤ``. Packed length-``k`` prefixes are a complete
residue system modulo ``3^k``. -/
theorem equivK_iff_functionCongr (k : ℕ) (f g : ℤ[X]) :
    equivK k f g ↔ functionCongr k f g := by
  constructor
  · intro h n
    set w := integerJet k n
    have hw : isTritList w := isTritList_integerJet k n
    have hlen : w.length = k := integerJet_length k n
    have hout := (equivK_iff_outputs k f g).1 h w hlen hw
    rw [outputAlong_word f hw, outputAlong_word g hw, hlen] at hout
    have hpack := (integerJet_eq_iff_dvd k (eval (packWord w) f)
        (eval (packWord w) g)).1 hout
    have hcong := packWord_integerJet_modEq k n
    have df := Int.modEq_iff_dvd.mp (eval_modEq f hcong)
    have dg := Int.modEq_iff_dvd.mp (eval_modEq g hcong)
    have dfn : (3 : ℤ) ^ k ∣ eval n f - eval (packWord w) f := by
      simpa [neg_sub] using df.neg_right
    have dgn : (3 : ℤ) ^ k ∣ eval n g - eval (packWord w) g := by
      simpa [neg_sub] using dg.neg_right
    have hexp :
        eval n f - eval n g =
          (eval n f - eval (packWord w) f)
            - (eval n g - eval (packWord w) g)
            + (eval (packWord w) f - eval (packWord w) g) := by ring
    rw [hexp]
    exact (dfn.sub dgn).add hpack
  · intro h
    refine (equivK_iff_outputs k f g).2 ?_
    intro w hlen hw
    rw [outputAlong_word f hw, outputAlong_word g hw, hlen]
    exact (integerJet_eq_iff_dvd k _ _).2 (h (packWord w))

/-- The zero quadratic is the zero polynomial. -/
theorem quad_zero : quad 0 0 0 = (0 : ℤ[X]) := by
  unfold quad
  simp

/-- Degree ``≤ 2``: vanishing as a function modulo ``3^k`` is
coefficientwise divisibility. Probes ``0, 1, -1`` recover the
coefficients because ``2`` is a unit modulo ``3^k``. -/
theorem vanishesMod_quad_iff (k : ℕ) (A B c0 : ℤ) :
    vanishesMod k (quad A B c0) ↔
      (3 : ℤ) ^ k ∣ A ∧ (3 : ℤ) ^ k ∣ B ∧ (3 : ℤ) ^ k ∣ c0 := by
  have hfun :
      functionCongr k (quad A B c0) (quad 0 0 0) ↔ vanishesMod k (quad A B c0) := by
    constructor
    · intro h n
      simpa [quad_zero, eval_zero] using h n
    · intro h n
      simpa [quad_zero, eval_zero] using h n
  constructor
  · intro h
    have heq := (equivK_iff_functionCongr k (quad A B c0) (quad 0 0 0)).2 (hfun.2 h)
    simpa using (equivK_quad k A B c0 0 0 0).1 heq
  · intro ⟨hA, hB, hC⟩
    have hA0 : (3 : ℤ) ^ k ∣ A - 0 := by simpa using hA
    have hB0 : (3 : ℤ) ^ k ∣ B - 0 := by simpa using hB
    have hC0 : (3 : ℤ) ^ k ∣ c0 - 0 := by simpa using hC
    exact hfun.1
      ((equivK_iff_functionCongr k (quad A B c0) (quad 0 0 0)).1
        ((equivK_quad k A B c0 0 0 0).2 ⟨hA0, hB0, hC0⟩))

def cubic (A B lin cst : ℤ) : ℤ[X] :=
  C A * X ^ 3 + C B * X ^ 2 + C lin * X + C cst

/-- `eval x (cubic A B lin cst) = A x^3 + B x^2 + lin x + cst`. -/
theorem eval_cubic (A B lin cst x : ℤ) :
    eval x (cubic A B lin cst) = A * x ^ 3 + B * x ^ 2 + lin * x + cst := by
  unfold cubic
  simp [eval_add, eval_mul, eval_C, eval_pow, eval_X, mul_comm, mul_left_comm, mul_assoc]

/-- Newton (falling-factorial) form of a cubic: `cst + (A+B+lin) x + (3A+B) x(x-1) + A x(x-1)(x-2)`. -/
theorem cubic_newton_eval (A B lin cst x : ℤ) :
    eval x (cubic A B lin cst) =
      cst + (A + B + lin) * x + (3 * A + B) * x * (x - 1)
        + A * x * (x - 1) * (x - 2) := by
  rw [eval_cubic]
  ring

/-- `2 | x (x - 1)`. -/
lemma two_dvd_x_mul_pred (x : ℤ) : (2 : ℤ) ∣ x * (x - 1) := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx
  · exact dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr hx) _
  · have : (x - 1) % 2 = 0 := by omega
    exact dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr this) _

/-- `3 | x (x - 1)(x - 2)`. -/
lemma three_dvd_falling_three (x : ℤ) :
    (3 : ℤ) ∣ x * (x - 1) * (x - 2) := by
  rcases emod3_cases x with hx | hx | hx
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr hx) _) _
  · have : (x - 1) % 3 = 0 := by omega
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr this) _) _
  · have : (x - 2) % 3 = 0 := by omega
    exact dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr this) _

/-- `6 | x (x - 1)(x - 2)`. -/
lemma six_dvd_falling_three (x : ℤ) :
    (6 : ℤ) ∣ x * (x - 1) * (x - 2) := by
  have h2 : (2 : ℤ) ∣ x * (x - 1) * (x - 2) :=
    dvd_mul_of_dvd_left (two_dvd_x_mul_pred x) _
  have h3 := three_dvd_falling_three x
  have hcop : IsCoprime (2 : ℤ) (3 : ℤ) := ⟨-1, 1, by decide⟩
  simpa using hcop.mul_dvd h2 h3

/-- Degree-3 vanishing criterion. The condition ``3^k ∣ 6A`` is strictly
weaker than ``3^k ∣ A``; this is the first higher-degree obstruction. -/
theorem vanishesMod_cubic_iff (k : ℕ) (A B lin cst : ℤ) :
    vanishesMod k (cubic A B lin cst) ↔
      (3 : ℤ) ^ k ∣ cst ∧
        (3 : ℤ) ^ k ∣ A + B + lin ∧
          (3 : ℤ) ^ k ∣ 3 * A + B ∧
            (3 : ℤ) ^ k ∣ 6 * A := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    rw [eval_cubic] at h0 h1 h2 h3
    have hcst : (3 : ℤ) ^ k ∣ cst := by simpa using h0
    have hsum : (3 : ℤ) ^ k ∣ A + B + lin := by
      simpa [add_sub_cancel_right] using dvd_sub h1 h0
    have hΔ2 : (3 : ℤ) ^ k ∣ 6 * A + 2 * B := by
      have h := (dvd_sub h2 (dvd_mul_of_dvd_right h1 (2 : ℤ))).add h0
      have heq :
          A * 8 + B * 4 + lin * 2 + cst - 2 * (A + B + lin + cst) + cst =
            6 * A + 2 * B := by
        omega
      simpa [heq] using h
    have hΔ3 : (3 : ℤ) ^ k ∣ 6 * A := by
      have h :=
        ((dvd_sub h3 (dvd_mul_of_dvd_right h2 (3 : ℤ))).add
            (dvd_mul_of_dvd_right h1 (3 : ℤ))).sub
          h0
      have heq :
          A * 27 + B * 9 + lin * 3 + cst - 3 * (A * 8 + B * 4 + lin * 2 + cst) +
              3 * (A + B + lin + cst) - cst =
            6 * A := by
        omega
      simpa [heq] using h
    have hmid : (3 : ℤ) ^ k ∣ 3 * A + B := by
      have h2mid : (3 : ℤ) ^ k ∣ 2 * (3 * A + B) := by
        have heq : 2 * (3 * A + B) = 6 * A + 2 * B := by omega
        simpa [heq] using hΔ2
      exact three_pow_dvd_of_two_mul h2mid
    exact ⟨hcst, hsum, hmid, hΔ3⟩
  · intro ⟨hcst, hsum, hmid, h6⟩
    intro x
    obtain ⟨qF, hF⟩ := six_dvd_falling_three x
    have hAf : A * (x * (x - 1) * (x - 2)) = (6 * A) * qF := by
      have : x * (x - 1) * (x - 2) = 6 * qF := hF
      rw [this]
      ring
    obtain ⟨qD, hD⟩ := hcst
    obtain ⟨q1, h1⟩ := hsum
    obtain ⟨q2, h2⟩ := hmid
    obtain ⟨q6, h6e⟩ := h6
    refine ⟨qD + q1 * x + q2 * x * (x - 1) + q6 * qF, ?_⟩
    have hfall : A * x * (x - 1) * (x - 2) = (6 * A) * qF := by
      convert hAf using 1
      ring
    rw [cubic_newton_eval, hD, h1, h2, hfall, h6e]
    ring

/-- `3 | x^3 - x` (Fermat at `3`). -/
theorem three_dvd_x_pow_three_sub_x (x : ℤ) : (3 : ℤ) ∣ x ^ 3 - x := by
  have hexp : x ^ 3 - x = x * (x - 1) * (x + 1) := by ring
  rw [hexp]
  rcases emod3_cases x with hx | hx | hx
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr hx) _) _
  · have : (x - 1) % 3 = 0 := by omega
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr this) _) _
  · have : (x + 1) % 3 = 0 := by omega
    exact dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr this) _

/-- The first invisible cubic: ``X^3 - X`` vanishes modulo ``3``, but its
leading coefficient is a unit. -/
theorem X_pow_three_sub_X_vanishes_one :
    vanishesMod 1 ((X : ℤ[X]) ^ 3 - X) := by
  intro n
  simpa [eval_sub, eval_pow, eval_X] using three_dvd_x_pow_three_sub_x n

/-- `X^3 - X` vanishes as a function mod `3` while its degree-3 coefficient does not: vanishing is not coefficientwise. -/
theorem not_three_dvd_coeff_X_pow_three_sub_X :
    ¬ (3 : ℤ) ∣ coeff ((X : ℤ[X]) ^ 3 - X) 3 := by
  have h : coeff ((X : ℤ[X]) ^ 3 - X) 3 = 1 := by
    simp [coeff_sub, coeff_X_pow, coeff_X]
  rw [h]
  decide

/-- `X^3 - X = cubic 1 0 (-1) 0`. -/
theorem X_pow_three_sub_X_eq_cubic :
    (X : ℤ[X]) ^ 3 - X = cubic 1 0 (-1) 0 := by
  unfold cubic
  simp
  ring

/-- `X^3 - X` does not vanish mod `9`. -/
theorem X_pow_three_sub_X_not_vanishes_two :
    ¬ vanishesMod 2 ((X : ℤ[X]) ^ 3 - X) := by
  intro h
  have hc := (vanishesMod_cubic_iff 2 1 0 (-1) 0).1
    (by simpa [X_pow_three_sub_X_eq_cubic] using h)
  have : ¬ (9 : ℤ) ∣ (6 : ℤ) := by decide
  exact this hc.2.2.2

/-- `eval x (X^3) = x^3`. -/
theorem eval_X_pow_three (x : ℤ) : eval x ((X : ℤ[X]) ^ 3) = x ^ 3 := by
  simp [eval_pow, eval_X]

/-- Pointwise section derivative of `X^3` at `a`. -/
theorem eval_sectionDeriv_X_pow_three (a x : ℤ) :
    eval x (sectionDeriv a ((X : ℤ[X]) ^ 3)) =
      DZ (a ^ 3) + 3 * a ^ 2 * x + 9 * a * x ^ 2 + 9 * x ^ 3 := by
  have hrec := section_reconstruction_eval ((X : ℤ[X]) ^ 3) a x
  have hf := eval_X_pow_three (a + 3 * x)
  have ha := eval_X_pow_three a
  have hd : a ^ 3 = lsdZ (a ^ 3) + 3 * DZ (a ^ 3) := decomp (a ^ 3)
  have hexpand :
      (a + 3 * x) ^ 3 =
        a ^ 3 + 3 * (3 * a ^ 2 * x + 9 * a * x ^ 2 + 9 * x ^ 3) := by ring
  have h3 :
      3 * eval x (sectionDeriv a ((X : ℤ[X]) ^ 3)) =
        3 * (DZ (a ^ 3) + 3 * a ^ 2 * x + 9 * a * x ^ 2 + 9 * x ^ 3) := by
    rw [hf, ha] at hrec
    linarith [hrec, hexpand, hd]
  linarith

/-- `sectionDeriv a (X^3)` as a polynomial in `X`. -/
theorem sectionDeriv_X_pow_three (a : ℤ) :
    sectionDeriv a ((X : ℤ[X]) ^ 3) =
      C (DZ (a ^ 3)) + C (3 * a ^ 2) * X + C (9 * a) * X ^ 2 + C 9 * X ^ 3 := by
  refine Polynomial.funext (fun x => ?_)
  have hL := eval_sectionDeriv_X_pow_three a x
  have hR :
      eval x (C (DZ (a ^ 3)) + C (3 * a ^ 2) * X + C (9 * a) * X ^ 2 + C 9 * X ^ 3) =
        DZ (a ^ 3) + 3 * a ^ 2 * x + 9 * a * x ^ 2 + 9 * x ^ 3 := by
    simp [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  exact hL.trans hR.symm

/-- `D (-1) = 0`. -/
theorem DZ_neg_one : DZ (-1) = 0 := by
  decide

/-- `D 1 = 0`. -/
theorem DZ_one : DZ 1 = 0 := by
  decide

/-- Residual of `X^3` along the letter `-1`. -/
theorem residual_X_pow_three_neg :
    residualAlong [(-1 : ℤ)] ((X : ℤ[X]) ^ 3) =
      C 9 * X ^ 3 + C (-9) * X ^ 2 + C 3 * X := by
  have hrw : residualAlong [(-1 : ℤ)] ((X : ℤ[X]) ^ 3) =
      sectionDeriv (-1) ((X : ℤ[X]) ^ 3) := rfl
  rw [hrw, sectionDeriv_X_pow_three]
  have hp : (-1 : ℤ) ^ 3 = -1 := by decide
  rw [hp, DZ_neg_one]
  simp
  ring

/-- Residual of `X^3` along the letter `1`. -/
theorem residual_X_pow_three_pos :
    residualAlong [(1 : ℤ)] ((X : ℤ[X]) ^ 3) =
      C 9 * X ^ 3 + C 9 * X ^ 2 + C 3 * X := by
  rw [show residualAlong [(1 : ℤ)] ((X : ℤ[X]) ^ 3) =
      sectionDeriv 1 ((X : ℤ[X]) ^ 3) from rfl]
  rw [sectionDeriv_X_pow_three, show (1 : ℤ) ^ 3 = 1 by decide, DZ_one]
  simp
  ring

/-- The two `X^3` residuals differ by `-18 x^2`, which is why they merge at `k = 2` and not at `k = 3`. -/
theorem x3_merge_eval_diff (x : ℤ) :
    eval x (residualAlong [(-1 : ℤ)] ((X : ℤ[X]) ^ 3))
      - eval x (residualAlong [(1 : ℤ)] ((X : ℤ[X]) ^ 3)) =
      -18 * x ^ 2 := by
  rw [residual_X_pow_three_neg, residual_X_pow_three_pos]
  simp [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- First ``x^3`` residual merge: the sign of a length-1 prefix is
invisible at horizon ``2`` because the difference is ``-18 x^2``. -/
theorem x3_first_merge_equiv_two :
    equivK 2
      (residualAlong [(-1 : ℤ)] ((X : ℤ[X]) ^ 3))
      (residualAlong [(1 : ℤ)] ((X : ℤ[X]) ^ 3)) := by
  refine (equivK_iff_functionCongr 2 _ _).2 ?_
  intro n
  have h := x3_merge_eval_diff n
  have : (3 : ℤ) ^ 2 ∣ -18 * n ^ 2 := ⟨-2 * n ^ 2, by ring⟩
  simpa [h] using this

/-- The two `X^3` residuals are not equivalent at horizon `3`. -/
theorem x3_first_merge_not_equiv_three :
    ¬ equivK 3
        (residualAlong [(-1 : ℤ)] ((X : ℤ[X]) ^ 3))
        (residualAlong [(1 : ℤ)] ((X : ℤ[X]) ^ 3)) := by
  intro h
  have hf := (equivK_iff_functionCongr 3 _ _).1 h 1
  have hd := x3_merge_eval_diff 1
  have : eval (1 : ℤ)
        (residualAlong [(-1 : ℤ)] ((X : ℤ[X]) ^ 3))
        - eval 1 (residualAlong [(1 : ℤ)] ((X : ℤ[X]) ^ 3)) =
      -18 := by
    simpa using hd
  rw [this] at hf
  have : ¬ (27 : ℤ) ∣ (-18 : ℤ) := by decide
  exact this hf

/-- `eval x (X^4) = x^4`. -/
theorem eval_X_pow_four (x : ℤ) : eval x ((X : ℤ[X]) ^ 4) = x ^ 4 := by
  simp [eval_pow, eval_X]

/-- `lsd 0 = 0`. -/
theorem lsdZ_zero : lsdZ 0 = 0 := by
  simp [lsdZ]

/-- `eval x (sectionDeriv 0 (X^4)) = 27 x^4`. -/
theorem eval_sectionDeriv_X_pow_four_zero (x : ℤ) :
    eval x (sectionDeriv 0 ((X : ℤ[X]) ^ 4)) = 27 * x ^ 4 := by
  have hrec := section_reconstruction_eval ((X : ℤ[X]) ^ 4) 0 x
  rw [eval_X_pow_four, eval_X_pow_four] at hrec
  have hz : (0 : ℤ) ^ 4 = 0 := by decide
  rw [hz, lsdZ_zero] at hrec
  have hexp : (0 + 3 * x) ^ 4 = 81 * x ^ 4 := by ring
  have : 3 * eval x (sectionDeriv 0 ((X : ℤ[X]) ^ 4)) = 3 * (27 * x ^ 4) := by
    linarith [hrec, hexp]
  linarith

/-- Residual of `X^4` along `[0]` is `27 X^4`. -/
theorem residual_X_pow_four_zero :
    residualAlong [(0 : ℤ)] ((X : ℤ[X]) ^ 4) = C 27 * X ^ 4 := by
  refine Polynomial.funext (fun x => ?_)
  have hL := eval_sectionDeriv_X_pow_four_zero x
  have hR : eval x (C (27 : ℤ) * X ^ 4) = 27 * x ^ 4 := by
    simp [eval_mul, eval_C, eval_pow, eval_X]
  have hrw : residualAlong [(0 : ℤ)] ((X : ℤ[X]) ^ 4) =
      sectionDeriv 0 ((X : ℤ[X]) ^ 4) := rfl
  rw [hrw, hL, hR]

/-- `eval x (sectionDeriv 0 (27 X^4)) = 729 x^4`. -/
theorem eval_sectionDeriv_27_X_pow_four_zero (x : ℤ) :
    eval x (sectionDeriv 0 (C (27 : ℤ) * X ^ 4)) = 729 * x ^ 4 := by
  have hrec := section_reconstruction_eval (C (27 : ℤ) * X ^ 4) 0 x
  have hf : eval (0 + 3 * x) (C (27 : ℤ) * X ^ 4) = 27 * (3 * x) ^ 4 := by
    simp [eval_mul, eval_C, eval_pow, eval_X]
  have ha : eval 0 (C (27 : ℤ) * X ^ 4) = 0 := by
    simp [eval_mul, eval_C, eval_pow, eval_X]
  have hexp : 27 * (3 * x) ^ 4 = 2187 * x ^ 4 := by ring
  rw [hf, ha, lsdZ_zero] at hrec
  have : 3 * eval x (sectionDeriv 0 (C (27 : ℤ) * X ^ 4)) = 3 * (729 * x ^ 4) := by
    linarith [hrec, hexp]
  linarith

/-- Residual of `X^4` along `[0, 0]` is `729 X^4`. -/
theorem residual_X_pow_four_zero_zero :
    residualAlong [(0 : ℤ), 0] ((X : ℤ[X]) ^ 4) = C 729 * X ^ 4 := by
  refine Polynomial.funext (fun x => ?_)
  have hsd : residualAlong [(0 : ℤ), 0] ((X : ℤ[X]) ^ 4) =
      sectionDeriv 0 (sectionDeriv 0 ((X : ℤ[X]) ^ 4)) := by
    simp [residualAlong]
  have h27 : sectionDeriv 0 ((X : ℤ[X]) ^ 4) = C 27 * X ^ 4 := by
    simpa [residualAlong] using residual_X_pow_four_zero
  have hL := eval_sectionDeriv_27_X_pow_four_zero x
  have hR : eval x (C (729 : ℤ) * X ^ 4) = 729 * x ^ 4 := by
    simp [eval_mul, eval_C, eval_pow, eval_X]
  rw [hsd, h27, hL, hR]

/-- The two `X^4` residuals differ by `-702 x^4`, which places the merge at `k = 3`. -/
theorem x4_merge_eval_diff (x : ℤ) :
    eval x (residualAlong [(0 : ℤ)] ((X : ℤ[X]) ^ 4))
      - eval x (residualAlong [(0 : ℤ), 0] ((X : ℤ[X]) ^ 4)) =
      -702 * x ^ 4 := by
  rw [residual_X_pow_four_zero, residual_X_pow_four_zero_zero]
  simp [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- First ``x^4`` residual merge: ``27 x^4`` and ``729 x^4`` agree as
functions through horizon ``3``. -/
theorem x4_first_merge_equiv_three :
    equivK 3
      (residualAlong [(0 : ℤ)] ((X : ℤ[X]) ^ 4))
      (residualAlong [(0 : ℤ), 0] ((X : ℤ[X]) ^ 4)) := by
  refine (equivK_iff_functionCongr 3 _ _).2 ?_
  intro n
  have h := x4_merge_eval_diff n
  have : (3 : ℤ) ^ 3 ∣ -702 * n ^ 4 := ⟨-26 * n ^ 4, by ring⟩
  simpa [h] using this

/-- The two `X^4` residuals are not equivalent at horizon `4`. -/
theorem x4_first_merge_not_equiv_four :
    ¬ equivK 4
        (residualAlong [(0 : ℤ)] ((X : ℤ[X]) ^ 4))
        (residualAlong [(0 : ℤ), 0] ((X : ℤ[X]) ^ 4)) := by
  intro h
  have hf := (equivK_iff_functionCongr 4 _ _).1 h 1
  have hd := x4_merge_eval_diff 1
  have : eval (1 : ℤ)
        (residualAlong [(0 : ℤ)] ((X : ℤ[X]) ^ 4))
        - eval 1 (residualAlong [(0 : ℤ), 0] ((X : ℤ[X]) ^ 4)) =
      -702 := by
    simpa using hd
  rw [this] at hf
  have : ¬ (81 : ℤ) ∣ (-702 : ℤ) := by decide
  exact this hf

end BTCalculus
