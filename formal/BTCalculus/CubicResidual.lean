import BTCalculus.PolynomialFunctionsMod

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Newton-class image of the residual machine of ``X^3``.

Along an LSD-first trit word ``w`` of length ``m`` with packed prefix
``p = packWord w``,

  ``𝔇_w(X^3) = 3^{2m} X^3 + 3^{m+1} p X^2 + 3 p^2 X + iterDZ m (p^3)``.

Finite-horizon equivalence of cubics is Newton-residue agreement
modulo ``3^k``. The first ``X^3`` merge is the sign pair at depth 1.
-/

def cubicResid (m : ℕ) (p : ℤ) : ℤ[X] :=
  cubic ((3 : ℤ) ^ (2 * m)) ((3 : ℤ) ^ (m + 1) * p) (3 * p ^ 2) (iterDZ m (p ^ 3))

def newtonCoords (A B lin cst : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (cst, A + B + lin, 6 * A + 2 * B, 6 * A)

/-- The residual family in closed form: `eval x (cubicResid m p) = 3^(2m) x^3 + 3^(m+1) p x^2 + 3 p^2 x + D^m (p^3)`. -/
theorem eval_cubicResid (m : ℕ) (p x : ℤ) :
    eval x (cubicResid m p) =
      (3 : ℤ) ^ (2 * m) * x ^ 3 + (3 : ℤ) ^ (m + 1) * p * x ^ 2
        + 3 * p ^ 2 * x + iterDZ m (p ^ 3) := by
  unfold cubicResid
  rw [eval_cubic]

/-- `X^3 = cubic 1 0 0 0`. -/
theorem X_pow_three_eq_cubic : (X : ℤ[X]) ^ 3 = cubic 1 0 0 0 := by
  unfold cubic
  simp

/-- `cubicResid 0 0 = X^3` -- the family starts at the cube. -/
theorem cubicResid_zero : cubicResid 0 0 = (X : ℤ[X]) ^ 3 := by
  unfold cubicResid
  simp [iterDZ, pow_zero, X_pow_three_eq_cubic]

/-- Constant coefficient of `cubic A B lin cst` is `cst`. -/
theorem coeff_cubic_zero (A B lin cst : ℤ) : coeff (cubic A B lin cst) 0 = cst := by
  unfold cubic
  rw [coeff_add, coeff_add, coeff_add]
  have hX3 : coeff (C A * X ^ 3) 0 = 0 := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX2 : coeff (C B * X ^ 2) 0 = 0 := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX : coeff (C lin * X) 0 = 0 := by
    rw [coeff_C_mul, coeff_X]; simp
  have hC : coeff (C cst) 0 = cst := by
    rw [coeff_C]; simp
  rw [hX3, hX2, hX, hC]
  simp

/-- Linear coefficient of `cubic A B lin cst` is `lin`. -/
theorem coeff_cubic_one (A B lin cst : ℤ) : coeff (cubic A B lin cst) 1 = lin := by
  unfold cubic
  rw [coeff_add, coeff_add, coeff_add]
  have hX3 : coeff (C A * X ^ 3) 1 = 0 := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX2 : coeff (C B * X ^ 2) 1 = 0 := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX : coeff (C lin * X) 1 = lin := by
    rw [coeff_C_mul, coeff_X]; simp
  have hC : coeff (C cst) 1 = 0 := by
    rw [coeff_C]; simp
  rw [hX3, hX2, hX, hC]
  simp

/-- Quadratic coefficient of `cubic A B lin cst` is `B`. -/
theorem coeff_cubic_two (A B lin cst : ℤ) : coeff (cubic A B lin cst) 2 = B := by
  unfold cubic
  rw [coeff_add, coeff_add, coeff_add]
  have hX3 : coeff (C A * X ^ 3) 2 = 0 := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX2 : coeff (C B * X ^ 2) 2 = B := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX : coeff (C lin * X) 2 = 0 := by
    rw [coeff_C_mul, coeff_X]; simp
  have hC : coeff (C cst) 2 = 0 := by
    rw [coeff_C]; simp
  rw [hX3, hX2, hX, hC]
  simp

/-- Cubic coefficient of `cubic A B lin cst` is `A`. -/
theorem coeff_cubic_three (A B lin cst : ℤ) : coeff (cubic A B lin cst) 3 = A := by
  unfold cubic
  rw [coeff_add, coeff_add, coeff_add]
  have hX3 : coeff (C A * X ^ 3) 3 = A := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX2 : coeff (C B * X ^ 2) 3 = 0 := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX : coeff (C lin * X) 3 = 0 := by
    rw [coeff_C_mul, coeff_X]; simp
  have hC : coeff (C cst) 3 = 0 := by
    rw [coeff_C]; simp
  rw [hX3, hX2, hX, hC]
  simp

/-- `cubic` is injective in its four coefficients. -/
theorem cubic_inj {A B lin cst A' B' lin' cst' : ℤ}
    (h : cubic A B lin cst = cubic A' B' lin' cst') :
    A = A' ∧ B = B' ∧ lin = lin' ∧ cst = cst' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [coeff_cubic_three] using congrArg (fun p => coeff p 3) h
  · simpa [coeff_cubic_two] using congrArg (fun p => coeff p 2) h
  · simpa [coeff_cubic_one] using congrArg (fun p => coeff p 1) h
  · simpa [coeff_cubic_zero] using congrArg (fun p => coeff p 0) h

/-- `cubic` subtracts coefficientwise. -/
theorem cubic_sub (A B lin cst A' B' lin' cst' : ℤ) :
    cubic A B lin cst - cubic A' B' lin' cst' =
      cubic (A - A') (B - B') (lin - lin') (cst - cst') := by
  refine Polynomial.funext (fun x => ?_)
  simp [eval_sub, eval_cubic]
  ring

/-- Cube of a lifted point: `(p + 3^m a)^3` split into `p^3` plus a `3^m`-multiple. -/
theorem cubic_cube_split (m : ℕ) (p a : ℤ) :
    (p + (3 : ℤ) ^ m * a) ^ 3 =
      p ^ 3 + (3 : ℤ) ^ m *
        (3 * p ^ 2 * a + (3 : ℤ) ^ (m + 1) * p * a ^ 2 + (3 : ℤ) ^ (2 * m) * a ^ 3) := by
  ring

/-- `eval a (cubicResid m p) = D^m ((p + 3^m a)^3)` -- the family is the iterated residual of a cube. -/
theorem eval_cubicResid_iter (m : ℕ) (p a : ℤ) :
    eval a (cubicResid m p) = iterDZ m ((p + (3 : ℤ) ^ m * a) ^ 3) := by
  have hsplit := cubic_cube_split m p a
  have hiter :=
    iterDZ_add_pow m (p ^ 3)
      (3 * p ^ 2 * a + (3 : ℤ) ^ (m + 1) * p * a ^ 2 + (3 : ℤ) ^ (2 * m) * a ^ 3)
  rw [eval_cubicResid, hsplit, hiter]
  ring

/-- Pointwise section derivative of a cubic at `a`. -/
theorem eval_sectionDeriv_cubic (A B lin cst a x : ℤ) :
    eval x (sectionDeriv a (cubic A B lin cst)) =
      9 * A * x ^ 3 + (9 * A * a + 3 * B) * x ^ 2
        + (3 * A * a ^ 2 + 2 * B * a + lin) * x
        + DZ (A * a ^ 3 + B * a ^ 2 + lin * a + cst) := by
  have hrec := section_reconstruction_eval (cubic A B lin cst) a x
  have hf := eval_cubic A B lin cst (a + 3 * x)
  have ha := eval_cubic A B lin cst a
  set n := A * a ^ 3 + B * a ^ 2 + lin * a + cst
  have hd : n = lsdZ n + 3 * DZ n := decomp n
  have hexpand :
      A * (a + 3 * x) ^ 3 + B * (a + 3 * x) ^ 2 + lin * (a + 3 * x) + cst =
        n + 3 * (9 * A * x ^ 3 + (9 * A * a + 3 * B) * x ^ 2
          + (3 * A * a ^ 2 + 2 * B * a + lin) * x) := by
    ring
  have hdecomp' :
      n + 3 * (9 * A * x ^ 3 + (9 * A * a + 3 * B) * x ^ 2
          + (3 * A * a ^ 2 + 2 * B * a + lin) * x) =
        lsdZ n + 3 * (9 * A * x ^ 3 + (9 * A * a + 3 * B) * x ^ 2
          + (3 * A * a ^ 2 + 2 * B * a + lin) * x + DZ n) := by
    conv_lhs => rw [hd]
    ring
  have hexp := hexpand.trans hdecomp'
  have h3 :
      3 * eval x (sectionDeriv a (cubic A B lin cst)) =
        3 * (9 * A * x ^ 3 + (9 * A * a + 3 * B) * x ^ 2
          + (3 * A * a ^ 2 + 2 * B * a + lin) * x + DZ n) := by
    rw [hf, ha] at hrec
    linarith [hrec, hexp]
  linarith

/-- The section derivative of a cubic is again a cubic, with the stated coefficients. -/
theorem sectionDeriv_cubic (A B lin cst a : ℤ) :
    sectionDeriv a (cubic A B lin cst) =
      cubic (9 * A) (9 * A * a + 3 * B)
        (3 * A * a ^ 2 + 2 * B * a + lin)
        (DZ (A * a ^ 3 + B * a ^ 2 + lin * a + cst)) := by
  refine Polynomial.funext (fun x => ?_)
  have hL := eval_sectionDeriv_cubic A B lin cst a x
  have hR :=
    eval_cubic (9 * A) (9 * A * a + 3 * B)
      (3 * A * a ^ 2 + 2 * B * a + lin)
      (DZ (A * a ^ 3 + B * a ^ 2 + lin * a + cst)) x
  linarith

/-- One more `D` on the family advances the iterate: `D (eval a (cubicResid m p)) = D^(m+1) ((p + 3^m a)^3)`. -/
theorem C_step_cubic (m : ℕ) (p a : ℤ) :
    DZ (eval a (cubicResid m p)) =
      iterDZ (m + 1) ((p + (3 : ℤ) ^ m * a) ^ 3) := by
  rw [eval_cubicResid_iter, iterDZ_succ_right]

/-- The family is closed under the section derivative: `sectionDeriv a (cubicResid m p) = cubicResid (m+1) (p + 3^m a)`. -/
theorem sectionDeriv_cubicResid (m : ℕ) (p a : ℤ) :
    sectionDeriv a (cubicResid m p) =
      cubicResid (m + 1) (p + (3 : ℤ) ^ m * a) := by
  have hA : 9 * (3 : ℤ) ^ (2 * m) = (3 : ℤ) ^ (2 * (m + 1)) := by
    have h : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h, pow_add, pow_two]
    ring
  have hB : 9 * (3 : ℤ) ^ (2 * m) * a + 3 * ((3 : ℤ) ^ (m + 1) * p) =
      (3 : ℤ) ^ (m + 1 + 1) * (p + (3 : ℤ) ^ m * a) := by
    rw [pow_succ]
    ring
  have hlin :
      3 * (3 : ℤ) ^ (2 * m) * a ^ 2 + 2 * ((3 : ℤ) ^ (m + 1) * p) * a + 3 * p ^ 2 =
        3 * (p + (3 : ℤ) ^ m * a) ^ 2 := by
    ring
  have hstep :=
    sectionDeriv_cubic ((3 : ℤ) ^ (2 * m)) ((3 : ℤ) ^ (m + 1) * p)
      (3 * p ^ 2) (iterDZ m (p ^ 3)) a
  have hval :
      (3 : ℤ) ^ (2 * m) * a ^ 3 + ((3 : ℤ) ^ (m + 1) * p) * a ^ 2
        + (3 * p ^ 2) * a + iterDZ m (p ^ 3) =
      eval a (cubicResid m p) := by
    simp [eval_cubicResid]
  unfold cubicResid
  rw [hstep, hval, C_step_cubic m p a]
  exact congr (congr (congr (congrArg cubic hA) hB) hlin) rfl

/-- Along any trit word, the family advances by the word's length and packed value. -/
theorem residualAlong_cubic_family (m : ℕ) (p : ℤ) :
    ∀ {w : List ℤ}, isTritList w →
      residualAlong w (cubicResid m p) =
        cubicResid (m + w.length) (p + (3 : ℤ) ^ m * packWord w)
  | [], _ => by
    simp [residualAlong, packWord, packTrits]
  | a :: rest, hw => by
    have hsd := sectionDeriv_cubicResid m p a
    have ih := residualAlong_cubic_family (m + 1) (p + (3 : ℤ) ^ m * a) hw.2
    rw [residualAlong_cons, hsd, ih]
    simp [packWord_cons, List.length_cons]
    congr 1
    · ac_rfl
    · ring

/-- Residuals of `X^3` are exactly the family: `residualAlong w (X^3) = cubicResid |w| (packWord w)`. -/
theorem residualAlong_Xcube {w : List ℤ} (hw : isTritList w) :
    residualAlong w ((X : ℤ[X]) ^ 3) =
      cubicResid w.length (packWord w) := by
  have h := residualAlong_cubic_family 0 0 hw
  simpa [cubicResid_zero, pow_zero] using h

/-- Distinct trit words give distinct residuals of `X^3`. -/
theorem residualAlong_Xcube_injective {w v : List ℤ}
    (hw : isTritList w) (hv : isTritList v)
    (h : residualAlong w ((X : ℤ[X]) ^ 3) = residualAlong v ((X : ℤ[X]) ^ 3)) :
    w = v := by
  have hf := residualAlong_Xcube hw
  have hg := residualAlong_Xcube hv
  rw [hf, hg] at h
  obtain ⟨hA, hB, _, _⟩ := cubic_inj h
  have hlen : w.length = v.length := by
    have hAbs := congrArg Int.natAbs hA
    rw [Int.natAbs_pow, Int.natAbs_pow] at hAbs
    have hpow : (3 : ℕ) ^ (2 * w.length) = (3 : ℕ) ^ (2 * v.length) := by
      simpa using hAbs
    have h2 : 2 * w.length = 2 * v.length :=
      Nat.pow_right_injective (by decide : (1 : ℕ) < 3) hpow
    omega
  have hp : packWord w = packWord v := by
    have hm : (3 : ℤ) ^ (w.length + 1) * packWord w =
        (3 : ℤ) ^ (v.length + 1) * packWord v := hB
    rw [hlen] at hm
    have hpow : (3 : ℤ) ^ (w.length + 1) ≠ 0 := pow_ne_zero _ (by decide)
    exact (mul_right_injective₀ hpow) (by simpa [hlen] using hm)
  exact packWord_injective hw hv hlen hp

/-- Newton coordinates of the residual family, written in terms of `m` and `p`. -/
theorem newton_cubicResid (m : ℕ) (p : ℤ) :
    newtonCoords ((3 : ℤ) ^ (2 * m)) ((3 : ℤ) ^ (m + 1) * p)
        (3 * p ^ 2) (iterDZ m (p ^ 3)) =
      (iterDZ m (p ^ 3),
        (3 : ℤ) ^ (2 * m) + (3 : ℤ) ^ (m + 1) * p + 3 * p ^ 2,
        2 * (3 : ℤ) ^ (m + 1) * (p + (3 : ℤ) ^ m),
        2 * (3 : ℤ) ^ (2 * m + 1)) := by
  unfold newtonCoords
  ring

/-- The section step scales the `N3` Newton coordinate by `9`. -/
theorem newton_section_N3 (A B lin : ℤ) (a : ℤ) :
    (newtonCoords (9 * A) (9 * A * a + 3 * B)
        (3 * A * a ^ 2 + 2 * B * a + lin) 0).2.2.2 =
      9 * (newtonCoords A B lin 0).2.2.2 := by
  unfold newtonCoords
  ring

/-- The section step sends `N2` to `3 N2 + 3(a + 2) N3`. -/
theorem newton_section_N2 (A B lin : ℤ) (a : ℤ) :
    (newtonCoords (9 * A) (9 * A * a + 3 * B)
        (3 * A * a ^ 2 + 2 * B * a + lin) 0).2.2.1 =
      3 * (newtonCoords A B lin 0).2.2.1
        + 3 * (a + 2) * (newtonCoords A B lin 0).2.2.2 := by
  unfold newtonCoords
  ring

/-- Finite-horizon equivalence of cubics is the cubic vanishing criterion
of the difference, hence Newton-residue agreement. -/
theorem equivK_cubic (k : ℕ) (A B lin cst A' B' lin' cst' : ℤ) :
    equivK k (cubic A B lin cst) (cubic A' B' lin' cst') ↔
      (3 : ℤ) ^ k ∣ cst - cst' ∧
        (3 : ℤ) ^ k ∣ (A + B + lin) - (A' + B' + lin') ∧
          (3 : ℤ) ^ k ∣ (3 * A + B) - (3 * A' + B') ∧
            (3 : ℤ) ^ k ∣ 6 * A - 6 * A' := by
  constructor
  · intro h
    have hf := (equivK_iff_functionCongr k _ _).1 h
    have hv := (functionCongr_iff_vanishesMod k _ _).1 hf
    rw [cubic_sub] at hv
    have h' :=
      (vanishesMod_cubic_iff k (A - A') (B - B') (lin - lin') (cst - cst')).1 hv
    refine ⟨h'.1, ?_, ?_, ?_⟩
    · convert h'.2.1 using 1; ring
    · convert h'.2.2.1 using 1; ring
    · convert h'.2.2.2 using 1; ring
  · intro ⟨hcst, hsum, hmid, h6⟩
    refine (equivK_iff_functionCongr k _ _).2 ?_
    refine (functionCongr_iff_vanishesMod k _ _).2 ?_
    rw [cubic_sub]
    refine (vanishesMod_cubic_iff k (A - A') (B - B') (lin - lin') (cst - cst')).2 ?_
    refine ⟨hcst, ?_, ?_, ?_⟩
    · convert hsum using 1; ring
    · convert hmid using 1; ring
    · convert h6 using 1; ring

/-- Two cubics are equivalent at horizon `k` exactly when their Newton coordinates agree modulo `3^k`. -/
theorem equivK_cubic_newton (k : ℕ) (A B lin cst A' B' lin' cst' : ℤ) :
    equivK k (cubic A B lin cst) (cubic A' B' lin' cst') ↔
      (3 : ℤ) ^ k ∣ (newtonCoords A B lin cst).1
          - (newtonCoords A' B' lin' cst').1 ∧
        (3 : ℤ) ^ k ∣ (newtonCoords A B lin cst).2.1
          - (newtonCoords A' B' lin' cst').2.1 ∧
          (3 : ℤ) ^ k ∣ (newtonCoords A B lin cst).2.2.1
            - (newtonCoords A' B' lin' cst').2.2.1 ∧
            (3 : ℤ) ^ k ∣ (newtonCoords A B lin cst).2.2.2
              - (newtonCoords A' B' lin' cst').2.2.2 := by
  have hiff := equivK_cubic k A B lin cst A' B' lin' cst'
  constructor
  · intro h
    obtain ⟨hcst, hsum, hmid, h6⟩ := hiff.1 h
    refine ⟨hcst, hsum, ?_, h6⟩
    have : (3 : ℤ) ^ k ∣ 2 * ((3 * A + B) - (3 * A' + B')) := by
      simpa [mul_comm] using hmid.mul_right (2 : ℤ)
    have hN2 : (3 : ℤ) ^ k ∣ (6 * A + 2 * B) - (6 * A' + 2 * B') := by
      have heq :
          2 * ((3 * A + B) - (3 * A' + B')) =
            (6 * A + 2 * B) - (6 * A' + 2 * B') := by
        omega
      simpa [heq] using this
    exact hN2
  · intro ⟨hcst, hsum, hN2, h6⟩
    refine hiff.2 ⟨hcst, hsum, ?_, h6⟩
    have h2 : (3 : ℤ) ^ k ∣ 2 * ((3 * A + B) - (3 * A' + B')) := by
      have heq :
          (newtonCoords A B lin cst).2.2.1 - (newtonCoords A' B' lin' cst').2.2.1 =
            2 * ((3 * A + B) - (3 * A' + B')) := by
        simp [newtonCoords]
        omega
      simpa [heq] using hN2
    exact three_pow_dvd_of_two_mul h2

/-- `-1` is a trit. -/
lemma isTrit_neg_one : isTrit (-1) :=
  Or.inl rfl

/-- `1` is a trit. -/
lemma isTrit_one : isTrit (1) :=
  Or.inr (Or.inr rfl)

/-- `[-1]` is a trit word. -/
lemma isTritList_singleton_neg : isTritList [(-1 : ℤ)] :=
  ⟨isTrit_neg_one, trivial⟩

/-- `[1]` is a trit word. -/
lemma isTritList_singleton_one : isTritList [(1 : ℤ)] :=
  ⟨isTrit_one, trivial⟩

/-- `packWord [-1] = -1`. -/
theorem packWord_neg_one : packWord [(-1 : ℤ)] = -1 := by
  simp [packWord, packTrits]

/-- `packWord [1] = 1`. -/
theorem packWord_one : packWord [(1 : ℤ)] = 1 := by
  simp [packWord, packTrits]

/-- `cubicResid 1 (-1) = cubic 9 (-9) 3 0`. -/
theorem cubicResid_one_neg :
    cubicResid 1 (-1) = cubic 9 (-9) 3 0 := by
  unfold cubicResid
  simp [iterDZ, DZ_neg_one]

/-- `cubicResid 1 1 = cubic 9 9 3 0`. -/
theorem cubicResid_one_pos :
    cubicResid 1 1 = cubic 9 9 3 0 := by
  unfold cubicResid
  simp [iterDZ, DZ_one]

/-- First merge: the depth-1 sign pair has identical Newton residues
modulo ``9``, hence ``≡_2``. -/
theorem x3_first_merge_newton :
    equivK 2 (cubicResid 1 (-1)) (cubicResid 1 1) := by
  rw [cubicResid_one_neg, cubicResid_one_pos]
  refine (equivK_cubic_newton 2 9 (-9) 3 0 9 9 3 0).2 ?_
  decide

/-- The two depth-one `X^3` residuals are not equivalent at horizon `3`. -/
theorem x3_first_merge_newton_not_three :
    ¬ equivK 3 (cubicResid 1 (-1)) (cubicResid 1 1) := by
  rw [cubicResid_one_neg, cubicResid_one_pos]
  intro h
  have hN := (equivK_cubic_newton 3 9 (-9) 3 0 9 9 3 0).1 h
  have : ¬ (27 : ℤ) ∣ (-18 : ℤ) := by decide
  exact this hN.2.1

/-- `residualAlong [-1] (X^3) = cubicResid 1 (-1)`. -/
theorem residualAlong_Xcube_neg :
    residualAlong [(-1 : ℤ)] ((X : ℤ[X]) ^ 3) = cubicResid 1 (-1) := by
  simpa [packWord_neg_one] using residualAlong_Xcube isTritList_singleton_neg

/-- `residualAlong [1] (X^3) = cubicResid 1 1`. -/
theorem residualAlong_Xcube_pos :
    residualAlong [(1 : ℤ)] ((X : ℤ[X]) ^ 3) = cubicResid 1 1 := by
  simpa [packWord_one] using residualAlong_Xcube isTritList_singleton_one

/-- The `k = 2` merge of the two `X^3` residuals, obtained through the Newton coordinates. -/
theorem x3_first_merge_via_newton :
    equivK 2
      (residualAlong [(-1 : ℤ)] ((X : ℤ[X]) ^ 3))
      (residualAlong [(1 : ℤ)] ((X : ℤ[X]) ^ 3)) := by
  rw [residualAlong_Xcube_neg, residualAlong_Xcube_pos]
  exact x3_first_merge_newton

end BTCalculus
