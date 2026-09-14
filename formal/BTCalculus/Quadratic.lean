import Mathlib.Algebra.Order.Group.Abs
import BTCalculus.MyhillNerode
import BTCalculus.NormalizedDerivative

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Quadratic residual calculus of ``x^2``.

Along an LSD-first trit word ``w``,

  ``𝔇_w(X^2) = 3^{|w|} X^2 + 2 p(w) X + iterDZ |w| (p(w)^2)``.

Degree-``≤ 2`` polynomials satisfy ``f ≡_k g`` iff their coefficients
agree modulo ``3^k``. Distinct prefixes of length ``< k`` are therefore
``≡_k``-separated, so ``M_k(x^2) = R_k(x^2) = (3^k-1)/2``.
-/

def quad (A B c0 : ℤ) : ℤ[X] :=
  C A * X ^ 2 + C B * X + C c0

def packWord (w : List ℤ) : ℤ :=
  packTrits w 0

theorem eval_quad (A B c0 x : ℤ) :
    eval x (quad A B c0) = A * x ^ 2 + B * x + c0 := by
  unfold quad
  simp [eval_add, eval_mul, eval_pow, eval_X]

theorem coeff_quad_zero (A B c0 : ℤ) : coeff (quad A B c0) 0 = c0 := by
  unfold quad
  rw [coeff_add, coeff_add, coeff_C]
  have hX2 : coeff (C A * X ^ 2) 0 = 0 := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX : coeff (C B * X) 0 = 0 := by
    rw [coeff_C_mul, coeff_X]; simp
  rw [hX2, hX]
  simp

theorem coeff_quad_one (A B c0 : ℤ) : coeff (quad A B c0) 1 = B := by
  unfold quad
  rw [coeff_add, coeff_add]
  have hX2 : coeff (C A * X ^ 2) 1 = 0 := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX : coeff (C B * X) 1 = B := by
    rw [coeff_C_mul, coeff_X]; simp
  have hC : coeff (C c0) 1 = 0 := by
    rw [coeff_C]; simp
  rw [hX2, hX, hC]
  simp

theorem coeff_quad_two (A B c0 : ℤ) : coeff (quad A B c0) 2 = A := by
  unfold quad
  rw [coeff_add, coeff_add]
  have hX2 : coeff (C A * X ^ 2) 2 = A := by
    rw [coeff_C_mul, coeff_X_pow]; simp
  have hX : coeff (C B * X) 2 = 0 := by
    rw [coeff_C_mul, coeff_X]; simp
  have hC : coeff (C c0) 2 = 0 := by
    rw [coeff_C]; simp
  rw [hX2, hX, hC]
  simp

theorem quad_inj {A B c0 A' B' c0' : ℤ}
    (h : quad A B c0 = quad A' B' c0') :
    A = A' ∧ B = B' ∧ c0 = c0' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [coeff_quad_two] using congrArg (fun p => coeff p 2) h
  · simpa [coeff_quad_one] using congrArg (fun p => coeff p 1) h
  · simpa [coeff_quad_zero] using congrArg (fun p => coeff p 0) h

theorem X_sq_eq_quad : (X : ℤ[X]) ^ 2 = quad 1 0 0 := by
  unfold quad
  simp

theorem lsdZ_of_isTrit {a : ℤ} (ha : isTrit a) : lsdZ a = a :=
  lsdZ_unique ha (Int.ModEq.refl a)

theorem packWord_nil : packWord [] = 0 := rfl

theorem packWord_cons (a : ℤ) (w : List ℤ) :
    packWord (a :: w) = a + 3 * packWord w := rfl

theorem packTrits_eq (w : List ℤ) (acc : ℤ) :
    packTrits w acc = packWord w + (3 : ℤ) ^ w.length * acc := by
  induction w with
  | nil => simp [packTrits, packWord]
  | cons b rest ih =>
    simp [packTrits, packWord_cons, ih, pow_succ]
    ring

theorem integerJet_length : ∀ (k : ℕ) (n : ℤ), (integerJet k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [integerJet, integerJet_length k]

theorem isTritList_integerJet : ∀ (k : ℕ) (n : ℤ), isTritList (integerJet k n)
  | 0, _ => trivial
  | k + 1, n => ⟨isTrit_lsdZ n, isTritList_integerJet k (DZ n)⟩

theorem isTritList_outputAlong : ∀ (w : List ℤ) (f : ℤ[X]), isTritList (outputAlong w f)
  | [], _ => trivial
  | a :: w, f => ⟨isTrit_lsdZ (eval a f), isTritList_outputAlong w (sectionDeriv a f)⟩

theorem outputAlong_length_eq : ∀ (w : List ℤ) (f : ℤ[X]),
    (outputAlong w f).length = w.length
  | [], _ => rfl
  | _a :: w, f => by simp [outputAlong, outputAlong_length_eq w]

theorem packTrits_integerJet : ∀ (k : ℕ) (n : ℤ),
    packTrits (integerJet k n) (iterDZ k n) = n
  | 0, n => by simp [integerJet, packTrits, iterDZ]
  | k + 1, n => by
    have ih := packTrits_integerJet k (DZ n)
    simp [integerJet, packTrits, iterDZ, ih]
    exact (decomp n).symm

theorem iterDZ_succ_right : ∀ (k : ℕ) (n : ℤ), iterDZ (k + 1) n = DZ (iterDZ k n)
  | 0, _ => rfl
  | k + 1, n => by
    change iterDZ (k + 1) (DZ n) = DZ (iterDZ (k + 1) n)
    rw [iterDZ_succ_right k (DZ n)]
    rfl

theorem integerJet_add_pow : ∀ (k : ℕ) (n t : ℤ),
    integerJet k (n + (3 : ℤ) ^ k * t) = integerJet k n
  | 0, _, _ => rfl
  | k + 1, n, t => by
    have hpow : (3 : ℤ) ^ (k + 1) * t = 3 * ((3 : ℤ) ^ k * t) := by
      rw [pow_succ]; ring
    have hlsd : lsdZ (n + (3 : ℤ) ^ (k + 1) * t) = lsdZ n := by
      rw [hpow, lsdZ_add_mul3]
    have hdz : DZ (n + (3 : ℤ) ^ (k + 1) * t) = DZ n + (3 : ℤ) ^ k * t := by
      rw [hpow, DZ_add_mul3]
    simp [integerJet, hlsd, hdz, integerJet_add_pow k]

theorem integerJet_eq_iff_dvd (k : ℕ) (a b : ℤ) :
    integerJet k a = integerJet k b ↔ (3 : ℤ) ^ k ∣ a - b := by
  constructor
  · intro h
    have ha := packTrits_integerJet k a
    have hb := packTrits_integerJet k b
    rw [packTrits_eq, integerJet_length] at ha hb
    rw [h] at ha
    exact ⟨iterDZ k a - iterDZ k b, by linarith⟩
  · rintro ⟨t, ht⟩
    have : a = b + (3 : ℤ) ^ k * t := by linarith
    rw [this, integerJet_add_pow]

theorem two_mul_packWord_le : ∀ {w : List ℤ}, isTritList w →
    2 * |packWord w| ≤ (3 : ℤ) ^ w.length - 1
  | [], _ => by
    simp [packWord, packTrits]
  | a :: rest, hw => by
    have ih := two_mul_packWord_le (w := rest) hw.2
    have habs : |a| ≤ 1 := by
      rcases (hw.1 : a = -1 ∨ a = 0 ∨ a = 1) with rfl | rfl | rfl <;> simp
    have hle : |a + 3 * packWord rest| ≤ |a| + 3 * |packWord rest| := by
      have := abs_add_le a (3 * packWord rest)
      simpa [abs_mul, abs_of_nonneg (by decide : (0 : ℤ) ≤ 3)] using this
    have hmain : 2 * |packWord (a :: rest)| ≤ 2 + 3 * ((3 : ℤ) ^ rest.length - 1) := by
      rw [packWord_cons]
      linarith
    have hpow : 2 + 3 * ((3 : ℤ) ^ rest.length - 1) = (3 : ℤ) ^ (a :: rest).length - 1 := by
      simp [pow_succ]
      ring
    linarith

theorem packWord_injective {w v : List ℤ}
    (hw : isTritList w) (hv : isTritList v)
    (hlen : w.length = v.length)
    (hp : packWord w = packWord v) : w = v := by
  induction w generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a rest ih =>
    cases v with
    | nil => simp at hlen
    | cons b rest' =>
      have hp' : a + 3 * packWord rest = b + 3 * packWord rest' := by
        simpa [packWord_cons] using hp
      have hmod : a ≡ b [ZMOD 3] := by
        refine Int.modEq_iff_dvd.mpr ⟨packWord rest - packWord rest', ?_⟩
        linarith
      have hab : a = b := trit_mod_unique hw.1 hv.1 hmod
      subst hab
      have hrest := ih hw.2 hv.2 (Nat.succ_injective hlen) (by linarith)
      rw [hrest]

theorem dvd_abs_lt_pow {k : ℕ} {δ : ℤ}
    (hdvd : (3 : ℤ) ^ k ∣ δ) (hlt : |δ| < (3 : ℤ) ^ k) : δ = 0 := by
  obtain ⟨q, hq⟩ := hdvd
  have hpos : 0 < (3 : ℤ) ^ k := pow_pos (by decide) k
  have habs : |δ| = (3 : ℤ) ^ k * |q| := by
    rw [hq, abs_mul, abs_pow]
    simp
  have : |q| < 1 := by
    have : (3 : ℤ) ^ k * |q| < (3 : ℤ) ^ k := by rwa [← habs]
    exact (mul_lt_iff_lt_one_right hpos).1 this
  have hq0 : q = 0 := Int.abs_lt_one_iff.mp this
  simp [hq, hq0]

theorem decomp_unique {w v : List ℤ} {r s : ℤ}
    (hw : isTritList w) (hv : isTritList v)
    (hlen : w.length = v.length)
    (heq : packTrits w r = packTrits v s) : w = v ∧ r = s := by
  have hwacc := packTrits_eq w r
  have hvacc := packTrits_eq v s
  have hsum : packWord w + (3 : ℤ) ^ w.length * r =
      packWord v + (3 : ℤ) ^ w.length * s := by
    have hpow : (3 : ℤ) ^ v.length = (3 : ℤ) ^ w.length := by rw [hlen]
    rw [hwacc, hvacc, hpow] at heq
    exact heq
  have hdiff : packWord w - packWord v = (3 : ℤ) ^ w.length * (s - r) := by
    linarith
  have hlt : |packWord w - packWord v| < (3 : ℤ) ^ w.length := by
    have hb1 := two_mul_packWord_le hw
    have hb2 := two_mul_packWord_le hv
    rw [← hlen] at hb2
    have habs : |packWord w - packWord v| ≤ |packWord w| + |packWord v| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (packWord w) (-packWord v)
    have : (0 : ℤ) < (3 : ℤ) ^ w.length := pow_pos (by decide) _
    nlinarith
  have hzero : packWord w - packWord v = 0 :=
    dvd_abs_lt_pow ⟨s - r, hdiff⟩ hlt
  have hp : packWord w = packWord v := sub_eq_zero.mp hzero
  refine ⟨packWord_injective hw hv hlen hp, ?_⟩
  have : (3 : ℤ) ^ w.length * (s - r) = 0 := by linarith
  have hnz : (3 : ℤ) ^ w.length ≠ 0 := pow_ne_zero _ (by decide)
  have hs : s - r = 0 := (mul_eq_zero.mp this).resolve_left hnz
  exact (sub_eq_zero.mp hs).symm

theorem outputAlong_integerJet (f : ℤ[X]) (n : ℤ) (k : ℕ) :
    outputAlong (integerJet k n) f = integerJet k (eval n f) := by
  have hrec := function_jet_reconstruction f n k
  have hdecomp := packTrits_integerJet k (eval n f)
  have heq :
      packTrits (outputAlong (integerJet k n) f)
          (eval (iterDZ k n) (residualAlong (integerJet k n) f)) =
        packTrits (integerJet k (eval n f)) (iterDZ k (eval n f)) := by
    rw [← hrec, hdecomp]
  exact (decomp_unique (isTritList_outputAlong _ _) (isTritList_integerJet k _)
    (by simp [outputAlong_length_eq, integerJet_length]) heq).1

theorem iterDZ_packWord : ∀ {w : List ℤ}, isTritList w →
    iterDZ w.length (packWord w) = 0
  | [], _ => rfl
  | a :: rest, hw => by
    have hlsd : lsdZ (packWord (a :: rest)) = a := by
      rw [packWord_cons, lsdZ_add_mul3, lsdZ_of_isTrit hw.1]
    have hdz : DZ (packWord (a :: rest)) = packWord rest := by
      rw [packWord_cons, DZ_add_mul3, trit_DZ hw.1, zero_add]
    change iterDZ rest.length (DZ (packWord (a :: rest))) = 0
    rw [hdz]
    exact iterDZ_packWord hw.2

theorem integerJet_packWord {w : List ℤ} (hw : isTritList w) :
    integerJet w.length (packWord w) = w := by
  have h1 := packTrits_integerJet w.length (packWord w)
  rw [iterDZ_packWord hw] at h1
  have : packTrits (integerJet w.length (packWord w)) 0 = packTrits w 0 := by
    simpa [packWord] using h1
  exact (decomp_unique (isTritList_integerJet _ _) hw
    (by simp [integerJet_length]) this).1

theorem outputAlong_word (f : ℤ[X]) {w : List ℤ} (hw : isTritList w) :
    outputAlong w f = integerJet w.length (eval (packWord w) f) := by
  have h := integerJet_packWord hw
  conv_lhs => rw [← h]
  exact outputAlong_integerJet f (packWord w) w.length

theorem packWord_replicate_zero : ∀ k : ℕ, packWord (List.replicate k (0 : ℤ)) = 0
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, packWord_cons, packWord_replicate_zero]
    simp

theorem packWord_one_zeros (k : ℕ) :
    packWord (1 :: List.replicate k (0 : ℤ)) = 1 := by
  simp [packWord_cons, packWord_replicate_zero]

theorem packWord_neg_zeros (k : ℕ) :
    packWord ((-1 : ℤ) :: List.replicate k 0) = -1 := by
  simp [packWord_cons, packWord_replicate_zero]

theorem isTritList_one_zeros (k : ℕ) :
    isTritList (1 :: List.replicate k (0 : ℤ)) :=
  ⟨Or.inr (Or.inr rfl), isTritList_replicate_zero k⟩

theorem isTritList_neg_zeros (k : ℕ) :
    isTritList ((-1 : ℤ) :: List.replicate k 0) :=
  ⟨Or.inl rfl, isTritList_replicate_zero k⟩

theorem eval_sectionDeriv_quad (A B c0 a x : ℤ) :
    eval x (sectionDeriv a (quad A B c0)) =
      3 * A * x ^ 2 + (B + 2 * A * a) * x + DZ (A * a ^ 2 + B * a + c0) := by
  have hrec := section_reconstruction_eval (quad A B c0) a x
  have hf := eval_quad A B c0 (a + 3 * x)
  have ha := eval_quad A B c0 a
  set n := A * a ^ 2 + B * a + c0
  have hd : n = lsdZ n + 3 * DZ n := decomp n
  have hexpand :
      A * (a + 3 * x) ^ 2 + B * (a + 3 * x) + c0 =
        n + 3 * (3 * A * x ^ 2 + (2 * A * a + B) * x) := by ring
  have hdecomp' :
      n + 3 * (3 * A * x ^ 2 + (2 * A * a + B) * x) =
        lsdZ n + 3 * (3 * A * x ^ 2 + (B + 2 * A * a) * x + DZ n) := by
    conv_lhs => rw [hd]
    ring
  have hexp := hexpand.trans hdecomp'
  have h3 :
      3 * eval x (sectionDeriv a (quad A B c0)) =
        3 * (3 * A * x ^ 2 + (B + 2 * A * a) * x + DZ n) := by
    rw [hf, ha] at hrec
    linarith [hrec, hexp]
  linarith

theorem sectionDeriv_quad (A B c0 a : ℤ) :
    sectionDeriv a (quad A B c0) =
      quad (3 * A) (B + 2 * A * a) (DZ (A * a ^ 2 + B * a + c0)) := by
  refine Polynomial.funext (fun x => ?_)
  have hL := eval_sectionDeriv_quad A B c0 a x
  have hR := eval_quad (3 * A) (B + 2 * A * a) (DZ (A * a ^ 2 + B * a + c0)) x
  linarith

theorem iterDZ_add_pow : ∀ (m : ℕ) (n t : ℤ),
    iterDZ m (n + (3 : ℤ) ^ m * t) = iterDZ m n + t
  | 0, _n, t => by simp [iterDZ]
  | m + 1, n, t => by
    have hpow : (3 : ℤ) ^ (m + 1) * t = 3 * ((3 : ℤ) ^ m * t) := by
      rw [pow_succ]; ring
    have hL : iterDZ (m + 1) (n + (3 : ℤ) ^ (m + 1) * t) =
        iterDZ m (DZ (n + (3 : ℤ) ^ (m + 1) * t)) := rfl
    have hR : iterDZ (m + 1) n = iterDZ m (DZ n) := rfl
    rw [hL, hR, hpow, DZ_add_mul3, iterDZ_add_pow m]

theorem C_step (m : ℕ) (p a : ℤ) :
    DZ ((3 : ℤ) ^ m * a ^ 2 + 2 * p * a + iterDZ m (p ^ 2)) =
      iterDZ (m + 1) ((p + (3 : ℤ) ^ m * a) ^ 2) := by
  have hsq :
      (p + (3 : ℤ) ^ m * a) ^ 2 =
        p ^ 2 + (3 : ℤ) ^ m * (2 * p * a + (3 : ℤ) ^ m * a ^ 2) := by ring
  have hiter := iterDZ_add_pow m (p ^ 2) (2 * p * a + (3 : ℤ) ^ m * a ^ 2)
  have hr : iterDZ (m + 1) ((p + (3 : ℤ) ^ m * a) ^ 2) =
      DZ (iterDZ m ((p + (3 : ℤ) ^ m * a) ^ 2)) :=
    iterDZ_succ_right m _
  rw [hr, hsq, hiter]
  ring

theorem residualAlong_family (m : ℕ) (p : ℤ) :
    ∀ {w : List ℤ}, isTritList w →
      residualAlong w (quad ((3 : ℤ) ^ m) (2 * p) (iterDZ m (p ^ 2))) =
        quad ((3 : ℤ) ^ (m + w.length))
          (2 * (p + (3 : ℤ) ^ m * packWord w))
          (iterDZ (m + w.length) ((p + (3 : ℤ) ^ m * packWord w) ^ 2))
  | [], _ => by
    simp [residualAlong, packWord, packTrits]
  | a :: rest, hw => by
    have hstep := sectionDeriv_quad ((3 : ℤ) ^ m) (2 * p) (iterDZ m (p ^ 2)) a
    have hC := C_step m p a
    have hsd :
        sectionDeriv a (quad ((3 : ℤ) ^ m) (2 * p) (iterDZ m (p ^ 2))) =
          quad ((3 : ℤ) ^ (m + 1)) (2 * (p + (3 : ℤ) ^ m * a))
            (iterDZ (m + 1) ((p + (3 : ℤ) ^ m * a) ^ 2)) := by
      rw [hstep, hC]
      congr 1
      · rw [pow_succ]; ring
      · ring
    have ih := residualAlong_family (m + 1) (p + (3 : ℤ) ^ m * a) hw.2
    rw [residualAlong_cons, hsd, ih]
    simp [packWord_cons, List.length_cons]
    congr 1
    · ac_rfl
    · ring
    · congr 1
      · ac_rfl
      · ring

theorem residualAlong_Xsq {w : List ℤ} (hw : isTritList w) :
    residualAlong w ((X : ℤ[X]) ^ 2) =
      quad ((3 : ℤ) ^ w.length) (2 * packWord w) (iterDZ w.length (packWord w ^ 2)) := by
  have h := residualAlong_family 0 0 hw
  simpa [X_sq_eq_quad, pow_zero, iterDZ, packWord, packTrits] using h

theorem residualAlong_Xsq_injective {w v : List ℤ}
    (hw : isTritList w) (hv : isTritList v)
    (h : residualAlong w ((X : ℤ[X]) ^ 2) = residualAlong v ((X : ℤ[X]) ^ 2)) :
    w = v := by
  have hf := residualAlong_Xsq hw
  have hg := residualAlong_Xsq hv
  rw [hf, hg] at h
  obtain ⟨hA, hB, _⟩ := quad_inj h
  have hlen : w.length = v.length := by
    apply Nat.pow_right_injective (by decide : (1 : ℕ) < 3)
    have hAbs := congrArg Int.natAbs hA
    rw [Int.natAbs_pow, Int.natAbs_pow] at hAbs
    exact_mod_cast hAbs
  exact packWord_injective hw hv hlen (by linarith)

theorem eval_diff_quad (A B c0 A' B' c0' x : ℤ) :
    eval x (quad A B c0) - eval x (quad A' B' c0') =
      (A - A') * x ^ 2 + (B - B') * x + (c0 - c0') := by
  simp [eval_quad]
  ring

/-- Coefficient congruence modulo ``3^k`` implies finite-horizon equivalence. -/
theorem equivK_quad_of_dvd (k : ℕ) {A B c0 A' B' c0' : ℤ}
    (hA : (3 : ℤ) ^ k ∣ A - A') (hB : (3 : ℤ) ^ k ∣ B - B')
    (hC : (3 : ℤ) ^ k ∣ c0 - c0') :
    equivK k (quad A B c0) (quad A' B' c0') := by
  refine (equivK_iff_outputs k _ _).2 ?_
  intro w hlen hw
  rw [outputAlong_word (quad A B c0) hw, outputAlong_word (quad A' B' c0') hw, hlen]
  refine (integerJet_eq_iff_dvd k _ _).2 ?_
  have hdiff := eval_diff_quad A B c0 A' B' c0' (packWord w)
  have hd1 : (3 : ℤ) ^ k ∣ (A - A') * packWord w ^ 2 := hA.mul_right _
  have hd2 : (3 : ℤ) ^ k ∣ (B - B') * packWord w := hB.mul_right _
  simpa [hdiff] using (hd1.add hd2).add hC

lemma two_coprime_three_pow (k : ℕ) : IsCoprime (2 : ℤ) ((3 : ℤ) ^ k) := by
  have hodd : Odd ((3 : ℤ) ^ k) := Odd.pow (by decide : Odd (3 : ℤ))
  obtain ⟨m, hm⟩ := hodd
  exact ⟨-m, 1, by linarith [hm]⟩

lemma three_pow_dvd_of_two_mul {k : ℕ} {δ : ℤ}
    (h : (3 : ℤ) ^ k ∣ 2 * δ) : (3 : ℤ) ^ k ∣ δ :=
  (two_coprime_three_pow k).symm.dvd_of_dvd_mul_left h

lemma not_three_dvd_pow_sub_one {t : ℕ} (ht : 0 < t) :
    ¬ (3 : ℤ) ∣ ((3 : ℤ) ^ t - 1) := by
  intro h
  have hz : ((3 : ℤ) ^ t - 1) % 3 = 0 := Int.dvd_iff_emod_eq_zero.mp h
  have hp : ((3 : ℤ) ^ t) % 3 = 0 := by
    rcases t with _ | t
    · exact (Nat.lt_irrefl _ ht).elim
    · rw [pow_succ, mul_comm]
      exact Int.mul_emod_right (3 : ℤ) ((3 : ℤ) ^ t)
  have h2 : ((3 : ℤ) ^ t - 1) % 3 = 2 := by
    rw [Int.sub_emod, hp]
    decide
  omega

lemma three_pow_sub_eq {m n : ℕ} (hmn : m ≤ n) :
    (3 : ℤ) ^ n - (3 : ℤ) ^ m = (3 : ℤ) ^ m * ((3 : ℤ) ^ (n - m) - 1) := by
  have : (3 : ℤ) ^ n = (3 : ℤ) ^ m * (3 : ℤ) ^ (n - m) := by
    rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hmn]
  rw [this]
  ring

lemma three_pow_inj_of_dvd {m n k : ℕ}
    (hm : m < k) (hn : n < k)
    (h : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ m - (3 : ℤ) ^ n) : m = n := by
  wlog hle : m ≤ n generalizing m n
  · have h' : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ n - (3 : ℤ) ^ m := by
      simpa [neg_sub] using h.neg_right
    exact (this hn hm h' (le_of_not_ge hle)).symm
  rcases hle.eq_or_lt with rfl | hlt
  · rfl
  · have ht : 0 < n - m := Nat.sub_pos_of_lt hlt
    have hneg : (3 : ℤ) ^ k ∣ (3 : ℤ) ^ n - (3 : ℤ) ^ m := by
      simpa [neg_sub] using h.neg_right
    have hk : (3 : ℤ) ^ (m + 1) ∣ (3 : ℤ) ^ n - (3 : ℤ) ^ m :=
      dvd_trans (pow_dvd_pow (3 : ℤ) (by omega : m + 1 ≤ k)) hneg
    have hnz : (3 : ℤ) ^ m ≠ 0 := pow_ne_zero _ (by decide)
    have : (3 : ℤ) ∣ ((3 : ℤ) ^ (n - m) - 1) := by
      rw [pow_succ, three_pow_sub_eq hle] at hk
      have hk' : (3 : ℤ) ^ m * 3 ∣ (3 : ℤ) ^ m * ((3 : ℤ) ^ (n - m) - 1) := by
        simpa [mul_comm] using hk
      exact (mul_dvd_mul_iff_left hnz).mp hk'
    exact (not_three_dvd_pow_sub_one ht this).elim

/-- Finite-horizon equivalence of degree-``≤ 2`` polynomials is coefficient
congruence modulo ``3^k``. Canonical probes: ``0^k``, ``10^{k-1}``, ``(-1)0^{k-1}``. -/
theorem equivK_quad (k : ℕ) (A B c0 A' B' c0' : ℤ) :
    equivK k (quad A B c0) (quad A' B' c0') ↔
      (3 : ℤ) ^ k ∣ A - A' ∧ (3 : ℤ) ^ k ∣ B - B' ∧ (3 : ℤ) ^ k ∣ c0 - c0' := by
  constructor
  · intro h
    cases k with
    | zero => simp
    | succ k =>
      have hout := (equivK_iff_outputs (k + 1) _ _).1 h
      have h0 :=
        hout (List.replicate (k + 1) (0 : ℤ))
          (by simp [List.length_replicate]) (isTritList_replicate_zero _)
      have h1 :=
        hout (1 :: List.replicate k (0 : ℤ))
          (by simp [List.length_replicate]) (isTritList_one_zeros k)
      have hm :=
        hout ((-1 : ℤ) :: List.replicate k 0)
          (by simp [List.length_replicate]) (isTritList_neg_zeros k)
      rw [outputAlong_word _ (isTritList_replicate_zero (k + 1)),
          outputAlong_word _ (isTritList_replicate_zero (k + 1)),
          packWord_replicate_zero, List.length_replicate] at h0
      rw [outputAlong_word _ (isTritList_one_zeros k),
          outputAlong_word _ (isTritList_one_zeros k),
          packWord_one_zeros, List.length_cons, List.length_replicate] at h1
      rw [outputAlong_word _ (isTritList_neg_zeros k),
          outputAlong_word _ (isTritList_neg_zeros k),
          packWord_neg_zeros, List.length_cons, List.length_replicate] at hm
      have hz0 := (integerJet_eq_iff_dvd (k + 1) _ _).1 h0
      have hz1 := (integerJet_eq_iff_dvd (k + 1) _ _).1 h1
      have hzm := (integerJet_eq_iff_dvd (k + 1) _ _).1 hm
      rw [eval_quad, eval_quad] at hz0 hz1 hzm
      have hγ : (3 : ℤ) ^ (k + 1) ∣ c0 - c0' := by simpa using hz0
      have h1' : (3 : ℤ) ^ (k + 1) ∣ (A - A') + (B - B') + (c0 - c0') := by
        convert hz1 using 1
        ring
      have hm' : (3 : ℤ) ^ (k + 1) ∣ (A - A') - (B - B') + (c0 - c0') := by
        convert hzm using 1
        ring
      have hαβ : (3 : ℤ) ^ (k + 1) ∣ (A - A') + (B - B') := by
        simpa [add_sub_cancel_right] using dvd_sub h1' hγ
      have hαmβ : (3 : ℤ) ^ (k + 1) ∣ (A - A') - (B - B') := by
        simpa [add_sub_cancel_right] using dvd_sub hm' hγ
      have h2α : (3 : ℤ) ^ (k + 1) ∣ 2 * (A - A') := by
        have h := dvd_add hαβ hαmβ
        have heq :
            (A - A') + (B - B') + ((A - A') - (B - B')) = 2 * (A - A') := by
          omega
        simpa [heq] using h
      have h2β : (3 : ℤ) ^ (k + 1) ∣ 2 * (B - B') := by
        have h := dvd_sub hαβ hαmβ
        have heq :
            (A - A') + (B - B') - ((A - A') - (B - B')) = 2 * (B - B') := by
          omega
        simpa [heq] using h
      exact ⟨three_pow_dvd_of_two_mul h2α, three_pow_dvd_of_two_mul h2β, hγ⟩
  · intro ⟨hA, hB, hC⟩
    exact equivK_quad_of_dvd k hA hB hC

/-- Distinct residuals of ``x^2`` at depth ``< k`` are ``≡_k``-separated. -/
theorem xsq_equivK_iff_eq (k : ℕ) {w v : List ℤ}
    (hw : isTritList w) (hv : isTritList v)
    (hwk : w.length < k) (hvk : v.length < k) :
    equivK k (residualAlong w ((X : ℤ[X]) ^ 2))
      (residualAlong v ((X : ℤ[X]) ^ 2)) ↔ w = v := by
  constructor
  · intro h
    have hf := residualAlong_Xsq hw
    have hg := residualAlong_Xsq hv
    rw [hf, hg] at h
    have hcoeff := (equivK_quad k _ _ _ _ _ _).1 h
    have hlen : w.length = v.length :=
      three_pow_inj_of_dvd hwk hvk hcoeff.1
    have hp : packWord w = packWord v := by
      have h2 : (3 : ℤ) ^ k ∣ 2 * (packWord w - packWord v) := by
        convert hcoeff.2.1 using 1
        ring
      have hd := three_pow_dvd_of_two_mul h2
      have hbound : |packWord w - packWord v| < (3 : ℤ) ^ k := by
        have hb1 := two_mul_packWord_le hw
        have hb2 := two_mul_packWord_le hv
        have habs : |packWord w - packWord v| ≤ |packWord w| + |packWord v| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le (packWord w) (-packWord v)
        have hx : (3 : ℤ) ^ w.length ≤ (3 : ℤ) ^ k :=
          pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 3) (Nat.le_of_lt hwk)
        have hy : (3 : ℤ) ^ v.length ≤ (3 : ℤ) ^ k :=
          pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 3) (Nat.le_of_lt hvk)
        have : (0 : ℤ) < (3 : ℤ) ^ k := pow_pos (by decide) _
        nlinarith
      exact sub_eq_zero.mp (dvd_abs_lt_pow hd hbound)
    exact packWord_injective hw hv hlen hp
  · intro h
    subst h
    exact equivK_refl k _

end BTCalculus
