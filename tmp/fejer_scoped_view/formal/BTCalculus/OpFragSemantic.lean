/-
Semantic canonicity of the enlarged operator-fragment NF grammar.

Distinct irreducibles `w(D^d(x))` and `w(D^d(N(x)))` for
`w ∈ {I-, I+, S}*` denote pairwise distinct integer operator functions.
Integer soundness of each tree rule is `BTCalculus/Rewrite.lean`.
Syntactic uniqueness of NF is `OpFrag.unique_normal_form`.
Coefficient-word confluence remains `BTCalculus/Confluence.lean`.
-/

import Mathlib.Logic.Relation
import BTCalculus.OpFragNewman
import BTCalculus.Rewrite

namespace BTCalculus
namespace OpFrag

open Representation.Words
open Relation (ReflTransGen Join)

/-! ### Integer evaluation of an open term -/

/-- Plug the hole with `n` and interpret constructors on `ℤ`. -/
def eval : OpFrag → ℤ → ℤ
  | .var, n => n
  | .D t, n => DZ (eval t n)
  | .Im t, n => IZ Trit.minus (eval t n)
  | .I0 t, n => IZ Trit.zero (eval t n)
  | .Ip t, n => IZ Trit.plus (eval t n)
  | .S t, n => SZ (eval t n)
  | .N t, n => -(eval t n)

/-! ### NF coordinates `(w, sign, d)` -/

/-- Letters of the outer spine `{I-, I+, S}`. -/
inductive SpineLetter
  | im
  | ip
  | s
  deriving DecidableEq, Repr

namespace SpineLetter

def toInt : SpineLetter → ℤ
  | .im => -1
  | .ip => 1
  | .s => 0

theorem toInt_is_trit (ℓ : SpineLetter) :
    ℓ.toInt = -1 ∨ ℓ.toInt = 0 ∨ ℓ.toInt = 1 := by
  cases ℓ <;> simp [toInt]

theorem toInt_injective {ℓ ℓ' : SpineLetter} (h : ℓ.toInt = ℓ'.toInt) :
    ℓ = ℓ' := by
  cases ℓ <;> cases ℓ' <;> simp [toInt] at h <;> rfl

end SpineLetter

def wrapLetter : SpineLetter → OpFrag → OpFrag
  | .im, t => .Im t
  | .ip, t => .Ip t
  | .s, t => .S t

def applySpine : List SpineLetter → OpFrag → OpFrag
  | [], t => t
  | ℓ :: w, t => wrapLetter ℓ (applySpine w t)

def nestD : ℕ → OpFrag → OpFrag
  | 0, t => t
  | k + 1, t => .D (nestD k t)

/-- `true` means the core is `D^d(N(x))`. -/
def mkCore (neg : Bool) (d : ℕ) : OpFrag :=
  nestD d (if neg then .N .var else .var)

def mkNF (w : List SpineLetter) (neg : Bool) (d : ℕ) : OpFrag :=
  applySpine w (mkCore neg d)

def spine : OpFrag → List SpineLetter
  | .Im t => .im :: spine t
  | .Ip t => .ip :: spine t
  | .S t => .s :: spine t
  | _ => []

def peel : OpFrag → OpFrag
  | .Im t | .Ip t | .S t => peel t
  | t => t

def depthD : OpFrag → ℕ
  | .D t => depthD t + 1
  | _ => 0

def isNegCore : OpFrag → Bool
  | .N _ => true
  | .D t => isNegCore t
  | _ => false

def coeff : List SpineLetter → ℤ
  | [] => 0
  | ℓ :: w => ℓ.toInt + 3 * coeff w

def signFactor (neg : Bool) : ℤ :=
  if neg then (-1 : ℤ) else 1

def Dpow : ℕ → ℤ → ℤ
  | 0, n => n
  | k + 1, n => DZ (Dpow k n)

/-! ### Reconstruction of an NF term -/

theorem peel_eq_of_isCore {t : OpFrag} (h : IsCore t) : peel t = t := by
  cases h <;> rfl

theorem isCore_peel {t : OpFrag} (h : IsNF t) : IsCore (peel t) := by
  induction h with
  | core hc =>
    simpa [peel_eq_of_isCore hc] using hc
  | im _ ih => exact ih
  | ip _ ih => exact ih
  | s _ ih => exact ih

theorem applySpine_spine (t : OpFrag) : applySpine (spine t) (peel t) = t := by
  induction t with
  | var => rfl
  | D x _ih => rfl
  | I0 x _ih => rfl
  | N x _ih => rfl
  | Im x ih =>
    simpa [spine, peel, applySpine, wrapLetter] using congrArg OpFrag.Im ih
  | Ip x ih =>
    simpa [spine, peel, applySpine, wrapLetter] using congrArg OpFrag.Ip ih
  | S x ih =>
    simpa [spine, peel, applySpine, wrapLetter] using congrArg OpFrag.S ih

theorem mkCore_succ (neg : Bool) (d : ℕ) :
    mkCore neg (d + 1) = .D (mkCore neg d) :=
  rfl

theorem mkCore_of_isCore {t : OpFrag} (h : IsCore t) :
    t = mkCore (isNegCore t) (depthD t) := by
  induction h with
  | hole => rfl
  | nHole => rfl
  | d _hx ih =>
    simp only [isNegCore, depthD, mkCore_succ]
    exact congrArg OpFrag.D ih

theorem mkNF_of_isNF {t : OpFrag} (h : IsNF t) :
    t = mkNF (spine t) (isNegCore (peel t)) (depthD (peel t)) := by
  rw [mkNF, ← mkCore_of_isCore (isCore_peel h), applySpine_spine]

theorem mkCore_ne_wrap (neg : Bool) (d : ℕ) (ℓ : SpineLetter) (t : OpFrag) :
    mkCore neg d ≠ wrapLetter ℓ t := by
  cases ℓ <;> cases d <;> cases neg <;> simp [mkCore, nestD, wrapLetter]

theorem mkCore_inj {neg neg' : Bool} {d d' : ℕ}
    (h : mkCore neg d = mkCore neg' d') : neg = neg' ∧ d = d' := by
  induction d generalizing d' with
  | zero =>
    cases d' with
    | zero =>
      cases neg <;> cases neg' <;> simp [mkCore, nestD] at h ⊢
    | succ d' =>
      cases neg <;> simp [mkCore, nestD] at h
  | succ d ih =>
    cases d' with
    | zero =>
      cases neg' <;> simp [mkCore, nestD] at h
    | succ d' =>
      simp [mkCore, nestD] at h
      obtain ⟨hb, hd⟩ := ih h
      exact ⟨hb, congrArg Nat.succ hd⟩

theorem wrapLetter_inj {ℓ ℓ' : SpineLetter} {t t' : OpFrag}
    (h : wrapLetter ℓ t = wrapLetter ℓ' t') : ℓ = ℓ' ∧ t = t' := by
  cases ℓ <;> cases ℓ' <;> simp [wrapLetter] at h ⊢ <;> exact h

theorem mkNF_inj {w w' : List SpineLetter} {neg neg' : Bool} {d d' : ℕ}
    (h : mkNF w neg d = mkNF w' neg' d') : w = w' ∧ neg = neg' ∧ d = d' := by
  induction w generalizing w' with
  | nil =>
    cases w' with
    | nil =>
      simp [mkNF, applySpine] at h
      exact ⟨rfl, mkCore_inj h⟩
    | cons ℓ w' =>
      simp [mkNF, applySpine] at h
      exact (mkCore_ne_wrap _ _ _ _ h).elim
  | cons ℓ w ih =>
    cases w' with
    | nil =>
      simp [mkNF, applySpine] at h
      exact (mkCore_ne_wrap _ _ _ _ h.symm).elim
    | cons ℓ' w' =>
      simp [mkNF, applySpine] at h
      obtain ⟨hℓ, ht⟩ := wrapLetter_inj h
      obtain ⟨hw, hb, hd⟩ := ih ht
      subst hℓ
      exact ⟨congrArg (ℓ :: ·) hw, hb, hd⟩

/-! ### Evaluation of an NF in closed form -/

theorem lsdZ_zero : lsdZ 0 = 0 := by
  simp [lsdZ]

theorem DZ_zero : DZ 0 = 0 := by
  simp [DZ, lsdZ]

theorem lsdZ_one : lsdZ 1 = 1 := by
  simp [lsdZ]

theorem DZ_one : DZ 1 = 0 := by
  simp [DZ, lsdZ]

theorem Dpow_zero (d : ℕ) : Dpow d 0 = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [Dpow, ih, DZ_zero]

theorem Dpow_neg (d : ℕ) (n : ℤ) : Dpow d (-n) = -(Dpow d n) := by
  induction d with
  | zero => simp [Dpow]
  | succ d ih =>
    simp [Dpow, ih, rewrite_N_D]

theorem DZ_three_mul (n : ℤ) : DZ (3 * n) = n :=
  D_after_S_int n

theorem DZ_three_zpow_succ (k : ℕ) :
    DZ ((3 : ℤ) ^ (k + 1)) = (3 : ℤ) ^ k := by
  rw [pow_succ, mul_comm]
  exact DZ_three_mul _

theorem Dpow_three_zpow (d m : ℕ) :
    Dpow d ((3 : ℤ) ^ m) = if d ≤ m then (3 : ℤ) ^ (m - d) else 0 := by
  induction d with
  | zero =>
    simp [Dpow]
  | succ d ih =>
    simp only [Dpow, ih]
    by_cases hle : d + 1 ≤ m
    · have hd : d ≤ m := Nat.le_of_succ_le hle
      rw [if_pos hd, if_pos hle]
      have hsplit : m - d = m - (d + 1) + 1 := by omega
      rw [hsplit, DZ_three_zpow_succ]
    · rw [if_neg hle]
      by_cases hd : d ≤ m
      · have heq : d = m := by omega
        subst heq
        simp [DZ_one]
      · simp [if_neg hd, DZ_zero]

theorem eval_nestD (k : ℕ) (t : OpFrag) (n : ℤ) :
    eval (nestD k t) n = Dpow k (eval t n) := by
  induction k with
  | zero => simp [nestD, Dpow]
  | succ k ih => simp [nestD, Dpow, eval, ih]

@[simp] theorem signFactor_false : signFactor false = 1 := rfl
@[simp] theorem signFactor_true : signFactor true = -1 := rfl

theorem signFactor_ne_zero (neg : Bool) : signFactor neg ≠ 0 := by
  cases neg <;> decide

theorem signFactor_mul_cancel {neg : Bool} {x y : ℤ}
    (h : signFactor neg * x = signFactor neg * y) : x = y := by
  cases neg <;> simp at h <;> linarith

theorem eval_mkCore (neg : Bool) (d : ℕ) (n : ℤ) :
    eval (mkCore neg d) n = signFactor neg * Dpow d n := by
  simp [mkCore, eval_nestD]
  cases neg <;> simp [eval, Dpow_neg]

theorem eval_wrap (ℓ : SpineLetter) (t : OpFrag) (n : ℤ) :
    eval (wrapLetter ℓ t) n = ℓ.toInt + 3 * eval t n := by
  cases ℓ <;> simp [wrapLetter, eval, IZ, SZ, SpineLetter.toInt, Trit.toInt]

theorem eval_applySpine (w : List SpineLetter) (t : OpFrag) (n : ℤ) :
    eval (applySpine w t) n = (3 : ℤ) ^ w.length * eval t n + coeff w := by
  induction w with
  | nil =>
    simp [applySpine, coeff]
  | cons ℓ w ih =>
    simp [applySpine, eval_wrap, coeff, ih, pow_succ]
    ring

theorem eval_mkNF (w : List SpineLetter) (neg : Bool) (d : ℕ) (n : ℤ) :
    eval (mkNF w neg d) n =
      signFactor neg * (3 : ℤ) ^ w.length * Dpow d n + coeff w := by
  simp [mkNF, eval_applySpine, eval_mkCore]
  ring

/-! ### Unique balanced word of a fixed length -/

theorem three_zpow_ne_zero (k : ℕ) : (3 : ℤ) ^ k ≠ 0 :=
  pow_ne_zero k (by decide : (3 : ℤ) ≠ 0)

theorem three_zpow_eq_one {k : ℕ} (h : (3 : ℤ) ^ k = 1) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    have hpow : (3 : ℤ) ^ (k + 1) = (3 : ℤ) ^ k * 3 := pow_succ _ _
    have hk : (0 : ℤ) < (3 : ℤ) ^ k := pow_pos (by decide : (0 : ℤ) < 3) k
    have hge : (3 : ℤ) ≤ (3 : ℤ) ^ (k + 1) := by
      rw [hpow]
      nlinarith
    linarith

theorem three_zpow_inj {a b : ℕ} (h : (3 : ℤ) ^ a = (3 : ℤ) ^ b) : a = b := by
  wlog hab : a ≤ b
  · exact (this h.symm (le_of_not_ge hab)).symm
  have hsplit : (3 : ℤ) ^ b = (3 : ℤ) ^ a * (3 : ℤ) ^ (b - a) := by
    rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hab]
  have : (3 : ℤ) ^ a * ((3 : ℤ) ^ (b - a) - 1) = 0 := by
    have := congrArg (fun z => z - (3 : ℤ) ^ a) h
    rw [hsplit] at this
    linarith
  have hrest : (3 : ℤ) ^ (b - a) - 1 = 0 :=
    (mul_eq_zero.mp this).resolve_left (three_zpow_ne_zero a)
  have : (3 : ℤ) ^ (b - a) = 1 := by linarith
  have : b - a = 0 := three_zpow_eq_one this
  omega

theorem three_zpow_pos (k : ℕ) : (0 : ℤ) < (3 : ℤ) ^ k :=
  pow_pos (by decide : (0 : ℤ) < 3) k

theorem three_zpow_ne_neg (a b : ℕ) : (3 : ℤ) ^ a ≠ -((3 : ℤ) ^ b) := by
  intro h
  have ha := three_zpow_pos a
  have hb := three_zpow_pos b
  have : (0 : ℤ) < -((3 : ℤ) ^ b) := by
    rw [← h]
    exact ha
  linarith

theorem coeff_eq_of_length {w w' : List SpineLetter}
    (hlen : w.length = w'.length) (hc : coeff w = coeff w') : w = w' := by
  induction w generalizing w' with
  | nil =>
    cases w' with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons ℓ w ih =>
    cases w' with
    | nil => simp at hlen
    | cons ℓ' w' =>
      simp [List.length_cons] at hlen
      simp [coeff] at hc
      have hmod : ℓ.toInt ≡ ℓ'.toInt [ZMOD 3] := by
        refine Int.modEq_iff_dvd.mpr ?_
        refine ⟨coeff w - coeff w', ?_⟩
        linarith
      have htrit :=
        trit_mod_unique (SpineLetter.toInt_is_trit ℓ)
          (SpineLetter.toInt_is_trit ℓ') hmod
      have hℓ : ℓ = ℓ' := SpineLetter.toInt_injective htrit
      subst hℓ
      have hrest : coeff w = coeff w' :=
        mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0) (by linarith)
      rw [ih hlen hrest]

/-! ### Distinct coordinates disagree as functions -/

theorem coeff_eq_of_eval {w w' : List SpineLetter} {neg neg' : Bool} {d d' : ℕ}
    (h : ∀ n, eval (mkNF w neg d) n = eval (mkNF w' neg' d') n) :
    coeff w = coeff w' := by
  simpa [eval_mkNF, Dpow_zero] using h 0

theorem scaled_eq_of_eval {w w' : List SpineLetter} {neg neg' : Bool} {d d' : ℕ}
    (h : ∀ n, eval (mkNF w neg d) n = eval (mkNF w' neg' d') n) (n : ℤ) :
    signFactor neg * (3 : ℤ) ^ w.length * Dpow d n =
      signFactor neg' * (3 : ℤ) ^ w'.length * Dpow d' n := by
  have hn := h n
  simp only [eval_mkNF, coeff_eq_of_eval h] at hn
  linarith

theorem Dpow_three_zpow_self (d : ℕ) : Dpow d ((3 : ℤ) ^ d) = 1 := by
  simp [Dpow_three_zpow]

theorem Dpow_three_zpow_of_lt {d m : ℕ} (h : m < d) :
    Dpow d ((3 : ℤ) ^ m) = 0 := by
  simp [Dpow_three_zpow, if_neg (not_le.mpr h)]

theorem Dpow_three_zpow_of_le {d m : ℕ} (h : d ≤ m) :
    Dpow d ((3 : ℤ) ^ m) = (3 : ℤ) ^ (m - d) := by
  simp [Dpow_three_zpow, if_pos h]

theorem eval_mkNF_inj {w w' : List SpineLetter} {neg neg' : Bool} {d d' : ℕ}
    (h : ∀ n, eval (mkNF w neg d) n = eval (mkNF w' neg' d') n) :
    w = w' ∧ neg = neg' ∧ d = d' := by
  have hc := coeff_eq_of_eval h
  by_cases hsign : neg = neg'
  · subst hsign
    by_cases hdep : d = d'
    · subst hdep
      have hprobe := scaled_eq_of_eval h ((3 : ℤ) ^ d)
      rw [Dpow_three_zpow_self] at hprobe
      have hpow : (3 : ℤ) ^ w.length = (3 : ℤ) ^ w'.length :=
        signFactor_mul_cancel (by simpa using hprobe)
      have hlen : w.length = w'.length := three_zpow_inj hpow
      exact ⟨coeff_eq_of_length hlen hc, rfl, rfl⟩
    · rcases lt_or_gt_of_ne hdep with hlt | hgt
      · have hprobe := scaled_eq_of_eval h ((3 : ℤ) ^ d)
        rw [Dpow_three_zpow_self, Dpow_three_zpow_of_lt hlt] at hprobe
        have : signFactor neg * (3 : ℤ) ^ w.length = 0 := by
          simpa using hprobe
        exact absurd this (mul_ne_zero (signFactor_ne_zero neg) (three_zpow_ne_zero _))
      · have hprobe := scaled_eq_of_eval h ((3 : ℤ) ^ d')
        rw [Dpow_three_zpow_of_lt hgt, Dpow_three_zpow_self] at hprobe
        have : signFactor neg * (3 : ℤ) ^ w'.length = 0 := by
          simpa using hprobe
        exact absurd this (mul_ne_zero (signFactor_ne_zero neg) (three_zpow_ne_zero _))
  · let M := max d d'
    have hprobe := scaled_eq_of_eval h ((3 : ℤ) ^ M)
    rw [Dpow_three_zpow_of_le (le_max_left d d'),
        Dpow_three_zpow_of_le (le_max_right d d')] at hprobe
    have hL :
        signFactor neg * (3 : ℤ) ^ w.length * (3 : ℤ) ^ (M - d) =
          signFactor neg * (3 : ℤ) ^ (w.length + (M - d)) := by
      rw [mul_assoc, ← pow_add]
    have hR :
        signFactor neg' * (3 : ℤ) ^ w'.length * (3 : ℤ) ^ (M - d') =
          signFactor neg' * (3 : ℤ) ^ (w'.length + (M - d')) := by
      rw [mul_assoc, ← pow_add]
    rw [hL, hR] at hprobe
    cases neg <;> cases neg' <;> simp [signFactor] at hsign hprobe
    · exact absurd hprobe (three_zpow_ne_neg _ _)
    · exact absurd hprobe.symm (three_zpow_ne_neg _ _)

/-! ### Soundness of the tree rules -/

theorem eval_step {t u : OpFrag} (h : Step t u) (n : ℤ) :
    eval t n = eval u n := by
  induction h generalizing n with
  | i0 =>
    simpa [eval] using rewrite_I0_S _
  | d_im =>
    simpa [eval] using rewrite_D_I Trit.minus _
  | d_ip =>
    simpa [eval] using rewrite_D_I Trit.plus _
  | d_i0 =>
    simpa [eval] using rewrite_D_I Trit.zero _
  | d_s =>
    simpa [eval] using rewrite_D_S _
  | n_n =>
    simp [eval]
  | n_s =>
    simpa [eval] using rewrite_N_S _
  | n_i0 =>
    simp [eval, rewrite_I0_S]
    exact rewrite_N_S _
  | n_im =>
    simpa [eval] using rewrite_N_Im _
  | n_ip =>
    simpa [eval] using rewrite_N_Ip _
  | n_d =>
    simpa [eval] using (rewrite_N_D _).symm
  | cong_D _hstep ih =>
    simp [eval, ih]
  | cong_Im _hstep ih =>
    simp [eval, ih]
  | cong_I0 _hstep ih =>
    simp [eval, ih]
  | cong_Ip _hstep ih =>
    simp [eval, ih]
  | cong_S _hstep ih =>
    simp [eval, ih]
  | cong_N _hstep ih =>
    simp [eval, ih]

theorem eval_rtc {t u : OpFrag} (h : ReflTransGen Step t u) (n : ℤ) :
    eval t n = eval u n := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    exact ih.trans (eval_step hstep n)

/-! ### Ledger claim: irreducibles are unique integer-function representatives -/

/-- Distinct irreducibles denote distinct maps `ℤ → ℤ`. -/
theorem irreducible_eval_injective {t u : OpFrag}
    (ht : Normal t) (hu : Normal u)
    (h : ∀ n : ℤ, eval t n = eval u n) : t = u := by
  have htN := isNF_of_normal ht
  have huN := isNF_of_normal hu
  have ht' := mkNF_of_isNF htN
  have hu' := mkNF_of_isNF huN
  have h' :
      ∀ n, eval (mkNF (spine t) (isNegCore (peel t)) (depthD (peel t))) n =
        eval (mkNF (spine u) (isNegCore (peel u)) (depthD (peel u))) n := by
    intro n
    simpa [ht'.symm, hu'.symm] using h n
  obtain ⟨hw, hb, hd⟩ := eval_mkNF_inj h'
  rw [ht', hu', hw, hb, hd]

/-- Semantically equal terms share the same irreducible. -/
theorem eval_eq_unique_nf {t u n₁ n₂ : OpFrag}
    (h : ∀ n, eval t n = eval u n)
    (hn₁ : Normal n₁) (hn₂ : Normal n₂)
    (ht : ReflTransGen Step t n₁) (hu : ReflTransGen Step u n₂) : n₁ = n₂ := by
  refine irreducible_eval_injective hn₁ hn₂ ?_
  intro n
  calc
    eval n₁ n = eval t n := (eval_rtc ht n).symm
    _ = eval u n := h n
    _ = eval n₂ n := eval_rtc hu n

end OpFrag
end BTCalculus
