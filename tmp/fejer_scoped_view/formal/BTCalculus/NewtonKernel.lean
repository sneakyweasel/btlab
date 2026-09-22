import BTCalculus.PolynomialFunctionsMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas

noncomputable section

namespace BTCalculus

open Polynomial Finset

/-!
Newton / binomial coefficients of an ordinary ``Z[X]`` polynomial, and
the classical kernel of polynomial functions modulo ``3^k``.

  ``h in I_k  iff  ∀ j,  3^k divides Delta^j h(0)``.

This is the missing general-degree half of ``equivK_iff_functionCongr``.
-/

def fwdDiff (h : ℤ → ℤ) (n : ℤ) : ℤ :=
  h (n + 1) - h n

def iterFwdDiff : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, h => h
  | j + 1, h => iterFwdDiff j (fwdDiff h)

def newtonCoeff (j : ℕ) (f : ℤ[X]) : ℤ :=
  iterFwdDiff j (fun n => eval n f) 0

def polyFwdDiff (f : ℤ[X]) : ℤ[X] :=
  f.comp (X + C 1) - f

def newtonKernel (k : ℕ) (h : ℤ[X]) : Prop :=
  ∀ j : ℕ, (3 : ℤ) ^ k ∣ newtonCoeff j h

theorem newtonCoeff_zero (f : ℤ[X]) : newtonCoeff 0 f = eval 0 f :=
  rfl

theorem eval_polyFwdDiff (f : ℤ[X]) (n : ℤ) :
    eval n (polyFwdDiff f) = eval (n + 1) f - eval n f := by
  simp [polyFwdDiff, eval_sub, eval_comp, eval_add, eval_X]

theorem fwdDiff_eval (f : ℤ[X]) :
    fwdDiff (fun m => eval m f) = fun n => eval n (polyFwdDiff f) := by
  funext n
  simp [fwdDiff, eval_polyFwdDiff]

theorem newtonCoeff_succ (j : ℕ) (f : ℤ[X]) :
    newtonCoeff (j + 1) f = newtonCoeff j (polyFwdDiff f) := by
  simp [newtonCoeff, iterFwdDiff, fwdDiff_eval]

theorem eval_eq_eval_zero_of_natDegree_le_zero {f : ℤ[X]}
    (h : f.natDegree ≤ 0) (n : ℤ) : eval n f = eval 0 f := by
  rw [eq_C_of_natDegree_le_zero h, eval_C, eval_C]

lemma iterFwdDiff_dvd {m : ℤ} {h : ℤ → ℤ} (hh : ∀ n, m ∣ h n) :
    ∀ j n, m ∣ iterFwdDiff j h n
  | 0, n => hh n
  | j + 1, n =>
    iterFwdDiff_dvd (fun t => (hh (t + 1)).sub (hh t)) j n

theorem newtonKernel_of_vanishesMod (k : ℕ) (h : ℤ[X])
    (hv : vanishesMod k h) : newtonKernel k h := by
  intro j
  exact iterFwdDiff_dvd hv j 0

lemma eval_nat_rec (f : ℤ[X]) :
    ∀ n : ℕ,
      eval (n : ℤ) f =
        eval 0 f + ∑ t ∈ range n, eval (t : ℤ) (polyFwdDiff f)
  | 0 => by simp
  | n + 1 => by
    have ih := eval_nat_rec f n
    have hDelta := eval_polyFwdDiff f n
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := Nat.cast_succ n
    rw [hcast, sum_range_succ]
    linarith [ih, hDelta]

lemma eval_neg_rec (f : ℤ[X]) :
    ∀ m : ℕ,
      eval (-(m : ℤ)) f =
        eval 0 f - ∑ t ∈ range m, eval (-((t : ℤ) + 1)) (polyFwdDiff f)
  | 0 => by simp
  | m + 1 => by
    have ih := eval_neg_rec f m
    have hDelta := eval_polyFwdDiff f (-((m : ℤ) + 1))
    have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := Nat.cast_succ m
    have hsimp : -((m : ℤ) + 1) + 1 = -(m : ℤ) := by ring
    have hstep :
        eval (-((m : ℤ) + 1)) f =
          eval (-(m : ℤ)) f - eval (-((m : ℤ) + 1)) (polyFwdDiff f) := by
      rw [hsimp] at hDelta
      linarith
    rw [hcast, hstep, ih, sum_range_succ]
    ring

lemma natDegree_comp_X_add_one (f : ℤ[X]) :
    natDegree (f.comp (X + C 1)) = f.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

lemma leadingCoeff_comp_X_add_one (f : ℤ[X]) :
    leadingCoeff (f.comp (X + C 1)) = leadingCoeff f := by
  rw [leadingCoeff_comp (by
      rw [natDegree_X_add_C]
      exact Nat.one_ne_zero),
    leadingCoeff_X_add_C, one_pow, mul_one]

lemma natDegree_polyFwdDiff_lt {f : ℤ[X]} (hd : 0 < f.natDegree) :
    (polyFwdDiff f).natDegree < f.natDegree := by
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hd
  have hcomp : natDegree (f.comp (X + C 1)) = f.natDegree :=
    natDegree_comp_X_add_one f
  have hlc : leadingCoeff (f.comp (X + C 1)) = leadingCoeff f :=
    leadingCoeff_comp_X_add_one f
  have hcomp0 : f.comp (X + C 1) ≠ 0 := by
    intro h
    have : natDegree (f.comp (X + C 1)) = 0 := by
      rw [h, natDegree_zero]
    rw [hcomp] at this
    omega
  have hdeg_eq : degree (f.comp (X + C 1)) = degree f := by
    rw [degree_eq_natDegree hcomp0, degree_eq_natDegree hf0, hcomp]
  have hlt := degree_sub_lt_left hdeg_eq hcomp0 hlc
  rw [hdeg_eq] at hlt
  by_cases hD : polyFwdDiff f = 0
  · simp [hD]
    exact hd
  · have : degree (polyFwdDiff f) < degree f := by
      simpa [polyFwdDiff] using hlt
    rw [degree_eq_natDegree hD, degree_eq_natDegree hf0] at this
    exact WithBot.coe_lt_coe.mp this

lemma polyFwdDiff_sub (f g : ℤ[X]) :
    polyFwdDiff (f - g) = polyFwdDiff f - polyFwdDiff g := by
  simp [polyFwdDiff, sub_comp]
  ring

lemma vanishesMod_of_newtonKernel_aux (k : ℕ) :
    ∀ d : ℕ, ∀ f : ℤ[X],
      f.natDegree ≤ d →
        (∀ j, (3 : ℤ) ^ k ∣ newtonCoeff j f) → vanishesMod k f
  | 0, f, hdeg, hN => by
    intro n
    have : eval n f = eval 0 f := eval_eq_eval_zero_of_natDegree_le_zero hdeg n
    rw [this]
    simpa [newtonCoeff_zero] using hN 0
  | d + 1, f, hdeg, hN => by
    intro n
    by_cases hconst : f.natDegree = 0
    · have : eval n f = eval 0 f :=
        eval_eq_eval_zero_of_natDegree_le_zero (by omega) n
      rw [this]
      simpa [newtonCoeff_zero] using hN 0
    · have hdpos : 0 < f.natDegree := Nat.pos_of_ne_zero hconst
      have hDdeg : (polyFwdDiff f).natDegree ≤ d := by
        have := natDegree_polyFwdDiff_lt hdpos
        omega
      have hDN : ∀ j, (3 : ℤ) ^ k ∣ newtonCoeff j (polyFwdDiff f) := by
        intro j
        simpa [newtonCoeff_succ] using hN (j + 1)
      have hD := vanishesMod_of_newtonKernel_aux k d (polyFwdDiff f) hDdeg hDN
      cases n with
      | ofNat m =>
        have hm : (Int.ofNat m : ℤ) = (m : ℤ) := rfl
        rw [hm, eval_nat_rec]
        refine dvd_add (by simpa [newtonCoeff_zero] using hN 0) ?_
        exact dvd_sum fun t _ => hD (t : ℤ)
      | negSucc m =>
        have hn : (Int.negSucc m : ℤ) = -((m : ℤ) + 1) := Int.negSucc_eq m
        have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := Nat.cast_succ m
        have hrec := eval_neg_rec f (m + 1)
        rw [hcast] at hrec
        rw [hn, hrec]
        have h0 : (3 : ℤ) ^ k ∣ eval 0 f := by
          simpa [newtonCoeff_zero] using hN 0
        exact h0.sub (dvd_sum fun t _ => hD _)

theorem vanishesMod_iff_newtonKernel (k : ℕ) (h : ℤ[X]) :
    vanishesMod k h ↔ newtonKernel k h := by
  constructor
  · exact newtonKernel_of_vanishesMod k h
  · intro hN
    exact vanishesMod_of_newtonKernel_aux k h.natDegree h le_rfl hN

theorem newtonCoeff_sub (j : ℕ) (f g : ℤ[X]) :
    newtonCoeff j (f - g) = newtonCoeff j f - newtonCoeff j g := by
  induction j generalizing f g with
  | zero =>
    simp [newtonCoeff, iterFwdDiff, eval_sub]
  | succ j ih =>
    rw [newtonCoeff_succ, newtonCoeff_succ, newtonCoeff_succ, polyFwdDiff_sub, ih]

theorem equivK_iff_newtonKernel (k : ℕ) (f g : ℤ[X]) :
    equivK k f g ↔ newtonKernel k (f - g) := by
  rw [equivK_iff_functionCongr, functionCongr_iff_vanishesMod,
    vanishesMod_iff_newtonKernel]

theorem equivK_iff_newtonCoeff (k : ℕ) (f g : ℤ[X]) :
    equivK k f g ↔
      ∀ j, newtonCoeff j f ≡ newtonCoeff j g [ZMOD (3 : ℤ) ^ k] := by
  rw [equivK_iff_newtonKernel]
  constructor
  · intro h j
    have hf : (3 : ℤ) ^ k ∣ newtonCoeff j f - newtonCoeff j g := by
      simpa [newtonCoeff_sub] using h j
    exact Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using dvd_neg.mpr hf)
  · intro h j
    have hf : (3 : ℤ) ^ k ∣ newtonCoeff j g - newtonCoeff j f :=
      Int.modEq_iff_dvd.mp (h j)
    simpa [newtonCoeff_sub, neg_sub] using (dvd_neg.mpr hf)

end BTCalculus
