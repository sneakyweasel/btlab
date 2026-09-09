import Problems.Juggler.ReturnCells
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Problems.Juggler.ReturnWordLoss

def step (b : Branch) (x : ℕ) : ℕ := (x ^ branchExp b).sqrt

def eval : List Branch → ℕ → ℕ
  | [], x => x
  | b :: w, x => eval w (step b x)

noncomputable def alpha (b : Branch) : ℝ := (branchExp b : ℝ) / 2

noncomputable def exponent : List Branch → ℝ
  | [] => 1
  | b :: w => alpha b * exponent w

def ConcaveTails : List Branch → Prop
  | [] => True
  | _ :: w => exponent w ≤ 1 ∧ ConcaveTails w

def InnerAbove (m : ℝ) : ℕ → List Branch → Prop
  | _, [] => True
  | x, b :: w => (w ≠ [] → m ≤ (step b x : ℝ)) ∧ InnerAbove m (step b x) w

noncomputable def budget (m : ℝ) : List Branch → ℝ
  | [] => 0
  | _ :: w => exponent w * m ^ (exponent w - 1) + budget m w

theorem exponent_pos (w : List Branch) : 0 < exponent w := by
  induction w with
  | nil => norm_num [exponent]
  | cons b w ih =>
    cases b <;> simp only [exponent, alpha, branchExp] <;> positivity

theorem eval_append (u v : List Branch) (x : ℕ) :
    eval (u ++ v) x = eval v (eval u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons b u ih => exact ih (step b x)

theorem exponent_append (u v : List Branch) :
    exponent (u ++ v) = exponent u * exponent v := by
  induction u with
  | nil => simp [exponent]
  | cons b u ih => simp [exponent, ih, mul_assoc]

theorem step_pos (b : Branch) {x : ℕ} (hx : 0 < x) : 0 < step b x := by
  exact Nat.sqrt_pos.mpr (pow_pos hx _)

theorem eval_pos (w : List Branch) {x : ℕ} (hx : 0 < x) : 0 < eval w x := by
  induction w generalizing x with
  | nil => exact hx
  | cons b w ih => exact ih (step_pos b hx)

theorem step_mono (b : Branch) : Monotone (step b) := by
  intro x y hxy
  exact Nat.sqrt_le_sqrt (Nat.pow_le_pow_left hxy _)

theorem eval_mono (w : List Branch) : Monotone (eval w) := by
  induction w with
  | nil => exact monotone_id
  | cons b w ih => exact ih.comp (step_mono b)

theorem eval_eq_image {x : ℕ} {w : List Branch} (hw : follows x w) :
    eval w x = image x w := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    have hs : step b x = floorPower x := by
      cases b with
      | even => simpa [step, branchExp] using (floorPower_even_eq hw.1).symm
      | odd => simpa [step, branchExp] using (floorPower_odd_eq hw.1).symm
    have hw' : follows (floorPower x) w := by cases b <;> exact hw.2
    simpa only [eval, image, hs] using ih hw'

theorem step_cell (b : Branch) (x : ℕ) :
    (step b x : ℝ) ≤ (x : ℝ) ^ alpha b ∧
      (x : ℝ) ^ alpha b < (step b x : ℝ) + 1 := by
  have hsq : ((x : ℝ) ^ alpha b) ^ 2 = (x ^ branchExp b : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg x)]
    simp [alpha]
  have hlo : (step b x : ℝ) ^ 2 ≤ (x ^ branchExp b : ℕ) := by
    exact_mod_cast Nat.sqrt_le' (x ^ branchExp b)
  have hhi : (x ^ branchExp b : ℕ) < ((step b x : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (x ^ branchExp b)
  have hr : 0 ≤ (x : ℝ) ^ alpha b := Real.rpow_nonneg (Nat.cast_nonneg x) _
  have hn : 0 ≤ (step b x : ℝ) := Nat.cast_nonneg _
  constructor <;> nlinarith

theorem rpow_sub_le {x y q : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    y ^ q - x ^ q ≤ q * x ^ (q - 1) * (y - x) := by
  have hs : -1 ≤ (y - x) / x := le_trans (by norm_num) (div_nonneg (sub_nonneg.mpr hxy) hx.le)
  have hb := rpow_one_add_le_one_add_mul_self hs hq0 hq1
  have hf : x * (1 + (y - x) / x) = y := by field_simp; ring
  have hh := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx.le q)
  have hp : x ^ q * (1 + (y - x) / x) ^ q = y ^ q := by
    rw [← Real.mul_rpow hx.le (by positivity), hf]
  rw [hp] at hh
  rw [Real.rpow_sub_one hx.ne']
  have hid : x ^ q * (1 + q * ((y - x) / x)) =
      x ^ q + q * (x ^ q / x) * (y - x) := by ring
  rw [hid] at hh
  linarith only [hh]

theorem eval_le_rpow (w : List Branch) (x : ℕ) :
    (eval w x : ℝ) ≤ (x : ℝ) ^ exponent w := by
  induction w generalizing x with
  | nil => simp [eval, exponent]
  | cons b w ih =>
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg (step b x))
      (step_cell b x).1 (exponent_pos w).le
    rw [← Real.rpow_mul (Nat.cast_nonneg x)] at hh
    exact (ih (step b x)).trans hh

theorem local_loss_lt {m : ℝ} (hm : 0 < m) (b : Branch) {x : ℕ}
    (hx : 0 < x) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hy : m ≤ (step b x : ℝ)) :
    ((x : ℝ) ^ alpha b) ^ q - (step b x : ℝ) ^ q < q * m ^ (q - 1) := by
  have hs := step_cell b x
  have hy0 : (0 : ℝ) < step b x := by exact_mod_cast step_pos b hx
  have hc := rpow_sub_le hy0 hs.1 hq0.le hq1
  have hcoef : 0 < q * (step b x : ℝ) ^ (q - 1) := by positivity
  have hlt := mul_lt_mul_of_pos_left (show (x : ℝ) ^ alpha b - step b x < 1 by linarith) hcoef
  have hm' := Real.rpow_le_rpow_of_nonpos hm hy (by linarith : q - 1 ≤ 0)
  have hh := mul_le_mul_of_nonneg_left hm' hq0.le
  nlinarith only [hc, hlt, hh]

theorem loss_le_budget {m : ℝ} (hm : 0 < m) (w : List Branch)
    {x : ℕ} (hx : 0 < x) (ht : ConcaveTails w) (ha : InnerAbove m x w) :
    (x : ℝ) ^ exponent w - (eval w x : ℝ) ≤ budget m w := by
  induction w generalizing x with
  | nil => simp [eval, exponent, budget]
  | cons b w ih =>
    by_cases hw : w = []
    · subst w
      have hs := (step_cell b x).2
      simpa [eval, exponent, budget] using (show (x : ℝ) ^ alpha b - step b x ≤ 1 by linarith)
    · have hh := ih (step_pos b hx) ht.2 ha.2
      have hl := local_loss_lt hm b hx (exponent_pos w) ht.1 (ha.1 hw)
      rw [← Real.rpow_mul (Nat.cast_nonneg x)] at hl
      change (x : ℝ) ^ (alpha b * exponent w) - (eval w (step b x) : ℝ) ≤
        exponent w * m ^ (exponent w - 1) + budget m w
      linarith

theorem loss_lt_budget {m : ℝ} (hm : 0 < m) {w : List Branch}
    (hw : w ≠ []) {x : ℕ} (hx : 0 < x)
    (ht : ConcaveTails w) (ha : InnerAbove m x w) :
    (x : ℝ) ^ exponent w - (eval w x : ℝ) < budget m w := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons b w =>
    by_cases hnil : w = []
    · subst w
      have hs := (step_cell b x).2
      simpa [eval, exponent, budget] using (show (x : ℝ) ^ alpha b - step b x < 1 by linarith)
    · have hh := loss_le_budget hm w (step_pos b hx) ht.2 ha.2
      have hl := local_loss_lt hm b hx (exponent_pos w) ht.1 (ha.1 hnil)
      rw [← Real.rpow_mul (Nat.cast_nonneg x)] at hl
      change (x : ℝ) ^ (alpha b * exponent w) - (eval w (step b x) : ℝ) <
        exponent w * m ^ (exponent w - 1) + budget m w
      linarith

theorem paired_bound {m : ℝ} (hm : 0 < m) {w : List Branch} (hw : w ≠ [])
    (ht : ConcaveTails w) (hp : exponent w ≤ 1) {x y : ℕ}
    (hx : 0 < x) (hmx : m ≤ x) (hxy : x ≤ y) (ha : InnerAbove m x w) :
    (eval w y : ℝ) - eval w x <
      exponent w * m ^ (exponent w - 1) * ((y : ℝ) - x) + budget m w := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have he := loss_lt_budget hm hw hx ht ha
  have hu := eval_le_rpow w y
  have hg := rpow_sub_le hx0 hxy' (exponent_pos w).le hp
  have hc := Real.rpow_le_rpow_of_nonpos hm hmx (by linarith : exponent w - 1 ≤ 0)
  have hc' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (exponent_pos w).le) (sub_nonneg.mpr hxy')
  linarith

theorem innerAbove_append {m : ℝ} (u v : List Branch) (x : ℕ)
    (hu : InnerAbove m x u) (hv : InnerAbove m (eval u x) v)
    (hend : v ≠ [] → m ≤ (eval u x : ℝ)) : InnerAbove m x (u ++ v) := by
  induction u generalizing x with
  | nil => exact hv
  | cons b u ih =>
    change (_ ∧ _) at hu ⊢
    constructor
    · intro hne
      by_cases hu0 : u = []
      · subst u
        exact hend (by simpa using hne)
      · exact hu.1 hu0
    · exact ih (step b x) hu.2 hv hend

noncomputable def transportedLoss (x : ℕ) : List Branch → ℝ
  | [] => 0
  | b :: w => ((x : ℝ) ^ alpha b) ^ exponent w - (step b x : ℝ) ^ exponent w +
      transportedLoss (step b x) w

theorem loss_exact (w : List Branch) (x : ℕ) :
    (x : ℝ) ^ exponent w - (eval w x : ℝ) = transportedLoss x w := by
  induction w generalizing x with
  | nil => simp [exponent, eval, transportedLoss]
  | cons b w ih =>
    simp only [exponent, eval, transportedLoss, ← ih]
    rw [← Real.rpow_mul (Nat.cast_nonneg x)]
    ring

def DyadicCertificate (k : ℕ) : List Branch → List ℕ → Prop
  | [], [] => True
  | _ :: w, h :: hs => (h : ℝ) ≤ k * (1 - exponent w) ∧ DyadicCertificate k w hs
  | _, _ => False

noncomputable def dyadicSum : List Branch → List ℕ → ℝ
  | [], _ => 0
  | _ :: w, h :: hs => exponent w / (2 : ℝ) ^ h + dyadicSum w hs
  | _, [] => 0

theorem dyadic_term_le {m q : ℝ} {k h : ℕ} (hm : (2 : ℝ) ^ k ≤ m)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hh : (h : ℝ) ≤ k * (1 - q)) :
    q * m ^ (q - 1) ≤ q / (2 : ℝ) ^ h := by
  have h₁ := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 2 ^ k)
    hm (by linarith : q - 1 ≤ 0)
  have he : ((2 : ℝ) ^ k) ^ (q - 1) = (2 : ℝ) ^ ((k : ℝ) * (q - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [he] at h₁
  have h₂ := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (show (k : ℝ) * (q - 1) ≤ -(h : ℝ) by linarith)
  have h₃ : m ^ (q - 1) ≤ ((2 : ℝ) ^ h)⁻¹ := by
    simpa only [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast] using h₁.trans h₂
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h₃ hq0

theorem budget_le_dyadic {m : ℝ} {k : ℕ} (hm : (2 : ℝ) ^ k ≤ m)
    (w : List Branch) (hs : List ℕ) (ht : ConcaveTails w)
    (hc : DyadicCertificate k w hs) : budget m w ≤ dyadicSum w hs := by
  induction w generalizing hs with
  | nil => simp [budget, dyadicSum]
  | cons b w ih =>
    cases hs with
    | nil => exact False.elim hc
    | cons h hs =>
      exact add_le_add (dyadic_term_le hm (exponent_pos w).le ht.1 hc.1) (ih hs ht.2 hc.2)

theorem dyadic_rpow_lower {m q c : ℝ} {k a b : ℕ}
    (hm : (2 : ℝ) ^ k ≤ m) (hq : 0 ≤ q)
    (he : (a : ℝ) ≤ (k : ℝ) * q * (b : ℝ))
    (hc : c ^ b < (2 : ℝ) ^ a) : c < m ^ q := by
  have hm0 : 0 ≤ m := (by positivity : (0 : ℝ) ≤ 2 ^ k).trans hm
  have h₁ := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ k) hm hq
  have h₂ := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ q) h₁ b
  have hiden : (((2 : ℝ) ^ k) ^ q) ^ b = (2 : ℝ) ^ ((k : ℝ) * q * (b : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hiden] at h₂
  have h₃ := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  rw [Real.rpow_natCast] at h₃
  exact lt_of_pow_lt_pow_left₀ b (Real.rpow_nonneg hm0 q) (hc.trans_le (h₃.trans h₂))

end Problems.Juggler.ReturnWordLoss
