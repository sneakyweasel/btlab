import Problems.Juggler.ReturnRankedCycle
import Problems.Juggler.ReturnWordData

namespace Problems.Juggler.ReturnSeams

open ReturnWordLoss ReturnWordBounds

theorem image_lt_of_exponent {w : List Branch} (hp : exponent w < 1)
    {x : ℕ} (hx : 1 < x) (hw : follows x w) : image x w < x := by
  have hxR : (1 : ℝ) < x := by exact_mod_cast hx
  have hb := eval_le_rpow w x
  have hr := Real.rpow_lt_rpow_of_exponent_lt hxR hp
  rw [Real.rpow_one] at hr
  rw [eval_eq_image hw] at hb
  exact_mod_cast hb.trans_lt hr

namespace RankedReturn

variable {a b m : ℕ} {y : ℕ → ℕ} {U V : List Branch}
variable (h : RankedReturn a b y U V)
include h

/-- Two left steps and the following direction change, including terminal exclusion. -/
theorem force_two_left (ha : 0 < a) (hb : 0 < b) (hm : m ≤ y 0)
    (hd₁ : ∀ x, m ≤ x → follows x (U ++ V) → image x (U ++ V) < x)
    (hd₂ : ∀ x, m ≤ x → follows x (U ++ (U ++ V)) →
      image x (U ++ (U ++ V)) < x)
    (hg : ∀ x, m ≤ x → follows x (U ++ (U ++ (U ++ V))) →
      x < image x (U ++ (U ++ (U ++ V)))) :
    2 * b < a ∧ a < 3 * b ∧
      RankedReturn (a - 2 * b) b y U (U ++ (U ++ V)) := by
  have h₁ : b < a := h.lt_of_concat_decreases hm ha hd₁
  have R₁ := h.left h₁.le
  have h₂ : b < a - b := R₁.lt_of_concat_decreases hm (by omega) hd₂
  have R₂ := R₁.left h₂.le
  have h₃ : a - b - b < b := R₂.lt_of_concat_grows hm hb hg
  refine ⟨by omega, by omega, ?_⟩
  simpa only [show a - b - b = a - 2 * b by omega] using R₂

/-- Two right steps and the following direction change, with positive remainder. -/
theorem force_two_right (ha : 0 < a) (hab : a < b) (hm : m ≤ y 0)
    (hg : ∀ x, m ≤ x → follows x ((U ++ V) ++ V) →
      x < image x ((U ++ V) ++ V))
    (hd : ∀ x, m ≤ x → follows x (((U ++ V) ++ V) ++ V) →
      image x (((U ++ V) ++ V) ++ V) < x) :
    2 * a < b ∧ b < 3 * a ∧
      RankedReturn a (b - 2 * a) y ((U ++ V) ++ V) V := by
  have R₁ := h.right hab.le
  have h₂ : a < b - a := R₁.lt_of_concat_grows hm (by omega) hg
  have R₂ := R₁.right h₂.le
  have h₃ : b - a - a < a := R₂.lt_of_concat_decreases hm ha hd
  refine ⟨by omega, by omega, ?_⟩
  simpa only [show b - a - a = b - 2 * a by omega] using R₂

/-- Three left steps followed by a genuine right step. -/
theorem force_three_left (hb : 0 < b) (hba : b < a) (hm : m ≤ y 0)
    (hd₂ : ∀ x, m ≤ x → follows x (U ++ (U ++ V)) →
      image x (U ++ (U ++ V)) < x)
    (hd₃ : ∀ x, m ≤ x → follows x (U ++ (U ++ (U ++ V))) →
      image x (U ++ (U ++ (U ++ V))) < x)
    (hg : ∀ x, m ≤ x → follows x (U ++ (U ++ (U ++ (U ++ V)))) →
      x < image x (U ++ (U ++ (U ++ (U ++ V))))) :
    3 * b < a ∧ a < 4 * b ∧
      RankedReturn (a - 3 * b) b y U (U ++ (U ++ (U ++ V))) := by
  have R₁ := h.left hba.le
  have h₂ : b < a - b := R₁.lt_of_concat_decreases hm (by omega) hd₂
  have R₂ := R₁.left h₂.le
  have h₃ : b < a - b - b := R₂.lt_of_concat_decreases hm (by omega) hd₃
  have R₃ := R₂.left h₃.le
  have h₄ : a - b - b - b < b := R₃.lt_of_concat_grows hm hb hg
  refine ⟨by omega, by omega, ?_⟩
  simpa only [show a - b - b - b = a - 3 * b by omega] using R₃

end RankedReturn

/-- The first two accelerated batches are forced by exact map inequalities. -/
theorem dc_rank_stages {a b m : ℕ} {y : ℕ → ℕ}
    (h : RankedReturn a b y wordA wordB) (ha : 0 < a) (hb : 0 < b)
    (hm : 2 ^ 24 ≤ m) (hy : m ≤ y 0) :
    ∃ r s, 0 < s ∧ s < r ∧ r < b ∧ a = 2 * b + r ∧ b = 2 * r + s ∧
      RankedReturn r b y wordA wordC ∧ RankedReturn r s y wordD wordC := by
  have hx1 : ∀ x : ℕ, m ≤ x → 1 < x := by intro x hx; omega
  obtain ⟨h₂, h₃, H₂⟩ := h.force_two_left ha hb hy
    (fun x hx hf => image_lt_of_exponent (by
      norm_num [exponent_append, exponent_A, exponent_B]) (hx1 x hx) hf)
    (fun x hx hf => image_lt_of_exponent (by
      norm_num [exponent_append, exponent_A, exponent_B]) (hx1 x hx) hf)
    (by
      intro x hx hf
      have hg := ac_grows (hm.trans hx)
      have he : wordA ++ wordA ++ (wordA ++ wordB) = wordA ++ wordC := by
        simp only [wordC, List.append_assoc]
      simpa only [← eval_eq_image hf, wordC, List.append_assoc] using hg)
  have HC : RankedReturn (a - 2 * b) b y wordA wordC := by
    simpa only [wordC, List.append_assoc] using H₂
  obtain ⟨h₄, h₅, H₄⟩ := HC.force_two_right (by omega) (by omega) hy
    (by
      intro x hx hf
      have hg := d_grows (hm.trans hx)
      simpa only [← eval_eq_image hf, wordD] using hg)
    (fun x hx hf => image_lt_of_exponent (by
      norm_num [exponent_append, exponent_A, exponent_C]) (hx1 x hx) hf)
  refine ⟨a - 2 * b, b - 2 * (a - 2 * b), by omega, by omega, by omega,
    by omega, by omega, HC, ?_⟩
  simpa only [wordD] using H₄

/-- The next left batch has exactly three steps and excludes its terminal equality. -/
theorem lr_rank_stage {r s m : ℕ} {y : ℕ → ℕ}
    (h : RankedReturn r s y wordD wordC) (hs : 0 < s) (hsr : s < r)
    (hm : 2 ^ 128 ≤ m) (hy : m ≤ y 0) :
    ∃ u, 0 < u ∧ u < s ∧ r = 3 * s + u ∧ RankedReturn u s y wordD wordW := by
  have hx1 : ∀ x : ℕ, m ≤ x → 1 < x := by intro x hx; omega
  obtain ⟨h₃, h₄, H₃⟩ := h.force_three_left hs hsr hy
    (fun x hx hf => image_lt_of_exponent (by
      norm_num [exponent_append, exponent_D, exponent_C]) (hx1 x hx) hf)
    (fun x hx hf => image_lt_of_exponent (by
      norm_num [exponent_append, exponent_D, exponent_C]) (hx1 x hx) hf)
    (by
      intro x hx hf
      have hg := v_grows (hm.trans hx)
      simpa only [← eval_eq_image hf, wordV, List.append_assoc] using hg)
  refine ⟨r - 3 * s, by omega, by omega, by omega, ?_⟩
  simpa only [wordW, List.append_assoc] using H₃

end Problems.Juggler.ReturnSeams
