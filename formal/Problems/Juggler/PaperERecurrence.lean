import Problems.Juggler.PaperEModularReturn
import BTCalculus.PowerBoxRecurrence

/-! # Unconditional recurrence and Paper E Theorem 4.1

The distinct positive exponents 3^a/2^(j+1) are noninteger, since their
numerators are odd and their denominators are even. The mixed-power
recurrence theorem supplies the actual box used by the floor construction.
-/

namespace Problems.Juggler.PaperERecurrence

noncomputable section

open PaperEModularReturn
open BTCalculus.PowerBoxRecurrence

/-- Each denominator contains a factor of two, while the numerator is odd. -/
theorem power_exponent_noninteger (a j : ℕ) :
    0 < (3 ^ a : ℝ) / 2 ^ (j + 1) ∧
      ∀ m : ℕ, (3 ^ a : ℝ) / 2 ^ (j + 1) ≠ (m : ℝ) := by
  refine ⟨by positivity, ?_⟩
  intro m hm
  have he : (3 ^ a : ℝ) = (m : ℝ) * 2 ^ (j + 1) :=
    (div_eq_iff (by positivity : (2 : ℝ) ^ (j + 1) ≠ 0)).mp hm
  have hn : (3 : ℕ) ^ a = m * 2 ^ (j + 1) := by exact_mod_cast he
  have hmod := congrArg (fun n : ℕ => n % 2) hn
  norm_num [Nat.mul_mod, Nat.pow_mod, pow_succ] at hmod

/-- Different root depths give distinct real exponents. -/
theorem power_exponent_injective (a b : ℕ) :
    Function.Injective (fun j : Fin (b + 1) => (3 ^ a : ℝ) / 2 ^ (j.val + 1)) := by
  intro i j hij
  have hcross := (div_eq_div_iff
    (by positivity : (2 : ℝ) ^ (i.val + 1) ≠ 0)
    (by positivity : (2 : ℝ) ^ (j.val + 1) ≠ 0)).mp hij
  have hd : (2 : ℝ) ^ (i.val + 1) = 2 ^ (j.val + 1) :=
    (mul_left_cancel₀ (by positivity : (3 : ℝ) ^ a ≠ 0) hcross).symm
  have he := (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective hd
  apply Fin.ext
  omega

/-- The precise box in the exact floor construction is recurrent without further hypotheses. -/
theorem box_recurrence (a b M : ℕ) (hM : 0 < M) : BoxRecurrence a b M := by
  classical
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  let p : Fin (b + 1) → ℝ := fun j => (3 ^ a : ℝ) / 2 ^ (j.val + 1)
  let w : Fin (b + 1) → ℝ := fun j => if j.val = b then 1 / (2 * M) else 1 / 2
  let lo : Fin (b + 1) → ℝ := fun j => if j.val = b then 1 / (2 * M) else 0
  let hi : Fin (b + 1) → ℝ := fun j => if j.val = b then 2 / (2 * M) else 1 / 2
  have hw : ∀ j, w j ≠ 0 := by
    intro j
    dsimp [w]
    split_ifs <;> positivity
  have hlo : ∀ j, 0 ≤ lo j := by
    intro j
    dsimp [lo]
    split_ifs <;> positivity
  have hhi : ∀ j, hi j ≤ 1 := by
    intro j
    dsimp [hi]
    split_ifs
    · apply (div_le_one (by positivity : (0 : ℝ) < 2 * M)).2
      have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    · norm_num
  have hbox : ∀ j, lo j < hi j := by
    intro j
    dsimp [lo, hi]
    split_ifs
    · exact div_lt_div_of_pos_right (by norm_num) (by positivity)
    · norm_num
  intro T
  obtain ⟨t, ht, hmem⟩ := exists_ge_power_fract_box p w
    (power_exponent_injective a b) (fun j => power_exponent_noninteger a j.val)
    hw (show (0 : ℝ) < 2 * M by positivity) 1 lo hi hlo hhi hbox T
  have hs : (2 : ℝ) * M * t + 1 = ((1 + 2 * M * t : ℕ) : ℝ) := by push_cast; ring
  have hlast := hmem ⟨b, by omega⟩
  have hlast' : (1 : ℝ) / (2 * M) <
      Int.fract (powerValue (1 + 2 * M * t) a b / (2 * M)) ∧
      Int.fract (powerValue (1 + 2 * M * t) a b / (2 * M)) < 2 / (2 * M) := by
    simpa only [p, w, lo, hi, if_pos rfl, hs, one_div_mul_eq_div, powerValue] using hlast
  refine ⟨t, ht, hlast'.1.le, hlast'.2, ?_⟩
  intro j hj
  have hm := (hmem ⟨j, by omega⟩).2
  have hjb : j ≠ b := by omega
  simpa only [p, w, hi, if_neg hjb, hs, one_div_mul_eq_div, powerValue] using hm

/-- The complete unconditional statement of Paper E Theorem 4.1. -/
theorem theorem41 {a b M : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (hex : 2 ^ (a + b) < 3 ^ a) :
    (∀ B : ℕ, {n : ℕ | B < n ∧ ModularReturn a b M n}.Infinite) ∧
    (runCode a b).den = (3 ^ a - 2 ^ (a + b)) / Nat.gcd (3 ^ a - 2 ^ a) (2 ^ b - 1) ∧
    (∀ Q : ℕ, ∃ A : ℕ, 0 < A ∧ 2 ^ (A + b) < 3 ^ A ∧ Q < (runCode A b).den) :=
  theorem41_of_box_recurrence ha hb hM hex (box_recurrence a b M hM)

end

end Problems.Juggler.PaperERecurrence
