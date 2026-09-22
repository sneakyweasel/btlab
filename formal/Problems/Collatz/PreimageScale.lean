import Problems.Collatz.BackwardMass

/-!
# Residue symmetry does not preserve the predecessor height comparison

The negative shortcut has odd predecessor `(2*a+1)/3`, above `2*a/3`.
The positive shortcut has odd predecessor `(2*a-1)/3`, below it. The
common homogeneous residue program therefore needs a separate justification
before it can bound actual negative-shortcut preimage counts.
-/

namespace Problems.Collatz.PreimageScale

def minusOddPreimage (a : ℕ) : ℕ := (2 * a + 1) / 3
def plusOddPreimage (a : ℕ) : ℕ := (2 * a - 1) / 3

theorem minus_preimage_exact {a : ℕ} (ha : a % 3 = 1) :
    3 * minusOddPreimage a = 2 * a + 1 ∧
    minusOddPreimage a % 2 = 1 ∧ negT (minusOddPreimage a) = a := by
  have he : 3 * minusOddPreimage a = 2 * a + 1 := by
    unfold minusOddPreimage
    omega
  have ho : minusOddPreimage a % 2 = 1 := by omega
  refine ⟨he, ho, ?_⟩
  simp only [negT, ho, Nat.one_ne_zero, ite_false]
  omega

theorem plus_preimage_exact {a : ℕ} (ha : a % 3 = 2) :
    3 * plusOddPreimage a + 1 = 2 * a ∧
    plusOddPreimage a % 2 = 1 ∧ shortcutC (plusOddPreimage a) = a := by
  have he : 3 * plusOddPreimage a + 1 = 2 * a := by
    unfold plusOddPreimage
    omega
  have ho : plusOddPreimage a % 2 = 1 := by omega
  refine ⟨he, ho, ?_⟩
  simp only [shortcutC, ho, Nat.one_ne_zero, ite_false]
  omega

theorem minus_preimage_above {a : ℕ} (ha : a % 3 = 1) :
    (2 : ℝ) * a / 3 < minusOddPreimage a := by
  have he : (3 : ℝ) * minusOddPreimage a = 2 * a + 1 := by
    exact_mod_cast (minus_preimage_exact ha).1
  linarith

theorem plus_preimage_below {a : ℕ} (ha : a % 3 = 2) :
    (plusOddPreimage a : ℝ) < 2 * a / 3 := by
  have he : (3 : ℝ) * plusOddPreimage a + 1 = 2 * a := by
    exact_mod_cast (plus_preimage_exact ha).1
  linarith

/-- Exact reduction in the available child scale, in multiplicative form. -/
theorem minus_scale_correction {a : ℕ} (ha : a % 3 = 1) (x : ℝ) :
    x / minusOddPreimage a =
      ((x / a) * (3 / 2)) / (1 + 1 / (2 * a)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hc0 : (0 : ℝ) < minusOddPreimage a := by
    have := (minus_preimage_exact ha).1
    exact_mod_cast (show 0 < minusOddPreimage a by omega)
  have he : (3 : ℝ) * minusOddPreimage a = 2 * a + 1 := by
    exact_mod_cast (minus_preimage_exact ha).1
  field_simp
  nlinarith [congrArg (fun t : ℝ => x * t) he]

/-- At a positive cutoff the nominal child budget is strictly too large. -/
theorem minus_nominal_budget_exceeds {a : ℕ} (ha : a % 3 = 1)
    {x : ℝ} (hx : 0 < x) :
    x < ((x / a) * (3 / 2)) * minusOddPreimage a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have h := mul_lt_mul_of_pos_left (minus_preimage_above ha)
    (show 0 < (x / a) * (3 / 2 : ℝ) by positivity)
  have he : ((x / a) * (3 / 2 : ℝ)) * (2 * a / 3) = x := by field_simp
  simpa only [he] using h

/-- For the positive shortcut the same nominal child budget is inside the cutoff. -/
theorem plus_nominal_budget_below {a : ℕ} (ha : a % 3 = 2)
    {x : ℝ} (hx : 0 < x) :
    ((x / a) * (3 / 2)) * plusOddPreimage a < x := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hp := plus_preimage_below ha
  have h := mul_lt_mul_of_pos_left hp (show 0 < (x / a) * (3 / 2 : ℝ) by positivity)
  have he : ((x / a) * (3 / 2 : ℝ)) * (2 * a / 3) = x := by field_simp
  simpa only [he] using h

/-- The excess contains actual ancestors, even at a nonperiodic target. -/
theorem excluded_ancestor :
    minusOddPreimage 19 = 13 ∧
    (negT^[3]) 104 = 13 ∧
    (∀ j ≤ 3, (negT^[j]) 104 ≤ 104) ∧
    (103 : ℕ) < 104 ∧ 4 * 19 ≤ (103 : ℕ) ∧
    (104 : ℝ) ≤ ((103 / 19) * (3 / 2)) * minusOddPreimage 19 := by
  refine ⟨by decide, by decide, ?_, by norm_num, by norm_num, ?_⟩
  · intro j hj
    interval_cases j <;> decide
  · norm_num [minusOddPreimage]

theorem nineteen_not_periodic : ∀ d : ℕ, 0 < d → (negT^[d]) 19 ≠ 19 := by
  let s : Finset ℕ := {28, 14, 7, 10, 5}
  have hclosed : ∀ n ∈ s, negT n ∈ s := by decide
  have hmem : ∀ d, (negT^[d + 1]) 19 ∈ s := by
    intro d
    induction d with
    | zero => decide
    | succ d ih =>
        rw [Function.iterate_succ_apply']
        exact hclosed _ ih
  intro d hd he
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have h := hmem k
  rw [he] at h
  norm_num [s] at h

/-- A formal inverse itinerary: `false` doubles, `true` takes `(2*x+1)/3`.
Integrality and parity guards are deliberately separate from this real formula. -/
noncomputable def inverseWord : List Bool → ℝ → ℝ
  | [], x => x
  | false :: w, x => inverseWord w (2 * x)
  | true :: w, x => inverseWord w ((2 * x + 1) / 3)

/-- The homogeneous multiplier of an inverse itinerary. -/
noncomputable def inverseFactor : List Bool → ℝ
  | [] => 1
  | false :: w => inverseFactor w * 2
  | true :: w => inverseFactor w * (2 / 3)

theorem inverseFactor_pos (w : List Bool) : 0 < inverseFactor w := by
  induction w with
  | nil => norm_num [inverseFactor]
  | cons b w ih => cases b <;> simp only [inverseFactor] <;> positivity

theorem inverseWord_affine (w : List Bool) (x : ℝ) :
    inverseWord w x = inverseFactor w * x + inverseWord w 0 := by
  induction w generalizing x with
  | nil => simp [inverseWord, inverseFactor]
  | cons b w ih =>
      cases b
      · simp only [inverseWord, inverseFactor]
        rw [ih (2 * x), ih (2 * 0)]
        ring
      · simp only [inverseWord, inverseFactor]
        rw [ih ((2 * x + 1) / 3), ih ((2 * 0 + 1) / 3)]
        ring

theorem inverseWord_nonneg (w : List Bool) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ inverseWord w x := by
  induction w generalizing x with
  | nil => exact hx
  | cons b w ih => cases b <;> apply ih <;> positivity

theorem inverseWord_append (u v : List Bool) (x : ℝ) :
    inverseWord (u ++ v) x = inverseWord v (inverseWord u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [List.cons_append, inverseWord, ih]

theorem inverseFactor_append (u v : List Bool) :
    inverseFactor (u ++ v) = inverseFactor v * inverseFactor u := by
  induction u with
  | nil => simp [inverseFactor]
  | cons b u ih =>
      cases b <;> simp only [List.cons_append, inverseFactor, ih] <;> ring

/-- The exact criterion for a shift to absorb an inverse block's offset. -/
theorem shifted_block_iff (w : List Bool) (K x : ℝ) :
    inverseWord w x + K ≤ inverseFactor w * (x + K) ↔
      inverseWord w 0 ≤ (inverseFactor w - 1) * K := by
  rw [inverseWord_affine]
  constructor <;> intro h <;> nlinarith

/-- The same shift works through arbitrarily many blocks; there is no
depth-dependent factor in this estimate. -/
theorem shifted_blocks (F : Finset (List Bool)) {K : ℝ}
    (hK : ∀ w ∈ F, inverseWord w 0 ≤ (inverseFactor w - 1) * K)
    (ws : List (List Bool)) (hws : ∀ w ∈ ws, w ∈ F) (x : ℝ) :
    inverseWord ws.flatten x + K ≤ inverseFactor ws.flatten * (x + K) := by
  induction ws generalizing x with
  | nil => simp [inverseWord, inverseFactor]
  | cons w ws ih =>
      simp only [List.flatten_cons, inverseWord_append, inverseFactor_append]
      have hw := (shifted_block_iff w K x).2 (hK w (hws w (by simp)))
      have ht := ih (fun v hv => hws v (by simp [hv])) (inverseWord w x)
      calc
        inverseWord ws.flatten (inverseWord w x) + K
            ≤ inverseFactor ws.flatten * (inverseWord w x + K) := ht
        _ ≤ inverseFactor ws.flatten * (inverseFactor w * (x + K)) :=
          mul_le_mul_of_nonneg_left hw (inverseFactor_pos _).le
        _ = (inverseFactor ws.flatten * inverseFactor w) * (x + K) := by ring

/-- Every finite family of strictly expanding inverse itineraries admits
a common nonnegative shift. No validity of a residue counting system is assumed
or concluded. One plus the displayed sum is an explicit, possibly nonminimal choice. -/
theorem finite_expanding_shift (F : Finset (List Bool))
    (hF : ∀ w ∈ F, 1 < inverseFactor w) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ws : List (List Bool),
      (∀ w ∈ ws, w ∈ F) → ∀ x : ℝ,
        inverseWord ws.flatten x + K ≤ inverseFactor ws.flatten * (x + K) := by
  let K := 1 + ∑ w ∈ F, inverseWord w 0 / (inverseFactor w - 1)
  have hnonneg : ∀ w ∈ F, 0 ≤ inverseWord w 0 / (inverseFactor w - 1) := by
    intro w hw
    exact div_nonneg (inverseWord_nonneg w le_rfl) (by linarith [hF w hw])
  have hsum := Finset.sum_nonneg hnonneg
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  have hK : ∀ w ∈ F, inverseWord w 0 ≤ (inverseFactor w - 1) * K := by
    intro w hw
    have hterm : inverseWord w 0 / (inverseFactor w - 1) ≤
        ∑ v ∈ F, inverseWord v 0 / (inverseFactor v - 1) :=
      Finset.single_le_sum hnonneg hw
    have hden : 0 < inverseFactor w - 1 := by linarith [hF w hw]
    have hbound : inverseWord w 0 / (inverseFactor w - 1) ≤ K := by
      dsimp [K]
      linarith
    have := (div_le_iff₀ hden).mp hbound
    nlinarith
  intro ws hws x
  exact shifted_blocks F hK ws hws x

/-- A coarse bound controls every internal prefix, separately from the
sharper bound at block boundaries. -/
theorem inverseWord_height (w : List Bool) {x : ℝ} (hx : 0 ≤ x) :
    inverseWord w x + 1 ≤ (2 : ℝ) ^ w.length * (x + 1) := by
  induction w generalizing x with
  | nil => simp [inverseWord]
  | cons b w ih =>
      cases b
      · have h := ih (show 0 ≤ 2 * x by positivity)
        simp only [inverseWord, List.length_cons, pow_succ]
        nlinarith [show 0 ≤ (2 : ℝ) ^ w.length by positivity]
      · have h := ih (show 0 ≤ (2 * x + 1) / 3 by positivity)
        simp only [inverseWord, List.length_cons, pow_succ]
        have hp : 0 ≤ (2 : ℝ) ^ w.length := by positivity
        nlinarith [mul_nonneg hp hx]

/-- Internal prefixes of length at most L cost at most one fixed factor
2^L, independently of how many expanding blocks precede them. -/
theorem internal_prefix_height (F : Finset (List Bool)) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ w ∈ F, inverseWord w 0 ≤ (inverseFactor w - 1) * K)
    (ws : List (List Bool)) (hws : ∀ w ∈ ws, w ∈ F)
    (u : List Bool) {L : ℕ} (hu : u.length ≤ L) {x : ℝ} (hx : 0 ≤ x) :
    inverseWord (ws.flatten ++ u) x + 1 ≤
      (2 : ℝ) ^ L * inverseFactor ws.flatten * (x + K) := by
  rw [inverseWord_append]
  have he := shifted_blocks F hK ws hws x
  have hn := inverseWord_nonneg ws.flatten hx
  have hi := inverseWord_height u hn
  have hp : (2 : ℝ) ^ u.length ≤ (2 : ℝ) ^ L :=
    pow_le_pow_right₀ (by norm_num) hu
  calc
    inverseWord u (inverseWord ws.flatten x) + 1
        ≤ (2 : ℝ) ^ u.length * (inverseWord ws.flatten x + 1) := hi
    _ ≤ (2 : ℝ) ^ L * (inverseWord ws.flatten x + 1) :=
      mul_le_mul_of_nonneg_right hp (by linarith)
    _ ≤ (2 : ℝ) ^ L * (inverseFactor ws.flatten * (x + K)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- Explicit example: the inverse blocks EE and OE have multipliers 4
and 4/3; one common shift is 2. The bound holds at every concatenated depth. -/
theorem two_block_shift (ws : List (List Bool))
    (hws : ∀ w ∈ ws, w = [false, false] ∨ w = [true, false]) (x : ℝ) :
    inverseWord ws.flatten x + 2 ≤ inverseFactor ws.flatten * (x + 2) := by
  apply shifted_blocks {[false, false], [true, false]}
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> norm_num [inverseWord, inverseFactor]
  · intro w hw
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hws w hw

/-- The OE example is an actual two-step predecessor whenever its odd
inverse branch is integral. -/
theorem two_step_preimage {a : ℕ} (ha : a % 3 = 1) :
    (negT^[2]) (2 * minusOddPreimage a) = a ∧
      (2 * minusOddPreimage a : ℕ) + (2 : ℝ) = (4 / 3 : ℝ) * (a + 2) := by
  constructor
  · have he : negT (2 * minusOddPreimage a) = minusOddPreimage a := by
      simp [negT]
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply,
      he] using (minus_preimage_exact ha).2.2
  · have he : (3 : ℝ) * minusOddPreimage a = 2 * a + 1 := by
      exact_mod_cast (minus_preimage_exact ha).1
    push_cast
    linarith

/-- No single translation absorbs both elementary inverse branches with
their exact homogeneous multipliers: doubling needs K ≥ 0, the odd branch
needs K ≤ -1. Expanding blocks are an essential hypothesis. -/
theorem no_elementary_shift : ¬ ∃ K : ℝ,
    (∀ x : ℝ, 2 * x + K ≤ 2 * (x + K)) ∧
    (∀ x : ℝ, (2 * x + 1) / 3 + K ≤ (2 / 3) * (x + K)) := by
  rintro ⟨K, he, ho⟩
  have he0 := he 0
  have ho0 := ho 0
  linarith

end Problems.Collatz.PreimageScale
