import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Data.Nat.Prime.Int
import BTCalculus.Quadratic

/-!
# Lifting trees of `f(x) ≡ 0 (mod 3^k)`

A residue modulo `3^k` is a balanced-ternary word `w` of length `k` with
value `packWord w`. Iterating the section reconstruction gives

  `eval (packTrits w x) f = packTrits (outputAlong w f) (eval x (residualAlong w f))`

and because the output trits pack to something strictly smaller in
absolute value than `3^k`, divisibility of `f(packWord w)` by `3^k` is
equivalent to every output trit vanishing. So the solution tree of the
congruence is the zero-output subtree of the residual Mealy machine.

The one-step count `0 / 1 / 3` is then the classical trichotomy, proved
here from `Polynomial.binomExpansion`: for `k ≥ 1` the quadratic
remainder is divisible by `3^{2k}` and hence by `3^{k+1}`, so only the
value and the derivative survive.
-/

noncomputable section

namespace BTCalculus

open Polynomial

/-- `x` solves `f(x) ≡ 0 (mod 3^k)`. -/
def IsRootMod (k : ℕ) (f : ℤ[X]) (x : ℤ) : Prop :=
  (3 : ℤ) ^ k ∣ eval x f

/-- Level-`k` lift relation: `y = x + 3^k t`. -/
def LiftsFrom (k : ℕ) (x y : ℤ) : Prop :=
  ∃ t : ℤ, y = x + 3 ^ k * t

theorem packWord_def (w : List ℤ) : packWord w = packTrits w 0 := rfl

/-! ## Iterated reconstruction along a word -/

/-- `f(n_w + 3^k x) = Σ ρ_i 3^i + 3^k (𝔇_w f)(x)`, in packed form. -/
theorem iterated_reconstruction (f : ℤ[X]) :
    ∀ (w : List ℤ) (x : ℤ),
      eval (packTrits w x) f =
        packTrits (outputAlong w f) (eval x (residualAlong w f))
  | [], x => by
    simp [packTrits, outputAlong, residualAlong]
  | a :: w, x => by
    rw [pack_cons, section_reconstruction_eval f a (packTrits w x),
      iterated_reconstruction (sectionDeriv a f) w x, outputAlong_cons,
      residualAlong_cons, pack_cons]

/-! ## Packed trit words that vanish -/

theorem abs_packWord_lt {w : List ℤ} (hw : isTritList w) :
    |packWord w| < (3 : ℤ) ^ w.length := by
  have hb := two_mul_packWord_le hw
  have hpos : (0 : ℤ) < (3 : ℤ) ^ w.length := pow_pos (by decide) _
  have hnn : (0 : ℤ) ≤ |packWord w| := abs_nonneg _
  linarith

theorem packWord_eq_zero_of_dvd {w : List ℤ} (hw : isTritList w)
    (h : (3 : ℤ) ^ w.length ∣ packWord w) : packWord w = 0 :=
  dvd_abs_lt_pow h (abs_packWord_lt hw)

theorem packWord_eq_zero_iff_replicate {w : List ℤ} (hw : isTritList w) :
    packWord w = 0 ↔ w = List.replicate w.length (0 : ℤ) := by
  constructor
  · intro h
    refine packWord_injective hw (isTritList_replicate_zero _) (by simp) ?_
    rw [h, packWord_replicate_zero]
  · intro h
    rw [h, packWord_replicate_zero]

/-! ## The lifting tree is the zero-output subtree -/

/-- `3^k` divides `f(n_w)` exactly when every output trit along `w` is `0`.

The word itself need not consist of trits: the outputs are trits
whatever the sections are, and that is all the packing bound needs. -/
theorem lift_iff_outputs_zero (w : List ℤ) (f : ℤ[X]) :
    IsRootMod w.length f (packWord w) ↔
      outputAlong w f = List.replicate w.length (0 : ℤ) := by
  have hout := isTritList_outputAlong w f
  have hlen := outputAlong_length_eq w f
  have hkey :
      eval (packWord w) f =
        packWord (outputAlong w f) +
          3 ^ w.length * eval 0 (residualAlong w f) := by
    rw [packWord_def, iterated_reconstruction f w 0, packTrits_eq,
      outputAlong_length_eq]
  unfold IsRootMod
  rw [hkey]
  constructor
  · intro h
    have hd : (3 : ℤ) ^ w.length ∣ 3 ^ w.length * eval 0 (residualAlong w f) :=
      dvd_mul_right _ _
    have hS : (3 : ℤ) ^ w.length ∣ packWord (outputAlong w f) := by
      simpa using dvd_sub h hd
    have hz : packWord (outputAlong w f) = 0 :=
      packWord_eq_zero_of_dvd hout (by rwa [hlen])
    have hrep := (packWord_eq_zero_iff_replicate hout).mp hz
    rwa [hlen] at hrep
  · intro h
    have hz : packWord (outputAlong w f) = 0 := by
      rw [h, packWord_replicate_zero]
    rw [hz, zero_add]
    exact dvd_mul_right _ _

/-! ## Reduction and the lift relation -/

theorem isRootMod_zero (f : ℤ[X]) (x : ℤ) : IsRootMod 0 f x := by
  simp [IsRootMod]

/-- A root modulo `3^{k+1}` is a root modulo `3^k`. -/
theorem isRootMod_reduce {k : ℕ} {f : ℤ[X]} {x : ℤ}
    (h : IsRootMod (k + 1) f x) : IsRootMod k f x :=
  dvd_trans (pow_dvd_pow 3 (Nat.le_succ k)) h

theorem liftsFrom_refl (k : ℕ) (x : ℤ) : LiftsFrom k x x :=
  ⟨0, by ring⟩

theorem liftsFrom_iff (k : ℕ) (x y : ℤ) :
    LiftsFrom k x y ↔ (3 : ℤ) ^ k ∣ y - x := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by ring⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by linarith⟩

/-- Reduction to level `k` is constant on a level-`k` lift class. -/
theorem isRootMod_lift_iff (f : ℤ[X]) (k : ℕ) (x t : ℤ) :
    IsRootMod k f (x + 3 ^ k * t) ↔ IsRootMod k f x := by
  obtain ⟨q, hq⟩ := f.binomExpansion x (3 ^ k * t)
  have hfact :
      eval (x + 3 ^ k * t) f =
        eval x f +
          3 ^ k * (eval x (derivative f) * t + q * (3 ^ k * t ^ 2)) := by
    rw [hq]; ring
  have hd : (3 : ℤ) ^ k ∣
      3 ^ k * (eval x (derivative f) * t + q * (3 ^ k * t ^ 2)) :=
    dvd_mul_right _ _
  unfold IsRootMod
  rw [hfact]
  constructor
  · intro h
    simpa using dvd_sub h hd
  · intro h
    exact dvd_add h hd

/-! ## One-step trichotomy -/

/-- With `f(x) = 3^k c` and `k ≥ 1`, lifting by `3^k t` is a linear
condition on `t` modulo `3`. -/
theorem lift_condition (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) {x c : ℤ}
    (hc : eval x f = 3 ^ k * c) (t : ℤ) :
    IsRootMod (k + 1) f (x + 3 ^ k * t) ↔
      (3 : ℤ) ∣ c + eval x (derivative f) * t := by
  obtain ⟨q, hq⟩ := f.binomExpansion x (3 ^ k * t)
  have hk3 : (3 : ℤ) ∣ 3 ^ k := dvd_pow_self 3 (Nat.one_le_iff_ne_zero.mp hk)
  have hfact :
      eval (x + 3 ^ k * t) f =
        3 ^ k * (c + eval x (derivative f) * t + q * (3 ^ k * t ^ 2)) := by
    rw [hq, hc]; ring
  have hne : (3 : ℤ) ^ k ≠ 0 := pow_ne_zero k (by decide)
  have hextra : (3 : ℤ) ∣ q * (3 ^ k * t ^ 2) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right hk3 _) q
  unfold IsRootMod
  rw [hfact, pow_succ, mul_dvd_mul_iff_left hne]
  constructor
  · intro h
    simpa using dvd_sub h hextra
  · intro h
    exact dvd_add h hextra

/-- With `f(x) = 3^k c`, being a root one level deeper means `3 ∣ c`. -/
theorem isRootMod_succ_iff {k : ℕ} {f : ℤ[X]} {x c : ℤ}
    (hc : eval x f = 3 ^ k * c) :
    IsRootMod (k + 1) f x ↔ (3 : ℤ) ∣ c := by
  unfold IsRootMod
  rw [hc, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero k (by decide : (3 : ℤ) ≠ 0))]

theorem sq_modEq_one_of_not_dvd {b : ℤ} (h : ¬ (3 : ℤ) ∣ b) :
    b * b ≡ 1 [ZMOD 3] := by
  have hm := lsdZ_mod b
  have hne : lsdZ b ≠ 0 := by
    intro h0
    refine h (Int.modEq_zero_iff_dvd.mp ?_)
    rwa [h0] at hm
  rcases lsdZ_is_trit b with h1 | h0 | h1
  · have hb : b ≡ -1 [ZMOD 3] := by rw [← h1]; exact hm
    simpa using hb.mul hb
  · exact absurd h0 hne
  · have hb : b ≡ 1 [ZMOD 3] := by rw [← h1]; exact hm
    simpa using hb.mul hb

/-- A unit `b` modulo `3` is its own inverse, so `lsdZ (-(c*b))` solves
`c + b t ≡ 0`. -/
theorem dvd_add_mul_lsdZ {b c : ℤ} (hb : ¬ (3 : ℤ) ∣ b) :
    (3 : ℤ) ∣ c + b * lsdZ (-(c * b)) := by
  have h1 : b * lsdZ (-(c * b)) ≡ b * (-(c * b)) [ZMOD 3] :=
    (Int.ModEq.refl b).mul (lsdZ_mod (-(c * b))).symm
  have hsq := sq_modEq_one_of_not_dvd hb
  have h2 : b * (-(c * b)) ≡ -c [ZMOD 3] := by
    have : -(c * (b * b)) ≡ -(c * 1) [ZMOD 3] := ((Int.ModEq.refl c).mul hsq).neg
    calc b * (-(c * b)) = -(c * (b * b)) := by ring
      _ ≡ -(c * 1) [ZMOD 3] := this
      _ = -c := by ring
  have h3 : c + b * lsdZ (-(c * b)) ≡ c + -c [ZMOD 3] :=
    (Int.ModEq.refl c).add (h1.trans h2)
  refine Int.modEq_zero_iff_dvd.mp ?_
  simpa using h3

theorem trit_unique_of_dvd {b c t₁ t₂ : ℤ} (hb : ¬ (3 : ℤ) ∣ b)
    (h₁ : isTrit t₁) (h₂ : isTrit t₂)
    (hd₁ : (3 : ℤ) ∣ c + b * t₁) (hd₂ : (3 : ℤ) ∣ c + b * t₂) :
    t₁ = t₂ := by
  have hsub : (3 : ℤ) ∣ b * (t₁ - t₂) := by
    have hd := dvd_sub hd₁ hd₂
    have heq : c + b * t₁ - (c + b * t₂) = b * (t₁ - t₂) := by ring
    rwa [heq] at hd
  rcases Int.prime_three.dvd_or_dvd hsub with h | h
  · exact absurd h hb
  · rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;> omega

/-- Nonsingular uniqueness: exactly one trit lifts a root when the
derivative is a unit modulo `3`. -/
theorem unique_lift_of_nonsingular (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) {x c : ℤ}
    (hc : eval x f = 3 ^ k * c)
    (hns : ¬ (3 : ℤ) ∣ eval x (derivative f)) :
    ∃! t : ℤ, isTrit t ∧ IsRootMod (k + 1) f (x + 3 ^ k * t) := by
  have hwit := dvd_add_mul_lsdZ (b := eval x (derivative f)) (c := c) hns
  refine ⟨lsdZ (-(c * eval x (derivative f))),
    ⟨lsdZ_is_trit _, (lift_condition f hk hc _).mpr hwit⟩, ?_⟩
  intro t ht
  exact trit_unique_of_dvd hns ht.1 (lsdZ_is_trit _)
    ((lift_condition f hk hc t).mp ht.2) hwit

/-- Singular and deep: every trit lifts. -/
theorem all_lifts_of_singular_deep (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) {x c : ℤ}
    (hc : eval x f = 3 ^ k * c)
    (hs : (3 : ℤ) ∣ eval x (derivative f)) (hdeep : (3 : ℤ) ∣ c) (t : ℤ) :
    IsRootMod (k + 1) f (x + 3 ^ k * t) := by
  rw [lift_condition f hk hc]
  exact dvd_add hdeep (hs.mul_right t)

/-- Singular and shallow: no trit lifts. -/
theorem no_lift_of_singular_shallow (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) {x c : ℤ}
    (hc : eval x f = 3 ^ k * c)
    (hs : (3 : ℤ) ∣ eval x (derivative f)) (hshallow : ¬ (3 : ℤ) ∣ c) (t : ℤ) :
    ¬ IsRootMod (k + 1) f (x + 3 ^ k * t) := by
  rw [lift_condition f hk hc]
  intro h
  exact hshallow (by simpa using dvd_sub h ((hs.mul_right t)))

/-- The trichotomy in one statement: at a level-`k` node with `k ≥ 1` the
set of lifting trits is a singleton, all of `{-1,0,1}`, or empty. -/
theorem lift_trichotomy (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) {x c : ℤ}
    (hc : eval x f = 3 ^ k * c) :
    (∃! t : ℤ, isTrit t ∧ IsRootMod (k + 1) f (x + 3 ^ k * t)) ∨
      (∀ t : ℤ, IsRootMod (k + 1) f (x + 3 ^ k * t)) ∨
      (∀ t : ℤ, ¬ IsRootMod (k + 1) f (x + 3 ^ k * t)) := by
  by_cases hns : (3 : ℤ) ∣ eval x (derivative f)
  · by_cases hdeep : (3 : ℤ) ∣ c
    · exact Or.inr (Or.inl (all_lifts_of_singular_deep f hk hc hns hdeep))
    · exact Or.inr (Or.inr (no_lift_of_singular_shallow f hk hc hns hdeep))
  · exact Or.inl (unique_lift_of_nonsingular f hk hc hns)

end BTCalculus
