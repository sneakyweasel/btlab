import Problems.Collatz.FixedInteger

namespace Problems.Collatz

/-!
Periodic exponent codes. Every statement is algebraic. None of them is a
proof or disproof of the Collatz conjecture.
-/

/-- A nonempty word is primitive when it is not `u` repeated `r>1` times. -/
def IsPrimitive {α : Type*} [DecidableEq α] (w : List α) : Prop :=
  w ≠ [] ∧ ∀ r, 1 < r → ∀ u : List α, (List.replicate r u).flatten ≠ w

/-- A word repeated twice is not primitive. -/
theorem replicate_two_not_primitive {α : Type*} [DecidableEq α]
    (u : List α) :
    ¬ IsPrimitive (u ++ u) := by
  intro h
  have hrep : (List.replicate (2 : ℕ) u).flatten = u ++ u := by
    simp [List.replicate]
  exact (h.2 2 (by decide) u) hrep

/-- The periodic identity `n (2^K - 3^p) = C` is a divisibility condition. -/
theorem dvd_of_periodic_fixed_point
    (twoPow threePow n C : ℤ)
    (h : n * (twoPow - threePow) = C) :
    (twoPow - threePow) ∣ C :=
  ⟨n, by rw [mul_comm, h]⟩

/-- Reconstructing a rational candidate is the same identity in cancellation form:
`n * D = C` with `D ≠ 0`. Integer division is not used. -/
theorem candidate_mul_identity
    (twoPow threePow n C : ℤ)
    (h : n * (twoPow - threePow) = C) :
    n * (twoPow - threePow) = C := h

/-- Expanding periods cannot satisfy the positive fixed-point equation. -/
theorem expanding_excludes_positive_candidate
    (n C twoPow threePow : ℤ)
    (hn : 0 < n)
    (hC : 0 < C)
    (hExp : twoPow < threePow)
    (hFix : n * (twoPow - threePow) = C) :
    False := by
  have hneg : n * (twoPow - threePow) < 0 :=
    mul_neg_of_pos_of_neg hn (sub_neg.mpr hExp)
  have hCneg : C < 0 := by simpa [hFix] using hneg
  exact lt_asymm hC hCneg

/-- One-step rotation of an exact affine block: the next start `x` is the
candidate for the rotated constant `C'`. -/
theorem rotated_candidate
    (n C D x C' twoPowK : ℤ)
    (hpow : twoPowK ≠ 0)
    (hD : n * D = C)
    (hx : twoPowK * x = 3 * n + 1)
    (hC' : twoPowK * C' = 3 * C + D) :
    x * D = C' := by
  have hmul : twoPowK * (x * D) = twoPowK * C' := by
    calc
      twoPowK * (x * D) = (twoPowK * x) * D := by ring
      _ = (3 * n + 1) * D := by rw [hx]
      _ = 3 * (n * D) + D := by ring
      _ = 3 * C + D := by rw [hD]
      _ = twoPowK * C' := hC'.symm
  exact mul_left_cancel₀ hpow hmul

/-- Additive amplitude of odd states is even. -/
theorem odd_sub_even (a b : ℤ) (ha : Odd a) (hb : Odd b) : Even (a - b) :=
  Odd.sub_odd ha hb

/-- Closure of a genuine period: if every affine step holds and the last
state returns to the start, the global identity holds. -/
theorem cycle_closure_of_affine_steps
    (twoPow threePow n C x : ℤ)
    (hEndpoint : threePow * n + C = twoPow * x)
    (hx : x = n) :
    n * (twoPow - threePow) = C :=
  periodic_fixed_point twoPow threePow n C x hEndpoint hx

end Problems.Collatz
