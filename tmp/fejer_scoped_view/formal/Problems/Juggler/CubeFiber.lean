import Mathlib.Tactic

/-!
# The OE fiber of a perfect cube is full or alternating, exactly

The `OE` fiber of `m` is the set of odd `n` with `m^4 ≤ n^3 < (m+1)^4`, that is
`⌊n^{3/4}⌋ = m`; the members whose odd-step image `⌊n^{3/2}⌋ = Nat.sqrt (n^3)` is even are
the ones that reach `m` in two steps.  Along a fiber that parity is not a coin: its phase
is a quadratic sweep whose reduced step is `{3 m^{2/3} / 2}`, and for `m = k^3` that step
is exactly `0` (even `k`) or `1/2` (odd `k`).

Underneath the heuristic is an integer identity.  On the fiber `n = k^4 + t`,

    Nat.sqrt ((k^4 + t)^3) = k^6 + 3 k^2 t / 2     whenever 3 t ≤ 4 k,

and `3t ≤ 4k` holds on the whole fiber (`cube_fiber_range`).  For even `k` the value is
even at every `t`, so the fiber is full; for odd `k` it has the parity of `1 + t/2`, so
the images alternate.  Everything here is `nlinarith` from the two square-root
inequalities; no real analysis and no `decide` over the fiber.
-/

namespace Problems.Juggler

/-- Every element of the fiber of `k^3` has offset `t = n - k^4` with `3t ≤ 4k`:
if `3t ≥ 4k + 1` then `(k^4 + t)^3 ≥ (k^3 + 1)^4`, so `n` is past the fiber. -/
theorem cube_fiber_range (k t : ℕ) (hk : 1 ≤ k) (h : (k ^ 4 + t) ^ 3 < (k ^ 3 + 1) ^ 4) :
    3 * t ≤ 4 * k := by
  by_contra hc
  have h1 : 4 * k + 1 ≤ 3 * t := by omega
  have h2 : (3 * k ^ 4 + 4 * k + 1) ^ 3 ≤ (3 * k ^ 4 + 3 * t) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have h3 : (3 * k ^ 4 + 3 * t) ^ 3 = 27 * (k ^ 4 + t) ^ 3 := by ring
  have h4 : 27 * (k ^ 3 + 1) ^ 4 ≤ (3 * k ^ 4 + 4 * k + 1) ^ 3 := by
    have hk2 : k ^ 2 ≥ 1 := Nat.one_le_pow _ _ hk
    nlinarith [pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) 3,
      pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) 8, hk2,
      Nat.pow_le_pow_right hk (show 3 ≤ 8 by norm_num),
      Nat.pow_le_pow_right hk (show 6 ≤ 8 by norm_num),
      Nat.pow_le_pow_right hk (show 1 ≤ 8 by norm_num)]
  omega

/-- Even `k = 2a`: the identity `√((16a⁴+t)³) = 64a⁶ + 6a²t` for `3t ≤ 8a`. -/
theorem cube_fiber_sqrt_even (a t : ℕ) (ha : 1 ≤ a) (ht : 3 * t ≤ 8 * a) :
    Nat.sqrt ((16 * a ^ 4 + t) ^ 3) = 64 * a ^ 6 + 6 * a ^ 2 * t := by
  symm
  rw [Nat.eq_sqrt]
  have h2 : 9 * t ^ 2 ≤ 64 * a ^ 2 := by nlinarith
  have h3 : 27 * t ^ 3 ≤ 512 * a ^ 3 := by nlinarith
  have ha3 : a ^ 3 ≤ a ^ 6 := Nat.pow_le_pow_right ha (by norm_num)
  constructor
  · nlinarith [sq_nonneg (a ^ 2 * t), sq_nonneg t, pow_nonneg (Nat.zero_le t) 3]
  · nlinarith [h2, h3, ha3, sq_nonneg (a ^ 2), pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one ha) 6]

/-- Hence every element of the fiber of `(2a)^3` has an even odd-step image. -/
theorem cube_fiber_even_image (a t : ℕ) (ha : 1 ≤ a) (ht : 3 * t ≤ 8 * a) :
    Nat.sqrt ((16 * a ^ 4 + t) ^ 3) % 2 = 0 := by
  rw [cube_fiber_sqrt_even a t ha ht]
  have h : 64 * a ^ 6 + 6 * a ^ 2 * t = 2 * (32 * a ^ 6 + 3 * a ^ 2 * t) := by ring
  rw [h, Nat.mul_mod_right]

/-- The fiber-level statement for even cubes: every `n` with `(2a)^4 ≤ n` and
`n^3 < ((2a)^3 + 1)^4` has even odd-step image.  The `OE` fiber of `(2a)^3` is full. -/
theorem even_cube_fiber_full (a n : ℕ) (ha : 1 ≤ a) (hlo : (2 * a) ^ 4 ≤ n)
    (hhi : n ^ 3 < ((2 * a) ^ 3 + 1) ^ 4) : Nat.sqrt (n ^ 3) % 2 = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hr := cube_fiber_range (2 * a) t (by omega) hhi
  have h16 : (2 * a) ^ 4 = 16 * a ^ 4 := by ring
  rw [h16]
  exact cube_fiber_even_image a t ha (by omega)

/-- Odd `k = 2a+1`, even offset `t = 2s`: the identity
`√(((2a+1)⁴+2s)³) = (2a+1)⁶ + 3(2a+1)²s` for `3s ≤ 2(2a+1)`. -/
theorem cube_fiber_sqrt_odd (a s : ℕ) (hs : 3 * s ≤ 2 * (2 * a + 1)) :
    Nat.sqrt (((2 * a + 1) ^ 4 + 2 * s) ^ 3) = (2 * a + 1) ^ 6 + 3 * (2 * a + 1) ^ 2 * s := by
  symm
  rw [Nat.eq_sqrt]
  set k := 2 * a + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have h2 : 9 * s ^ 2 ≤ 4 * k ^ 2 := by nlinarith
  have h3 : 27 * s ^ 3 ≤ 8 * k ^ 3 := by nlinarith
  have hk3 : k ^ 3 ≤ k ^ 6 := Nat.pow_le_pow_right hk1 (by norm_num)
  constructor
  · nlinarith [sq_nonneg (k ^ 2 * s), sq_nonneg s, pow_nonneg (Nat.zero_le s) 3]
  · nlinarith [h2, h3, hk3, sq_nonneg (k ^ 2), pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1) 6]

/-- Along the fiber of `(2a+1)^3` the odd-step images alternate in parity: the image at
offset `2s` has the parity of `1 + s`. -/
theorem cube_fiber_alternating (a s : ℕ) (hs : 3 * s ≤ 2 * (2 * a + 1)) :
    (Nat.sqrt (((2 * a + 1) ^ 4 + 2 * s) ^ 3) + s) % 2 = 1 := by
  rw [cube_fiber_sqrt_odd a s hs]
  have h6 : (2 * a + 1) ^ 6 % 2 = 1 := by
    rw [Nat.pow_mod]; norm_num [Nat.add_mod, Nat.mul_mod]
  have h2 : (3 * (2 * a + 1) ^ 2 * s) % 2 = s % 2 := by
    rw [Nat.mul_mod, Nat.mul_mod 3, Nat.pow_mod]; norm_num [Nat.add_mod, Nat.mul_mod]
  omega

/-- The fiber-level statement for odd cubes: an odd `n` with `(2a+1)^4 ≤ n` and
`n^3 < ((2a+1)^3 + 1)^4` sits at an even offset `2s`, and its image has the parity of
`1 + s`.  Consecutive fiber elements therefore have opposite image parity. -/
theorem odd_cube_fiber_alternating (a n : ℕ) (hodd : n % 2 = 1) (hlo : (2 * a + 1) ^ 4 ≤ n)
    (hhi : n ^ 3 < ((2 * a + 1) ^ 3 + 1) ^ 4) :
    (Nat.sqrt (n ^ 3) + (n - (2 * a + 1) ^ 4) / 2) % 2 = 1 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hr := cube_fiber_range (2 * a + 1) t (by omega) hhi
  have hk4 : (2 * a + 1) ^ 4 % 2 = 1 := by
    rw [Nat.pow_mod]; norm_num [Nat.add_mod, Nat.mul_mod]
  have ht : t % 2 = 0 := by omega
  obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s := ⟨t / 2, by omega⟩
  have hs : 3 * s ≤ 2 * (2 * a + 1) := by omega
  have := cube_fiber_alternating a s hs
  simpa [Nat.add_sub_cancel_left] using this

/-- Sanity: the two smallest instances by kernel computation. -/
example : Nat.sqrt (257 ^ 3) = 4120 ∧ Nat.sqrt (259 ^ 3) = 4168 ∧ Nat.sqrt (261 ^ 3) = 4216 := by
  decide +kernel

example : Nat.sqrt (81 ^ 3) = 729 ∧ Nat.sqrt (83 ^ 3) = 756 ∧ Nat.sqrt (85 ^ 3) = 783 := by
  decide +kernel

end Problems.Juggler
