import Problems.Juggler.Envelope

namespace Problems.Juggler

/-!
# Two-sided power corridor

Upper information is an `EnvelopeState` or a cell bound `x < n^U`.
Lower information is an integer power `n^L ≤ x`. Together they form
the corridor

```
n^L ≤ x < n^U.
```

The collision `U ≤ L` is impossible for `n ≥ 2`. Even reset is the
one-step map `x < n^{2k} ⇒ T(x) < n^k`. Cube-band specializations
live in `CubeCorridor`. This file does not know `AboveAnchor`,
`CycleMin`, or `MinimalNonTerm`.
-/

/-- Integer two-sided cell `n^lower ≤ x < n^upper`. -/
def PowerCorridor (n x lower upper : ℕ) : Prop :=
  n ^ lower ≤ x ∧ x < n ^ upper

theorem PowerCorridor.lower {n x L U : ℕ} (h : PowerCorridor n x L U) :
    n ^ L ≤ x :=
  h.1

theorem PowerCorridor.upper {n x L U : ℕ} (h : PowerCorridor n x L U) :
    x < n ^ U :=
  h.2

/-- Generic collision: `n^L ≤ x < n^U` and `U ≤ L` is impossible. -/
theorem power_corridor_contradiction {n x L U : ℕ}
    (hn : 2 ≤ n) (hL : n ^ L ≤ x) (hU : x < n ^ U) (hUL : U ≤ L) : False := by
  have hlt : n ^ L < n ^ U := lt_of_le_of_lt hL hU
  have hle : n ^ U ≤ n ^ L :=
    Nat.pow_le_pow_right (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn) hUL
  exact (not_le_of_gt hlt) hle

theorem PowerCorridor.contradiction {n x L U : ℕ}
    (hn : 2 ≤ n) (h : PowerCorridor n x L U) (hUL : U ≤ L) : False :=
  power_corridor_contradiction hn h.1 h.2 hUL

/-- Corollary A: a lower power and an upper envelope collide when
`B < L·A`. -/
theorem envelope_corridor_contradiction {n x A B L : ℕ}
    (hn : 2 ≤ n) (hA : 0 < A) (henv : x ^ A ≤ n ^ B)
    (hge : n ^ L ≤ x) (hgap : B < L * A) : False :=
  (not_le_of_gt (envelope_lt_pow hn hA henv hgap)) hge

theorem EnvelopeState.corridor_contradiction {n x L : ℕ}
    (h : EnvelopeState n x) (hn : 2 ≤ n) (hA : 0 < h.A)
    (hge : n ^ L ≤ x) (hgap : h.B < L * h.A) : False :=
  envelope_corridor_contradiction hn hA h.le hge hgap

/-- Even cell: `T(x) < n ↔ x < n^2`. Shared square-trap primitive. -/
theorem even_below_square_iff {x n : ℕ} (he : x % 2 = 0) :
    floorPower x < n ↔ x < n ^ 2 := by
  rw [floorPower_even_eq he]
  simpa [pow_two] using (@Nat.sqrt_lt x n)

theorem even_below_square_drop {x n : ℕ} (he : x % 2 = 0)
    (hlt : x < n ^ 2) : floorPower x < n :=
  (even_below_square_iff he).mpr hlt

/-- Corollary B: `x < n^{2k}` and `x` even give `T(x) < n^k`.
The `k = 1` case is `even_below_square_iff`. -/
theorem even_below_anchor_pow {x n k : ℕ} (he : x % 2 = 0) :
    floorPower x < n ^ k ↔ x < n ^ (2 * k) := by
  have h := even_below_square_iff (n := n ^ k) he
  have hsq : (n ^ k) ^ 2 = n ^ (2 * k) := by
    rw [pow_two, ← Nat.pow_add, Nat.two_mul]
  simpa [hsq] using h

/-- `k = 2`: even `x < n^4` gives `T(x) < n^2`. -/
theorem even_below_fourth {x n : ℕ} (he : x % 2 = 0) :
    floorPower x < n ^ 2 ↔ x < n ^ 4 :=
  even_below_anchor_pow (k := 2) he

/-- `k = 3`: even `x < n^6` gives `T(x) < n^3`. -/
theorem even_below_cube {x n : ℕ} (he : x % 2 = 0) :
    floorPower x < n ^ 3 ↔ x < n ^ 6 := by
  simpa [show (2 : ℕ) * 3 = 6 from rfl] using even_below_anchor_pow (k := 3) he

/-- Cube cell plus even is a square cell for the next state:
`x < n^3 < n^4` and `even_below_fourth`. -/
theorem even_below_cube_preimage {x n : ℕ} (hn : 2 ≤ n) (he : x % 2 = 0)
    (hlt : x < n ^ 3) : floorPower x < n ^ 2 :=
  (even_below_fourth he).mpr
    (lt_trans hlt (pow_lt_of_two_le hn (by decide : (3 : ℕ) < 4)))

/-- Corollary C: two evens below the fourth power drop below `n`.
Integer `k < 2` is the one-step square trap. The cube band uses
`n^3 < n^4`. -/
theorem two_even_below_fourth {x n : ℕ}
    (he : x % 2 = 0) (he2 : floorPower x % 2 = 0)
    (hlt : x < n ^ 4) :
    floorPower (floorPower x) < n :=
  even_below_square_drop he2 ((even_below_fourth he).mpr hlt)

theorem odd_sq_odd {n : ℕ} (hodd : n % 2 = 1) : n ^ 2 % 2 = 1 := by
  have : n * n % 2 = 1 := by simp [Nat.mul_mod, hodd]
  simpa [pow_two] using this

theorem even_ne_odd_square {z n : ℕ} (heven : z % 2 = 0)
    (hodd : n % 2 = 1) : z ≠ n ^ 2 := by
  intro h
  have : z % 2 = 1 := by simpa [h] using odd_sq_odd hodd
  omega

/-- Cube specialization of `two_even_below_fourth`. -/
theorem two_even_below_cube {x n : ℕ} (hn : 2 ≤ n)
    (he : x % 2 = 0) (he2 : floorPower x % 2 = 0)
    (hlt : x < n ^ 3) :
    floorPower (floorPower x) < n :=
  two_even_below_fourth he he2
    (lt_trans hlt (pow_lt_of_two_le hn (by decide : (3 : ℕ) < 4)))

theorem even_ge_sq_of_succ_ge {x n : ℕ} (he : x % 2 = 0)
    (hge : n ≤ floorPower x) : n ^ 2 ≤ x := by
  rw [floorPower_even_eq he] at hge
  exact (by simpa [pow_two] using Nat.le_sqrt.mp hge)

theorem odd_floor_lt_sq {n : ℕ} (hn : 2 ≤ n) (hodd : n % 2 = 1) :
    floorPower n < n ^ 2 := by
  rw [floorPower_odd_eq hodd]
  refine Nat.sqrt_lt.mpr ?_
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn
  have hpow : n ^ 3 < n ^ 4 :=
    Nat.pow_lt_pow_right hn1 (by decide : (3 : ℕ) < 4)
  have h4 : n ^ 4 = n ^ 2 * n ^ 2 := Nat.pow_add n 2 2
  simpa [h4] using hpow

end Problems.Juggler
