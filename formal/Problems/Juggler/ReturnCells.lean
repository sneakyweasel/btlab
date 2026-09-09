import Problems.Juggler.FateContagion

namespace Problems.Juggler.ReturnCells

/-!
Exact integer cells for the prescribed OE and OOE returns. The actual-step
bridges require every source parity. Endpoint compression alone does not
provide those guards, as the perfect-power family below demonstrates.
-/

/-- The prescribed O then E return, without a source-parity assumption. -/
def oe (x : ℕ) : ℕ := ((x ^ 3).sqrt).sqrt

/-- The prescribed O, O, E return. -/
def ooe (x : ℕ) : ℕ := oe ((x ^ 3).sqrt)

theorem oe_eq_iff {x y : ℕ} :
    oe x = y ↔ y ^ 4 ≤ x ^ 3 ∧ x ^ 3 < (y + 1) ^ 4 := by
  exact Problems.Juggler.sqrt_sqrt_eq_iff

theorem oe_cell (x : ℕ) :
    oe x ^ 4 ≤ x ^ 3 ∧ x ^ 3 < (oe x + 1) ^ 4 :=
  oe_eq_iff.mp rfl

theorem oe_actual {x : ℕ} (hx : x % 2 = 1)
    (hu : (x ^ 3).sqrt % 2 = 0) :
    floorPower (floorPower x) = oe x := by
  rw [floorPower_odd_eq hx, floorPower_even_eq hu]
  rfl

theorem ooe_actual {x : ℕ} (hx : x % 2 = 1)
    (hu : (x ^ 3).sqrt % 2 = 1)
    (hv : (((x ^ 3).sqrt) ^ 3).sqrt % 2 = 0) :
    floorPower (floorPower (floorPower x)) = ooe x := by
  rw [floorPower_odd_eq hx, floorPower_odd_eq hu, floorPower_even_eq hv]
  rfl

theorem ooe_upper_pow (x : ℕ) : ooe x ^ 8 ≤ x ^ 9 := by
  have h₁ := Nat.pow_le_pow_left (oe_cell ((x ^ 3).sqrt)).1 2
  have h₂ := Nat.pow_le_pow_left (Nat.sqrt_le' (x ^ 3)) 3
  have ha : ooe x ^ 8 ≤ (x ^ 3).sqrt ^ 6 := by
    simpa [ooe, ← pow_mul] using h₁
  have hb : (x ^ 3).sqrt ^ 6 ≤ x ^ 9 := by
    simpa [← pow_mul] using h₂
  exact ha.trans hb

theorem cube_lt_fourth_succ {u k : ℕ} (hk : 0 < k)
    (h : u ^ 3 < k ^ 4) : (u + 1) ^ 3 < (k + 1) ^ 4 := by
  have hk8 : k ^ 8 ≤ k ^ 9 := Nat.pow_le_pow_right hk (by omega)
  have hu2 : u ^ 2 ≤ k ^ 3 := by
    by_contra hn
    have hh := Nat.pow_lt_pow_left (show k ^ 3 < u ^ 2 by omega) (by decide : 3 ≠ 0)
    have hh' := Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)
    norm_num [← pow_mul] at hh hh'
    omega
  have hu1 : u ≤ k ^ 2 := by
    by_contra hn
    have hh := Nat.pow_lt_pow_left (show k ^ 2 < u by omega) (by decide : 2 ≠ 0)
    have hk3 : k ^ 3 ≤ k ^ 4 := Nat.pow_le_pow_right hk (by omega)
    norm_num [← pow_mul] at hh
    omega
  nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2)]

theorem ooe_lower_pow (x : ℕ) : x ^ 9 < (ooe x + 2) ^ 8 := by
  let u := (x ^ 3).sqrt
  have hx : x ^ 3 < (u + 1) ^ 2 := Nat.lt_succ_sqrt' (x ^ 3)
  have hu : u ^ 3 < (ooe x + 1) ^ 4 := (oe_cell u).2
  have hu' := cube_lt_fourth_succ (by omega : 0 < ooe x + 1) hu
  have hx' := Nat.pow_lt_pow_left hx (by decide : 3 ≠ 0)
  have hz' := Nat.pow_lt_pow_left hu' (by decide : 2 ≠ 0)
  have ha : x ^ 9 < (u + 1) ^ 6 := by simpa [← pow_mul] using hx'
  have hb : (u + 1) ^ 6 < (ooe x + 2) ^ 8 := by
    simpa [← pow_mul, Nat.add_assoc] using hz'
  exact ha.trans hb

theorem ooe_two_cell (x : ℕ) :
    ooe x ^ 8 ≤ x ^ 9 ∧ x ^ 9 < (ooe x + 2) ^ 8 :=
  ⟨ooe_upper_pow x, ooe_lower_pow x⟩

theorem ooe_one_integer {x y : ℕ}
    (hy : y ^ 8 ≤ x ^ 9 ∧ x ^ 9 < (y + 1) ^ 8) :
    ooe x = y ∨ ooe x + 1 = y := by
  have hz := ooe_two_cell x
  have h₁ : ooe x ≤ y := by
    by_contra hn
    have hh := Nat.pow_le_pow_left (show y + 1 ≤ ooe x by omega) 8
    omega
  have h₂ : y ≤ ooe x + 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_left (show ooe x + 2 ≤ y by omega) 8
    omega
  omega

theorem ooe_odd_maximal {x y : ℕ} (hx : ooe x % 2 = 1)
    (hy : y % 2 = 1) (hpow : y ^ 8 ≤ x ^ 9) :
    y ≤ ooe x := by
  by_contra hn
  have hh := Nat.pow_le_pow_left (show ooe x + 2 ≤ y by omega) 8
  have hl := ooe_lower_pow x
  omega

theorem oe_perfect_power (s : ℕ) :
    ((s ^ 4) ^ 3).sqrt = s ^ 6 ∧ oe (s ^ 4) = s ^ 3 := by
  have h₁ : ((s ^ 4) ^ 3).sqrt = s ^ 6 := by
    have he : (s ^ 4) ^ 3 = (s ^ 6) ^ 2 := by ring
    rw [he, Nat.sqrt_eq']
  constructor
  · exact h₁
  · unfold oe
    rw [h₁]
    have he : s ^ 6 = (s ^ 3) ^ 2 := by ring
    rw [he, Nat.sqrt_eq']

theorem oe_perfect_power_hidden_odd {s : ℕ} (hs : s % 2 = 1) :
    (s ^ 4) % 2 = 1 ∧ (((s ^ 4) ^ 3).sqrt) % 2 = 1 ∧
      oe (s ^ 4) % 2 = 1 := by
  rw [(oe_perfect_power s).1, (oe_perfect_power s).2]
  constructor
  · rw [Nat.pow_mod, hs]
  constructor
  · rw [Nat.pow_mod, hs]
  · rw [Nat.pow_mod, hs]

end Problems.Juggler.ReturnCells
