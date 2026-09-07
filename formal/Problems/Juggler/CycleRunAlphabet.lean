import Problems.Juggler.TowerAbsorption
import Problems.Juggler.ItineraryStats

namespace Problems.Juggler

/-!
# Cycle height forces a run alphabet

A nontrivial cycle has a minimum `m` and a maximum `M`.  Its runs are bounded by the
height ratio `R = log M / log m`, by pure bookkeeping: an odd run of length `r` multiplies
the logarithm by `(3/2)^r` and an even run of length `g` divides it by `2^g`, and both
endpoints lie between `m` and `M`.  This file carries the integer content of those two
statements, plus the combinatorial half of the reason a cycle cannot avoid two adjacent
odd letters.

* `odd_step_sq_le` and `odd_step_le_sq_add` are the two sides of one odd step.
* `odd_run_upper`: after `r` odd steps, `y^(2^r) ≤ v^(3^r)`.  This is the run bound.
* `even_run_contracts`: after `g` even steps, `z^(2^g) ≤ w`.
* `oo_step_lower`: two odd steps climb by nine quarters, in the integer form
  `x^9 < 2 (z+1)^4`.  With the certified floor this is what forces `M ≥ m^(9/4)`.
* `oddCount_le_of_noAdjOdd`: a word with no two adjacent odd letters has at most half its
  letters odd.  A cycle's letters satisfy `o log(3/2) = e log 2`, so `o/e = 1.7095 > 1`,
  and the two cannot both hold: some odd run has length at least two.

Nothing here is a halt theorem.  It constrains the shape a cycle would have to have.
-/

/-- One odd step, upper half: `y^2 ≤ x^3`. -/
theorem odd_step_sq_le {x : ℕ} (hx : x % 2 = 1) :
    floorPower x ^ 2 ≤ x ^ 3 := by
  rw [floorPower_odd_eq hx, pow_two]
  exact Nat.sqrt_le _

/-- One odd step, lower half: `x^3 ≤ y^2 + 2y`. -/
theorem odd_step_le_sq_add {x : ℕ} (hx : x % 2 = 1) :
    x ^ 3 ≤ floorPower x ^ 2 + 2 * floorPower x := by
  rw [floorPower_odd_eq hx]
  have h : x ^ 3 < ((x ^ 3).sqrt + 1) * ((x ^ 3).sqrt + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt (x ^ 3)
  nlinarith [h]

/-- `(y+2)^3 ≤ 2 y^3` once `y ≥ 8`: the slack that turns the floor loss into a factor two. -/
theorem cube_shift_le_two {y : ℕ} (hy : 8 ≤ y) : (y + 2) ^ 3 ≤ 2 * y ^ 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hy
  ring_nf
  nlinarith [Nat.zero_le k, sq_nonneg k]

/-- **Two odd steps climb by nine quarters.**  In integers, `x^9 < 2 (z+1)^4`, so
`z > x^(9/4) / 2^(1/4) - 1`.  Applied to a cycle with an `OO`, whose bottom is at least the
minimum and whose top is at most the maximum, this is `M ≥ m^(9/4)` up to the factor. -/
theorem oo_step_lower {x : ℕ} (hx : x % 2 = 1) (hy : floorPower x % 2 = 1)
    (h8 : 8 ≤ floorPower x) :
    x ^ 9 < 2 * (floorPower (floorPower x) + 1) ^ 4 := by
  set y := floorPower x with hydef
  set z := floorPower y with hzdef
  have h1 : x ^ 3 ≤ y ^ 2 + 2 * y := odd_step_le_sq_add hx
  have h2 : y ^ 3 ≤ z ^ 2 + 2 * z := odd_step_le_sq_add hy
  have hA : x ^ 9 ≤ (y ^ 2 + 2 * y) ^ 3 := by
    calc x ^ 9 = (x ^ 3) ^ 3 := by ring
      _ ≤ (y ^ 2 + 2 * y) ^ 3 := Nat.pow_le_pow_left h1 3
  have hB : (y ^ 2 + 2 * y) ^ 3 = y ^ 3 * (y + 2) ^ 3 := by ring
  have hC : y ^ 3 * (y + 2) ^ 3 ≤ 2 * y ^ 6 := by
    calc y ^ 3 * (y + 2) ^ 3 ≤ y ^ 3 * (2 * y ^ 3) :=
          Nat.mul_le_mul_left _ (cube_shift_le_two h8)
      _ = 2 * y ^ 6 := by ring
  have hE : y ^ 3 < (z + 1) ^ 2 := by nlinarith [h2]
  have hF : y ^ 6 < (z + 1) ^ 4 := by
    calc y ^ 6 = (y ^ 3) ^ 2 := by ring
      _ < ((z + 1) ^ 2) ^ 2 := Nat.pow_lt_pow_left hE (by norm_num)
      _ = (z + 1) ^ 4 := by ring
  calc x ^ 9 ≤ (y ^ 2 + 2 * y) ^ 3 := hA
    _ = y ^ 3 * (y + 2) ^ 3 := hB
    _ ≤ 2 * y ^ 6 := hC
    _ < 2 * (z + 1) ^ 4 := by omega

/-- **The odd-run bound.**  After `r` odd steps from `v`, the top `y` satisfies
`y^(2^r) ≤ v^(3^r)`: the logarithm has been multiplied by at most `(3/2)^r`. -/
theorem odd_run_upper (v : ℕ) : ∀ r : ℕ, (∀ i < r, floorPower^[i] v % 2 = 1) →
    (floorPower^[r] v) ^ 2 ^ r ≤ v ^ 3 ^ r := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
      intro hodd
      have hstep : (floorPower^[r] v) % 2 = 1 := hodd r (Nat.lt_succ_self r)
      have hprev : ∀ i < r, floorPower^[i] v % 2 = 1 :=
        fun i hi => hodd i (Nat.lt_succ_of_lt hi)
      have hIH := ih hprev
      rw [Function.iterate_succ_apply']
      have hsq : (floorPower (floorPower^[r] v)) ^ 2 ≤ (floorPower^[r] v) ^ 3 :=
        odd_step_sq_le hstep
      calc (floorPower (floorPower^[r] v)) ^ 2 ^ (r + 1)
          = ((floorPower (floorPower^[r] v)) ^ 2) ^ 2 ^ r := by
            rw [← pow_mul, pow_succ, mul_comm]
        _ ≤ ((floorPower^[r] v) ^ 3) ^ 2 ^ r := Nat.pow_le_pow_left hsq _
        _ = ((floorPower^[r] v) ^ 2 ^ r) ^ 3 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (v ^ 3 ^ r) ^ 3 := Nat.pow_le_pow_left hIH 3
        _ = v ^ 3 ^ (r + 1) := by rw [← pow_mul, pow_succ, mul_comm]

/-- **The even-run bound.**  After `g` even steps from `w`, the bottom `z` satisfies
`z^(2^g) ≤ w`: the logarithm has been divided by at least `2^g`. -/
theorem even_run_contracts {w g : ℕ} (heven : ∀ i < g, Nat.sqrt^[i] w % 2 = 0) :
    (floorPower^[g] w) ^ 2 ^ g ≤ w := by
  rw [floorPower_iter_of_even heven]
  exact ((sqrt_iter_eq_iff g).mp rfl).1

/-! ## The letter count -/

/-- No two adjacent odd letters. -/
def NoAdjOdd (w : List Branch) : Prop :=
  List.IsChain (fun a b => ¬(a = Branch.odd ∧ b = Branch.odd)) w

/-- A word with no two adjacent odd letters is at most half odd.  A cycle's letters
satisfy `o log(3/2) = e log 2`, hence `o/e = log 2 / log(3/2) = 1.7095 > 1`, which this
forbids: some odd run of a cycle has length at least two. -/
theorem oddCount_le_of_noAdjOdd : ∀ (w : List Branch), NoAdjOdd w →
    2 * oddCount w ≤ w.length + 1
  | [], _ => by simp [oddCount]
  | [a], _ => by cases a <;> simp [oddCount]
  | a :: b :: t, h => by
      have hcons : (¬(a = Branch.odd ∧ b = Branch.odd)) ∧ NoAdjOdd (b :: t) :=
        List.isChain_cons_cons.mp h
      obtain ⟨hab, hbt⟩ := hcons
      cases a with
      | even =>
          have ih := oddCount_le_of_noAdjOdd (b :: t) hbt
          simp only [oddCount, List.length_cons] at ih ⊢
          omega
      | odd =>
          have hb : b = Branch.even := by
            cases b with
            | even => rfl
            | odd => exact absurd ⟨rfl, rfl⟩ hab
          subst hb
          have htail : NoAdjOdd t := hbt.tail
          have ih := oddCount_le_of_noAdjOdd t htail
          simp only [oddCount, List.length_cons] at ih ⊢
          omega

end Problems.Juggler
