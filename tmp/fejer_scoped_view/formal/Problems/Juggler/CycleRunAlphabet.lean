import Problems.Juggler.TowerAbsorption
import Problems.Juggler.ItineraryStats

namespace Problems.Juggler

/-!
# Exact run inequalities and conditional word algebra

Floors matter: an odd run has an upper growth bound, not an exact logarithmic
multiplier.  It does not follow that a cycle's height bounds its odd-run length by
the floor-free formula.  This file proves the inequalities below, not a two-block
alphabet for every cycle of height ratio below `27/8`.

* `odd_step_sq_le` and `odd_step_le_sq_add` are the two sides of one odd step.
* `odd_run_upper`: after `r` odd steps, `y^(2^r) ≤ v^(3^r)`, an upper growth bound.
* `even_run_contracts`: after `g` even steps, `z^(2^g) ≤ w`.
* `oo_step_lower`: `x^9 < 2 (z+1)^4`; retain both the factor two and the shift.
* `oddCount_le_of_noAdjOdd`: a linear word has `2 o ≤ L + 1`.
  The cyclic counting argument is separate.  Actual nontrivial cycles satisfy
  `o log(3/2) > e log 2`, not exact closure, by Paper A's floor-defect inequality.
* `walk_eq_discrepancy` assumes exact closure as an abstract algebraic hypothesis;
  it does not identify actual cycle height with centered word discrepancy.

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
`z > x^(9/4) / 2^(1/4) - 1`.  For an `OO` inside `[m, M]`, with the stated intermediate
size condition, it gives `m^9 < 2 (M+1)^4`, not the factor-free inequality. -/
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

/-- **Upper growth on an odd run.**  After `r` odd steps from `v`, the top `y` satisfies
`y^(2^r) ≤ v^(3^r)`.  This inequality alone gives no upper bound on `r` from cycle height. -/
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

/-- A linear word with no two adjacent odd letters has `2 o ≤ L + 1`.
This includes the endpoint allowance; a cyclic no-adjacency argument is separate. -/
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

/-! ## Discrepancy under an explicit zero-drift hypothesis

Write `s = o/L` and `D_t = o_t - t s`.  With the closure `o α = (L - o) β` the walk height
`o_t α - (t - o_t) β` is exactly `(α + β) D_t`.  Without that hypothesis the missing
term is `(t/L) (o α - (L-o) β)`.  With Juggler's logarithmic step sizes a nontrivial
cycle has strictly positive drift, and its actual height also involves floor defects.
No cycle-height identification is proved here. -/

/-- Under the supplied zero-drift hypothesis, the formal walk equals scaled discrepancy. -/
theorem walk_eq_discrepancy {α β : ℝ} {o L t oₜ : ℕ} (hL : 0 < L)
    (hclose : (o : ℝ) * α = ((L : ℝ) - o) * β) :
    (oₜ : ℝ) * α - ((t : ℝ) - oₜ) * β =
      (α + β) * ((oₜ : ℝ) - (t : ℝ) * ((o : ℝ) / L)) := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hβ : (α + β) * ((o : ℝ) / L) = β := by
    field_simp
    linear_combination hclose
  linear_combination (t : ℝ) * hβ

/-- Two even steps land at most at the fourth root, so an `EE` inside a cycle whose values
lie in `[m, M]` forces `m^4 ≤ M`. -/
theorem ee_forces_fourth_power {w : ℕ} (h0 : w % 2 = 0) (h1 : Nat.sqrt w % 2 = 0) :
    (floorPower (floorPower w)) ^ 4 ≤ w := by
  have h := even_run_contracts (w := w) (g := 2) (by
    intro i hi
    interval_cases i
    · simpa using h0
    · simpa using h1)
  simpa using h

/-! ## The minimum must open with three climbing blocks

A cycle minimum has no contracting prefix: `prefixNoncontracting` is exactly the
statement that every prefix has `3^o >= 2^t`.  In the band alphabet the two blocks are
`OE`, which contracts, and `OOE`, which expands, so a minimum cannot open with `OE` and
cannot reach one until enough `OOE` have paid for it.  The arithmetic is finite:
`OOE^k ++ OE` has `o = 2k+1` and `t = 3k+2`, and

  k = 0:  3^1 = 3    < 4    = 2^2
  k = 1:  3^3 = 27   < 32   = 2^5
  k = 2:  3^5 = 243  < 256  = 2^8
  k = 3:  3^7 = 2187 > 2048 = 2^11

so the first three cases are exponent gaps and the fourth is not.  The results below
assume the displayed block prefix; no cycle-height hypothesis supplies this alphabet. -/

/-- The band's falling block. -/
def oeBlock : List Branch := [Branch.odd, Branch.even]

/-- The band's climbing block. -/
def ooeBlock : List Branch := [Branch.odd, Branch.odd, Branch.even]

/-- `k` climbing blocks in a row. -/
def climbRun : ℕ → List Branch
  | 0 => []
  | k + 1 => ooeBlock ++ climbRun k

@[simp] theorem climbRun_length (k : ℕ) : (climbRun k).length = 3 * k := by
  induction k with
  | zero => simp [climbRun]
  | succ k ih => simp [climbRun, ooeBlock, ih]; ring

@[simp] theorem climbRun_oddCount (k : ℕ) : oddCount (climbRun k) = 2 * k := by
  induction k with
  | zero => simp [climbRun]
  | succ k ih =>
      simp [climbRun, ooeBlock, ih]
      ring

/-- `OOE^k ++ OE` is an exponent gap exactly while `k ≤ 2`. -/
theorem climbRun_append_oe_exponentGap {k : ℕ} (hk : k ≤ 2) :
    exponentGap (climbRun k ++ oeBlock) := by
  have hlen : (climbRun k ++ oeBlock).length = 3 * k + 2 := by
    simp [oeBlock]
  have hodd : oddCount (climbRun k ++ oeBlock) = 2 * k + 1 := by
    simp [oeBlock, oddCount_append, oddCount]
  unfold exponentGap
  rw [hlen, hodd]
  interval_cases k <;> norm_num

/-- **A band cycle minimum opens with at least three climbing blocks.**  If the itinerary
of a prefix-noncontracting word begins with `k` copies of `OOE` and then an `OE`, then
`k ≥ 3`.  An application to a cycle must independently establish this block prefix. -/
theorem band_min_needs_three_climbs {k : ℕ} {v : List Branch}
    (h : prefixNoncontracting (climbRun k ++ oeBlock ++ v)) : 3 ≤ k := by
  by_contra hlt
  have hk : k ≤ 2 := by omega
  have hassoc : climbRun k ++ oeBlock ++ v = (climbRun k ++ oeBlock) ++ v := by
    simp [List.append_assoc]
  have hlen : (climbRun k ++ oeBlock).length = 3 * k + 2 := by simp [oeBlock]
  have htake : (climbRun k ++ oeBlock ++ v).take (3 * k + 2) = climbRun k ++ oeBlock := by
    rw [hassoc]
    exact List.take_left' hlen
  have hle : 3 * k + 2 ≤ (climbRun k ++ oeBlock ++ v).length := by
    rw [hassoc, List.length_append, hlen]
    omega
  have hgap : exponentGap ((climbRun k ++ oeBlock ++ v).take (3 * k + 2)) := by
    rw [htake]
    exact climbRun_append_oe_exponentGap hk
  exact (h (3 * k + 2) hle) hgap

/-- The opening itself: three climbing blocks are nine letters, `OOEOOEOOE`. -/
theorem climbRun_three :
    climbRun 3 = [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd,
                  Branch.even, Branch.odd, Branch.odd, Branch.even] := by
  simp [climbRun, ooeBlock]

/-- After three climbing blocks and one fall, a second fall is an exponent gap:
`OOE^3 ++ OE ++ OE` has `o = 8`, `t = 13`, and `3^8 = 6561 < 8192 = 2^13`. -/
theorem climbRun_three_two_falls_exponentGap :
    exponentGap (climbRun 3 ++ oeBlock ++ oeBlock) := by
  unfold exponentGap
  norm_num [climbRun, ooeBlock, oeBlock, oddCount]

/-- **The fall cannot repeat.**  A prefix-noncontracting word cannot open with three
climbing blocks and then two falls.  If the next block is independently known to belong
to `{OE, OOE}`, it must be `OOE`.  Neither that alphabet nor the first fall's location
is a conclusion of a cycle-height bound here. -/
theorem band_min_no_second_fall {v : List Branch}
    (h : prefixNoncontracting (climbRun 3 ++ oeBlock ++ oeBlock ++ v)) : False := by
  have hassoc : climbRun 3 ++ oeBlock ++ oeBlock ++ v
      = (climbRun 3 ++ oeBlock ++ oeBlock) ++ v := by
    simp [List.append_assoc]
  have hlen : (climbRun 3 ++ oeBlock ++ oeBlock).length = 13 := by
    simp [climbRun, ooeBlock, oeBlock]
  have htake : (climbRun 3 ++ oeBlock ++ oeBlock ++ v).take 13
      = climbRun 3 ++ oeBlock ++ oeBlock := by
    rw [hassoc]
    exact List.take_left' hlen
  have hle : 13 ≤ (climbRun 3 ++ oeBlock ++ oeBlock ++ v).length := by
    rw [hassoc, List.length_append, hlen]
    omega
  have hgap : exponentGap ((climbRun 3 ++ oeBlock ++ oeBlock ++ v).take 13) := by
    rw [htake]
    exact climbRun_three_two_falls_exponentGap
  exact (h 13 hle) hgap

end Problems.Juggler
