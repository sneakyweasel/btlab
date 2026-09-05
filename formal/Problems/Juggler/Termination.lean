import Mathlib.Tactic
import Problems.Juggler.Iteration

set_option maxRecDepth 4000000

namespace Problems.Juggler

/-!
# Hitting 1

`ReachesOne` is the trajectory predicate `∃ k, T^[k] n = 1`. This file does
not mention words or certificates. Finite seed identities live here as
examples, not as a map theorem.
-/

def ReachesOne (n : ℕ) : Prop :=
  ∃ k, floorPower^[k] n = 1

theorem reachesOne_one : ReachesOne 1 :=
  ⟨0, rfl⟩

theorem reachesOne_of_iterate {n m k : ℕ}
    (h : floorPower^[k] n = m) (hm : ReachesOne m) : ReachesOne n := by
  obtain ⟨j, hj⟩ := hm
  refine ⟨k + j, ?_⟩
  rw [Nat.add_comm, Function.iterate_add_apply, h, hj]

/-- Packet seed `13` reaches `1` in four steps. Not a map theorem. -/
theorem floorPower_thirteen_reaches_one :
    (floorPower^[4] 13) = 1 := by
  decide +kernel

theorem two_reachesOne : ReachesOne 2 :=
  ⟨1, by
    change floorPower 2 = 1
    exact floorPower_two⟩

theorem four_reachesOne : ReachesOne 4 :=
  reachesOne_of_iterate (k := 1) (by
    change floorPower 4 = 2
    exact floorPower_four) two_reachesOne

theorem six_reachesOne : ReachesOne 6 :=
  reachesOne_of_iterate (k := 1) (by
    change floorPower 6 = 2
    exact floorPower_six) two_reachesOne

theorem eight_reachesOne : ReachesOne 8 :=
  reachesOne_of_iterate (k := 1) (by
    change floorPower 8 = 2
    exact floorPower_eight) two_reachesOne

theorem three_reachesOne : ReachesOne 3 :=
  ⟨6, by decide +kernel⟩

theorem five_reachesOne : ReachesOne 5 :=
  ⟨5, by decide +kernel⟩

theorem seven_reachesOne : ReachesOne 7 :=
  ⟨4, by decide +kernel⟩

theorem nine_reachesOne : ReachesOne 9 :=
  ⟨7, by decide +kernel⟩

theorem ten_reachesOne : ReachesOne 10 :=
  reachesOne_of_iterate (k := 1) (by
    change floorPower 10 = 3
    decide +kernel) three_reachesOne

theorem eleven_reachesOne : ReachesOne 11 :=
  ⟨4, by decide +kernel⟩

/-- Every positive residual strictly below `12` is `ReachesOne`.
This is a finite certificate, not a halt theorem. -/
theorem reachesOne_of_lt_twelve {y : ℕ} (hpos : 1 ≤ y) (hy : y < 12) :
    ReachesOne y := by
  match y with
  | 0 => omega
  | 1 => exact reachesOne_one
  | 2 => exact two_reachesOne
  | 3 => exact three_reachesOne
  | 4 => exact four_reachesOne
  | 5 => exact five_reachesOne
  | 6 => exact six_reachesOne
  | 7 => exact seven_reachesOne
  | 8 => exact eight_reachesOne
  | 9 => exact nine_reachesOne
  | 10 => exact ten_reachesOne
  | 11 => exact eleven_reachesOne
  | _ + 12 => omega

/-- A positive non-`ReachesOne` value cannot lie in `{1,…,11}`. -/
theorem non_reachesOne_ge_twelve {n : ℕ} (hn : 1 ≤ n) (hfail : ¬ReachesOne n) :
    12 ≤ n := by
  by_contra h
  exact hfail (reachesOne_of_lt_twelve hn (Nat.not_le.mp h))

/-- One even step into `{1,…,11}`: every even `n` with `1 ≤ n < 144`
is `ReachesOne`. Not a halt theorem. -/
theorem even_lt_sq_twelve_reachesOne {n : ℕ} (heven : n % 2 = 0)
    (hpos : 1 ≤ n) (hn : n < 144) : ReachesOne n := by
  have hsqrt : n.sqrt < 12 := by
    rw [Nat.sqrt_lt]
    simpa using hn
  have himg : floorPower n < 12 := by
    rw [floorPower_even_eq heven]
    exact hsqrt
  exact reachesOne_of_iterate (k := 1) rfl
    (reachesOne_of_lt_twelve (floorPower_pos hpos) himg)

theorem thirteen_reachesOne : ReachesOne 13 :=
  ⟨4, floorPower_thirteen_reaches_one⟩

theorem fifteen_reachesOne : ReachesOne 15 :=
  ⟨6, by decide +kernel⟩

theorem seventeen_reachesOne : ReachesOne 17 :=
  ⟨4, by decide +kernel⟩

theorem nineteen_reachesOne : ReachesOne 19 :=
  ⟨9, by decide +kernel⟩

theorem twentyone_reachesOne : ReachesOne 21 :=
  ⟨9, by decide +kernel⟩

theorem twentythree_reachesOne : ReachesOne 23 :=
  ⟨9, by decide +kernel⟩

theorem twentyfive_reachesOne : ReachesOne 25 :=
  ⟨11, by decide +kernel⟩

theorem twentyseven_reachesOne : ReachesOne 27 :=
  ⟨6, by decide +kernel⟩

theorem twentynine_reachesOne : ReachesOne 29 :=
  ⟨9, by decide +kernel⟩

theorem thirtyone_reachesOne : ReachesOne 31 :=
  ⟨6, by decide +kernel⟩

theorem thirtythree_reachesOne : ReachesOne 33 :=
  ⟨8, by decide +kernel⟩

theorem thirtyfive_reachesOne : ReachesOne 35 :=
  ⟨8, by decide +kernel⟩

theorem thirtyseven_reachesOne : ReachesOne 37 :=
  ⟨17, by decide +kernel⟩

theorem thirtynine_reachesOne : ReachesOne 39 :=
  ⟨14, by decide +kernel⟩

theorem fortyone_reachesOne : ReachesOne 41 :=
  ⟨5, by decide +kernel⟩

theorem fortythree_reachesOne : ReachesOne 43 :=
  ⟨6, by decide +kernel⟩

theorem fortyfive_reachesOne : ReachesOne 45 :=
  ⟨6, by decide +kernel⟩

theorem fortyseven_reachesOne : ReachesOne 47 :=
  ⟨6, by decide +kernel⟩

theorem fortynine_reachesOne : ReachesOne 49 :=
  ⟨11, by decide +kernel⟩

theorem fiftyone_reachesOne : ReachesOne 51 :=
  ⟨11, by decide +kernel⟩

/-- Every positive residual strictly below `53` is `ReachesOne`.
This is a finite certificate, not a halt theorem. Combined with
`cycleMin_finance` it excludes cycle length `11`. -/
theorem reachesOne_of_lt_fifty_three {y : ℕ} (hpos : 1 ≤ y) (hy : y < 53) :
    ReachesOne y := by
  cases Nat.mod_two_eq_zero_or_one y with
  | inl heven =>
      exact even_lt_sq_twelve_reachesOne heven hpos
        (lt_trans hy (by norm_num : (53 : ℕ) < 144))
  | inr hodd =>
      interval_cases y <;> first
        | exact reachesOne_one
        | exact three_reachesOne
        | exact five_reachesOne
        | exact seven_reachesOne
        | exact nine_reachesOne
        | exact eleven_reachesOne
        | exact thirteen_reachesOne
        | exact fifteen_reachesOne
        | exact seventeen_reachesOne
        | exact nineteen_reachesOne
        | exact twentyone_reachesOne
        | exact twentythree_reachesOne
        | exact twentyfive_reachesOne
        | exact twentyseven_reachesOne
        | exact twentynine_reachesOne
        | exact thirtyone_reachesOne
        | exact thirtythree_reachesOne
        | exact thirtyfive_reachesOne
        | exact thirtyseven_reachesOne
        | exact thirtynine_reachesOne
        | exact fortyone_reachesOne
        | exact fortythree_reachesOne
        | exact fortyfive_reachesOne
        | exact fortyseven_reachesOne
        | exact fortynine_reachesOne
        | exact fiftyone_reachesOne
        | omega

/-- A positive non-`ReachesOne` value cannot lie in `{1,…,52}`. -/
theorem non_reachesOne_ge_fifty_three {n : ℕ} (hn : 1 ≤ n)
    (hfail : ¬ReachesOne n) : 53 ≤ n := by
  by_contra h
  exact hfail (reachesOne_of_lt_fifty_three hn (Nat.not_le.mp h))

/-- One even step into `{1,…,52}`: every even `n` with `1 ≤ n < 2809`
is `ReachesOne`. Not a halt theorem. -/
theorem even_lt_sq_fifty_three_reachesOne {n : ℕ} (heven : n % 2 = 0)
    (hpos : 1 ≤ n) (hn : n < 2809) : ReachesOne n := by
  have hsqrt : n.sqrt < 53 := by
    rw [Nat.sqrt_lt]
    simpa using hn
  have himg : floorPower n < 53 := by
    rw [floorPower_even_eq heven]
    exact hsqrt
  exact reachesOne_of_iterate (k := 1) rfl
    (reachesOne_of_lt_fifty_three (floorPower_pos hpos) himg)

end Problems.Juggler
