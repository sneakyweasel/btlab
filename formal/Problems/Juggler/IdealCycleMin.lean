import Problems.Juggler.EvenCountThree
import Problems.Juggler.O7EEEEGap
import Problems.Juggler.CycleMinFudge
import Problems.Juggler.WalkChargeItineraries

namespace Problems.Juggler

/-!
# CycleMin shape catalog and balloon stations

Laboratory wrapper. Existing CycleMin theorems already fix the forced
letters and the interval bounds. This file names that shape and the
only allowed UI alphabet. It does not reprove Paper A, does not raise
a floor, and is not a halt theorem.

Imported by `Problems.Juggler` only. Not a `JugglerPaper` review object.

Lemma 3.21b's full e-run form
`w = O^{a₁} E ⋯ O^{aₑ} E` with `a₁ ≥ 2` is `EXACT — HUMAN PROOF`.
Lean wraps the first block (`oddEvenBlock`, `cycleMin_exists_oddEven_split`)
and the last odd-run (`exists_cycleMin_last_odd_run`). Unused middle
runs stay interval slots, not beads.
-/

/-! ## Shape -/

/-- Combinatorial CycleMin shape: forced letters plus interval bounds.
    A leftover word may inhabit the shape without being a cycle. -/
structure CycleMinShape (w : List Branch) : Prop where
  evenCount_ge_four : 4 ≤ evenCount w
  oddCount_ge_seven : 7 ≤ oddCount w
  lastOddRun_le_one :
    ∃ u a, w = u ++ List.replicate a Branch.odd ++ [Branch.even] ∧
      a ≤ 1 ∧ (u = [] ∨ u.getLast? = some Branch.even)
  startsTwoOdds : ∃ rest, w = Branch.odd :: Branch.odd :: rest
  endsEven : w.getLast? = some Branch.even
  expanding : 2 ^ w.length < 3 ^ oddCount w
  length_ge_eleven : 11 ≤ w.length

theorem two_pow_add_four_lt_three_pow {o : ℕ}
    (h : 2 ^ (o + 4) < 3 ^ o) : 7 ≤ o := by
  by_contra hlt
  have : o ≤ 6 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  interval_cases o <;> exact absurd h (by decide)

theorem cycleMin_oddCount_ge_seven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : 7 ≤ oddCount w := by
  have he := cycle_itinerary_even_count_ge_four hn h.1
  have hexp := cycle_itinerary_formally_expanding hn h.1
  have hsum := evenCount_add_oddCount w
  have hlen : oddCount w + 4 ≤ w.length := by omega
  have hpow : 2 ^ (oddCount w + 4) ≤ 2 ^ w.length :=
    Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) hlen
  exact two_pow_add_four_lt_three_pow (lt_of_le_of_lt hpow hexp)

theorem cycleMin_unplaced_odds_ge_five {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : 5 ≤ oddCount w - 2 := by
  have ho := cycleMin_oddCount_ge_seven hn h
  omega

theorem cycleMin_extra_evens_ge_zero {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : 0 ≤ evenCount w - 4 := by
  have he := cycle_itinerary_even_count_ge_four hn h.1
  omega

theorem cycleMin_last_odd_run_mem {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ u a, w = u ++ List.replicate a Branch.odd ++ [Branch.even] ∧
      a ≤ 1 ∧ (u = [] ∨ u.getLast? = some Branch.even) :=
  exists_cycleMin_last_odd_run hn h

theorem cycleMin_inhabits_shape {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : CycleMinShape w where
  evenCount_ge_four := cycle_itinerary_even_count_ge_four hn h.1
  oddCount_ge_seven := cycleMin_oddCount_ge_seven hn h
  lastOddRun_le_one := exists_cycleMin_last_odd_run hn h
  startsTwoOdds := cycleMin_starts_two_odds hn h
  endsEven := cycleMin_getLast_even hn h
  expanding := cycle_itinerary_formally_expanding hn h.1
  length_ge_eleven := cycle_itinerary_length_ge_eleven hn h.1

theorem cycle_has_cycleMin {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    ∃ k < w.length, CycleMin (floorPower^[k] n) (rotateItinerary w k) :=
  exists_cycleMin hn h

/-! ## First-block and even roles -/

/-- First-run wrap of Lemma 3.21b: `O^{a₁} E` plus a tail, `a₁ ≥ 2`. -/
theorem cycleMin_run_form_first_block {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ a v, 2 ≤ a ∧ w = oddEvenBlock a 1 ++ v := by
  obtain ⟨a, v, hw⟩ := cycleMin_exists_oddEven_split hn h
  refine ⟨a, v, cycleMin_oddEvenBlock_starts_two_odds hn (by simpa [hw] using h), hw⟩

theorem cycleMin_first_even_role {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ a v, w = oddEvenBlock a 1 ++ v ∧
      (n + 1) ^ 2 ≤ image n (List.replicate a Branch.odd) ∧
        n < image n (oddEvenBlock a 1) := by
  obtain ⟨a, v, hw⟩ := cycleMin_exists_oddEven_split hn h
  refine ⟨a, v, hw, cycleMin_first_even_overshoots hn (by simpa [hw] using h)⟩

theorem cycleMin_last_even_role {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ u, w = u ++ [Branch.even] ∧
      n ^ 2 ≤ image n u ∧ image n u < (n + 1) ^ 2 := by
  obtain ⟨u, hu⟩ := (List.getLast?_eq_some_iff).mp (cycleMin_getLast_even hn h)
  exact ⟨u, hu, cycle_last_even_interval (by simpa [hu] using h.1)⟩

theorem cycleMin_hug_prefix_odds {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∀ k, k ≤ w.length → hugOdds k ≤ oddCount (w.take k) :=
  cycleMin_prefix_odds_ge_hug hn h

/-! ## Balloon stations: the only allowed UI alphabet -/

inductive EvenRole
  | first
  | middle
  | last
  deriving DecidableEq, Repr

inductive IntervalOddKind
  | a1Extras
  | middle
  | lastZeroOrOne
  deriving DecidableEq, Repr

/-- Sure letters and interval slots. There is no unknown-letter bead. -/
inductive BalloonStation
  | sureLaunchO
  | sureEven (role : EvenRole)
  | intervalOdd (kind : IntervalOddKind)
  | intervalExtraEven
  deriving DecidableEq, Repr

def BalloonStation.isForced : BalloonStation → Bool
  | .sureLaunchO | .sureEven _ => true
  | .intervalOdd _ | .intervalExtraEven => false

def BalloonStation.sureLetterCount : BalloonStation → ℕ
  | .sureLaunchO => 2
  | .sureEven _ => 1
  | .intervalOdd _ | .intervalExtraEven => 0

def BalloonStation.intervalMin : BalloonStation → Option ℕ
  | .intervalOdd _ | .intervalExtraEven => some 0
  | .sureLaunchO | .sureEven _ => none

def BalloonStation.intervalMax : BalloonStation → Option ℕ
  | .intervalOdd .lastZeroOrOne => some 1
  | .intervalOdd .a1Extras | .intervalOdd .middle
  | .intervalExtraEven | .sureLaunchO | .sureEven _ => none

/-- Unique figure schema in CycleMin reading order.
    Six sure letters (`OO` + four `E`); interval slots are bounds. -/
def balloonSchema : List BalloonStation :=
  [ .sureLaunchO
  , .intervalOdd .a1Extras
  , .sureEven .first
  , .intervalOdd .middle
  , .sureEven .middle
  , .sureEven .middle
  , .intervalOdd .lastZeroOrOne
  , .sureEven .last
  , .intervalExtraEven
  ]

def balloonSchemaForced : List BalloonStation :=
  balloonSchema.filter BalloonStation.isForced

theorem balloonSchema_forced_eq :
    balloonSchemaForced =
      [.sureLaunchO, .sureEven .first, .sureEven .middle,
        .sureEven .middle, .sureEven .last] :=
  rfl

theorem balloonSchema_sure_letter_count :
    (balloonSchemaForced.map BalloonStation.sureLetterCount).sum = 6 :=
  rfl

theorem balloonSchema_sure_even_count :
    (balloonSchemaForced.filter fun s =>
      match s with
      | .sureEven _ => true
      | _ => false).length = 4 :=
  rfl

theorem balloonSchema_sure_launch_repeat :
    BalloonStation.sureLetterCount .sureLaunchO = 2 :=
  rfl

theorem last_odd_interval_bounds :
    BalloonStation.intervalMin (.intervalOdd .lastZeroOrOne) = some 0 ∧
      BalloonStation.intervalMax (.intervalOdd .lastZeroOrOne) = some 1 :=
  ⟨rfl, rfl⟩

theorem extra_even_interval_min_zero :
    BalloonStation.intervalMin .intervalExtraEven = some 0 ∧
      BalloonStation.intervalMax .intervalExtraEven = none :=
  ⟨rfl, rfl⟩

theorem balloonStation_cases (s : BalloonStation) :
    s = .sureLaunchO ∨ (∃ r, s = .sureEven r) ∨
      (∃ k, s = .intervalOdd k) ∨ s = .intervalExtraEven := by
  cases s <;> simp

theorem balloonStation_forced_iff (s : BalloonStation) :
    s.isForced = true ↔ s = .sureLaunchO ∨ ∃ r, s = .sureEven r := by
  cases s <;> simp [BalloonStation.isForced]

theorem interval_station_not_forced :
    ¬ BalloonStation.isForced (.intervalOdd .a1Extras) ∧
      ¬ BalloonStation.isForced (.intervalOdd .middle) ∧
        ¬ BalloonStation.isForced (.intervalOdd .lastZeroOrOne) ∧
          ¬ BalloonStation.isForced .intervalExtraEven := by
  simp [BalloonStation.isForced]

/-- Every CycleMin word fills the sure stations of `balloonSchema`.
    Interval stations are not forced. -/
theorem cycleMin_projects_balloonSchema {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    CycleMinShape w ∧
      (∃ rest, w = Branch.odd :: Branch.odd :: rest) ∧
        (∃ a v, 2 ≤ a ∧ w = oddEvenBlock a 1 ++ v) ∧
          w.getLast? = some Branch.even ∧
            4 ≤ evenCount w ∧ 0 ≤ evenCount w - 4 ∧
              5 ≤ oddCount w - 2 :=
  ⟨cycleMin_inhabits_shape hn h,
    cycleMin_starts_two_odds hn h,
    cycleMin_run_form_first_block hn h,
    cycleMin_getLast_even hn h,
    cycle_itinerary_even_count_ge_four hn h.1,
    cycleMin_extra_evens_ge_zero hn h,
    cycleMin_unplaced_odds_ge_five hn h⟩

theorem sure_mem_balloonSchemaForced :
    BalloonStation.sureLaunchO ∈ balloonSchemaForced ∧
      BalloonStation.sureEven .first ∈ balloonSchemaForced ∧
        BalloonStation.sureEven .middle ∈ balloonSchemaForced ∧
          BalloonStation.sureEven .last ∈ balloonSchemaForced := by
  rw [balloonSchema_forced_eq]
  exact ⟨List.Mem.head _,
    List.Mem.tail _ (List.Mem.head _),
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩

/-- No station outside the sure list is forced by the shape. -/
theorem no_forced_station_outside_sure (s : BalloonStation)
    (hs : s ∉ balloonSchemaForced) : s.isForced = false := by
  cases s with
  | sureLaunchO =>
      exact (hs sure_mem_balloonSchemaForced.1).elim
  | sureEven r =>
      cases r with
      | first => exact (hs sure_mem_balloonSchemaForced.2.1).elim
      | middle => exact (hs sure_mem_balloonSchemaForced.2.2.1).elim
      | last => exact (hs sure_mem_balloonSchemaForced.2.2.2).elim
  | intervalOdd k =>
      cases k <;> rfl
  | intervalExtraEven => rfl

/-! ## Leftovers inhabit the shape and are not cycles -/

theorem leftover_O7EEEE_split :
    itineraryO7EEEE =
      (sevenOdds ++ List.replicate 3 Branch.even) ++
        List.replicate 0 Branch.odd ++ [Branch.even] := by
  have h4 : List.replicate 4 Branch.even =
      List.replicate 3 Branch.even ++ [Branch.even] := rfl
  simp [itineraryO7EEEE, h4]

theorem leftover_O7EEEE_prefix_ends_even :
    (sevenOdds ++ List.replicate 3 Branch.even).getLast? = some Branch.even := by
  decide

theorem leftover_O7EEEE_inhabits_shape : CycleMinShape itineraryO7EEEE where
  evenCount_ge_four := by decide
  oddCount_ge_seven := by decide
  lastOddRun_le_one :=
    ⟨sevenOdds ++ List.replicate 3 Branch.even, 0,
      leftover_O7EEEE_split, Nat.zero_le _, Or.inr leftover_O7EEEE_prefix_ends_even⟩
  startsTwoOdds := ⟨List.replicate 5 Branch.odd ++ List.replicate 4 Branch.even, by
    simp [itineraryO7EEEE, sevenOdds, List.replicate_succ]⟩
  endsEven := by decide
  expanding := by decide
  length_ge_eleven := by decide

theorem leftover_O7EEEE_not_cycle {n : ℕ} :
    ¬ CycleItinerary n itineraryO7EEEE :=
  no_cycle_itinerary_oooooooeeee

theorem leftover_O6EEEOE_eq : fourEvenWord 6 0 0 1 =
    List.replicate 6 Branch.odd ++
      [Branch.even, Branch.even, Branch.even, Branch.odd, Branch.even] := by
  simp [fourEvenWord]

theorem leftover_O6EEEOE_inhabits_shape :
    CycleMinShape (fourEvenWord 6 0 0 1) where
  evenCount_ge_four := by decide
  oddCount_ge_seven := by decide
  lastOddRun_le_one :=
    ⟨List.replicate 6 Branch.odd ++ [Branch.even, Branch.even, Branch.even], 1,
      by simp [fourEvenWord], by omega, by
      right
      simp⟩
  startsTwoOdds := ⟨List.replicate 4 Branch.odd ++
      [Branch.even, Branch.even, Branch.even, Branch.odd, Branch.even], by
    simp [fourEvenWord, List.replicate_succ]⟩
  endsEven := by decide
  expanding := by decide
  length_ge_eleven := by decide

theorem leftover_O6EEEOE_not_cycle {n : ℕ} (hn : 2 ≤ n) :
    ¬ CycleItinerary n (fourEvenWord 6 0 0 1) :=
  no_cycle_itinerary_ooooooeeeoe hn

/-- (1,3) EEE leftovers are CycleMin-shaped four-even words and do not
    close. They fill intervals; they are not stations. -/
theorem leftover_one_three_eee_not_cycleMin {n a0 a1 : ℕ}
    (hmem : fourEvenWord a0 a1 0 0 ∈ fudgeWords) :
    ¬ CycleMin n (fourEvenWord a0 a1 0 0) :=
  no_cycleMin_one_three_eee hmem

end Problems.Juggler
