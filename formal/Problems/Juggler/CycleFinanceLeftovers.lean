import Problems.Juggler.CycleFinance
import Problems.Juggler.LengthEightCensus
import Problems.Juggler.Termination
import Problems.Juggler.TerminationFloor257
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Problems.Juggler

/-!
# Cycle finance leftovers: the length census at floors 53/257/261

Laboratory companion of `CycleFinance.lean`: everything the
finance inequality (Theorem 4.4) buys once the certified residual
floors are injected.

Every cycle state is at least `261`
(`cycleItinerary_iterate_not_lt_two_hundred_sixty_one`) and the
rotated minimum is odd (`cycleMin_start_odd`), so the minimum is
at least `261` and `n * log n >= 261 * log 257 > 15921/11`.
This excludes cycle lengths wholesale. The residual floor `261`
(`reachesOne_of_lt_two_hundred_sixty_one`) kills the cheap
leftovers `57` and `76`. Together with
`no_cycle_itinerary_length_le_eighteen` the census extends to
`no_cycle_itinerary_length_le_nineteen`, lengths `20`–`83` die by
the same comparison table (`financeRows53` / `financeRows257` /
`financeRows261`), and any remaining cycle has period `84` or
at least `85`.

Eliahou packaging (`cycle_itinerary_eliahou_leftover`) rewrites that
leftover plus the computational finance table as: period `84`, or
a listed near-convergent, or at least `10^5`. Not a new
inequality.

Dossier: `docs/problems/juggler_cycle_finance.md`. Writeup:
Paper A Section 4; the leftover `84` is an Appendix A companion,
not the printed leftover. The height leftover
(`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`)
lives in `CycleHeightFinance.lean`. This is not a halt theorem
and not a leftover-itinerary census named
`no_cycle_itinerary_length_eleven`. Length `84` is the next record
near-convergent leftover at the Lean floor.
-/
/-- Rotation preserves the odd count. -/
theorem oddCount_rotateItinerary : ∀ (k : ℕ) (w : List Branch),
    oddCount (rotateItinerary w k) = oddCount w := by
  intro k
  induction k with
  | zero => intro w; rfl
  | succ k ih =>
    intro w
    cases w with
    | nil => rfl
    | cons b rest =>
      have hrot : rotateItinerary (b :: rest) (k + 1) =
          rotateItinerary (rest ++ [b]) k := rfl
      rw [hrot, ih, oddCount_append]
      cases b <;> simp [oddCount]

/-- Numeric certificate `log 13 > 5/2`, via `e^5 < 169`. -/
theorem log_thirteen_gt : (5 / 2 : ℝ) < Real.log 13 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 13)]
  have hsq : Real.exp (5 / 2) ^ 2 = Real.exp 5 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hpow : Real.exp 1 ^ (5 : ℕ) = Real.exp 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hlt : Real.exp 1 ^ (5 : ℕ) < (2.7182818286 : ℝ) ^ (5 : ℕ) := by
    gcongr
    exact Real.exp_one_lt_d9
  have hnum : (2.7182818286 : ℝ) ^ (5 : ℕ) < 169 := by norm_num
  have h169 : Real.exp (5 / 2) ^ 2 < 169 := by
    rw [hsq, ← hpow]
    linarith
  nlinarith [Real.exp_pos (5 / 2 : ℝ), h169,
    sq_nonneg (Real.exp (5 / 2) - 13)]

/-- Finance at the rotated odd minimum: every cycle itinerary satisfies
`(65/2)(3^o - 2^L) ≤ L 3^o`, because the minimum is at least `13`
and `13 log 13 > 65/2`. -/
theorem cycle_finance_min_thirteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (65 / 2 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w := by
  obtain ⟨k, hkL, hmin⟩ := exists_cycleMin hn h
  have hm12 : 12 ≤ floorPower^[k] n := cycleItinerary_iterate_not_lt_twelve hn h
  have hm2 : 2 ≤ floorPower^[k] n := by omega
  have hmodd : (floorPower^[k] n) % 2 = 1 := cycleMin_start_odd hm2 hmin
  have hm13 : 13 ≤ floorPower^[k] n := by omega
  have hfin := cycleMin_finance hm2 hmin
  rw [rotateItinerary_length, oddCount_rotateItinerary] at hfin
  have hexpand : (2 : ℝ) ^ w.length < (3 : ℝ) ^ oddCount w := by
    exact_mod_cast cycle_itinerary_formally_expanding hn h
  have hm13R : (13 : ℝ) ≤ (floorPower^[k] n : ℝ) := by exact_mod_cast hm13
  have hlog : (5 / 2 : ℝ) ≤ Real.log (floorPower^[k] n) := by
    have hmono : Real.log (13 : ℝ) ≤ Real.log (floorPower^[k] n) := by
      gcongr
    linarith [log_thirteen_gt]
  have hmlog : (65 / 2 : ℝ) ≤
      (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) := by
    have h1 : (13 : ℝ) * (5 / 2) ≤
        (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) :=
      mul_le_mul hm13R hlog (by norm_num) (by linarith)
    linarith
  calc (65 / 2 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length)
      ≤ (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) *
          ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) :=
        mul_le_mul_of_nonneg_right hmlog (by linarith)
    _ ≤ (w.length : ℝ) * (3 : ℝ) ^ oddCount w := hfin

/-- No cycle itinerary of length `9`: `o ≥ 6` forces
`(65/2)(3^o - 512) > 9 · 3^o`. -/
theorem no_cycle_itinerary_length_nine {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 9) : ¬CycleItinerary n w := by
  intro h
  have hfin := cycle_finance_min_thirteen hn h
  have hexp := cycle_itinerary_formally_expanding hn h
  rw [hlen] at hfin hexp
  have ho : 6 ≤ oddCount w := by
    by_contra hc
    push Not at hc
    have hle : (3 : ℕ) ^ oddCount w ≤ 3 ^ 5 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 9 < 3 ^ 5 := lt_of_lt_of_le hexp hle
    norm_num at this
  have hA : (729 : ℕ) ≤ 3 ^ oddCount w := by
    calc (729 : ℕ) = 3 ^ 6 := by norm_num
      _ ≤ 3 ^ oddCount w := Nat.pow_le_pow_right (by norm_num) ho
  have hAR : (729 : ℝ) ≤ (3 : ℝ) ^ oddCount w := by exact_mod_cast hA
  norm_num at hfin
  linarith

/-- No cycle itinerary of length `10`: `o ≥ 7` forces
`(65/2)(3^o - 1024) > 10 · 3^o`. -/
theorem no_cycle_itinerary_length_ten {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 10) : ¬CycleItinerary n w := by
  intro h
  have hfin := cycle_finance_min_thirteen hn h
  have hexp := cycle_itinerary_formally_expanding hn h
  rw [hlen] at hfin hexp
  have ho : 7 ≤ oddCount w := by
    by_contra hc
    push Not at hc
    have hle : (3 : ℕ) ^ oddCount w ≤ 3 ^ 6 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 10 < 3 ^ 6 := lt_of_lt_of_le hexp hle
    norm_num at this
  have hA : (2187 : ℕ) ≤ 3 ^ oddCount w := by
    calc (2187 : ℕ) = 3 ^ 7 := by norm_num
      _ ≤ 3 ^ oddCount w := Nat.pow_le_pow_right (by norm_num) ho
  have hAR : (2187 : ℝ) ≤ (3 : ℝ) ^ oddCount w := by exact_mod_cast hA
  norm_num at hfin
  linarith

/-- No cycle itinerary of length `12`: `o ≥ 8` forces
`(65/2)(3^o - 4096) > 12 · 3^o` (margin `6561 > 6494`). -/
theorem no_cycle_itinerary_length_twelve {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 12) : ¬CycleItinerary n w := by
  intro h
  have hfin := cycle_finance_min_thirteen hn h
  have hexp := cycle_itinerary_formally_expanding hn h
  rw [hlen] at hfin hexp
  have ho : 8 ≤ oddCount w := by
    by_contra hc
    push Not at hc
    have hle : (3 : ℕ) ^ oddCount w ≤ 3 ^ 7 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 12 < 3 ^ 7 := lt_of_lt_of_le hexp hle
    norm_num at this
  have hA : (6561 : ℕ) ≤ 3 ^ oddCount w := by
    calc (6561 : ℕ) = 3 ^ 8 := by norm_num
      _ ≤ 3 ^ oddCount w := Nat.pow_le_pow_right (by norm_num) ho
  have hAR : (6561 : ℝ) ≤ (3 : ℝ) ^ oddCount w := by exact_mod_cast hA
  norm_num at hfin
  linarith

/-- No cycle itinerary of length `13`: `o ≥ 9` forces
`(65/2)(3^o - 8192) > 13 · 3^o`. -/
theorem no_cycle_itinerary_length_thirteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 13) : ¬CycleItinerary n w := by
  intro h
  have hfin := cycle_finance_min_thirteen hn h
  have hexp := cycle_itinerary_formally_expanding hn h
  rw [hlen] at hfin hexp
  have ho : 9 ≤ oddCount w := by
    by_contra hc
    push Not at hc
    have hle : (3 : ℕ) ^ oddCount w ≤ 3 ^ 8 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 13 < 3 ^ 8 := lt_of_lt_of_le hexp hle
    norm_num at this
  have hA : (19683 : ℕ) ≤ 3 ^ oddCount w := by
    calc (19683 : ℕ) = 3 ^ 9 := by norm_num
      _ ≤ 3 ^ oddCount w := Nat.pow_le_pow_right (by norm_num) ho
  have hAR : (19683 : ℝ) ≤ (3 : ℝ) ^ oddCount w := by exact_mod_cast hA
  norm_num at hfin
  linarith

/-- No cycle itinerary of length `16`: `o ≥ 11` forces
`(65/2)(3^o - 65536) > 16 · 3^o`. -/
theorem no_cycle_itinerary_length_sixteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 16) : ¬CycleItinerary n w := by
  intro h
  have hfin := cycle_finance_min_thirteen hn h
  have hexp := cycle_itinerary_formally_expanding hn h
  rw [hlen] at hfin hexp
  have ho : 11 ≤ oddCount w := by
    by_contra hc
    push Not at hc
    have hle : (3 : ℕ) ^ oddCount w ≤ 3 ^ 10 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 16 < 3 ^ 10 := lt_of_lt_of_le hexp hle
    norm_num at this
  have hA : (177147 : ℕ) ≤ 3 ^ oddCount w := by
    calc (177147 : ℕ) = 3 ^ 11 := by norm_num
      _ ≤ 3 ^ oddCount w := Nat.pow_le_pow_right (by norm_num) ho
  have hAR : (177147 : ℝ) ≤ (3 : ℝ) ^ oddCount w := by exact_mod_cast hA
  norm_num at hfin
  linarith

/-- Census extension: no cycle itinerary of length at most `10`.
Lengths `≤ 8` are the Lean census; `9` and `10` are the finance
inequality. -/
theorem no_cycle_itinerary_length_le_ten {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 10) : ¬CycleItinerary n w := by
  intro h
  rcases Nat.lt_or_ge w.length 9 with h9 | h9
  · exact no_cycle_itinerary_length_le_eight hn (by omega) h
  · rcases Nat.lt_or_ge w.length 10 with h10 | h10
    · exact no_cycle_itinerary_length_nine hn (by omega) h
    · exact no_cycle_itinerary_length_ten hn (by omega) h

/-- If a nontrivial cycle exists, its period is `11` or at least
`14`: lengths `≤ 10`, `12`, and `13` are impossible. -/
theorem cycle_itinerary_length_eleven_or_ge_fourteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 11 ∨ 14 ≤ w.length := by
  by_contra hc
  push Not at hc
  obtain ⟨h11, h14⟩ := hc
  have hsplit : w.length ≤ 10 ∨ w.length = 12 ∨ w.length = 13 := by omega
  rcases hsplit with hle | h12 | h13
  · exact no_cycle_itinerary_length_le_ten hn hle h
  · exact no_cycle_itinerary_length_twelve hn h12 h
  · exact no_cycle_itinerary_length_thirteen hn h13 h

/-- Residual class `{1,…,52}` is disjoint from a nontrivial cycle. -/
theorem cycleItinerary_iterate_not_lt_fifty_three {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    53 ≤ floorPower^[i] n := by
  by_contra h53
  have hmod : floorPower^[i] n = floorPower^[i % w.length] n :=
    cycle_iterate_mod h
  have hlenpos : 0 < w.length :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2
  have hlt : i % w.length < w.length := Nat.mod_lt i hlenpos
  have hge := cycleItinerary_iterate_ge_two hn h hlt
  have hpos : 1 ≤ floorPower^[i] n := by
    have : 2 ≤ floorPower^[i % w.length] n := hge
    exact le_trans (by decide : (1 : ℕ) ≤ 2) (by simpa [hmod] using this)
  have hy : floorPower^[i] n < 53 := Nat.lt_of_not_ge h53
  have hR : ReachesOne (floorPower^[i] n) :=
    reachesOne_of_lt_fifty_three hpos hy
  exact cycleItinerary_not_reachesOne hn h (reachesOne_of_iterate rfl hR)

/-- Numeric certificate `log 53 > 7/2`, via `e < 3` and `3^7 < 53^2`. -/
theorem log_fifty_three_gt : (7 / 2 : ℝ) < Real.log 53 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 53)]
  have hsq : Real.exp (7 / 2) ^ 2 = Real.exp 7 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hpow : Real.exp 1 ^ (7 : ℕ) = Real.exp 7 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hlt : Real.exp 1 ^ (7 : ℕ) < (3 : ℝ) ^ (7 : ℕ) := by
    gcongr
    exact Real.exp_one_lt_three
  have hnum : (3 : ℝ) ^ (7 : ℕ) < (53 : ℝ) ^ 2 := by norm_num
  have h2809 : Real.exp (7 / 2) ^ 2 < (53 : ℝ) ^ 2 := by
    rw [hsq, ← hpow]
    linarith
  nlinarith [Real.exp_pos (7 / 2 : ℝ), h2809,
    sq_nonneg (Real.exp (7 / 2) - 53)]

/-- Finance at the rotated odd minimum after the residual floor `53`:
`(371/2)(3^o - 2^L) ≤ L 3^o`, because the minimum is at least `53`
and `53 log 53 > 371/2`. -/
theorem cycle_finance_min_fifty_three {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (371 / 2 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w := by
  obtain ⟨k, hkL, hmin⟩ := exists_cycleMin hn h
  have hm53 : 53 ≤ floorPower^[k] n :=
    cycleItinerary_iterate_not_lt_fifty_three hn h
  have hm2 : 2 ≤ floorPower^[k] n := by omega
  have hfin := cycleMin_finance hm2 hmin
  rw [rotateItinerary_length, oddCount_rotateItinerary] at hfin
  have hexpand : (2 : ℝ) ^ w.length < (3 : ℝ) ^ oddCount w := by
    exact_mod_cast cycle_itinerary_formally_expanding hn h
  have hm53R : (53 : ℝ) ≤ (floorPower^[k] n : ℝ) := by exact_mod_cast hm53
  have hlog : (7 / 2 : ℝ) ≤ Real.log (floorPower^[k] n) := by
    have hmono : Real.log (53 : ℝ) ≤ Real.log (floorPower^[k] n) := by
      gcongr
    linarith [log_fifty_three_gt]
  have hmlog : (371 / 2 : ℝ) ≤
      (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) := by
    have h1 : (53 : ℝ) * (7 / 2) ≤
        (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) :=
      mul_le_mul hm53R hlog (by norm_num) (by linarith)
    linarith
  calc (371 / 2 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length)
      ≤ (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) *
          ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) :=
        mul_le_mul_of_nonneg_right hmlog (by linarith)
    _ ≤ (w.length : ℝ) * (3 : ℝ) ^ oddCount w := hfin

/-- Finance excludes length `11`: `o ≥ 7` forces
`(371/2)(3^o - 2048) > 11 · 3^o`. Not a leftover-itinerary census. -/
theorem finance_excludes_length_eleven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 11) : ¬CycleItinerary n w := by
  intro h
  have hfin := cycle_finance_min_fifty_three hn h
  have hexp := cycle_itinerary_formally_expanding hn h
  rw [hlen] at hfin hexp
  have ho : 7 ≤ oddCount w := by
    by_contra hc
    push Not at hc
    have hle : (3 : ℕ) ^ oddCount w ≤ 3 ^ 6 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 11 < 3 ^ 6 := lt_of_lt_of_le hexp hle
    norm_num at this
  have hA : (2187 : ℕ) ≤ 3 ^ oddCount w := by
    calc (2187 : ℕ) = 3 ^ 7 := by norm_num
      _ ≤ 3 ^ oddCount w := Nat.pow_le_pow_right (by norm_num) ho
  have hAR : (2187 : ℝ) ≤ (3 : ℝ) ^ oddCount w := by exact_mod_cast hA
  norm_num at hfin
  linarith

/-- Census extension: no cycle itinerary of length at most `11`.
Lengths `≤ 10` are the prior census; `11` is finance at the
residual floor `53`. -/
theorem no_cycle_itinerary_length_le_eleven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 11) : ¬CycleItinerary n w := by
  intro h
  rcases Nat.lt_or_ge w.length 11 with h11 | h11
  · exact no_cycle_itinerary_length_le_ten hn (by omega) h
  · exact finance_excludes_length_eleven hn (by omega) h

/-- If a nontrivial cycle exists, its period is at least `14`.
Corollary of the floor-`53` leftover; lengths `14`–`18` and
`20`–`29` are excluded separately. -/
theorem cycle_itinerary_length_ge_fourteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : 14 ≤ w.length := by
  rcases cycle_itinerary_length_eleven_or_ge_fourteen hn h with h11 | h14
  · exact absurd h (finance_excludes_length_eleven hn h11)
  · exact h14

/-- Formal expansion forces more odds than any `o0` with `3^{o0} ≤ 2^L`. -/
theorem cycle_oddCount_gt_of_three_pow_le {n : ℕ} {w : List Branch} {o0 : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w)
    (hle : 3 ^ o0 ≤ 2 ^ w.length) : o0 < oddCount w := by
  have hexp := cycle_itinerary_formally_expanding hn h
  have : 3 ^ o0 < 3 ^ oddCount w := lt_of_le_of_lt hle hexp
  exact (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 3)).mp this

/-- If the floor-`53` comparison already fails at the minimal
admissible `3^{o0}`, it fails for every larger odd count. Requires
`L < 371/2` so the comparison is increasing in `3^o`. -/
theorem finance_contradicts_min_fifty_three {n : ℕ} {w : List Branch}
    {L o0 : ℕ} (hn : 2 ≤ n) (h : CycleItinerary n w)
    (hlen : w.length = L) (hL : (L : ℝ) < 371 / 2)
    (ho : o0 ≤ oddCount w)
    (hnum : (371 / 2 : ℝ) * ((3 : ℝ) ^ o0 - (2 : ℝ) ^ L) >
      (L : ℝ) * (3 : ℝ) ^ o0) : False := by
  have hfin := cycle_finance_min_fifty_three hn h
  rw [hlen] at hfin
  have hA : (3 : ℝ) ^ o0 ≤ (3 : ℝ) ^ oddCount w := by
    have : (3 : ℕ) ^ o0 ≤ 3 ^ oddCount w :=
      Nat.pow_le_pow_right (by norm_num) ho
    exact_mod_cast this
  have hc : (0 : ℝ) < 371 / 2 - L := sub_pos.mpr hL
  have hnum' : (371 / 2 - (L : ℝ)) * (3 : ℝ) ^ o0 >
      (371 / 2) * (2 : ℝ) ^ L := by nlinarith
  have hfin' : (371 / 2 - (L : ℝ)) * (3 : ℝ) ^ oddCount w ≤
      (371 / 2) * (2 : ℝ) ^ L := by nlinarith
  have hleA : (3 : ℝ) ^ oddCount w ≤ (3 : ℝ) ^ o0 :=
    le_of_mul_le_mul_left (le_trans hfin' hnum'.le) hc
  have heq : (3 : ℝ) ^ oddCount w = (3 : ℝ) ^ o0 := le_antisymm hleA hA
  rw [heq] at hfin'
  exact not_le_of_gt hnum' hfin'

/-- Instantiate the floor-`53` comparison at a concrete length. -/
theorem finance_excludes_at {n : ℕ} {w : List Branch} {L oPred : ℕ}
    (hn : 2 ≤ n) (hlen : w.length = L)
    (hL : (L : ℝ) < 371 / 2)
    (hpred : 3 ^ oPred ≤ 2 ^ L)
    (hnum : (371 / 2 : ℝ) * ((3 : ℝ) ^ (oPred + 1) - (2 : ℝ) ^ L) >
      (L : ℝ) * (3 : ℝ) ^ (oPred + 1)) :
    ¬CycleItinerary n w := by
  intro h
  have hpred' : 3 ^ oPred ≤ 2 ^ w.length := by simpa [hlen] using hpred
  have ho : oPred + 1 ≤ oddCount w :=
    Nat.succ_le_of_lt (cycle_oddCount_gt_of_three_pow_le hn h hpred')
  exact finance_contradicts_min_fifty_three hn h hlen hL ho hnum

/-- Excluded lengths at the residual floor `53`: rows `(L, oPred)`
with `3^{oPred} ≤ 2^L` and the finance comparison at
`o = oPred + 1`. -/
def financeRows53 : List (ℕ × ℕ) :=
  [(14, 8), (15, 9), (17, 10), (18, 11), (20, 12), (21, 13), (22, 13),
   (23, 14), (24, 15), (25, 15), (26, 16), (27, 17), (28, 17), (29, 18)]

/-- Every row of the floor-`53` table is an excluded length. -/
theorem finance_excludes_rows53 :
    ∀ p ∈ financeRows53, ∀ {n : ℕ} {w : List Branch},
      2 ≤ n → w.length = p.1 → ¬CycleItinerary n w := by
  intro p hp n w hn hlen
  refine finance_excludes_at (oPred := p.2) hn hlen ?_ ?_ ?_ <;>
    fin_cases hp <;> norm_num

/-- Any length in the floor-`53` table is excluded. -/
theorem finance_excludes_mem53 {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hmem : w.length ∈ financeRows53.map Prod.fst) :
    ¬CycleItinerary n w := by
  obtain ⟨p, hp, hfst⟩ := List.mem_map.mp hmem
  exact finance_excludes_rows53 p hp hn hfst.symm

theorem finance_excludes_length_fourteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 14) : ¬CycleItinerary n w :=
  finance_excludes_mem53 hn (by rw [hlen]; decide)

/-- Census extension: no cycle itinerary of length at most `18`.
Length `11` is the near-convergent killed by the floor `53`;
`14`–`18` die by the same comparison. -/
theorem no_cycle_itinerary_length_le_eighteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 18) : ¬CycleItinerary n w := by
  intro h
  rcases Nat.lt_or_ge w.length 12 with h11 | h12
  · exact no_cycle_itinerary_length_le_eleven hn (Nat.lt_succ_iff.mp h11) h
  · have hsplit : w.length = 12 ∨ w.length = 13 ∨ w.length = 14 ∨
        w.length = 15 ∨ w.length = 16 ∨ w.length = 17 ∨ w.length = 18 := by
      omega
    rcases hsplit with hL | hL | hL | hL | hL | hL | hL
    · exact no_cycle_itinerary_length_twelve hn hL h
    · exact no_cycle_itinerary_length_thirteen hn hL h
    · exact finance_excludes_length_fourteen hn hL h
    · exact finance_excludes_mem53 hn (by rw [hL]; decide) h
    · exact no_cycle_itinerary_length_sixteen hn hL h
    · exact finance_excludes_mem53 hn (by rw [hL]; decide) h
    · exact finance_excludes_mem53 hn (by rw [hL]; decide) h

/-- No cycle itinerary of length below `30` except possibly `19`. -/
theorem no_cycle_itinerary_length_lt_thirty_ne_nineteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hLt : w.length < 30) (hne : w.length ≠ 19) :
    ¬CycleItinerary n w := by
  intro h
  rcases Nat.lt_or_ge w.length 19 with h18 | h19
  · exact no_cycle_itinerary_length_le_eighteen hn (Nat.le_of_lt_succ h18) h
  · have hge : 20 ≤ w.length :=
      Nat.succ_le_of_lt (lt_of_le_of_ne h19 hne.symm)
    have hcover : ∀ L < 30, 20 ≤ L →
        L ∈ financeRows53.map Prod.fst := by decide
    exact finance_excludes_mem53 hn (hcover w.length hLt hge) h

/-- If a nontrivial cycle exists, its period is `19` or at least `30`.
The gap `20..29` dies by finance at the residual floor `53`; `19` is
the next near-convergent (`2^19 < 3^12`). -/
theorem cycle_itinerary_length_nineteen_or_ge_thirty {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 19 ∨ 30 ≤ w.length := by
  by_contra hc
  push Not at hc
  obtain ⟨h19, h30⟩ := hc
  exact no_cycle_itinerary_length_lt_thirty_ne_nineteen hn (by omega) h19 h

/-- Weaker leftover: period is `19` or at least `20`. -/
theorem cycle_itinerary_length_nineteen_or_ge_twenty {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 19 ∨ 20 ≤ w.length := by
  rcases cycle_itinerary_length_nineteen_or_ge_thirty hn h with h19 | h30
  · exact Or.inl h19
  · exact Or.inr (le_trans (by decide : (20 : ℕ) ≤ 30) h30)

/-- Residual class `{1,…,256}` is disjoint from a nontrivial cycle. -/
theorem cycleItinerary_iterate_not_lt_two_hundred_fifty_seven
    {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    257 ≤ floorPower^[i] n := by
  by_contra h257
  have hmod : floorPower^[i] n = floorPower^[i % w.length] n :=
    cycle_iterate_mod h
  have hlenpos : 0 < w.length :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2
  have hlt : i % w.length < w.length := Nat.mod_lt i hlenpos
  have hge := cycleItinerary_iterate_ge_two hn h hlt
  have hpos : 1 ≤ floorPower^[i] n := by
    have : 2 ≤ floorPower^[i % w.length] n := hge
    exact le_trans (by decide : (1 : ℕ) ≤ 2) (by simpa [hmod] using this)
  have hy : floorPower^[i] n < 257 := Nat.lt_of_not_ge h257
  have hR : ReachesOne (floorPower^[i] n) :=
    reachesOne_of_lt_two_hundred_fifty_seven hpos hy
  exact cycleItinerary_not_reachesOne hn h (reachesOne_of_iterate rfl hR)

/-- Residual class `{1,…,260}` is disjoint from a nontrivial cycle. -/
theorem cycleItinerary_iterate_not_lt_two_hundred_sixty_one
    {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    261 ≤ floorPower^[i] n := by
  by_contra h261
  have hmod : floorPower^[i] n = floorPower^[i % w.length] n :=
    cycle_iterate_mod h
  have hlenpos : 0 < w.length :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2
  have hlt : i % w.length < w.length := Nat.mod_lt i hlenpos
  have hge := cycleItinerary_iterate_ge_two hn h hlt
  have hpos : 1 ≤ floorPower^[i] n := by
    have : 2 ≤ floorPower^[i % w.length] n := hge
    exact le_trans (by decide : (1 : ℕ) ≤ 2) (by simpa [hmod] using this)
  have hy : floorPower^[i] n < 261 := Nat.lt_of_not_ge h261
  have hR : ReachesOne (floorPower^[i] n) :=
    reachesOne_of_lt_two_hundred_sixty_one hpos hy
  exact cycleItinerary_not_reachesOne hn h (reachesOne_of_iterate rfl hR)

/-- Numeric certificate `log 257 > 61/11`, via `e < 2.7182818286`
and `e^61 < 257^11`. -/
theorem log_two_hundred_fifty_seven_gt : (61 / 11 : ℝ) < Real.log 257 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 257)]
  have hpow : Real.exp (61 / 11) ^ (11 : ℕ) = Real.exp 61 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he : Real.exp 1 ^ (61 : ℕ) = Real.exp 61 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hlt : Real.exp 1 ^ (61 : ℕ) < (2.7182818286 : ℝ) ^ (61 : ℕ) := by
    gcongr
    exact Real.exp_one_lt_d9
  have hnum : (2.7182818286 : ℝ) ^ (61 : ℕ) < (257 : ℝ) ^ (11 : ℕ) := by
    norm_num
  have h11 : Real.exp (61 / 11) ^ (11 : ℕ) < (257 : ℝ) ^ (11 : ℕ) := by
    rw [hpow, ← he]
    linarith
  refine (pow_lt_pow_iff_left₀ ?_ ?_ (by norm_num : (11 : ℕ) ≠ 0)).1 h11
  · exact (Real.exp_pos _).le
  · norm_num

/-- Finance at the rotated odd minimum after the residual floor `257`:
`(15677/11)(3^o - 2^L) ≤ L 3^o`, because the minimum is at least `257`
and `257 log 257 > 15677/11`. -/
theorem cycle_finance_min_two_hundred_fifty_seven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (15677 / 11 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w := by
  obtain ⟨k, hkL, hmin⟩ := exists_cycleMin hn h
  have hm257 : 257 ≤ floorPower^[k] n :=
    cycleItinerary_iterate_not_lt_two_hundred_fifty_seven hn h
  have hm2 : 2 ≤ floorPower^[k] n := by omega
  have hfin := cycleMin_finance hm2 hmin
  rw [rotateItinerary_length, oddCount_rotateItinerary] at hfin
  have hexpand : (2 : ℝ) ^ w.length < (3 : ℝ) ^ oddCount w := by
    exact_mod_cast cycle_itinerary_formally_expanding hn h
  have hm257R : (257 : ℝ) ≤ (floorPower^[k] n : ℝ) := by exact_mod_cast hm257
  have hlog : (61 / 11 : ℝ) ≤ Real.log (floorPower^[k] n) := by
    have hmono : Real.log (257 : ℝ) ≤ Real.log (floorPower^[k] n) := by
      gcongr
    linarith [log_two_hundred_fifty_seven_gt]
  have hmlog : (15677 / 11 : ℝ) ≤
      (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) := by
    have h1 : (257 : ℝ) * (61 / 11) ≤
        (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) :=
      mul_le_mul hm257R hlog (by norm_num) (by linarith)
    linarith
  calc (15677 / 11 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length)
      ≤ (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) *
          ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) :=
        mul_le_mul_of_nonneg_right hmlog (by linarith)
    _ ≤ (w.length : ℝ) * (3 : ℝ) ^ oddCount w := hfin

/-- If the floor-`257` comparison already fails at the minimal
admissible `3^{o0}`, it fails for every larger odd count. Requires
`L < 15677/11` so the comparison is increasing in `3^o`. -/
theorem finance_contradicts_min_two_hundred_fifty_seven
    {n : ℕ} {w : List Branch} {L o0 : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w)
    (hlen : w.length = L) (hL : (L : ℝ) < 15677 / 11)
    (ho : o0 ≤ oddCount w)
    (hnum : (15677 / 11 : ℝ) * ((3 : ℝ) ^ o0 - (2 : ℝ) ^ L) >
      (L : ℝ) * (3 : ℝ) ^ o0) : False := by
  have hfin := cycle_finance_min_two_hundred_fifty_seven hn h
  rw [hlen] at hfin
  have hA : (3 : ℝ) ^ o0 ≤ (3 : ℝ) ^ oddCount w := by
    have : (3 : ℕ) ^ o0 ≤ 3 ^ oddCount w :=
      Nat.pow_le_pow_right (by norm_num) ho
    exact_mod_cast this
  have hc : (0 : ℝ) < 15677 / 11 - L := sub_pos.mpr hL
  have hnum' : (15677 / 11 - (L : ℝ)) * (3 : ℝ) ^ o0 >
      (15677 / 11) * (2 : ℝ) ^ L := by nlinarith
  have hfin' : (15677 / 11 - (L : ℝ)) * (3 : ℝ) ^ oddCount w ≤
      (15677 / 11) * (2 : ℝ) ^ L := by nlinarith
  have hleA : (3 : ℝ) ^ oddCount w ≤ (3 : ℝ) ^ o0 :=
    le_of_mul_le_mul_left (le_trans hfin' hnum'.le) hc
  have heq : (3 : ℝ) ^ oddCount w = (3 : ℝ) ^ o0 := le_antisymm hleA hA
  rw [heq] at hfin'
  exact not_le_of_gt hnum' hfin'

/-- Instantiate the floor-`257` comparison at a concrete length. -/
theorem finance_excludes_at_two_hundred_fifty_seven
    {n : ℕ} {w : List Branch} {L oPred : ℕ}
    (hn : 2 ≤ n) (hlen : w.length = L)
    (hL : (L : ℝ) < 15677 / 11)
    (hpred : 3 ^ oPred ≤ 2 ^ L)
    (hnum : (15677 / 11 : ℝ) * ((3 : ℝ) ^ (oPred + 1) - (2 : ℝ) ^ L) >
      (L : ℝ) * (3 : ℝ) ^ (oPred + 1)) :
    ¬CycleItinerary n w := by
  intro h
  have hpred' : 3 ^ oPred ≤ 2 ^ w.length := by simpa [hlen] using hpred
  have ho : oPred + 1 ≤ oddCount w :=
    Nat.succ_le_of_lt (cycle_oddCount_gt_of_three_pow_le hn h hpred')
  exact finance_contradicts_min_two_hundred_fifty_seven hn h hlen hL ho hnum

/-- Finance excludes length `19`: `2^19 < 3^12` and
`(15677/11)(3^{12} - 2^{19}) > 19 · 3^{12}`. -/
theorem finance_excludes_length_nineteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 19) : ¬CycleItinerary n w :=
  finance_excludes_at_two_hundred_fifty_seven hn hlen (by norm_num)
    (by norm_num : (3 : ℕ) ^ 11 ≤ 2 ^ 19) (by norm_num)

/-- Census extension: no cycle itinerary of length at most `19`. -/
theorem no_cycle_itinerary_length_le_nineteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 19) : ¬CycleItinerary n w := by
  intro h
  rcases Nat.lt_or_ge w.length 19 with h19 | h19
  · exact no_cycle_itinerary_length_le_eighteen hn (by omega) h
  · exact finance_excludes_length_nineteen hn (by omega) h

/-- Excluded lengths at the residual floor `257`: rows `(L, oPred)`
with `3^{oPred} ≤ 2^L` and the finance comparison at
`o = oPred + 1`. -/
def financeRows257 : List (ℕ × ℕ) :=
  [(30, 18), (31, 19), (32, 20), (33, 20), (34, 21), (35, 22), (36, 22),
   (37, 23), (38, 23), (39, 24), (40, 25), (41, 25), (42, 26), (43, 27),
   (44, 27), (45, 28), (46, 29), (47, 29), (48, 30), (49, 30), (50, 31),
   (51, 32), (52, 32), (53, 33), (54, 34), (55, 34), (56, 35)]

/-- Every row of the floor-`257` table is an excluded length. -/
theorem finance_excludes_rows257 :
    ∀ p ∈ financeRows257, ∀ {n : ℕ} {w : List Branch},
      2 ≤ n → w.length = p.1 → ¬CycleItinerary n w := by
  intro p hp n w hn hlen
  refine finance_excludes_at_two_hundred_fifty_seven (oPred := p.2)
      hn hlen ?_ ?_ ?_ <;>
    fin_cases hp <;> norm_num

/-- Any length in the floor-`257` table is excluded. -/
theorem finance_excludes_mem257 {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hmem : w.length ∈ financeRows257.map Prod.fst) :
    ¬CycleItinerary n w := by
  obtain ⟨p, hp, hfst⟩ := List.mem_map.mp hmem
  exact finance_excludes_rows257 p hp hn hfst.symm

/-- No cycle itinerary of length below `38` except possibly `38`. -/
theorem no_cycle_itinerary_length_lt_thirty_eight {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hLt : w.length < 38) : ¬CycleItinerary n w := by
  intro h
  rcases Nat.lt_or_ge w.length 19 with h18 | h19
  · exact no_cycle_itinerary_length_le_eighteen hn (Nat.le_of_lt_succ h18) h
  · rcases Nat.eq_or_lt_of_le h19 with _ | hlt19
    · exact finance_excludes_length_nineteen hn (by omega) h
    · have hge : 20 ≤ w.length := Nat.succ_le_of_lt hlt19
      rcases Nat.lt_or_ge w.length 30 with h29 | h30
      · exact no_cycle_itinerary_length_lt_thirty_ne_nineteen hn h29
          (ne_of_gt (lt_of_lt_of_le (by decide : (19 : ℕ) < 20) hge)) h
      · have hcover : ∀ L < 38, 30 ≤ L →
            L ∈ financeRows257.map Prod.fst := by decide
        exact finance_excludes_mem257 hn (hcover w.length hLt h30) h

/-- If a nontrivial cycle exists, its period is at least `30`. -/
theorem cycle_itinerary_length_ge_thirty {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : 30 ≤ w.length := by
  rcases cycle_itinerary_length_nineteen_or_ge_thirty hn h with h19 | h30
  · exact absurd h (finance_excludes_length_nineteen hn h19)
  · exact h30

/-- If a nontrivial cycle exists, its period is `38` or at least `39`.
Weaker leftover: `log 257 > 61/11` also kills `38`. -/
theorem cycle_itinerary_length_thirty_eight_or_ge_thirty_nine
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 38 ∨ 39 ≤ w.length := by
  by_contra hc
  push Not at hc
  obtain ⟨h38, h39⟩ := hc
  exact no_cycle_itinerary_length_lt_thirty_eight hn (by omega) h

/-- Finance excludes length `38`: `2^38 < 3^24` and
`(15677/11)(3^{24} - 2^{38}) > 38 · 3^{24}`. -/
theorem finance_excludes_length_thirtyeight {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 38) : ¬CycleItinerary n w :=
  finance_excludes_mem257 hn (by rw [hlen]; decide)

/-- No cycle itinerary of length below `57`. -/
theorem no_cycle_itinerary_length_lt_fifty_seven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hLt : w.length < 57) : ¬CycleItinerary n w := by
  intro h
  rcases Nat.lt_or_ge w.length 38 with h37 | h38
  · exact no_cycle_itinerary_length_lt_thirty_eight hn h37 h
  · have hcover : ∀ L < 57, 38 ≤ L →
        L ∈ financeRows257.map Prod.fst := by decide
    exact finance_excludes_mem257 hn (hcover w.length hLt h38) h

/-- If a nontrivial cycle exists, its period is `57` or at least `58`.
Weaker leftover: the floor `261` also kills `57` and `76`. -/
theorem cycle_itinerary_length_fifty_seven_or_ge_fifty_eight
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 57 ∨ 58 ≤ w.length := by
  by_contra hc
  push Not at hc
  obtain ⟨h57, h58⟩ := hc
  exact no_cycle_itinerary_length_lt_fifty_seven hn (by omega) h

/-- Finance at the rotated odd minimum after the residual floor `261`:
`(15921/11)(3^o - 2^L) ≤ L 3^o`, because the minimum is at least `261`
and `261 log 257 > 15921/11`. -/
theorem cycle_finance_min_two_hundred_sixty_one {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (15921 / 11 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w := by
  obtain ⟨k, hkL, hmin⟩ := exists_cycleMin hn h
  have hm261 : 261 ≤ floorPower^[k] n :=
    cycleItinerary_iterate_not_lt_two_hundred_sixty_one hn h
  have hm2 : 2 ≤ floorPower^[k] n := by omega
  have hfin := cycleMin_finance hm2 hmin
  rw [rotateItinerary_length, oddCount_rotateItinerary] at hfin
  have hexpand : (2 : ℝ) ^ w.length < (3 : ℝ) ^ oddCount w := by
    exact_mod_cast cycle_itinerary_formally_expanding hn h
  have hm261R : (261 : ℝ) ≤ (floorPower^[k] n : ℝ) := by exact_mod_cast hm261
  have hlog : (61 / 11 : ℝ) ≤ Real.log (floorPower^[k] n) := by
    have hmono : Real.log (257 : ℝ) ≤ Real.log (floorPower^[k] n) := by
      have : (257 : ℝ) ≤ (floorPower^[k] n : ℝ) := by
        exact_mod_cast (le_trans (by decide : (257 : ℕ) ≤ 261) hm261)
      gcongr
    linarith [log_two_hundred_fifty_seven_gt]
  have hmlog : (15921 / 11 : ℝ) ≤
      (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) := by
    have h1 : (261 : ℝ) * (61 / 11) ≤
        (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) :=
      mul_le_mul hm261R hlog (by norm_num) (by linarith)
    linarith
  calc (15921 / 11 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length)
      ≤ (floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n) *
          ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) :=
        mul_le_mul_of_nonneg_right hmlog (by linarith)
    _ ≤ (w.length : ℝ) * (3 : ℝ) ^ oddCount w := hfin

theorem finance_contradicts_min_two_hundred_sixty_one
    {n : ℕ} {w : List Branch} {L o0 : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w)
    (hlen : w.length = L) (hL : (L : ℝ) < 15921 / 11)
    (ho : o0 ≤ oddCount w)
    (hnum : (15921 / 11 : ℝ) * ((3 : ℝ) ^ o0 - (2 : ℝ) ^ L) >
      (L : ℝ) * (3 : ℝ) ^ o0) : False := by
  have hfin := cycle_finance_min_two_hundred_sixty_one hn h
  rw [hlen] at hfin
  have hA : (3 : ℝ) ^ o0 ≤ (3 : ℝ) ^ oddCount w := by
    have : (3 : ℕ) ^ o0 ≤ 3 ^ oddCount w :=
      Nat.pow_le_pow_right (by norm_num) ho
    exact_mod_cast this
  have hc : (0 : ℝ) < 15921 / 11 - L := sub_pos.mpr hL
  have hnum' : (15921 / 11 - (L : ℝ)) * (3 : ℝ) ^ o0 >
      (15921 / 11) * (2 : ℝ) ^ L := by nlinarith
  have hfin' : (15921 / 11 - (L : ℝ)) * (3 : ℝ) ^ oddCount w ≤
      (15921 / 11) * (2 : ℝ) ^ L := by nlinarith
  have hleA : (3 : ℝ) ^ oddCount w ≤ (3 : ℝ) ^ o0 :=
    le_of_mul_le_mul_left (le_trans hfin' hnum'.le) hc
  have heq : (3 : ℝ) ^ oddCount w = (3 : ℝ) ^ o0 := le_antisymm hleA hA
  rw [heq] at hfin'
  exact not_le_of_gt hnum' hfin'

theorem finance_excludes_at_two_hundred_sixty_one
    {n : ℕ} {w : List Branch} {L oPred : ℕ}
    (hn : 2 ≤ n) (hlen : w.length = L)
    (hL : (L : ℝ) < 15921 / 11)
    (hpred : 3 ^ oPred ≤ 2 ^ L)
    (hnum : (15921 / 11 : ℝ) * ((3 : ℝ) ^ (oPred + 1) - (2 : ℝ) ^ L) >
      (L : ℝ) * (3 : ℝ) ^ (oPred + 1)) :
    ¬CycleItinerary n w := by
  intro h
  have hpred' : 3 ^ oPred ≤ 2 ^ w.length := by simpa [hlen] using hpred
  have ho : oPred + 1 ≤ oddCount w :=
    Nat.succ_le_of_lt (cycle_oddCount_gt_of_three_pow_le hn h hpred')
  exact finance_contradicts_min_two_hundred_sixty_one hn h hlen hL ho hnum

/-- Excluded lengths at the residual floor `261`: rows `(L, oPred)`
with `3^{oPred} ≤ 2^L` and the finance comparison at
`o = oPred + 1`. -/
def financeRows261 : List (ℕ × ℕ) :=
  [(57, 35), (58, 36), (59, 37), (60, 37), (61, 38), (62, 39), (63, 39),
   (64, 40), (65, 41), (66, 41), (67, 42), (68, 42), (69, 43), (70, 44),
   (71, 44), (72, 45), (73, 46), (74, 46), (75, 47), (76, 47), (77, 48),
   (78, 49), (79, 49), (80, 50), (81, 51), (82, 51), (83, 52)]

/-- Every row of the floor-`261` table is an excluded length. -/
theorem finance_excludes_rows261 :
    ∀ p ∈ financeRows261, ∀ {n : ℕ} {w : List Branch},
      2 ≤ n → w.length = p.1 → ¬CycleItinerary n w := by
  intro p hp n w hn hlen
  refine finance_excludes_at_two_hundred_sixty_one (oPred := p.2)
      hn hlen ?_ ?_ ?_ <;>
    fin_cases hp <;> norm_num

/-- Any length in the floor-`261` table is excluded. -/
theorem finance_excludes_mem261 {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hmem : w.length ∈ financeRows261.map Prod.fst) :
    ¬CycleItinerary n w := by
  obtain ⟨p, hp, hfst⟩ := List.mem_map.mp hmem
  exact finance_excludes_rows261 p hp hn hfst.symm

/-- Finance excludes length `57` (also killed by the floor `261`
residual). Named leftover milestone. -/
theorem finance_excludes_length_fiftyseven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 57) : ¬CycleItinerary n w :=
  finance_excludes_mem261 hn (by rw [hlen]; decide)

/-- Finance excludes length `76` (also killed by the floor `261`
residual). Named leftover milestone. -/
theorem finance_excludes_length_seventysix {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 76) : ¬CycleItinerary n w :=
  finance_excludes_mem261 hn (by rw [hlen]; decide)

/-- No cycle itinerary of length below `84`. -/
theorem no_cycle_itinerary_length_lt_eighty_four {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hLt : w.length < 84) : ¬CycleItinerary n w := by
  intro h
  rcases Nat.lt_or_ge w.length 57 with h56 | h57
  · exact no_cycle_itinerary_length_lt_fifty_seven hn h56 h
  · have hcover : ∀ L < 84, 57 ≤ L →
        L ∈ financeRows261.map Prod.fst := by decide
    exact finance_excludes_mem261 hn (hcover w.length hLt h57) h

/-- If a nontrivial cycle exists, its period is `84` or at least `85`.
The cheap leftovers `57` and `76` die at the residual floor `261`;
`58`–`75` and `77`–`83` die by the same comparison. `L=84` is the
next record near-convergent. -/
theorem cycle_itinerary_length_eighty_four_or_ge_eighty_five
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 84 ∨ 85 ≤ w.length := by
  by_contra hc
  push Not at hc
  obtain ⟨h84, h85⟩ := hc
  exact no_cycle_itinerary_length_lt_eighty_four hn (by omega) h

/-- Finance table cutoff used by the Eliahou leftover. -/
def eliahouTableCutoff : ℕ := 10 ^ 5

/-- Eliahou leftover: period `84`, a listed near-convergent, or at
least the finance table cutoff. -/
def EliahouLeftover (L : ℕ) (exceptions : List ℕ) : Prop :=
  L = 84 ∨ L ∈ exceptions ∨ eliahouTableCutoff ≤ L

/-- Every length in `[30, cutoff)` outside the named family is
already excluded. Instantiated by the computational gap table. -/
def EliahouTable (exceptions : List ℕ) : Prop :=
  ∀ (n : ℕ) (w : List Branch),
    2 ≤ n → 30 ≤ w.length → w.length < eliahouTableCutoff →
      w.length ∉ exceptions → ¬CycleItinerary n w

/-- Bookkeeping: the Lean leftover `84` or `≥ 85`, plus the finance
table, is the Eliahou leftover. Not a new inequality. -/
theorem cycle_itinerary_eliahou_leftover {n : ℕ} {w : List Branch}
    {exceptions : List ℕ} (hn : 2 ≤ n) (h : CycleItinerary n w)
    (hTable : EliahouTable exceptions) :
    EliahouLeftover w.length exceptions := by
  rcases cycle_itinerary_length_eighty_four_or_ge_eighty_five hn h with h84 | h85
  · exact Or.inl h84
  · rcases Nat.lt_or_ge w.length eliahouTableCutoff with hlt | hge
    · have hmem : w.length ∈ exceptions := by
        by_contra hne
        have h30 : 30 ≤ w.length :=
          le_trans (by decide : (30 : ℕ) ≤ 85) h85
        exact hTable n w hn h30 hlt hne h
      exact Or.inr (Or.inl hmem)
    · exact Or.inr (Or.inr hge)

end Problems.Juggler

