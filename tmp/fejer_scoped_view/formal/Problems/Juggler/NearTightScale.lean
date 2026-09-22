import Problems.Juggler.ExpansionSlack

namespace Problems.Juggler

/-!
# Scale-induced near-tightness

The local remainder window `0 ≤ ρ < 2T+1` makes the relative
remainder `η = ρ / T^2` decay as `T` grows. For a fixed finite
itinerary the relative slack `1+q` is a weighted product of local
`1+η` factors, so `q` becomes small at large scale. A large-`λ`
predecessor only enters by making the next start enormous.

This file does not claim that every start reaches `1`, and it
does not claim that scale-induced near-tightness is an obstruction.
-/

theorem even_remainder_bound {x : ℕ} (heven : x % 2 = 0) :
    localDefectEven x < 2 * floorPower x + 1 :=
  localDefectEven_lt_succ heven

theorem odd_remainder_bound {x : ℕ} (hodd : x % 2 = 1) :
    localDefectOdd x < 2 * floorPower x + 1 :=
  localDefectOdd_lt_succ hodd

theorem even_remainder_le_two {x : ℕ} (heven : x % 2 = 0) :
    localDefectEven x ≤ 2 * floorPower x :=
  Nat.lt_succ_iff.mp (even_remainder_bound heven)

theorem odd_remainder_le_two {x : ℕ} (hodd : x % 2 = 1) :
    localDefectOdd x ≤ 2 * floorPower x :=
  Nat.lt_succ_iff.mp (odd_remainder_bound hodd)

/-- `η ≤ 2 / T` as a `ℕ` comparison: `ρ T ≤ 2 T^2`. -/
theorem even_eta_le_two_over_T {x : ℕ} (heven : x % 2 = 0) :
    localDefectEven x * floorPower x ≤ 2 * floorPower x ^ 2 := by
  have hle := even_remainder_le_two heven
  have :
      localDefectEven x * floorPower x ≤
        2 * floorPower x * floorPower x :=
    Nat.mul_le_mul_right (floorPower x) hle
  simpa [pow_two, mul_assoc] using this

theorem odd_eta_le_two_over_T {x : ℕ} (hodd : x % 2 = 1) :
    localDefectOdd x * floorPower x ≤ 2 * floorPower x ^ 2 := by
  have hle := odd_remainder_le_two hodd
  have :
      localDefectOdd x * floorPower x ≤
        2 * floorPower x * floorPower x :=
    Nat.mul_le_mul_right (floorPower x) hle
  simpa [pow_two, mul_assoc] using this

/-- `η < 2/T + 1/T^2` as `ρ T^2` versus `(2T+1) T^2`, i.e. `ρ < 2T+1`. -/
theorem normalized_remainder_upper {x : ℕ} {b : Branch}
    (h : follows x [b]) :
    branchDefect b x < 2 * floorPower x + 1 :=
  branchDefect_lt h

/-- `1+η < ((T+1)/T)^2`. -/
theorem one_plus_eta_lt_succ_sq {x : ℕ} {b : Branch}
    (h : follows x [b]) :
    x ^ branchExp b < (floorPower x + 1) ^ 2 := by
  have hadd := branchDefect_add h
  have hρ := branchDefect_lt h
  have hsq : (floorPower x + 1) ^ 2 =
      floorPower x ^ 2 + 2 * floorPower x + 1 := by ring
  rw [hadd, hsq]
  exact Nat.add_lt_add_left hρ _

theorem local_eta_scale {x : ℕ} {b : Branch} (h : follows x [b])
    (hT : 0 < floorPower x) :
    x ^ branchExp b * floorPower x ^ 2 <
      (floorPower x + 1) ^ 2 * floorPower x ^ 2 :=
  Nat.mul_lt_mul_of_pos_right (one_plus_eta_lt_succ_sq h) (Nat.pow_pos hT)

theorem slackNum_ooe (n : ℕ) : slackNum n ooeWord = n ^ 9 := by
  simp [slackNum, ooeWord, oddCount]

theorem slackDen_ooe (n : ℕ) :
    slackDen n ooeWord = image n ooeWord ^ 8 := by
  simp [slackDen, ooeWord]

theorem image_ooe (n : ℕ) :
    image n ooeWord = floorPower (floorPower (floorPower n)) := by
  simp [ooeWord, image]

/-- Exact `OOE` product: `1+q = (1+η0)^3 (1+η1)^2 (1+η2)^4`. -/
theorem ooe_eta_product (n : ℕ) :
    slackNum n ooeWord *
        (floorPower n ^ 2) ^ 3 *
        (floorPower (floorPower n) ^ 2) ^ 2 *
        (floorPower (floorPower (floorPower n)) ^ 2) ^ 4 =
      (n ^ 3) ^ 3 *
        (floorPower n ^ 3) ^ 2 *
        floorPower (floorPower n) ^ 4 *
        slackDen n ooeWord := by
  simp [slackNum_ooe, slackDen_ooe, image_ooe]
  ring

theorem follows_ooe_parities {n : ℕ} (hw : follows n ooeWord) :
    n % 2 = 1 ∧
      floorPower n % 2 = 1 ∧
        floorPower (floorPower n) % 2 = 0 := by
  have h : follows n [.odd, .odd, .even] := by simpa [ooeWord] using hw
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem follows_ooe_start {n : ℕ} (hw : follows n ooeWord) : 1 ≤ n := by
  have hn : n % 2 = 1 := (follows_ooe_parities hw).1
  omega

/-- Upper bound `1+q_OOE < ((T0+1)/T0)^6 ((T1+1)/T1)^4 ((T2+1)/T2)^8`. -/
theorem ooe_one_plus_slack_lt_succ_ratio {n : ℕ}
    (hw : follows n ooeWord) :
    slackNum n ooeWord *
        floorPower n ^ 6 *
        floorPower (floorPower n) ^ 4 *
        floorPower (floorPower (floorPower n)) ^ 8 <
      slackDen n ooeWord *
        (floorPower n + 1) ^ 6 *
        (floorPower (floorPower n) + 1) ^ 4 *
        (floorPower (floorPower (floorPower n)) + 1) ^ 8 := by
  have ⟨h0, h1, h2⟩ := follows_ooe_parities hw
  have hn : 1 ≤ n := follows_ooe_start hw
  have ht0 : 1 ≤ floorPower n := floorPower_pos hn
  have ht1 : 1 ≤ floorPower (floorPower n) := floorPower_pos ht0
  have ht2 : 1 ≤ floorPower (floorPower (floorPower n)) := floorPower_pos ht1
  have hf0 : follows n [Branch.odd] := ⟨h0, trivial⟩
  have hf1 : follows (floorPower n) [Branch.odd] := ⟨h1, trivial⟩
  have hf2 : follows (floorPower (floorPower n)) [Branch.even] :=
    ⟨h2, trivial⟩
  have ha : n ^ 3 < (floorPower n + 1) ^ 2 := by
    simpa [branchExp] using one_plus_eta_lt_succ_sq hf0
  have hb : floorPower n ^ 3 < (floorPower (floorPower n) + 1) ^ 2 := by
    simpa [branchExp] using one_plus_eta_lt_succ_sq hf1
  have hc :
      floorPower (floorPower n) <
        (floorPower (floorPower (floorPower n)) + 1) ^ 2 := by
    simpa [branchExp, pow_one] using one_plus_eta_lt_succ_sq hf2
  have hA : n ^ 9 < (floorPower n + 1) ^ 6 := by
    have : (n ^ 3) ^ 3 < ((floorPower n + 1) ^ 2) ^ 3 :=
      Nat.pow_lt_pow_left ha (by decide)
    simpa [← Nat.pow_mul] using this
  have hB : floorPower n ^ 6 < (floorPower (floorPower n) + 1) ^ 4 := by
    have : (floorPower n ^ 3) ^ 2 <
        ((floorPower (floorPower n) + 1) ^ 2) ^ 2 :=
      Nat.pow_lt_pow_left hb (by decide)
    simpa [← Nat.pow_mul] using this
  have hC :
      floorPower (floorPower n) ^ 4 <
        (floorPower (floorPower (floorPower n)) + 1) ^ 8 := by
    have : (floorPower (floorPower n)) ^ 4 <
        ((floorPower (floorPower (floorPower n)) + 1) ^ 2) ^ 4 :=
      Nat.pow_lt_pow_left hc (by decide)
    simpa [← Nat.pow_mul] using this
  have hpos0 : 0 < floorPower n ^ 6 :=
    Nat.pow_pos (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) ht0)
  have hpos1 : 0 < floorPower (floorPower n) ^ 4 :=
    Nat.pow_pos (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) ht1)
  have hpos2 : 0 < floorPower (floorPower (floorPower n)) ^ 8 :=
    Nat.pow_pos (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) ht2)
  have hposA : 0 < (floorPower n + 1) ^ 6 :=
    Nat.pow_pos (Nat.succ_pos _)
  have hposB : 0 < (floorPower (floorPower n) + 1) ^ 4 :=
    Nat.pow_pos (Nat.succ_pos _)
  have hAB : n ^ 9 * floorPower n ^ 6 <
      (floorPower n + 1) ^ 6 * (floorPower (floorPower n) + 1) ^ 4 := by
    have hL : n ^ 9 * floorPower n ^ 6 <
        (floorPower n + 1) ^ 6 * floorPower n ^ 6 :=
      Nat.mul_lt_mul_of_pos_right hA hpos0
    have hR : (floorPower n + 1) ^ 6 * floorPower n ^ 6 <
        (floorPower n + 1) ^ 6 * (floorPower (floorPower n) + 1) ^ 4 :=
      Nat.mul_lt_mul_of_pos_left hB hposA
    exact lt_trans hL hR
  have hABC : n ^ 9 * floorPower n ^ 6 * floorPower (floorPower n) ^ 4 <
      (floorPower n + 1) ^ 6 * (floorPower (floorPower n) + 1) ^ 4 *
        (floorPower (floorPower (floorPower n)) + 1) ^ 8 := by
    have hL :
        n ^ 9 * floorPower n ^ 6 * floorPower (floorPower n) ^ 4 <
          (floorPower n + 1) ^ 6 * (floorPower (floorPower n) + 1) ^ 4 *
            floorPower (floorPower n) ^ 4 :=
      Nat.mul_lt_mul_of_pos_right hAB hpos1
    have hR :
        (floorPower n + 1) ^ 6 * (floorPower (floorPower n) + 1) ^ 4 *
            floorPower (floorPower n) ^ 4 <
          (floorPower n + 1) ^ 6 * (floorPower (floorPower n) + 1) ^ 4 *
            (floorPower (floorPower (floorPower n)) + 1) ^ 8 :=
      Nat.mul_lt_mul_of_pos_left hC (Nat.mul_pos hposA hposB)
    exact lt_trans hL hR
  have hmul :
      n ^ 9 * floorPower n ^ 6 * floorPower (floorPower n) ^ 4 *
          floorPower (floorPower (floorPower n)) ^ 8 <
        (floorPower n + 1) ^ 6 * (floorPower (floorPower n) + 1) ^ 4 *
          (floorPower (floorPower (floorPower n)) + 1) ^ 8 *
          floorPower (floorPower (floorPower n)) ^ 8 :=
    Nat.mul_lt_mul_of_pos_right hABC hpos2
  simpa [slackNum_ooe, slackDen_ooe, image_ooe, mul_comm, mul_left_comm,
    mul_assoc] using hmul

/-- The `OOE` successor bound depends only on the itinerary of `y`.
A large-`λ` predecessor enters only by making `y` large. -/
theorem large_lambda_successor_q_bound {y : ℕ}
    (hw : follows y ooeWord) :
    slackNum y ooeWord *
        floorPower y ^ 6 *
        floorPower (floorPower y) ^ 4 *
        floorPower (floorPower (floorPower y)) ^ 8 <
      slackDen y ooeWord *
        (floorPower y + 1) ^ 6 *
        (floorPower (floorPower y) + 1) ^ 4 *
        (floorPower (floorPower (floorPower y)) + 1) ^ 8 :=
  ooe_one_plus_slack_lt_succ_ratio hw

/-- Image form of `T_w(n)^{2^{|w|}} (1+q) = n^{3^{#O}}`. -/
theorem block_growth_from_q {n : ℕ} {w : List Branch} (hw : follows n w) :
    slackNum n w = slackDen n w + globalDefect n w :=
  slack_identity hw

end Problems.Juggler
