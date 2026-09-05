import Problems.Juggler.NormalizedDefect

set_option maxRecDepth 4000000

namespace Problems.Juggler

/-!
# Weighted slack budget

The relative slack `1+q` already multiplies under concatenation.
The objects below are the log-free `ℕ` form of the affine rewrite

```
log T_w(n) = λ(w) log n - c_w(n)
```

with `λ = 3^{#O} / 2^{|w|}` and `c = log(1+q) / 2^{|w|}`.
They are a change of coordinates, not a new obstruction, and they
do not claim that every start reaches `1`.
-/

/-- Formal block multiplier `λ = 3^{#O} / 2^{|w|}` as the pair
`(A, B) = (3^{#O(w)}, 2^{|w|})`. -/
def blockMultiplier (w : List Branch) : ℕ × ℕ :=
  (3 ^ oddCount w, 2 ^ w.length)

/-- Formal expansion margin `μ = λ - 1` as the pair `(A - B, B)`.
The first component is `0` in `ℕ` when the itinerary is not expanding. -/
def expansionMargin (w : List Branch) : ℕ × ℕ :=
  ((blockMultiplier w).1 - (blockMultiplier w).2, (blockMultiplier w).2)

/-- Log-free pair for `ℓ = log(1+q)`. Same pair as `onePlusSlack`. -/
def blockLogSlack (n : ℕ) (w : List Branch) : ℕ × ℕ :=
  onePlusSlack n w

/-- Log-free pair for the slack tax `c = ℓ / B`. Same pair as
`onePlusSlack`; the weight `B` is `(blockMultiplier w).2`. -/
def blockSlackTax (n : ℕ) (w : List Branch) : ℕ × ℕ :=
  onePlusSlack n w

/-- Concatenated `1+q`. In logs this is the weighted slack `C`. -/
def weightedSlack (n : ℕ) (w : List Branch) : ℕ × ℕ :=
  onePlusSlack n w

/-- Concatenated `1+q`. In logs this is the normalized budget
`B = C / Λ`. -/
def normalizedSlackBudget (n : ℕ) (w : List Branch) : ℕ × ℕ :=
  onePlusSlack n w

theorem slackNum_blockMultiplier (n : ℕ) (w : List Branch) :
    slackNum n w = n ^ (blockMultiplier w).1 :=
  rfl

theorem slackDen_blockMultiplier (n : ℕ) (w : List Branch) :
    slackDen n w = image n w ^ (blockMultiplier w).2 :=
  rfl

/-- Multiplier product `Λ_{uv} = Λ_u Λ_v`. -/
theorem blockMultiplier_mul (u v : List Branch) :
    (blockMultiplier (u ++ v)).1 =
      (blockMultiplier u).1 * (blockMultiplier v).1 ∧
    (blockMultiplier (u ++ v)).2 =
      (blockMultiplier u).2 * (blockMultiplier v).2 := by
  constructor
  · simp [blockMultiplier, oddCount_append, pow_add]
  · simp [blockMultiplier, List.length_append, pow_add]

theorem blockMultiplier_oddEvenBlock (a b : ℕ) :
    blockMultiplier (oddEvenBlock a b) = (3 ^ a, 2 ^ (a + b)) := by
  simp [blockMultiplier, oddCount_oddEvenBlock, length_oddEvenBlock]

theorem expansionMargin_pos_iff (w : List Branch) :
    0 < (expansionMargin w).1 ↔ exponentExpanding w := by
  simp [expansionMargin, blockMultiplier, exponentExpanding]

/-- Exact power identity `n^A = T^B + Δ`. This is `slack_identity`
in multiplier coordinates. -/
theorem block_power_identity {n : ℕ} {w : List Branch} (hw : follows n w) :
    n ^ (blockMultiplier w).1 =
      image n w ^ (blockMultiplier w).2 + globalDefect n w := by
  simpa [blockMultiplier, slackNum, slackDen] using slack_identity hw

/-- Log-free form of `log T = λ log n - c`. -/
theorem block_log_growth {n : ℕ} {w : List Branch} (hw : follows n w) :
    slackNum n w = slackDen n w + globalDefect n w :=
  slack_identity hw

/-- Exact concatenation law in multiplier coordinates.
This is the Nat form of `ℓ_{uv} = A_v ℓ_u + B_u ℓ_v` and of
`C_{uv} = λ_v C_u + C_v`. -/
theorem weighted_slack_concat (n : ℕ) (u v : List Branch) :
    slackNum n (u ++ v) *
        slackDen n u ^ (blockMultiplier v).1 *
        slackDen (image n u) v ^ (blockMultiplier u).2 =
      slackNum n u ^ (blockMultiplier v).1 *
        slackNum (image n u) v ^ (blockMultiplier u).2 *
        slackDen n (u ++ v) := by
  simpa [blockMultiplier] using onePlusSlack_concat n u v

/-- Two-block form of the weighted cocycle. Same identity. -/
theorem weighted_slack_cocycle (n : ℕ) (u v : List Branch) :
    slackNum n (u ++ v) *
        slackDen n u ^ (blockMultiplier v).1 *
        slackDen (image n u) v ^ (blockMultiplier u).2 =
      slackNum n u ^ (blockMultiplier v).1 *
        slackNum (image n u) v ^ (blockMultiplier u).2 *
        slackDen n (u ++ v) :=
  weighted_slack_concat n u v

/-- Normalized budget identity: concatenated `1+q` is the product
of the block slacks with the exact expansion weights. In logs this
is `y_m = Λ_m (y_0 - B_m)`. -/
theorem normalized_budget_identity (n : ℕ) (u v : List Branch) :
    slackNum n (u ++ v) *
        slackDen n u ^ (blockMultiplier v).1 *
        slackDen (image n u) v ^ (blockMultiplier u).2 =
      slackNum n u ^ (blockMultiplier v).1 *
        slackNum (image n u) v ^ (blockMultiplier u).2 *
        slackDen n (u ++ v) :=
  weighted_slack_concat n u v

/-- Local compatibility `c < μ log n` iff `T > n`. This is the
endpoint comparison on one block, not a sequence constraint. -/
theorem block_growth_compat {n : ℕ} {w : List Branch}
    (hn : 1 ≤ n) (hexp : exponentExpanding w) :
    n < image n w ↔
      slackNum n w < slackDen n w * n ^ (expansionMargin w).1 := by
  have hle : 2 ^ w.length ≤ 3 ^ oddCount w := le_of_lt hexp
  have hsum :
      (3 ^ oddCount w - 2 ^ w.length) + 2 ^ w.length = 3 ^ oddCount w :=
    Nat.sub_add_cancel hle
  have hne : 2 ^ w.length ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos _)
  have hnpos : 0 < n := hn
  have hposμ : 0 < n ^ (3 ^ oddCount w - 2 ^ w.length) := Nat.pow_pos hnpos
  constructor
  · intro hlt
    have hpow : n ^ (2 ^ w.length) < image n w ^ (2 ^ w.length) :=
      (Nat.pow_lt_pow_iff_left hne).mpr hlt
    have hmul :
        n ^ (3 ^ oddCount w - 2 ^ w.length) * n ^ (2 ^ w.length) <
          n ^ (3 ^ oddCount w - 2 ^ w.length) *
            image n w ^ (2 ^ w.length) :=
      Nat.mul_lt_mul_of_pos_left hpow hposμ
    calc
      slackNum n w = n ^ (3 ^ oddCount w) := rfl
      _ = n ^ ((3 ^ oddCount w - 2 ^ w.length) + 2 ^ w.length) := by
            rw [hsum]
      _ = n ^ (3 ^ oddCount w - 2 ^ w.length) * n ^ (2 ^ w.length) :=
            pow_add _ _ _
      _ < n ^ (3 ^ oddCount w - 2 ^ w.length) *
            image n w ^ (2 ^ w.length) := hmul
      _ = image n w ^ (2 ^ w.length) *
            n ^ (3 ^ oddCount w - 2 ^ w.length) := by
            rw [mul_comm]
      _ = slackDen n w * n ^ (expansionMargin w).1 := rfl
  · intro h
    have h' : n ^ (3 ^ oddCount w) <
        image n w ^ (2 ^ w.length) *
          n ^ (3 ^ oddCount w - 2 ^ w.length) := by
      simpa [slackNum, slackDen, expansionMargin, blockMultiplier] using h
    have hleft : n ^ (3 ^ oddCount w) =
        n ^ (3 ^ oddCount w - 2 ^ w.length) * n ^ (2 ^ w.length) := by
      nth_rw 1 [← hsum]
      rw [pow_add]
    have hmul :
        n ^ (3 ^ oddCount w - 2 ^ w.length) * n ^ (2 ^ w.length) <
          n ^ (3 ^ oddCount w - 2 ^ w.length) *
            image n w ^ (2 ^ w.length) := by
      rw [← hleft]
      rw [mul_comm (n ^ (3 ^ oddCount w - 2 ^ w.length))]
      exact h'
    have hpow : n ^ (2 ^ w.length) < image n w ^ (2 ^ w.length) :=
      (Nat.mul_lt_mul_left hposμ).mp hmul
    exact (Nat.pow_lt_pow_iff_left hne).mp hpow

theorem pe_ooe_of {x y : ℕ}
    (hw : itinerary x 3 = [.odd, .odd, .even])
    (himg : floorPower^[3] x = y)
    (hxy : x < y) (hy : y % 2 = 1)
    (ht : floorPower y % 2 = 1) :
    PersistentExpandingResidual x y :=
  persistent_expanding_of (by decide) (follows_oddEvenBlock_two_one hw)
    (image_oddEvenBlock_two_one himg) hxy hy ht ooe_is_expanding

theorem oddEvenBlock_four_two :
    oddEvenBlock 4 2 = [.odd, .odd, .odd, .odd, .even, .even] := by
  simp [oddEvenBlock]

theorem ooooee_is_expanding : exponentExpanding (oddEvenBlock 4 2) := by
  rw [exponentExpanding_oddEvenBlock]
  decide

theorem follows_oddEvenBlock_four_two {n : ℕ}
    (h : itinerary n 6 = [.odd, .odd, .odd, .odd, .even, .even]) :
    follows n (oddEvenBlock 4 2) := by
  have hlen : (oddEvenBlock 4 2).length = 6 := length_oddEvenBlock 4 2
  have hw : itinerary n (oddEvenBlock 4 2).length = oddEvenBlock 4 2 := by
    rw [hlen, oddEvenBlock_four_two, h]
  exact (follows_iff_itinerary n _).mpr hw

theorem image_oddEvenBlock_four_two {n y : ℕ}
    (h : floorPower^[6] n = y) :
    image n (oddEvenBlock 4 2) = y := by
  simpa [image_eq_iterate, length_oddEvenBlock] using h

theorem pe_ooooee_of {x y : ℕ}
    (hw : itinerary x 6 = [.odd, .odd, .odd, .odd, .even, .even])
    (himg : floorPower^[6] x = y)
    (hxy : x < y) (hy : y % 2 = 1)
    (ht : floorPower y % 2 = 1) :
    PersistentExpandingResidual x y :=
  persistent_expanding_of (by decide) (follows_oddEvenBlock_four_two hw)
    (image_oddEvenBlock_four_two himg) hxy hy ht ooooee_is_expanding

/-- Four consecutive expanding persistent residual blocks.
This kills any uniform run bound `M ≤ 4`. -/
theorem four_block_pe_1999 :
    PersistentExpandingResidual 1999 5169 ∧
      PersistentExpandingResidual 5169 50093 ∧
      PersistentExpandingResidual 50093 193753 ∧
      PersistentExpandingResidual 193753 887471 := by
  have w1999 : itinerary 1999 3 = [.odd, .odd, .even] := by decide +kernel
  have w5169 : itinerary 5169 6 = [.odd, .odd, .odd, .odd, .even, .even] := by
    decide +kernel
  have w50093 : itinerary 50093 3 = [.odd, .odd, .even] := by decide +kernel
  have w193753 : itinerary 193753 3 = [.odd, .odd, .even] := by decide +kernel
  have i1999 : floorPower^[3] 1999 = 5169 := by decide +kernel
  have i5169 : floorPower^[6] 5169 = 50093 := by decide +kernel
  have i50093 : floorPower^[3] 50093 = 193753 := by decide +kernel
  have i193753 : floorPower^[3] 193753 = 887471 := by decide +kernel
  have h5169 : (5169 : ℕ) % 2 = 1 := by decide +kernel
  have ht5169 : floorPower 5169 % 2 = 1 := by decide +kernel
  have h50093 : (50093 : ℕ) % 2 = 1 := by decide +kernel
  have ht50093 : floorPower 50093 % 2 = 1 := by decide +kernel
  have h193753 : (193753 : ℕ) % 2 = 1 := by decide +kernel
  have ht193753 : floorPower 193753 % 2 = 1 := by decide +kernel
  have h887471 : (887471 : ℕ) % 2 = 1 := by decide +kernel
  have ht887471 : floorPower 887471 % 2 = 1 := by decide +kernel
  exact ⟨
    pe_ooe_of w1999 i1999 (by decide) h5169 ht5169,
    pe_ooooee_of w5169 i5169 (by decide) h50093 ht50093,
    pe_ooe_of w50093 i50093 (by decide) h193753 ht193753,
    pe_ooe_of w193753 i193753 (by decide) h887471 ht887471⟩

theorem four_consecutive_persistent_expanding_exists :
    ∃ x y z u v,
      PersistentExpandingResidual x y ∧
        PersistentExpandingResidual y z ∧
          PersistentExpandingResidual z u ∧
            PersistentExpandingResidual u v :=
  ⟨1999, 5169, 50093, 193753, 887471, four_block_pe_1999⟩

end Problems.Juggler
