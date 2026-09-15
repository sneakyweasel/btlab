# Rating sheet: the twenty most surprising proofs that are not copies, templates or certificates

Mark each: **routine** (I'd have written this), **neat** (a move I'd remember), or **wrong-list** (this is a template or certificate the filter missed).

## 1. `height_strip`  (formal/Problems/Juggler/CubicReturnStrip.lean:8)
mean surprise 3.07 nats/token, 48 tokens, first tactic `obtain`

```lean
/-- Exact first-return ordering excludes the terminal strip of a cubic band.
The integer conclusion is equivalent to `M < m³ - m^(15/8)`. -/
theorem height_strip {C : Set ℕ} {m M : ℕ}
    (D : PeriodicExtrema C m M) (hm : 7 ≤ m) (hM : M < m ^ 3) :
    m ^ 15 < (m ^ 3 - M) ^ 8 := by
  obtain ⟨_, hmax, hseam⟩ := exact_return_seam D (by omega) hM
  exact cubic_return_height_algebra hm (ReturnCells.ooe_upper_pow m) hseam hmax
```

Rating: 

## 2. `cycle_remainders_project_to_envelope`  (formal/Problems/Juggler/CycleExtrema.lean:1112)
mean surprise 2.70 nats/token, 17 tokens, first tactic `simpa`

```lean
/-- Dropping every remainder recovers the ordinary itinerary envelope. -/
theorem cycle_remainders_project_to_envelope {n : ℕ} {w : List Branch}
    (h : CycleItinerary n w) :
    (floorPower^[w.length] n) ^ (2 ^ w.length) ≤
      n ^ (3 ^ oddCount w) := by
  simpa [image_eq_iterate] using power_bound_word h.1
```

Rating: 

## 3. `cubicResid_one_neg`  (formal/BTCalculus/CubicResidual.lean:386)
mean surprise 2.64 nats/token, 19 tokens, first tactic `unfold`

```lean
/-- `cubicResid 1 (-1) = cubic 9 (-9) 3 0`. -/
theorem cubicResid_one_neg :
    cubicResid 1 (-1) = cubic 9 (-9) 3 0 := by
  unfold cubicResid
  simp [iterDZ, DZ_neg_one]
```

Rating: 

## 4. `succIdx_val_of_lt`  (formal/Problems/Juggler/CubicRemainderAssembly.lean:303)
mean surprise 2.50 nats/token, 34 tokens, first tactic `let`

```lean
theorem succIdx_val_of_lt (Q : OrbitUpperChargeCertificate m M k)
    {i : Fin Q.length} (h : i.val + 1 < Q.length) :
    (succIdx Q i).val = i.val + 1 := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  rw [succIdx, finRotate_val, Nat.mod_eq_of_lt h]
```

Rating: 

## 5. `warp_wordThree`  (formal/Operators/Algebra.lean:38)
mean surprise 2.43 nats/token, 29 tokens, first tactic `unfold`

```lean
theorem warp_wordThree : warpWord wordThree = [Trit.plus] := by
  unfold warpWord canonicalize dropLeadingZeros wordThree
  simp [List.reverse_cons, List.reverse_nil, List.dropWhile]
```

Rating: 

## 6. `guard_int_sqrt_cell`  (formal/Problems/Juggler/GuardResidueFamily.lean:357)
mean surprise 2.43 nats/token, 51 tokens, first tactic `have`

```lean
private theorem guard_int_sqrt_cell {a v : ℤ}
    (ha : 0 ≤ a) (hv : 0 ≤ v)
    (hlo : v^2 ≤ a^9) (hhi : a^9 < (v+1)^2) :
    Nat.sqrt ((a.toNat^3)^3) = v.toNat := by
  have hc := NumericBridge.int_toNat_pow_cell ha hv hlo hhi
  apply (Nat.eq_sqrt.mpr ?_).symm
  simpa only [← pow_mul, Nat.reduceMul, pow_two] using hc
```

Rating: 

## 7. `PZ_zero_eq`  (formal/Problems/BalancedTernary/SignedP0.lean:21)
mean surprise 2.37 nats/token, 27 tokens, first tactic `unfold`

```lean
theorem PZ_zero_eq (n : ℤ) : PZ Trit.zero n = n - lsdZ n := by
  unfold PZ IZ
  simp [Trit.toInt]
  simpa [SZ] using S_after_D_int n
```

Rating: 

## 8. `actual_OE_lower_cube`  (formal/Problems/Juggler/QuarticCells.lean:271)
mean surprise 2.35 nats/token, 30 tokens, first tactic `exact`

```lean
theorem actual_OE_lower_cube {x : ℕ}
    (hx : x % 2 = 1) (hO : O x % 2 = 0) (hB : B x % 2 = 1) :
    (B x ^ 2 + 1) ^ 2 + 3 ≤ x ^ 3 := by
  exact guarded_OE_lower_cube hx hO hB (CubicReturn.O_sq_le x)
    (B_source_cell x).1
```

Rating: 

## 9. `cycleMin_finance_inv_sum`  (formal/Problems/Juggler/CycleFinance.lean:377)
mean surprise 2.34 nats/token, 42 tokens, first tactic `have`

```lean
/-- **Inv-sum finance inequality.** Same one-step-preimage-log defects as
`cycleMin_finance`, remainders kept as `1/x_{i+1}`.
`(3^o - 2^L) log n ≤ 3^o ∑ 1/x_i`. -/
theorem cycleMin_finance_inv_sum {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) * Real.log n ≤
      (3 : ℝ) ^ oddCount w *
        ∑ i ∈ Finset.range w.length, (1 : ℝ) / (floorPower^[i + 1] n) := by
  have henv := cycleMin_log_envelope_inv hn h w.length le_rfl
  rw [List.take_length, cycle_iterate_period h.1] at henv
  linarith
```

Rating: 

## 10. `low_odd`  (formal/Problems/Juggler/QuarticBand.lean:15)
mean surprise 2.26 nats/token, 78 tokens, first tactic `rcases`

```lean
theorem low_odd (D : PeriodicExtrema C m M) {x : ℕ}
    (hx : x ∈ C) (hl : x < m ^ 2) : x % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one x with he | ho
  · have hb := (D.bounds _ (D.closed _ hx)).1
    rw [floorPower_even_eq he] at hb
    have hs : x.sqrt < m := Nat.sqrt_lt.mpr (by simpa [pow_two] using hl)
    omega
  · exact ho
```

Rating: 

## 11. `no_cycle_itinerary_ooooooee`  (formal/Problems/Juggler/LengthEightCensus.lean:232)
mean surprise 2.24 nats/token, 45 tokens, first tactic `simpa`

```lean
theorem no_cycle_itinerary_ooooooee {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n
      [.odd, .odd, .odd, .odd, .odd, .odd, .even, .even] := by
  simpa [twoEvenEE] using
    no_cycle_itinerary_two_even_ee (n := n) (k := 8) hn (by decide : (6 : ℕ) ≤ 8)
```

Rating: 

## 12. `packWord_integerJet_balWidth`  (formal/BTCalculus/CubicDeepestLayer.lean:134)
mean surprise 2.23 nats/token, 32 tokens, first tactic `have`

```lean
/-- A packed jet has balanced width `m`. -/
lemma packWord_integerJet_balWidth (m : ℕ) (n : ℤ) :
    balWidth m (packWord (integerJet m n)) := by
  have := two_mul_packWord_le (isTritList_integerJet m n)
  simpa [balWidth, integerJet_length] using this
```

Rating: 

## 13. `odd_run_lower_growth`  (formal/Problems/Juggler/LeftoverPreimage.lean:185)
mean surprise 2.19 nats/token, 42 tokens, first tactic `have`

```lean
theorem odd_run_lower_growth {n a : ℕ} (hn : 1 ≤ n)
    (hw : follows n (List.replicate a Branch.odd)) :
    n ^ (3 ^ a) ≤
      2 ^ denomBits a * image n (List.replicate a Branch.odd) ^ (2 ^ a) := by
  have hL := lower_growth_word hn hw
  simpa [LowerPowerBound, oddCount_replicate_odd, List.length_replicate,
    lowerDenom_replicate_odd] using hL
```

Rating: 

## 14. `even_run_contracts`  (formal/Problems/Juggler/CycleRunAlphabet.lean:101)
mean surprise 2.19 nats/token, 25 tokens, first tactic `rw`

```lean
/-- **The even-run bound.**  After `g` even steps from `w`, the bottom `z` satisfies
`z^(2^g) ≤ w`: the logarithm has been divided by at least `2^g`. -/
theorem even_run_contracts {w g : ℕ} (heven : ∀ i < g, Nat.sqrt^[i] w % 2 = 0) :
    (floorPower^[g] w) ^ 2 ^ g ≤ w := by
  rw [floorPower_iter_of_even heven]
  exact ((sqrt_iter_eq_iff g).mp rfl).1
```

Rating: 

## 15. `cycleItineraryB_iff`  (formal/Problems/Juggler/LeftoverShort.lean:32)
mean surprise 2.08 nats/token, 31 tokens, first tactic `simp`

```lean
theorem cycleItineraryB_iff {n : ℕ} {w : List Branch} :
    cycleItineraryB n w = true ↔ CycleItinerary n w := by
  simp [cycleItineraryB, CycleItinerary, followsB_iff, Bool.and_eq_true, beq_iff_eq]
  exact and_assoc
```

Rating: 

## 16. `oddCount_take_succ`  (formal/Problems/Juggler/WalkTransport.lean:187)
mean surprise 2.08 nats/token, 35 tokens, first tactic `rw`

```lean
/-- One more letter adds one to the odd count exactly when that letter is odd. -/
theorem oddCount_take_succ {w : List Branch} {k : ℕ} (hk : k < w.length) :
    oddCount (w.take (k + 1)) =
      oddCount (w.take k) + if w[k] = .odd then 1 else 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  cases h : w[k] <;> simp [oddCount_append]
```

Rating: 

## 17. `rotateItinerary_cons`  (formal/Problems/Juggler/LeftoverFamilies.lean:2494)
mean surprise 2.05 nats/token, 33 tokens, first tactic `rw`

```lean
theorem rotateItinerary_cons {w : List Branch} {k : ℕ} (hk : k < w.length) :
    rotateItinerary w k = w[k] :: (w.drop (k + 1) ++ w.take k) := by
  rw [rotateItinerary_eq_drop_append_take w k (Nat.le_of_lt hk),
    List.drop_eq_getElem_cons hk, List.cons_append]
```

Rating: 

## 18. `Am_step_le`  (formal/Problems/Juggler/FateThinFibers.lean:99)
mean surprise 2.04 nats/token, 25 tokens, first tactic `unfold`

```lean
theorem Am_step_le {m : ℕ} (hm : 1 ≤ m) : Am (m + 1) - Am m ≤ eps m := by
  unfold Am eps
  have := rpow_two_thirds_succ_le hm
  push_cast
  linarith
```

Rating: 

## 19. `oe_block_scale`  (formal/Problems/Juggler/Scale.lean:15)
mean surprise 1.97 nats/token, 25 tokens, first tactic `have`

```lean
/-- One realized `OE` block: `T^2(x)^4 ≤ x^3`. -/
theorem oe_block_scale {x : ℕ} (hw : follows x itineraryOE) :
    image x itineraryOE ^ 4 ≤ x ^ 3 := by
  have h := power_bound_word hw
  simpa [itineraryOE, image_eq_iterate] using h
```

Rating: 

## 20. `next_succ`  (formal/Problems/Juggler/CubicRemainderAssembly.lean:318)
mean surprise 1.96 nats/token, 59 tokens, first tactic `let`

```lean
theorem next_succ (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) :
    Q.next (succIdx Q i) = succIdx Q (Q.next i) := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  have hcomm :=
    rank_commute_finRotate Q.next (evenCount Q) (fun j => by
      simpa [evenCount] using Q.rotation j)
  exact hcomm.eq i
```

Rating: 

