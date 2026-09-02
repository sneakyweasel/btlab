import Problems.Juggler.Preimages
import Problems.Juggler.Envelope
import Problems.Juggler.MinimumRelative

namespace Problems.Juggler

/-!
# Cycle itineraries, cells, and CycleMin filters

Semantic cycle foundations: `CycleItinerary`, `CycleMin`, closure,
extrema, and the `AboveAnchor` bridge. Named trajectory exclusions
live in `CycleObstructions`. Isolated-prefix algebra lives in
`FirstInternalOO`.

`CycleItinerary n w` is a realized nonempty return `T_w(n) = n`. Cycle
return is not envelope equality: the defect stays positive. The
lower-growth theorem still gives `n^{3^o - 2^k} ≤ lowerDenom w`.

A last even letter is the square *cell* `n^2 ≤ z < (n+1)^2`, not an
exact-square identity. If a suffix `v` sits at or above the next
square, `vE` cannot be a cycle.

Existing next-square inventory, not a new engine:

* exact `OO` at `N = 5` (`oo_suffix_threshold`)
* exact `OOO` at `N = 3` (`ooo_suffix_threshold`)
* inherited `O^a` for `a ≥ 3` at `N = 3` (odd-append)
* eventual every superquadratic `v` at a huge `Q0(v)`
  (`eventually_no_first_even_contraction`)
* cell-specific `EOO` uses `(√n+1)^2`, not `(n+1)^2`

Every length-5 E-terminating itinerary is either contracting or `OOOOE`.
A cycle minimum forbids an `OE` start: the first even residual is
below `n^2`. An internal `E` plus a next-square suffix then
contradicts the last-even cell.

Extrema, peak blocks, and cycle remainders live in `CycleExtrema`.
This is not a halt theorem and not a claim that every cycle itinerary
is impossible.
-/

def CycleItinerary (n : ℕ) (w : List Branch) : Prop :=
  follows n w ∧ image n w = n ∧ 1 ≤ w.length

theorem cycleItinerary_follows {n : ℕ} {w : List Branch} (h : CycleItinerary n w) :
    follows n w :=
  h.1

theorem cycleItinerary_image {n : ℕ} {w : List Branch} (h : CycleItinerary n w) :
    image n w = n :=
  h.2.1

theorem cycleItinerary_nonempty {n : ℕ} {w : List Branch} (h : CycleItinerary n w) :
    1 ≤ w.length :=
  h.2.2

theorem cycle_itinerary_formally_expanding {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    2 ^ w.length < 3 ^ oddCount w :=
  cycle_strict_envelope hn h.1 h.2.1 h.2.2

theorem cycle_itinerary_not_contracting {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    ¬3 ^ oddCount w < 2 ^ w.length :=
  cycle_not_contracting hn h.1 h.2.1

/-- Cycle return plus lower growth: `n^{3^o} ≤ D_w n^{2^k}`. -/
theorem cycle_lower_growth {n : ℕ} {w : List Branch}
    (hn : 1 ≤ n) (h : CycleItinerary n w) :
    n ^ (3 ^ oddCount w) ≤ lowerDenom w * n ^ (2 ^ w.length) := by
  have hL := lower_growth_word hn h.1
  have himg : image n w = n := h.2.1
  simpa [LowerPowerBound, himg] using hL

/-- The exact cycle size inequality. -/
theorem cycle_pow_le_lowerDenom {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    n ^ (3 ^ oddCount w - 2 ^ w.length) ≤ lowerDenom w := by
  have hexp := cycle_itinerary_formally_expanding hn h
  have hle : 2 ^ w.length ≤ 3 ^ oddCount w := le_of_lt hexp
  have hL := cycle_lower_growth (le_trans (by decide : (1 : ℕ) ≤ 2) hn) h
  have hsplit :
      n ^ (3 ^ oddCount w) =
        n ^ (3 ^ oddCount w - 2 ^ w.length) * n ^ (2 ^ w.length) := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hle]
  rw [hsplit] at hL
  have hpos : 0 < n ^ (2 ^ w.length) :=
    pow_pos (lt_of_lt_of_le (by decide : (0 : ℕ) < 1)
      (le_trans (by decide : (1 : ℕ) ≤ 2) hn)) _
  exact Nat.le_of_mul_le_mul_right hL hpos

/-- Crude explicit bound. Not optimized. -/
theorem cycle_le_lowerDenom {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    n ≤ lowerDenom w := by
  have hpow := cycle_pow_le_lowerDenom hn h
  have hexp := cycle_itinerary_formally_expanding hn h
  have hge : 1 ≤ 3 ^ oddCount w - 2 ^ w.length :=
    Nat.succ_le_of_lt (Nat.sub_pos_of_lt hexp)
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hn
  have hself : n ≤ n ^ (3 ^ oddCount w - 2 ^ w.length) :=
    le_trans (by simp : n ≤ n ^ 1) (Nat.pow_le_pow_right hn1 hge)
  exact le_trans hself hpow

theorem lowerDenom_odd : lowerDenom [.odd] = 4 := by native_decide

theorem lowerDenom_odd_odd : lowerDenom [.odd, .odd] = 1024 := by native_decide

theorem no_cycle_itinerary_odd {n : ℕ} (hn : 2 ≤ n) : ¬CycleItinerary n [.odd] := by
  intro h
  have hle := cycle_le_lowerDenom hn h
  rw [lowerDenom_odd] at hle
  have hodd : n % 2 = 1 := h.1.1
  have himg : floorPower n = n := by simpa [image] using h.2.1
  have hn3 : n = 3 := by
    interval_cases n <;> omega
  subst hn3
  have : floorPower 3 = 5 := by native_decide
  exact (by decide : ¬(5 : ℕ) = 3) (this.symm.trans himg)

theorem cycle_oo_le_four {n : ℕ} (hn : 2 ≤ n)
    (h : CycleItinerary n [.odd, .odd]) : n ≤ 4 := by
  have hpow := cycle_pow_le_lowerDenom hn h
  have hlen : ([.odd, .odd] : List Branch).length = 2 := rfl
  have hodd : oddCount [.odd, .odd] = 2 := by simp
  have : n ^ 5 ≤ 1024 := by
    simpa [hlen, hodd, lowerDenom_odd_odd] using hpow
  refine Nat.lt_succ_iff.mp ?_
  have : ¬5 ≤ n := by
    intro hge
    have h5 : (5 : ℕ) ^ 5 ≤ n ^ 5 := Nat.pow_le_pow_left hge 5
    have : (3125 : ℕ) ≤ 1024 :=
      le_trans (by decide : (3125 : ℕ) ≤ 5 ^ 5) (le_trans h5 this)
    exact (by decide : ¬(3125 : ℕ) ≤ 1024) this
  omega

theorem no_cycle_itinerary_oo {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n [.odd, .odd] := by
  intro h
  have hle := cycle_oo_le_four hn h
  have hodd : n % 2 = 1 := h.1.1
  have hn3 : n = 3 := by
    interval_cases n <;> omega
  subst hn3
  have himg : image 3 [.odd, .odd] = 3 := h.2.1
  have : image 3 [.odd, .odd] = 11 := by native_decide
  exact (by decide : ¬(11 : ℕ) = 3) (this.symm.trans himg)

theorem no_cycle_itinerary_eoo {n : ℕ} (hn : 2 ≤ n) : ¬CycleItinerary n itineraryEOO := by
  intro h
  have hw := h.1
  have himg : floorPower^[3] n = n := by
    have : image n itineraryEOO = floorPower^[3] n := by
      simpa [length_itineraryEOO] using image_eq_iterate n itineraryEOO
    rw [← this, h.2.1]
  rcases eoo_sqrt_cases hw with h1 | h3 | h5
  · have hn2 : n = 2 := eoo_eq_two_of_sqrt_one hw h1
    subst hn2
    have : floorPower^[3] 2 = 1 := floorPower_eoo_two_eq
    exact (by decide : ¬(1 : ℕ) = 2) (this.symm.trans himg)
  · have hout : floorPower^[3] n = 11 :=
      floorPower_eoo_image_of_sqrt_three hw h3
    have hmem := eoo_of_sqrt_three hw h3
    rw [hout] at himg
    rcases hmem with hn10 | hn12 | hn14
    · subst hn10; exact (by decide : ¬(11 : ℕ) = 10) himg
    · subst hn12; exact (by decide : ¬(11 : ℕ) = 12) himg
    · subst hn14; exact (by decide : ¬(11 : ℕ) = 14) himg
  · exact (ne_of_gt (eoo_expands_of_sqrt_ge_five hw h5)) himg

theorem lowerDenom_itineraryOOE : lowerDenom itineraryOOE = 262144 := by native_decide

theorem cycle_ooe_le_lowerDenom {n : ℕ} (hn : 2 ≤ n)
    (h : CycleItinerary n itineraryOOE) : n ≤ 262144 := by
  have := cycle_le_lowerDenom hn h
  simpa [lowerDenom_itineraryOOE] using this

theorem cycle_iterate_period {n : ℕ} {w : List Branch} (h : CycleItinerary n w) :
    floorPower^[w.length] n = n := by
  simpa [image_eq_iterate] using h.2.1

theorem cycle_iterate_one_tail {n k : ℕ} (h : floorPower^[k] n = 1) :
    ∀ j, floorPower^[k + j] n = 1
  | 0 => by simpa using h
  | j + 1 => by
      rw [Nat.add_succ, Function.iterate_succ_apply']
      simpa [cycle_iterate_one_tail h j] using floorPower_one

theorem cycleItinerary_iterate_ge_two {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w) (hi : i < w.length) :
    2 ≤ floorPower^[i] n := by
  have hpos : 1 ≤ floorPower^[i] n :=
    floorPower_iterate_pos (le_trans (by decide : (1 : ℕ) ≤ 2) hn) i
  refine Nat.succ_le_of_lt (lt_of_le_of_ne hpos ?_)
  intro heq
  have htail := cycle_iterate_one_tail heq.symm (w.length - i)
  have hsum : i + (w.length - i) = w.length := Nat.add_sub_of_le (Nat.le_of_lt hi)
  have hone : floorPower^[w.length] n = 1 := by simpa [hsum] using htail
  have : n = 1 := (cycle_iterate_period h).symm.trans hone
  omega

/-- Even states strictly descend. Last-even cycle return is therefore
never a fixed point of `T`. -/
theorem cycle_last_even_interval {n : ℕ} {u : List Branch}
    (h : CycleItinerary n (u ++ [.even])) :
    n ^ 2 ≤ image n u ∧ image n u < (n + 1) ^ 2 := by
  have hf := follows_of_append_right (u := u) h.1
  have he : image n u % 2 = 0 := hf.1
  have hz : floorPower (image n u) = n := by
    have : image (image n u) [.even] = n := by
      simpa [image_append] using h.2.1
    simpa [image] using this
  exact (floorPower_even_eq_iff_sq_interval he).mp hz

/-- If a cycle itinerary ends with `r ≥ 1` even letters, the state before
that even run satisfies `T_v(n) < (n+1)^{2^r}`. The case `r = 1` is
the last-even cell; `r = 2` is the two-even bound used by Lemma 3.5
on `OOOOEE`; `r = 3` is the three-even bound for `OOOOOOEEE`. -/
theorem cycle_trailing_evens_lt {n : ℕ} {v : List Branch} :
    ∀ {r : ℕ}, 1 ≤ r →
      CycleItinerary n (v ++ List.replicate r Branch.even) →
      image n v < (n + 1) ^ (2 ^ r) := by
  intro r hr h
  induction r generalizing v with
  | zero => exact (Nat.not_succ_le_zero 0 hr).elim
  | succ r ih =>
    match r with
    | 0 =>
      have h1 : CycleItinerary n (v ++ [Branch.even]) := by
        simpa [List.replicate] using h
      exact (cycle_last_even_interval h1).2
    | r' + 1 =>
      have hsplit :
          v ++ List.replicate (r' + 2) Branch.even =
            (v ++ [Branch.even]) ++ List.replicate (r' + 1) Branch.even := by
        simp [List.replicate_succ, List.append_assoc]
      have hC : CycleItinerary n
          ((v ++ [Branch.even]) ++ List.replicate (r' + 1) Branch.even) := by
        simpa [hsplit] using h
      have ih' := ih (v := v ++ [Branch.even]) (by omega) hC
      have he : image n v % 2 = 0 := by
        have hf : follows (image n v)
            (List.replicate (r' + 2) Branch.even) :=
          follows_of_append_right (u := v) h.1
        simpa [List.replicate_succ] using hf.1
      have hfp : image n v < (floorPower (image n v) + 1) ^ 2 :=
        ((floorPower_even_eq_iff_sq_interval he).mp rfl).2
      have himg : image n (v ++ [Branch.even]) = floorPower (image n v) := by
        simp [image_append, image]
      have hsucc : floorPower (image n v) + 1 ≤ (n + 1) ^ (2 ^ (r' + 1)) :=
        Nat.succ_le_of_lt (by simpa [himg] using ih')
      have hsq :
          (floorPower (image n v) + 1) ^ 2 ≤
            ((n + 1) ^ (2 ^ (r' + 1))) ^ 2 :=
        Nat.pow_le_pow_left hsucc 2
      have hexp :
          ((n + 1) ^ (2 ^ (r' + 1))) ^ 2 = (n + 1) ^ (2 ^ (r' + 2)) := by
        rw [← Nat.pow_mul]
        exact congrArg (fun e => (n + 1) ^ e) (Nat.pow_succ 2 (r' + 1)).symm
      exact lt_of_lt_of_le hfp (hexp ▸ hsq)

theorem cycle_last_even_ne_odd_sq {n : ℕ} {u : List Branch}
    (hodd : n % 2 = 1) (h : CycleItinerary n (u ++ [.even])) :
    image n u ≠ n ^ 2 :=
  even_ne_odd_square (follows_of_append_right (u := u) h.1).1 hodd

theorem cycle_last_odd_interval {n : ℕ} {u : List Branch}
    (h : CycleItinerary n (u ++ [.odd])) :
    n ^ 2 ≤ image n u ^ 3 ∧ image n u ^ 3 < (n + 1) ^ 2 := by
  have hf := follows_of_append_right (u := u) h.1
  have ho : image n u % 2 = 1 := hf.1
  have hz : floorPower (image n u) = n := by
    have : image (image n u) [.odd] = n := by
      simpa [image_append] using h.2.1
    simpa [image] using this
  exact (floorPower_odd_eq_iff_cube_interval ho).mp hz

theorem cycleItinerary_rotate_cons {n : ℕ} {b : Branch} {w : List Branch}
    (h : CycleItinerary n (b :: w)) :
    CycleItinerary (floorPower n) (w ++ [b]) := by
  have hf0 : follows (floorPower n) w := by
    cases b <;> exact h.1.2
  have hb : follows n [b] := by
    cases b <;> exact ⟨h.1.1, trivial⟩
  have himg_w : image (floorPower n) w = n := by
    simpa [image] using h.2.1
  refine ⟨follows_append hf0 (by simpa [himg_w] using hb), ?_, by simp⟩
  rw [image_append, himg_w]
  cases b <;> simp [image]

theorem exists_iterate_min (n k : ℕ) (hk : 1 ≤ k) :
    ∃ i < k, ∀ j < k, floorPower^[i] n ≤ floorPower^[j] n := by
  induction k with
  | zero => omega
  | succ k ih =>
      match k with
      | 0 =>
          refine ⟨0, by omega, ?_⟩
          intro j hj
          have : j = 0 := by omega
          subst this
          exact le_rfl
      | k' + 1 =>
          have ⟨i, hi, hmin⟩ := ih (by omega : 1 ≤ k' + 1)
          cases le_or_gt (floorPower^[i] n) (floorPower^[k' + 1] n) with
          | inl hle =>
              refine ⟨i, Nat.lt_trans hi (by omega), ?_⟩
              intro j hj
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
              · exact hmin j hlt
              · simpa [heq] using hle
          | inr hgt =>
              refine ⟨k' + 1, by omega, ?_⟩
              intro j hj
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjt | heq
              · exact (le_of_lt hgt).trans (hmin j hjt)
              · subst heq
                exact le_rfl

/-- The minimum state of a nontrivial cycle is odd, because an even
state strictly descends. -/
theorem exists_cycle_min_odd {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    ∃ i < w.length,
      (∀ j < w.length, floorPower^[i] n ≤ floorPower^[j] n) ∧
        floorPower^[i] n % 2 = 1 := by
  have ⟨i, hi, hmin⟩ := exists_iterate_min n w.length h.2.2
  refine ⟨i, hi, hmin, ?_⟩
  have hge := cycleItinerary_iterate_ge_two hn h hi
  rcases Nat.mod_two_eq_zero_or_one (floorPower^[i] n) with he | ho
  · exfalso
    have hlt : floorPower^[i + 1] n < floorPower^[i] n := by
      simpa [Function.iterate_succ_apply'] using floorPower_even_lt hge he
    cases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with
    | inl hlen =>
        exact (not_le_of_gt hlt) (hmin (i + 1) hlen)
    | inr heq =>
        have hper := cycle_iterate_period h
        have hlt' : floorPower^[w.length] n < floorPower^[i] n := by
          convert hlt
          exact heq.symm
        rw [hper] at hlt'
        exact (not_le_of_gt hlt') (hmin 0 (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2))
  · exact ho

theorem no_cycle_itinerary_ooe {n : ℕ} (hn : 2 ≤ n) : ¬CycleItinerary n itineraryOOE := by
  intro h
  have hw := follows_itineraryOOE_iff.mp h.1
  have hOO : follows n [.odd, .odd] := ⟨hw.1, hw.2.1, trivial⟩
  have hcell : CycleItinerary n ([.odd, .odd] ++ [.even]) := by
    simpa [itineraryOOE] using h
  have hI := cycle_last_even_interval hcell
  have hb : image n [.odd, .odd] = floorPower^[2] n :=
    image_eq_iterate n [.odd, .odd]
  rw [hb] at hI
  cases lt_or_ge n 5 with
  | inl hlt =>
      have hn3 : n = 3 := by
        have : n % 2 = 1 := hw.1
        omega
      subst hn3
      have himg : floorPower^[2] 3 = 11 := by
        simpa [eooCellOutput_eq_iterate hOO] using eoo_cell_output_three
      have he : floorPower^[2] 3 % 2 = 0 := by
        have := (follows_of_append_right (u := [.odd, .odd]) hcell.1).1
        simpa [hb] using this
      have : (11 : ℕ) % 2 = 1 := by decide
      omega
  | inr hge =>
      exact (not_le_of_gt hI.2) (oo_suffix_threshold hge hOO)

theorem no_cycle_itinerary_oeo {n : ℕ} (hn : 2 ≤ n) : ¬CycleItinerary n itineraryOEO := by
  intro h
  have hw := follows_itineraryOEO_iff.mp h.1
  have hn3 : 3 ≤ n := by
    have : n % 2 = 1 := hw.1
    omega
  have ha : 2 ≤ floorPower n :=
    le_trans hn (le_of_lt (floorPower_odd_gt hn3 hw.1))
  have hrot : CycleItinerary (floorPower n) itineraryEOO := by
    have hcons : CycleItinerary n (.odd :: [.even, .odd]) := by
      simpa [itineraryOEO] using h
    simpa [itineraryEOO] using cycleItinerary_rotate_cons hcons
  exact no_cycle_itinerary_eoo ha hrot

theorem cycle_last_even_cell {n : ℕ} {v : List Branch}
    (h : CycleItinerary n (v ++ [.even])) :
    n ^ 2 ≤ image n v ∧ image n v < (n + 1) ^ 2 :=
  cycle_last_even_interval h

theorem cycle_last_even_cell_odd {n : ℕ} {v : List Branch}
    (hodd : n % 2 = 1) (h : CycleItinerary n (v ++ [.even])) :
    n ^ 2 < image n v ∧ image n v < (n + 1) ^ 2 :=
  ⟨lt_of_le_of_ne (cycle_last_even_interval h).1
      (cycle_last_even_ne_odd_sq hodd h).symm,
    (cycle_last_even_interval h).2⟩

/-- If a suffix sits at or above the next square, it cannot be the
pre-final state of an E-terminating cycle. -/
theorem no_cycle_append_even_of_suffix_threshold {v : List Branch} {N : ℕ}
    (hth : ∀ m, N ≤ m → follows m v → (m + 1) ^ 2 ≤ image m v)
    {n : ℕ} (hn : N ≤ n) (h : CycleItinerary n (v ++ [.even])) : False :=
  (not_le_of_gt (cycle_last_even_interval h).2)
    (hth n hn (follows_of_append_left h.1))

def itineraryOOOE : List Branch := [.odd, .odd, .odd, .even]

theorem itineraryOOOE_eq_append :
    itineraryOOOE = [.odd, .odd, .odd] ++ [.even] :=
  rfl

theorem no_cycle_itinerary_oooe {n : ℕ} (hn : 2 ≤ n) : ¬CycleItinerary n itineraryOOOE := by
  intro h
  have hcell : CycleItinerary n ([.odd, .odd, .odd] ++ [.even]) := by
    simpa [itineraryOOOE] using h
  have hw := follows_of_append_left hcell.1
  have hn3 : 3 ≤ n := by
    have : n % 2 = 1 := hw.1
    omega
  refine no_cycle_append_even_of_suffix_threshold (N := 3) ?_ hn3 hcell
  intro m hm hf
  simpa [image_eq_iterate] using ooo_suffix_threshold hm hf

theorem no_cycle_itinerary_length_four_ends_even {n : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (hv : v.length = 3)
    (h : CycleItinerary n (v ++ [Branch.even])) : False := by
  have hexp := cycle_itinerary_formally_expanding hn h
  have hlen : (v ++ [Branch.even]).length = 4 := by simp [hv]
  have ho : oddCount (v ++ [Branch.even]) = oddCount v := by
    simp [oddCount_append]
  rw [hlen, ho] at hexp
  have hge : 3 ≤ oddCount v := by
    refine Nat.succ_le_of_lt (lt_of_not_ge fun hle => ?_)
    have hpow : 3 ^ oddCount v ≤ 9 := by
      interval_cases oddCount v <;> decide
    exact (not_le_of_gt hexp) (le_trans hpow (by decide : (9 : ℕ) ≤ 16))
  have hle : oddCount v ≤ 3 := by
    simpa [hv] using oddCount_le_length v
  have hodd : oddCount v = 3 := le_antisymm hle hge
  have hvOOO : v = [.odd, .odd, .odd] := by
    have := eq_replicate_odd_of_oddCount_eq_length (hodd.trans hv.symm)
    simpa [hv] using this
  have hOOOE : CycleItinerary n itineraryOOOE := by
    simpa [itineraryOOOE, hvOOO] using h
  exact no_cycle_itinerary_oooe hn hOOOE

theorem threshold_inherits_odd_append {v : List Branch} {N : ℕ}
    (hth : ∀ m, N ≤ m → follows m v → (m + 1) ^ 2 ≤ image m v)
    {n : ℕ} (hn : N ≤ n) (hw : follows n (v ++ [Branch.odd])) :
    (n + 1) ^ 2 ≤ image n (v ++ [Branch.odd]) := by
  have hv := follows_of_append_left hw
  have hodd : image n v % 2 = 1 := (follows_of_append_right hw).1
  have hge := hth n hn hv
  have himg : image n (v ++ [Branch.odd]) = floorPower (image n v) := by
    rw [image_append]
    simp [image]
  exact le_trans hge (by simpa [himg] using floorPower_odd_ge hodd)

theorem replicate_odd_concat (a : ℕ) :
    List.replicate a Branch.odd ++ [Branch.odd] =
      List.replicate (a + 1) Branch.odd := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [List.replicate_succ, List.cons_append, ih]
      rfl

theorem follows_replicate_odd_head {n a : ℕ} (ha : 1 ≤ a)
    (hw : follows n (List.replicate a Branch.odd)) : n % 2 = 1 := by
  cases a with
  | zero => omega
  | succ a =>
      simpa [List.replicate_succ] using hw.1

theorem odd_run_suffix_threshold_add :
    ∀ k m, 3 ≤ m → follows m (List.replicate (3 + k) Branch.odd) →
      (m + 1) ^ 2 ≤ image m (List.replicate (3 + k) Branch.odd)
  | 0, m, hm, hf => by
      simpa [image_eq_iterate] using ooo_suffix_threshold hm hf
  | k + 1, m, hm, hf => by
      have hrep :
          List.replicate (3 + (k + 1)) Branch.odd =
            List.replicate (3 + k) Branch.odd ++ [Branch.odd] := by
        have : 3 + (k + 1) = (3 + k) + 1 := Nat.add_assoc 3 k 1
        rw [this, replicate_odd_concat]
      have hf' :
          follows m (List.replicate (3 + k) Branch.odd ++ [Branch.odd]) := by
        simpa [hrep] using hf
      have hle :=
        threshold_inherits_odd_append (N := 3)
          (odd_run_suffix_threshold_add k) hm hf'
      simpa [hrep] using hle

theorem odd_run_suffix_threshold {a : ℕ} (ha : 3 ≤ a) :
    ∀ m, 3 ≤ m → follows m (List.replicate a Branch.odd) →
      (m + 1) ^ 2 ≤ image m (List.replicate a Branch.odd) := by
  have hlen : a = 3 + (a - 3) := (Nat.add_sub_of_le ha).symm
  rw [hlen]
  exact odd_run_suffix_threshold_add (a - 3)

theorem no_cycle_odd_run_append_even {a : ℕ} (ha : 3 ≤ a)
    {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (List.replicate a Branch.odd ++ [Branch.even]) := by
  intro h
  have hw := follows_of_append_left h.1
  have hodd :=
    follows_replicate_odd_head (le_trans (by decide : (1 : ℕ) ≤ 3) ha) hw
  have hn3 : 3 ≤ n := by omega
  exact no_cycle_append_even_of_suffix_threshold
    (odd_run_suffix_threshold ha) hn3 h

/-- Coarse coverage: every expanding `vE` is excluded above a huge `Q0`. -/
theorem eventually_no_cycle_append_even {v : List Branch}
    (hα : 2 ^ (v.length + 1) < 3 ^ oddCount v) :
    ∃ Q0, ∀ n, Q0 ≤ n → ¬CycleItinerary n (v ++ [Branch.even]) := by
  rcases eventually_no_first_even_contraction hα with ⟨Q0, hth⟩
  exact ⟨Q0, fun n hn h => no_cycle_append_even_of_suffix_threshold hth hn h⟩

/-- Every length-5 E-terminating cycle itinerary is impossible: it is either
formally contracting, or it is `OOOOE` and inherits the `OOO` threshold. -/
theorem no_cycle_itinerary_length_five_ends_even {n : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (hv : v.length = 4)
    (h : CycleItinerary n (v ++ [Branch.even])) : False := by
  have hexp := cycle_itinerary_formally_expanding hn h
  have hlen : (v ++ [Branch.even]).length = 5 := by simp [hv]
  have ho : oddCount (v ++ [Branch.even]) = oddCount v := by
    simp [oddCount_append]
  rw [hlen, ho] at hexp
  have hge : 4 ≤ oddCount v := by
    refine Nat.succ_le_of_lt (lt_of_not_ge fun hle => ?_)
    have hpow : 3 ^ oddCount v ≤ 27 := by
      interval_cases oddCount v <;> decide
    exact (not_le_of_gt hexp) (le_trans hpow (by decide : (27 : ℕ) ≤ 32))
  have hle : oddCount v ≤ 4 := by
    simpa [hv] using oddCount_le_length v
  have hodd : oddCount v = 4 := le_antisymm hle hge
  have hvO : v = List.replicate 4 Branch.odd := by
    have := eq_replicate_odd_of_oddCount_eq_length (hodd.trans hv.symm)
    simpa [hv] using this
  have hC : CycleItinerary n (List.replicate 4 Branch.odd ++ [Branch.even]) := by
    simpa [hvO] using h
  exact no_cycle_odd_run_append_even (by decide : (3 : ℕ) ≤ 4) hn hC

/-- The start is a minimum of its realized cycle. Cycle-internal. -/
def CycleMin (n : ℕ) (w : List Branch) : Prop :=
  CycleItinerary n w ∧ ∀ j, j < w.length → n ≤ floorPower^[j] n

theorem cycleMin_cycleItinerary {n : ℕ} {w : List Branch} (h : CycleMin n w) :
    CycleItinerary n w :=
  h.1

theorem cycleMin_ge {n : ℕ} {w : List Branch} {j : ℕ}
    (h : CycleMin n w) (hj : j < w.length) : n ≤ floorPower^[j] n :=
  h.2 j hj

/-- A cycle minimum is minimum-relative: interior states are `≥ n`
by the ge-filter, and the endpoint is `n` by closure. -/
theorem aboveAnchor_of_cycleMin {n : ℕ} {w : List Branch}
    (h : CycleMin n w) : AboveAnchor n w := by
  refine ⟨h.1.1, ?_⟩
  intro i hi
  rcases lt_or_eq_of_le hi with hlt | heq
  · exact cycleMin_ge h hlt
  · have himg : floorPower^[w.length] n = n := cycle_iterate_period h.1
    rw [heq]
    exact le_of_eq himg.symm

/-- On a `CycleMin`, every iterate through one period is at least
the start (the boundary `j = L` returns to the start exactly).
Instance of the `AboveAnchor` bridge. -/
theorem cycleMin_iterate_ge {n : ℕ} {w : List Branch} (h : CycleMin n w) :
    ∀ j, j ≤ w.length → n ≤ floorPower^[j] n :=
  (aboveAnchor_of_cycleMin h).2

/-- Prefix non-contraction on an `AboveAnchor` prefix: a
walk-negative prefix would contract strictly below the anchor
(`power_bound_contracts`), so a never-descending trajectory segment
keeps `u_k ≥ 0` at every prefix length. The primitive form; a
minimum-based cycle is the closed instance. -/
theorem aboveAnchor_prefix_pow_le {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : AboveAnchor n w) :
    ∀ k, k ≤ w.length → 2 ^ k ≤ 3 ^ oddCount (w.take k) := by
  intro k hk
  by_contra hc
  have hf : follows n (w.take k) := follows_take w k h.1
  have hlen : (w.take k).length = k := by
    simp [List.length_take, Nat.min_eq_left hk]
  have hgap : 3 ^ oddCount (w.take k) < 2 ^ (w.take k).length := by
    rw [hlen]; exact Nat.lt_of_not_le hc
  have hcontr := power_bound_contracts hn hf hgap
  rw [hlen] at hcontr
  exact absurd hcontr (not_lt.mpr (h.2 k hk))

/-- Prefix non-contraction on a `CycleMin`: an exponent-gap prefix
would contract strictly below the cycle minimum. Closed instance of
`aboveAnchor_prefix_pow_le`. -/
theorem cycleMin_prefix_pow_le {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∀ k, k ≤ w.length → 2 ^ k ≤ 3 ^ oddCount (w.take k) :=
  aboveAnchor_prefix_pow_le hn (aboveAnchor_of_cycleMin h)

theorem cycle_iterate_mul_length {n : ℕ} {w : List Branch}
    (h : CycleItinerary n w) : ∀ q, floorPower^[q * w.length] n = n
  | 0 => by simp
  | q + 1 => by
      have hmul : (q + 1) * w.length = q * w.length + w.length :=
        Nat.succ_mul q w.length
      rw [hmul, Function.iterate_add_apply, cycle_iterate_period h,
        cycle_iterate_mul_length h q]

theorem cycle_iterate_mod {n : ℕ} {w : List Branch} {k : ℕ}
    (h : CycleItinerary n w) : floorPower^[k] n = floorPower^[k % w.length] n := by
  have hsum : k = k % w.length + k / w.length * w.length := by
    have hdiv := Nat.div_add_mod k w.length
    rw [Nat.mul_comm, Nat.add_comm] at hdiv
    exact hdiv.symm
  conv => lhs; rw [hsum]
  rw [Function.iterate_add_apply, cycle_iterate_mul_length h]

theorem cycleMin_succ_ge {n : ℕ} {w : List Branch} {i : ℕ}
    (h : CycleMin n w) (hi : i < w.length) :
    n ≤ floorPower (floorPower^[i] n) := by
  have hnext : floorPower (floorPower^[i] n) = floorPower^[i + 1] n :=
    (Function.iterate_succ_apply' floorPower i n).symm
  rw [hnext]
  cases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with
  | inl hlt =>
      exact cycleMin_ge h hlt
  | inr heq =>
      rw [← Nat.succ_eq_add_one, heq, cycle_iterate_period h.1]

/-- Even cycle states sit at or above `n^2`. The next-state lower
bound is the shared `AboveAnchor` cell, including the closing
return `T_w(n)=n`. -/
theorem cycleMin_even_ge_sq {n : ℕ} {w : List Branch} {i : ℕ}
    (_hn : 2 ≤ n) (h : CycleMin n w) (hi : i < w.length)
    (he : floorPower^[i] n % 2 = 0) :
    n ^ 2 ≤ floorPower^[i] n :=
  even_ge_sq_of_aboveAnchor (aboveAnchor_of_cycleMin h)
    (Nat.succ_le_of_lt hi) he

theorem floorPower_odd_lt_sq {n : ℕ} (hn : 2 ≤ n) (hodd : n % 2 = 1) :
    floorPower n < n ^ 2 :=
  odd_floor_lt_sq hn hodd

theorem cycleMin_start_odd {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · exfalso
    have hlt : floorPower n < n := floorPower_even_lt hn he
    cases Nat.eq_or_lt_of_le h.1.2.2 with
    | inl h1 =>
        have hper := cycle_iterate_period h.1
        have hlen1 : w.length = 1 := by omega
        rw [hlen1] at hper
        change floorPower n = n at hper
        omega
    | inr hgt =>
        have hge : n ≤ floorPower^[1] n := cycleMin_ge h hgt
        exact (not_le_of_gt hlt) hge
  · exact ho

theorem cycleMin_not_start_even {n : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n (.even :: v)) : False := by
  have he : n % 2 = 0 := h.1.1.1
  have ho := cycleMin_start_odd hn h
  omega

/-- A cycle minimum cannot start `OE`: the first even residual is `< n^2`. -/
theorem cycleMin_not_odd_even {n : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n (.odd :: .even :: v)) : False :=
  aboveAnchor_not_odd_even hn (aboveAnchor_of_cycleMin h)

def rotateItinerary : List Branch → ℕ → List Branch
  | w, 0 => w
  | [], _k + 1 => []
  | b :: rest, k + 1 => rotateItinerary (rest ++ [b]) k

theorem rotateItinerary_length : ∀ w k, (rotateItinerary w k).length = w.length
  | w, 0 => rfl
  | [], _k + 1 => rfl
  | b :: rest, k + 1 => by
      have := rotateItinerary_length (rest ++ [b]) k
      simpa [rotateItinerary, List.length_append] using this

/-- `rotateItinerary` is the cyclic shift `drop k ++ take k` for `k` up to
the length. -/
theorem rotateItinerary_eq_drop_append_take :
    ∀ (w : List Branch) (k : ℕ), k ≤ w.length →
      rotateItinerary w k = w.drop k ++ w.take k
  | _w, 0, _ => by simp [rotateItinerary]
  | [], k + 1, hk => by simp at hk
  | b :: rest, k + 1, hk => by
      have hkr : k ≤ rest.length := by
        simp only [List.length_cons] at hk
        omega
      have hk' : k ≤ (rest ++ [b]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      show rotateItinerary (rest ++ [b]) k =
        (b :: rest).drop (k + 1) ++ (b :: rest).take (k + 1)
      rw [rotateItinerary_eq_drop_append_take (rest ++ [b]) k hk']
      rw [List.drop_append_of_le_length hkr,
        List.take_append_of_le_length hkr]
      simp [List.append_assoc]

theorem cycleItinerary_rotateItinerary {n : ℕ} {w : List Branch}
    (h : CycleItinerary n w) : ∀ k, CycleItinerary (floorPower^[k] n) (rotateItinerary w k)
  | 0 => by simpa [rotateItinerary] using h
  | k + 1 => by
      match w with
      | [] =>
          exact (Nat.not_succ_le_zero 0 h.2.2).elim
      | b :: rest =>
          have hrot := cycleItinerary_rotate_cons (by simpa using h)
          have ih := cycleItinerary_rotateItinerary hrot k
          have : floorPower^[k + 1] n = floorPower^[k] (floorPower n) :=
            Function.iterate_succ_apply floorPower k n
          simpa [rotateItinerary, this] using ih

theorem exists_cycleMin {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    ∃ k < w.length, CycleMin (floorPower^[k] n) (rotateItinerary w k) := by
  have ⟨i, hi, hle, _hodd⟩ := exists_cycle_min_odd hn h
  refine ⟨i, hi, cycleItinerary_rotateItinerary h i, ?_⟩
  intro j hj
  have hlen : (rotateItinerary w i).length = w.length := rotateItinerary_length w i
  rw [hlen] at hj
  have himg : floorPower^[j] (floorPower^[i] n) = floorPower^[i + j] n := by
    simpa [Nat.add_comm] using
      (Function.iterate_add_apply floorPower j i n).symm
  rw [himg, cycle_iterate_mod (k := i + j) h]
  exact hle _ (Nat.mod_lt _ (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2))

/-- A `CycleMin` rotation starts at a global minimum of the trajectory. -/
theorem cycleMin_le_cycle_state {n : ℕ} {w : List Branch} {k j : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length) (hj : j < w.length)
    (hmin : CycleMin (floorPower^[k] n) (rotateItinerary w k)) :
    floorPower^[k] n ≤ floorPower^[j] n := by
  have hlen : (rotateItinerary w k).length = w.length := rotateItinerary_length w k
  have hL : 0 < w.length :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2
  let t := (j + (w.length - k)) % w.length
  have ht : t < (rotateItinerary w k).length := by
    simpa [t, hlen] using Nat.mod_lt (j + (w.length - k)) hL
  have himg : floorPower^[t] (floorPower^[k] n) = floorPower^[k + t] n := by
    simpa [Nat.add_comm] using
      (Function.iterate_add_apply floorPower t k n).symm
  have hmod : (k + t) % w.length = j := by
    have hsum : k + (j + (w.length - k)) = j + w.length := by omega
    have hred : (k + t) % w.length = (j + w.length) % w.length := by
      simp only [t]
      rw [Nat.add_mod_mod, hsum]
    have hr : (j + w.length) % w.length = j := by
      rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
      exact Nat.mod_eq_of_lt hj
    exact hred.trans hr
  have hpj : floorPower^[k + t] n = floorPower^[j] n := by
    rw [cycle_iterate_mod h, cycle_iterate_mod (k := j) h, hmod,
      Nat.mod_eq_of_lt hj]
  have hge := cycleMin_ge hmin ht
  simpa [himg, hpj] using hge

theorem cycle_min_value_unique {n : ℕ} {w : List Branch} {k k' : ℕ}
    (h : CycleItinerary n w) (hk : k < w.length) (hk' : k' < w.length)
    (hmin : CycleMin (floorPower^[k] n) (rotateItinerary w k))
    (hmin' : CycleMin (floorPower^[k'] n) (rotateItinerary w k')) :
    floorPower^[k] n = floorPower^[k'] n :=
  le_antisymm
    (cycleMin_le_cycle_state h hk hk' hmin)
    (cycleMin_le_cycle_state h hk' hk hmin')

/-- A nontrivial cycle cannot reach 1. -/
theorem cycleItinerary_not_reachesOne {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : ¬ReachesOne n := by
  intro ⟨k, hk⟩
  have hmod : floorPower^[k] n = floorPower^[k % w.length] n :=
    cycle_iterate_mod h
  rw [hmod] at hk
  have hlenpos : 0 < w.length :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2
  have hlt : k % w.length < w.length := Nat.mod_lt k hlenpos
  have hge := cycleItinerary_iterate_ge_two hn h hlt
  omega

/-- Residual class `R = {1,…,11}` is disjoint from a nontrivial cycle. -/
theorem cycleItinerary_iterate_not_lt_twelve {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    12 ≤ floorPower^[i] n := by
  by_contra h12
  have hmod : floorPower^[i] n = floorPower^[i % w.length] n :=
    cycle_iterate_mod h
  have hlenpos : 0 < w.length :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2
  have hlt : i % w.length < w.length := Nat.mod_lt i hlenpos
  have hge := cycleItinerary_iterate_ge_two hn h hlt
  have hpos : 1 ≤ floorPower^[i] n := by
    have : 2 ≤ floorPower^[i % w.length] n := hge
    exact le_trans (by decide : (1 : ℕ) ≤ 2) (by simpa [hmod] using this)
  have hy : floorPower^[i] n < 12 := Nat.lt_of_not_ge h12
  have hR : ReachesOne (floorPower^[i] n) :=
    reachesOne_of_lt_twelve hpos hy
  exact cycleItinerary_not_reachesOne hn h (reachesOne_of_iterate rfl hR)

/-- Internal `E` plus a next-square suffix contradicts the last-even cell
on a cycle minimum. `y ≥ n` is enough; `y > n` is not required. -/
theorem no_cycleMin_internal_even_threshold {u v : List Branch} {N : ℕ}
    (hth : ∀ m, N ≤ m → follows m v → (m + 1) ^ 2 ≤ image m v)
    {n : ℕ} (hn : N ≤ n)
    (h : CycleMin n (u ++ [.even] ++ v ++ [.even])) : False := by
  have hw : CycleItinerary n (u ++ [.even] ++ v ++ [.even]) := h.1
  have hcell : CycleItinerary n ((u ++ [.even] ++ v) ++ [.even]) := by
    simpa [List.append_assoc] using hw
  have hI := cycle_last_even_interval hcell
  have himg_y := image_eq_iterate n (u ++ [.even])
  have hlen :
      (u ++ [Branch.even]).length <
        (u ++ [Branch.even] ++ v ++ [Branch.even]).length := by
    simp [List.length_append]
  have hy_ge : n ≤ image n (u ++ [.even]) := by
    simpa [himg_y] using cycleMin_ge h hlen
  have hf_tail : follows (image n (u ++ [.even])) (v ++ [.even]) :=
    follows_of_append_right (u := u ++ [.even])
      (by simpa [List.append_assoc] using hw.1)
  have hf_v : follows (image n (u ++ [.even])) v :=
    follows_of_append_left (v := [.even]) hf_tail
  have hth' := hth _ (le_trans hn hy_ge) hf_v
  have himg : image n (u ++ [.even] ++ v) = image (image n (u ++ [.even])) v :=
    image_append n (u ++ [.even]) v
  rw [himg] at hI
  have hy2 : (n + 1) ^ 2 ≤ image (image n (u ++ [.even])) v :=
    le_trans (Nat.pow_le_pow_left (Nat.succ_le_succ hy_ge) 2) hth'
  exact (not_le_of_gt hI.2) hy2

/-- A cycle minimum cannot end in `O`: the last-odd cell is
`n^2 ≤ x^3 < (n+1)^2`, while `x ≥ n` forces `n^3 < (n+1)^2`. -/
theorem cycleMin_not_end_odd {n : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n (u ++ [Branch.odd])) : False := by
  have hodd := cycleMin_start_odd hn h
  have hn3 : 3 ≤ n := by omega
  have hI := cycle_last_odd_interval h.1
  have hlen : u.length < (u ++ [Branch.odd]).length := by simp
  have hx : n ≤ image n u := by
    simpa [image_eq_iterate] using cycleMin_ge h hlen
  have hcube : n ^ 3 ≤ image n u ^ 3 := Nat.pow_le_pow_left hx 3
  exact (not_lt_of_ge (succ_sq_le_cube hn3)) (lt_of_le_of_lt hcube hI.2)

/-- Prefix `OOO` plus an internal even step cannot land at the cycle
minimum: `T^3(n) ≥ (n+1)^2` and `isqrt(T^3(n)) = n` are incompatible. -/
theorem cycleMin_prefix_ooo_even_sqrt_ne {n : ℕ} {v : List Branch}
    (hn : 2 ≤ n)
    (h : CycleMin n
      ([Branch.odd, Branch.odd, Branch.odd] ++ [Branch.even] ++
        v ++ [Branch.even])) :
    image n ([Branch.odd, Branch.odd, Branch.odd] ++ [Branch.even]) ≠ n := by
  intro hy
  have hOOO : follows n [Branch.odd, Branch.odd, Branch.odd] :=
    follows_of_append_left (by simpa [List.append_assoc] using h.1.1)
  have hn3 : 3 ≤ n := by
    have : n % 2 = 1 := h.1.1.1
    omega
  have hth : (n + 1) ^ 2 ≤ floorPower^[3] n :=
    ooo_suffix_threshold hn3 hOOO
  have hfE :
      follows (image n [Branch.odd, Branch.odd, Branch.odd]) [Branch.even] :=
    follows_of_append_right (u := [Branch.odd, Branch.odd, Branch.odd])
      (follows_of_append_left (v := v ++ [Branch.even])
        (by simpa [List.append_assoc] using h.1.1))
  have he : image n [Branch.odd, Branch.odd, Branch.odd] % 2 = 0 := hfE.1
  have himg3 : image n [Branch.odd, Branch.odd, Branch.odd] = floorPower^[3] n :=
    image_eq_iterate n [Branch.odd, Branch.odd, Branch.odd]
  have hfp : floorPower (image n [Branch.odd, Branch.odd, Branch.odd]) = n := by
    have himg :
        image n ([Branch.odd, Branch.odd, Branch.odd] ++ [Branch.even]) =
          floorPower (image n [Branch.odd, Branch.odd, Branch.odd]) := by
      simp [image]
    exact himg ▸ hy
  have hI := (floorPower_even_eq_iff_sq_interval he).mp hfp
  rw [himg3] at hI
  exact (not_le_of_gt hI.2) hth

/-!
## Named itinerary exclusions

Historical short-word CycleMin / CycleItinerary refutations live in
`CycleObstructions`. This file keeps cycle foundations only.
-/

end Problems.Juggler
