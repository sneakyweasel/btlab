import Problems.Juggler.LeftoverFamilies
import Problems.Juggler.CycleExtrema
import Problems.Juggler.Residuals

namespace Problems.Juggler

/-!
# Laboratory assembler: no cycle itinerary with even-count at most three

Every `CycleItinerary` has a `CycleMin` rotation. A cycle minimum starts
`OO`, ends `E`, and is formally expanding. The even-terminating
expanding itineraries with at most three evens are the odd-run family, the
two-even leftovers (Theorem 3.12), the internal-E bootstrap, the
seven bunched leftovers (Theorems 3.14--3.20), and the gapped
leftovers (Theorems 3.13 and 3.21).

This is Paper A Theorem 3.22 / Corollary 3.23, imported by
`Problems.JugglerPaper`. It is an even-count theorem, not a
length-9 or length-10 itinerary census. Not a halt theorem and not
an exclusion of four-even leftovers. First-even overshoot
sharpens the extrema package to `M ≥ (m+1)^2`.
-/

def evenCount : List Branch → ℕ
  | [] => 0
  | .even :: w => evenCount w + 1
  | .odd :: w => evenCount w

@[simp] theorem evenCount_nil : evenCount [] = 0 := rfl

@[simp] theorem evenCount_even_cons (w : List Branch) :
    evenCount (.even :: w) = evenCount w + 1 := rfl

@[simp] theorem evenCount_odd_cons (w : List Branch) :
    evenCount (.odd :: w) = evenCount w := rfl

theorem evenCount_append : ∀ u v : List Branch,
    evenCount (u ++ v) = evenCount u + evenCount v
  | [], _ => by simp
  | .even :: u, v => by
      have ih := evenCount_append u v
      simp [ih]
      omega
  | .odd :: u, v => by
      simp [evenCount_append u v]

theorem evenCount_replicate_odd (k : ℕ) :
    evenCount (List.replicate k Branch.odd) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

theorem evenCount_replicate_even (k : ℕ) :
    evenCount (List.replicate k Branch.even) = k := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

theorem evenCount_add_oddCount : ∀ w : List Branch,
    evenCount w + oddCount w = w.length
  | [] => rfl
  | .even :: w => by
      have ih := evenCount_add_oddCount w
      simp [List.length_cons]
      omega
  | .odd :: w => by
      have ih := evenCount_add_oddCount w
      simp [List.length_cons]
      omega

theorem oddCount_eq_length_sub_evenCount (w : List Branch) :
    oddCount w = w.length - evenCount w := by
  have := evenCount_add_oddCount w
  omega

theorem eq_replicate_odd_of_evenCount_zero {w : List Branch}
    (h : evenCount w = 0) : w = List.replicate w.length Branch.odd := by
  induction w with
  | nil => simp
  | cons b rest ih =>
      cases b with
      | odd =>
          have hrest : evenCount rest = 0 := by simpa using h
          simpa [List.replicate_succ] using
            congrArg (List.cons Branch.odd) (ih hrest)
      | even =>
          simp at h

theorem evenCount_rotateItinerary : ∀ (w : List Branch) (k : ℕ),
    evenCount (rotateItinerary w k) = evenCount w
  | _w, 0 => rfl
  | [], _k + 1 => rfl
  | b :: rest, k + 1 => by
      have ih := evenCount_rotateItinerary (rest ++ [b]) k
      have hswap : evenCount (rest ++ [b]) = evenCount (b :: rest) := by
        cases b <;> simp [evenCount_append]
      simpa [rotateItinerary, hswap] using ih

theorem exists_first_even {w : List Branch} (h : 1 ≤ evenCount w) :
    ∃ a v, w = List.replicate a Branch.odd ++ Branch.even :: v := by
  induction w with
  | nil => simp [evenCount] at h
  | cons b rest ih =>
      cases b with
      | even => exact ⟨0, rest, by simp⟩
      | odd =>
          have hrest : 1 ≤ evenCount rest := by simpa [evenCount] using h
          obtain ⟨a, v, hv⟩ := ih hrest
          exact ⟨a + 1, v, by simp [List.replicate_succ, hv]⟩

theorem getLast?_append_cons {α : Type*} (u : List α) (b : α) (v : List α) :
    (u ++ b :: v).getLast? = (b :: v).getLast? := by
  induction u with
  | nil => simp
  | cons x xs ih =>
      have hne : xs ++ b :: v ≠ [] := by
        cases xs <;> simp
      simpa [List.cons_append, List.getLast?_cons_of_ne_nil
        (List.append_ne_nil_of_right_ne_nil xs (List.cons_ne_nil b v))] using ih

theorem cycleMin_starts_two_odds {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ rest, w = Branch.odd :: Branch.odd :: rest := by
  match w with
  | [] =>
      exact (Nat.not_succ_le_zero 0 h.1.2.2).elim
  | .even :: rest =>
      exact (cycleMin_not_start_even hn h).elim
  | .odd :: rest =>
      match rest with
      | [] =>
          exact (cycleMin_not_end_odd (u := []) hn (by simpa using h)).elim
      | .even :: rest' =>
          exact (cycleMin_not_odd_even hn h).elim
      | .odd :: rest' =>
          exact ⟨rest', rfl⟩

theorem cycleMin_getLast_even {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    w.getLast? = some Branch.even := by
  have hwne : w ≠ [] := List.ne_nil_of_length_pos h.1.2.2
  rw [← List.dropLast_append_getLast hwne] at h
  cases hlast : w.getLast hwne with
  | odd =>
      exact (cycleMin_not_end_odd hn (by simpa [hlast] using h)).elim
  | even =>
      rw [List.getLast?_eq_some_getLast hwne, hlast]

theorem cycleMin_ge_twelve {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : 12 ≤ n :=
  cycleItinerary_iterate_not_lt_twelve (i := 0) hn h.1

theorem expanding_two_even_ee {a : ℕ} (h : 2 ^ (a + 2) < 3 ^ a) : 4 ≤ a := by
  by_contra hlt
  have : a ≤ 3 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  interval_cases a <;> exact absurd h (by decide)

theorem expanding_two_even_eoe {a : ℕ} (h : 2 ^ (a + 3) < 3 ^ (a + 1)) : 3 ≤ a := by
  by_contra hlt
  have : a ≤ 2 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  interval_cases a <;> exact absurd h (by decide)

theorem expanding_eee {a : ℕ} (h : 2 ^ (a + 3) < 3 ^ a) : 6 ≤ a := by
  by_contra hlt
  have : a ≤ 5 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  interval_cases a <;> exact absurd h (by decide)

theorem expanding_eoee {a : ℕ} (h : 2 ^ (a + 4) < 3 ^ (a + 1)) : 5 ≤ a := by
  by_contra hlt
  have : a ≤ 4 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  interval_cases a <;> exact absurd h (by decide)

theorem expanding_eooee {a : ℕ} (h : 2 ^ (a + 5) < 3 ^ (a + 2)) : 4 ≤ a := by
  by_contra hlt
  have : a ≤ 3 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  interval_cases a <;> exact absurd h (by decide)

theorem expanding_eoooee {a : ℕ} (h : 2 ^ (a + 6) < 3 ^ (a + 3)) : 3 ≤ a := by
  by_contra hlt
  have : a ≤ 2 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  interval_cases a <;> exact absurd h (by decide)

theorem two_pow_lt_three_pow_sub_four {k : ℕ}
    (hk : 4 ≤ k) (h : 2 ^ k < 3 ^ (k - 4)) : 11 ≤ k := by
  by_contra hlt
  have : k ≤ 10 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  revert h
  interval_cases k <;> decide

theorem two_odds_of_odd_even_split {a : ℕ} {tail rest : List Branch}
    (h : List.replicate a Branch.odd ++ Branch.even :: tail =
      Branch.odd :: Branch.odd :: rest) : 2 ≤ a := by
  match a with
  | 0 => simp at h
  | 1 => simp [List.replicate_succ] at h
  | _a + 2 => omega

theorem replicate_odd_getLast? {k : ℕ} (hk : 1 ≤ k) :
    (List.replicate k Branch.odd).getLast? = some Branch.odd := by
  cases k with
  | zero => omega
  | succ k =>
      simp [List.getLast?_replicate]

theorem no_cycleMin_odd_run {n a : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a)
    (h : CycleMin n (List.replicate a Branch.odd ++ [Branch.even])) : False := by
  have hC : CycleItinerary n (List.replicate a Branch.odd ++ [Branch.even]) := h.1
  cases lt_or_ge a 3 with
  | inr ha3 =>
      exact no_cycle_odd_run_append_even ha3 hn hC
  | inl ha2 =>
      have : a = 2 := by omega
      subst this
      exact no_cycle_itinerary_ooe hn (by simpa [itineraryOOE] using hC)

theorem no_cycleMin_bootstrap_last_gap {n : ℕ} {u : List Branch} {c : ℕ}
    (hn : 2 ≤ n) (hc : 2 ≤ c)
    (h : CycleMin n
      (u ++ [Branch.even] ++ List.replicate c Branch.odd ++ [Branch.even])) :
    False := by
  have hn12 : 12 ≤ n := cycleMin_ge_twelve hn h
  have hn5 : 5 ≤ n := le_trans (by decide : (5 : ℕ) ≤ 12) hn12
  cases lt_or_ge c 3 with
  | inl hc2 =>
      have : c = 2 := by omega
      subst this
      refine no_cycleMin_internal_even_threshold (N := 5) ?_ hn5 h
      intro m hm hf
      have hlist : List.replicate 2 Branch.odd = [Branch.odd, Branch.odd] := rfl
      rw [hlist] at hf ⊢
      simpa [image_eq_iterate] using oo_suffix_threshold hm hf
  | inr hc3 =>
      exact no_cycleMin_internal_even_threshold
        (odd_run_suffix_threshold hc3)
        (le_trans (by decide : (3 : ℕ) ≤ 5) hn5) h

/-- Trailing odd-run of any itinerary: the prefix is empty or ends even. -/
theorem exists_trailing_odds :
    ∀ w : List Branch,
      ∃ u a, w = u ++ List.replicate a Branch.odd ∧
        (u = [] ∨ u.getLast? = some Branch.even)
  | [] => ⟨[], 0, by simp, Or.inl rfl⟩
  | b :: rest => by
      obtain ⟨u, a, hsplit, hcut⟩ := exists_trailing_odds rest
      cases u with
      | nil =>
          have hrest : rest = List.replicate a Branch.odd := by
            simpa using hsplit
          cases b with
          | odd =>
              refine ⟨[], a + 1, ?_, Or.inl rfl⟩
              simp [List.replicate_succ, hrest]
          | even =>
              refine ⟨[Branch.even], a, ?_, Or.inr (by simp)⟩
              simp [hrest]
      | cons x xs =>
          refine ⟨b :: x :: xs, a, ?_, ?_⟩
          · simp [hsplit]
          · have hx : (x :: xs).getLast? = some Branch.even := by
              simpa using hcut
            have hne : x :: xs ≠ [] := List.cons_ne_nil x xs
            simpa [List.getLast?_cons_of_ne_nil hne] using hx

/-- A CycleMin itinerary cannot end `O^a E` for `a ≥ 2`. This is
`no_cycleMin_odd_run` when the prefix is empty and
`no_cycleMin_bootstrap_last_gap` after an internal even. -/
theorem cycleMin_not_last_odd_run_ge_two {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 2 ≤ a)
    (h : CycleMin n (u ++ List.replicate a Branch.odd ++ [Branch.even]))
    (hcut : u = [] ∨ u.getLast? = some Branch.even) : False := by
  rcases hcut with hu | hu
  · subst hu
    simpa using no_cycleMin_odd_run hn ha h
  · obtain ⟨u0, rfl⟩ := (List.getLast?_eq_some_iff).mp hu
    exact no_cycleMin_bootstrap_last_gap hn ha (by
      simpa [List.append_assoc] using h)

/-- On a CycleMin itinerary ending `O^a E` with `a ≥ 1` and the preceding
letter not odd, the last odd-run has length exactly one. Paper A §3
writes that last excursion as unconstrained `O^{a_e}E`; this is the
`OOEOOE` sandwich of Theorem 3.6 at an arbitrary last valley. -/
theorem cycleMin_last_odd_run_eq_one {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 1 ≤ a)
    (h : CycleMin n (u ++ List.replicate a Branch.odd ++ [Branch.even]))
    (hcut : u = [] ∨ u.getLast? = some Branch.even) :
    a = 1 := by
  by_contra hne
  exact cycleMin_not_last_odd_run_ge_two hn (by omega) h hcut

/-- Every CycleMin itinerary ends `O^a E` with `a ≤ 1`. The case `a = 0`
is a trailing even run of length at least two. -/
theorem exists_cycleMin_last_odd_run {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ u a, w = u ++ List.replicate a Branch.odd ++ [Branch.even] ∧
      a ≤ 1 ∧ (u = [] ∨ u.getLast? = some Branch.even) := by
  have hlast := cycleMin_getLast_even hn h
  obtain ⟨pref, hpref⟩ := (List.getLast?_eq_some_iff).mp hlast
  obtain ⟨u, a, hsplit, hcut⟩ := exists_trailing_odds pref
  refine ⟨u, a, ?_, ?_, hcut⟩
  · simp [hpref, hsplit]
  · cases lt_or_ge a 2 with
    | inl hlt => omega
    | inr hge =>
        exact (cycleMin_not_last_odd_run_ge_two hn hge
          (by simpa [hpref, hsplit] using h) hcut).elim

theorem eq_two_even_form {w : List Branch}
    (h2 : evenCount w = 2) (hend : w.getLast? = some Branch.even) :
    ∃ a c, w =
      List.replicate a Branch.odd ++ [.even] ++
        List.replicate c Branch.odd ++ [.even] := by
  have hpos : 1 ≤ evenCount w := by omega
  obtain ⟨a, v, rfl⟩ := exists_first_even hpos
  have hv1 : evenCount v = 1 := by
    have : evenCount (List.replicate a Branch.odd ++ .even :: v) =
        evenCount v + 1 := by
      simp [evenCount_append, evenCount_replicate_odd]
    omega
  obtain ⟨c, t, rfl⟩ := exists_first_even (by omega : 1 ≤ evenCount v)
  have ht0 : evenCount t = 0 := by
    have : evenCount (List.replicate c Branch.odd ++ .even :: t) =
        evenCount t + 1 := by
      simp [evenCount_append, evenCount_replicate_odd]
    omega
  have ht : t = List.replicate t.length Branch.odd :=
    eq_replicate_odd_of_evenCount_zero ht0
  cases t with
  | nil =>
      exact ⟨a, c, by simp [List.append_assoc]⟩
  | cons b rest =>
      have hoddlast :
          (List.replicate a Branch.odd ++ Branch.even ::
              (List.replicate c Branch.odd ++ Branch.even :: b :: rest)).getLast? =
            some Branch.odd := by
        have hne :
            List.replicate c Branch.odd ++ Branch.even :: (b :: rest) ≠ [] :=
          List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
        rw [getLast?_append_cons, List.getLast?_cons_of_ne_nil hne,
          getLast?_append_cons, ht]
        exact replicate_odd_getLast? (Nat.succ_le_of_lt (Nat.succ_pos _))
      cases hend.symm.trans hoddlast

theorem eq_three_even_form {w : List Branch}
    (h3 : evenCount w = 3) (hend : w.getLast? = some Branch.even) :
    ∃ a b c, w =
      List.replicate a Branch.odd ++ [.even] ++
        List.replicate b Branch.odd ++ [.even] ++
          List.replicate c Branch.odd ++ [.even] := by
  have hpos : 1 ≤ evenCount w := by omega
  obtain ⟨a, v, rfl⟩ := exists_first_even hpos
  have hv2 : evenCount v = 2 := by
    have : evenCount (List.replicate a Branch.odd ++ .even :: v) =
        evenCount v + 1 := by
      simp [evenCount_append, evenCount_replicate_odd]
    omega
  have hendv : v.getLast? = some Branch.even := by
    have hvne : v ≠ [] := by
      intro hv
      subst hv
      simp [evenCount] at hv2
    rw [getLast?_append_cons, List.getLast?_cons_of_ne_nil hvne] at hend
    exact hend
  obtain ⟨b, c, hv⟩ := eq_two_even_form hv2 hendv
  exact ⟨a, b, c, by simp [hv, List.append_assoc]⟩

theorem no_cycleMin_two_even {n a c : ℕ} (hn : 2 ≤ n) (_ha : 2 ≤ a)
    (h : CycleMin n
      (List.replicate a Branch.odd ++ [.even] ++
        List.replicate c Branch.odd ++ [.even])) : False := by
  have hC : CycleItinerary n
      (List.replicate a Branch.odd ++ [.even] ++
        List.replicate c Branch.odd ++ [.even]) := h.1
  have hexp := cycle_itinerary_formally_expanding hn hC
  have hodd : oddCount
      (List.replicate a Branch.odd ++ [.even] ++
        List.replicate c Branch.odd ++ [.even]) = a + c := by
    simp [oddCount_append, oddCount_replicate_odd]
  have hlen :
      (List.replicate a Branch.odd ++ [Branch.even] ++
        List.replicate c Branch.odd ++ [Branch.even]).length = a + c + 2 := by
    simp [List.length_append]
    omega
  rw [hodd, hlen] at hexp
  cases lt_or_ge c 2 with
  | inr hc =>
      exact no_cycleMin_bootstrap_last_gap hn hc h
  | inl hc =>
      interval_cases c
      · have ha4 : 4 ≤ a := expanding_two_even_ee (by simpa using hexp)
        have hk : 6 ≤ a + 2 := by omega
        have hform :
            List.replicate a Branch.odd ++ [.even] ++
              List.replicate 0 Branch.odd ++ [.even] =
              List.replicate (a + 2 - 2) Branch.odd ++
                List.replicate 2 Branch.even := by
          simp
        exact no_cycle_itinerary_two_even_ee hn hk (by simpa [hform] using hC)
      · have ha3 : 3 ≤ a := expanding_two_even_eoe (by simpa using hexp)
        have hk : 6 ≤ a + 3 := by omega
        have hform :
            List.replicate a Branch.odd ++ [.even] ++
              List.replicate 1 Branch.odd ++ [.even] =
              List.replicate (a + 3 - 3) Branch.odd ++
                [Branch.even, Branch.odd, Branch.even] := by
          simp [List.replicate_succ]
        exact no_cycle_itinerary_two_even_eoe hn hk (by simpa [hform] using hC)

theorem no_cycleMin_three_even {n a b c : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a)
    (h : CycleMin n
      (List.replicate a Branch.odd ++ [.even] ++
        List.replicate b Branch.odd ++ [.even] ++
          List.replicate c Branch.odd ++ [.even])) : False := by
  have hC : CycleItinerary n
      (List.replicate a Branch.odd ++ [.even] ++
        List.replicate b Branch.odd ++ [.even] ++
          List.replicate c Branch.odd ++ [.even]) := h.1
  have hexp := cycle_itinerary_formally_expanding hn hC
  have hodd : oddCount
      (List.replicate a Branch.odd ++ [.even] ++
        List.replicate b Branch.odd ++ [.even] ++
          List.replicate c Branch.odd ++ [.even]) = a + b + c := by
    simp [oddCount_append, oddCount_replicate_odd]
    omega
  have hlen :
      (List.replicate a Branch.odd ++ [Branch.even] ++
        List.replicate b Branch.odd ++ [Branch.even] ++
          List.replicate c Branch.odd ++ [Branch.even]).length =
        a + b + c + 3 := by
    simp [List.length_append]
    omega
  rw [hodd, hlen] at hexp
  cases lt_or_ge c 2 with
  | inr hc =>
      exact no_cycleMin_bootstrap_last_gap (u :=
        List.replicate a Branch.odd ++ [.even] ++ List.replicate b Branch.odd)
        hn hc (by simpa [List.append_assoc] using h)
  | inl hc =>
      interval_cases c
      · cases lt_or_ge b 4 with
        | inr hb =>
            exact no_cycle_itinerary_gapped_three_even_ee hn ha hb
              (by
                have hform :
                    List.replicate a Branch.odd ++ [Branch.even] ++
                      List.replicate b Branch.odd ++ [Branch.even] ++
                        List.replicate 0 Branch.odd ++ [Branch.even] =
                      gappedThreeEvenEE a b := by
                  simp [gappedThreeEvenEE, firstEPrefix, List.replicate_zero,
                    List.append_nil, List.append_assoc]
                exact hform ▸ hC)
        | inl hb =>
            interval_cases b
            · have ha6 : 6 ≤ a := expanding_eee (by simpa using hexp)
              exact no_cycle_itinerary_three_even_eee hn ha6
                (by
                  have hform :
                      List.replicate a Branch.odd ++ [.even] ++
                        List.replicate 0 Branch.odd ++ [.even] ++
                          List.replicate 0 Branch.odd ++ [.even] =
                        threeEvenEEE a := by
                    simp [threeEvenEEE, List.replicate_succ]
                  simpa [hform] using hC)
            · have ha5 : 5 ≤ a := expanding_eoee (by simpa using hexp)
              exact no_cycle_itinerary_three_even_eoee hn ha5
                (by
                  have hform :
                      List.replicate a Branch.odd ++ [.even] ++
                        List.replicate 1 Branch.odd ++ [.even] ++
                          List.replicate 0 Branch.odd ++ [.even] =
                        threeEvenEOEE a := by
                    simp [threeEvenEOEE, List.replicate_succ]
                  simpa [hform] using hC)
            · have ha4 : 4 ≤ a := expanding_eooee (by simpa using hexp)
              exact no_cycle_itinerary_three_even_eooee hn ha4
                (by
                  have hform :
                      List.replicate a Branch.odd ++ [.even] ++
                        List.replicate 2 Branch.odd ++ [.even] ++
                          List.replicate 0 Branch.odd ++ [.even] =
                        threeEvenEOOEE a := by
                    simp [threeEvenEOOEE, List.replicate_succ]
                  simpa [hform] using hC)
            · have ha3 : 3 ≤ a := expanding_eoooee (by simpa using hexp)
              exact no_cycle_itinerary_three_even_eoooee hn ha3
                (by
                  have hform :
                      List.replicate a Branch.odd ++ [.even] ++
                        List.replicate 3 Branch.odd ++ [.even] ++
                          List.replicate 0 Branch.odd ++ [.even] =
                        threeEvenEOOOEE a := by
                    simp [threeEvenEOOOEE, List.replicate_succ]
                  simpa [hform] using hC)
      · cases lt_or_ge b 3 with
        | inr hb =>
            exact no_cycle_itinerary_gapped_three_even_eoe hn ha hb
              (by
                have hform :
                    List.replicate a Branch.odd ++ [Branch.even] ++
                      List.replicate b Branch.odd ++ [Branch.even] ++
                        List.replicate 1 Branch.odd ++ [Branch.even] =
                      gappedThreeEvenEOE a b := by
                  simp [gappedThreeEvenEOE, firstEPrefix, List.replicate_succ,
                    List.append_assoc]
                exact hform ▸ hC)
        | inl hb =>
            interval_cases b
            · have ha5 : 5 ≤ a := expanding_eoee (by simpa using hexp)
              exact no_cycle_itinerary_three_even_eeoe hn ha5
                (by
                  have hform :
                      List.replicate a Branch.odd ++ [.even] ++
                        List.replicate 0 Branch.odd ++ [.even] ++
                          List.replicate 1 Branch.odd ++ [.even] =
                        threeEvenEEOE a := by
                    simp [threeEvenEEOE, List.replicate_succ]
                  simpa [hform] using hC)
            · have ha4 : 4 ≤ a := expanding_eooee (by simpa using hexp)
              exact no_cycle_itinerary_three_even_eoeoe hn ha4
                (by
                  have hform :
                      List.replicate a Branch.odd ++ [.even] ++
                        List.replicate 1 Branch.odd ++ [.even] ++
                          List.replicate 1 Branch.odd ++ [.even] =
                        threeEvenEOEOE a := by
                    simp [threeEvenEOEOE, List.replicate_succ]
                  simpa [hform] using hC)
            · have ha3 : 3 ≤ a := expanding_eoooee (by simpa using hexp)
              exact no_cycle_itinerary_three_even_eooeoe hn ha3
                (by
                  have hform :
                      List.replicate a Branch.odd ++ [.even] ++
                        List.replicate 2 Branch.odd ++ [.even] ++
                          List.replicate 1 Branch.odd ++ [.even] =
                        threeEvenEOOEOE a := by
                    simp [threeEvenEOOEOE, List.replicate_succ]
                  simpa [hform] using hC)

theorem no_cycleMin_even_count_le_three {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) (he : evenCount w ≤ 3) : False := by
  obtain ⟨rest, hw⟩ := cycleMin_starts_two_odds hn h
  have hend := cycleMin_getLast_even hn h
  have hpos : 1 ≤ evenCount w := by
    by_contra hz
    have h0 : evenCount w = 0 := by omega
    have hrep := eq_replicate_odd_of_evenCount_zero h0
    have hlast : w.getLast? = some Branch.odd := by
      rw [hrep]
      exact replicate_odd_getLast? h.1.2.2
    simp [hend] at hlast
  match heq : evenCount w with
  | 0 => omega
  | 1 =>
      obtain ⟨a, v, hv⟩ := exists_first_even (by omega : 1 ≤ evenCount w)
      have hv0 : evenCount v = 0 := by
        have : evenCount (List.replicate a Branch.odd ++ .even :: v) =
            evenCount v + 1 := by
          simp [evenCount_append, evenCount_replicate_odd]
        rw [← hv, heq] at this
        omega
      have : v = [] := by
        cases v with
        | nil => rfl
        | cons b t =>
            have ht := eq_replicate_odd_of_evenCount_zero hv0
            have hlast : w.getLast? = some Branch.odd := by
              have : 1 ≤ (b :: t).length := by simp
              rw [hv, getLast?_append_cons, ht]
              exact replicate_odd_getLast? this
            simp [hend] at hlast
      subst this
      have ha2 : 2 ≤ a :=
        two_odds_of_odd_even_split (tail := []) (by
          simpa using hv.symm.trans hw)
      exact no_cycleMin_odd_run hn ha2 (by simpa [hv] using h)
  | 2 =>
      obtain ⟨a, c, hv⟩ := eq_two_even_form heq hend
      have ha2 : 2 ≤ a :=
        two_odds_of_odd_even_split
          (tail := List.replicate c Branch.odd ++ [Branch.even])
          (by simpa [List.append_assoc] using hv.symm.trans hw)
      exact no_cycleMin_two_even hn ha2 (by simpa [hv] using h)
  | 3 =>
      obtain ⟨a, b, c, hv⟩ := eq_three_even_form heq hend
      have ha2 : 2 ≤ a :=
        two_odds_of_odd_even_split
          (tail :=
            List.replicate b Branch.odd ++ [Branch.even] ++
              List.replicate c Branch.odd ++ [Branch.even])
          (by simpa [List.append_assoc] using hv.symm.trans hw)
      exact no_cycleMin_three_even hn ha2 (by simpa [hv] using h)
  | _n + 4 =>
      omega

/-- **Even-count assembler.** No `n ≥ 2` realizes a cycle itinerary with
at most three even letters. This is not a length census and not a
halt theorem. -/
theorem no_cycle_itinerary_even_count_le_three {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) (he : evenCount w ≤ 3) : False := by
  obtain ⟨k, hk, hm⟩ := exists_cycleMin hn h
  have hnk : 2 ≤ floorPower^[k] n := cycleItinerary_iterate_ge_two hn h hk
  have he' : evenCount (rotateItinerary w k) ≤ 3 := by
    simpa [evenCount_rotateItinerary] using he
  exact no_cycleMin_even_count_le_three hnk hm he'

theorem cycle_itinerary_even_count_ge_four {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : 4 ≤ evenCount w := by
  by_contra hlt
  exact no_cycle_itinerary_even_count_le_three hn h (Nat.le_of_lt_succ (Nat.lt_of_not_ge hlt))

/-- A nontrivial cycle itinerary has length at least eleven: four evens
plus the expansion demand \(2^{|w|}<3^{\#O}\). -/
theorem cycle_itinerary_length_ge_eleven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : 11 ≤ w.length := by
  have he : 4 ≤ evenCount w := cycle_itinerary_even_count_ge_four hn h
  have hexp := cycle_itinerary_formally_expanding hn h
  have hsum := evenCount_add_oddCount w
  have hodd : oddCount w = w.length - evenCount w := by omega
  have hk4 : 4 ≤ w.length := by
    have := Nat.le_add_right (evenCount w) (oddCount w)
    rw [hsum] at this
    exact le_trans he this
  have hpow : 2 ^ w.length < 3 ^ (w.length - evenCount w) := by
    simpa [hodd] using hexp
  have hle : w.length - evenCount w ≤ w.length - 4 :=
    Nat.sub_le_sub_left he w.length
  have hbound : 3 ^ (w.length - evenCount w) ≤ 3 ^ (w.length - 4) :=
    Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 3) hle
  have hbound' : 2 ^ w.length < 3 ^ (w.length - 4) :=
    lt_of_lt_of_le hpow hbound
  exact two_pow_lt_three_pow_sub_four hk4 hbound'

theorem evenCount_oddEvenBlock (a b : ℕ) :
    evenCount (oddEvenBlock a b) = b := by
  simp [oddEvenBlock, evenCount_append, evenCount_replicate_odd,
    evenCount_replicate_even]

theorem oddEvenBlock_length (a b : ℕ) :
    (oddEvenBlock a b).length = a + b :=
  length_oddEvenBlock a b

/-- Return on the first `O^a E` is an even-count-1 cycle itinerary. -/
theorem no_cycle_itinerary_oddEvenBlock_one {n a : ℕ} (hn : 2 ≤ n)
    (h : CycleItinerary n (oddEvenBlock a 1)) : False :=
  no_cycle_itinerary_even_count_le_three hn h (by simp [evenCount_oddEvenBlock])

/-- On a `MinimalNonTerm` start the first even residual always
overshoots. The return cell is an even-count-1 cycle itinerary. This is
not a halt theorem. -/
theorem minimal_first_even_overshoots {n a : ℕ}
    (h : MinimalNonTerm n) (hw : follows n (oddEvenBlock a 1)) :
    (n + 1) ^ 2 ≤ image n (List.replicate a Branch.odd) ∧
      n < image n (oddEvenBlock a 1) := by
  rcases minimal_first_even_dichotomy h hw with hret | hover
  · have hn2 : 2 ≤ n :=
      le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
    have hlen : 1 ≤ (oddEvenBlock a 1).length := by
      simp [oddEvenBlock_length]
    exact (no_cycle_itinerary_oddEvenBlock_one hn2 ⟨hw, hret.1, hlen⟩).elim
  · exact hover

theorem cycleMin_oddEvenBlock_starts_two_odds {n a : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n (oddEvenBlock a 1 ++ v)) : 2 ≤ a := by
  obtain ⟨rest, hrest⟩ := cycleMin_starts_two_odds hn h
  refine two_odds_of_odd_even_split (tail := v) (rest := rest) ?_
  have : List.replicate a Branch.odd ++ Branch.even :: v =
      oddEvenBlock a 1 ++ v := by
    simp [oddEvenBlock]
  exact this.trans hrest

/-- On a `CycleMin` the first even residual overshoots. Return would
be an even-count-1 cycle itinerary. -/
theorem cycleMin_first_even_overshoots {n a : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n (oddEvenBlock a 1 ++ v)) :
    (n + 1) ^ 2 ≤ image n (List.replicate a Branch.odd) ∧
      n < image n (oddEvenBlock a 1) := by
  have ha2 : 2 ≤ a := cycleMin_oddEvenBlock_starts_two_odds hn h
  have hw : follows n (oddEvenBlock a 1) :=
    follows_of_append_left h.1.1
  cases v with
  | nil =>
      exact (no_cycleMin_odd_run hn ha2 (by simpa [oddEvenBlock] using h)).elim
  | cons b t =>
      have hj : a + 1 < (oddEvenBlock a 1 ++ b :: t).length := by
        simp [oddEvenBlock_length]
      have hy : n ≤ image n (oddEvenBlock a 1) := by
        have := cycleMin_ge (j := a + 1) h (by simpa using hj)
        simpa [image_oddEvenBlock_iterate] using this
      have hz := odd_run_even_residual hw
      have himg : image n (oddEvenBlock a 1) =
          floorPower (image n (List.replicate a Branch.odd)) := by
        simp [image_oddEvenBlock, image]
      rcases le_iff_eq_or_lt.mp hy with heq | hlt
      · have hlen : 1 ≤ (oddEvenBlock a 1).length := by
          simp [oddEvenBlock_length]
        exact (no_cycle_itinerary_oddEvenBlock_one hn ⟨hw, heq.symm, hlen⟩).elim
      · refine ⟨?_, hlt⟩
        have : n < floorPower (image n (List.replicate a Branch.odd)) := by
          simpa [himg] using hlt
        exact (even_floorPower_gt_iff hz).mp this

theorem evenCount_pos_of_getLast_even {w : List Branch}
    (h : w.getLast? = some Branch.even) : 1 ≤ evenCount w := by
  induction w with
  | nil => simp at h
  | cons b rest ih =>
      cases rest with
      | nil =>
          cases b with
          | even => simp [evenCount]
          | odd => simp [List.getLast?] at h
      | cons c t =>
          have hrest : (c :: t).getLast? = some Branch.even := by
            simpa [List.getLast?] using h
          have ih' := ih hrest
          cases b with
          | even => simp [evenCount]
          | odd => simpa [evenCount] using ih'

theorem cycleMin_evenCount_pos {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : 1 ≤ evenCount w :=
  evenCount_pos_of_getLast_even (cycleMin_getLast_even hn h)

/-- Every `CycleMin` itinerary is a first-even block plus a nonempty tail. -/
theorem cycleMin_exists_oddEven_split {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ a v, w = oddEvenBlock a 1 ++ v := by
  obtain ⟨a, v, hw⟩ := exists_first_even (cycleMin_evenCount_pos hn h)
  refine ⟨a, v, ?_⟩
  simp [oddEvenBlock, hw]

/-- On a cycle minimum the maximum sits at or above `(n+1)^2`. The
first even residual already overshoots, so the first-cell family
`n^2 < M < (n+1)^2` is impossible. Not a halt theorem. -/
theorem cycleMin_max_ge_succ_sq {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ i < w.length,
      (∀ j < w.length, floorPower^[j] n ≤ floorPower^[i] n) ∧
        floorPower^[i] n % 2 = 0 ∧
          (n + 1) ^ 2 ≤ floorPower^[i] n := by
  obtain ⟨a, v, hw⟩ := cycleMin_exists_oddEven_split hn h
  have hover := cycleMin_first_even_overshoots hn (by simpa [hw] using h)
  have ⟨i, hi, hmax, heven⟩ := exists_cycle_max_even hn h.1
  refine ⟨i, hi, hmax, heven, ?_⟩
  have ha : a < w.length := by
    rw [hw, List.length_append, oddEvenBlock_length]
    omega
  have hz : (n + 1) ^ 2 ≤ floorPower^[a] n := by
    simpa [image_odd_run] using hover.1
  exact hz.trans (hmax a ha)

theorem cycleMin_max_not_first_preimage {n : ℕ} {w : List Branch}
    {i : ℕ} (hn : 2 ≤ n) (h : CycleMin n w) (hi : i < w.length)
    (hmax : ∀ j < w.length, floorPower^[j] n ≤ floorPower^[i] n) :
    (n + 1) ^ 2 ≤ floorPower^[i] n := by
  obtain ⟨i0, hi0, hmax0, _, hge⟩ := cycleMin_max_ge_succ_sq hn h
  have heq : floorPower^[i] n = floorPower^[i0] n :=
    le_antisymm (hmax0 i hi) (hmax i0 hi0)
  simpa [heq] using hge

/-- On a cycle maximum the rotated minimum satisfies `(m+1)^2 ≤ M`. -/
theorem cycleMax_min_succ_sq_le {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (h : CycleMax n w) (hk : k < w.length)
    (hmin : CycleMin (floorPower^[k] n) (rotateItinerary w k)) :
    (floorPower^[k] n + 1) ^ 2 ≤ n := by
  have hk0 : k ≠ 0 := by
    intro hk0
    have : CycleMin n w := by
      simpa [hk0, rotateItinerary] using hmin
    exact cycleMax_not_cycleMin hn h this
  have hm2 : 2 ≤ floorPower^[k] n := cycleItinerary_iterate_ge_two hn h.1 hk
  have ⟨i, hi, hmax, _, hge⟩ :=
    cycleMin_max_ge_succ_sq (n := floorPower^[k] n) hm2 hmin
  have hlen : (rotateItinerary w k).length = w.length := rotateItinerary_length w k
  have hle : floorPower^[i] (floorPower^[k] n) ≤ n := by
    have himg : floorPower^[i] (floorPower^[k] n) = floorPower^[k + i] n := by
      simpa [Nat.add_comm] using
        (Function.iterate_add_apply floorPower i k n).symm
    simpa [himg] using cycleMax_iterate_le h (k + i)
  have hfrom : floorPower^[w.length - k] (floorPower^[k] n) = n := by
    have hsum : w.length - k + k = w.length := Nat.sub_add_cancel (Nat.le_of_lt hk)
    have hiter := Function.iterate_add_apply floorPower (w.length - k) k n
    rw [← hiter, hsum, cycle_iterate_period h.1]
  have hidx : w.length - k < (rotateItinerary w k).length := by
    rw [hlen]
    omega
  have hnle : n ≤ floorPower^[i] (floorPower^[k] n) := by
    simpa [hfrom] using hmax (w.length - k) hidx
  have heq : floorPower^[i] (floorPower^[k] n) = n := le_antisymm hle hnle
  simpa [heq] using hge

/-- The maximum cannot collapse to the minimum in one even step. -/
theorem cycleMax_landing_gt_min {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (h : CycleMax n w) (hk : k < w.length)
    (hmin : CycleMin (floorPower^[k] n) (rotateItinerary w k)) :
    floorPower^[k] n < floorPower n := by
  have he := cycleMax_start_even hn h
  exact (even_floorPower_gt_iff he).mpr (cycleMax_min_succ_sq_le hn h hk hmin)

theorem cycleMax_exists_min_succ_sq {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ k < w.length,
      CycleMin (floorPower^[k] n) (rotateItinerary w k) ∧
        (floorPower^[k] n + 1) ^ 2 ≤ n := by
  obtain ⟨k, hk, hmin⟩ := exists_cycleMin hn h.1
  exact ⟨k, hk, hmin, cycleMax_min_succ_sq_le hn h hk hmin⟩

/-- Laboratory sharpening of `cycle_distinguished_order`: first-even
overshoot replaces `m^2 < M` by `(m+1)^2 ≤ M`. -/
theorem cycle_distinguished_order_succ_sq {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ m p x r, 2 ≤ m ∧ 2 ≤ p ∧
      m % 2 = 1 ∧ p % 2 = 1 ∧
        m ≤ p ∧ p < x ∧ x < n ∧
          (m + 1) ^ 2 ≤ n ∧
            1 ≤ r ∧
              p ^ (2 ^ r) < n ∧ n < (p + 1) ^ (2 ^ r) ∧
                n ^ 2 ≤ x ^ 3 ∧ x ^ 3 < (n + 1) ^ 2 ∧
                  m ^ 4 < x ^ 3 := by
  obtain ⟨k, m, p, x, r, hk, hmin, hm_eq, hm, hp2, hmodd, hpodd, hmlep, hpx,
      hxn, _hMsq, hr1, hwin, hhi, hxlo, hxhi, hfourth⟩ :=
    cycle_distinguished_order hn h
  refine ⟨m, p, x, r, hm, hp2, hmodd, hpodd, hmlep, hpx, hxn, ?_, hr1, hwin,
    hhi, hxlo, hxhi, hfourth⟩
  simpa [hm_eq] using cycleMax_min_succ_sq_le hn h hk hmin

end Problems.Juggler
