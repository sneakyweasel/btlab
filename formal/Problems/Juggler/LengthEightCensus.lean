import Problems.Juggler.LeftoverFamilies
import Problems.Juggler.SmallCycleCensus

namespace Problems.Juggler

/-!
# Laboratory census: no cycle itinerary of length at most eight

Assembly of named filters already in Lean: the length-≤7 census,
the odd-run exclusion of `O^7E`, Theorem 3.12 at `k = 8`, rotation
of `EOOOOOOE` and `OEOOOOOE` onto those two-even leftovers, and the
internal-E bootstrap exclusions of `OOOOEOOE`, `OOOEOOOE`, and
`OOEOOOOE`.

This file is a laboratory strengthening of Paper A Theorem 3.8. It
is not imported by `Problems.JugglerPaper`. Not a halt theorem and
not an exclusion of length nine.
-/

def itineraryOOOOEOOE : List Branch :=
  [.odd, .odd, .odd, .odd, .even, .odd, .odd, .even]

def itineraryOOOEOOOE : List Branch :=
  [.odd, .odd, .odd, .even, .odd, .odd, .odd, .even]

def itineraryOOEOOOOE : List Branch :=
  [.odd, .odd, .even, .odd, .odd, .odd, .odd, .even]

theorem itineraryOOOOEOOE_split :
    itineraryOOOOEOOE =
      [.odd, .odd, .odd, .odd] ++ [.even] ++ [.odd, .odd] ++ [.even] :=
  rfl

theorem itineraryOOOEOOOE_split :
    itineraryOOOEOOOE =
      [.odd, .odd, .odd] ++ [.even] ++ [.odd, .odd, .odd] ++ [.even] :=
  rfl

theorem itineraryOOEOOOOE_split :
    itineraryOOEOOOOE =
      [.odd, .odd] ++ [.even] ++ [.odd, .odd, .odd, .odd] ++ [.even] :=
  rfl

theorem no_followsB_3_ooooeooe : followsB 3 itineraryOOOOEOOE = false := by
  native_decide

theorem no_follows_3_ooooeooe : ¬follows 3 itineraryOOOOEOOE := by
  intro hf
  have htrue : followsB 3 itineraryOOOOEOOE = true := (followsB_iff 3 _).mpr hf
  rw [no_followsB_3_ooooeooe] at htrue
  exact Bool.false_ne_true htrue

theorem no_cycleMin_ooooeooe {n : ℕ} (hn : 2 ≤ n)
    (h : CycleMin n itineraryOOOOEOOE) : False := by
  have hodd : n % 2 = 1 := h.1.1.1
  cases lt_or_ge n 5 with
  | inl hlt =>
      have hn3 : n = 3 := by omega
      subst hn3
      exact no_follows_3_ooooeooe h.1.1
  | inr hge =>
      have hsplit :
          CycleMin n
            ([.odd, .odd, .odd, .odd] ++ [.even] ++ [.odd, .odd] ++ [.even]) := by
        simpa [itineraryOOOOEOOE] using h
      refine no_cycleMin_internal_even_threshold (N := 5) ?_ hge hsplit
      intro m hm hf
      simpa [image_eq_iterate] using oo_suffix_threshold hm hf

theorem no_cycleMin_oooeoooe {n : ℕ} (hn : 2 ≤ n)
    (h : CycleMin n itineraryOOOEOOOE) : False := by
  have hn3 : 3 ≤ n := by
    have : n % 2 = 1 := h.1.1.1
    omega
  have hsplit :
      CycleMin n
        ([.odd, .odd, .odd] ++ [.even] ++ [.odd, .odd, .odd] ++ [.even]) := by
    simpa [itineraryOOOEOOOE] using h
  refine no_cycleMin_internal_even_threshold (N := 3) ?_ hn3 hsplit
  intro m hm hf
  simpa [image_eq_iterate] using ooo_suffix_threshold hm hf

theorem no_cycleMin_ooeooooe {n : ℕ} (hn : 2 ≤ n)
    (h : CycleMin n itineraryOOEOOOOE) : False := by
  have hn3 : 3 ≤ n := by
    have : n % 2 = 1 := h.1.1.1
    omega
  have hsplit :
      CycleMin n
        ([.odd, .odd] ++ [.even] ++ [.odd, .odd, .odd, .odd] ++ [.even]) := by
    simpa [itineraryOOEOOOOE] using h
  refine no_cycleMin_internal_even_threshold (N := 3) ?_ hn3 hsplit
  intro m hm hf
  simpa [image_eq_iterate] using
    odd_run_suffix_threshold (a := 4) (by decide : (3 : ℕ) ≤ 4) m hm hf

theorem rotate_ooooeooe :
    ∀ k, k < 8 →
      rotateItinerary itineraryOOOOEOOE k = itineraryOOOOEOOE ∨
        rotateItinerary itineraryOOOOEOOE k = itineraryOOEOOOOE ∨
          rotateItinerary itineraryOOOOEOOE k =
              [.odd, .odd, .odd, .even, .odd, .odd, .even, .odd] ∨
            rotateItinerary itineraryOOOOEOOE k =
                [.odd, .odd, .even, .odd, .odd, .even, .odd, .odd] ∨
              rotateItinerary itineraryOOOOEOOE k =
                  [.odd, .even, .odd, .odd, .even, .odd, .odd, .odd] ∨
                rotateItinerary itineraryOOOOEOOE k =
                    [.even, .odd, .odd, .even, .odd, .odd, .odd, .odd] ∨
                  rotateItinerary itineraryOOOOEOOE k =
                      [.odd, .even, .odd, .odd, .odd, .odd, .even, .odd] ∨
                    rotateItinerary itineraryOOOOEOOE k =
                      [.even, .odd, .odd, .odd, .odd, .even, .odd, .odd] := by
  intro k hk
  interval_cases k <;> simp [itineraryOOOOEOOE, itineraryOOEOOOOE, rotateItinerary]

theorem rotate_ooeooooe :
    ∀ k, k < 8 →
      rotateItinerary itineraryOOEOOOOE k = itineraryOOEOOOOE ∨
        rotateItinerary itineraryOOEOOOOE k = itineraryOOOOEOOE ∨
          rotateItinerary itineraryOOEOOOOE k =
              [.odd, .even, .odd, .odd, .odd, .odd, .even, .odd] ∨
            rotateItinerary itineraryOOEOOOOE k =
                [.even, .odd, .odd, .odd, .odd, .even, .odd, .odd] ∨
              rotateItinerary itineraryOOEOOOOE k =
                  [.odd, .odd, .odd, .even, .odd, .odd, .even, .odd] ∨
                rotateItinerary itineraryOOEOOOOE k =
                    [.odd, .odd, .even, .odd, .odd, .even, .odd, .odd] ∨
                  rotateItinerary itineraryOOEOOOOE k =
                      [.odd, .even, .odd, .odd, .even, .odd, .odd, .odd] ∨
                    rotateItinerary itineraryOOEOOOOE k =
                      [.even, .odd, .odd, .even, .odd, .odd, .odd, .odd] := by
  intro k hk
  interval_cases k <;> simp [itineraryOOEOOOOE, itineraryOOOOEOOE, rotateItinerary]

theorem rotate_oooeoooe :
    ∀ k, k < 8 →
      rotateItinerary itineraryOOOEOOOE k = itineraryOOOEOOOE ∨
        rotateItinerary itineraryOOOEOOOE k =
            [.odd, .odd, .even, .odd, .odd, .odd, .even, .odd] ∨
          rotateItinerary itineraryOOOEOOOE k =
              [.odd, .even, .odd, .odd, .odd, .even, .odd, .odd] ∨
            rotateItinerary itineraryOOOEOOOE k =
                [.even, .odd, .odd, .odd, .even, .odd, .odd, .odd] := by
  intro k hk
  interval_cases k <;> simp [itineraryOOOEOOOE, rotateItinerary]

theorem no_cycle_itinerary_ooooeooe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n itineraryOOOOEOOE := by
  intro h
  have ⟨k, hk, hm⟩ := exists_cycleMin hn h
  have hlen : itineraryOOOOEOOE.length = 8 := rfl
  rw [hlen] at hk
  have hnk : 2 ≤ floorPower^[k] n :=
    cycleItinerary_iterate_ge_two hn h (by omega)
  rcases rotate_ooooeooe k hk with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact no_cycleMin_ooooeooe hnk (by simpa [h0] using hm)
  · exact no_cycleMin_ooeooooe hnk (by simpa [h1] using hm)
  · have heq :
        [Branch.odd, Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd,
            Branch.even, Branch.odd] =
          [Branch.odd, Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd,
              Branch.even] ++ [Branch.odd] :=
      rfl
    rw [h2, heq] at hm
    exact cycleMin_not_end_odd hnk hm
  · have heq :
        [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd, Branch.even,
            Branch.odd, Branch.odd] =
          [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd, Branch.even,
              Branch.odd] ++ [Branch.odd] :=
      rfl
    rw [h3, heq] at hm
    exact cycleMin_not_end_odd hnk hm
  · exact cycleMin_not_odd_even hnk (by simpa [h4] using hm)
  · exact cycleMin_not_start_even hnk (by simpa [h5] using hm)
  · exact cycleMin_not_odd_even hnk (by simpa [h6] using hm)
  · exact cycleMin_not_start_even hnk (by simpa [h7] using hm)

theorem no_cycle_itinerary_ooeooooe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n itineraryOOEOOOOE := by
  intro h
  have ⟨k, hk, hm⟩ := exists_cycleMin hn h
  have hlen : itineraryOOEOOOOE.length = 8 := rfl
  rw [hlen] at hk
  have hnk : 2 ≤ floorPower^[k] n :=
    cycleItinerary_iterate_ge_two hn h (by omega)
  rcases rotate_ooeooooe k hk with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact no_cycleMin_ooeooooe hnk (by simpa [h0] using hm)
  · exact no_cycleMin_ooooeooe hnk (by simpa [h1] using hm)
  · exact cycleMin_not_odd_even hnk (by simpa [h2] using hm)
  · exact cycleMin_not_start_even hnk (by simpa [h3] using hm)
  · have heq :
        [Branch.odd, Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd,
            Branch.even, Branch.odd] =
          [Branch.odd, Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd,
              Branch.even] ++ [Branch.odd] :=
      rfl
    rw [h4, heq] at hm
    exact cycleMin_not_end_odd hnk hm
  · have heq :
        [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd, Branch.even,
            Branch.odd, Branch.odd] =
          [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd, Branch.even,
              Branch.odd] ++ [Branch.odd] :=
      rfl
    rw [h5, heq] at hm
    exact cycleMin_not_end_odd hnk hm
  · exact cycleMin_not_odd_even hnk (by simpa [h6] using hm)
  · exact cycleMin_not_start_even hnk (by simpa [h7] using hm)

theorem no_cycle_itinerary_oooeoooe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n itineraryOOOEOOOE := by
  intro h
  have ⟨k, hk, hm⟩ := exists_cycleMin hn h
  have hlen : itineraryOOOEOOOE.length = 8 := rfl
  rw [hlen] at hk
  have hnk : 2 ≤ floorPower^[k] n :=
    cycleItinerary_iterate_ge_two hn h (by omega)
  rcases rotate_oooeoooe k hk with h0 | h1 | h2 | h3
  · exact no_cycleMin_oooeoooe hnk (by simpa [h0] using hm)
  · have heq :
        [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd, Branch.odd,
            Branch.even, Branch.odd] =
          [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.odd, Branch.odd,
              Branch.even] ++ [Branch.odd] :=
      rfl
    rw [h1, heq] at hm
    exact cycleMin_not_end_odd hnk hm
  · exact cycleMin_not_odd_even hnk (by simpa [h2] using hm)
  · exact cycleMin_not_start_even hnk (by simpa [h3] using hm)

theorem no_cycle_itinerary_ooooooee {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n
      [.odd, .odd, .odd, .odd, .odd, .odd, .even, .even] := by
  simpa [twoEvenEE] using
    no_cycle_itinerary_two_even_ee (n := n) (k := 8) hn (by decide : (6 : ℕ) ≤ 8)

theorem no_cycle_itinerary_oooooeeoe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n
      [.odd, .odd, .odd, .odd, .odd, .even, .odd, .even] := by
  simpa [twoEvenEOE] using
    no_cycle_itinerary_two_even_eoe (n := n) (k := 8) hn (by decide : (6 : ℕ) ≤ 8)

/-- Every even-terminating length-eight cycle itinerary is impossible. The
expanding filter leaves eight candidates; odd-run, Theorem 3.12,
internal-E bootstrap, and rotation cover them. -/
theorem no_cycle_itinerary_len_eight_ends_even {m : ℕ} {v : List Branch}
    (hm : 2 ≤ m) (hv : v.length = 7) :
    ¬CycleItinerary m (v ++ [Branch.even]) := by
  intro h
  rcases v with _ | ⟨a, v⟩; · simp at hv
  rcases v with _ | ⟨b, v⟩; · simp at hv
  rcases v with _ | ⟨c, v⟩; · simp at hv
  rcases v with _ | ⟨d, v⟩; · simp at hv
  rcases v with _ | ⟨e, v⟩; · simp at hv
  rcases v with _ | ⟨f, v⟩; · simp at hv
  rcases v with _ | ⟨g, v⟩; · simp at hv
  rcases v with _ | ⟨hrest, v⟩
  swap
  · simp only [List.length_cons] at hv
    omega
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    cases g <;>
    first
      | exact absurd (cycle_itinerary_formally_expanding hm h) (by decide)
      | exact no_cycle_odd_run_append_even (a := 7)
          (by decide : (3 : ℕ) ≤ 7) hm h
      | exact no_cycle_itinerary_ooooeooe hm h
      | exact no_cycle_itinerary_oooeoooe hm h
      | exact no_cycle_itinerary_ooeooooe hm h
      | exact no_cycle_itinerary_ooooooee hm h
      | exact no_cycle_itinerary_oooooeeoe hm h
      | -- EOOOOOOE rotates once onto OOOOOOEE
        (have h1 : 2 ≤ floorPower m := by
          have := cycleItinerary_iterate_ge_two (i := 1) hm h (by decide)
          simpa using this
         exact no_cycle_itinerary_ooooooee h1 (cycleItinerary_rotate_cons h))
      | -- OEOOOOOE rotates twice onto OOOOOEOE
        (have h2 : 2 ≤ floorPower (floorPower m) := by
          have := cycleItinerary_iterate_ge_two (i := 2) hm h (by decide)
          simpa [Function.iterate_succ_apply'] using this
         exact no_cycle_itinerary_oooooeeoe h2
           (cycleItinerary_rotate_cons (cycleItinerary_rotate_cons h)))

/-- **Laboratory small-cycle census.** No `n ≥ 2` realizes a cycle
itinerary of length at most eight. Length nine and beyond is open. This
is not a halt theorem. -/
theorem no_cycle_itinerary_length_le_eight {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 8) : ¬CycleItinerary n w := by
  intro h
  have hne : 1 ≤ w.length := h.2.2
  rcases lt_or_eq_of_le (oddCount_le_length w) with hlt | heq
  · obtain ⟨m, v, hm, hv, hC⟩ := cycleItinerary_exists_even_terminating hn h hlt
    have hv7 : v.length ≤ 7 := by omega
    rcases v with _ | ⟨a, v⟩
    · exact absurd (cycle_itinerary_formally_expanding hm hC) (by decide)
    rcases v with _ | ⟨b, v⟩
    · cases a <;>
        exact absurd (cycle_itinerary_formally_expanding hm hC) (by decide)
    rcases v with _ | ⟨c, v⟩
    · cases a <;> cases b <;>
        first
          | exact absurd (cycle_itinerary_formally_expanding hm hC) (by decide)
          | exact no_cycle_itinerary_ooe hm hC
    rcases v with _ | ⟨d, v⟩
    · exact no_cycle_itinerary_length_four_ends_even hm (by simp) hC
    rcases v with _ | ⟨e, v⟩
    · exact no_cycle_itinerary_length_five_ends_even hm (by simp) hC
    rcases v with _ | ⟨f, v⟩
    · exact no_cycle_itinerary_len_six_ends_even hm (by simp) hC
    rcases v with _ | ⟨g, v⟩
    · exact no_cycle_itinerary_len_seven_ends_even hm (by simp) hC
    rcases v with _ | ⟨i, v⟩
    · exact no_cycle_itinerary_len_eight_ends_even hm (by simp) hC
    · exfalso
      simp only [List.length_cons] at hv7
      omega
  · have hrep := eq_replicate_odd_of_oddCount_eq_length heq
    rw [hrep] at h
    exact no_cycle_itinerary_replicate_odd hne hn h

end Problems.Juggler
