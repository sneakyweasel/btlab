import Problems.Juggler.CycleCore
import Problems.Juggler.CycleObstructions
import Problems.Juggler.LeftoverShort

namespace Problems.Juggler

/-!
# Small-cycle census: no cycle word of length at most seven

Assembly of existing certified exclusions, not a new engine. Rotation
moves any cycle word to an even-terminating orientation. The formal
expansion filter, the all-odd growth argument, the general length-four
and length-five even-terminating theorems, the odd-run threshold, and
the named exclusions of the length-six and length-seven leftovers then
cover every word of length at most seven.

This is a census for lengths `≤ 7` only. Length eight is open
in this assembly (Paper A Theorem 3.8). Paper A Theorem 3.22
assembles the leftover families as
`no_cycle_word_even_count_le_three`, so a nontrivial cycle has
period at least eleven. The dedicated length-eight assembler
remains `no_cycle_word_length_le_eight`. Not a halt theorem and
not an exclusion of all cycles.
-/

/-- On an all-odd realized word from an odd start `n ≥ 3`, the image
strictly exceeds the start. -/
theorem replicate_odd_image_gt :
    ∀ (a : ℕ) {n : ℕ}, 3 ≤ n → n % 2 = 1 →
      follows n (List.replicate (a + 1) Branch.odd) →
      n < image n (List.replicate (a + 1) Branch.odd)
  | 0, n, hn, hodd, _hf => by
      simpa [List.replicate_succ] using floorPower_odd_gt hn hodd
  | a + 1, n, hn, hodd, hf => by
      have hrep :
          List.replicate (a + 2) Branch.odd =
            Branch.odd :: List.replicate (a + 1) Branch.odd := by
        simp [List.replicate_succ]
      rw [hrep] at hf ⊢
      have hgt : n < floorPower n := floorPower_odd_gt hn hodd
      have hf' : follows (floorPower n) (List.replicate (a + 1) Branch.odd) :=
        hf.2
      have hodd' : floorPower n % 2 = 1 :=
        follows_replicate_odd_head (by omega) hf'
      have hn' : 3 ≤ floorPower n := by omega
      have ih := replicate_odd_image_gt a hn' hodd' hf'
      calc n < floorPower n := hgt
        _ < image (floorPower n) (List.replicate (a + 1) Branch.odd) := ih

/-- All-odd words are never cycle words for `n ≥ 2`: the odd branch
strictly ascends, so the trajectory cannot return. -/
theorem no_cycle_word_replicate_odd {a n : ℕ} (ha : 1 ≤ a) (hn : 2 ≤ n) :
    ¬CycleWord n (List.replicate a Branch.odd) := by
  intro h
  have hodd : n % 2 = 1 := follows_replicate_odd_head ha h.1
  have hn3 : 3 ≤ n := by omega
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hgt := replicate_odd_image_gt a' hn3 hodd h.1
  have himg := h.2.1
  omega

/-- A word with fewer odd letters than its length contains an even
letter at some index. -/
theorem exists_even_getElem_of_oddCount_lt :
    ∀ {w : List Branch}, oddCount w < w.length →
      ∃ i, ∃ _ : i < w.length, w[i] = Branch.even := by
  intro w
  induction w with
  | nil => intro h; simp at h
  | cons b rest ih =>
      intro h
      cases b with
      | even => exact ⟨0, by simp, rfl⟩
      | odd =>
          have hrest : oddCount rest < rest.length := by
            have : oddCount (Branch.odd :: rest) = oddCount rest + 1 := rfl
            simp [this] at h
            omega
          obtain ⟨i, hi, he⟩ := ih hrest
          exact ⟨i + 1, by simpa using Nat.succ_lt_succ hi, by simpa using he⟩

/-- Any cycle word with an even letter has an even-terminating rotation
based at a cycle state at least `2`. -/
theorem cycleWord_exists_even_terminating {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleWord n w) (hlt : oddCount w < w.length) :
    ∃ (m : ℕ) (v : List Branch), 2 ≤ m ∧ v.length + 1 = w.length ∧
      CycleWord m (v ++ [Branch.even]) := by
  obtain ⟨i, hi, he⟩ := exists_even_getElem_of_oddCount_lt hlt
  have hk : i + 1 ≤ w.length := hi
  have hrot := cycleWord_rotateWord h (i + 1)
  have htake : w.take (i + 1) = w.take i ++ [Branch.even] := by
    rw [List.take_add_one]
    simp [List.getElem?_eq_getElem hi, he]
  have hform : rotateWord w (i + 1) =
      (w.drop (i + 1) ++ w.take i) ++ [Branch.even] := by
    rw [rotateWord_eq_drop_append_take w (i + 1) hk, htake,
      ← List.append_assoc]
  have hm : 2 ≤ floorPower^[i + 1] n := by
    rcases lt_or_eq_of_le hk with hlt' | heq
    · exact cycleWord_iterate_ge_two hn h hlt'
    · rw [heq, cycle_iterate_period h]; exact hn
  refine ⟨floorPower^[i + 1] n, w.drop (i + 1) ++ w.take i, hm, ?_, ?_⟩
  · have hlen : (w.drop (i + 1) ++ w.take i).length =
        (w.length - (i + 1)) + i := by
      simp [List.length_append, List.length_drop, List.length_take]
      omega
    omega
  · rw [← hform]; exact hrot

/-- Every even-terminating length-six cycle word is impossible. The
expanding filter leaves six candidates; the odd-run threshold, the
internal-even threshold, and the two leftover exclusions cover four of
them, and the remaining two rotate onto excluded words. -/
theorem no_cycle_word_len_six_ends_even {m : ℕ} {v : List Branch}
    (hm : 2 ≤ m) (hv : v.length = 5) :
    ¬CycleWord m (v ++ [Branch.even]) := by
  intro h
  rcases v with _ | ⟨a, v⟩; · simp at hv
  rcases v with _ | ⟨b, v⟩; · simp at hv
  rcases v with _ | ⟨c, v⟩; · simp at hv
  rcases v with _ | ⟨d, v⟩; · simp at hv
  rcases v with _ | ⟨e, v⟩; · simp at hv
  rcases v with _ | ⟨f, v⟩
  swap
  · simp only [List.length_cons] at hv
    omega
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    first
      | exact absurd (cycle_word_formally_expanding hm h) (by decide)
      | exact no_cycle_odd_run_append_even (a := 5)
          (by decide : (3 : ℕ) ≤ 5) hm h
      | exact no_cycle_word_ooeooe hm h
      | exact no_cycle_word_oooeoe hm h
      | exact no_cycle_word_ooooee hm h
      | -- EOOOOE rotates once onto OOOOEE
        (have h1 : 2 ≤ floorPower m := by
          have := cycleWord_iterate_ge_two (i := 1) hm h (by decide)
          simpa using this
         exact no_cycle_word_ooooee h1 (cycleWord_rotate_cons h))
      | -- OEOOOE rotates twice onto OOOEOE
        (have h2 : 2 ≤ floorPower (floorPower m) := by
          have := cycleWord_iterate_ge_two (i := 2) hm h (by decide)
          simpa [Function.iterate_succ_apply'] using this
         exact no_cycle_word_oooeoe h2
           (cycleWord_rotate_cons (cycleWord_rotate_cons h)))

/-- **Small-cycle census.** No `n ≥ 2` realizes a cycle word of length
at most six. Length seven is the separate strengthening
`no_cycle_word_length_le_seven`. -/
theorem no_cycle_word_length_le_six {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 6) : ¬CycleWord n w := by
  intro h
  have hne : 1 ≤ w.length := h.2.2
  rcases lt_or_eq_of_le (oddCount_le_length w) with hlt | heq
  · obtain ⟨m, v, hm, hv, hC⟩ := cycleWord_exists_even_terminating hn h hlt
    have hv5 : v.length ≤ 5 := by omega
    rcases v with _ | ⟨a, v⟩
    · exact absurd (cycle_word_formally_expanding hm hC) (by decide)
    rcases v with _ | ⟨b, v⟩
    · cases a <;>
        exact absurd (cycle_word_formally_expanding hm hC) (by decide)
    rcases v with _ | ⟨c, v⟩
    · cases a <;> cases b <;>
        first
          | exact absurd (cycle_word_formally_expanding hm hC) (by decide)
          | exact no_cycle_word_ooe hm hC
    rcases v with _ | ⟨d, v⟩
    · exact no_cycle_word_length_four_ends_even hm (by simp) hC
    rcases v with _ | ⟨e, v⟩
    · exact no_cycle_word_length_five_ends_even hm (by simp) hC
    rcases v with _ | ⟨f, v⟩
    · exact no_cycle_word_len_six_ends_even hm (by simp) hC
    · exfalso
      simp only [List.length_cons] at hv5
      omega
  · have hrep := eq_replicate_odd_of_oddCount_eq_length heq
    rw [hrep] at h
    exact no_cycle_word_replicate_odd hne hn h

/-- Every even-terminating length-seven cycle word is impossible. The
expanding filter leaves seven candidates; odd-run, internal-E
bootstrap, and the two leftover exclusions cover them up to rotation. -/
theorem no_cycle_word_len_seven_ends_even {m : ℕ} {v : List Branch}
    (hm : 2 ≤ m) (hv : v.length = 6) :
    ¬CycleWord m (v ++ [Branch.even]) := by
  intro h
  rcases v with _ | ⟨a, v⟩; · simp at hv
  rcases v with _ | ⟨b, v⟩; · simp at hv
  rcases v with _ | ⟨c, v⟩; · simp at hv
  rcases v with _ | ⟨d, v⟩; · simp at hv
  rcases v with _ | ⟨e, v⟩; · simp at hv
  rcases v with _ | ⟨f, v⟩; · simp at hv
  rcases v with _ | ⟨g, v⟩
  swap
  · simp only [List.length_cons] at hv
    omega
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    first
      | exact absurd (cycle_word_formally_expanding hm h) (by decide)
      | exact no_cycle_odd_run_append_even (a := 6)
          (by decide : (3 : ℕ) ≤ 6) hm h
      | exact no_cycle_word_ooeoooe hm h
      | exact no_cycle_word_oooeooe hm h
      | exact no_cycle_word_ooooeoe hm h
      | exact no_cycle_word_oooooee hm h
      | -- EOOOOOE rotates once onto OOOOOEE
        (have h1 : 2 ≤ floorPower m := by
          have := cycleWord_iterate_ge_two (i := 1) hm h (by decide)
          simpa using this
         exact no_cycle_word_oooooee h1 (cycleWord_rotate_cons h))
      | -- OEOOOOE rotates twice onto OOOOEOE
        (have h2 : 2 ≤ floorPower (floorPower m) := by
          have := cycleWord_iterate_ge_two (i := 2) hm h (by decide)
          simpa [Function.iterate_succ_apply'] using this
         exact no_cycle_word_ooooeoe h2
           (cycleWord_rotate_cons (cycleWord_rotate_cons h)))

/-- **Small-cycle census.** No `n ≥ 2` realizes a cycle word of length
at most seven. Length eight and beyond is open. -/
theorem no_cycle_word_length_le_seven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 7) : ¬CycleWord n w := by
  intro h
  have hne : 1 ≤ w.length := h.2.2
  rcases lt_or_eq_of_le (oddCount_le_length w) with hlt | heq
  · obtain ⟨m, v, hm, hv, hC⟩ := cycleWord_exists_even_terminating hn h hlt
    have hv6 : v.length ≤ 6 := by omega
    rcases v with _ | ⟨a, v⟩
    · exact absurd (cycle_word_formally_expanding hm hC) (by decide)
    rcases v with _ | ⟨b, v⟩
    · cases a <;>
        exact absurd (cycle_word_formally_expanding hm hC) (by decide)
    rcases v with _ | ⟨c, v⟩
    · cases a <;> cases b <;>
        first
          | exact absurd (cycle_word_formally_expanding hm hC) (by decide)
          | exact no_cycle_word_ooe hm hC
    rcases v with _ | ⟨d, v⟩
    · exact no_cycle_word_length_four_ends_even hm (by simp) hC
    rcases v with _ | ⟨e, v⟩
    · exact no_cycle_word_length_five_ends_even hm (by simp) hC
    rcases v with _ | ⟨f, v⟩
    · exact no_cycle_word_len_six_ends_even hm (by simp) hC
    rcases v with _ | ⟨g, v⟩
    · exact no_cycle_word_len_seven_ends_even hm (by simp) hC
    · exfalso
      simp only [List.length_cons] at hv6
      omega
  · have hrep := eq_replicate_odd_of_oddCount_eq_length heq
    rw [hrep] at h
    exact no_cycle_word_replicate_odd hne hn h

end Problems.Juggler
