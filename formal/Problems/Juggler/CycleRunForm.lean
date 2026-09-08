import Problems.Juggler.EvenCountThree

namespace Problems.Juggler

/-!
# The CycleMin run form

`w = O^{a₁}E ⋯ O^{a_e}E` with `e` even letters, `a₁ ≥ 2` and `a_e ≤ 1`.

Hoisted here from `IdealCycleMin` so that it sits inside Paper A's barrel.
The companion's lollipop figure is laid out by this theorem — the bead count,
the `a₁ ≥ 2` launch and the `a_e ≤ 1` tail — and a reader checking Paper A's
Lean should find it there rather than in a display module. Its two substantive
inputs, `cycleMin_getLast_even` and `exists_cycleMin_last_odd_run`, live in
`EvenCountThree`, which the barrel already carries.

The bead schema itself stays in `IdealCycleMin`: it is a *projection* of this
run list and `assembleFill` is not a characterization, so it is display
scaffolding rather than a claim of the paper.
-/

/-- Concatenate odd-runs separated by one even each. -/
def assembleOddEvenRuns : List ℕ → List Branch
  | [] => []
  | a :: as =>
      List.replicate a Branch.odd ++ Branch.even :: assembleOddEvenRuns as

/-- Recover the odd-run lengths of a word. Empty unless the word ends `E`. -/
def oddEvenRuns : List Branch → List ℕ
  | [] => []
  | Branch.odd :: rest =>
      match oddEvenRuns rest with
      | [] => []
      | a :: as => (a + 1) :: as
  | Branch.even :: rest => 0 :: oddEvenRuns rest

theorem oddEvenRuns_ne_nil_of_endsEven {w : List Branch}
    (hw : w.getLast? = some Branch.even) : oddEvenRuns w ≠ [] := by
  induction w with
  | nil => simp at hw
  | cons b rest ih =>
      cases b with
      | even => simp [oddEvenRuns]
      | odd =>
          have hrest : rest.getLast? = some Branch.even := by
            cases rest with
            | nil => simp [List.getLast?] at hw
            | cons _ _ => simpa [List.getLast?] using hw
          have hne := ih hrest
          match hruns : oddEvenRuns rest with
          | [] => exact (hne hruns).elim
          | a :: as => simp [oddEvenRuns, hruns]

theorem assemble_oddEvenRuns {w : List Branch}
    (hw : w.getLast? = some Branch.even) :
    assembleOddEvenRuns (oddEvenRuns w) = w := by
  induction w with
  | nil => simp at hw
  | cons b rest ih =>
      cases b with
      | even =>
          cases rest with
          | nil => simp [oddEvenRuns, assembleOddEvenRuns]
          | cons c t =>
              have hrest : (c :: t).getLast? = some Branch.even := by
                simpa [List.getLast?] using hw
              simp [oddEvenRuns, assembleOddEvenRuns, ih hrest]
      | odd =>
          have hrest : rest.getLast? = some Branch.even := by
            cases rest with
            | nil => simp [List.getLast?] at hw
            | cons _ _ => simpa [List.getLast?] using hw
          have hne := oddEvenRuns_ne_nil_of_endsEven hrest
          match hruns : oddEvenRuns rest with
          | [] => exact (hne hruns).elim
          | a :: as =>
              have hrest' : assembleOddEvenRuns (a :: as) = rest := by
                simpa [hruns] using ih hrest
              simp [oddEvenRuns, hruns, assembleOddEvenRuns, List.replicate_succ]
              exact hrest'

theorem evenCount_assembleOddEvenRuns : ∀ as : List ℕ,
    evenCount (assembleOddEvenRuns as) = as.length
  | [] => rfl
  | a :: as => by
      simp [assembleOddEvenRuns, evenCount_append, evenCount_replicate_odd,
        evenCount_assembleOddEvenRuns as]

theorem oddEvenRuns_length_eq_evenCount {w : List Branch}
    (hw : w.getLast? = some Branch.even) :
    (oddEvenRuns w).length = evenCount w := by
  have h := evenCount_assembleOddEvenRuns (oddEvenRuns w)
  rw [assemble_oddEvenRuns hw] at h
  exact h.symm

theorem oddEvenRuns_cons_first_even (a : ℕ) (v : List Branch) :
    oddEvenRuns (List.replicate a Branch.odd ++ Branch.even :: v) =
      a :: oddEvenRuns v := by
  induction a with
  | zero => simp [oddEvenRuns]
  | succ a ih =>
      simp [List.replicate_succ, oddEvenRuns, ih]

theorem oddEvenRuns_replicate_odds_even (a : ℕ) :
    oddEvenRuns (List.replicate a Branch.odd ++ [Branch.even]) = [a] := by
  simpa [oddEvenRuns] using oddEvenRuns_cons_first_even a []

theorem oddEvenRuns_append_of_endsEven {u w : List Branch}
    (hu : u.getLast? = some Branch.even) :
    oddEvenRuns (u ++ w) = oddEvenRuns u ++ oddEvenRuns w := by
  induction u with
  | nil => simp at hu
  | cons b rest ih =>
      cases b with
      | even =>
          cases rest with
          | nil => simp [oddEvenRuns]
          | cons c t =>
              have hrest : (c :: t).getLast? = some Branch.even := by
                simpa [List.getLast?] using hu
              simp [oddEvenRuns]
              exact ih hrest
      | odd =>
          have hrest : rest.getLast? = some Branch.even := by
            cases rest with
            | nil => simp [List.getLast?] at hu
            | cons _ _ => simpa [List.getLast?] using hu
          have hne := oddEvenRuns_ne_nil_of_endsEven hrest
          have happ := ih hrest
          match hruns : oddEvenRuns rest with
          | [] => exact (hne hruns).elim
          | a :: as =>
              have hsplit :
                  oddEvenRuns (rest ++ w) = a :: as ++ oddEvenRuns w := by
                simpa [hruns] using happ
              simp [oddEvenRuns, hruns, hsplit]

/-- First-run wrap of Lemma 3.21b: `O^{a₁} E` plus a tail, `a₁ ≥ 2`. -/
theorem cycleMin_run_form_first_block {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ a v, 2 ≤ a ∧ w = oddEvenBlock a 1 ++ v := by
  obtain ⟨a, v, hw⟩ := cycleMin_exists_oddEven_split hn h
  refine ⟨a, v, cycleMin_oddEvenBlock_starts_two_odds hn (by simpa [hw] using h), hw⟩

/-- Full CycleMin run form: `w = O^{a₁}E ⋯ O^{aₑ}E` with `e = #E`,
    `a₁ ≥ 2`, `aₑ ≤ 1`. The bead schema is a projection of this list,
    not a characterization. Lemma 3.21b's leftover use for `e ≤ 3`
    stays the Paper A argument. -/
theorem cycleMin_has_full_odd_even_run_form {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ as, w = assembleOddEvenRuns as ∧
      as.length = evenCount w ∧
        4 ≤ as.length ∧
          (∃ a1 t, as = a1 :: t ∧ 2 ≤ a1) ∧
            (∃ u ae, as = u ++ [ae] ∧ ae ≤ 1) := by
  have hend := cycleMin_getLast_even hn h
  refine ⟨oddEvenRuns w, (assemble_oddEvenRuns hend).symm,
    oddEvenRuns_length_eq_evenCount hend, ?_, ?_, ?_⟩
  · have he := cycle_itinerary_even_count_ge_four hn h.1
    rwa [← oddEvenRuns_length_eq_evenCount hend] at he
  · obtain ⟨a, v, ha, hw⟩ := cycleMin_run_form_first_block hn h
    have hw' : w = List.replicate a Branch.odd ++ Branch.even :: v := by
      simpa [oddEvenBlock] using hw
    refine ⟨a, oddEvenRuns v, ?_, ha⟩
    rw [hw', oddEvenRuns_cons_first_even]
  · obtain ⟨u, a, hw, ha, hcut⟩ := exists_cycleMin_last_odd_run hn h
    have hw' : w = u ++ (List.replicate a Branch.odd ++ [Branch.even]) := by
      simpa [List.append_assoc] using hw
    refine ⟨oddEvenRuns u, a, ?_, ha⟩
    cases hcut with
    | inl hu =>
        rw [hw', hu, List.nil_append, oddEvenRuns_replicate_odds_even]
        simp [oddEvenRuns]
    | inr hu =>
        rw [hw', oddEvenRuns_append_of_endsEven hu, oddEvenRuns_replicate_odds_even]


end Problems.Juggler
