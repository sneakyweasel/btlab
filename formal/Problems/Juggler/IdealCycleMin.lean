import Problems.Juggler.EvenCountThree
import Problems.Juggler.O7EEEEGap
import Problems.Juggler.CycleMinFudge
import Problems.Juggler.WalkChargeItineraries

namespace Problems.Juggler

/-!
# CycleMin beads, bounds, and sure links

Laboratory wrapper. Existing CycleMin theorems already fix the forced
letters, the interval bounds, and the two sure adjacencies. This file
names that bead model. It does not reprove Paper A, does not raise a
floor, and is not a halt theorem.

Imported by `Problems.Juggler` only. Not a `JugglerPaper` review object.

The combinatorial e-run form
`w = O^{a₁} E ⋯ O^{aₑ} E` with `e = #E`, `a₁ ≥ 2`, `aₑ ≤ 1` is Lean
(`cycleMin_has_full_odd_even_run_form`). Lemma 3.21b's leftover use of
that form for `e ≤ 3` stays the Paper A argument. Unused middle runs
are interval slots, not beads.

`balloonSchema` is a projection of this run list onto six sure letters
and four slots, not an `assembleFill` reconstruction. Exact fill counts
live on `NecklaceFill`. A general CycleMin run list need not equal
`NecklaceFill.toRuns f`.
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

/-! ## Bead parity and count bounds -/

/-- Parity of a bead. `unknown` is interval-only or the optional stem. -/
inductive BeadParity
  | odd
  | even
  | unknown
  deriving DecidableEq, Repr

def BeadParity.ofBranch : Branch → BeadParity
  | .odd => .odd
  | .even => .even

/-- `unknown` matches either letter. Sure beads never use `unknown`. -/
def BeadParity.matches : BeadParity → Branch → Prop
  | .odd, .odd => True
  | .even, .even => True
  | .unknown, _ => True
  | _, _ => False

theorem beadParity_ofBranch_matches (b : Branch) :
    (BeadParity.ofBranch b).matches b := by
  cases b <;> simp [BeadParity.ofBranch, BeadParity.matches]

theorem sure_parity_not_unknown (b : Branch) :
    BeadParity.ofBranch b ≠ .unknown := by
  cases b <;> simp [BeadParity.ofBranch]

/-- How many letters a slot contributes. `max = none` means `min+`. -/
structure CountBound where
  min : ℕ
  max : Option ℕ
  deriving DecidableEq, Repr

def CountBound.exactly (n : ℕ) : CountBound := ⟨n, some n⟩
def CountBound.atLeast (n : ℕ) : CountBound := ⟨n, none⟩
def CountBound.between (lo hi : ℕ) : CountBound := ⟨lo, some hi⟩
def CountBound.zeroPlus : CountBound := .atLeast 0
def CountBound.onePlus : CountBound := .atLeast 1
def CountBound.zeroOrOne : CountBound := .between 0 1

def CountBound.admitsProp (b : CountBound) (k : ℕ) : Prop :=
  b.min ≤ k ∧ ∀ m, b.max = some m → k ≤ m

@[simp] theorem CountBound.admitsProp_zeroPlus (k : ℕ) :
    CountBound.admitsProp .zeroPlus k :=
  ⟨Nat.zero_le k, fun _ hm => by
    simp [CountBound.zeroPlus, CountBound.atLeast] at hm⟩

@[simp] theorem CountBound.admitsProp_onePlus (k : ℕ) :
    CountBound.admitsProp .onePlus k ↔ 1 ≤ k :=
  ⟨fun h => h.1, fun hk =>
    ⟨hk, fun _ hm => by simp [CountBound.onePlus, CountBound.atLeast] at hm⟩⟩

theorem CountBound.admitsProp_zeroOrOne (k : ℕ) :
    CountBound.admitsProp .zeroOrOne k ↔ k ≤ 1 := by
  constructor
  · intro h
    exact h.2 1 rfl
  · intro hk
    refine ⟨Nat.zero_le k, ?_⟩
    intro m hm
    have : m = 1 := by
      simp [CountBound.zeroOrOne, CountBound.between] at hm
      exact hm.symm
    omega

theorem CountBound.admitsProp_exactly (n k : ℕ) :
    CountBound.admitsProp (.exactly n) k ↔ k = n := by
  constructor
  · intro h
    exact Nat.le_antisymm (h.2 n rfl) h.1
  · rintro rfl
    refine ⟨le_rfl, fun m hm => ?_⟩
    simp [CountBound.exactly] at hm
    exact le_of_eq hm

/-! ## Slots and sure links -/

/-- One figure slot: parity, how many letters, and whether they exist. -/
structure BeadSlot where
  parity : BeadParity
  bound : CountBound
  sure : Bool
  deriving DecidableEq, Repr

def BeadSlot.sureOdd : BeadSlot := ⟨.odd, .exactly 1, true⟩
def BeadSlot.sureEven : BeadSlot := ⟨.even, .exactly 1, true⟩
def BeadSlot.launchOO : BeadSlot := ⟨.odd, .exactly 2, true⟩
def BeadSlot.intervalOdd (b : CountBound) : BeadSlot := ⟨.odd, b, false⟩
def BeadSlot.intervalEven (b : CountBound) : BeadSlot := ⟨.even, b, false⟩
def BeadSlot.intervalUnknown (b : CountBound) : BeadSlot := ⟨.unknown, b, false⟩

/-- A necklace edge between consecutive sure beads. -/
inductive BeadEdge
  | sure
  | interval (parity : BeadParity) (bound : CountBound)
  deriving DecidableEq, Repr

def BeadEdge.isSure : BeadEdge → Bool
  | .sure => true
  | .interval _ _ => false

/-- Six sure beads in CycleMin reading order: launch `OO` then four `E`. -/
def sureBeadParities : List BeadParity :=
  [.odd, .odd, .even, .even, .even, .even]

/-- Cyclic edges, one after each sure bead. Index `5` wraps to launch. -/
def cycleEdges : List BeadEdge :=
  [ .sure
  , .interval .odd .zeroPlus
  , .interval .odd .zeroPlus
  , .interval .even .zeroPlus
  , .interval .odd .zeroOrOne
  , .sure
  ]

def sureLink (i j : ℕ) : Bool :=
  decide (i < sureBeadParities.length) &&
    decide (j = (i + 1) % sureBeadParities.length) &&
      (cycleEdges[i]?.map BeadEdge.isSure == some true)

theorem sureBeadParities_length : sureBeadParities.length = 6 := rfl

theorem cycleEdges_length :
    cycleEdges.length = sureBeadParities.length := rfl

theorem cycleEdges_OO_sure : cycleEdges.head? = some .sure := rfl

theorem cycleEdges_wrap_sure : cycleEdges.getLast? = some .sure := rfl

theorem sure_link_count :
    (cycleEdges.filter BeadEdge.isSure).length = 2 :=
  rfl

/-- Launch `OO` is the only linear sure link. -/
theorem OO_sure_link : sureLink 0 1 = true := rfl

/-- Last `E` is cyclically adjacent to the first launch `O`. -/
theorem wrap_sure_link : sureLink 5 0 = true := rfl

theorem launch_to_firstE_not_sure : sureLink 1 2 = false := rfl

theorem firstE_to_secondE_not_sure : sureLink 2 3 = false := rfl

theorem extraEven_edge_not_sure : sureLink 3 4 = false := rfl

theorem lastOdd_edge_not_sure : sureLink 4 5 = false := rfl

private theorem sureLink_index_lt_six {i j : ℕ} (h : sureLink i j = true) :
    i < 6 := by
  have h' : (i < 6 ∧ j = (i + 1) % 6) ∧
      ∃ a, cycleEdges[i]? = some a ∧ a.isSure = true := by
    simpa [sureLink, sureBeadParities] using h
  exact h'.1.1

/-- Exactly two table adjacencies are sure: launch `OO` and the `EO` wrap. -/
theorem sureLink_iff (i j : ℕ) :
    sureLink i j = true ↔ (i = 0 ∧ j = 1) ∨ (i = 5 ∧ j = 0) := by
  constructor
  · intro h
    have : i < 6 := sureLink_index_lt_six h
    interval_cases i
    · refine Or.inl ⟨rfl, ?_⟩
      simpa [sureLink, sureBeadParities, cycleEdges, BeadEdge.isSure] using h
    · simp [sureLink, sureBeadParities, cycleEdges, BeadEdge.isSure] at h
    · simp [sureLink, sureBeadParities, cycleEdges, BeadEdge.isSure] at h
    · simp [sureLink, sureBeadParities, cycleEdges, BeadEdge.isSure] at h
    · simp [sureLink, sureBeadParities, cycleEdges, BeadEdge.isSure] at h
    · refine Or.inr ⟨rfl, ?_⟩
      simpa [sureLink, sureBeadParities, cycleEdges, BeadEdge.isSure] using h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact OO_sure_link
    · exact wrap_sure_link

/-- The only forced cyclic adjacencies are launch `OO` and wrap `EO`. -/
theorem cycleMin_only_forced_adjacencies (i j : ℕ) :
    sureLink i j = true ↔ (i = 0 ∧ j = 1) ∨ (i = 5 ∧ j = 0) :=
  sureLink_iff i j

theorem sure_beads_known_parity :
    ∀ p ∈ sureBeadParities, p ≠ .unknown := by
  decide

/-! ## Full odd-even run form -/

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

theorem assembleOddEvenRuns_append : ∀ as bs : List ℕ,
    assembleOddEvenRuns (as ++ bs) =
      assembleOddEvenRuns as ++ assembleOddEvenRuns bs
  | [], bs => by simp [assembleOddEvenRuns]
  | a :: as, bs => by
      simp [assembleOddEvenRuns, assembleOddEvenRuns_append as bs,
        List.append_assoc]

theorem assembleOddEvenRuns_singleton (a : ℕ) :
    assembleOddEvenRuns [a] =
      List.replicate a Branch.odd ++ [Branch.even] := by
  simp [assembleOddEvenRuns]

theorem assembleOddEvenRuns_replicate_zero :
    ∀ k, assembleOddEvenRuns (List.replicate k 0) = List.replicate k Branch.even
  | 0 => rfl
  | k + 1 => by
      simp [List.replicate_succ, assembleOddEvenRuns,
        assembleOddEvenRuns_replicate_zero k]

theorem assembleOddEvenRuns_eq_nil (as : List ℕ) :
    assembleOddEvenRuns as = [] ↔ as = [] := by
  cases as with
  | nil => simp [assembleOddEvenRuns]
  | cons a rest => simp [assembleOddEvenRuns]

theorem oddEvenRuns_assemble : ∀ as, oddEvenRuns (assembleOddEvenRuns as) = as
  | [] => rfl
  | a :: as => by
      simp [assembleOddEvenRuns, oddEvenRuns_cons_first_even, oddEvenRuns_assemble as]

theorem assembleOddEvenRuns_inj {as bs : List ℕ}
    (h : assembleOddEvenRuns as = assembleOddEvenRuns bs) : as = bs := by
  rw [← oddEvenRuns_assemble as, ← oddEvenRuns_assemble bs, h]

/-- Combinatorial splitting: a word ending `E` is odd-runs separated by
    its `e` evens. Unique. -/
theorem exists_oddEven_run_form {w : List Branch}
    (hw : w.getLast? = some Branch.even) :
    ∃! as, w = assembleOddEvenRuns as := by
  refine ⟨oddEvenRuns w, (assemble_oddEvenRuns hw).symm, ?_⟩
  intro bs hbs
  apply assembleOddEvenRuns_inj
  rw [← hbs, assemble_oddEvenRuns hw]

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

/-- Prefix odd budget: global `#O` and the hug constraint are different. -/
def PrefixOddBudget (w : List Branch) : Prop :=
  ∀ k, k ≤ w.length → hugOdds k ≤ oddCount (w.take k)

theorem cycleMin_bead_prefix_dominates_hug {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : PrefixOddBudget w :=
  cycleMin_hug_prefix_odds hn h

/-- CycleMin letters are `O` or `E`. Unknown beads are stem-only. -/
theorem cycleMin_letters_known_parity {n : ℕ} {w : List Branch}
    (_hn : 2 ≤ n) (_h : CycleMin n w) :
    ∀ b ∈ w, BeadParity.ofBranch b ≠ .unknown :=
  fun b _ => sure_parity_not_unknown b

/-- Sure link `OO`: the first two letters are odd. -/
theorem cycleMin_sure_OO {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    w.head? = some Branch.odd ∧ w.tail.head? = some Branch.odd := by
  obtain ⟨rest, hw⟩ := cycleMin_starts_two_odds hn h
  subst hw
  simp

/-- Sure wrap `E—O`: last letter even, first letter odd. -/
theorem cycleMin_sure_wrap {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    w.getLast? = some Branch.even ∧ w.head? = some Branch.odd := by
  refine ⟨cycleMin_getLast_even hn h, ?_⟩
  exact (cycleMin_sure_OO hn h).1

/-- `a₁` extras are `0+` odds after the sure launch `OO`. -/
theorem cycleMin_a1_interval {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ k v, CountBound.admitsProp .zeroPlus k ∧
      w = List.replicate (k + 2) Branch.odd ++ [Branch.even] ++ v := by
  obtain ⟨a, v, ha, hw⟩ := cycleMin_run_form_first_block hn h
  refine ⟨a - 2, v, CountBound.admitsProp_zeroPlus (a - 2), ?_⟩
  have hka : a - 2 + 2 = a := Nat.sub_add_cancel ha
  have hblock : oddEvenBlock a 1 =
      List.replicate a Branch.odd ++ [Branch.even] := by
    simp [oddEvenBlock]
  calc
    w = oddEvenBlock a 1 ++ v := hw
    _ = List.replicate a Branch.odd ++ [Branch.even] ++ v := by rw [hblock]
    _ = List.replicate (a - 2 + 2) Branch.odd ++ [Branch.even] ++ v := by
        rw [hka]

/-- Last odd-run is the `0 or 1` interval before the last sure `E`. -/
theorem cycleMin_last_interval {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ u k, CountBound.admitsProp .zeroOrOne k ∧
      w = u ++ List.replicate k Branch.odd ++ [Branch.even] := by
  obtain ⟨u, a, hw, ha, _⟩ := exists_cycleMin_last_odd_run hn h
  refine ⟨u, a, (CountBound.admitsProp_zeroOrOne a).mpr ha, hw⟩

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

theorem cycleMin_realizes_sure_links {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    w.head? = some Branch.odd ∧ w.tail.head? = some Branch.odd ∧
      w.getLast? = some Branch.even :=
  ⟨(cycleMin_sure_OO hn h).1, (cycleMin_sure_OO hn h).2,
    (cycleMin_sure_wrap hn h).1⟩

theorem cycleMin_launch_is_OO {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    w.head? = some Branch.odd ∧ w.tail.head? = some Branch.odd :=
  cycleMin_sure_OO hn h

theorem cycleMin_wrap_is_EO {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    w.getLast? = some Branch.even ∧ w.head? = some Branch.odd :=
  cycleMin_sure_wrap hn h

theorem cycleMin_firstEven_is_overshoot {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ a v, w = oddEvenBlock a 1 ++ v ∧
      (n + 1) ^ 2 ≤ image n (List.replicate a Branch.odd) ∧
        n < image n (oddEvenBlock a 1) :=
  cycleMin_first_even_role hn h

theorem cycleMin_lastEven_is_closure_cell {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ u, w = u ++ [Branch.even] ∧
      n ^ 2 ≤ image n u ∧ image n u < (n + 1) ^ 2 :=
  cycleMin_last_even_role hn h

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

def BalloonStation.bound : BalloonStation → CountBound
  | .sureLaunchO => .exactly 2
  | .sureEven _ => .exactly 1
  | .intervalOdd .lastZeroOrOne => .zeroOrOne
  | .intervalOdd _ | .intervalExtraEven => .zeroPlus

def BalloonStation.parity : BalloonStation → BeadParity
  | .sureLaunchO | .intervalOdd _ => .odd
  | .sureEven _ | .intervalExtraEven => .even

def BalloonStation.asSlot (s : BalloonStation) : BeadSlot :=
  ⟨s.parity, s.bound, s.isForced⟩

def BalloonStation.intervalMin : BalloonStation → Option ℕ
  | .intervalOdd _ | .intervalExtraEven => some 0
  | .sureLaunchO | .sureEven _ => none

def BalloonStation.intervalMax : BalloonStation → Option ℕ
  | .intervalOdd .lastZeroOrOne => some 1
  | .intervalOdd .a1Extras | .intervalOdd .middle
  | .intervalExtraEven | .sureLaunchO | .sureEven _ => none

/-- Candidate bead schema in CycleMin reading order.
    Exact realization of a CycleMin word as this schema requires the
    full e-run decomposition (Lemma 3.21b, `EXACT — HUMAN PROOF`).
    Six sure letters (`OO` + four `E`); interval slots are bounds.
    Extra evens sit between the two middle sure `E`, not after the last. -/
def balloonSchema : List BalloonStation :=
  [ .sureLaunchO
  , .intervalOdd .a1Extras
  , .sureEven .first
  , .intervalOdd .middle
  , .sureEven .middle
  , .intervalExtraEven
  , .sureEven .middle
  , .intervalOdd .lastZeroOrOne
  , .sureEven .last
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

/-- Six sure letters: launch `OO` plus four sure `E`. -/
theorem cycleMin_sure_letter_inventory :
    (balloonSchemaForced.map BalloonStation.sureLetterCount).sum = 6 ∧
      (balloonSchemaForced.filter fun s =>
        match s with
        | .sureEven _ => true
        | _ => false).length = 4 ∧
          BalloonStation.sureLetterCount .sureLaunchO = 2 :=
  ⟨balloonSchema_sure_letter_count, balloonSchema_sure_even_count,
    balloonSchema_sure_launch_repeat⟩

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

theorem balloonSchema_slots :
    balloonSchema.map BalloonStation.asSlot =
      [ BeadSlot.launchOO
      , BeadSlot.intervalOdd .zeroPlus
      , BeadSlot.sureEven
      , BeadSlot.intervalOdd .zeroPlus
      , BeadSlot.sureEven
      , BeadSlot.intervalEven .zeroPlus
      , BeadSlot.sureEven
      , BeadSlot.intervalOdd .zeroOrOne
      , BeadSlot.sureEven
      ] :=
  rfl

theorem sureLaunch_two_odds :
    (BalloonStation.asSlot .sureLaunchO).parity = .odd ∧
      (BalloonStation.asSlot .sureLaunchO).bound = .exactly 2 ∧
        (BalloonStation.asSlot .sureLaunchO).sure = true :=
  ⟨rfl, rfl, rfl⟩

/-- Projection onto forced stations, not an `assembleFill` reconstruction.
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

/-! ## Optional stem (not a CycleMin theorem) -/

/-- Optional first-visit stem: sure `OO`, unknown middle `0+`, sure `t = E`.
    This bead join is still a picture. Actual integer edges and
    Collision Factorization live in `Seam.lean` (`SeamData`). -/
def stemSureParities : List BeadParity := [.odd, .odd, .even]

def stemEdges : List BeadEdge :=
  [ .sure
  , .interval .unknown .zeroPlus
  ]

def stemSlots : List BeadSlot :=
  [ BeadSlot.sureOdd
  , BeadSlot.sureOdd
  , BeadSlot.intervalUnknown .zeroPlus
  , BeadSlot.sureEven
  ]

theorem stem_linear :
    stemEdges.length + 1 = stemSureParities.length :=
  rfl

theorem stem_OO_sure : stemEdges.head? = some .sure := rfl

theorem stem_middle_unknown :
    (BeadSlot.intervalUnknown .zeroPlus).parity = .unknown ∧
      (BeadSlot.intervalUnknown .zeroPlus).sure = false ∧
        CountBound.admitsProp .zeroPlus 0 :=
  ⟨rfl, rfl, CountBound.admitsProp_zeroPlus 0⟩

theorem stem_slots_not_cycle_schema :
    stemSlots ≠ balloonSchema.map BalloonStation.asSlot := by
  decide

/-! ## Necklace fills: interval lengths between sure beads -/

/-- Lengths for the four open edges. Extra evens are letters past four `E`. -/
structure NecklaceFill where
  a1Extras : ℕ
  middleOdds : ℕ
  extraEvens : ℕ
  lastOdds : ℕ
  deriving DecidableEq, Repr

def NecklaceFill.admits (f : NecklaceFill) : Prop :=
  CountBound.admitsProp .zeroPlus f.a1Extras ∧
    CountBound.admitsProp .zeroPlus f.middleOdds ∧
      CountBound.admitsProp .zeroPlus f.extraEvens ∧
        CountBound.admitsProp .zeroOrOne f.lastOdds

def assembleFill (f : NecklaceFill) : List Branch :=
  List.replicate 2 Branch.odd ++
    List.replicate f.a1Extras Branch.odd ++
    [Branch.even] ++
    List.replicate f.middleOdds Branch.odd ++
    [Branch.even] ++
    List.replicate f.extraEvens Branch.even ++
    [Branch.even] ++
    List.replicate f.lastOdds Branch.odd ++
    [Branch.even]

theorem NecklaceFill.admits_of_last_le_one (f : NecklaceFill)
    (hlast : f.lastOdds ≤ 1) : f.admits :=
  ⟨CountBound.admitsProp_zeroPlus _,
    CountBound.admitsProp_zeroPlus _,
    CountBound.admitsProp_zeroPlus _,
    (CountBound.admitsProp_zeroOrOne f.lastOdds).mpr hlast⟩

theorem assemble_of_no_extra_evens (f : NecklaceFill)
    (h0 : f.extraEvens = 0) :
    assembleFill f =
      fourEvenWord (2 + f.a1Extras) f.middleOdds 0 f.lastOdds := by
  simp [assembleFill, fourEvenWord, h0]
  have hrep :
      List.replicate (2 + f.a1Extras) Branch.odd =
        Branch.odd :: Branch.odd :: List.replicate f.a1Extras Branch.odd := by
    rw [List.replicate_add]
    rfl
  rw [hrep]
  simp [List.cons_append]

theorem assembleFill_oddCount (f : NecklaceFill) :
    oddCount (assembleFill f) = 2 + f.a1Extras + f.middleOdds + f.lastOdds := by
  simp [assembleFill, oddCount_append, oddCount_replicate_odd, oddCount_replicate_even]
  omega

theorem assembleFill_evenCount (f : NecklaceFill) :
    evenCount (assembleFill f) = 4 + f.extraEvens := by
  simp [assembleFill, evenCount_append, evenCount_replicate_odd, evenCount_replicate_even]
  omega

theorem assembleFill_length (f : NecklaceFill) :
    (assembleFill f).length =
      6 + f.a1Extras + f.middleOdds + f.extraEvens + f.lastOdds := by
  simp [assembleFill]
  omega

theorem assembleFill_unplaced_odds (f : NecklaceFill) :
    oddCount (assembleFill f) - 2 =
      f.a1Extras + f.middleOdds + f.lastOdds := by
  rw [assembleFill_oddCount]
  omega

theorem assembleFill_extra_evens (f : NecklaceFill) :
    evenCount (assembleFill f) - 4 = f.extraEvens := by
  rw [assembleFill_evenCount]
  omega

/-- Unplaced odds on a fill are exactly the three open odd slots. -/
theorem necklaceFill_unplaced_odd_budget (f : NecklaceFill) :
    oddCount (assembleFill f) - 2 =
      f.a1Extras + f.middleOdds + f.lastOdds :=
  assembleFill_unplaced_odds f

/-- Extra evens on a fill are exactly the extra-even slot. -/
theorem necklaceFill_extra_even_budget (f : NecklaceFill) :
    evenCount (assembleFill f) - 4 = f.extraEvens :=
  assembleFill_extra_evens f

/-- Bead fill as a run list: first run, bunched middle odds, extra
    evens as empty interior runs, last run. This is a projection, not
    the general CycleMin decomposition. -/
def NecklaceFill.toRuns (f : NecklaceFill) : List ℕ :=
  [2 + f.a1Extras, f.middleOdds] ++
    List.replicate (f.extraEvens + 1) 0 ++
    [f.lastOdds]

theorem NecklaceFill.toRuns_length (f : NecklaceFill) :
    f.toRuns.length = 4 + f.extraEvens := by
  simp [NecklaceFill.toRuns]
  omega

theorem NecklaceFill.toRuns_index_two (f : NecklaceFill) :
    f.toRuns[2]? = some 0 := by
  have h :
      f.toRuns =
        (2 + f.a1Extras) :: f.middleOdds ::
          0 :: (List.replicate f.extraEvens 0 ++ [f.lastOdds]) := by
    simp [NecklaceFill.toRuns, List.replicate_succ]
  simp [h]

/-- The four-slot bead word is exactly this aggregated run list. -/
theorem assembleFill_eq_assembleOddEvenRuns (f : NecklaceFill) :
    assembleFill f = assembleOddEvenRuns f.toRuns := by
  have hruns :
      f.toRuns =
        [2 + f.a1Extras, f.middleOdds] ++
          List.replicate (f.extraEvens + 1) 0 ++ [f.lastOdds] :=
    rfl
  have hleft :
      assembleOddEvenRuns f.toRuns =
        List.replicate (2 + f.a1Extras) Branch.odd ++ [Branch.even] ++
          List.replicate f.middleOdds Branch.odd ++ [Branch.even] ++
          List.replicate (f.extraEvens + 1) Branch.even ++
          List.replicate f.lastOdds Branch.odd ++ [Branch.even] := by
    rw [hruns, assembleOddEvenRuns_append, assembleOddEvenRuns_append,
      assembleOddEvenRuns_replicate_zero]
    simp [assembleOddEvenRuns]
  have hrep :
      List.replicate (2 + f.a1Extras) Branch.odd =
        List.replicate 2 Branch.odd ++ List.replicate f.a1Extras Branch.odd :=
    List.replicate_add 2 f.a1Extras Branch.odd
  have hextra :
      List.replicate (f.extraEvens + 1) Branch.even =
        List.replicate f.extraEvens Branch.even ++ [Branch.even] :=
    List.replicate_succ'
  simp [assembleFill, hleft, hrep, hextra, List.append_assoc]

theorem fourEvenWord_eq_assembleOddEvenRuns (a0 a1 a2 a3 : ℕ) :
    fourEvenWord a0 a1 a2 a3 = assembleOddEvenRuns [a0, a1, a2, a3] := by
  simp [fourEvenWord, assembleOddEvenRuns]

/-- Interior three-valley leftover is a run list, not a bead fill. -/
theorem leftover_three_valley_not_fill_runs (f : NecklaceFill) :
    f.toRuns ≠ [3, 2, 2, 0] := by
  intro hf
  have h0 : f.toRuns[2]? = some 0 := NecklaceFill.toRuns_index_two f
  simp [hf] at h0

/-! ## Leftovers inhabit the shape and are not cycles -/

def leftoverO7EEEE_fill : NecklaceFill := ⟨5, 0, 0, 0⟩
def leftoverO6EEEOE_fill : NecklaceFill := ⟨4, 0, 0, 1⟩

theorem leftover_O7EEEE_fill_admits : leftoverO7EEEE_fill.admits :=
  NecklaceFill.admits_of_last_le_one _ (by decide)

theorem leftover_O7EEEE_fill_eq :
    assembleFill leftoverO7EEEE_fill = itineraryO7EEEE := by
  simp [assembleFill, leftoverO7EEEE_fill, itineraryO7EEEE, sevenOdds]

theorem leftover_O6EEEOE_fill_admits : leftoverO6EEEOE_fill.admits :=
  NecklaceFill.admits_of_last_le_one _ (by decide)

theorem leftover_O6EEEOE_fill_eq :
    assembleFill leftoverO6EEEOE_fill = fourEvenWord 6 0 0 1 := by
  simpa [leftoverO6EEEOE_fill] using
    assemble_of_no_extra_evens leftoverO6EEEOE_fill rfl

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

/-- Shape is not a CycleMin characterization. -/
theorem CycleMinShape_not_of_CycleMin :
    ∃ w, CycleMinShape w ∧ ∀ n, ¬ CycleItinerary n w :=
  ⟨itineraryO7EEEE, leftover_O7EEEE_inhabits_shape, fun _ => leftover_O7EEEE_not_cycle⟩

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
