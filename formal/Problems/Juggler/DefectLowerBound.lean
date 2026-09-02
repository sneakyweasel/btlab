import Problems.Juggler.GlobalDefect

namespace Problems.Juggler

/-!
# First-defect amplification

The first positive local remainder sits after a rigid tight prefix.
Its contribution is then lifted through the suffix by the same
nonlinear recurrence, with later remainders dropped. This file does
not claim that the resulting lower bound exceeds the formal surplus,
and does not claim that every start reaches `1`.
-/

/-- Index of the first positive local remainder, or `w.length` if none. -/
def firstDefectFrom (current : ℕ) : List Branch → ℕ
  | [] => 0
  | b :: w =>
      if branchDefect b current = 0 then
        firstDefectFrom (floorPower current) w + 1
      else
        0

def firstDefect (n : ℕ) (w : List Branch) : ℕ :=
  firstDefectFrom n w

theorem firstDefectFrom_le_length (current : ℕ) :
    ∀ w, firstDefectFrom current w ≤ w.length
  | [] => le_rfl
  | b :: w => by
      simp only [firstDefectFrom, List.length_cons]
      split_ifs
      · exact Nat.succ_le_succ (firstDefectFrom_le_length _ w)
      · exact Nat.zero_le _

theorem firstDefect_le_length (n : ℕ) (w : List Branch) :
    firstDefect n w ≤ w.length :=
  firstDefectFrom_le_length n w

theorem firstDefectFrom_prefix_zero (current : ℕ) :
    ∀ (w : List Branch) (i : ℕ), i < firstDefectFrom current w →
      (hi : i < w.length) →
        branchDefect w[i] (floorPower^[i] current) = 0
  | [], i, hlt, hi => by cases hi
  | b :: w, i, hlt, hi => by
      simp only [firstDefectFrom] at hlt
      split_ifs at hlt with hz
      · cases i with
        | zero =>
            simpa [List.getElem_cons_zero, Function.iterate_zero_apply] using hz
        | succ j =>
            have hlt' : j < firstDefectFrom (floorPower current) w := by omega
            have hj : j < w.length := by
              simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
            have ih :=
              firstDefectFrom_prefix_zero (floorPower current) w j hlt' hj
            simpa [List.getElem_cons_succ, iterate_cons] using ih
      · cases hlt

theorem firstDefectFrom_pos (current : ℕ) :
    ∀ (w : List Branch) (h : firstDefectFrom current w < w.length),
      0 < branchDefect w[firstDefectFrom current w]
            (floorPower^[firstDefectFrom current w] current)
  | [], h => by simp [firstDefectFrom] at h
  | b :: w, h => by
      simp only [firstDefectFrom] at h
      split_ifs at h with hz
      · have hidx :
            firstDefectFrom current (b :: w) =
              firstDefectFrom (floorPower current) w + 1 := by
          simp [firstDefectFrom, hz]
        have hih : firstDefectFrom (floorPower current) w < w.length := by
          simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp h
        have ih := firstDefectFrom_pos (floorPower current) w hih
        simpa [hidx, List.getElem_cons_succ, iterate_cons] using ih
      · have hidx : firstDefectFrom current (b :: w) = 0 := by
          simp [firstDefectFrom, hz]
        have hne : branchDefect b current ≠ 0 := hz
        simpa [hidx, List.getElem_cons_zero, Function.iterate_zero_apply] using
          Nat.pos_of_ne_zero hne

/-- Prefix remainders vanish; the selected index is the first positive one. -/
theorem firstDefect_spec {n : ℕ} {w : List Branch} :
    (∀ i, i < firstDefect n w → (hi : i < w.length) →
        branchDefect w[i] (floorPower^[i] n) = 0) ∧
      (∀ (h : firstDefect n w < w.length),
        0 < branchDefect w[firstDefect n w]
              (floorPower^[firstDefect n w] n)) :=
  ⟨firstDefectFrom_prefix_zero n w, firstDefectFrom_pos n w⟩

theorem firstDefect_pos {n : ℕ} {w : List Branch}
    (h : firstDefect n w < w.length) :
    0 < branchDefect w[firstDefect n w] (floorPower^[firstDefect n w] n) :=
  firstDefect_spec.2 h

theorem firstDefectFrom_eq_length_iff (current : ℕ) :
    ∀ w, firstDefectFrom current w = w.length ↔
      ∀ i, (hi : i < w.length) →
        branchDefect w[i] (floorPower^[i] current) = 0
  | [] => by simp [firstDefectFrom]
  | b :: w => by
      simp only [firstDefectFrom, List.length_cons]
      split_ifs with hz
      · constructor
        · intro heq i hi
          have hih : firstDefectFrom (floorPower current) w = w.length := by omega
          cases i with
          | zero =>
              simpa [List.getElem_cons_zero, Function.iterate_zero_apply] using hz
          | succ j =>
              have hj : j < w.length := by
                simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
              have ih :=
                (firstDefectFrom_eq_length_iff (floorPower current) w).mp hih
              simpa [List.getElem_cons_succ, iterate_cons] using ih j hj
        · intro hall
          have ih :=
            (firstDefectFrom_eq_length_iff (floorPower current) w).mpr ?_
          · omega
          · intro j hj
            have hj' : j + 1 < (b :: w).length := by
              simpa [List.length_cons] using Nat.succ_lt_succ hj
            simpa [List.getElem_cons_succ, iterate_cons] using hall (j + 1) hj'
      · constructor
        · intro heq i hi
          exact heq.elim
        · intro hall
          have : branchDefect b current = 0 := by
            simpa [List.getElem_cons_zero, Function.iterate_zero_apply] using
              hall 0 (Nat.succ_pos _)
          exact (hz this).elim

theorem firstDefect_eq_length_iff_zero_defects (n : ℕ) (w : List Branch) :
    firstDefect n w = w.length ↔
      ∀ i, (hi : i < w.length) →
        branchDefect w[i] (floorPower^[i] n) = 0 :=
  firstDefectFrom_eq_length_iff n w

theorem firstDefect_lt_iff_pos {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    firstDefect n w < w.length ↔ 0 < globalDefect n w := by
  have hlen := firstDefect_le_length n w
  have heq := firstDefect_eq_length_iff_zero_defects n w
  have hΔ := global_defect_eq_zero_iff_locals hw
  constructor
  · intro hlt
    exact Nat.pos_of_ne_zero fun hz => by
      have : firstDefect n w = w.length := heq.mpr (hΔ.mp hz)
      omega
  · intro hpos
    refine lt_of_le_of_ne hlen ?_
    intro he
    exact (Nat.ne_of_gt hpos) (hΔ.mpr (heq.mp he))

theorem firstDefect_lt_of_mixed {n : ℕ} {w : List Branch}
    (hw : follows n w) (hmix : ¬ isMonochrome w) :
    firstDefect n w < w.length :=
  (firstDefect_lt_iff_pos hw).mpr (global_defect_pos_of_mixed hw hmix)

theorem localsTight_take {n : ℕ} :
    ∀ (w : List Branch) (i : ℕ), localsTight n w → localsTight n (w.take i)
  | _w, 0, _ => trivial
  | [], _i + 1, h => h
  | _b :: rest, i + 1, h => ⟨h.1, localsTight_take rest i h.2⟩

theorem follows_singleton {n : ℕ} {b : Branch} {w : List Branch}
    (hw : follows n (b :: w)) : follows n [b] := by
  cases b <;> exact ⟨hw.1, trivial⟩

/-- The prefix before the first defect is completely tight. -/
theorem firstDefect_prefix_tight {n : ℕ} :
    ∀ {w : List Branch}, follows n w →
      localsTight n (w.take (firstDefect n w))
  | [], _ => trivial
  | b :: w, hw => by
      simp only [firstDefect, firstDefectFrom]
      split_ifs with hz
      · have hloc :
            localTight n b :=
          (branchDefect_eq_zero_iff_localTight (follows_singleton hw)).mp hz
        have hrest : follows (floorPower n) w := by
          cases b <;> exact hw.2
        have ih := firstDefect_prefix_tight (n := floorPower n) hrest
        change localsTight n (b :: w.take (firstDefect (floorPower n) w))
        exact ⟨hloc, ih⟩
      · trivial

/-- The tight prefix is an even or odd power-of-two tower. -/
theorem firstDefect_prefix_extremal {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    let j := firstDefect n w
    let u := w.take j
    (u = List.replicate j Branch.even ∧ ∃ a, a % 2 = 0 ∧ n = a ^ (2 ^ j)) ∨
      (u = List.replicate j Branch.odd ∧ ∃ a, a % 2 = 1 ∧ n = a ^ (2 ^ j)) := by
  set j := firstDefect n w
  set u := w.take j
  have hj : j ≤ w.length := firstDefect_le_length n w
  have hlen : u.length = j := List.length_take_of_le hj
  have hu : follows n u := follows_take w j hw
  have ht : localsTight n u := firstDefect_prefix_tight hw
  have heq := localsTight_implies_power_bound_eq u hu ht
  have hex :=
    (power_bound_eq_iff_extremal (n := n) (w := u)).mp ⟨hu, heq⟩
  simpa [hlen] using hex

/-- Canonical first-defect form of `ρ_j^{2^j} ≤ Δ`. -/
theorem firstDefect_contribution {n : ℕ} {w : List Branch}
    (hw : follows n w) (hpos : firstDefect n w < w.length) :
    (branchDefect w[firstDefect n w] (floorPower^[firstDefect n w] n)) ^
      (2 ^ firstDefect n w) ≤
      globalDefect n w :=
  global_defect_ge_local hw hpos

theorem branchDefect_eq_zero_of_localTight {x : ℕ} {b : Branch}
    (h : localTight x b) : branchDefect b x = 0 := by
  cases b with
  | even =>
      simp [branchDefect, localDefectEven, localTight] at h ⊢
      simp [h]
  | odd =>
      simp [branchDefect, localDefectOdd, localTight] at h ⊢
      simp [h]

theorem localTight_odd_image_odd {x : ℕ} (hodd : x % 2 = 1)
    (ht : localTight x Branch.odd) : floorPower x % 2 = 1 := by
  have hsq : floorPower x ^ 2 = x ^ 3 := ht
  by_cases hT : floorPower x % 2 = 1
  · exact hT
  · have h0 : floorPower x % 2 = 0 := by omega
    have hsq2 : floorPower x ^ 2 % 2 = 0 := by
      rw [pow_two, Nat.mul_mod, h0]
    have hx3 : x ^ 3 % 2 = 0 := by
      rw [← hsq]
      exact hsq2
    have hx3' : x ^ 3 % 2 = 1 := by
      rw [Nat.pow_mod, hodd]
    omega

theorem localsTight_replicate_odd_stays_odd {x : ℕ} :
    ∀ a, follows x (List.replicate a Branch.odd) →
      localsTight x (List.replicate a Branch.odd) →
        a = 0 ∨ image x (List.replicate a Branch.odd) % 2 = 1
  | 0, _, _ => Or.inl rfl
  | a + 1, hw, ht => by
      have hodd : x % 2 = 1 := by
        simpa [List.replicate_succ] using hw.1
      have hloc : localTight x Branch.odd := by
        simpa [List.replicate_succ, localsTight] using ht.1
      have hy := localTight_odd_image_odd hodd hloc
      have hrest :=
        localsTight_replicate_odd_stays_odd a
          (by simpa [List.replicate_succ] using hw.2)
          (by simpa [List.replicate_succ, localsTight] using ht.2)
      cases hrest with
      | inl h0 =>
          subst h0
          exact Or.inr (by simpa [image, List.replicate] using hy)
      | inr himg =>
          exact Or.inr (by simpa [image, List.replicate_succ] using himg)

/-- A later even letter cannot follow a completely tight odd run. -/
theorem firstDefect_lt_of_odd_run_then_even {n odds : ℕ} {w : List Branch}
    (hpos : 0 < odds)
    (hw : follows n (List.replicate odds Branch.odd ++ Branch.even :: w)) :
    firstDefect n (List.replicate odds Branch.odd ++ Branch.even :: w) < odds := by
  set word := List.replicate odds Branch.odd ++ Branch.even :: w
  by_contra hge
  have hge' : odds ≤ firstDefect n word := Nat.le_of_not_gt hge
  have ht := firstDefect_prefix_tight hw
  have htake_eq : word.take odds = List.replicate odds Branch.odd := by
    have hlen : (List.replicate odds Branch.odd).length = odds :=
      List.length_replicate
    simpa [word, hlen] using
      (List.take_left (l₁ := List.replicate odds Branch.odd)
        (l₂ := Branch.even :: w))
  have htake_nested :
      word.take odds = (word.take (firstDefect n word)).take odds := by
    rw [List.take_take, min_eq_left hge']
  have ht_odds : localsTight n (word.take odds) := by
    rw [htake_nested]
    exact localsTight_take _ odds ht
  rw [htake_eq] at ht_odds
  have hu : follows n (List.replicate odds Branch.odd) :=
    follows_of_append_left (u := List.replicate odds Branch.odd) hw
  have himg := localsTight_replicate_odd_stays_odd odds hu ht_odds
  have hodd_img : image n (List.replicate odds Branch.odd) % 2 = 1 := by
    cases himg with
    | inl h0 => omega
    | inr h => exact h
  have hv :
      follows (image n (List.replicate odds Branch.odd)) (Branch.even :: w) :=
    follows_of_append_right hw
  have heven_img : image n (List.replicate odds Branch.odd) % 2 = 0 := hv.1
  omega

def ooeWord : List Branch := [.odd, .odd, .even]

def ooeoWord : List Branch := [.odd, .odd, .even, .odd]

def oooeWord : List Branch := [.odd, .odd, .odd, .even]

theorem ooeWord_decompose :
    ooeWord = List.replicate 2 Branch.odd ++ [Branch.even] :=
  rfl

theorem ooeoWord_decompose :
    ooeoWord = List.replicate 2 Branch.odd ++ [.even, .odd] :=
  rfl

theorem oooeWord_decompose :
    oooeWord = List.replicate 3 Branch.odd ++ [Branch.even] :=
  rfl

theorem ooeWord_not_monochrome : ¬ isMonochrome ooeWord := by
  rintro (h | h) <;> simp [ooeWord] at h

theorem ooeoWord_not_monochrome : ¬ isMonochrome ooeoWord := by
  rintro (h | h) <;> simp [ooeoWord] at h

theorem oooeWord_not_monochrome : ¬ isMonochrome oooeWord := by
  rintro (h | h) <;> simp [oooeWord] at h

theorem firstDefect_OOE_le_one {n : ℕ} (hw : follows n ooeWord) :
    firstDefect n ooeWord ≤ 1 := by
  rw [ooeWord_decompose] at hw ⊢
  have h :=
    firstDefect_lt_of_odd_run_then_even (n := n) (odds := 2) (w := [])
      (by decide) (by simpa using hw)
  omega

theorem firstDefect_OOEO_le_one {n : ℕ} (hw : follows n ooeoWord) :
    firstDefect n ooeoWord ≤ 1 := by
  rw [ooeoWord_decompose] at hw ⊢
  have h :=
    firstDefect_lt_of_odd_run_then_even (n := n) (odds := 2)
      (w := [Branch.odd]) (by decide) (by simpa using hw)
  omega

theorem firstDefect_OOOE_le_two {n : ℕ} (hw : follows n oooeWord) :
    firstDefect n oooeWord ≤ 2 := by
  rw [oooeWord_decompose] at hw ⊢
  have h :=
    firstDefect_lt_of_odd_run_then_even (n := n) (odds := 3) (w := [])
      (by decide) (by simpa using hw)
  omega

theorem powGap_mono_addend {a ρ₁ ρ₂ e : ℕ} (h : ρ₁ ≤ ρ₂) :
    powGap a ρ₁ e ≤ powGap a ρ₂ e := by
  have : (a + ρ₁) ^ e ≤ (a + ρ₂) ^ e :=
    Nat.pow_le_pow_left (Nat.add_le_add_left h a) e
  exact Nat.sub_le_sub_right this (a ^ e)

theorem add_pow_three (x y : ℕ) :
    (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  ring

/-- Exact cubic lift of an already-inserted defect. -/
theorem odd_defect_lift (scale D : ℕ) :
    powGap scale D 3 = 3 * scale ^ 2 * D + 3 * scale * D ^ 2 + D ^ 3 := by
  have hexp := add_pow_three scale D
  have hsum :
      scale ^ 3 + (3 * scale ^ 2 * D + 3 * scale * D ^ 2 + D ^ 3) =
        (scale + D) ^ 3 := by
    rw [hexp]
    ac_rfl
  rw [powGap, ← hsum, Nat.add_sub_cancel_left]

/-- Universal odd-step lower bound. The factor `3` is sharp as `D/scale → 0`. -/
theorem odd_defect_lift_lower_bound (scale D : ℕ) :
    3 * scale ^ 2 * D ≤ powGap scale D 3 := by
  rw [odd_defect_lift, add_assoc]
  exact Nat.le_add_right _ _

theorem powGap_one (a ρ : ℕ) : powGap a ρ 1 = ρ := by
  simp [powGap]

/-- Suffix lift of an already-inserted defect. Later remainders are dropped. -/
def amplifyDefect (current D k : ℕ) : List Branch → ℕ
  | [] => D
  | .even :: w => amplifyDefect (floorPower current) D (k + 1) w
  | .odd :: w =>
      amplifyDefect (floorPower current) (powGap (current ^ (2 ^ k)) D 3)
        (k + 1) w

theorem amplifyDefect_ge (current D k : ℕ) :
    ∀ w, D ≤ amplifyDefect current D k w
  | [] => le_rfl
  | .even :: w => amplifyDefect_ge (floorPower current) D (k + 1) w
  | .odd :: w =>
      le_trans (powGap_ge (by decide : (1 : ℕ) ≤ 3))
        (amplifyDefect_ge _ _ _ w)

theorem amplifyDefect_mono (current : ℕ) {D₁ D₂ : ℕ} (k : ℕ) (h : D₁ ≤ D₂) :
    ∀ w, amplifyDefect current D₁ k w ≤ amplifyDefect current D₂ k w
  | [] => h
  | .even :: w => amplifyDefect_mono (floorPower current) (k + 1) h w
  | .odd :: w =>
      amplifyDefect_mono (floorPower current) (k + 1) (powGap_mono_addend h) w

theorem accumulatedDefect_mono (current : ℕ) {D₁ D₂ : ℕ} (k : ℕ) (h : D₁ ≤ D₂) :
    ∀ w, accumulatedDefect current D₁ k w ≤ accumulatedDefect current D₂ k w
  | [] => h
  | .even :: w => by
      have hD :
          accumulateEven D₁ (localDefectEven current) (floorPower current) k ≤
            accumulateEven D₂ (localDefectEven current) (floorPower current) k :=
        Nat.add_le_add_right h _
      exact accumulatedDefect_mono (floorPower current) (k + 1) hD w
  | .odd :: w => by
      have hD :
          accumulateOdd D₁ (localDefectOdd current) current (floorPower current) k ≤
            accumulateOdd D₂ (localDefectOdd current) current
              (floorPower current) k :=
        Nat.add_le_add_left (powGap_mono_addend h) _
      exact accumulatedDefect_mono (floorPower current) (k + 1) hD w

theorem amplifyDefect_le_accumulated (current D k : ℕ) :
    ∀ w, amplifyDefect current D k w ≤ accumulatedDefect current D k w
  | [] => le_rfl
  | .even :: w => by
      have hle :
          D ≤ accumulateEven D (localDefectEven current) (floorPower current) k :=
        accumulateEven_ge _ _ _ _
      exact le_trans
        (amplifyDefect_le_accumulated (floorPower current) D (k + 1) w)
        (accumulatedDefect_mono (floorPower current) (k + 1) hle w)
  | .odd :: w => by
      have hle :
          powGap (current ^ (2 ^ k)) D 3 ≤
            accumulateOdd D (localDefectOdd current) current
              (floorPower current) k :=
        Nat.le_add_left _ _
      exact le_trans
        (amplifyDefect_le_accumulated (floorPower current)
          (powGap (current ^ (2 ^ k)) D 3) (k + 1) w)
        (accumulatedDefect_mono (floorPower current) (k + 1) hle w)

theorem amplifyDefect_odd_ge_triple (current D k : ℕ) (w : List Branch) :
    amplifyDefect (floorPower current)
        (3 * (current ^ (2 ^ k)) ^ 2 * D) (k + 1) w ≤
      amplifyDefect current D k (Branch.odd :: w) :=
  amplifyDefect_mono (floorPower current) (k + 1)
    (odd_defect_lift_lower_bound _ _) w

theorem accumulatedDefect_of_tight_prefix {current k : ℕ} :
    ∀ u v, localsTight current u →
      accumulatedDefect current 0 k (u ++ v) =
        accumulatedDefect (image current u) 0 (k + u.length) v
  | [], v, _ => by simp [accumulatedDefect, image]
  | .even :: u, v, ht => by
      have hρ : localDefectEven current = 0 := by
        simpa [branchDefect] using branchDefect_eq_zero_of_localTight ht.1
      have hD :
          accumulateEven 0 (localDefectEven current) (floorPower current) k = 0 := by
        simp [accumulateEven, hρ]
      simp [accumulatedDefect, List.cons_append, image, hD]
      have ih :=
        accumulatedDefect_of_tight_prefix (current := floorPower current)
          (k := k + 1) u v ht.2
      have hk : k + 1 + u.length = k + (u.length + 1) := by omega
      simpa [hk] using ih
  | .odd :: u, v, ht => by
      have hρ : localDefectOdd current = 0 := by
        simpa [branchDefect] using branchDefect_eq_zero_of_localTight ht.1
      have hD :
          accumulateOdd 0 (localDefectOdd current) current (floorPower current) k =
            0 := by
        simp [accumulateOdd, hρ]
      simp [accumulatedDefect, List.cons_append, image, hD]
      have ih :=
        accumulatedDefect_of_tight_prefix (current := floorPower current)
          (k := k + 1) u v ht.2
      have hk : k + 1 + u.length = k + (u.length + 1) := by omega
      simpa [hk] using ih

theorem globalDefect_eq_accumulated_drop {n : ℕ} {w : List Branch} {j : ℕ}
    (_hw : follows n w) (ht : localsTight n (w.take j)) (hj : j ≤ w.length) :
    globalDefect n w =
      accumulatedDefect (floorPower^[j] n) 0 j (w.drop j) := by
  have hsplit : w.take j ++ w.drop j = w := List.take_append_drop j w
  have himg : image n (w.take j) = floorPower^[j] n := image_take_of_le hj
  have h :=
    accumulatedDefect_of_tight_prefix (current := n) (k := 0)
      (w.take j) (w.drop j) ht
  have hlen : (w.take j).length = j := List.length_take_of_le hj
  simpa [globalDefect, hsplit, himg, hlen] using h

theorem accumulate_first_step (current k : ℕ) (b : Branch) (w : List Branch) :
    accumulatedDefect current 0 k (b :: w) =
      accumulatedDefect (floorPower current)
        (powGap (floorPower current ^ 2) (branchDefect b current) (2 ^ k))
        (k + 1) w := by
  cases b with
  | even =>
      simp [accumulatedDefect, accumulateEven, branchDefect]
  | odd =>
      simp [accumulatedDefect, accumulateOdd, branchDefect]

/-- After the first defect, the remaining suffix cannot shrink that
contribution below the zero-remainder lift. -/
theorem global_defect_lower_bound {n : ℕ} {w : List Branch}
    (hw : follows n w) (hpos : firstDefect n w < w.length) :
    amplifyDefect (floorPower (floorPower^[firstDefect n w] n))
        ((branchDefect w[firstDefect n w]
            (floorPower^[firstDefect n w] n)) ^
          (2 ^ firstDefect n w))
        (firstDefect n w + 1) (w.drop (firstDefect n w + 1)) ≤
      globalDefect n w := by
  set j := firstDefect n w
  have hj : j ≤ w.length := firstDefect_le_length n w
  have ht := firstDefect_prefix_tight hw
  have hacc := globalDefect_eq_accumulated_drop hw ht hj
  have hdrop : w.drop j = w[j] :: w.drop (j + 1) :=
    List.drop_eq_getElem_cons hpos
  have hstep :=
    accumulate_first_step (floorPower^[j] n) j w[j] (w.drop (j + 1))
  have hD :
      (branchDefect w[j] (floorPower^[j] n)) ^ (2 ^ j) ≤
        powGap (floorPower (floorPower^[j] n) ^ 2)
          (branchDefect w[j] (floorPower^[j] n)) (2 ^ j) :=
    powGap_ge_pow Nat.one_le_two_pow
  have hamp :=
    amplifyDefect_le_accumulated
      (floorPower (floorPower^[j] n))
      (powGap (floorPower (floorPower^[j] n) ^ 2)
        (branchDefect w[j] (floorPower^[j] n)) (2 ^ j))
      (j + 1) (w.drop (j + 1))
  have hmono :=
    amplifyDefect_mono (floorPower (floorPower^[j] n)) (j + 1) hD
      (w.drop (j + 1))
  have hchain :
      amplifyDefect (floorPower (floorPower^[j] n))
          ((branchDefect w[j] (floorPower^[j] n)) ^ (2 ^ j))
          (j + 1) (w.drop (j + 1)) ≤
        accumulatedDefect (floorPower (floorPower^[j] n))
          (powGap (floorPower (floorPower^[j] n) ^ 2)
            (branchDefect w[j] (floorPower^[j] n)) (2 ^ j))
          (j + 1) (w.drop (j + 1)) :=
    le_trans hmono hamp
  rw [hacc, hdrop, hstep]
  exact hchain

def defectScale (current k : ℕ) : ℕ :=
  current ^ (2 ^ k)

/-- Normalized pair `(D, current^{2^k})`. The ratio is the natural
dimensionless defect; Lean keeps both sides as natural numbers. -/
def normalizedDefect (current D k : ℕ) : ℕ × ℕ :=
  (D, defectScale current k)

theorem defectScale_even_tight {current k : ℕ}
    (h : floorPower current ^ 2 = current) :
    defectScale (floorPower current) (k + 1) = defectScale current k := by
  simp [defectScale]
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  rw [h2, pow_mul, h]

theorem defectScale_odd_tight {current k : ℕ}
    (h : floorPower current ^ 2 = current ^ 3) :
    defectScale (floorPower current) (k + 1) = (defectScale current k) ^ 3 := by
  simp [defectScale]
  have h2 := pow_sq_pow (floorPower current) k
  rw [← h2, h, ← Nat.pow_mul, mul_comm, Nat.pow_mul]

/-- Tight even preserves the pair. Tight odd cubes the scale and
replaces `D` by the cubic lift. -/
theorem normalizedDefect_step {current D k : ℕ} :
    (floorPower current ^ 2 = current →
        normalizedDefect (floorPower current) D (k + 1) =
          normalizedDefect current D k) ∧
      (floorPower current ^ 2 = current ^ 3 →
        normalizedDefect (floorPower current)
            (powGap (defectScale current k) D 3) (k + 1) =
          (powGap (defectScale current k) D 3, (defectScale current k) ^ 3)) := by
  constructor
  · intro h
    simp [normalizedDefect, defectScale_even_tight h]
  · intro h
    simp [normalizedDefect, defectScale_odd_tight h]

theorem even_sq_mod_four {n : ℕ} (h : n % 2 = 0) : n ^ 2 % 4 = 0 := by
  have hn : n % 4 = 0 ∨ n % 4 = 2 := by omega
  rcases hn with h4 | h4
  · rw [Nat.pow_mod, h4]
  · rw [Nat.pow_mod, h4]

theorem odd_sq_mod_four {n : ℕ} (h : n % 2 = 1) : n ^ 2 % 4 = 1 := by
  have hn : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases hn with h4 | h4
  · rw [Nat.pow_mod, h4]
  · rw [Nat.pow_mod, h4]

theorem sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · exact Or.inl (even_sq_mod_four h)
  · exact Or.inr (odd_sq_mod_four h)

theorem not_square_of_two_mod_four {x : ℕ} (h : x % 4 = 2) :
    x.sqrt ^ 2 ≠ x := by
  intro hs
  have hx : x.sqrt ^ 2 % 4 = 2 := by
    rw [hs]
    exact h
  have hsq := sq_mod_four x.sqrt
  omega

theorem localDefectEven_two_mod_four_pos {x : ℕ} (h : x % 4 = 2) :
    0 < localDefectEven x := by
  have heven : x % 2 = 0 := by omega
  rw [localDefectEven_eq heven]
  have hne := not_square_of_two_mod_four h
  have hle : x.sqrt ^ 2 ≤ x := by simpa [pow_two] using Nat.sqrt_le x
  omega

/-- Scale-free residue bound: an even successor of an `x ≡ 2 (mod 4)`
state forces remainder at least `2`. -/
theorem conditional_remainder_lower_bound {x : ℕ}
    (h : x % 4 = 2) (hy : floorPower x % 2 = 0) :
    2 ≤ localDefectEven x := by
  have heven : x % 2 = 0 := by omega
  rw [localDefectEven_eq heven]
  have hle : x.sqrt ^ 2 ≤ x := by simpa [pow_two] using Nat.sqrt_le x
  have hy' : floorPower x = x.sqrt := floorPower_even_eq heven
  have hsq4 : x.sqrt ^ 2 % 4 = 0 := by
    rw [← hy']
    exact even_sq_mod_four hy
  obtain ⟨a, ha⟩ : ∃ a, x = 4 * a + 2 := ⟨x / 4, by omega⟩
  have hdiv : 4 ∣ x.sqrt ^ 2 := (Nat.dvd_iff_mod_eq_zero).mpr hsq4
  obtain ⟨b, hb⟩ := hdiv
  have : x - x.sqrt ^ 2 = 4 * (a - b) + 2 := by
    have : 4 * b ≤ 4 * a + 2 := by
      rw [← hb, ← ha]
      exact hle
    omega
  omega

theorem odd_sq_mod_eight {n : ℕ} (h : n % 2 = 1) : n ^ 2 % 8 = 1 := by
  have hn : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases hn with h8 | h8 | h8 | h8
  · rw [Nat.pow_mod, h8]
  · rw [Nat.pow_mod, h8]
  · rw [Nat.pow_mod, h8]
  · rw [Nat.pow_mod, h8]

theorem sq_mod_eight (n : ℕ) :
    n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  have _hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  interval_cases hn : n % 8
  · exact Or.inl (by rw [Nat.pow_mod, hn])
  · exact Or.inr (Or.inl (by rw [Nat.pow_mod, hn]))
  · exact Or.inr (Or.inr (by rw [Nat.pow_mod, hn]))
  · exact Or.inr (Or.inl (by rw [Nat.pow_mod, hn]))
  · exact Or.inl (by rw [Nat.pow_mod, hn])
  · exact Or.inr (Or.inl (by rw [Nat.pow_mod, hn]))
  · exact Or.inr (Or.inr (by rw [Nat.pow_mod, hn]))
  · exact Or.inr (Or.inl (by rw [Nat.pow_mod, hn]))

theorem localDefectOdd_three_mod_eight {x : ℕ} (h : x % 8 = 3) :
    2 ≤ localDefectOdd x := by
  have hodd : x % 2 = 1 := by omega
  rw [localDefectOdd_eq hodd]
  have hle : (x ^ 3).sqrt ^ 2 ≤ x ^ 3 := by
    simpa [pow_two] using Nat.sqrt_le (x ^ 3)
  have hx3 : x ^ 3 % 8 = 3 := by
    rw [Nat.pow_mod, h]
  obtain ⟨a, ha⟩ : ∃ a, x ^ 3 = 8 * a + 3 := ⟨x ^ 3 / 8, by omega⟩
  rcases sq_mod_eight (x ^ 3).sqrt with h0 | h1 | h4
  · have hdiv : 8 ∣ (x ^ 3).sqrt ^ 2 := (Nat.dvd_iff_mod_eq_zero).mpr h0
    obtain ⟨b, hb⟩ := hdiv
    have : x ^ 3 - (x ^ 3).sqrt ^ 2 = 8 * (a - b) + 3 := by
      have : 8 * b ≤ 8 * a + 3 := by
        rw [← hb, ← ha]
        exact hle
      omega
    omega
  · obtain ⟨b, hb⟩ : ∃ b, (x ^ 3).sqrt ^ 2 = 8 * b + 1 :=
      ⟨(x ^ 3).sqrt ^ 2 / 8, by omega⟩
    have : x ^ 3 - (x ^ 3).sqrt ^ 2 = 8 * (a - b) + 2 := by
      have : 8 * b + 1 ≤ 8 * a + 3 := by
        rw [← hb, ← ha]
        exact hle
      omega
    omega
  · obtain ⟨b, hb⟩ : ∃ b, (x ^ 3).sqrt ^ 2 = 8 * b + 4 :=
      ⟨(x ^ 3).sqrt ^ 2 / 8, by omega⟩
    have : x ^ 3 - (x ^ 3).sqrt ^ 2 = 8 * (a - b - 1) + 7 := by
      have : 8 * b + 4 ≤ 8 * a + 3 := by
        rw [← hb, ← ha]
        exact hle
      omega
    omega

theorem localDefectOdd_seven_mod_eight {x : ℕ} (h : x % 8 = 7) :
    3 ≤ localDefectOdd x := by
  have hodd : x % 2 = 1 := by omega
  rw [localDefectOdd_eq hodd]
  have hle : (x ^ 3).sqrt ^ 2 ≤ x ^ 3 := by
    simpa [pow_two] using Nat.sqrt_le (x ^ 3)
  have hx3 : x ^ 3 % 8 = 7 := by
    rw [Nat.pow_mod, h]
  obtain ⟨a, ha⟩ : ∃ a, x ^ 3 = 8 * a + 7 := ⟨x ^ 3 / 8, by omega⟩
  rcases sq_mod_eight (x ^ 3).sqrt with h0 | h1 | h4
  · have hdiv : 8 ∣ (x ^ 3).sqrt ^ 2 := (Nat.dvd_iff_mod_eq_zero).mpr h0
    obtain ⟨b, hb⟩ := hdiv
    have : x ^ 3 - (x ^ 3).sqrt ^ 2 = 8 * (a - b) + 7 := by
      have : 8 * b ≤ 8 * a + 7 := by
        rw [← hb, ← ha]
        exact hle
      omega
    omega
  · obtain ⟨b, hb⟩ : ∃ b, (x ^ 3).sqrt ^ 2 = 8 * b + 1 :=
      ⟨(x ^ 3).sqrt ^ 2 / 8, by omega⟩
    have : x ^ 3 - (x ^ 3).sqrt ^ 2 = 8 * (a - b) + 6 := by
      have : 8 * b + 1 ≤ 8 * a + 7 := by
        rw [← hb, ← ha]
        exact hle
      omega
    omega
  · obtain ⟨b, hb⟩ : ∃ b, (x ^ 3).sqrt ^ 2 = 8 * b + 4 :=
      ⟨(x ^ 3).sqrt ^ 2 / 8, by omega⟩
    have : x ^ 3 - (x ^ 3).sqrt ^ 2 = 8 * (a - b) + 3 := by
      have : 8 * b + 4 ≤ 8 * a + 7 := by
        rw [← hb, ← ha]
        exact hle
      omega
    omega

theorem amplifyDefect_OOE_j_zero (n ρ : ℕ) :
    amplifyDefect (floorPower n) ρ 1 [Branch.odd, Branch.even] =
      powGap (floorPower n ^ 2) ρ 3 :=
  rfl

theorem globalDefect_OOE_eq (n : ℕ) :
    globalDefect n ooeWord =
      accumulatedDefect (floorPower n) (localDefectOdd n) 1
        [Branch.odd, Branch.even] := by
  simp [globalDefect, ooeWord, accumulatedDefect, accumulateOdd,
    powGap_zero_addend, powGap_one, branchDefect]

theorem globalDefect_OOE_of_j_zero {n : ℕ}
    (_hw : follows n ooeWord) (_hj : firstDefect n ooeWord = 0) :
    3 * floorPower n ^ 4 * localDefectOdd n ≤ globalDefect n ooeWord := by
  have hamp :
      amplifyDefect (floorPower n) (localDefectOdd n) 1
          [Branch.odd, Branch.even] ≤
        accumulatedDefect (floorPower n) (localDefectOdd n) 1
          [Branch.odd, Branch.even] :=
    amplifyDefect_le_accumulated _ _ _ _
  have hexact := amplifyDefect_OOE_j_zero n (localDefectOdd n)
  have hge : 3 * (floorPower n ^ 2) ^ 2 * localDefectOdd n ≤
      powGap (floorPower n ^ 2) (localDefectOdd n) 3 :=
    odd_defect_lift_lower_bound _ _
  have hpow : (floorPower n ^ 2) ^ 2 = floorPower n ^ 4 := by
    rw [← Nat.pow_mul]
  have : 3 * floorPower n ^ 4 * localDefectOdd n ≤
      amplifyDefect (floorPower n) (localDefectOdd n) 1
        [Branch.odd, Branch.even] := by
    rw [hexact, ← hpow]
    exact hge
  exact le_trans this (hamp.trans (globalDefect_OOE_eq n).ge)

theorem globalDefect_OOE_of_j_one {n : ℕ}
    (hw : follows n ooeWord) (hj : firstDefect n ooeWord = 1) :
    localDefectOdd (floorPower n) ^ 2 ≤ globalDefect n ooeWord := by
  have hlen : ooeWord.length = 3 := rfl
  have hpos : firstDefect n ooeWord < ooeWord.length := by
    simpa [hj, hlen]
  have hbound := firstDefect_contribution hw hpos
  have hget : ooeWord[1] = Branch.odd := rfl
  have hiter : floorPower^[1] n = floorPower n := by
    simp [Function.iterate_one]
  simpa [hj, hget, hiter, branchDefect] using hbound

/-- Conditional lower bound for the previously difficult mixed class `OOE`.
This does not claim the bound exceeds the formal surplus. -/
theorem expanding_defect_lower_bound {n : ℕ} (hw : follows n ooeWord) :
    (firstDefect n ooeWord = 0 ∧
        3 * floorPower n ^ 4 * localDefectOdd n ≤ globalDefect n ooeWord) ∨
      (firstDefect n ooeWord = 1 ∧
        localDefectOdd (floorPower n) ^ 2 ≤ globalDefect n ooeWord) := by
  have hle := firstDefect_OOE_le_one hw
  have _hpos : firstDefect n ooeWord < ooeWord.length :=
    firstDefect_lt_of_mixed hw ooeWord_not_monochrome
  interval_cases hfd : firstDefect n ooeWord
  · exact Or.inl ⟨rfl, globalDefect_OOE_of_j_zero hw hfd⟩
  · exact Or.inr ⟨rfl, globalDefect_OOE_of_j_one hw hfd⟩

/-- Negative control: `Δ > n^{3^o} - n^{2^k}` is exactly `T_w(n) < n`. -/
theorem global_defect_le_surplus_of_expanding {n : ℕ} {w : List Branch}
    (hw : follows n w) (hge : n ≤ image n w) :
    globalDefect n w + n ^ (2 ^ w.length) ≤ n ^ (3 ^ oddCount w) := by
  have hid := global_defect_identity hw
  have hpow :
      n ^ (2 ^ w.length) ≤ image n w ^ (2 ^ w.length) :=
    Nat.pow_le_pow_left hge _
  have :
      globalDefect n w + n ^ (2 ^ w.length) ≤
        globalDefect n w + image n w ^ (2 ^ w.length) :=
    Nat.add_le_add_left hpow _
  exact le_trans this (add_comm (globalDefect n w) _ ▸ hid.symm.le)

end Problems.Juggler
