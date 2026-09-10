import Problems.Juggler.ReturnSeams

namespace Problems.Juggler.ReturnSeams

theorem image_oe_eq {x : ℕ} (h : follows x [.odd, .even]) :
    image x [.odd, .even] = ReturnCells.oe x := by
  simp only [image_cons, image_nil]
  rw [floorPower_even_eq h.2.1, floorPower_odd_eq h.1]
  rfl

theorem image_ooe_eq {x : ℕ} (h : follows x [.odd, .odd, .even]) :
    image x [.odd, .odd, .even] = ReturnCells.ooe x := by
  simp only [image_cons, image_nil]
  rw [floorPower_even_eq h.2.2.1, floorPower_odd_eq h.2.1, floorPower_odd_eq h.1]
  rfl

theorem image_oe_lt {x : ℕ} (hx : 3 ≤ x) (h : follows x [.odd, .even]) :
    image x [.odd, .even] < x := by
  rw [image_oe_eq h]
  have hcell := (ReturnCells.oe_cell x).1
  have hxpos : 0 < x ^ 3 := pow_pos (by omega) _
  have hxp : x ^ 3 < x ^ 4 := by
    have he : x ^ 4 = x ^ 3 * x := by ring
    nlinarith
  by_contra hn
  have hh := Nat.pow_le_pow_left (show x ≤ ReturnCells.oe x by omega) 4
  omega

theorem image_ooe_gt {x : ℕ} (hx : 5 ≤ x) (h : follows x [.odd, .odd, .even]) :
    x < image x [.odd, .odd, .even] := by
  rw [image_ooe_eq h]
  simpa [ReturnCells.ooe, ReturnCells.oe, CubicReturn.O] using CubicReturn.ooe_gt hx

/-- The OOE/OE section follows from actual one-letter rank branches. -/
theorem RankedReturn.ooe_oe_section {o e m : ℕ} {y : ℕ → ℕ}
    (h : RankedReturn o e y [.odd] [.even]) (ho : 0 < o) (he : 0 < e)
    (hm : 5 ≤ m) (hy : m ≤ y 0) :
    ∃ a b, 0 < a ∧ 0 < b ∧ o = 2 * a + b ∧ e = a + b ∧
      RankedReturn a b y [.odd, .odd, .even] [.odd, .even] ∧
      (∀ i, i < a + b → y i % 2 = 1) := by
  have heo : e < o := h.lt_of_concat_decreases hy ho (by
    intro x hx hf
    exact image_oe_lt (by omega) hf)
  have h₁ := h.left heo.le
  have hsmall : o - e < e := h₁.lt_of_concat_grows hy he (by
    intro x hx hf
    exact image_ooe_gt (by omega) hf)
  have h₂ := h₁.right hsmall.le
  refine ⟨o - e, e - (o - e), by omega, by omega, by omega, by omega, h₂, ?_⟩
  intro i hi
  exact (h.lower i (by omega)).1.1

/-- A harmless extension lets all induced prefixes keep the same rank function. -/
def extendRanks {L : ℕ} (c : Fin L → ℕ) (i : ℕ) : ℕ :=
  if hi : i < L then c ⟨i, hi⟩ else 0

theorem extendRanks_apply {L : ℕ} (c : Fin L → ℕ) (i : Fin L) :
    extendRanks c i.val = c i := by simp [extendRanks, i.isLt]

theorem rankStep_mod {a b i : ℕ} (hi : i < a + b) :
    ReturnInduction.rankStep a b i = (i + b) % (a + b) := by
  by_cases hia : i < a
  · simp [ReturnInduction.rankStep, hia, Nat.mod_eq_of_lt (show i + b < a + b by omega)]
  · have he : i + b = (i - a) + (a + b) := by omega
    have hi' : i - a < a + b := by omega
    simp [ReturnInduction.rankStep, hia, he, Nat.mod_eq_of_lt hi']

/-- Actual sorted cubic permutations supply all one-letter guards and rank equations. -/
theorem rankedReturn_of_sorted_cubic {m L o : ℕ} (ho : o ≤ L)
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand m (c i))
    (hcut : ∀ i, c i < m ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (p i) = floorPower (c i)) :
    RankedReturn o (L - o) (extendRanks c) [.odd] [.even] := by
  have hlen : o + (L - o) = L := Nat.add_sub_of_le ho
  have hrot := cubicBand_rank_rotation ho c hc p hband hcut hstep
  have hpar : ∀ i, c i % 2 = 1 ↔ i.val < o := by
    intro i
    have hn := cubicBand_parity_iff (hband i) (by simpa [hstep i] using hband (p i))
    exact hn.trans (hcut i)
  have hnext : ∀ i : Fin L,
      floorPower (c i) = extendRanks c (ReturnInduction.rankStep o (L - o) i.val) := by
    intro i
    rw [rankStep_mod (by simp [hlen]), hlen, ← hrot i]
    rw [extendRanks_apply, hstep]
  constructor
  · intro i j hij hj
    have hjL : j < L := by omega
    have hiL : i < L := by omega
    simpa only [extendRanks, dif_pos hiL, dif_pos hjL] using
      hc (show (⟨i, hiL⟩ : Fin L) < ⟨j, hjL⟩ from hij)
  · intro i hi
    have hiL : i < L := by omega
    let j : Fin L := ⟨i, hiL⟩
    have hj : extendRanks c i = c j := by simp [extendRanks, hiL, j]
    refine ⟨?_, ?_⟩
    · exact ⟨by rw [hj]; exact (hpar j).mpr hi, trivial⟩
    · simpa [image, hj, j, ReturnInduction.rankStep, hi] using hnext j
  · intro i hi hin
    have hiL : i < L := by omega
    let j : Fin L := ⟨i, hiL⟩
    have hj : extendRanks c i = c j := by simp [extendRanks, hiL, j]
    refine ⟨?_, ?_⟩
    · have hn : c j % 2 ≠ 1 := by
        intro hp
        have := (hpar j).mp hp
        change i < o at this
        omega
      exact ⟨by rw [hj]; omega, trivial⟩
    · simpa [image, hj, j, ReturnInduction.rankStep, show ¬i < o by omega] using hnext j

/-- Sorting an actual bounded periodic set constructs the guarded return section. -/
theorem periodicExtrema_return_model {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 3) :
    ∃ a b y, 0 < a ∧ 0 < b ∧ y 0 = m ∧ y (a + b - 1) = M.sqrt ∧
      RankedReturn a b y [.odd, .odd, .even] [.odd, .even] ∧
      (∀ i, i < a + b → y i ∈ C ∧ y i % 2 = 1) := by
  classical
  let s := (Finset.Icc m M).filter (fun x => x ∈ C)
  have hs : ∀ x, x ∈ s ↔ x ∈ C := by
    intro x
    simp only [s, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun h => h.2, fun h => ⟨D.bounds x h, h⟩⟩
  have hL : 0 < s.card := Finset.card_pos.mpr ⟨m, (hs m).mpr D.min_mem⟩
  let c : Fin s.card → ℕ := s.orderEmbOfFin rfl
  have hc : StrictMono c := (s.orderEmbOfFin rfl).strictMono
  have hcC : ∀ i, c i ∈ C := fun i =>
    (hs (c i)).mp (s.orderEmbOfFin_mem rfl i)
  have hclosed : ∀ x ∈ s, floorPower x ∈ s := fun x hx =>
    (hs _).mpr (D.closed x ((hs x).mp hx))
  have hinj : Set.InjOn floorPower s := by
    intro x hx y hy he
    exact D.inj ((hs x).mp hx) ((hs y).mp hy) he
  obtain ⟨p, hstep⟩ := sorted_invariant_permutation s floorPower hclosed hinj
  change ∀ i, c (p i) = floorPower (c i) at hstep
  obtain ⟨o, ho, hcut, _⟩ := sorted_threshold_cut c hc (t := m ^ 2)
  have hband : ∀ i, InCubicBand m (c i) := fun i => D.band hM (hcC i)
  have hthreshold : ∀ i, c (p i) = thresholdMap m (c i) := by
    intro i
    rw [hstep, D.normalized hM (hcC i)]
  obtain ⟨hop, hoL⟩ := threshold_branch_count_bounds (by omega) hL ho c hc p
    hband hcut hthreshold
  have hr := rankedReturn_of_sorted_cubic ho c hc p hband hcut hstep
  let y := extendRanks c
  have hyC : ∀ i, i < s.card → y i ∈ C := by
    intro i hi
    simpa [y, extendRanks, hi] using hcC ⟨i, hi⟩
  have hy0 : y 0 = m := by
    have hmS := (hs m).mpr D.min_mem
    have hmin := s.min'_le m hmS
    have he := s.orderEmbOfFin_zero (h := rfl) hL
    have hb := (D.bounds _ (hyC 0 hL)).1
    have hy : y 0 = s.min' (Finset.card_pos.mp hL) := by
      simpa [y, extendRanks, hL, c] using he
    omega
  have hyLast : y (s.card - 1) = M := by
    have hMS := (hs M).mpr D.max_mem
    have hmax := s.le_max' M hMS
    have he := s.orderEmbOfFin_last (h := rfl) hL
    have hl : s.card - 1 < s.card := by omega
    have hb := (D.bounds _ (hyC _ hl)).2
    have hy : y (s.card - 1) = s.max' (Finset.card_pos.mp hL) := by
      simpa [y, extendRanks, hl, c] using he
    omega
  obtain ⟨a, b, ha, hb, hoab, heab, hreturn, hodd⟩ :=
    hr.ooe_oe_section hop (by omega) hm (by simp [y, hy0])
  have hmaxstep := (hr.upper (s.card - 1) (by omega) (by omega)).2
  have hlast : y (a + b - 1) = M.sqrt := by
    change floorPower (y (s.card - 1)) = y (s.card - 1 - o) at hmaxstep
    rw [hyLast, floorPower_even_eq (D.max_even (by omega))] at hmaxstep
    have hi : s.card - 1 - o = a + b - 1 := by omega
    simpa [hi] using hmaxstep.symm
  refine ⟨a, b, y, ha, hb, hy0, hlast, hreturn, ?_⟩
  intro i hi
  exact ⟨hyC i (by omega), hodd i hi⟩

end Problems.Juggler.ReturnSeams
