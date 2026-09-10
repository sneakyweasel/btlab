import Problems.Juggler.CubicReturn
import Problems.Juggler.ReturnRankedCycle

namespace Problems.Juggler.QuarticBand

open CubicReturn

def Low (m x : ℕ) : Prop := x < m ^ 2
def Section (m x : ℕ) : Prop := x < m ^ 2 ∧ m ^ 4 ≤ x ^ 3

instance (m x : ℕ) : Decidable (Section m x) := inferInstanceAs (Decidable (_ ∧ _))

variable {C : Set ℕ} {m M : ℕ}

theorem low_odd (D : PeriodicExtrema C m M) {x : ℕ}
    (hx : x ∈ C) (hl : x < m ^ 2) : x % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one x with he | ho
  · have hb := (D.bounds _ (D.closed _ hx)).1
    rw [floorPower_even_eq he] at hb
    have hs : x.sqrt < m := Nat.sqrt_lt.mpr (by simpa [pow_two] using hl)
    omega
  · exact ho

theorem min_odd (D : PeriodicExtrema C m M) (hm : 3 ≤ m) : m % 2 = 1 := by
  apply low_odd D D.min_mem
  nlinarith

theorem even_ge_square (D : PeriodicExtrema C m M) {x : ℕ}
    (hx : x ∈ C) (he : x % 2 = 0) : m ^ 2 ≤ x := by
  by_contra hn
  have := low_odd D hx (by omega)
  omega

theorem even_image_low (D : PeriodicExtrema C m M) (hM : M < m ^ 4)
    {x : ℕ} (hx : x ∈ C) (he : x % 2 = 0) :
    floorPower x < m ^ 2 := by
  rw [floorPower_even_eq he, Nat.sqrt_lt]
  have hb := (D.bounds _ hx).2.trans_lt hM
  nlinarith only [hb]

theorem high_odd_image_even (D : PeriodicExtrema C m M) (hm : 3 ≤ m)
    (hM : M < m ^ 4) {x : ℕ} (hx : x ∈ C)
    (ho : x % 2 = 1) (hh : m ^ 2 ≤ x) : (O x) % 2 = 0 := by
  have hmem : O x ∈ C := by simpa [floorPower_odd_eq ho, O] using D.closed _ hx
  have hlow : m ^ 3 ≤ O x := by
    apply Nat.le_sqrt.mpr
    have hp := Nat.pow_le_pow_left hh 3
    nlinarith only [hp]
  rcases Nat.mod_two_eq_zero_or_one (O x) with he | ho'
  · exact he
  · have hnext : O (O x) ∈ C := by
      have h := D.closed _ hmem
      rw [floorPower_odd_eq ho'] at h
      exact h
    have hbig : m ^ 4 ≤ O (O x) := by
      apply Nat.le_sqrt.mpr
      have hp := Nat.pow_le_pow_left hlow 3
      have hmpos : 0 < m := by omega
      have he : m ^ 8 ≤ m ^ 9 := Nat.pow_le_pow_right hmpos (by omega)
      nlinarith only [hp, he]
    have hb := (D.bounds _ hnext).2
    omega

theorem odd_image_mem (D : PeriodicExtrema C m M) {x : ℕ}
    (hx : x ∈ C) (ho : x % 2 = 1) : O x ∈ C := by
  simpa [floorPower_odd_eq ho, O] using D.closed _ hx

theorem first_image_high {x : ℕ} (hx : Section m x) : m ^ 2 ≤ O x := by
  apply Nat.le_sqrt.mpr
  nlinarith only [hx.2]

theorem low_oe_mem (D : PeriodicExtrema C m M) (hM : M < m ^ 4)
    {x : ℕ} (hx : x ∈ C) (hl : x < m ^ 2) (he : O x % 2 = 0) :
    ReturnCells.oe x ∈ C ∧ ReturnCells.oe x < m ^ 2 := by
  have hom := odd_image_mem D hx (low_odd D hx hl)
  have hm' := D.closed _ hom
  have hb := even_image_low D hM hom he
  rw [floorPower_even_eq he] at hm' hb
  exact ⟨hm', hb⟩

theorem section_ooe (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) {x : ℕ} (hx : x ∈ C)
    (hs : Section m x) (ho : O x % 2 = 1) :
    follows x [.odd, .odd, .even] ∧
    ReturnCells.ooe x ∈ C ∧ Section m (ReturnCells.ooe x) := by
  have hxo := low_odd D hx hs.1
  have hmem := odd_image_mem D hx hxo
  have he := high_odd_image_even D (by omega) hM hmem ho (first_image_high hs)
  have hnext := odd_image_mem D hmem ho
  have hlast := D.closed _ hnext
  have hlow := even_image_low D hM hnext he
  have hret : ReturnCells.ooe x = floorPower (O (O x)) := by
    rw [floorPower_even_eq he]
    rfl
  have hg : x < ReturnCells.ooe x := CubicReturn.ooe_gt (hm.trans (D.bounds _ hx).1)
  have hp := Nat.pow_le_pow_left hg.le 3
  refine ⟨?_, ?_, ?_, hs.2.trans hp⟩
  · change x % 2 = 1 ∧ floorPower x % 2 = 1 ∧
      floorPower (floorPower x) % 2 = 0 ∧ True
    rw [floorPower_odd_eq hxo]
    change x % 2 = 1 ∧ O x % 2 = 1 ∧ floorPower (O x) % 2 = 0 ∧ True
    rw [floorPower_odd_eq ho]
    exact ⟨hxo, ho, he, trivial⟩
  · simpa [hret] using hlast
  · simpa [hret] using hlow

theorem min_image_section (D : PeriodicExtrema C m M) (hm : 5 ≤ m) :
    O m ∈ C ∧ Section m (O m) := by
  have hmem := odd_image_mem D D.min_mem (min_odd D (by omega))
  have hl := CubicReturn.PeriodicExtrema.min_image_lower (by omega : 3 ≤ m)
  have hg := CubicReturn.ooe_gt hm
  have hs : (m + 1) ^ 2 ≤ O (O m) := by
    have hh := Nat.le_sqrt.mp (show m + 1 ≤ (O (O m)).sqrt by omega)
    nlinarith only [hh]
  have hp := Nat.pow_le_pow_left hs 2
  have ho := O_sq_le (O m)
  have hm4 : m ^ 4 ≤ (m + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  exact ⟨hmem, hl, by nlinarith only [hp, ho, hm4]⟩

theorem odd_high_forces_lower_cell (D : PeriodicExtrema C m M)
    (_hm : 3 ≤ m) (hM : M < m ^ 4) {x : ℕ}
    (hx : x ∈ C) (hs : Section m x) (ho : O x % 2 = 1) :
    (ReturnCells.oe x) ^ 3 < m ^ 4 := by
  have hmem := odd_image_mem D hx (low_odd D hx hs.1)
  have hnext := odd_image_mem D hmem ho
  have hcell : ReturnCells.oe x ^ 2 ≤ O x := by
    simpa [ReturnCells.oe, O] using Nat.sqrt_le' (O x)
  have hl : ReturnCells.oe x ^ 3 ≤ O (O x) := by
    apply Nat.le_sqrt.mpr
    have hp := Nat.pow_le_pow_left hcell 3
    nlinarith only [hp]
  exact hl.trans_lt ((D.bounds _ hnext).2.trans_lt hM)

theorem low_to_section (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    {x : ℕ} (hx : x ∈ C) (hl : x < m ^ 2) (hsmall : x ^ 3 < m ^ 4) :
    O x ∈ C ∧ Section m (O x) := by
  have hmem := odd_image_mem D hx (low_odd D hx hl)
  have hlow : O x < m ^ 2 := Nat.sqrt_lt.mpr (by nlinarith only [hsmall])
  have hmono : O m ≤ O x := Nat.sqrt_le_sqrt (Nat.pow_le_pow_left (D.bounds _ hx).1 3)
  have hp := Nat.pow_le_pow_left hmono 3
  exact ⟨hmem, hlow, (min_image_section D hm).2.2.trans hp⟩

theorem section_oeo (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) {x : ℕ} (hx : x ∈ C)
    (hs : Section m x) (he : O x % 2 = 0)
    (hsmall : (ReturnCells.oe x) ^ 3 < m ^ 4) :
    follows x [.odd, .even, .odd] ∧
    O (ReturnCells.oe x) ∈ C ∧ Section m (O (ReturnCells.oe x)) := by
  have hxo := low_odd D hx hs.1
  obtain ⟨hv, hvlow⟩ := low_oe_mem D hM hx hs.1 he
  have hvo := low_odd D hv hvlow
  refine ⟨?_, low_to_section D hm hv hvlow hsmall⟩
  change x % 2 = 1 ∧ floorPower x % 2 = 0 ∧
    floorPower (floorPower x) % 2 = 1 ∧ True
  rw [floorPower_odd_eq hxo]
  change x % 2 = 1 ∧ O x % 2 = 0 ∧ floorPower (O x) % 2 = 1 ∧ True
  rw [floorPower_even_eq he]
  exact ⟨hxo, he, hvo, trivial⟩

def returnMap (m x : ℕ) : ℕ :=
  if O x % 2 = 1 then ReturnCells.ooe x
  else if (ReturnCells.oe x) ^ 3 < m ^ 4 then O (ReturnCells.oe x)
  else ReturnCells.oe x

theorem returnMap_closed (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) {x : ℕ} (hx : x ∈ C) (hs : Section m x) :
    returnMap m x ∈ C ∧ Section m (returnMap m x) := by
  unfold returnMap
  split_ifs with ho hsmall
  · exact (section_ooe D hm hM hx hs ho).2
  · have he : O x % 2 = 0 := by omega
    exact (section_oeo D hm hM hx hs he hsmall).2
  · have he : O x % 2 = 0 := by omega
    obtain ⟨hr, hl⟩ := low_oe_mem D hM hx hs.1 he
    exact ⟨hr, hl, by omega⟩

theorem returnMap_eq_two_or_three (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) {x : ℕ} (hx : x ∈ C) (hs : Section m x) :
    returnMap m x = floorPower (floorPower x) ∨
    returnMap m x = floorPower (floorPower (floorPower x)) := by
  have hxo := low_odd D hx hs.1
  unfold returnMap
  split_ifs with ho hsmall
  · right
    have hom := odd_image_mem D hx hxo
    have he := high_odd_image_even D (by omega) hM hom ho (first_image_high hs)
    exact (ReturnCells.ooe_actual hxo ho he).symm
  · right
    have he : O x % 2 = 0 := by omega
    obtain ⟨hv, hl⟩ := low_oe_mem D hM hx hs.1 he
    have hvo := low_odd D hv hl
    rw [ReturnCells.oe_actual hxo he, floorPower_odd_eq hvo]
    rfl
  · left
    have he : O x % 2 = 0 := by omega
    exact (ReturnCells.oe_actual hxo he).symm

theorem two_steps_inj (D : PeriodicExtrema C m M) {x y : ℕ}
    (hx : x ∈ C) (hy : y ∈ C)
    (h : floorPower (floorPower x) = floorPower (floorPower y)) : x = y :=
  D.inj hx hy (D.inj (D.closed _ hx) (D.closed _ hy) h)

theorem returnMap_inj (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) {x y : ℕ} (hx : x ∈ C) (hy : y ∈ C)
    (hsx : Section m x) (hsy : Section m y)
    (h : returnMap m x = returnMap m y) : x = y := by
  have hhighx : m ^ 2 ≤ floorPower x := by
    rw [floorPower_odd_eq (low_odd D hx hsx.1)]
    exact first_image_high hsx
  have hhighy : m ^ 2 ≤ floorPower y := by
    rw [floorPower_odd_eq (low_odd D hy hsy.1)]
    exact first_image_high hsy
  rcases returnMap_eq_two_or_three D hm hM hx hsx with hx2 | hx3 <;>
    rcases returnMap_eq_two_or_three D hm hM hy hsy with hy2 | hy3
  · exact two_steps_inj D hx hy (hx2.symm.trans (h.trans hy2))
  · have hxy := two_steps_inj D hx (D.closed _ hy) (hx2.symm.trans (h.trans hy3))
    have hl := hsx.1
    omega
  · have hxy := two_steps_inj D (D.closed _ hx) hy (hx3.symm.trans (h.trans hy2))
    have hl := hsy.1
    omega
  · exact D.inj hx hy (two_steps_inj D (D.closed _ hx) (D.closed _ hy)
      (hx3.symm.trans (h.trans hy3)))

theorem guarded_return_cases (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) {x : ℕ} (hx : x ∈ C) (hs : Section m x) :
    (follows x [.odd, .odd, .even] ∧ returnMap m x = ReturnCells.ooe x) ∨
    (follows x [.odd, .even, .odd] ∧ returnMap m x = O (ReturnCells.oe x)) ∨
    (follows x [.odd, .even] ∧ returnMap m x = ReturnCells.oe x) := by
  unfold returnMap
  split_ifs with ho hsmall
  · exact Or.inl ⟨(section_ooe D hm hM hx hs ho).1, rfl⟩
  · have he : O x % 2 = 0 := by omega
    exact Or.inr (Or.inl ⟨(section_oeo D hm hM hx hs he hsmall).1, rfl⟩)
  · have he : O x % 2 = 0 := by omega
    have hxo := low_odd D hx hs.1
    refine Or.inr (Or.inr ⟨?_, rfl⟩)
    change x % 2 = 1 ∧ floorPower x % 2 = 0 ∧ True
    rw [floorPower_odd_eq hxo]
    exact ⟨hxo, he, trivial⟩

/-- The taller slab supplies a genuinely guarded F tower in the section. -/
theorem exists_F_source (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) (htall : m ^ 3 ≤ M) :
    ∃ x ∈ C, Section m x ∧ O x % 2 = 1 ∧ follows x [.odd, .odd, .even] := by
  have hmpos : 0 < m := by omega
  have hm23 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right hmpos (by omega)
  obtain ⟨h, hh, hhM⟩ := D.preimage D.max_mem
  have hho : h % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one h with he | ho
    · have hl := even_image_low D hM hh he
      rw [hhM] at hl
      omega
    · exact ho
  have hO : O h = M := by simpa [floorPower_odd_eq hho, O] using hhM
  have hhigh : m ^ 2 ≤ h := by
    by_contra hn
    have hp := Nat.pow_lt_pow_left (show h < m ^ 2 by omega) (by decide : 3 ≠ 0)
    have hmM := Nat.pow_le_pow_left htall 2
    have hsq := O_sq_le h
    rw [hO] at hsq
    nlinarith only [hp, hmM, hsq]
  obtain ⟨x, hx, hxh⟩ := D.preimage hh
  have hxo : x % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one x with he | ho
    · have hl := even_image_low D hM hx he
      rw [hxh] at hl
      omega
    · exact ho
  have hxO : O x = h := by simpa [floorPower_odd_eq hxo, O] using hxh
  have hlow : x < m ^ 2 := by
    by_contra hn
    have he := high_odd_image_even D (by omega) hM hx hxo (by omega)
    rw [hxO] at he
    omega
  have hcut : m ^ 4 ≤ x ^ 3 := by
    have hp := Nat.pow_le_pow_left hhigh 2
    have hsq := O_sq_le x
    rw [hxO] at hsq
    nlinarith only [hp, hsq]
  have hs : Section m x := ⟨hlow, hcut⟩
  have ho : O x % 2 = 1 := by simpa [hxO] using hho
  exact ⟨x, hx, hs, ho, (section_ooe D hm hM hx hs ho).1⟩

/-- Sorting the actual selected section gives a genuine guarded return permutation. -/
theorem sorted_return_model (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) :
    ∃ (e : ℕ) (c : Fin e → ℕ) (p : Equiv.Perm (Fin e)),
      0 < e ∧ StrictMono c ∧
      (∀ i, c i ∈ C ∧ Section m (c i)) ∧
      (∀ x ∈ C, Section m x → ∃ i, c i = x) ∧
      (∀ i, c (p i) = returnMap m (c i)) := by
  classical
  let S := (Finset.Icc m M).filter (fun x => x ∈ C ∧ Section m x)
  have hS : ∀ x, x ∈ S ↔ x ∈ C ∧ Section m x := by
    intro x
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun h => h.2, fun h => ⟨D.bounds _ h.1, h⟩⟩
  have hpos : 0 < S.card := Finset.card_pos.mpr
    ⟨O m, (hS _).mpr (min_image_section D hm)⟩
  have hclosed : ∀ x ∈ S, returnMap m x ∈ S := by
    intro x hx
    exact (hS _).mpr (returnMap_closed D hm hM ((hS x).mp hx).1 ((hS x).mp hx).2)
  have hinj : Set.InjOn (returnMap m) S := by
    intro x hx y hy h
    exact returnMap_inj D hm hM ((hS x).mp hx).1 ((hS y).mp hy).1
      ((hS x).mp hx).2 ((hS y).mp hy).2 h
  obtain ⟨p, hstep⟩ := sorted_invariant_permutation S (returnMap m) hclosed hinj
  refine ⟨S.card, S.orderEmbOfFin rfl, p, hpos, (S.orderEmbOfFin rfl).strictMono,
    ?_, ?_, hstep⟩
  · intro i
    exact (hS _).mp (S.orderEmbOfFin_mem rfl i)
  · intro x hx hs
    have hmem : x ∈ (S : Set ℕ) := (hS x).mpr ⟨hx, hs⟩
    rw [← S.range_orderEmbOfFin rfl] at hmem
    exact hmem

end Problems.Juggler.QuarticBand
