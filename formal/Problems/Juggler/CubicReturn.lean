import Problems.Juggler.CubicBand
import Problems.Juggler.ReturnCells
import Problems.Juggler.CycleExtrema

namespace Problems.Juggler.CubicReturn

def O (x : ℕ) : ℕ := (x ^ 3).sqrt

theorem O_sq_le (x : ℕ) : O x ^ 2 ≤ x ^ 3 := by
  simpa [O, pow_two] using Nat.sqrt_le (x ^ 3)

theorem lt_O_succ_sq (x : ℕ) : x ^ 3 < (O x + 1) ^ 2 := by
  simpa [O, pow_two] using Nat.lt_succ_sqrt (x ^ 3)

theorem sqrt_mul_le_O (x : ℕ) : x.sqrt * x ≤ O x := by
  apply Nat.le_sqrt.mpr
  have h := Nat.mul_le_mul_right (x ^ 2) (Nat.sqrt_le x)
  nlinarith

theorem sq_le_OO {x : ℕ} (hx : 3 ≤ x) : x ^ 2 ≤ O (O x) := by
  by_cases hx4 : x < 4
  · have he : x = 3 := by omega
    subst x
    decide +kernel
  let k := x.sqrt
  have hk : 2 ≤ k := Nat.le_sqrt.mpr (by omega)
  have hcell : x < (k + 1) ^ 2 := by
    simpa [k, pow_two] using Nat.lt_succ_sqrt x
  have hkx : x ≤ k ^ 3 := by
    have hprod : 0 ≤ k * (k - 2) * (k + 1) := Nat.zero_le _
    have hk2 : k - 2 + 2 = k := Nat.sub_add_cancel hk
    nlinarith
  have hmul := sqrt_mul_le_O x
  have hpow := Nat.pow_le_pow_left hmul 3
  have hxp := Nat.mul_le_mul_right (x ^ 3) hkx
  apply Nat.le_sqrt.mpr
  dsimp [k] at *
  nlinarith [show (x.sqrt * x) ^ 3 = x.sqrt ^ 3 * x ^ 3 by ring]

theorem ooe_gt {x : ℕ} (hx : 5 ≤ x) : x < (O (O x)).sqrt := by
  by_cases hx9 : x < 9
  · interval_cases x <;> decide +kernel
  let k := x.sqrt
  have hk : 3 ≤ k := Nat.le_sqrt.mpr (by omega)
  have hcell : x < (k + 1) ^ 2 := by
    simpa [k, pow_two] using Nat.lt_succ_sqrt x
  have hkx : x + 12 ≤ k ^ 3 := by
    have hk3 : k - 3 + 3 = k := Nat.sub_add_cancel hk
    have hp : 0 ≤ (k - 3) * (k ^ 2 + 2 * k + 4) := Nat.zero_le _
    nlinarith
  have hmul := sqrt_mul_le_O x
  have hpow := Nat.pow_le_pow_left hmul 3
  have hxp := Nat.mul_le_mul_right (x ^ 3) hkx
  have hg : (x + 1) ^ 4 ≤ O x ^ 3 := by
    have hp : 0 ≤ (x - 9) * x ^ 2 := Nat.zero_le _
    have hxsub : x - 9 + 9 = x := Nat.sub_add_cancel (by omega)
    have hid : (x.sqrt * x) ^ 3 = x.sqrt ^ 3 * x ^ 3 := by ring
    dsimp [k] at *
    nlinarith [sq_nonneg (x : ℤ)]
  have hfirst : (x + 1) ^ 2 ≤ O (O x) := by
    apply Nat.le_sqrt.mpr
    nlinarith
  have hsecond := Nat.le_sqrt.mpr (show (x + 1) * (x + 1) ≤ O (O x) by
    simpa [pow_two] using hfirst)
  omega

/-- A bounded invariant set of actual periodic states, with attained extrema. -/
structure PeriodicExtrema (C : Set ℕ) (m M : ℕ) : Prop where
  min_mem : m ∈ C
  max_mem : M ∈ C
  bounds : ∀ x ∈ C, m ≤ x ∧ x ≤ M
  closed : ∀ x ∈ C, floorPower x ∈ C
  periodic : C ⊆ Function.periodicPts floorPower

namespace PeriodicExtrema

variable {C : Set ℕ} {m M : ℕ} (D : PeriodicExtrema C m M)
include D

theorem inj : Set.InjOn floorPower C := by
  intro x hx y hy h
  exact periodicPoints_injOn floorPower (D.periodic hx) (D.periodic hy) h

theorem iter_mem {x : ℕ} (hx : x ∈ C) (k : ℕ) : floorPower^[k] x ∈ C := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact D.closed _ ih

theorem preimage {x : ℕ} (hx : x ∈ C) : ∃ y ∈ C, floorPower y = x := by
  obtain ⟨k, hk, hp⟩ := D.periodic hx
  refine ⟨floorPower^[k - 1] x, D.iter_mem hx _, ?_⟩
  rw [← Function.iterate_succ_apply' floorPower (k - 1) x,
    Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  exact hp

theorem band (hM : M < m ^ 3) {x : ℕ} (hx : x ∈ C) : InCubicBand m x :=
  ⟨(D.bounds _ hx).1, ((D.bounds _ hx).2).trans_lt hM⟩

theorem parity (hM : M < m ^ 3) {x : ℕ} (hx : x ∈ C) :
    x % 2 = 1 ↔ x < m ^ 2 :=
  cubicBand_parity_iff (D.band hM hx) (D.band hM (D.closed _ hx))

theorem normalized (hM : M < m ^ 3) {x : ℕ} (hx : x ∈ C) :
    floorPower x = thresholdMap m x :=
  cubicBand_floorPower_eq_threshold (D.band hM hx) (D.band hM (D.closed _ hx))

theorem even_of_upper (hM : M < m ^ 3) {x : ℕ} (hx : x ∈ C)
    (hupper : m ^ 2 ≤ x) : x % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one x with he | ho
  · exact he
  · have := (D.parity hM hx).mp ho
    omega

theorem min_odd (hm : 3 ≤ m) (hM : M < m ^ 3) : m % 2 = 1 := by
  apply (D.parity hM D.min_mem).mpr
  nlinarith

theorem max_even (hm : 3 ≤ m) : M % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one M with he | ho
  · exact he
  · have hg := floorPower_odd_gt (hm.trans (D.bounds _ D.max_mem).1) ho
    have hb := (D.bounds _ (D.closed _ D.max_mem)).2
    omega

theorem min_image_mem (hm : 3 ≤ m) (hM : M < m ^ 3) : O m ∈ C := by
  simpa [floorPower_odd_eq (D.min_odd hm hM), O] using D.closed _ D.min_mem

theorem max_image_mem (hm : 3 ≤ m) : M.sqrt ∈ C := by
  simpa [floorPower_even_eq (D.max_even hm)] using D.closed _ D.max_mem

omit D in
theorem min_image_lower (hm : 3 ≤ m) : O m < m ^ 2 := by
  rw [O, Nat.sqrt_lt]
  have hmpos : 0 < m ^ 3 := pow_pos (by omega) _
  have hprod := Nat.mul_lt_mul_of_pos_right (show 1 < m by omega) hmpos
  nlinarith

theorem even_image_lt_min_image (hm : 3 ≤ m) (hM : M < m ^ 3)
    {x : ℕ} (hx : x ∈ C) (he : x % 2 = 0) : x.sqrt < O m := by
  have hle : x.sqrt ≤ O m := Nat.sqrt_le_sqrt (Nat.le_of_lt (D.band hM hx).2)
  apply lt_of_le_of_ne hle
  intro heq
  have heqf : floorPower x = floorPower m := by
    rw [floorPower_even_eq he, floorPower_odd_eq (D.min_odd hm hM)]
    exact heq
  have hxm := D.inj hx D.min_mem heqf
  have hmo := D.min_odd hm hM
  omega

/-- The exact cycle-selected return section is the set of even-branch images. -/
theorem return_section (hm : 3 ≤ m) (hM : M < m ^ 3) :
    M.sqrt ∈ C ∧ M.sqrt < O m ∧
      (∀ x ∈ C, x < O m ↔ ∃ y ∈ C, y % 2 = 0 ∧ floorPower y = x) ∧
      (∀ x ∈ C, x < O m → x ≤ M.sqrt) := by
  have heq : ∀ x ∈ C, x < O m ↔ ∃ y ∈ C, y % 2 = 0 ∧ floorPower y = x := by
    intro x hx
    constructor
    · intro hlt
      obtain ⟨y, hy, hyx⟩ := D.preimage hx
      refine ⟨y, hy, ?_, hyx⟩
      rcases Nat.mod_two_eq_zero_or_one y with he | ho
      · exact he
      · have hylo := (D.bounds _ hy).1
        have hmono := Nat.sqrt_le_sqrt (Nat.pow_le_pow_left hylo 3)
        rw [floorPower_odd_eq ho] at hyx
        change O m ≤ O y at hmono
        change O y = x at hyx
        omega
    · rintro ⟨y, hy, he, rfl⟩
      rw [floorPower_even_eq he]
      exact D.even_image_lt_min_image hm hM hy he
  refine ⟨D.max_image_mem hm,
    D.even_image_lt_min_image hm hM D.max_mem (D.max_even hm), heq, ?_⟩
  intro x hx hlt
  obtain ⟨y, hy, he, rfl⟩ := (heq x hx).mp hlt
  rw [floorPower_even_eq he]
  exact Nat.sqrt_le_sqrt (D.bounds _ hy).2

end PeriodicExtrema

/-- The maximum even-image base uses OE; its return lies strictly below the
minimum base's OOE return. Both return values are odd actual cycle states. -/
theorem return_endpoint_gap {C : Set ℕ} {m M : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 3) :
    M.sqrt % 2 = 1 ∧ O M.sqrt % 2 = 0 ∧
      ReturnCells.oe M.sqrt % 2 = 1 ∧ ReturnCells.ooe m % 2 = 1 ∧
      ReturnCells.oe M.sqrt + 2 ≤ ReturnCells.ooe m := by
  have hm3 : 3 ≤ m := by omega
  let q := O m
  let t := M.sqrt
  let p₀ := O q
  let p := O t
  let z := p₀.sqrt
  let w := p.sqrt
  have hqmem : q ∈ C := D.min_image_mem hm3 hM
  have hqlow : q < m ^ 2 := PeriodicExtrema.min_image_lower hm3
  have hqodd : q % 2 = 1 := (D.parity hM hqmem).mpr hqlow
  obtain ⟨htmem, htq, _, _⟩ := D.return_section hm3 hM
  change t ∈ C at htmem
  change t < q at htq
  have htodd : t % 2 = 1 := (D.parity hM htmem).mpr (htq.trans hqlow)
  have htmin : m ≤ t := (D.bounds _ htmem).1
  have hp₀mem : p₀ ∈ C := by
    have hf : floorPower q = p₀ := floorPower_odd_eq hqodd
    rw [← hf]
    exact D.closed _ hqmem
  have hp₀even : p₀ % 2 = 0 := D.even_of_upper hM hp₀mem (sq_le_OO hm3)
  have hzmem : z ∈ C := by
    simpa [floorPower_even_eq hp₀even] using D.closed _ hp₀mem
  have hzodd : z % 2 = 1 := (D.parity hM hzmem).mpr
    ((D.even_image_lt_min_image hm3 hM hp₀mem hp₀even).trans hqlow)
  have hpmem : p ∈ C := by
    have hf : floorPower t = p := floorPower_odd_eq htodd
    rw [← hf]
    exact D.closed _ htmem
  have hpeven : p % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one p with he | ho
    · exact he
    · have hrmem : O p ∈ C := by
        simpa [floorPower_odd_eq ho, O] using D.closed _ hpmem
      have hrupper : m ^ 2 ≤ O p :=
        (Nat.pow_le_pow_left htmin 2).trans (sq_le_OO (hm3.trans htmin))
      have hre := D.even_of_upper hM hrmem hrupper
      have hle : (O p).sqrt ≤ t := Nat.sqrt_le_sqrt (D.bounds _ hrmem).2
      have hgt : t < (O p).sqrt := ooe_gt (hm.trans htmin)
      omega
  have hwmem : w ∈ C := by
    simpa [floorPower_even_eq hpeven] using D.closed _ hpmem
  have hwodd : w % 2 = 1 := (D.parity hM hwmem).mpr
    ((D.even_image_lt_min_image hm3 hM hpmem hpeven).trans hqlow)
  have hle : w ≤ z :=
    Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt (Nat.pow_le_pow_left (Nat.le_of_lt htq) 3))
  have hne : w ≠ z := by
    intro heq
    have hpp : p = p₀ := D.inj hpmem hp₀mem (by
      simpa [floorPower_even_eq hpeven, floorPower_even_eq hp₀even] using heq)
    have htqeq : t = q := D.inj htmem hqmem (by
      rw [floorPower_odd_eq htodd, floorPower_odd_eq hqodd]
      exact hpp)
    exact (ne_of_lt htq) htqeq
  have hgap : w + 2 ≤ z := by omega
  exact ⟨htodd, hpeven, hwodd, hzodd, hgap⟩

/-- Exact parity faces at both return cells give a minimum-determined ceiling. -/
theorem exact_return_seam {C : Set ℕ} {m M : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 3) :
    let t := M.sqrt
    let z := ReturnCells.ooe m
    t ^ 3 + 2 ≤ (z * (z - 2)) ^ 2 ∧
      M + 2 ≤ (t + 1) ^ 2 ∧ t ^ 3 < (z - 1) ^ 4 := by
  let t := M.sqrt
  let p := O t
  let w := ReturnCells.oe t
  let z := ReturnCells.ooe m
  obtain ⟨htodd, hpeven, hwodd, hzodd, hgap⟩ := return_endpoint_gap D hm hM
  change t % 2 = 1 at htodd
  change p % 2 = 0 at hpeven
  change w % 2 = 1 at hwodd
  change z % 2 = 1 at hzodd
  change w + 2 ≤ z at hgap
  have hpcell : p < (w + 1) ^ 2 := by
    simpa [w, ReturnCells.oe, O, p, pow_two] using Nat.lt_succ_sqrt p
  have hpmod : (w + 1) ^ 2 % 2 = 0 := by
    simp [Nat.pow_mod, Nat.add_mod, hwodd]
  have hpbound : p + 2 ≤ (w + 1) ^ 2 := by omega
  have htcell : t ^ 3 < (p + 1) ^ 2 := lt_O_succ_sq t
  have htmod : t ^ 3 % 2 = 1 := by simp [Nat.pow_mod, htodd]
  have hp1mod : (p + 1) ^ 2 % 2 = 1 := by
    simp [Nat.pow_mod, Nat.add_mod, hpeven]
  have htbound : t ^ 3 + 2 ≤ (p + 1) ^ 2 := by omega
  have hz2 : 2 ≤ z := by omega
  have hzsub2 : z - 2 + 2 = z := Nat.sub_add_cancel hz2
  have hzsub1 : z - 1 + 1 = z := Nat.sub_add_cancel (by omega)
  have hwsq := Nat.pow_le_pow_left (show w + 1 ≤ z - 1 by omega) 2
  have hpend : p + 1 ≤ z * (z - 2) := by nlinarith
  have hseam : t ^ 3 + 2 ≤ (z * (z - 2)) ^ 2 :=
    htbound.trans (Nat.pow_le_pow_left hpend 2)
  have hMcell : M < (t + 1) ^ 2 := by
    simpa [t, pow_two] using Nat.lt_succ_sqrt M
  have hMmod := D.max_even (by omega : 3 ≤ m)
  have ht1mod : (t + 1) ^ 2 % 2 = 0 := by
    simp [Nat.pow_mod, Nat.add_mod, htodd]
  have hMbound : M + 2 ≤ (t + 1) ^ 2 := by omega
  have hweak : t ^ 3 < (z - 1) ^ 4 :=
    (ReturnCells.oe_cell t).2.trans_le
      (Nat.pow_le_pow_left (show w + 1 ≤ z - 1 by omega) 4)
  exact ⟨hseam, hMbound, hweak⟩

/-- Ordinary finite-period orbit hypotheses produce all the structural data;
neither injectivity nor a return-section ordering is an extra premise. -/
theorem periodicExtrema_of_orbit {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    PeriodicExtrema (Set.range (fun j : ℕ => floorPower^[j] m)) m M := by
  have hper : Function.IsPeriodicPt floorPower k m := hp
  refine ⟨⟨0, rfl⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨j, _, hj⟩ := hmax
    exact ⟨j, hj⟩
  · rintro x ⟨j, rfl⟩
    change m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M
    rw [← hper.iterate_mod_apply j]
    exact hbound _ (Nat.mod_lt _ hk)
  · rintro x ⟨j, rfl⟩
    exact ⟨j + 1, Function.iterate_succ_apply' floorPower j m⟩
  · rintro x ⟨j, rfl⟩
    exact ⟨k, hk, hper.apply_iterate j⟩

theorem periodicExtrema_of_cycleMin {m M : ℕ} {w : List Branch}
    (h : CycleMin m w)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    PeriodicExtrema (Set.range (fun j : ℕ => floorPower^[j] m)) m M := by
  apply periodicExtrema_of_orbit (by have := h.1.2.2; omega) (cycle_iterate_period h.1)
  · intro j hj
    exact ⟨h.2 j hj, hupper j hj⟩
  · exact hmax

/-- The exact return ceiling for the repository's actual cycle-minimum API. -/
theorem cycleMin_exact_return_seam {m M : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 5 ≤ m) (hM : M < m ^ 3)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    let t := M.sqrt
    let z := ReturnCells.ooe m
    t ^ 3 + 2 ≤ (z * (z - 2)) ^ 2 ∧
      M + 2 ≤ (t + 1) ^ 2 ∧ t ^ 3 < (z - 1) ^ 4 :=
  exact_return_seam (periodicExtrema_of_cycleMin h hupper hmax) hm hM

end Problems.Juggler.CubicReturn
