import Problems.Juggler.CubicRotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD

namespace Problems.Juggler

/-!
# Residue classes and interlacing for finite rank translations

Each orbit is one residue class modulo the gcd of the step and ambient
size. Counting the residues also gives each orbit's upper-branch count.
-/

theorem rankResidue_range_card {N g r : ℕ} (hg : 0 < g) (hd : g ∣ N)
    (hr : r < g) :
    ((Finset.range N).filter (fun x => x % g = r)).card = N / g := by
  have hN : N / g * g = N := Nat.div_mul_cancel hd
  have hs : (Finset.range N).filter (fun x => x % g = r) =
      (Finset.range (N / g)).image (fun k => k * g + r) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx, hmod⟩
      refine ⟨x / g, ?_, ?_⟩
      · apply (Nat.div_lt_iff_lt_mul hg).mpr
        rwa [hN]
      · have := Nat.div_add_mod x g
        nlinarith
    · rintro ⟨k, hk, rfl⟩
      constructor
      · have hmul := Nat.mul_le_mul_right g (show k + 1 ≤ N / g by omega)
        nlinarith
      · simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  rw [hs, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro a b h
    nlinarith

theorem rankResidue_fin_card {N g r : ℕ} (hg : 0 < g) (hd : g ∣ N)
    (hr : r < g) :
    (Finset.univ.filter (fun x : Fin N => x.val % g = r)).card = N / g := by
  calc
    _ = ((Finset.range N).filter (fun x => x % g = r)).card := by
      apply Finset.card_bij (fun x _ => x.val)
      · intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt,
          (Finset.mem_filter.mp hx).2⟩
      · intro x hx y hy h
        exact Fin.ext h
      · intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hy, hr'⟩
        let x : Fin N := ⟨y, Finset.mem_range.mp hy⟩
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr'⟩, rfl⟩
    _ = N / g := rankResidue_range_card hg hd hr

/-- A full least-period orbit fills its entire gcd residue class. -/
theorem rankRotation_orbit_finset {L e : ℕ} (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) (i : Fin L) :
    (Finset.range (L / L.gcd e)).image (fun k => p^[k] i) =
      Finset.univ.filter (fun j : Fin L => j.val % L.gcd e = i.val % L.gcd e) := by
  have hL : 0 < L := Nat.zero_lt_of_lt i.isLt
  have hg : 0 < L.gcd e := Nat.gcd_pos_of_pos_left e hL
  have hinj : Set.InjOn (fun k => p^[k] i) (Finset.range (L / L.gcd e)) := by
    intro a ha b hb hab
    have ha' : a < Function.minimalPeriod p i := by
      rw [rankRotation_minimalPeriod p hrot]
      exact Finset.mem_range.mp ha
    have hb' : b < Function.minimalPeriod p i := by
      rw [rankRotation_minimalPeriod p hrot]
      exact Finset.mem_range.mp hb
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod ha' hb').mp hab
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rankRotation_residue p hrot k i⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range,
      rankResidue_fin_card hg (Nat.gcd_dvd_left L e) (Nat.mod_lt _ hg)]

/-- Two ranks belong to the same orbit exactly when their gcd residues agree. -/
theorem rankRotation_orbit_iff_residue {L e : ℕ} (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) (i j : Fin L) :
    (∃ k : ℕ, p^[k] i = j) ↔ i.val % L.gcd e = j.val % L.gcd e := by
  constructor
  · rintro ⟨k, rfl⟩
    exact (rankRotation_residue p hrot k i).symm
  · intro h
    have hj : j ∈ Finset.univ.filter
        (fun j : Fin L => j.val % L.gcd e = i.val % L.gcd e) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩
    rw [← rankRotation_orbit_finset p hrot i] at hj
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hj
    exact ⟨k, heq⟩

/-- Ranks 0 through g-1 give exactly one representative for each orbit. -/
theorem rankRotation_orbit_representatives {L e : ℕ} (hL : 0 < L)
    (p : Fin L → Fin L) (hrot : ∀ i, (p i).val = (i.val + e) % L)
    (i : Fin L) :
    ∃! r : Fin (L.gcd e), ∃ k : ℕ,
      p^[k] ⟨r.val, lt_of_lt_of_le r.isLt (Nat.le_of_dvd hL (Nat.gcd_dvd_left L e))⟩ = i := by
  have hg : 0 < L.gcd e := Nat.gcd_pos_of_pos_left e hL
  let r : Fin (L.gcd e) := ⟨i.val % L.gcd e, Nat.mod_lt _ hg⟩
  refine ⟨r, ?_, ?_⟩
  · apply (rankRotation_orbit_iff_residue p hrot _ i).mpr
    exact Nat.mod_mod _ _
  · intro s hs
    have heq := (rankRotation_orbit_iff_residue p hrot _ i).mp hs
    apply Fin.ext
    simpa only [Nat.mod_eq_of_lt s.isLt] using heq

/-- The increasing positions in a residue class are r, g+r, 2g+r, and so forth. -/
theorem rankResidue_parameterization {L g r : ℕ} (hg : 0 < g)
    (hd : g ∣ L) (hr : r < g) (i : Fin L) :
    i.val % g = r ↔ ∃! q : Fin (L / g), i.val = q.val * g + r := by
  constructor
  · intro hi
    have hq : i.val / g < L / g := by
      apply (Nat.div_lt_iff_lt_mul hg).mpr
      simpa only [Nat.div_mul_cancel hd] using i.isLt
    let q : Fin (L / g) := ⟨i.val / g, hq⟩
    have heq : i.val = q.val * g + r := by
      have := Nat.div_add_mod i.val g
      change i.val = i.val / g * g + r
      nlinarith
    refine ⟨q, heq, ?_⟩
    intro s hs
    apply Fin.ext
    nlinarith
  · rintro ⟨q, hq, _⟩
    rw [hq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

/-- The upper tail has the same residue proportions when its length is divisible by g. -/
theorem rankResidue_upper_card {L e g r : ℕ} (he : e ≤ L) (hg : 0 < g)
    (hL : g ∣ L) (he' : g ∣ e) (hr : r < g) :
    (Finset.univ.filter (fun x : Fin L => x.val % g = r ∧ L - e ≤ x.val)).card =
      e / g := by
  have hcut : (L - e) % g = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hL he')
  have hsubmod : ∀ n : ℕ, L - e ≤ n → (n - (L - e)) % g = n % g := by
    intro n hn
    have h := Nat.add_mod (L - e) (n - (L - e)) g
    rw [Nat.add_sub_of_le hn, hcut, Nat.zero_add, Nat.mod_mod] at h
    exact h.symm
  calc
    _ = ((Finset.range e).filter (fun x => x % g = r)).card := by
      apply Finset.card_bij (fun x _ => x.val - (L - e))
      · intro x hx
        rcases (Finset.mem_filter.mp hx).2 with ⟨hxr, hxcut⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by have := x.isLt; omega), ?_⟩
        rwa [hsubmod x.val hxcut]
      · intro x hx y hy h
        have hx' := (Finset.mem_filter.mp hx).2.2
        have hy' := (Finset.mem_filter.mp hy).2.2
        apply Fin.ext
        omega
      · intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hy, hyr⟩
        have hy' := Finset.mem_range.mp hy
        let x : Fin L := ⟨L - e + y, by omega⟩
        refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · constructor
          · change (L - e + y) % g = r
            simpa only [Nat.add_mod, hcut, Nat.zero_add, Nat.mod_mod] using hyr
          · change L - e ≤ L - e + y
            omega
        · change L - e + y - (L - e) = y
          omega
    _ = e / g := rankResidue_range_card hg he' hr

/-- Every orbit has e/g upper ranks, even when the translation has several cycles. -/
theorem rankRotation_orbit_upper_card {L e : ℕ} (he : e ≤ L)
    (p : Fin L → Fin L) (hrot : ∀ i, (p i).val = (i.val + e) % L)
    (i : Fin L) :
    (((Finset.range (L / L.gcd e)).image (fun k => p^[k] i)).filter
      (fun j => L - e ≤ j.val)).card = e / L.gcd e := by
  rw [rankRotation_orbit_finset p hrot i, Finset.filter_filter]
  have hg : 0 < L.gcd e := Nat.gcd_pos_of_pos_left e (Nat.zero_lt_of_lt i.isLt)
  exact rankResidue_upper_card he hg (Nat.gcd_dvd_left L e)
    (Nat.gcd_dvd_right L e) (Nat.mod_lt _ hg)

/-- Sorted residue classes alternate in the same order in every block of g ranks. -/
theorem rankResidue_interlaces {g r s q : ℕ} (hrs : r < s) (hs : s < g) :
    q * g + r < q * g + s ∧ q * g + s < (q + 1) * g + r := by
  constructor <;> nlinarith

end Problems.Juggler
