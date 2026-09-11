import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

namespace Problems.Juggler

/-- An exact rank translation has an explicit iterate at every nonnegative time. -/
theorem rankRotation_iterate {L e : ℕ} (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) (k : ℕ) (i : Fin L) :
    (p^[k] i).val = (i.val + k * e) % L := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', hrot, ih, Nat.mod_add_mod]
    congr 1
    ring

/-- The return times of a rank translation are exactly the divisibility times. -/
theorem rankRotation_period_iff {L e k : ℕ} (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) (i : Fin L) :
    Function.IsPeriodicPt p k i ↔ L ∣ k * e := by
  change p^[k] i = i ↔ _
  rw [Fin.ext_iff, rankRotation_iterate p hrot]
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt] using
    (Nat.add_modEq_left_iff (n := L) (a := i.val) (b := k * e))

/-- Dividing by the gcd gives the least return modulus. -/
theorem rankRotation_dvd_iff {L e k : ℕ} (hL : 0 < L) :
    L ∣ k * e ↔ L / L.gcd e ∣ k := by
  rw [← ZMod.natCast_eq_zero_iff (k * e) L, Nat.cast_mul]
  have h : ((k : ZMod L) * (e : ZMod L) = 0) ↔
      addOrderOf (e : ZMod L) ∣ k := by
    simpa only [nsmul_eq_mul] using
      (addOrderOf_dvd_iff_nsmul_eq_zero (x := (e : ZMod L)) (n := k)).symm
  rw [h, ZMod.addOrderOf_coe e hL.ne']

/-- Every point of one rank translation has the same least period. -/
theorem rankRotation_minimalPeriod {L e : ℕ} (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) (i : Fin L) :
    Function.minimalPeriod p i = L / L.gcd e := by
  have hL : 0 < L := Nat.zero_lt_of_lt i.isLt
  apply Nat.dvd_antisymm
  · apply Function.IsPeriodicPt.minimalPeriod_dvd
    exact (rankRotation_period_iff p hrot i).mpr
      ((rankRotation_dvd_iff hL).mpr dvd_rfl)
  · exact (rankRotation_dvd_iff hL).mp
      ((rankRotation_period_iff p hrot i).mp (Function.isPeriodicPt_minimalPeriod p i))

/-- Full transitivity forces the rank step and ambient size to be coprime. -/
theorem rankRotation_coprime {L e : ℕ} (hL : 0 < L)
    (p : Equiv.Perm (Fin L))
    (hrot : ∀ i, (p i).val = (i.val + e) % L)
    (hcycle : p.IsCycleOn (↑(Finset.univ : Finset (Fin L)))) :
    Nat.Coprime L e := by
  by_cases hsmall : L = 1
  · simp [hsmall]
  have htwo : 1 < L := by omega
  let i : Fin L := ⟨0, hL⟩
  let j : Fin L := ⟨1, htwo⟩
  obtain ⟨k, _, hk⟩ := hcycle.exists_pow_eq
    (a := i) (b := j) (Finset.mem_univ _) (Finset.mem_univ _)
  have hi : k * e % L = 1 := by
    have hr := rankRotation_iterate (p : Fin L → Fin L) hrot k i
    rw [p.iterate_eq_pow, hk] at hr
    simpa [i, j] using hr.symm
  have hd : L.gcd e ∣ k * e % L := by
    have he : k * e % L.gcd e = 0 := Nat.mod_eq_zero_of_dvd
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right L e) k)
    apply Nat.dvd_of_mod_eq_zero
    rwa [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left L e)]
  rw [hi] at hd
  exact Nat.eq_one_of_dvd_one hd

/-- Every iterate stays in its rank residue class modulo the gcd. -/
theorem rankRotation_residue {L e : ℕ} (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) (k : ℕ) (i : Fin L) :
    (p^[k] i).val % L.gcd e = i.val % L.gcd e := by
  rw [rankRotation_iterate p hrot, Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left L e)]
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd
    (dvd_mul_of_dvd_right (Nat.gcd_dvd_right L e) k), Nat.add_zero, Nat.mod_mod]

/-- Rank translation commutes with the adjacent-rank permutation. -/
theorem rankRotation_commute_adjacent {L e : ℕ} (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) :
    Function.Commute p (finRotate L) := by
  intro i
  have : NeZero L := ⟨(Nat.zero_lt_of_lt i.isLt).ne'⟩
  apply Fin.ext
  simp only [hrot, finRotate_apply, Fin.val_add]
  simp only [Nat.mod_add_mod]
  congr 1
  omega

/-- One upper-branch visit is exactly one wrap in the integer quotient. -/
theorem rankRotation_quotient_step {L e : ℕ} (hL : 0 < L) (he : e ≤ L) (k : ℕ) :
    ((k + 1) * e) / L = (k * e) / L +
      if L - e ≤ (k * e) % L then 1 else 0 := by
  have hr := Nat.mod_lt (k * e) hL
  have hsplit := Nat.mod_add_div (k * e) L
  have hex : (k + 1) * e = ((k * e) % L + e) + L * ((k * e) / L) := by
    nlinarith
  rw [hex, Nat.add_mul_div_left _ _ hL]
  by_cases h : L - e ≤ (k * e) % L
  · rw [if_pos h]
    have hq : ((k * e) % L + e) / L = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    omega
  · rw [if_neg h]
    have hq : ((k * e) % L + e) / L = 0 := Nat.div_eq_of_lt (by omega)
    omega

/-- The wrap identity is valid at every initial rank, not only at zero. -/
theorem rankRotation_quotient_step_from {L e : ℕ} (hL : 0 < L) (he : e ≤ L)
    (a k : ℕ) :
    (a + (k + 1) * e) / L = (a + k * e) / L +
      if L - e ≤ (a + k * e) % L then 1 else 0 := by
  have hr := Nat.mod_lt (a + k * e) hL
  have hsplit := Nat.mod_add_div (a + k * e) L
  have hex : a + (k + 1) * e =
      ((a + k * e) % L + e) + L * ((a + k * e) / L) := by nlinarith
  rw [hex, Nat.add_mul_div_left _ _ hL]
  by_cases h : L - e ≤ (a + k * e) % L
  · rw [if_pos h]
    have hq : ((a + k * e) % L + e) / L = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    omega
  · rw [if_neg h]
    have hq : ((a + k * e) % L + e) / L = 0 := Nat.div_eq_of_lt (by omega)
    omega

/-- Exact upper-branch prefix count with an arbitrary initial rank. -/
theorem rankRotation_upper_prefix_from {L e a : ℕ} (ha : a < L) (he : e ≤ L)
    (k : ℕ) :
    (∑ j ∈ Finset.range k, if L - e ≤ (a + j * e) % L then 1 else 0) =
      (a + k * e) / L := by
  induction k with
  | zero => simp [Nat.div_eq_of_lt ha]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    exact (rankRotation_quotient_step_from (Nat.zero_lt_of_lt ha) he a k).symm

/-- Exact upper-branch prefix count along any orbit of the rank translation. -/
theorem rankRotation_upper_orbit_prefix {L e : ℕ} (he : e ≤ L)
    (p : Fin L → Fin L) (hrot : ∀ i, (p i).val = (i.val + e) % L)
    (i : Fin L) (k : ℕ) :
    (∑ j ∈ Finset.range k, if L - e ≤ (p^[j] i).val then 1 else 0) =
      (i.val + k * e) / L := by
  simp_rw [rankRotation_iterate p hrot]
  exact rankRotation_upper_prefix_from i.isLt he k

/-- The lower visits complement the upper visits at every initial rank. -/
theorem rankRotation_lower_orbit_prefix {L e : ℕ} (he : e ≤ L)
    (p : Fin L → Fin L) (hrot : ∀ i, (p i).val = (i.val + e) % L)
    (i : Fin L) (k : ℕ) :
    (∑ j ∈ Finset.range k, if (p^[j] i).val < L - e then 1 else 0) =
      k - (i.val + k * e) / L := by
  have hcomp : (∑ j ∈ Finset.range k, if (p^[j] i).val < L - e then 1 else 0) +
      (∑ j ∈ Finset.range k, if L - e ≤ (p^[j] i).val then 1 else 0) = k := by
    rw [← Finset.sum_add_distrib]
    have : ∀ j ∈ Finset.range k,
        (if (p^[j] i).val < L - e then 1 else 0) +
        (if L - e ≤ (p^[j] i).val then 1 else 0) = (1 : ℕ) := by
      intro j _
      split_ifs <;> omega
    rw [Finset.sum_congr rfl this]
    simp
  rw [rankRotation_upper_orbit_prefix he p hrot] at hcomp
  omega

/-- The number of upper visits from rank zero is the floor of k e / L. -/
theorem rankRotation_upper_prefix {L e : ℕ} (hL : 0 < L) (he : e ≤ L) (k : ℕ) :
    (∑ j ∈ Finset.range k, if L - e ≤ (j * e) % L then 1 else 0) = k * e / L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    exact (rankRotation_quotient_step hL he k).symm

/-- The number of lower visits is complementary to the wrap count. -/
theorem rankRotation_lower_prefix {L e : ℕ} (hL : 0 < L) (he : e ≤ L) (k : ℕ) :
    (∑ j ∈ Finset.range k, if (j * e) % L < L - e then 1 else 0) =
      k - k * e / L := by
  have hcomp : (∑ j ∈ Finset.range k, if (j * e) % L < L - e then 1 else 0) +
      (∑ j ∈ Finset.range k, if L - e ≤ (j * e) % L then 1 else 0) = k := by
    rw [← Finset.sum_add_distrib]
    have : ∀ j ∈ Finset.range k,
        (if (j * e) % L < L - e then 1 else 0) +
        (if L - e ≤ (j * e) % L then 1 else 0) = (1 : ℕ) := by
      intro j _
      split_ifs <;> omega
    rw [Finset.sum_congr rfl this]
    simp
  rw [rankRotation_upper_prefix hL he] at hcomp
  omega

/-- Natural-number form of the ceiling k o / L. -/
theorem rankRotation_ceiling_identity {L o e : ℕ} (hL : 0 < L)
    (hcounts : o + e = L) (k : ℕ) :
    k - k * e / L = (k * o + L - 1) / L := by
  have he : e ≤ L := by omega
  have hq : k * e / L ≤ k := Nat.div_le_of_le_mul (by nlinarith)
  have hsplit := Nat.mod_add_div (k * e) L
  have hr := Nat.mod_lt (k * e) hL
  have ht := Nat.sub_add_cancel hq
  have hsum : (k - k * e / L) * L = k * o + k * e % L := by
    nlinarith
  symm
  apply Nat.div_eq_of_lt_le
  · omega
  · have : (k - k * e / L + 1) * L = (k - k * e / L) * L + L := by ring
    omega

/-- Exact ceiling-mechanical prefix counts along a rank-translation orbit. -/
theorem rankRotation_mechanical_prefix {L o e : ℕ} (hL : 0 < L)
    (hcounts : o + e = L) (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      if (p^[j] ⟨0, hL⟩).val < o then 1 else 0) = (k * o + L - 1) / L := by
  have ho : L - e = o := by omega
  simp_rw [rankRotation_iterate p hrot, Nat.zero_add]
  rw [← ho, rankRotation_lower_prefix hL (by omega)]
  simpa only [ho] using rankRotation_ceiling_identity hL hcounts k

end Problems.Juggler
