import Problems.Juggler.CubicConstraintFusion
import Problems.Juggler.RootCells

/-!
# Critical corrections and two complete square-root cells

These finite arithmetic implications retain explicit positive-product and
square-cell premises. They do not construct or exclude a periodic orbit.
-/

namespace Problems.Juggler.CriticalCostKernel

open CubicConstraintFusion

/-- Criticality is exactly a strict excess of the target-product valuation. -/
theorem critical_iff_valuation_lt {N B l l' : ℕ} {r : ℤ}
    (hN : 0 < N) (hB : 0 < B) (hl : 0 < l) (hl' : 0 < l')
    (hodd : N % 2 = 1)
    (hr : r = (N : ℤ) * l - (B : ℤ) * l') :
    Critical l r ↔ padicValNat 2 l < padicValNat 2 B + padicValNat 2 l' := by
  have hzero : padicValNat 2 N = 0 :=
    padicValNat.eq_zero_of_not_dvd (by omega)
  have hleft : padicValNat 2 (N * l) = padicValNat 2 l := by
    rw [padicValNat.mul (Nat.ne_of_gt hN) (Nat.ne_of_gt hl), hzero, zero_add]
  have hright : padicValNat 2 (B * l') =
      padicValNat 2 B + padicValNat 2 l' :=
    padicValNat.mul (Nat.ne_of_gt hB) (Nat.ne_of_gt hl')
  have heq : ((N * l : ℕ) : ℤ) - ((B * l' : ℕ) : ℤ) = r := by
    push_cast
    exact hr.symm
  constructor
  · rintro ⟨hrne, hrval⟩
    by_contra hnot
    have hle : padicValNat 2 (B * l') ≤ padicValNat 2 (N * l) := by
      rw [hleft, hright]
      omega
    rcases lt_or_eq_of_le hle with hlt | hequal
    · have hrev := valuation_sub_of_lt (Nat.mul_pos hB hl') hlt
      have hrev_eq : ((B * l' : ℕ) : ℤ) - ((N * l : ℕ) : ℤ) = -r := by
        rw [← heq]
        ring
      rw [hrev_eq] at hrev
      have hneg : padicValInt 2 (-r) = padicValInt 2 r := by
        simp [padicValInt]
      rw [hneg, hrval, ← hleft] at hrev
      omega
    · let k := padicValNat 2 (N * l)
      have hxdiv : 2 ^ k ∣ N * l := pow_padicValNat_dvd
      have hydiv : 2 ^ k ∣ B * l' := by
        change 2 ^ padicValNat 2 (N * l) ∣ B * l'
        rw [← hequal]
        exact
          (pow_padicValNat_dvd (p := 2) (n := B * l'))
      obtain ⟨u, hu⟩ := hxdiv
      obtain ⟨v, hv⟩ := hydiv
      have hunot : ¬2 ∣ u := by
        rintro ⟨z, hz⟩
        have hxnot : ¬2 ^ (k + 1) ∣ N * l :=
          pow_succ_padicValNat_not_dvd (p := 2) (Nat.ne_of_gt (Nat.mul_pos hN hl))
        apply hxnot
        refine ⟨z, ?_⟩
        rw [hu, hz, pow_succ]
        ring
      have hvnot : ¬2 ∣ v := by
        rintro ⟨z, hz⟩
        have hd : 2 ^ (k + 1) ∣ B * l' := by
          refine ⟨z, ?_⟩
          rw [hv, hz, pow_succ]
          ring
        have hn := pow_succ_padicValNat_not_dvd
          (p := 2) (Nat.ne_of_gt (Nat.mul_pos hB hl'))
        apply hn
        rw [hequal]
        exact hd
      have huv : (2 : ℤ) ∣ (u : ℤ) - v := by omega
      obtain ⟨z, hz⟩ := huv
      have hrdiv : (2 : ℤ) ^ (k + 1) ∣ r := by
        refine ⟨z, ?_⟩
        rw [← heq, hu, hv]
        push_cast
        rw [pow_succ]
        calc
          (2 : ℤ) ^ k * u - 2 ^ k * v = 2 ^ k * ((u : ℤ) - v) := by ring
          _ = 2 ^ k * (2 * z) := by rw [hz]
          _ = 2 ^ k * 2 * z := by ring
      have hbound := (((padicValInt_dvd_iff (p := 2) (k + 1) r).mp hrdiv).resolve_left hrne)
      rw [hrval, ← hleft] at hbound
      change k + 1 ≤ k at hbound
      omega
  · intro hlt
    by_contra hn
    have hbudget := noncritical_valuation_budget hN hB hl hl' hodd hr hn
    omega

/-- Distinct odd outputs of two even square-root cells force this source gap. -/
theorem even_cells_separation {x y t q D : ℕ}
    (hx : x % 2 = 0) (hy : y % 2 = 0)
    (ht : t % 2 = 1) (hq : q % 2 = 1) (htq : t < q)
    (hxu : x < (t + 1) ^ 2)
    (hyq : q ^ 2 ≤ y)
    (hD : x + D = y) : 2 * t + 6 ≤ D ∧ 4 * x < D ^ 2 := by
  have hqmod : q ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hq]
  have htmod : (t + 1) ^ 2 % 2 = 0 := by
    simp [Nat.pow_mod, Nat.add_mod, ht]
  have hupper : x + 2 ≤ (t + 1) ^ 2 := by omega
  have hlower : q ^ 2 + 1 ≤ y := by omega
  have hstep : t + 2 ≤ q := by omega
  have hsep : 2 * t + 6 ≤ D := by nlinarith
  exact ⟨hsep, by nlinarith⟩

/-- Actual square-root outputs supply the cells automatically. Even inputs
make these the prescribed E outputs, with both exit parities retained. -/
theorem even_sqrt_separation {x y : ℕ}
    (hx : x % 2 = 0) (hy : y % 2 = 0)
    (ht : x.sqrt % 2 = 1) (hq : y.sqrt % 2 = 1)
    (hlt : x.sqrt < y.sqrt) :
    2 * x.sqrt + 6 ≤ y - x ∧ 4 * x < (y - x) ^ 2 := by
  have hxy : x ≤ y := by
    by_contra hn
    have hmono := Nat.sqrt_le_sqrt (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    omega
  apply even_cells_separation hx hy ht hq hlt
  · simpa only [pow_two] using Nat.lt_succ_sqrt x
  · simpa only [pow_two] using Nat.sqrt_le y
  · exact Nat.add_sub_of_le hxy

/-- Separate the polynomial cost from the square-root geometry. The last
inequality supplies the integer denominator comparison for normalization. -/
theorem symmetric_family_cost_of_separation {s a ym yp : ℕ}
    (hs : 2 ≤ s) (ha : 1 ≤ a) (has : a ≤ s)
    (hminus : ym + 3 * s * a = 8 * s ^ 3)
    (hplus : yp = 8 * s ^ 3 + 3 * s * a)
    (hsep : 4 * ym < (6 * s * a) ^ 2) :
    2 * s < 3 * a ^ 2 ∧ 32 * s ^ 3 < 27 * (2 * a ^ 3) ^ 2 ∧
      s ^ 3 < 3 * s ^ 2 * a ^ 2 - a ^ 3 ∧
      2 * yp + 1 < 23 * (3 * s ^ 2 * a ^ 2 - a ^ 3) := by
  have hscaled : 8 * s ^ 2 < 9 * s * a ^ 2 + 3 * a := by
    by_contra hn
    have hmul := Nat.mul_le_mul_left (4 * s) (Nat.le_of_not_gt hn)
    nlinarith
  have hsize : 2 * s < 3 * a ^ 2 := by
    by_contra hn
    have hmul := Nat.mul_le_mul_left (3 * s) (Nat.le_of_not_gt hn)
    nlinarith
  have hcube : (2 * s) ^ 3 < (3 * a ^ 2) ^ 3 := by gcongr
  have hcorrection : 32 * s ^ 3 < 27 * (2 * a ^ 3) ^ 2 := by
    nlinarith only [hcube]
  have ha2 : s < 2 * a ^ 2 := by omega
  have hspos : 0 < s ^ 2 := by positivity
  have hlarge := Nat.mul_lt_mul_of_pos_left ha2 hspos
  have ha_lt_sq : a < s ^ 2 := by nlinarith
  have hapos : 0 < a ^ 2 := by positivity
  have hsmall := Nat.mul_lt_mul_of_pos_right ha_lt_sq hapos
  have hcost_add : s ^ 3 + a ^ 3 < 3 * s ^ 2 * a ^ 2 := by nlinarith
  have hcost : s ^ 3 < 3 * s ^ 2 * a ^ 2 - a ^ 3 := by omega
  have hdenom : 2 * yp + 1 ≤ 23 * s ^ 3 := by
    have hsa := Nat.mul_le_mul_left (6 * s) has
    have h23 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hcube_pos : 0 < s ^ 3 := by positivity
    nlinarith
  have hratio := Nat.mul_lt_mul_of_pos_left hcost (by decide : 0 < 23)
  exact ⟨hsize, hcorrection, hcost, hdenom.trans_lt hratio⟩

/-- The symmetric family pays a cubic raw remainder when both E cells separate.
The additive equation for the lower source avoids truncated subtraction. -/
theorem symmetric_family_cost {s a ym yp tm tp : ℕ}
    (hs : 2 ≤ s) (ha : 1 ≤ a) (has : a ≤ s)
    (hminus : ym + 3 * s * a = 8 * s ^ 3)
    (hplus : yp = 8 * s ^ 3 + 3 * s * a)
    (heven : ym % 2 = 0 ∧ yp % 2 = 0)
    (hodd : tm % 2 = 1 ∧ tp % 2 = 1) (hlt : tm < tp)
    (hcellminus : ym < (tm + 1) ^ 2)
    (hcellplus : tp ^ 2 ≤ yp) :
    5 * s < 9 * a ^ 2 ∧ s < 2 * a ^ 2 ∧
      s ^ 3 < 3 * s ^ 2 * a ^ 2 - a ^ 3 := by
  have hD : ym + 6 * s * a = yp := by nlinarith
  have hsep := even_cells_separation heven.1 heven.2 hodd.1 hodd.2 hlt
    hcellminus hcellplus hD
  have hcost := symmetric_family_cost_of_separation hs ha has hminus hplus hsep.2
  exact ⟨by omega, by omega, hcost.2.2.1⟩

/-- Consume actual odd square-root exits instead of supplying cell witnesses. -/
theorem symmetric_family_sqrt_cost {s a ym yp : ℕ}
    (hs : 2 ≤ s) (ha : 1 ≤ a) (has : a ≤ s)
    (hminus : ym + 3 * s * a = 8 * s ^ 3)
    (hplus : yp = 8 * s ^ 3 + 3 * s * a)
    (heven : ym % 2 = 0 ∧ yp % 2 = 0)
    (hodd : ym.sqrt % 2 = 1 ∧ yp.sqrt % 2 = 1)
    (hlt : ym.sqrt < yp.sqrt) :
    2 * s < 3 * a ^ 2 ∧ 32 * s ^ 3 < 27 * (2 * a ^ 3) ^ 2 ∧
      s ^ 3 < 3 * s ^ 2 * a ^ 2 - a ^ 3 ∧
      2 * yp + 1 < 23 * (3 * s ^ 2 * a ^ 2 - a ^ 3) := by
  have hsep := even_sqrt_separation heven.1 heven.2 hodd.1 hodd.2 hlt
  have hadd : ym + 6 * s * a = yp := by nlinarith
  have hD : yp - ym = 6 * s * a := by rw [← hadd, Nat.add_sub_cancel_left]
  rw [hD] at hsep
  exact symmetric_family_cost_of_separation hs ha has hminus hplus hsep.2

/-- Distinct odd parameters in the specified range give a large quartic gap.
The comparison with an adjacent-cycle gap ceiling is a separate input. -/
theorem quartic_family_gap {b c : ℕ}
    (hb : b % 2 = 1) (hc : c % 2 = 1)
    (hbmin : 3 ≤ b) (hbc : b < c) (hcmax : c < 23000) :
    c ^ 4 + 2 < 4800 * (c ^ 4 - b ^ 4) := by
  have hstep : b + 2 ≤ c := by omega
  have hcmin : 5 ≤ c := by omega
  by_cases hcfive : c = 5
  · have hbthree : b = 3 := by omega
    subst c
    subst b
    norm_num
  have hcseven : 7 ≤ c := by omega
  let u := c - 7
  have hcu : c = u + 7 := by dsimp [u]; omega
  have hcsub : c - 2 = u + 5 := by omega
  have hpower : b ^ 4 ≤ (c - 2) ^ 4 := by
    gcongr
    omega
  have hpoly : 5 * c ^ 3 + (c - 2) ^ 4 ≤ c ^ 4 := by
    rw [hcsub, hcu]
    ring_nf
    omega
  have hgap : 5 * c ^ 3 ≤ c ^ 4 - b ^ 4 := by omega
  have hcube : 2 < c ^ 3 := by
    calc
      2 < (5 : ℕ) ^ 3 := by norm_num
      _ ≤ c ^ 3 := by gcongr
  have hsmall : c ^ 4 + 2 < (c + 1) * c ^ 3 := by nlinarith
  have hmul : (c + 1) * c ^ 3 ≤ 23000 * c ^ 3 :=
    Nat.mul_le_mul_right (c ^ 3) (by omega)
  have hcost := Nat.mul_le_mul_left 4800 hgap
  nlinarith

/-- Exact prescribed O cells of the unit-offset symmetric pair, with their
raw remainders. Source and later return parities remain separate guards. -/
theorem symmetric_unit_odd_cells {s : ℕ} (hs : 1 ≤ s) :
    CubicReturn.O (4 * s ^ 2 - 1) = 8 * s ^ 3 - 3 * s ∧
      CubicReturn.O (4 * s ^ 2 + 1) = 8 * s ^ 3 + 3 * s ∧
      (4 * s ^ 2 - 1) ^ 3 = (8 * s ^ 3 - 3 * s) ^ 2 + (3 * s ^ 2 - 1) ∧
      (4 * s ^ 2 + 1) ^ 3 = (8 * s ^ 3 + 3 * s) ^ 2 + (3 * s ^ 2 + 1) := by
  let u := s - 1
  have hsu : s = u + 1 := by dsimp [u]; omega
  have hxm : 4 * s ^ 2 - 1 = 4 * u ^ 2 + 8 * u + 3 := by
    rw [hsu]
    ring_nf
    omega
  have hym : 8 * s ^ 3 - 3 * s = 8 * u ^ 3 + 24 * u ^ 2 + 21 * u + 5 := by
    rw [hsu]
    ring_nf
    omega
  have hmcell : (8 * s ^ 3 - 3 * s) ^ 2 ≤ (4 * s ^ 2 - 1) ^ 3 ∧
      (4 * s ^ 2 - 1) ^ 3 < (8 * s ^ 3 - 3 * s + 1) ^ 2 := by
    rw [hxm, hym]
    constructor <;> ring_nf <;> omega
  have hpcell : (8 * s ^ 3 + 3 * s) ^ 2 ≤ (4 * s ^ 2 + 1) ^ 3 ∧
      (4 * s ^ 2 + 1) ^ 3 < (8 * s ^ 3 + 3 * s + 1) ^ 2 := by
    rw [hsu]
    constructor <;> ring_nf <;> omega
  have hmraw : (4 * s ^ 2 - 1) ^ 3 =
      (8 * s ^ 3 - 3 * s) ^ 2 + (3 * s ^ 2 - 1) := by
    rw [hxm, hym, hsu]
    ring_nf
    omega
  have hpraw : (4 * s ^ 2 + 1) ^ 3 =
      (8 * s ^ 3 + 3 * s) ^ 2 + (3 * s ^ 2 + 1) := by ring
  refine ⟨?_, ?_, hmraw, hpraw⟩
  · unfold CubicReturn.O
    symm
    apply Nat.eq_sqrt.mpr
    simpa only [pow_two] using hmcell
  · unfold CubicReturn.O
    symm
    apply Nat.eq_sqrt.mpr
    simpa only [pow_two] using hpcell

/-- Exact equal-gap OO triple of Result 15. Integer cells, remainders,
complements and opposite raw complement signs; the log-log comparison RC48
remains written. -/
theorem oo_equal_gap_triple {t : ℕ} (ht : 9 ≤ t) (hodd : t % 2 = 1) :
    let xm := t ^ 2 - 4
    let x0 := t ^ 2
    let xp := t ^ 2 + 4
    let ym := t ^ 3 - 6 * t
    let y0 := t ^ 3
    let yp := t ^ 3 + 6 * t
    xm % 2 = 1 ∧ x0 % 2 = 1 ∧ xp % 2 = 1 ∧
      ym % 2 = 1 ∧ y0 % 2 = 1 ∧ yp % 2 = 1 ∧
      CubicReturn.O xm = ym ∧ CubicReturn.O x0 = y0 ∧ CubicReturn.O xp = yp ∧
      xm ^ 3 = ym ^ 2 + (12 * t ^ 2 - 64) ∧
      x0 ^ 3 = y0 ^ 2 ∧
      xp ^ 3 = yp ^ 2 + (12 * t ^ 2 + 64) ∧
      (ym + 1) ^ 2 = xm ^ 3 + (2 * t ^ 3 - 12 * t ^ 2 - 12 * t + 65) ∧
      (y0 + 1) ^ 2 = x0 ^ 3 + (2 * t ^ 3 + 1) ∧
      (yp + 1) ^ 2 = xp ^ 3 + (2 * t ^ 3 - 12 * t ^ 2 + 12 * t - 63) ∧
      x0 - xm = 4 ∧ xp - x0 = 4 ∧
      y0 - ym = 6 * t ∧ yp - y0 = 6 * t ∧
      Nat.gcd 4 (6 * t) = 2 ∧
      0 < 12 * t ^ 2 + 12 * t - 64 ∧
      0 < 12 * t ^ 2 - 12 * t + 64 ∧
      12 * t ^ 2 + 12 * t - 64 +
          (2 * t ^ 3 - 12 * t ^ 2 - 12 * t + 65) = 2 * t ^ 3 + 1 ∧
      12 * t ^ 2 - 12 * t + 64 +
          (2 * t ^ 3 - 12 * t ^ 2 + 12 * t - 63) = 2 * t ^ 3 + 1 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hxm : (9 + u) ^ 2 - 4 = u ^ 2 + 18 * u + 77 := by ring_nf; omega
  have hx0 : (9 + u) ^ 2 = u ^ 2 + 18 * u + 81 := by ring
  have hxp : (9 + u) ^ 2 + 4 = u ^ 2 + 18 * u + 85 := by ring
  have hym : (9 + u) ^ 3 - 6 * (9 + u) = u ^ 3 + 27 * u ^ 2 + 237 * u + 675 := by
    ring_nf; omega
  have hy0 : (9 + u) ^ 3 = u ^ 3 + 27 * u ^ 2 + 243 * u + 729 := by ring
  have hyp : (9 + u) ^ 3 + 6 * (9 + u) = u ^ 3 + 27 * u ^ 2 + 249 * u + 783 := by
    ring
  have hrem : 12 * (9 + u) ^ 2 - 64 = 12 * u ^ 2 + 216 * u + 908 := by
    ring_nf; omega
  have hU : 2 * (9 + u) ^ 3 - 12 * (9 + u) ^ 2 - 12 * (9 + u) + 65 =
      2 * u ^ 3 + 42 * u ^ 2 + 258 * u + 443 := by
    ring_nf; omega
  have hUp : 2 * (9 + u) ^ 3 - 12 * (9 + u) ^ 2 + 12 * (9 + u) - 63 =
      2 * u ^ 3 + 42 * u ^ 2 + 282 * u + 531 := by
    ring_nf; omega
  have hΔ : 12 * (9 + u) ^ 2 + 12 * (9 + u) - 64 =
      12 * u ^ 2 + 228 * u + 1016 := by
    ring_nf; omega
  have hΔ' : 12 * (9 + u) ^ 2 - 12 * (9 + u) + 64 =
      12 * u ^ 2 + 204 * u + 928 := by
    ring_nf; omega
  have hrawm : ((9 + u) ^ 2 - 4) ^ 3 =
      ((9 + u) ^ 3 - 6 * (9 + u)) ^ 2 + (12 * (9 + u) ^ 2 - 64) := by
    rw [hxm, hym, hrem]; ring
  have hraw0 : ((9 + u) ^ 2) ^ 3 = ((9 + u) ^ 3) ^ 2 := by ring
  have hrawp : ((9 + u) ^ 2 + 4) ^ 3 =
      ((9 + u) ^ 3 + 6 * (9 + u)) ^ 2 + (12 * (9 + u) ^ 2 + 64) := by ring
  have hUmid : ((9 + u) ^ 3 - 6 * (9 + u) + 1) ^ 2 =
      ((9 + u) ^ 2 - 4) ^ 3 +
        (2 * (9 + u) ^ 3 - 12 * (9 + u) ^ 2 - 12 * (9 + u) + 65) := by
    rw [hym, hxm, hU]; ring
  have hU0id : ((9 + u) ^ 3 + 1) ^ 2 =
      ((9 + u) ^ 2) ^ 3 + (2 * (9 + u) ^ 3 + 1) := by ring
  have hUpid : ((9 + u) ^ 3 + 6 * (9 + u) + 1) ^ 2 =
      ((9 + u) ^ 2 + 4) ^ 3 +
        (2 * (9 + u) ^ 3 - 12 * (9 + u) ^ 2 + 12 * (9 + u) - 63) := by
    rw [hyp, hxp, hUp]; ring
  have hcellm :
      ((9 + u) ^ 3 - 6 * (9 + u)) ^ 2 ≤ ((9 + u) ^ 2 - 4) ^ 3 ∧
        ((9 + u) ^ 2 - 4) ^ 3 < ((9 + u) ^ 3 - 6 * (9 + u) + 1) ^ 2 := by
    constructor
    · rw [hrawm]; exact Nat.le_add_right _ _
    · rw [hUmid, hU]; exact Nat.lt_add_of_pos_right (by positivity)
  have hcell0 : ((9 + u) ^ 3) ^ 2 ≤ ((9 + u) ^ 2) ^ 3 ∧
      ((9 + u) ^ 2) ^ 3 < ((9 + u) ^ 3 + 1) ^ 2 := by
    constructor
    · exact hraw0.symm.le
    · rw [hU0id]; exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
  have hcellp :
      ((9 + u) ^ 3 + 6 * (9 + u)) ^ 2 ≤ ((9 + u) ^ 2 + 4) ^ 3 ∧
        ((9 + u) ^ 2 + 4) ^ 3 < ((9 + u) ^ 3 + 6 * (9 + u) + 1) ^ 2 := by
    constructor
    · rw [hrawp]; exact Nat.le_add_right _ _
    · rw [hUpid, hUp]; exact Nat.lt_add_of_pos_right (by positivity)
  have hparx0 : (9 + u) ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hodd]
  have hparxm : ((9 + u) ^ 2 - 4) % 2 = 1 := by omega
  have hparxp : ((9 + u) ^ 2 + 4) % 2 = 1 := by omega
  have hpary0 : (9 + u) ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hodd]
  have hparym : ((9 + u) ^ 3 - 6 * (9 + u)) % 2 = 1 := by omega
  have hparyp : ((9 + u) ^ 3 + 6 * (9 + u)) % 2 = 1 := by omega
  have hOm : CubicReturn.O ((9 + u) ^ 2 - 4) = (9 + u) ^ 3 - 6 * (9 + u) := by
    unfold CubicReturn.O
    symm
    apply Nat.eq_sqrt.mpr
    simpa only [pow_two] using hcellm
  have hO0 : CubicReturn.O ((9 + u) ^ 2) = (9 + u) ^ 3 := by
    unfold CubicReturn.O
    symm
    apply Nat.eq_sqrt.mpr
    simpa only [pow_two] using hcell0
  have hOp : CubicReturn.O ((9 + u) ^ 2 + 4) = (9 + u) ^ 3 + 6 * (9 + u) := by
    unfold CubicReturn.O
    symm
    apply Nat.eq_sqrt.mpr
    simpa only [pow_two] using hcellp
  have hdx : (9 + u) ^ 2 - ((9 + u) ^ 2 - 4) = 4 := by omega
  have hdxp : (9 + u) ^ 2 + 4 - (9 + u) ^ 2 = 4 := by omega
  have hdy : (9 + u) ^ 3 - ((9 + u) ^ 3 - 6 * (9 + u)) = 6 * (9 + u) := by omega
  have hdyp : (9 + u) ^ 3 + 6 * (9 + u) - (9 + u) ^ 3 = 6 * (9 + u) := by omega
  have hgcd : Nat.gcd 4 (6 * (9 + u)) = 2 := by
    have hmod : (6 * (9 + u)) % 4 = 2 := by
      have hcases : (9 + u) % 4 = 1 ∨ (9 + u) % 4 = 3 := by omega
      rcases hcases with h | h <;> rw [Nat.mul_mod, h]
    rw [Nat.gcd_rec 4 (6 * (9 + u)), hmod]
    decide
  have hposΔ : 0 < 12 * (9 + u) ^ 2 + 12 * (9 + u) - 64 := by
    rw [hΔ]; omega
  have hposΔ' : 0 < 12 * (9 + u) ^ 2 - 12 * (9 + u) + 64 := by
    rw [hΔ']; omega
  have hsignm : 12 * (9 + u) ^ 2 + 12 * (9 + u) - 64 +
      (2 * (9 + u) ^ 3 - 12 * (9 + u) ^ 2 - 12 * (9 + u) + 65) =
        2 * (9 + u) ^ 3 + 1 := by
    rw [hΔ, hU]; ring
  have hsignp : 12 * (9 + u) ^ 2 - 12 * (9 + u) + 64 +
      (2 * (9 + u) ^ 3 - 12 * (9 + u) ^ 2 + 12 * (9 + u) - 63) =
        2 * (9 + u) ^ 3 + 1 := by
    rw [hΔ', hUp]; ring
  exact ⟨hparxm, hparx0, hparxp, hparym, hpary0, hparyp, hOm, hO0, hOp,
    hrawm, hraw0, hrawp, hUmid, hU0id, hUpid, hdx, hdxp, hdy, hdyp, hgcd,
    hposΔ, hposΔ', hsignm, hsignp⟩

end Problems.Juggler.CriticalCostKernel
