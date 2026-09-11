import Problems.Juggler.ReturnCells
import Problems.Juggler.NumericBridge

namespace Problems.Juggler.RemainderCarry

/-!
A clipped square-cell quotient has three candidates. Retaining the exact
first square remainder repairs the OOE quotient with four candidates and
an entirely integer recovery function. The endpoint is separately validated;
these short-return results do not assert closure for arbitrary return words.
-/

/-- A clipped quotient provides three adjacent candidates for the integer root. -/
def baseline (N y : ℕ) : ℕ :=
  y ^ 2 + min ((N - y ^ 4) / (2 * y ^ 2)) (2 * y)

theorem baseline_bounds {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    N.sqrt ≤ baseline N y ∧ baseline N y ≤ N.sqrt + 2 := by
  let u := N.sqrt
  let c := u - y ^ 2
  let r := N - y ^ 4
  let D := 2 * y ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hu₀ : y ^ 2 ≤ u := by
    apply Nat.le_sqrt.mpr
    simpa [u, ← pow_two, ← pow_mul] using hc.1
  have hu₁ : u < (y + 1) ^ 2 := by
    apply Nat.sqrt_lt.mpr
    simpa [← pow_two, ← pow_mul] using hc.2
  have hu : u = y ^ 2 + c := by dsimp [c]; omega
  have hc₂ : c ≤ 2 * y := by nlinarith
  have hr : N = y ^ 4 + r := by dsimp [r]; omega
  have hlu : u ^ 2 ≤ N := Nat.sqrt_le' N
  have hhu : N < (u + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hcd : c ≤ r / D := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    dsimp [D]
    nlinarith [Nat.zero_le (c ^ 2)]
  have hcmin : c ≤ min (r / D) (2 * y) := le_min hcd hc₂
  have hmin : min (r / D) (2 * y) ≤ c + 2 := by
    by_cases heq : c = 2 * y
    · exact (min_le_right _ _).trans (by omega)
    · have hcs : c + 1 ≤ 2 * y := by omega
      have hs := Nat.pow_le_pow_left hcs 2
      have hquot : r / D < c + 3 := by
        apply (Nat.div_lt_iff_lt_mul hD).mpr
        dsimp [D]
        nlinarith
      exact (min_le_left _ _).trans (by omega)
  change u ≤ y ^ 2 + min (r / D) (2 * y) ∧
    y ^ 2 + min (r / D) (2 * y) ≤ u + 2
  omega

theorem baseline_correction {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    ∃ κ : ℕ, κ ≤ 2 ∧ baseline N y = N.sqrt + κ := by
  obtain ⟨hlo, hhi⟩ := baseline_bounds hy hc
  exact ⟨baseline N y - N.sqrt, by omega, by omega⟩

theorem baseline_zero_iff {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    baseline N y = N.sqrt ↔ baseline N y ^ 2 ≤ N := by
  have h := (baseline_bounds hy hc).1
  constructor
  · intro he; rw [he]; exact Nat.sqrt_le' N
  · intro hh
    have hh' : baseline N y ≤ N.sqrt :=
      Nat.le_sqrt.mpr (by simpa [pow_two] using hh)
    omega

theorem baseline_one_iff {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    baseline N y = N.sqrt + 1 ↔
      (baseline N y - 1) ^ 2 ≤ N ∧ N < baseline N y ^ 2 := by
  have h := baseline_bounds hy hc
  constructor
  · intro he
    rw [he]
    simp only [Nat.add_sub_cancel]
    exact ⟨Nat.sqrt_le' N, Nat.lt_succ_sqrt' N⟩
  · rintro ⟨hlo, hhi⟩
    have hl : baseline N y - 1 ≤ N.sqrt :=
      Nat.le_sqrt.mpr (by simpa [pow_two] using hlo)
    have hh : N.sqrt < baseline N y :=
      Nat.sqrt_lt.mpr (by simpa [pow_two] using hhi)
    omega

theorem baseline_two_iff {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    baseline N y = N.sqrt + 2 ↔ N < (baseline N y - 1) ^ 2 := by
  have h := baseline_bounds hy hc
  constructor
  · intro he
    rw [he]
    simpa using Nat.lt_succ_sqrt' N
  · intro hh
    have hh' : N.sqrt < baseline N y - 1 :=
      Nat.sqrt_lt.mpr (by simpa [pow_two] using hh)
    omega

theorem square_guard_iff {N y : ℕ} (hy : y % 2 = 1)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    N.sqrt % 2 = 0 ↔ (N.sqrt - y ^ 2) % 2 = 1 := by
  have hlo : y ^ 2 ≤ N.sqrt := by
    apply Nat.le_sqrt.mpr
    nlinarith [hc.1]
  have he : y ^ 2 + (N.sqrt - y ^ 2) = N.sqrt := by omega
  have hm := congrArg (fun n : ℕ => n % 2) he
  rw [Nat.add_mod, Nat.pow_mod, hy] at hm
  have hs : N.sqrt % 2 < 2 := Nat.mod_lt _ (by decide)
  have hd : (N.sqrt - y ^ 2) % 2 < 2 := Nat.mod_lt _ (by decide)
  norm_num at hm
  omega

theorem oe_sq_ge {u : ℕ} (hu : 3 ≤ u) : u ≤ ReturnCells.oe u ^ 2 := by
  let z := ReturnCells.oe u
  change u ≤ z ^ 2
  have hc : u ^ 3 < (z + 1) ^ 4 := (ReturnCells.oe_cell u).2
  have hz : 2 ≤ z := by
    by_contra hn
    have h₁ := Nat.pow_le_pow_left (show z + 1 ≤ 2 by omega) 4
    have h₂ := Nat.pow_le_pow_left hu 3
    norm_num at h₁ h₂
    omega
  by_contra hn
  have h₁ := Nat.pow_le_pow_left (show z ^ 2 + 1 ≤ u by omega) 3
  have hz₂ : 4 ≤ z ^ 2 := by simpa using Nat.pow_le_pow_left hz 2
  have h₆ : 4 * z ^ 4 ≤ z ^ 6 := by
    nlinarith [Nat.mul_le_mul_right (z ^ 4) hz₂]
  have h₄ : 2 * z ^ 3 ≤ z ^ 4 := by
    nlinarith [Nat.mul_le_mul_right (z ^ 3) hz]
  have h₂ : 2 * z ≤ z ^ 2 := by
    nlinarith [Nat.mul_le_mul_right z hz]
  have h₄' : 4 * z ^ 2 ≤ z ^ 4 := by
    nlinarith [Nat.mul_le_mul_right (z ^ 2) hz₂]
  nlinarith

theorem correction_identity (t u z : ℝ) (hz : z ≠ 0) :
    3 * t * (t ^ 2 - u ^ 2) / (4 * z ^ 2) -
        (t ^ 3 - u ^ 3) / (2 * z ^ 2) =
      (t - u) ^ 2 * (t + 2 * u) / (4 * z ^ 2) := by
  field_simp
  ring

theorem correction_error_bound {t u z : ℝ} (hu : 3 ≤ u)
    (htu : u ≤ t) (hut : t < u + 1) (huz : u ≤ z ^ 2) :
    0 ≤ (t - u) ^ 2 * (t + 2 * u) / (4 * z ^ 2) ∧
      (t - u) ^ 2 * (t + 2 * u) / (4 * z ^ 2) < 5 / 6 := by
  have hz : 0 < 4 * z ^ 2 := by nlinarith
  have hη : (t - u) ^ 2 < 1 := by nlinarith
  have htu' : 0 ≤ t + 2 * u := by linarith
  have hnum : (t - u) ^ 2 * (t + 2 * u) < 3 * u + 1 := by
    have hh := mul_le_mul_of_nonneg_right (le_of_lt hη) htu'
    nlinarith
  constructor
  · exact div_nonneg (mul_nonneg (sq_nonneg _) htu') hz.le
  · apply (div_lt_iff₀ hz).mpr
    nlinarith

theorem exact_remainder_correction {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    let t := Real.sqrt ((x : ℝ) ^ 3)
    0 ≤ 3 * t * R / (4 * (z : ℝ) ^ 2) -
        (t ^ 3 - (u : ℝ) ^ 3) / (2 * (z : ℝ) ^ 2) ∧
      3 * t * R / (4 * (z : ℝ) ^ 2) -
        (t ^ 3 - (u : ℝ) ^ 3) / (2 * (z : ℝ) ^ 2) < 5 / 6 := by
  let t := Real.sqrt ((x : ℝ) ^ 3)
  have hsq : t ^ 2 = (x : ℝ) ^ 3 := Real.sq_sqrt (by positivity)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hu0 : 0 ≤ (u : ℝ) := by positivity
  have hnatlo : u ^ 2 ≤ x ^ 3 := by rw [hu]; exact Nat.sqrt_le' _
  have hr : (R : ℝ) = t ^ 2 - (u : ℝ) ^ 2 := by
    rw [hR, Nat.cast_sub hnatlo, Nat.cast_pow, Nat.cast_pow, hsq]
  have hroot : ((x ^ 3 : ℕ) : ℝ) = (x : ℝ) ^ 3 := by norm_cast
  have hlo : (u : ℝ) ≤ t := by
    change (u : ℝ) ≤ Real.sqrt ((x : ℝ) ^ 3)
    rw [← hroot, hu]
    exact Real.nat_sqrt_le_real_sqrt
  have hhi : t < (u : ℝ) + 1 := by
    change Real.sqrt ((x : ℝ) ^ 3) < (u : ℝ) + 1
    rw [← hroot, hu]
    exact Real.real_sqrt_lt_nat_sqrt_succ
  have hzu : (u : ℝ) ≤ (z : ℝ) ^ 2 := by
    rw [hz]
    exact_mod_cast oe_sq_ge hmin
  have hzr : (z : ℝ) ≠ 0 := by
    have hum : (3 : ℝ) ≤ u := by exact_mod_cast hmin
    nlinarith
  change 0 ≤ 3 * t * (R : ℝ) / (4 * (z : ℝ) ^ 2) -
      (t ^ 3 - (u : ℝ) ^ 3) / (2 * (z : ℝ) ^ 2) ∧ _
  rw [hr, correction_identity t (u : ℝ) (z : ℝ) hzr]
  exact correction_error_bound (by exact_mod_cast hmin) hlo hhi hzu

theorem floor_gap_one {a b : ℝ} (hlo : 0 ≤ b - a) (hhi : b - a < 1) :
    ⌊b⌋ = ⌊a⌋ ∨ ⌊b⌋ = ⌊a⌋ + 1 := by
  have h₁ : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_mono (by linarith)
  have h₂ : ⌊b⌋ ≤ ⌊a⌋ + 1 := by
    simpa only [Int.floor_add_one] using
      (Int.floor_mono (show b ≤ a + 1 by linarith))
  omega

/-- The exact real floor is signed: its value is permitted to be minus one. -/
noncomputable def correctedQuotient (x z R : ℕ) : ℤ :=
  let t := Real.sqrt ((x : ℝ) ^ 3)
  ⌊(t ^ 3 - (z : ℝ) ^ 4) / (2 * (z : ℝ) ^ 2) -
    3 * t * R / (4 * (z : ℝ) ^ 2)⌋

theorem exact_quotient_gap {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    (((u ^ 3 - z ^ 4) / (2 * z ^ 2) : ℕ) : ℤ) = correctedQuotient x z R ∨
      (((u ^ 3 - z ^ 4) / (2 * z ^ 2) : ℕ) : ℤ) =
        correctedQuotient x z R + 1 := by
  let t := Real.sqrt ((x : ℝ) ^ 3)
  let a := (t ^ 3 - (z : ℝ) ^ 4) / (2 * (z : ℝ) ^ 2) -
    3 * t * R / (4 * (z : ℝ) ^ 2)
  let b := ((u : ℝ) ^ 3 - (z : ℝ) ^ 4) / (2 * (z : ℝ) ^ 2)
  have he := exact_remainder_correction hu hz hmin hR
  have hdiff : b - a =
      3 * t * R / (4 * (z : ℝ) ^ 2) -
        (t ^ 3 - (u : ℝ) ^ 3) / (2 * (z : ℝ) ^ 2) := by
    dsimp [a, b]
    ring
  have hg := floor_gap_one (a := a) (b := b)
    (by rw [hdiff]; exact he.1)
    (by rw [hdiff]; linarith [he.2])
  have hcell : z ^ 4 ≤ u ^ 3 := by
    rw [hz]
    exact (ReturnCells.oe_cell u).1
  have hb : ⌊b⌋ = (((u ^ 3 - z ^ 4) / (2 * z ^ 2) : ℕ) : ℤ) := by
    have hb' : b = ((u ^ 3 - z ^ 4 : ℕ) : ℝ) / ((2 * z ^ 2 : ℕ) : ℝ) := by
      dsimp [b]
      simp only [Nat.cast_sub hcell, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    rw [hb', Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
  simpa only [hb, a, t, correctedQuotient] using hg

noncomputable def correctedBaseline (x z R : ℕ) : ℕ :=
  z ^ 2 + min (correctedQuotient x z R + 1).toNat (2 * z)

theorem corrected_baseline_bounds {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    (u ^ 3).sqrt ≤ correctedBaseline x z R ∧
      correctedBaseline x z R ≤ (u ^ 3).sqrt + 3 := by
  have hcell : z ^ 4 ≤ u ^ 3 ∧ u ^ 3 < (z + 1) ^ 4 := by
    rw [hz]
    exact ReturnCells.oe_cell u
  have hzpos : 0 < z := by
    have hh : u ≤ z ^ 2 := by rw [hz]; exact oe_sq_ge hmin
    nlinarith
  have hb := baseline_bounds hzpos hcell
  have hgap := exact_quotient_gap hu hz hmin hR
  unfold baseline at hb
  unfold correctedBaseline
  generalize hd : (u ^ 3 - z ^ 4) / (2 * z ^ 2) = d at hb hgap
  have hdpos : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  omega

theorem corrected_baseline_correction {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    ∃ κ : ℕ, κ ≤ 3 ∧ correctedBaseline x z R = (u ^ 3).sqrt + κ := by
  obtain ⟨hlo, hhi⟩ := corrected_baseline_bounds hu hz hmin hR
  exact ⟨correctedBaseline x z R - (u ^ 3).sqrt, by omega, by omega⟩

theorem retained_square {x u R : ℕ} (hu : u = (x ^ 3).sqrt)
    (hR : R = x ^ 3 - u ^ 2) : x ^ 3 - R = u ^ 2 := by
  have h : u ^ 2 ≤ x ^ 3 := by rw [hu]; exact Nat.sqrt_le' _
  omega

theorem endpoint_validation {x u z R : ℕ} (hu : u = (x ^ 3).sqrt)
    (hR : R = x ^ 3 - u ^ 2) :
    ReturnCells.oe u = z ↔
      z ^ 8 ≤ (x ^ 3 - R) ^ 3 ∧ (x ^ 3 - R) ^ 3 < (z + 1) ^ 8 := by
  rw [retained_square hu hR, ReturnCells.oe_eq_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · simpa [← pow_mul] using Nat.pow_le_pow_left hlo 2
    · simpa [← pow_mul] using Nat.pow_lt_pow_left hhi (by decide : 2 ≠ 0)
  · rintro ⟨hlo, hhi⟩
    constructor
    · by_contra hn
      have hh := Nat.pow_lt_pow_left (show u ^ 3 < z ^ 4 by omega)
        (by decide : 2 ≠ 0)
      norm_num [← pow_mul] at hh hlo
      omega
    · by_contra hn
      have hh := Nat.pow_le_pow_left (show (z + 1) ^ 4 ≤ u ^ 3 by omega) 2
      norm_num [← pow_mul] at hh hhi
      omega

theorem retained_fourth_cell {x u R : ℕ} (hu : u = (x ^ 3).sqrt)
    (hR : R = x ^ 3 - u ^ 2) :
    (u ^ 3).sqrt ^ 4 ≤ (x ^ 3 - R) ^ 3 ∧
      (x ^ 3 - R) ^ 3 < ((u ^ 3).sqrt + 1) ^ 4 := by
  rw [retained_square hu hR]
  constructor
  · convert Nat.pow_le_pow_left (Nat.sqrt_le' (u ^ 3)) 2 using 1 <;> ring
  · have hhi : u ^ 3 < ((u ^ 3).sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' _
    convert Nat.pow_lt_pow_left hhi (by decide : 2 ≠ 0) using 1 <;> ring

theorem fourth_cell_unique {N a b : ℕ}
    (ha : a ^ 4 ≤ N ∧ N < (a + 1) ^ 4)
    (hb : b ^ 4 ≤ N ∧ N < (b + 1) ^ 4) : a = b := by
  have h₁ : a ≤ b := by
    by_contra hn
    have hh := Nat.pow_le_pow_left (show b + 1 ≤ a by omega) 4
    omega
  have h₂ : b ≤ a := by
    by_contra hn
    have hh := Nat.pow_le_pow_left (show a + 1 ≤ b by omega) 4
    omega
  omega

theorem corrected_candidate_iff {x u z R κ : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) (_hκ : κ ≤ 3) :
    ((correctedBaseline x z R - κ) ^ 4 ≤ (x ^ 3 - R) ^ 3 ∧
        (x ^ 3 - R) ^ 3 < (correctedBaseline x z R - κ + 1) ^ 4) ↔
      correctedBaseline x z R = (u ^ 3).sqrt + κ := by
  have hvcell := retained_fourth_cell hu hR
  have hvmin : 3 ≤ (u ^ 3).sqrt := by
    apply Nat.le_sqrt.mpr
    have hh := Nat.pow_le_pow_left hmin 3
    norm_num at hh ⊢
    omega
  have hbase := (corrected_baseline_bounds hu hz hmin hR).1
  constructor
  · intro hc
    have hh := fourth_cell_unique hc hvcell
    omega
  · intro he
    rw [he]
    simpa using hvcell

theorem first_guard_iff {x u R : ℕ} (hu : u = (x ^ 3).sqrt)
    (hR : R = x ^ 3 - u ^ 2) (hx : x % 2 = 1) :
    u % 2 = 1 ↔ R % 2 = 0 := by
  have hlo : u ^ 2 ≤ x ^ 3 := by rw [hu]; exact Nat.sqrt_le' _
  have he : u ^ 2 + R = x ^ 3 := by omega
  have hm := congrArg (fun n : ℕ => n % 2) he
  have hx3 : x ^ 3 % 2 = 1 := by rw [Nat.pow_mod, hx]
  rw [hx3, Nat.add_mod, Nat.pow_mod] at hm
  have hum : u % 2 < 2 := Nat.mod_lt _ (by decide)
  have hrm : R % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases h : u % 2 <;> norm_num at hm ⊢ <;> omega

theorem second_guard_iff {x u z R κ : ℕ}
    (he : correctedBaseline x z R = (u ^ 3).sqrt + κ) :
    (u ^ 3).sqrt % 2 = 0 ↔ κ % 2 = correctedBaseline x z R % 2 := by
  rw [he, Nat.add_mod]
  have hv : (u ^ 3).sqrt % 2 < 2 := Nat.mod_lt _ (by decide)
  have hk : κ % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

theorem ooe_guard_iff {x u z R κ : ℕ} (hu : u = (x ^ 3).sqrt)
    (hR : R = x ^ 3 - u ^ 2) (hx : x % 2 = 1)
    (he : correctedBaseline x z R = (u ^ 3).sqrt + κ) :
    (u % 2 = 1 ∧ (u ^ 3).sqrt % 2 = 0) ↔
      (R % 2 = 0 ∧ κ % 2 = correctedBaseline x z R % 2) :=
  and_congr (first_guard_iff hu hR hx) (second_guard_iff he)

theorem corrected_candidate_minimal {x u z R κ : ℕ}
    (hu : u = (x ^ 3).sqrt) (hR : R = x ^ 3 - u ^ 2)
    (he : correctedBaseline x z R = (u ^ 3).sqrt + κ) :
    (correctedBaseline x z R - κ) ^ 4 ≤ (x ^ 3 - R) ^ 3 ∧
      ∀ j < κ, (x ^ 3 - R) ^ 3 < (correctedBaseline x z R - j) ^ 4 := by
  have hc := retained_fourth_cell hu hR
  constructor
  · simpa [he] using hc.1
  · intro j hj
    have hh := Nat.pow_le_pow_left
      (show (u ^ 3).sqrt + 1 ≤ correctedBaseline x z R - j by omega) 4
    exact hc.2.trans_le hh

theorem record_initializes {x u R : ℕ}
    (he : x ^ 3 = u ^ 2 + R) (hR : R ^ 2 ≤ 4 * u ^ 2) :
    u = (x ^ 3).sqrt := by
  have hr : R ≤ 2 * u := by nlinarith
  have hlo : u ≤ (x ^ 3).sqrt := Nat.le_sqrt.mpr (by nlinarith)
  have hhi : (x ^ 3).sqrt < u + 1 := Nat.sqrt_lt.mpr (by nlinarith)
  omega

/-- Integer floor division, including a possibly negative numerator. -/
def integerQuotient (x z R : ℕ) : ℤ :=
  (((((2 * x ^ 3 - 3 * R) ^ 2 * x ^ 3).sqrt : ℕ) : ℤ) -
    2 * (z : ℤ) ^ 4) / (4 * (z : ℤ) ^ 2)

theorem corrected_quotient_integer {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    correctedQuotient x z R = integerQuotient x z R := by
  let K := 2 * x ^ 3 - 3 * R
  let t := Real.sqrt ((x : ℝ) ^ 3)
  have hlo : u ^ 2 ≤ x ^ 3 := by rw [hu]; exact Nat.sqrt_le' _
  have hhi : x ^ 3 < (u + 1) ^ 2 := by rw [hu]; exact Nat.lt_succ_sqrt' _
  have he : x ^ 3 = u ^ 2 + R := by omega
  have hRle : R ≤ 2 * u := by nlinarith
  have hk : 3 * R ≤ 2 * x ^ 3 := by nlinarith
  have hkcast : (K : ℝ) = 2 * (x : ℝ) ^ 3 - 3 * R := by
    dsimp [K]
    rw [Nat.cast_sub hk]
    push_cast
    rfl
  have hsq : t ^ 2 = (x : ℝ) ^ 3 := Real.sq_sqrt (by positivity)
  have ht3 : t ^ 3 = (x : ℝ) ^ 3 * t := by rw [← hsq]; ring
  have hzpos : 0 < z := by
    have hh : u ≤ z ^ 2 := by rw [hz]; exact oe_sq_ge hmin
    nlinarith
  have hzr : (z : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hzpos
  have hformula : (t ^ 3 - (z : ℝ) ^ 4) / (2 * (z : ℝ) ^ 2) -
      3 * t * R / (4 * (z : ℝ) ^ 2) =
      ((K : ℝ) * t - ((2 * z ^ 4 : ℕ) : ℝ)) / ((4 * z ^ 2 : ℕ) : ℝ) := by
    push_cast
    rw [ht3, hkcast]
    field_simp
    ring
  have hroot : (K : ℝ) * t = Real.sqrt ((K ^ 2 * x ^ 3 : ℕ) : ℝ) := by
    push_cast
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg K)]
  unfold correctedQuotient
  change ⌊(t ^ 3 - (z : ℝ) ^ 4) / (2 * (z : ℝ) ^ 2) -
    3 * t * R / (4 * (z : ℝ) ^ 2)⌋ = _
  rw [hformula, Int.floor_div_natCast, Int.floor_sub_natCast, hroot,
    Real.floor_real_sqrt_eq_nat_sqrt]
  simp only [integerQuotient, K, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

def integerBaseline (x z R : ℕ) : ℕ :=
  z ^ 2 + min (integerQuotient x z R + 1).toNat (2 * z)

def selectFour (N a : ℕ) : ℕ :=
  if a ^ 4 ≤ N then a else
  if (a - 1) ^ 4 ≤ N then a - 1 else
  if (a - 2) ^ 4 ≤ N then a - 2 else a - 3

theorem fourth_le_iff {N v a : ℕ}
    (hc : v ^ 4 ≤ N ∧ N < (v + 1) ^ 4) : a ^ 4 ≤ N ↔ a ≤ v := by
  constructor
  · intro ha
    by_contra hn
    have hh := Nat.pow_le_pow_left (show v + 1 ≤ a by omega) 4
    omega
  · intro ha
    exact (Nat.pow_le_pow_left ha 4).trans hc.1

theorem selectFour_eq {N a v : ℕ}
    (hc : v ^ 4 ≤ N ∧ N < (v + 1) ^ 4)
    (hlo : v ≤ a) (hhi : a ≤ v + 3) : selectFour N a = v := by
  unfold selectFour
  simp only [fourth_le_iff hc]
  split_ifs <;> omega

/-- A fully integer short-block recovery using the retained absolute remainder. -/
def recoverPeak (x z R : ℕ) : ℕ :=
  selectFour ((x ^ 3 - R) ^ 3) (integerBaseline x z R)

theorem recoverPeak_eq {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    recoverPeak x z R = (u ^ 3).sqrt := by
  have he : integerBaseline x z R = correctedBaseline x z R := by
    unfold integerBaseline correctedBaseline
    rw [corrected_quotient_integer hu hz hmin hR]
  unfold recoverPeak
  rw [he]
  exact selectFour_eq (retained_fourth_cell hu hR)
    (corrected_baseline_bounds hu hz hmin hR).1
    (corrected_baseline_bounds hu hz hmin hR).2

theorem recoverPeak_guard_iff {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) (hx : x % 2 = 1) :
    (u % 2 = 1 ∧ (u ^ 3).sqrt % 2 = 0) ↔
      (R % 2 = 0 ∧ recoverPeak x z R % 2 = 0) := by
  rw [recoverPeak_eq hu hz hmin hR, first_guard_iff hu hR hx]

end Problems.Juggler.RemainderCarry
