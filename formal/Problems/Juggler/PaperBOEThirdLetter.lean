/-
# Paper B, Proposition 3.2: the OE third letter

`docs/theory/juggler_parity_discrepancy_note.md`, Proposition 3.2. An odd start `n = 2r+1`
has word `OE·` exactly when `⌊n^{3/2}⌋` is even, and its third letter is the parity of
`⌊⌊n^{3/2}⌋^{1/2}⌋ = ⌊n^{3/4}⌋`. The two words `OEE` and `OEO` are therefore box counts
for the torus points `({n^{3/2}/2}, {n^{3/4}/2})`, in boxes of area `1/4`.

This module holds the exact part:

* `floor_sqrt_eq_sqrt_floor`: `⌊√x⌋₊ = Nat.sqrt ⌊x⌋₊` for `x ≥ 0`;
* `word3_oee_iff`, `word3_oeo_iff`: the two words as parities of `Nat.sqrt (n^3)` and
  `Nat.sqrt (Nat.sqrt (n^3))`;
* `torusPoint` and `torusPoint_mem_iff`: those parities as membership of the torus point in a
  box `[0, 1/2) × [0, 1/2)` or `[0, 1/2) × [1/2, 1)`.
-/

import BTCalculus.ErdosTuranBox
import Problems.Juggler.PaperBSingleFloorBound

attribute [local instance] Classical.propDecidable

namespace Problems.Juggler

namespace PaperBOEThirdLetter

open Finset Real
open BTCalculus.FejerArc BTCalculus.ErdosTuranBox
open PaperBSingleFloor

/-! ## The floor of a square root -/

/-- `⌊√x⌋₊ = Nat.sqrt ⌊x⌋₊` for `x ≥ 0`: for an integer `s ≥ 0`, `s² ≤ ⌊x⌋` and `s² ≤ x`
are equivalent. -/
theorem floor_sqrt_eq_sqrt_floor {x : ℝ} (hx : 0 ≤ x) : ⌊√x⌋₊ = Nat.sqrt ⌊x⌋₊ := by
  set s := Nat.sqrt ⌊x⌋₊ with hs
  rw [Nat.floor_eq_iff (sqrt_nonneg x)]
  have hsq : s * s ≤ ⌊x⌋₊ := Nat.sqrt_le ⌊x⌋₊
  have hlt : ⌊x⌋₊ < (s + 1) * (s + 1) := Nat.lt_succ_sqrt ⌊x⌋₊
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hfl' : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hsq' : (s : ℝ) * s ≤ ⌊x⌋₊ := by exact_mod_cast hsq
  have hlt' : (⌊x⌋₊ : ℝ) + 1 ≤ ((s : ℝ) + 1) * ((s : ℝ) + 1) := by
    exact_mod_cast (show ⌊x⌋₊ + 1 ≤ (s + 1) * (s + 1) by omega)
  constructor
  · rw [le_sqrt (Nat.cast_nonneg _) hx]
    nlinarith
  · rw [sqrt_lt' (by positivity)]
    nlinarith

/-- `n^{3/4} = √√(n^3)` for a natural `n`. -/
theorem rpow_three_quarters_eq (n : ℕ) :
    (n : ℝ) ^ (3 / 4 : ℝ) = √(√((n ^ 3 : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [sqrt_eq_rpow, sqrt_eq_rpow, ← rpow_mul (by positivity)]
  push_cast
  rw [← rpow_natCast, ← rpow_mul hn]
  norm_num

/-- `⌊n^{3/4}⌋₊ = Nat.sqrt (Nat.sqrt (n^3))`. -/
theorem floor_rpow_three_quarters (n : ℕ) :
    ⌊(n : ℝ) ^ (3 / 4 : ℝ)⌋₊ = Nat.sqrt (Nat.sqrt (n ^ 3)) := by
  rw [rpow_three_quarters_eq, floor_sqrt_eq_sqrt_floor (sqrt_nonneg _),
    nat_floor_real_sqrt_eq_nat_sqrt]

/-! ## The third letter -/

/-- The length-three itinerary of `n`, letter by letter. -/
theorem itinerary_three (n : ℕ) :
    itinerary n 3 = [bit n, bit (floorPower n), bit (floorPower (floorPower n))] := rfl

/-- An odd start has word `OEE` exactly when `Nat.sqrt (n^3)` and
`Nat.sqrt (Nat.sqrt (n^3))` are both even. -/
theorem word3_oee_iff {n : ℕ} (hn : n % 2 = 1) :
    itinerary n 3 = [.odd, .even, .even] ↔
      Nat.sqrt (n ^ 3) % 2 = 0 ∧ Nat.sqrt (Nat.sqrt (n ^ 3)) % 2 = 0 := by
  rw [itinerary_three, floorPower_odd_eq hn]
  have hb : bit n = .odd := bit_odd hn
  rw [hb]
  by_cases h1 : Nat.sqrt (n ^ 3) % 2 = 0
  · rw [floorPower_even_eq h1, bit_even h1]
    by_cases h2 : Nat.sqrt (Nat.sqrt (n ^ 3)) % 2 = 0
    · simp [bit_even h2, h1, h2]
    · have h2' : Nat.sqrt (Nat.sqrt (n ^ 3)) % 2 = 1 := by omega
      simp [bit_odd h2', h2]
  · have h1' : Nat.sqrt (n ^ 3) % 2 = 1 := by omega
    simp [bit_odd h1', h1]

/-- An odd start has word `OEO` exactly when `Nat.sqrt (n^3)` is even and
`Nat.sqrt (Nat.sqrt (n^3))` is odd. -/
theorem word3_oeo_iff {n : ℕ} (hn : n % 2 = 1) :
    itinerary n 3 = [.odd, .even, .odd] ↔
      Nat.sqrt (n ^ 3) % 2 = 0 ∧ Nat.sqrt (Nat.sqrt (n ^ 3)) % 2 = 1 := by
  rw [itinerary_three, floorPower_odd_eq hn]
  have hb : bit n = .odd := bit_odd hn
  rw [hb]
  by_cases h1 : Nat.sqrt (n ^ 3) % 2 = 0
  · rw [floorPower_even_eq h1, bit_even h1]
    by_cases h2 : Nat.sqrt (Nat.sqrt (n ^ 3)) % 2 = 0
    · simp [bit_even h2, h1, h2]
    · have h2' : Nat.sqrt (Nat.sqrt (n ^ 3)) % 2 = 1 := by omega
      simp [bit_odd h2', h1, h2']
  · have h1' : Nat.sqrt (n ^ 3) % 2 = 1 := by omega
    simp [bit_odd h1', h1]

/-- An even start never has a word beginning with `O`. -/
theorem word3_head_odd {n : ℕ} {w : List Branch} (hw : itinerary n 3 = .odd :: w) :
    n % 2 = 1 := by
  rw [itinerary_three] at hw
  have h := List.head_eq_of_cons_eq hw
  unfold bit at h
  split_ifs at h with hn
  omega

/-! ## The torus point -/

/-- The second phase `h(r) = (1/2)(2r+1)^{3/4}`. -/
noncomputable def phaseQ (r : ℝ) : ℝ := (1 / 2) * (2 * r + 1) ^ (3 / 4 : ℝ)

/-- The torus point of the odd start `2r+1`: `(g(r), h(r))` modulo one. -/
noncomputable def torusPoint (r : ℝ) : UnitAddCircle × UnitAddCircle :=
  ((phaseG r : UnitAddCircle), (phaseQ r : UnitAddCircle))

/-- A point of the circle lies in the arc `[a, b)` exactly when its fractional part does. -/
theorem coe_mem_arc_iff_fract {a b x : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (x : UnitAddCircle) ∈ arc a b ↔ a ≤ Int.fract x ∧ Int.fract x < b := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hu01 : u ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨ha.trans hu.1, by linarith [hu.2]⟩
    have hx01 : Int.fract x ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one x⟩
    have he' : (u : UnitAddCircle) = ((Int.fract x : ℝ) : UnitAddCircle) := by
      simpa only [AddCircle.coe_fract] using he
    have hu' := (AddCircle.coe_eq_coe_iff_of_mem_Ico hu01 hx01).1 he'
    simpa only [hu', Set.mem_Ico] using hu
  · intro hx
    exact ⟨Int.fract x, hx, AddCircle.coe_fract x⟩

/-- `y/2` lies in `[0, 1/2)` modulo one exactly when `⌊y⌋` is even. -/
theorem half_mem_lower_iff (y : ℝ) :
    ((y / 2 : ℝ) : UnitAddCircle) ∈ arc 0 (1 / 2) ↔ ⌊y⌋ % 2 = 0 := by
  rw [coe_mem_arc_iff_fract le_rfl (by norm_num), fract_lt_half_iff,
    show 2 * (y / 2) = y by ring]
  exact and_iff_right (Int.fract_nonneg _)

/-- `y/2` lies in `[1/2, 1)` modulo one exactly when `⌊y⌋` is odd. -/
theorem half_mem_upper_iff (y : ℝ) :
    ((y / 2 : ℝ) : UnitAddCircle) ∈ arc (1 / 2) 1 ↔ ⌊y⌋ % 2 = 1 := by
  rw [coe_mem_arc_iff_fract (by norm_num) le_rfl]
  have h := fract_lt_half_iff (y / 2)
  rw [show 2 * (y / 2) = y by ring] at h
  constructor
  · rintro ⟨h1, -⟩
    by_contra hne
    have : ⌊y⌋ % 2 = 0 := by omega
    linarith [h.mpr this]
  · intro hodd
    refine ⟨?_, Int.fract_lt_one _⟩
    by_contra hlt
    have := h.mp (not_le.mp hlt)
    omega

/-- The first coordinate is `⌊(2r+1)^{3/2}⌋ / 2` in the sense of parity. -/
theorem phaseG_eq_half (r : ℕ) :
    phaseG (r : ℝ) = (((2 * r + 1 : ℕ) : ℝ) * √((2 * r + 1 : ℕ) : ℝ)) / 2 := by
  rw [← two_mul_phaseG_natCast]
  ring

/-- The second coordinate is `(2r+1)^{3/4} / 2`. -/
theorem phaseQ_eq_half (r : ℕ) :
    phaseQ (r : ℝ) = (((2 * r + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)) / 2 := by
  simp only [phaseQ]
  push_cast
  ring

/-- `⌊(2r+1)^{3/4}⌋ = Nat.sqrt (Nat.sqrt ((2r+1)^3))` as an integer floor. -/
theorem int_floor_rpow_three_quarters (n : ℕ) :
    ⌊(n : ℝ) ^ (3 / 4 : ℝ)⌋ = ((Nat.sqrt (Nat.sqrt (n ^ 3)) : ℕ) : ℤ) := by
  rw [← floor_rpow_three_quarters, Int.natCast_floor_eq_floor (by positivity)]

/-- **The box of `OEE`.** The odd start `2r+1` has word `OEE` exactly when its torus point
lies in `[0, 1/2) × [0, 1/2)`. -/
theorem torusPoint_mem_oee_iff (r : ℕ) :
    ((torusPoint r).1 ∈ arc 0 (1 / 2) ∧ (torusPoint r).2 ∈ arc 0 (1 / 2)) ↔
      itinerary (2 * r + 1) 3 = [.odd, .even, .even] := by
  rw [word3_oee_iff (by omega)]
  simp only [torusPoint]
  rw [phaseG_eq_half, phaseQ_eq_half, half_mem_lower_iff, half_mem_lower_iff, floor_pow32,
    int_floor_rpow_three_quarters]
  omega

/-- **The box of `OEO`.** The odd start `2r+1` has word `OEO` exactly when its torus point
lies in `[0, 1/2) × [1/2, 1)`. -/
theorem torusPoint_mem_oeo_iff (r : ℕ) :
    ((torusPoint r).1 ∈ arc 0 (1 / 2) ∧ (torusPoint r).2 ∈ arc (1 / 2) 1) ↔
      itinerary (2 * r + 1) 3 = [.odd, .even, .odd] := by
  rw [word3_oeo_iff (by omega)]
  simp only [torusPoint]
  rw [phaseG_eq_half, phaseQ_eq_half, half_mem_lower_iff, half_mem_upper_iff, floor_pow32,
    int_floor_rpow_three_quarters]
  omega

/-! ## Derivatives of the second phase -/

/-- `h'(r) = (3/4)(2r+1)^{-1/4}` wherever `2r+1 > 0`. -/
theorem hasDerivAt_phaseQ {x : ℝ} (hx : 0 < 2 * x + 1) :
    HasDerivAt phaseQ ((3 / 4) * (2 * x + 1) ^ (-1 / 4 : ℝ)) x := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * t + 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const 1
  have hp := (hasDerivAt_rpow_const (p := (3 / 4 : ℝ)) (Or.inl hx.ne')).comp x hlin
  have h := hp.const_mul (1 / 2 : ℝ)
  have hfun : (fun y => (1 / 2 : ℝ) * ((fun x : ℝ => x ^ (3 / 4 : ℝ)) ∘ fun t => 2 * t + 1) y) =
      phaseQ := by
    funext t
    simp [phaseQ]
  have hder : (1 / 2 : ℝ) * ((3 / 4) * (2 * x + 1) ^ ((3 / 4 : ℝ) - 1) * 2) =
      (3 / 4) * (2 * x + 1) ^ (-1 / 4 : ℝ) := by
    rw [show (3 / 4 : ℝ) - 1 = -1 / 4 by norm_num]
    ring
  rw [hfun, hder] at h
  exact h

/-- `h''(r) = -(3/8)(2r+1)^{-5/4}` wherever `2r+1 > 0`. -/
theorem hasDerivAt_phaseQ' {x : ℝ} (hx : 0 < 2 * x + 1) :
    HasDerivAt (fun t => (3 / 4) * (2 * t + 1) ^ (-1 / 4 : ℝ))
      (-(3 / 8) * (2 * x + 1) ^ (-5 / 4 : ℝ)) x := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * t + 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const 1
  have hp := (hasDerivAt_rpow_const (p := (-1 / 4 : ℝ)) (Or.inl hx.ne')).comp x hlin
  have h := hp.const_mul (3 / 4 : ℝ)
  have hfun : (fun y => (3 / 4 : ℝ) * ((fun x : ℝ => x ^ (-1 / 4 : ℝ)) ∘ fun t => 2 * t + 1) y) =
      fun t => (3 / 4) * (2 * t + 1) ^ (-1 / 4 : ℝ) := by
    funext t
    simp
  have hder : (3 / 4 : ℝ) * ((-1 / 4) * (2 * x + 1) ^ ((-1 / 4 : ℝ) - 1) * 2) =
      -(3 / 8) * (2 * x + 1) ^ (-5 / 4 : ℝ) := by
    rw [show (-1 / 4 : ℝ) - 1 = -5 / 4 by norm_num]
    ring
  rw [hfun, hder] at h
  exact h

/-! ## Fourier modes of the torus point -/

/-- `e(k x)` on the circle is the phase `e(k x)` on the line. -/
theorem fourier_coe_eq_phase (k : ℤ) (x : ℝ) :
    fourier k (x : UnitAddCircle) = BTCalculus.WeylDifferencing.phase ((k : ℝ) * x) := by
  rw [fourier_coe_apply]
  unfold BTCalculus.WeylDifferencing.phase
  congr 1
  push_cast
  simp only [div_one]
  ring

/-- One torus mode is one phase of the mixed function `k g + l h`. -/
theorem mode_torusPoint (k l : ℤ) (x : ℝ) :
    BTCalculus.FejerBox.mode k l (torusPoint x) =
      BTCalculus.WeylDifferencing.phase ((k : ℝ) * phaseG x + (l : ℝ) * phaseQ x) := by
  simp only [BTCalculus.FejerBox.mode, torusPoint, fourier_coe_eq_phase]
  unfold BTCalculus.WeylDifferencing.phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## Curvature on one block -/

/-- `X^{-5/4} = X^{-1/2} X^{-3/4}` and `X^{-1/2} = 1/√X` for `X > 0`. -/
theorem rpow_neg_five_quarters {X : ℝ} (hX : 0 < X) :
    X ^ (-5 / 4 : ℝ) = (1 / √X) * (1 / X ^ (3 / 4 : ℝ)) := by
  rw [show (-5 / 4 : ℝ) = -(1 / 2) + -(3 / 4) by norm_num, rpow_add hX,
    rpow_neg hX.le, rpow_neg hX.le, ← sqrt_eq_rpow]
  ring

/-- The `n^{3/4}` curvature is at most a quarter of the `n^{3/2}` curvature once
`|l| ≤ X^{3/4}` and `i ≥ 1`. -/
theorem small_curvature {X l i : ℝ} (hX : 0 < X) (hl : |l| ≤ X ^ (3 / 4 : ℝ)) (hi : 1 ≤ i) :
    |l * ((3 / 8) * X ^ (-5 / 4 : ℝ))| ≤ (1 / 4) * (i * ((3 / 2) / √X)) := by
  have hs : 0 < √X := sqrt_pos.mpr hX
  have hp : 0 < X ^ (3 / 4 : ℝ) := rpow_pos_of_pos hX _
  rw [rpow_neg_five_quarters hX, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 3 / 8 * (1 / √X * (1 / X ^ (3 / 4 : ℝ))) by positivity)]
  have hq : |l| * (1 / X ^ (3 / 4 : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one hp]
    exact hl
  have h1 : 0 ≤ 1 / √X := by positivity
  calc |l| * (3 / 8 * (1 / √X * (1 / X ^ (3 / 4 : ℝ))))
      = (3 / 8) * (1 / √X) * (|l| * (1 / X ^ (3 / 4 : ℝ))) := by ring
    _ ≤ (3 / 8) * (1 / √X) * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ (3 / 8) * (1 / √X) * i := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (1 / 4) * (i * ((3 / 2) / √X)) := by ring

/-- **Modes with `i ≥ 1`.** On a block `[a, a+M]` with `1 ≤ a`, `M ≤ a` and
`|l| ≤ a^{3/4}`, the mixed sum is at most `14 M √λ + 10/√λ`,
`λ = i (3/2) / √(2(a+M)+1)`. -/
theorem mixed_mode_bound {a : ℝ} {M i : ℕ} {l : ℝ} (ha : 1 ≤ a) (hM : (M : ℝ) ≤ a)
    (hi : 1 ≤ i) (hl : |l| ≤ a ^ (3 / 4 : ℝ)) :
    ‖∑ n ∈ range M, BTCalculus.WeylDifferencing.phase
        ((i : ℝ) * phaseG (a + n) + l * phaseQ (a + n))‖ ≤
      14 * M * √((i : ℝ) * (3 / 2) / √(2 * (a + M) + 1)) +
        10 / √((i : ℝ) * (3 / 2) / √(2 * (a + M) + 1)) := by
  set lam := (i : ℝ) * (3 / 2) / √(2 * (a + M) + 1) with hlam
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hlam0 : 0 < lam := div_pos (by linarith) (sqrt_pos.mpr (by positivity))
  have hb := BTCalculus.SecondDerivative.signed_second_derivative_sum_bound
    (fun x => (i : ℝ) * phaseG x + l * phaseQ x)
    (fun x => (i : ℝ) * ((3 / 2) * √(2 * x + 1)) + l * ((3 / 4) * (2 * x + 1) ^ (-1 / 4 : ℝ)))
    (fun x => (i : ℝ) * ((3 / 2) / √(2 * x + 1)) +
      l * (-(3 / 8) * (2 * x + 1) ^ (-5 / 4 : ℝ)))
    a M (lam := (3 / 4) * lam) (C := 10 / 3) (by positivity) (by norm_num)
    (fun x hx => by
      have hx1 : 0 < 2 * x + 1 := by linarith [hx.1]
      exact ((hasDerivAt_phaseG hx1).const_mul _).add ((hasDerivAt_phaseQ hx1).const_mul _))
    (fun x hx => by
      have hx1 : 0 < 2 * x + 1 := by linarith [hx.1]
      exact ((hasDerivAt_phaseG' hx1).const_mul _).add ((hasDerivAt_phaseQ' hx1).const_mul _))
    (Or.inl (fun x hx => by
      have hx1 : 0 < 2 * x + 1 := by linarith [hx.1]
      obtain ⟨hlo, hhi⟩ := block_curvature ha hM hi hx
      have hX : a ^ (3 / 4 : ℝ) ≤ (2 * x + 1) ^ (3 / 4 : ℝ) :=
        rpow_le_rpow (by linarith) (by linarith [hx.1]) (by norm_num)
      have he := small_curvature hx1 (hl.trans hX) hi1
      have he' := abs_le.mp he
      have hmain : 0 ≤ (i : ℝ) * ((3 / 2) / √(2 * x + 1)) := by positivity
      constructor
      · have : l * (-(3 / 8) * (2 * x + 1) ^ (-5 / 4 : ℝ)) =
            -(l * ((3 / 8) * (2 * x + 1) ^ (-5 / 4 : ℝ))) := by ring
        rw [this]
        change lam ≤ _ at hlo
        linarith [he'.2]
      · have : l * (-(3 / 8) * (2 * x + 1) ^ (-5 / 4 : ℝ)) =
            -(l * ((3 / 8) * (2 * x + 1) ^ (-5 / 4 : ℝ))) := by ring
        rw [this]
        change _ ≤ 2 * lam at hhi
        linarith [he'.1]))
  have hs : √((3 / 4) * lam) ≤ √lam := sqrt_le_sqrt (by linarith)
  have hs0 : 0 < √lam := sqrt_pos.mpr hlam0
  have hinv : 8 / √((3 / 4) * lam) ≤ 10 / √lam := by
    rw [sqrt_mul (by norm_num), div_le_div_iff₀ (by positivity) hs0]
    have h34 : (4 / 5 : ℝ) ≤ √(3 / 4) := by
      rw [le_sqrt (by norm_num) (by norm_num)]
      norm_num
    nlinarith
  calc _ ≤ 4 * (10 / 3) * M * √((3 / 4) * lam) + 8 / √((3 / 4) * lam) := hb
    _ ≤ 14 * M * √lam + 10 / √lam := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith

/-- `Y^{-5/4} ≤ X^{-5/4} ≤ 4 Y^{-5/4}` for `Y/2 ≤ X ≤ Y`. -/
theorem rpow_neg_five_quarters_bounds {X Y : ℝ} (hY : 0 < Y) (h1 : Y / 2 ≤ X) (h2 : X ≤ Y) :
    Y ^ (-5 / 4 : ℝ) ≤ X ^ (-5 / 4 : ℝ) ∧ X ^ (-5 / 4 : ℝ) ≤ 4 * Y ^ (-5 / 4 : ℝ) := by
  have hX : 0 < X := by linarith
  have e (Z : ℝ) (hZ : 0 < Z) : Z ^ (-5 / 4 : ℝ) = 1 / Z ^ (5 / 4 : ℝ) := by
    rw [show (-5 / 4 : ℝ) = -(5 / 4) by norm_num, rpow_neg hZ.le, one_div]
  rw [e X hX, e Y hY]
  have hXp : 0 < X ^ (5 / 4 : ℝ) := rpow_pos_of_pos hX _
  have hYp : 0 < Y ^ (5 / 4 : ℝ) := rpow_pos_of_pos hY _
  constructor
  · exact one_div_le_one_div_of_le hXp (rpow_le_rpow hX.le h2 (by norm_num))
  · have hh : (Y / 2) ^ (5 / 4 : ℝ) ≤ X ^ (5 / 4 : ℝ) := rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [div_rpow hY.le (by norm_num)] at hh
    have h2p : (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 4 := by
      calc (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 2 ^ (2 : ℝ) :=
            rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := by norm_num
    have h2p0 : 0 < (2 : ℝ) ^ (5 / 4 : ℝ) := rpow_pos_of_pos (by norm_num) _
    rw [div_le_iff₀ h2p0] at hh
    rw [div_le_iff₀ hXp]
    calc 1 = (1 / Y ^ (5 / 4 : ℝ)) * Y ^ (5 / 4 : ℝ) := by field_simp
      _ ≤ (1 / Y ^ (5 / 4 : ℝ)) * (X ^ (5 / 4 : ℝ) * 2 ^ (5 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ (1 / Y ^ (5 / 4 : ℝ)) * (X ^ (5 / 4 : ℝ) * 4) := by gcongr
      _ = 4 * (1 / Y ^ (5 / 4 : ℝ)) * X ^ (5 / 4 : ℝ) := by ring

/-- **Modes with `i = 0`.** On a block `[a, a+M]` with `1 ≤ a` and `M ≤ a`, the sum of
`e(l h(r))` for `l ≠ 0` is at most `16 M √μ + 8/√μ`, `μ = |l| (3/8) (2(a+M)+1)^{-5/4}`. -/
theorem quarter_mode_bound {a : ℝ} {M : ℕ} {l : ℝ} (ha : 1 ≤ a) (hM : (M : ℝ) ≤ a)
    (hl : l ≠ 0) :
    ‖∑ n ∈ range M, BTCalculus.WeylDifferencing.phase (l * phaseQ (a + n))‖ ≤
      16 * M * √(|l| * (3 / 8) * (2 * (a + M) + 1) ^ (-5 / 4 : ℝ)) +
        8 / √(|l| * (3 / 8) * (2 * (a + M) + 1) ^ (-5 / 4 : ℝ)) := by
  set Y := 2 * (a + M) + 1 with hYdef
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hY : 0 < Y := by positivity
  have hYp : 0 < Y ^ (-5 / 4 : ℝ) := rpow_pos_of_pos hY _
  have hl0 : 0 < |l| := abs_pos.mpr hl
  set mu := |l| * (3 / 8) * Y ^ (-5 / 4 : ℝ) with hmu
  have hmu0 : 0 < mu := by positivity
  have hbounds : ∀ x ∈ Set.Icc a (a + M),
      Y ^ (-5 / 4 : ℝ) ≤ (2 * x + 1) ^ (-5 / 4 : ℝ) ∧
        (2 * x + 1) ^ (-5 / 4 : ℝ) ≤ 4 * Y ^ (-5 / 4 : ℝ) := fun x hx =>
    rpow_neg_five_quarters_bounds hY (by rw [hYdef]; linarith [hx.1]) (by rw [hYdef]; linarith [hx.2])
  have hb := BTCalculus.SecondDerivative.signed_second_derivative_sum_bound
    (fun x => l * phaseQ x)
    (fun x => l * ((3 / 4) * (2 * x + 1) ^ (-1 / 4 : ℝ)))
    (fun x => l * (-(3 / 8) * (2 * x + 1) ^ (-5 / 4 : ℝ)))
    a M (lam := mu) (C := 4) hmu0 (by norm_num)
    (fun x hx => by
      have hx1 : 0 < 2 * x + 1 := by linarith [hx.1]
      exact (hasDerivAt_phaseQ hx1).const_mul _)
    (fun x hx => by
      have hx1 : 0 < 2 * x + 1 := by linarith [hx.1]
      exact (hasDerivAt_phaseQ' hx1).const_mul _)
    (by
      rcases lt_or_gt_of_ne hl with hneg | hpos
      · left
        intro x hx
        obtain ⟨h1, h2⟩ := hbounds x hx
        have habs : |l| = -l := abs_of_neg hneg
        rw [hmu, habs]
        constructor <;> nlinarith
      · right
        intro x hx
        obtain ⟨h1, h2⟩ := hbounds x hx
        have habs : |l| = l := abs_of_pos hpos
        rw [hmu, habs]
        constructor <;> nlinarith)
  exact hb.trans (le_of_eq (by ring))

end PaperBOEThirdLetter

end Problems.Juggler
