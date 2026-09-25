/-
# Paper B, Proposition 3.2: the OE third letter

`docs/theory/juggler_parity_discrepancy_note.md`, Proposition 3.2. An odd start `n = 2r+1`
has word `OE·` exactly when `⌊n^{3/2}⌋` is even, and its third letter is the parity of
`⌊⌊n^{3/2}⌋^{1/2}⌋ = ⌊n^{3/4}⌋`. The two words `OEE` and `OEO` are therefore box counts
for the torus points `({n^{3/2}/2}, {n^{3/4}/2})`, in boxes of area `1/4`.

* `floor_sqrt_eq_sqrt_floor`: `⌊√x⌋₊ = Nat.sqrt ⌊x⌋₊` for `x ≥ 0`;
* `word3_oee_iff`, `word3_oeo_iff`, `torusPoint_mem_oee_iff`, `torusPoint_mem_oeo_iff`: the
  two words as the boxes `[0, 1/2) × [0, 1/2)` and `[0, 1/2) × [1/2, 1)`;
* `mixed_mode_bound`, `quarter_mode_bound`: the second-derivative test for the modes of a
  block `[a, a+M)`, `M ≤ a`; for `i ≠ 0` and `|l| ≤ a^{3/4}` the `n^{3/4}` curvature is at
  most a quarter of the `n^{3/2}` curvature (`small_curvature`);
* `abs_block_boxError_le`: the two-dimensional Erdős–Turán inequality
  `BTCalculus.ErdosTuranBox` at `H = ⌊a^{1/6}⌋` bounds the block discrepancy by
  `1712 a^{5/6} (1 + log a)`;
* `abs_oe_boxError_le`: halving at `⌈R/2⌉` gives `6848 R^{5/6} (1 + log R)`;
* `abs_oeeCount_sub_le`, `abs_oeoCount_sub_le`: Proposition 3.2 with explicit constants,
  `|#{n ≤ N : word_3(n) = w} - N/8| ≤ 6849 N^{5/6} (1 + log N)` for `w = OEE, OEO`.
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

/-! ## One block -/

section Block

open scoped ComplexConjugate
open BTCalculus.WeylDifferencing

/-- A block mode sum, written as phases of the mixed function `k g + l h`. -/
theorem block_mode_sum_eq (a : ℝ) (M : ℕ) (k l : ℤ) :
    ∑ n ∈ range M, BTCalculus.FejerBox.mode k l (torusPoint (a + n)) =
      ∑ n ∈ range M, phase ((k : ℝ) * phaseG (a + n) + (l : ℝ) * phaseQ (a + n)) := by
  simp only [mode_torusPoint]

/-- Negating both frequencies conjugates a block mode sum. -/
theorem norm_block_mode_neg (a : ℝ) (M : ℕ) (k l : ℤ) :
    ‖∑ n ∈ range M, BTCalculus.FejerBox.mode (-k) (-l) (torusPoint (a + n))‖ =
      ‖∑ n ∈ range M, BTCalculus.FejerBox.mode k l (torusPoint (a + n))‖ := by
  rw [block_mode_sum_eq, block_mode_sum_eq]
  have h : ∀ n ∈ range M,
      phase (((-k : ℤ) : ℝ) * phaseG (a + n) + ((-l : ℤ) : ℝ) * phaseQ (a + n)) =
        conj (phase ((k : ℝ) * phaseG (a + n) + (l : ℝ) * phaseQ (a + n))) := by
    intro n _
    rw [← BTCalculus.SecondDerivative.phase_neg]
    congr 1
    push_cast
    ring
  rw [sum_congr rfl h, ← map_sum (starRingEnd ℂ), Complex.norm_conj]

/-- `(u^{12})^p = u^k` when `12 p = k`. -/
theorem pow_twelve_rpow {u : ℝ} (hu : 0 ≤ u) {p : ℝ} {k : ℕ} (hk : 12 * p = k) :
    (u ^ 12) ^ p = u ^ k := by
  rw [← rpow_natCast u 12, ← rpow_mul hu, show ((12 : ℕ) : ℝ) * p = k by push_cast; linarith,
    rpow_natCast]

/-- A nonzero integer frequency has absolute value at least one. -/
theorem one_le_abs_intCast {l : ℤ} (hl : l ≠ 0) : (1 : ℝ) ≤ |(l : ℝ)| := by
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hl

/-- **The modes `(0, l)` of a block at scale `a = u^{12}`.** For `0 < |l| ≤ u^2`, the sum is
at most `88 u^8`. -/
theorem zero_mode_le {a u : ℝ} {M : ℕ} {l : ℤ} (hu1 : 1 ≤ u) (hua : u ^ 12 = a)
    (hM : (M : ℝ) ≤ a) (hl0 : l ≠ 0) (hlH : |(l : ℝ)| ≤ u ^ 2) :
    ‖∑ n ∈ range M, BTCalculus.FejerBox.mode 0 l (torusPoint (a + n))‖ ≤ 88 * u ^ 8 := by
  have hu0 : 0 < u := by linarith
  have ha : 1 ≤ a := by rw [← hua]; exact one_le_pow₀ hu1
  rw [block_mode_sum_eq]
  simp only [Int.cast_zero, zero_mul, zero_add]
  have hl1 := one_le_abs_intCast hl0
  have hb := quarter_mode_bound ha hM (l := (l : ℝ)) (by exact_mod_cast hl0)
  set Y := 2 * (a + M) + 1 with hYdef
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hYa : a ≤ Y := by rw [hYdef]; linarith
  have hY5 : Y ≤ 5 * a := by rw [hYdef]; linarith
  have ha0 : 0 < a := by linarith
  have hY0 : 0 < Y := by linarith
  have hA : a ^ (5 / 4 : ℝ) = u ^ 15 := by
    rw [← hua]; exact pow_twelve_rpow hu0.le (by norm_num)
  have e (Z : ℝ) (hZ : 0 < Z) : Z ^ (-5 / 4 : ℝ) = 1 / Z ^ (5 / 4 : ℝ) := by
    rw [show (-5 / 4 : ℝ) = -(5 / 4) by norm_num, rpow_neg hZ.le, one_div]
  have hu15 : 0 < u ^ 15 := by positivity
  have hYp : 0 < Y ^ (5 / 4 : ℝ) := rpow_pos_of_pos hY0 _
  have hup : Y ^ (-5 / 4 : ℝ) ≤ 1 / u ^ 15 := by
    rw [e Y hY0, ← hA]
    exact one_div_le_one_div_of_le (rpow_pos_of_pos ha0 _) (rpow_le_rpow ha0.le hYa (by norm_num))
  have hlo : 1 / (25 * u ^ 15) ≤ Y ^ (-5 / 4 : ℝ) := by
    rw [e Y hY0]
    apply one_div_le_one_div_of_le hYp
    calc Y ^ (5 / 4 : ℝ) ≤ (5 * a) ^ (5 / 4 : ℝ) := rpow_le_rpow hY0.le hY5 (by norm_num)
      _ = 5 ^ (5 / 4 : ℝ) * a ^ (5 / 4 : ℝ) := mul_rpow (by norm_num) ha0.le
      _ ≤ 25 * u ^ 15 := by
        rw [hA]
        have h5 : (5 : ℝ) ^ (5 / 4 : ℝ) ≤ 25 := by
          calc (5 : ℝ) ^ (5 / 4 : ℝ) ≤ 5 ^ (2 : ℝ) :=
                rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 25 := by norm_num
        exact mul_le_mul_of_nonneg_right h5 hu15.le
  set mu := |(l : ℝ)| * (3 / 8) * Y ^ (-5 / 4 : ℝ) with hmu
  have hmu_hi : mu ≤ 1 / u ^ 12 := by
    have h1 : mu ≤ u ^ 2 * (3 / 8) * (1 / u ^ 15) := by
      rw [hmu]
      have hYn : 0 ≤ Y ^ (-5 / 4 : ℝ) := (rpow_pos_of_pos hY0 _).le
      calc |(l : ℝ)| * (3 / 8) * Y ^ (-5 / 4 : ℝ) ≤ u ^ 2 * (3 / 8) * Y ^ (-5 / 4 : ℝ) := by
            gcongr
        _ ≤ u ^ 2 * (3 / 8) * (1 / u ^ 15) := by gcongr
    have h2 : u ^ 2 * (3 / 8) * (1 / u ^ 15) ≤ 1 / u ^ 12 := by
      rw [show u ^ 2 * (3 / 8) * (1 / u ^ 15) = (3 / 8) * (1 / u ^ 12) * (1 / u) by
        field_simp]
      have hinv : 1 / u ≤ 1 := by rw [div_le_one hu0]; exact hu1
      have hp : 0 ≤ 1 / u ^ 12 := by positivity
      nlinarith
    linarith
  have hmu_lo : 1 / (81 * u ^ 16) ≤ mu := by
    have h1 : 1 * (3 / 8) * (1 / (25 * u ^ 15)) ≤ mu := by
      rw [hmu]
      gcongr
    have h2 : 1 / (81 * u ^ 16) ≤ 1 * (3 / 8) * (1 / (25 * u ^ 15)) := by
      rw [show (1 : ℝ) * (3 / 8) * (1 / (25 * u ^ 15)) = 3 / (200 * u ^ 15) by field_simp; ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : u ^ 15 ≤ u ^ 16 := pow_le_pow_right₀ hu1 (by norm_num)
      nlinarith
    linarith
  have hmu0 : 0 < mu := lt_of_lt_of_le (by positivity) hmu_lo
  have hs1 : √mu ≤ 1 / u ^ 6 := by
    rw [sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, one_pow, ← pow_mul]
    exact hmu_hi
  have hs2 : 1 / √mu ≤ 9 * u ^ 8 := by
    have hl : 1 / (9 * u ^ 8) ≤ √mu := by
      rw [le_sqrt (by positivity) hmu0.le]
      calc (1 / (9 * u ^ 8)) ^ 2 = 1 / (81 * u ^ 16) := by ring
        _ ≤ mu := hmu_lo
    calc 1 / √mu ≤ 1 / (1 / (9 * u ^ 8)) := one_div_le_one_div_of_le (by positivity) hl
      _ = 9 * u ^ 8 := by field_simp
  have hMu : (M : ℝ) ≤ u ^ 12 := hM.trans_eq hua.symm
  have h6 : u ^ 6 ≤ u ^ 8 := pow_le_pow_right₀ hu1 (by norm_num)
  have hA1 : 16 * (M : ℝ) * √mu ≤ 16 * u ^ 8 := by
    calc 16 * (M : ℝ) * √mu ≤ 16 * u ^ 12 * (1 / u ^ 6) := by gcongr
      _ = 16 * u ^ 6 := by field_simp
      _ ≤ 16 * u ^ 8 := by linarith
  have hA2 : 8 / √mu ≤ 72 * u ^ 8 := by
    rw [show 8 / √mu = 8 * (1 / √mu) by ring]
    linarith
  linarith

/-- **The modes `(k, l)` with `k ≥ 1` of a block at scale `a = u^{12}`.** For `|l| ≤ u^2`, the
sum is at most `48 u^9 √k`. -/
theorem pos_mode_le {a u : ℝ} {M : ℕ} {k : ℕ} {l : ℤ} (hu1 : 1 ≤ u) (hua : u ^ 12 = a)
    (hM : (M : ℝ) ≤ a) (hk : 1 ≤ k) (hlH : |(l : ℝ)| ≤ u ^ 2) :
    ‖∑ n ∈ range M, BTCalculus.FejerBox.mode (k : ℤ) l (torusPoint (a + n))‖ ≤
      48 * u ^ 9 * √(k : ℝ) := by
  have hu0 : 0 < u := by linarith
  have ha : 1 ≤ a := by rw [← hua]; exact one_le_pow₀ hu1
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl34 : |(l : ℝ)| ≤ a ^ (3 / 4 : ℝ) := by
    rw [← hua, pow_twelve_rpow hu0.le (k := 9) (by norm_num)]
    exact hlH.trans (pow_le_pow_right₀ hu1 (by norm_num))
  have hb := mixed_mode_bound ha hM hk hl34
  rw [block_mode_sum_eq]
  simp only [Int.cast_natCast]
  obtain ⟨hlo, hhi⟩ := curvature_bounds ha hM0 hM hk1 hua
  obtain ⟨h1, h2⟩ := sqrt_curvature_bounds hk1 hu1 hlo hhi
  set lam := (k : ℝ) * (3 / 2) / √(2 * (a + M) + 1)
  have hsk : 1 ≤ √(k : ℝ) := by rw [show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt hk1
  have hu39 : u ^ 3 ≤ u ^ 9 := pow_le_pow_right₀ hu1 (by norm_num)
  have hMu : (M : ℝ) ≤ u ^ 12 := hM.trans_eq hua.symm
  have hB1 : 14 * (M : ℝ) * √lam ≤ 28 * u ^ 9 * √(k : ℝ) := by
    calc 14 * (M : ℝ) * √lam ≤ 14 * u ^ 12 * (2 * √(k : ℝ) / u ^ 3) := by gcongr
      _ = 28 * u ^ 9 * √(k : ℝ) := by field_simp; ring
  have hB2 : 10 / √lam ≤ 20 * u ^ 9 * √(k : ℝ) := by
    rw [show 10 / √lam = 10 * (1 / √lam) by ring]
    have hq : 2 * u ^ 3 / √(k : ℝ) ≤ 2 * u ^ 9 * √(k : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      have hkk : √(k : ℝ) * √(k : ℝ) = k := mul_self_sqrt (by linarith)
      calc 2 * u ^ 3 ≤ 2 * u ^ 9 := by linarith
        _ ≤ 2 * u ^ 9 * (√(k : ℝ) * √(k : ℝ)) := by
          rw [hkk]
          have : 0 ≤ u ^ 9 := by positivity
          nlinarith
        _ = 2 * u ^ 9 * √(k : ℝ) * √(k : ℝ) := by ring
    linarith
  linarith

/-- Every nonzero-`k` mode of a block is at most `48 u^9 √|k|`. -/
theorem nonzero_mode_le {a u : ℝ} {M : ℕ} {k l : ℤ} (hu1 : 1 ≤ u) (hua : u ^ 12 = a)
    (hM : (M : ℝ) ≤ a) (hk : k ≠ 0) (hlH : |(l : ℝ)| ≤ u ^ 2) :
    ‖∑ n ∈ range M, BTCalculus.FejerBox.mode k l (torusPoint (a + n))‖ ≤
      48 * u ^ 9 * √|(k : ℝ)| := by
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, k = -(i : ℤ) := ⟨k.natAbs, by omega⟩
    have hi1 : 1 ≤ i := by omega
    have habs : |(k : ℝ)| = i := by
      rw [hi]; push_cast; rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    have h := pos_mode_le (l := -l) hu1 hua hM hi1 (by rw [Int.cast_neg, abs_neg]; exact hlH)
    have h2 := norm_block_mode_neg a M (i : ℤ) (-l)
    rw [neg_neg] at h2
    rw [habs, hi, h2]
    exact h
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, k = (i : ℤ) := ⟨k.natAbs, by omega⟩
    have hi1 : 1 ≤ i := by omega
    have habs : |(k : ℝ)| = i := by
      rw [hi]; push_cast; exact abs_of_nonneg (Nat.cast_nonneg _)
    rw [habs, hi]
    exact pos_mode_le hu1 hua hM hi1 hlH

/-- `#([-H, H] ∩ ℤ) = 2H + 1`. -/
theorem card_Icc_neg (H : ℕ) : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
  rw [Int.card_Icc]
  omega

/-- **The weighted mode sum of a block** at scale `a = u^{12}` with `1 ≤ H ≤ u^2`. -/
theorem block_boxModeSum_le {a u : ℝ} {M H : ℕ} (hu1 : 1 ≤ u) (hua : u ^ 12 = a)
    (hM : (M : ℝ) ≤ a) (hHu : (H : ℝ) ≤ u ^ 2) :
    boxModeSum (fun n => torusPoint (a + n)) M H ≤
      264 * u ^ 10 + 192 * u ^ 10 * (1 + 2 * (harmonic H : ℝ)) := by
  have hu0 : 0 < u := by linarith
  set W := 1 + 2 * (harmonic H : ℝ) with hW
  have hW0 : 0 ≤ W := by
    have : (0 : ℝ) ≤ harmonic H := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact sum_nonneg (fun _ _ => by positivity)
    linarith
  let G : ℤ → ℤ → ℝ := fun k l =>
    if k = 0 then 88 * u ^ 8 else 48 * u ^ 9 / √|(k : ℝ)| * frequencyWeight l
  have hterm : ∀ k ∈ Finset.Icc (-(H : ℤ)) H, ∀ l ∈ Finset.Icc (-(H : ℤ)) H,
      (if k = 0 ∧ l = 0 then 0 else
        frequencyWeight k * frequencyWeight l *
          ‖∑ n ∈ range M, BTCalculus.FejerBox.mode k l (torusPoint (a + n))‖) ≤ G k l := by
    intro k _ l hl
    have hlH : |(l : ℝ)| ≤ u ^ 2 := by
      have : |l| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hl)
      have : |(l : ℝ)| ≤ H := by rw [← Int.cast_abs]; exact_mod_cast this
      linarith
    have hwl0 := frequencyWeight_nonneg l
    have hwl1 : frequencyWeight l ≤ 1 := by
      unfold frequencyWeight
      split_ifs with h
      · exact le_rfl
      · rw [div_le_one (abs_pos.mpr (by exact_mod_cast h))]
        exact one_le_abs_intCast h
    by_cases hk : k = 0
    · subst hk
      simp only [G, if_true]
      by_cases hl0 : l = 0
      · simp [hl0]; positivity
      · simp only [hl0, and_false, if_false]
        have hz := zero_mode_le hu1 hua hM hl0 hlH
        have hw0 : frequencyWeight 0 = 1 := by simp [frequencyWeight]
        rw [hw0, one_mul]
        calc frequencyWeight l *
              ‖∑ n ∈ range M, BTCalculus.FejerBox.mode 0 l (torusPoint (a + n))‖
            ≤ 1 * (88 * u ^ 8) := mul_le_mul hwl1 hz (norm_nonneg _) (by norm_num)
          _ = 88 * u ^ 8 := one_mul _
    · simp only [G, hk, false_and, if_false]
      have hm := nonzero_mode_le hu1 hua hM hk hlH
      have hk1 := one_le_abs_intCast hk
      have hsk : 0 < √|(k : ℝ)| := sqrt_pos.mpr (by linarith)
      have hwk : frequencyWeight k = 1 / |(k : ℝ)| := by simp [frequencyWeight, hk]
      rw [hwk]
      have hsq : √|(k : ℝ)| * √|(k : ℝ)| = |(k : ℝ)| := mul_self_sqrt (by linarith)
      set sk := √|(k : ℝ)| with hsk_def
      have hks : |(k : ℝ)| = sk * sk := hsq.symm
      calc 1 / |(k : ℝ)| * frequencyWeight l *
            ‖∑ n ∈ range M, BTCalculus.FejerBox.mode k l (torusPoint (a + n))‖
          ≤ 1 / |(k : ℝ)| * frequencyWeight l * (48 * u ^ 9 * √|(k : ℝ)|) :=
            mul_le_mul_of_nonneg_left hm (by positivity)
        _ = 48 * u ^ 9 / sk * frequencyWeight l := by
            rw [hks]
            field_simp
            rw [sqrt_sq hsk.le]
            ring
  have hsum : boxModeSum (fun n => torusPoint (a + n)) M H ≤
      ∑ k ∈ Finset.Icc (-(H : ℤ)) H, ∑ l ∈ Finset.Icc (-(H : ℤ)) H, G k l :=
    sum_le_sum (fun k hk => sum_le_sum (fun l hl => hterm k hk l hl))
  have hrow : ∀ k : ℤ, k ≠ 0 →
      ∑ l ∈ Finset.Icc (-(H : ℤ)) H, G k l = 48 * u ^ 9 / √|(k : ℝ)| * W := by
    intro k hk
    simp only [G, hk, if_false]
    rw [← mul_sum, sum_frequencyWeight]
  have hzero : ∑ l ∈ Finset.Icc (-(H : ℤ)) H, G 0 l ≤ 264 * u ^ 10 := by
    simp only [G, if_true, sum_const, card_Icc_neg, nsmul_eq_mul]
    push_cast
    have h1 : (1 : ℝ) ≤ u ^ 2 := one_le_pow₀ hu1
    have : (2 * (H : ℝ) + 1) ≤ 3 * u ^ 2 := by linarith
    calc (2 * (H : ℝ) + 1) * (88 * u ^ 8) ≤ 3 * u ^ 2 * (88 * u ^ 8) := by gcongr
      _ = 264 * u ^ 10 := by ring
  rw [BTCalculus.ErdosTuran.sum_Icc_neg_eq (fun k => ∑ l ∈ Finset.Icc (-(H : ℤ)) H, G k l)] at hsum
  have hpairs : ∑ h ∈ Finset.Icc 1 H,
      (∑ l ∈ Finset.Icc (-(H : ℤ)) H, G (h : ℤ) l +
        ∑ l ∈ Finset.Icc (-(H : ℤ)) H, G (-(h : ℤ)) l) =
      96 * u ^ 9 * W * ∑ h ∈ Finset.Icc 1 H, 1 / √(h : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro h hh
    have h1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
    have hz : (h : ℤ) ≠ 0 := by omega
    rw [hrow _ hz, hrow _ (neg_ne_zero.mpr hz)]
    simp only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast]
    ring
  have hsqrt : ∑ h ∈ Finset.Icc 1 H, 1 / √(h : ℝ) ≤ 2 * u := by
    have hsH : √(H : ℝ) ≤ u := by
      rw [show u = √(u ^ 2) by rw [sqrt_sq hu0.le]]
      exact sqrt_le_sqrt hHu
    linarith [sum_one_div_sqrt_le H]
  rw [hpairs] at hsum
  have hfin : 96 * u ^ 9 * W * ∑ h ∈ Finset.Icc 1 H, 1 / √(h : ℝ) ≤ 192 * u ^ 10 * W := by
    calc 96 * u ^ 9 * W * ∑ h ∈ Finset.Icc 1 H, 1 / √(h : ℝ) ≤ 96 * u ^ 9 * W * (2 * u) := by
          gcongr
      _ = 192 * u ^ 10 * W := by ring
  linarith

end Block

/-- **One block.** For `1 ≤ a` and `M ≤ a`, every box `[0, 1/2) × [c, d)` has discrepancy at most
`1712 a^{5/6} (1 + log a)` on the block `[a, a+M)` of odd-start parameters. -/
theorem abs_block_boxError_le (a M : ℕ) (ha : 1 ≤ a) (hM : M ≤ a) {c d : ℝ} (hcd : c ≤ d)
    (hd : d ≤ c + 1) :
    |boxError (fun n => torusPoint ((a : ℝ) + n)) M 0 (1 / 2) c d| ≤
      1712 * (a : ℝ) ^ (5 / 6 : ℝ) * (1 + log a) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hMa : (M : ℝ) ≤ a := by exact_mod_cast hM
  set u : ℝ := (a : ℝ) ^ (1 / 12 : ℝ) with hudef
  have hu0 : 0 ≤ u := by positivity
  have hu1 : 1 ≤ u := one_le_rpow ha1 (by norm_num)
  have hpow (k : ℕ) : u ^ k = (a : ℝ) ^ ((k : ℝ) / 12) := by
    rw [hudef, ← rpow_natCast, ← rpow_mul (by linarith)]
    congr 1
    ring
  have hua : u ^ 12 = a := by rw [hpow]; norm_num
  have h56 : (a : ℝ) ^ (5 / 6 : ℝ) = u ^ 10 := by rw [hpow]; norm_num
  rw [h56]
  have hlog : log u = log a / 12 := by
    rw [hudef, log_rpow (by linarith)]
    ring
  have hloga : 0 ≤ log (a : ℝ) := log_nonneg ha1
  have hu10 : 0 ≤ u ^ 10 := by positivity
  have hp : 0 ≤ u ^ 10 * log (a : ℝ) := mul_nonneg hu10 hloga
  set H := ⌊u ^ 2⌋₊ with hHdef
  have hHle : (H : ℝ) ≤ u ^ 2 := Nat.floor_le (by positivity)
  have hHlt : u ^ 2 < H + 1 := Nat.lt_floor_add_one _
  by_cases hH : 7 ≤ H
  · have het := abs_boxError_le_modeSum (fun n => torusPoint ((a : ℝ) + n)) M hH
      (a := 0) (b := 1 / 2) (by norm_num) (by norm_num) hcd hd
    have hms := block_boxModeSum_le hu1 hua hMa hHle
    have hharm : (harmonic H : ℝ) ≤ 1 + log H := harmonic_le_one_add_log H
    have hH0 : (0 : ℝ) < H := by
      have : (7 : ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have hlogH : log (H : ℝ) ≤ 2 * log u := by
      have := log_le_log hH0 hHle
      rw [log_pow] at this
      push_cast at this
      linarith
    have hmain : 32 * (M : ℝ) / ((H : ℝ) + 1) ≤ 32 * u ^ 10 := by
      rw [div_le_iff₀ (by positivity)]
      have : (M : ℝ) ≤ u ^ 10 * u ^ 2 := by
        rw [show u ^ 10 * u ^ 2 = u ^ 12 by ring]
        linarith
      nlinarith
    have hW : 1 + 2 * (harmonic H : ℝ) ≤ 3 + log a / 3 := by
      rw [hlog] at hlogH
      linarith
    have hW' := mul_le_mul_of_nonneg_left hW (show 0 ≤ 192 * u ^ 10 by positivity)
    nlinarith
  · have hH7 : (H : ℝ) ≤ 6 := by exact_mod_cast (show H ≤ 6 by omega)
    have hu2 : u ^ 2 ≤ 7 := by linarith
    have hE := abs_boxError_le (fun n => torusPoint ((a : ℝ) + n)) M (a := 0) (b := 1 / 2)
      (by norm_num) (by norm_num) hcd hd
    calc _ ≤ (M : ℝ) := hE
      _ ≤ u ^ 12 := hMa.trans_eq hua.symm
      _ = u ^ 2 * u ^ 10 := by ring
      _ ≤ 7 * u ^ 10 := mul_le_mul_of_nonneg_right hu2 hu10
      _ ≤ 1712 * u ^ 10 * (1 + log a) := by nlinarith

/-! ## All odd starts below a bound -/

/-- Splitting the samples `[0, a+M)` at `a` splits the box discrepancy. -/
theorem boxError_add (z : ℕ → UnitAddCircle × UnitAddCircle) (a M : ℕ) (p q c d : ℝ) :
    boxError z (a + M) p q c d =
      boxError z a p q c d + boxError (fun n => z (a + n)) M p q c d := by
  simp only [boxError, boxCount, sum_range_add]
  push_cast
  ring

/-- **All odd starts below `2R`.** Every box `[0, 1/2) × [c, d)` has discrepancy at most
`6848 R^{5/6} (1 + log R)` for the torus points of `r < R`. -/
theorem abs_oe_boxError_le (R : ℕ) {c d : ℝ} (hcd : c ≤ d) (hd : d ≤ c + 1) :
    |boxError (fun r : ℕ => torusPoint (r : ℝ)) R 0 (1 / 2) c d| ≤
      6848 * (R : ℝ) ^ (5 / 6 : ℝ) * (1 + log R) := by
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    rcases Nat.lt_or_ge R 2 with hR | hR
    · interval_cases R
      · simp [boxError, boxCount]
      · have hE := abs_boxError_le (fun r : ℕ => torusPoint (r : ℝ)) 1 (a := 0) (b := 1 / 2)
          (by norm_num) (by norm_num) hcd hd
        simp only [Nat.cast_one, one_rpow, log_one, add_zero, mul_one] at hE ⊢
        linarith
    · set a := (R + 1) / 2 with hadef
      set M := R / 2 with hMdef
      have hsplit : a + M = R := by omega
      have ha : 1 ≤ a := by omega
      have hMa : M ≤ a := by omega
      have haR : a < R := by omega
      have h1 := ih a haR
      have h2 := abs_block_boxError_le a M ha hMa hcd hd
      have hshift : (fun n => (fun r : ℕ => torusPoint (r : ℝ)) (a + n)) =
          fun n : ℕ => torusPoint ((a : ℝ) + n) := by
        funext n
        push_cast
        rfl
      rw [← hsplit, boxError_add, hshift, hsplit]
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
      have haR' : (a : ℝ) ≤ R := by exact_mod_cast haR.le
      have hscale : (a : ℝ) ^ (5 / 6 : ℝ) ≤ 4 / 5 * (R : ℝ) ^ (5 / 6 : ℝ) := by
        have hle : (a : ℝ) ≤ 3 / 4 * R := by
          have : 4 * a ≤ 3 * R := by omega
          have : (4 * a : ℝ) ≤ 3 * R := by exact_mod_cast this
          linarith
        calc (a : ℝ) ^ (5 / 6 : ℝ) ≤ (3 / 4 * (R : ℝ)) ^ (5 / 6 : ℝ) :=
              rpow_le_rpow (Nat.cast_nonneg _) hle (by norm_num)
          _ = (3 / 4 : ℝ) ^ (5 / 6 : ℝ) * (R : ℝ) ^ (5 / 6 : ℝ) :=
              mul_rpow (by norm_num) (Nat.cast_nonneg _)
          _ ≤ 4 / 5 * (R : ℝ) ^ (5 / 6 : ℝ) :=
              mul_le_mul_of_nonneg_right three_quarters_rpow_le (by positivity)
      have hloga : 0 ≤ log (a : ℝ) := log_nonneg ha1
      have hlogaR : log (a : ℝ) ≤ log R := log_le_log (by linarith) haR'
      have hav : (a : ℝ) ^ (5 / 6 : ℝ) * (1 + log a) ≤
          4 / 5 * ((R : ℝ) ^ (5 / 6 : ℝ) * (1 + log R)) := by
        have := mul_le_mul hscale (show 1 + log (a : ℝ) ≤ 1 + log R by linarith)
          (by linarith) (by positivity)
        linarith
      calc _ ≤ |boxError (fun r : ℕ => torusPoint (r : ℝ)) a 0 (1 / 2) c d| +
            |boxError (fun n : ℕ => torusPoint ((a : ℝ) + n)) M 0 (1 / 2) c d| := abs_add_le _ _
        _ ≤ 6848 * (a : ℝ) ^ (5 / 6 : ℝ) * (1 + log a) +
            1712 * (a : ℝ) ^ (5 / 6 : ℝ) * (1 + log a) := add_le_add h1 h2
        _ ≤ 6848 * (R : ℝ) ^ (5 / 6 : ℝ) * (1 + log R) := by nlinarith

/-! ## The printed counts -/

/-- The starts `n ≤ N` whose first three letters are `w`. -/
def word3Count (N : ℕ) (w : List Branch) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => itinerary n 3 = w)).card

/-- A word beginning with `O` is counted on the odd starts `2r+1`, `r < ⌈N/2⌉`. -/
theorem word3Count_eq_card {N : ℕ} {w : List Branch} (hw : ∃ v, w = .odd :: v) :
    word3Count N w =
      ((range ((N + 1) / 2)).filter (fun r => itinerary (2 * r + 1) 3 = w)).card := by
  obtain ⟨v, rfl⟩ := hw
  unfold word3Count
  symm
  refine card_bij (fun r _ => 2 * r + 1) ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_range, Finset.mem_Icc] at hr ⊢
    exact ⟨⟨by omega, by omega⟩, hr.2⟩
  · intro r _ s _ h
    omega
  · intro n hn
    simp only [mem_filter, Finset.mem_Icc] at hn
    have hodd := word3_head_odd hn.2
    refine ⟨n / 2, ?_, by omega⟩
    have hn' : 2 * (n / 2) + 1 = n := by omega
    simp only [mem_filter, mem_range]
    exact ⟨by omega, by rw [hn']; exact hn.2⟩

/-- A box count over `r < R` is the number of `r` whose torus point lies in the box. -/
theorem boxCount_eq_card (R : ℕ) (A B : Set UnitAddCircle) :
    boxCount (fun r : ℕ => torusPoint (r : ℝ)) R A B =
      (((range R).filter (fun r : ℕ => (torusPoint (r : ℝ)).1 ∈ A ∧
        (torusPoint (r : ℝ)).2 ∈ B)).card : ℝ) := by
  rw [boxCount, sum_boole]

/-- The general count bound for a word whose box is `[0, 1/2) × [c, c + 1/2)`. -/
theorem abs_word3Count_sub_le {N : ℕ} (hN : 1 ≤ N) {w : List Branch} {c : ℝ}
    (hbox : ∀ r : ℕ, ((torusPoint r).1 ∈ arc 0 (1 / 2) ∧ (torusPoint r).2 ∈ arc c (c + 1 / 2)) ↔
      itinerary (2 * r + 1) 3 = w)
    (hw : ∃ v, w = .odd :: v) :
    |(word3Count N w : ℝ) - N / 8| ≤ 6849 * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + log N) := by
  set R := (N + 1) / 2 with hRdef
  have hRN : R ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcount : (word3Count N w : ℝ) = boxCount (fun r : ℕ => torusPoint (r : ℝ)) R
      (arc 0 (1 / 2)) (arc c (c + 1 / 2)) := by
    rw [boxCount_eq_card, word3Count_eq_card hw, filter_congr (fun r _ => hbox r)]
  have hE := abs_oe_boxError_le R (c := c) (d := c + 1 / 2) (by linarith) (by linarith)
  have hmono : 6848 * (R : ℝ) ^ (5 / 6 : ℝ) * (1 + log R) ≤
      6848 * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + log N) := by
    rcases Nat.eq_zero_or_pos R with hR0 | hRpos
    · have : (R : ℝ) = 0 := by exact_mod_cast hR0
      rw [this, zero_rpow (by norm_num), mul_zero, zero_mul]
      have hl : 0 ≤ log (N : ℝ) := log_nonneg hN1
      exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (by linarith)
    · have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hRpos
      have hRN' : (R : ℝ) ≤ N := by exact_mod_cast hRN
      have hp : (R : ℝ) ^ (5 / 6 : ℝ) ≤ (N : ℝ) ^ (5 / 6 : ℝ) :=
        rpow_le_rpow (by linarith) hRN' (by norm_num)
      have hl : log (R : ℝ) ≤ log N := log_le_log (by linarith) hRN'
      have hl0 : 0 ≤ log (R : ℝ) := log_nonneg hR1
      have := mul_le_mul hp (show 1 + log (R : ℝ) ≤ 1 + log N by linarith) (by linarith)
        (by positivity)
      nlinarith
  have hhalf : |(R : ℝ) / 4 - N / 8| ≤ 1 / 8 := by
    have h1 : 2 * R ≤ N + 1 := by omega
    have h2 : N ≤ 2 * R := by omega
    have h1' : (2 * R : ℝ) ≤ N + 1 := by exact_mod_cast h1
    have h2' : (N : ℝ) ≤ 2 * R := by exact_mod_cast h2
    rw [abs_le]
    constructor <;> linarith
  have hone : 1 / 8 ≤ (N : ℝ) ^ (5 / 6 : ℝ) * (1 + log N) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (5 / 6 : ℝ) := one_le_rpow hN1 (by norm_num)
    have h2 : (1 : ℝ) ≤ 1 + log N := by linarith [log_nonneg hN1]
    nlinarith
  rw [hcount]
  have harea : (R : ℝ) * ((1 / 2 - 0) * (c + 1 / 2 - c)) = R / 4 := by ring
  rw [boxError, harea] at hE
  calc |boxCount (fun r : ℕ => torusPoint (r : ℝ)) R (arc 0 (1 / 2)) (arc c (c + 1 / 2)) -
        N / 8|
      = |(boxCount (fun r : ℕ => torusPoint (r : ℝ)) R (arc 0 (1 / 2)) (arc c (c + 1 / 2)) -
          R / 4) + ((R : ℝ) / 4 - N / 8)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 6849 * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + log N) := by linarith

/-- **Paper B, Proposition 3.2, `OEE`.** For `N ≥ 1`,
`|#{n ≤ N : word_3(n) = OEE} - N/8| ≤ 6849 N^{5/6} (1 + log N)`. -/
theorem abs_oeeCount_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |(word3Count N [.odd, .even, .even] : ℝ) - N / 8| ≤
      6849 * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + log N) :=
  abs_word3Count_sub_le hN (c := 0)
    (fun r => by simpa using torusPoint_mem_oee_iff r) ⟨_, rfl⟩

/-- **Paper B, Proposition 3.2, `OEO`.** For `N ≥ 1`,
`|#{n ≤ N : word_3(n) = OEO} - N/8| ≤ 6849 N^{5/6} (1 + log N)`. -/
theorem abs_oeoCount_sub_le (N : ℕ) (hN : 1 ≤ N) :
    |(word3Count N [.odd, .even, .odd] : ℝ) - N / 8| ≤
      6849 * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + log N) :=
  abs_word3Count_sub_le hN (c := 1 / 2)
    (fun r => by
      rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
      exact torusPoint_mem_oeo_iff r) ⟨_, rfl⟩

end PaperBOEThirdLetter

end Problems.Juggler
