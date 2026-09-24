import Problems.Juggler.FateDepthFiveAssembly
import Problems.Juggler.OOEEFibreGeometry

/-! # Exact depth-five target fibres and their source scale

For the words `OOOEE` and `OOEOE` the fifth iterate along the word is a nested
floor formula in `n`. Each target `t` has an exact source interval
`[endpoint t, endpoint (t+1))`, built from the ceilings `inverse a = ⌈a^(2/3)⌉`.
The source scale is `base t = t^(32/27)`, the window scale is
`scale t = t^(5/27)`, and there are about `(16/27) scale t` odd candidates.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Problems.Juggler.DepthFiveFibreGeometry

open Finset OddPredecessorTransport FateOOEEAssembly OOEEFibreGeometry
open FateOOOEEAssembly (OOOEEGuard)
open FateDepthFiveAssembly (OOEOEGuard)

/-- The source scale `t^(32/27)` of a depth-five target. -/
def base (t : ℕ) : ℝ := (t:ℝ)^(32/27:ℝ)

/-- The window scale `t^(5/27)`. -/
def scale (t : ℕ) : ℝ := (t:ℝ)^(5/27:ℝ)

/-- Least source reaching at least `t` along `OOOEE`. -/
def endpointA (t : ℕ) : ℕ := inverse (inverse (inverse (t^4)))

/-- Least source reaching at least `t` along `OOEOE`. -/
def endpointB (t : ℕ) : ℕ := inverse (inverse ((inverse (t^2))^2))

/-- The formula for `J^5` along `OOOEE`. -/
def formulaA (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (oddMap (oddMap (oddMap n))))

/-- The formula for `J^5` along `OOEOE`. -/
def formulaB (n : ℕ) : ℕ := Nat.sqrt (oddMap (Nat.sqrt (oddMap (oddMap n))))

/-- Exact threshold: `endpointA t ≤ n` iff `OOOEE`'s formula reaches `t`. -/
theorem endpointA_le (t n : ℕ) : endpointA t ≤ n ↔ t ≤ formulaA n := by
  rw [endpointA, inverse_le, inverse_le, inverse_le, formulaA, Nat.le_sqrt, Nat.le_sqrt]
  constructor <;> intro h <;> nlinarith [h]

/-- Exact threshold: `endpointB t ≤ n` iff `OOEOE`'s formula reaches `t`. -/
theorem endpointB_le (t n : ℕ) : endpointB t ≤ n ↔ t ≤ formulaB n := by
  unfold endpointB formulaB
  simp only [pow_two]
  rw [Nat.le_sqrt, ← inverse_le, Nat.le_sqrt, ← inverse_le, ← inverse_le]

/-- The `OOOEE` endpoint is monotone in the target. -/
theorem endpointA_monotone : Monotone endpointA := by
  intro a b hab
  exact inverse_monotone (inverse_monotone (inverse_monotone (Nat.pow_le_pow_left hab 4)))

/-- The `OOEOE` endpoint is monotone in the target. -/
theorem endpointB_monotone : Monotone endpointB := by
  intro a b hab
  exact inverse_monotone (inverse_monotone
    (Nat.pow_le_pow_left (inverse_monotone (Nat.pow_le_pow_left hab 2)) 2))

/-- The `OOOEE` formula equals `t` exactly on `[endpointA t, endpointA (t+1))`. -/
theorem formulaA_cell (t n : ℕ) : formulaA n = t ↔ endpointA t ≤ n ∧ n < endpointA (t+1) := by
  have h1 := endpointA_le t n
  have h2 := endpointA_le (t+1) n
  omega

/-- The `OOEOE` formula equals `t` exactly on `[endpointB t, endpointB (t+1))`. -/
theorem formulaB_cell (t n : ℕ) : formulaB n = t ↔ endpointB t ≤ n ∧ n < endpointB (t+1) := by
  have h1 := endpointB_le t n
  have h2 := endpointB_le (t+1) n
  omega

/-- Along `OOOEE` the fifth iterate is `formulaA`. -/
theorem actual_five_steps_A {n : ℕ} (hn : OOOEEGuard n) : floorPower^[5] n = formulaA n := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hn
  have ho1 : oddMap n % 2 = 1 := by simpa only [oddMap_eq_step h0] using h1
  have ho2 : oddMap (oddMap n) % 2 = 1 := by
    simpa only [oddMap_eq_step h0, oddMap_eq_step h1] using h2
  have he3 : oddMap (oddMap (oddMap n)) % 2 = 0 := by
    simpa only [oddMap_eq_step h0, oddMap_eq_step h1, oddMap_eq_step h2] using h3
  have he4 : Nat.sqrt (oddMap (oddMap (oddMap n))) % 2 = 0 := by
    simpa only [oddMap_eq_step h0, oddMap_eq_step h1, oddMap_eq_step h2,
      floorPower_even_eq h3] using h4
  change floorPower (floorPower (floorPower (floorPower (floorPower n)))) = _
  rw [← oddMap_eq_step h0, ← oddMap_eq_step ho1, ← oddMap_eq_step ho2,
    floorPower_even_eq he3, floorPower_even_eq he4, formulaA]

/-- Along `OOEOE` the fifth iterate is `formulaB`. -/
theorem actual_five_steps_B {n : ℕ} (hn : OOEOEGuard n) : floorPower^[5] n = formulaB n := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hn
  have ho1 : oddMap n % 2 = 1 := by simpa only [oddMap_eq_step h0] using h1
  have he2 : oddMap (oddMap n) % 2 = 0 := by
    simpa only [oddMap_eq_step h0, oddMap_eq_step h1] using h2
  have ho3 : Nat.sqrt (oddMap (oddMap n)) % 2 = 1 := by
    simpa only [oddMap_eq_step h0, oddMap_eq_step h1, floorPower_even_eq h2] using h3
  have h3' : Nat.sqrt (floorPower (floorPower n)) % 2 = 1 := by
    simpa only [floorPower_even_eq h2] using h3
  have he4 : oddMap (Nat.sqrt (oddMap (oddMap n))) % 2 = 0 := by
    simpa only [oddMap_eq_step h0, oddMap_eq_step h1, floorPower_even_eq h2,
      oddMap_eq_step h3'] using h4
  change floorPower (floorPower (floorPower (floorPower (floorPower n)))) = _
  rw [← oddMap_eq_step h0, ← oddMap_eq_step ho1, floorPower_even_eq he2,
    ← oddMap_eq_step ho3, floorPower_even_eq he4, formulaB]

/-! ### Real bounds on the endpoints -/

/-- The ceiling `inverse a` lies in `[a^(2/3), a^(2/3) + 1]`. -/
theorem inverse_bounds (a : ℕ) :
    (a:ℝ)^(2/3:ℝ) ≤ inverse a ∧ (inverse a:ℝ) ≤ (a:ℝ)^(2/3:ℝ) + 1 :=
  ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le⟩

/-- One `2/3` power absorbs an additive error: `(y+e)^(2/3) ≤ y^(2/3) + e` for `y ≥ 1`. -/
theorem rpow_two_thirds_add {y e : ℝ} (hy : 1 ≤ y) (he : 0 ≤ e) :
    (y + e)^(2/3:ℝ) ≤ y^(2/3:ℝ) + e := by
  have hb := Numerics.bernoulli_le (a := y) (h := e) (p := 2/3) (q := -1/3)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hi : y^(-1/3:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num)
  have hi0 : 0 ≤ y^(-1/3:ℝ) := Real.rpow_nonneg (by linarith) _
  nlinarith

/-- The `2/3` power is monotone on the nonnegative reals. -/
theorem rpow_mono_two_thirds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a^(2/3:ℝ) ≤ b^(2/3:ℝ) := Real.rpow_le_rpow ha hab (by norm_num)

/-- A `2/3` power of a number at least `1` is at least `1`. -/
theorem one_le_two_thirds {a : ℝ} (ha : 1 ≤ a) : 1 ≤ a^(2/3:ℝ) :=
  Real.one_le_rpow ha (by norm_num)

/-- The `OOOEE` endpoint lies within `3` above `t^(32/27)`. -/
theorem endpointA_bounds {t : ℕ} (ht : 1 ≤ t) :
    base t ≤ endpointA t ∧ (endpointA t:ℝ) ≤ base t + 3 := by
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  set y0 : ℝ := ((t^4:ℕ):ℝ) with hy0
  have hy01 : 1 ≤ y0 := by rw [hy0]; exact_mod_cast Nat.one_le_pow _ _ ht
  set b1 := y0^(2/3:ℝ)
  set b2 := b1^(2/3:ℝ)
  set b3 := b2^(2/3:ℝ)
  have hb1 : 1 ≤ b1 := one_le_two_thirds hy01
  have hb2 : 1 ≤ b2 := one_le_two_thirds hb1
  have hb3 : b3 = base t := by
    simp only [b3, b2, b1, hy0, base]
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
    norm_num
  obtain ⟨l1, u1⟩ := inverse_bounds (t^4)
  obtain ⟨l2, u2⟩ := inverse_bounds (inverse (t^4))
  obtain ⟨l3, u3⟩ := inverse_bounds (inverse (inverse (t^4)))
  have i1l : b1 ≤ (inverse (t^4):ℝ) := l1
  have i1u : (inverse (t^4):ℝ) ≤ b1 + 1 := u1
  have i2l : b2 ≤ (inverse (inverse (t^4)):ℝ) :=
    (rpow_mono_two_thirds (by linarith) i1l).trans l2
  have i2u : (inverse (inverse (t^4)):ℝ) ≤ b2 + 2 := by
    have := (rpow_mono_two_thirds (by positivity) i1u).trans
      (rpow_two_thirds_add hb1 (by norm_num))
    linarith
  have i3l : b3 ≤ (endpointA t:ℝ) :=
    (rpow_mono_two_thirds (by linarith) i2l).trans l3
  have i3u : (endpointA t:ℝ) ≤ b3 + 3 := by
    have := (rpow_mono_two_thirds (by positivity) i2u).trans
      (rpow_two_thirds_add hb2 (by norm_num))
    change (inverse (inverse (inverse (t^4))):ℝ) ≤ _
    linarith
  rw [hb3] at i3l i3u
  exact ⟨i3l, i3u⟩

/-- The `OOEOE` endpoint lies within `4` above `t^(32/27)`. -/
theorem endpointB_bounds {t : ℕ} (ht : 1 ≤ t) :
    base t ≤ endpointB t ∧ (endpointB t:ℝ) ≤ base t + 4 := by
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  set c1 := (((t^2:ℕ)):ℝ)^(2/3:ℝ) with hc1d
  have hc1 : 1 ≤ c1 := one_le_two_thirds (by exact_mod_cast Nat.one_le_pow _ _ ht)
  have hc10 : 0 ≤ c1 := by linarith
  set c2 := (c1^2)^(2/3:ℝ) with hc2d
  have hc2 : 1 ≤ c2 := one_le_two_thirds (by nlinarith)
  set c3 := c2^(2/3:ℝ) with hc3d
  have hc3 : c3 = base t := by
    simp only [c3, c2, c1, base]
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity)]
    norm_num
  -- c1^2's inverse carries an error of order c1; two more 2/3 powers absorb it.
  have hc2eq : c2 = c1^(4/3:ℝ) := by
    rw [hc2d, ← Real.rpow_natCast, ← Real.rpow_mul hc10]; norm_num
  obtain ⟨l1, u1⟩ := inverse_bounds (t^2)
  have i1l : c1 ≤ (inverse (t^2):ℝ) := l1
  have i1u : (inverse (t^2):ℝ) ≤ c1 + 1 := u1
  set v := (inverse (t^2))^2
  have vl : c1^2 ≤ (v:ℝ) := by push_cast [v]; nlinarith
  have vu : (v:ℝ) ≤ c1^2 + (2*c1 + 1) := by push_cast [v]; nlinarith
  obtain ⟨l2, u2⟩ := inverse_bounds v
  -- (c1^2 + e)^(2/3) ≤ c1^(4/3) + (2/3) c1^(-2/3) e, with c1^(-2/3) (2 c1 + 1) ≤ 3 c1^(1/3)
  have hb := Numerics.bernoulli_le (a := c1^2) (h := 2*c1+1) (p := 2/3) (q := -1/3)
    (by positivity) (by nlinarith) (by norm_num) (by norm_num) (by norm_num)
  have hneg : (c1^2)^(-1/3:ℝ) = c1^(-2/3:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc10]; norm_num
  have hprod : c1^(-2/3:ℝ) * c1 = c1^(1/3:ℝ) := by
    rw [show c1^(-2/3:ℝ) * c1 = c1^(-2/3:ℝ) * c1^(1:ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add (by linarith)]
    norm_num
  have hsmall : c1^(-2/3:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hsm0 : 0 ≤ c1^(-2/3:ℝ) := Real.rpow_nonneg hc10 _
  have hthird : 1 ≤ c1^(1/3:ℝ) := Real.one_le_rpow hc1 (by norm_num)
  have i2l : c2 ≤ (inverse v:ℝ) := (rpow_mono_two_thirds (by positivity) vl).trans l2
  have i2u : (inverse v:ℝ) ≤ c2 + 2*c1^(1/3:ℝ) + 2 := by
    have hv := (rpow_mono_two_thirds (by positivity) vu).trans hb
    rw [hneg] at hv
    have : (2/3:ℝ) * c1^(-2/3:ℝ) * (2*c1 + 1) ≤ 2*c1^(1/3:ℝ) + 1 := by
      have e1 : (2/3:ℝ) * c1^(-2/3:ℝ) * (2*c1 + 1)
          = (4/3) * (c1^(-2/3:ℝ) * c1) + (2/3) * c1^(-2/3:ℝ) := by ring
      rw [e1, hprod]; nlinarith
    have hc2' : (c1^2)^(2/3:ℝ) = c2 := rfl
    rw [hc2'] at hv
    linarith
  -- third inverse: (c2 + E)^(2/3) ≤ c3 + (2/3) c2^(-1/3) E with c2^(-1/3) c1^(1/3) ≤ 1
  obtain ⟨l3, u3⟩ := inverse_bounds (inverse v)
  have hb3 := Numerics.bernoulli_le (a := c2) (h := 2*c1^(1/3:ℝ) + 2) (p := 2/3) (q := -1/3)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hc2neg : c2^(-1/3:ℝ) * c1^(1/3:ℝ) ≤ 1 := by
    rw [hc2eq, ← Real.rpow_mul hc10, ← Real.rpow_add (by linarith)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hc2n1 : c2^(-1/3:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc2 (by norm_num)
  have hc2n0 : 0 ≤ c2^(-1/3:ℝ) := Real.rpow_nonneg (by linarith) _
  have i3l : c3 ≤ (endpointB t:ℝ) := (rpow_mono_two_thirds (by linarith) i2l).trans l3
  have i3u : (endpointB t:ℝ) ≤ c3 + 4 := by
    have hv1 := rpow_mono_two_thirds (by positivity) i2u
    have hb3' : (c2 + 2*c1^(1/3:ℝ) + 2)^(2/3:ℝ)
        ≤ c2^(2/3:ℝ) + 2/3 * c2^(-1/3:ℝ) * (2*c1^(1/3:ℝ) + 2) := by
      have e : c2 + 2*c1^(1/3:ℝ) + 2 = c2 + (2*c1^(1/3:ℝ) + 2) := by ring
      rw [e]; exact hb3
    have hsplit : 2/3 * c2^(-1/3:ℝ) * (2*c1^(1/3:ℝ) + 2)
        = 4/3 * (c2^(-1/3:ℝ) * c1^(1/3:ℝ)) + 4/3 * c2^(-1/3:ℝ) := by ring
    have hsm : 2/3 * c2^(-1/3:ℝ) * (2*c1^(1/3:ℝ) + 2) ≤ 8/3 := by
      rw [hsplit]; linarith
    change (inverse (inverse v):ℝ) ≤ _
    linarith
  rw [hc3] at i3l i3u
  exact ⟨i3l, i3u⟩

/-! ### Candidates, fibres and the source window, for any monotone endpoint -/

/-- First odd integer at or above `E t`. -/
def firstOdd (E : ℕ → ℕ) (t : ℕ) : ℕ := 2*(E t/2)+1

/-- Number of odd integers in `[E t, E (t+1))`. -/
def candidateCount (E : ℕ → ℕ) (t : ℕ) : ℕ := E (t+1)/2 - E t/2

/-- The `j`-th odd candidate of target `t`. -/
def sample (E : ℕ → ℕ) (t j : ℕ) : ℕ := firstOdd E t + 2*j

/-- The odd integers in `[E t, E (t+1))`. -/
def candidates (E : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (range (candidateCount E t)).image (sample E t)

/-- Distinct indices give distinct odd candidates. -/
theorem sample_injective (E : ℕ → ℕ) (t : ℕ) : Function.Injective (sample E t) := by
  intro a b hab
  dsimp [sample] at hab
  omega

/-- The candidates are exactly the odd integers in `[E t, E (t+1))`. -/
theorem mem_candidates {E : ℕ → ℕ} (hE : Monotone E) {t n : ℕ} :
    n ∈ candidates E t ↔ n % 2 = 1 ∧ E t ≤ n ∧ n < E (t+1) := by
  have hL := hE (Nat.le_succ t)
  have hdiv : E t/2 ≤ E (t+1)/2 := Nat.div_le_div_right hL
  simp only [candidates, mem_image, mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    dsimp [sample, firstOdd, candidateCount] at *
    omega
  · rintro ⟨hn, hl, hu⟩
    refine ⟨n/2 - E t/2, ?_, ?_⟩ <;> dsimp [sample, firstOdd, candidateCount] <;> omega

/-- The candidate set has exactly `candidateCount E t` elements. -/
theorem candidate_card (E : ℕ → ℕ) (t : ℕ) : (candidates E t).card = candidateCount E t := by
  rw [candidates, Finset.card_image_of_injective _ (sample_injective E t), card_range]

/-- The actual `OOOEE` fibre of target `t`. -/
def fibreA (t : ℕ) : Finset ℕ := (candidates endpointA t).filter OOOEEGuard

/-- The actual `OOEOE` fibre of target `t`. -/
def fibreB (t : ℕ) : Finset ℕ := (candidates endpointB t).filter OOEOEGuard

/-- The finite set is exactly the actual `OOOEE` fibre of `t`. -/
theorem mem_fibreA {t n : ℕ} : n ∈ fibreA t ↔ OOOEEGuard n ∧ floorPower^[5] n = t := by
  rw [fibreA, mem_filter, mem_candidates endpointA_monotone]
  constructor
  · rintro ⟨⟨_, hl, hu⟩, hg⟩
    exact ⟨hg, (actual_five_steps_A hg).trans ((formulaA_cell t n).mpr ⟨hl, hu⟩)⟩
  · rintro ⟨hg, ht⟩
    exact ⟨⟨hg.1, (formulaA_cell t n).mp ((actual_five_steps_A hg).symm.trans ht)⟩, hg⟩

/-- The finite set is exactly the actual `OOEOE` fibre of `t`. -/
theorem mem_fibreB {t n : ℕ} : n ∈ fibreB t ↔ OOEOEGuard n ∧ floorPower^[5] n = t := by
  rw [fibreB, mem_filter, mem_candidates endpointB_monotone]
  constructor
  · rintro ⟨⟨_, hl, hu⟩, hg⟩
    exact ⟨hg, (actual_five_steps_B hg).trans ((formulaB_cell t n).mpr ⟨hl, hu⟩)⟩
  · rintro ⟨hg, ht⟩
    exact ⟨⟨hg.1, (formulaB_cell t n).mp ((actual_five_steps_B hg).symm.trans ht)⟩, hg⟩

/-- The source scale is `t` times the window scale. -/
theorem base_eq_mul_scale (t : ℕ) : base t = (t:ℝ) * scale t := by
  by_cases ht : t = 0
  · simp [ht, base, scale]
  · have h0 : (0:ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
    dsimp [base, scale]
    rw [show (32/27:ℝ) = 1 + 5/27 by norm_num, Real.rpow_add h0, Real.rpow_one]

/-- `(32/27) scale t ≤ base (t+1) - base t ≤ (32/27) scale t + 2`. -/
theorem power_increment {t : ℕ} (ht : 1 ≤ t) :
    (32/27) * scale t ≤ base (t+1) - base t ∧ base (t+1) - base t ≤ (32/27) * scale t + 2 := by
  have h0 : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have h1 : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hl := Numerics.bernoulli_ge (a := (t:ℝ)) (h := 1) (p := 32/27) (q := 5/27)
    h0 (by linarith) (by norm_num) (by norm_num)
  have hu := Numerics.bernoulli_ge (a := (t:ℝ)+1) (h := -1) (p := 32/27) (q := 5/27)
    (by positivity) (by linarith) (by norm_num) (by norm_num)
  have hb := Numerics.bernoulli_le (a := (t:ℝ)) (h := 1) (p := 5/27) (q := -22/27)
    h0 (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hi : (t:ℝ)^(-22/27:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
  rw [show (t:ℝ)+1+ -1 = t by ring] at hu
  dsimp [base, scale]
  push_cast
  constructor <;> nlinarith

/-- The window scale is at least `1` for positive targets. -/
theorem one_le_scale {t : ℕ} (ht : 1 ≤ t) : 1 ≤ scale t :=
  Real.one_le_rpow (by exact_mod_cast ht) (by norm_num)

/-- The odd count differs from half the endpoint gap by at most one. -/
theorem candidate_rounding (E : ℕ → ℕ) (hE : Monotone E) (t : ℕ) :
    |(candidateCount E t:ℝ) - ((E (t+1):ℝ) - E t)/2| ≤ 1 := by
  have hL : E t ≤ E (t+1) := hE (Nat.le_succ t)
  have hlo : E (t+1) ≤ E t + 2*candidateCount E t + 1 := by dsimp [candidateCount]; omega
  have hhi : E t + 2*candidateCount E t ≤ E (t+1) + 1 := by dsimp [candidateCount]; omega
  have hloR : (E (t+1):ℝ) ≤ E t + 2*candidateCount E t + 1 := by exact_mod_cast hlo
  have hhiR : (E t:ℝ) + 2*candidateCount E t ≤ E (t+1) + 1 := by exact_mod_cast hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Any monotone endpoint within `c ≤ 4` of `base` has about `(16/27) scale t` odd
candidates, and its sources lie below `base t + (32/27) scale t + 6`. -/
theorem window_of_bounds {E : ℕ → ℕ} (hE : Monotone E) {c : ℝ} (hc : c ≤ 4)
    (hb : ∀ s, 1 ≤ s → base s ≤ E s ∧ (E s:ℝ) ≤ base s + c) {t : ℕ} (ht : 1 ≤ t) :
    |(candidateCount E t:ℝ) - (16/27) * scale t| ≤ 4 ∧
      ∀ n ∈ candidates E t, base t ≤ n ∧ (n:ℝ) ≤ base t + (32/27) * scale t + 6 := by
  obtain ⟨l0, u0⟩ := hb t ht
  obtain ⟨l1, u1⟩ := hb (t+1) (by omega)
  obtain ⟨pi1, pi2⟩ := power_increment ht
  have hr := abs_le.mp (candidate_rounding E hE t)
  refine ⟨abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
  intro n hn
  obtain ⟨_, hl, hu⟩ := (mem_candidates hE).mp hn
  have hlR : (E t:ℝ) ≤ n := by exact_mod_cast hl
  have huR : (n:ℝ) ≤ E (t+1) := by exact_mod_cast hu.le
  constructor <;> linarith

/-- The `OOOEE` candidate count is `(16/27) t^(5/27)` up to `4`, and its sources lie in the window. -/
theorem windowA {t : ℕ} (ht : 1 ≤ t) :
    |(candidateCount endpointA t:ℝ) - (16/27) * scale t| ≤ 4 ∧
      ∀ n ∈ candidates endpointA t, base t ≤ n ∧ (n:ℝ) ≤ base t + (32/27) * scale t + 6 :=
  window_of_bounds endpointA_monotone (by norm_num)
    (fun s hs => endpointA_bounds hs) ht

/-- The `OOEOE` candidate count is `(16/27) t^(5/27)` up to `4`, and its sources lie in the window. -/
theorem windowB {t : ℕ} (ht : 1 ≤ t) :
    |(candidateCount endpointB t:ℝ) - (16/27) * scale t| ≤ 4 ∧
      ∀ n ∈ candidates endpointB t, base t ≤ n ∧ (n:ℝ) ≤ base t + (32/27) * scale t + 6 :=
  window_of_bounds endpointB_monotone (by norm_num)
    (fun s hs => endpointB_bounds hs) ht

end Problems.Juggler.DepthFiveFibreGeometry
