import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Problems.Juggler.FateSweepMonotone
import Problems.Juggler.FateContagion

namespace Problems.Juggler

open Finset
open scoped Classical

namespace FiberParity

/-!
# Fiber parity: Lemma 4.2 of the fate-contagion paper

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Lemma 4.2: on a *good* fiber
`Φ(m)` (odd `n` with `m⁴ ≤ n³ < (m+1)⁴`), at least `H_m/3 - 2` of the images `⌊n^{3/2}⌋` are
even and at least `H_m/3 - 2` are odd. Goodness is the paper's: with
`α_m = {(3/2) m^{2/3}}`, `‖α_m‖ ≥ 22 m^{-1/3}` and `‖α_m - 1/2‖ ≥ 2 m^{-1/3}`, for
`m ≥ 10^6`.

The proof is the paper's, through Lemma 4.1' (`FateSweepMonotone`). Write `x(n) = n √n / 2`,
so that `⌊2 x(n)⌋ = ⌊√(n³)⌋ = Nat.sqrt (n³)` and the image is even iff `{x(n)} < 1/2`
(`cell_xval_even_iff`). Along the fiber `n_j = n₀ + 2j` the step is
`x(n+2) - x(n) = (u² + uv + v²)/(u + v)` with `u = √(n+2)`, `v = √n` (`xval_step`), which
lies in `[(3/2) v, (3/2) u]` by `(2u + v)(u - v) ≥ 0` and `(u + 2v)(u - v) ≥ 0`
(`xval_step_ge`, `xval_step_le`), and is nondecreasing in `n` because the upper bound at `n`
is the lower bound at `n + 2` (`xval_step_mono`); no derivative is needed. The fiber holds
at least `(2/3) m^{1/3} - 1` odd integers by Bernoulli on `(1 + 1/m)^{4/3}` (`fiber_card_ge`).

Case 1 (`α_m ≤ 1/2 - 2 m^{-1/3}`) subtracts `j ⌊A_m⌋` from `x_j`, which keeps every fractional
part and puts the steps in `[α_m, α_m + η_m]` with `η_m ≤ m^{-1/3}`; Case 2
(`α_m ≥ 1/2 + 2 m^{-1/3}`) uses `j(⌊A_m⌋ + 1) - x_j` with nonincreasing steps in
`[1 - α_m - η_m, 1 - α_m]`, and `⌈2 z_j⌉ ≡ ⌊2 x_j⌋ (mod 2)` carries the parity across.

Not a statement about all fibers: the bad fibers are Lemma 4.3, which stays a human proof.
Not a halt theorem.
-/

/-! ### The half-value `x(n) = n √n / 2` and its parity -/

/-- `x(n) = n √n / 2 = n^{3/2}/2`. -/
noncomputable def xval (n : ℕ) : ℝ := (n : ℝ) * Real.sqrt n / 2

theorem two_xval (n : ℕ) : 2 * xval n = Real.sqrt (((n ^ 3 : ℕ) : ℝ)) := by
  unfold xval
  have hn : (0 : ℝ) ≤ n := by positivity
  push_cast
  rw [show (n : ℝ) ^ 3 = ((n : ℝ) * n) * n by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_mul_self hn]
  ring

theorem floor_two_xval (n : ℕ) : ⌊2 * xval n⌋ = ((Nat.sqrt (n ^ 3) : ℕ) : ℤ) := by
  rw [two_xval, Real.floor_real_sqrt_eq_nat_sqrt]

/-- The image `⌊n^{3/2}⌋` is even iff `{x(n)} < 1/2`, i.e. iff the half-cell of `x(n)` is even. -/
theorem cell_xval_even_iff (n : ℕ) :
    Sweep.cell (xval n) ≡ 0 [ZMOD 2] ↔ Nat.sqrt (n ^ 3) % 2 = 0 := by
  unfold Sweep.cell
  rw [floor_two_xval]
  unfold Int.ModEq
  omega

theorem cell_xval_odd_iff (n : ℕ) :
    Sweep.cell (xval n) ≡ 1 [ZMOD 2] ↔ Nat.sqrt (n ^ 3) % 2 = 1 := by
  unfold Sweep.cell
  rw [floor_two_xval]
  unfold Int.ModEq
  omega

/-! ### The step over two units -/

theorem xval_step (n : ℕ) :
    xval (n + 2) - xval n =
      (Real.sqrt (n + 2) ^ 2 + Real.sqrt (n + 2) * Real.sqrt n + Real.sqrt n ^ 2) /
        (Real.sqrt (n + 2) + Real.sqrt n) := by
  set u := Real.sqrt ((n : ℝ) + 2) with hu
  set v := Real.sqrt (n : ℝ) with hv
  have hu2 : u ^ 2 = (n : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hupos : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hsum : 0 < u + v := by linarith
  unfold xval
  push_cast
  rw [eq_div_iff hsum.ne']
  have huv : u ^ 2 - v ^ 2 = 2 := by rw [hu2, hv2]; ring
  -- replace `n + 2` and `n` by `u²` and `v²`
  rw [show ((n : ℝ) + 2) * u / 2 - (n : ℝ) * v / 2 = (u ^ 2 * u - v ^ 2 * v) / 2 by
    rw [hu2, hv2]; ring]
  linear_combination ((u ^ 2 + u * v + v ^ 2) / 2) * huv

theorem xval_step_ge (n : ℕ) : 3 / 2 * Real.sqrt n ≤ xval (n + 2) - xval n := by
  rw [xval_step]
  set u := Real.sqrt ((n : ℝ) + 2) with hu
  set v := Real.sqrt (n : ℝ) with hv
  have hupos : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hvu : v ≤ u := Real.sqrt_le_sqrt (by linarith)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * u + v) (sub_nonneg.mpr hvu)]

theorem xval_step_le (n : ℕ) : xval (n + 2) - xval n ≤ 3 / 2 * Real.sqrt (n + 2) := by
  rw [xval_step]
  set u := Real.sqrt ((n : ℝ) + 2) with hu
  set v := Real.sqrt (n : ℝ) with hv
  have hupos : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hvu : v ≤ u := Real.sqrt_le_sqrt (by linarith)
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u + 2 * v) (sub_nonneg.mpr hvu)]

/-- The steps are nondecreasing: the upper bound at `n` is the lower bound at `n + 2`. -/
theorem xval_step_mono (n : ℕ) : xval (n + 2) - xval n ≤ xval (n + 4) - xval (n + 2) := by
  have h1 := xval_step_le n
  have h2 := xval_step_ge (n + 2)
  push_cast at h2
  have e : (n : ℝ) + 2 + 2 = n + 4 := by ring
  rw [show n + 2 + 2 = n + 4 by omega] at h2
  linarith

/-! ### The fiber and its enumeration -/

/-- The `OE` fiber `Φ(m)`: odd `n` with `m⁴ ≤ n³ < (m+1)⁴`. -/
noncomputable def oeFiber (m : ℕ) : Finset ℕ :=
  (Finset.range ((m + 1) ^ 2 + 1)).filter (fun n => n % 2 = 1 ∧ m ^ 4 ≤ n ^ 3 ∧ n ^ 3 < (m + 1) ^ 4)

theorem mem_oeFiber {m n : ℕ} :
    n ∈ oeFiber m ↔ n % 2 = 1 ∧ m ^ 4 ≤ n ^ 3 ∧ n ^ 3 < (m + 1) ^ 4 := by
  unfold oeFiber
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    -- `n³ < (m+1)⁴ ≤ (m+1)⁶ = ((m+1)²)³` forces `n < (m+1)²`
    by_contra hge
    push Not at hge
    have : ((m + 1) ^ 2) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h6 : (m + 1) ^ 4 ≤ ((m + 1) ^ 2) ^ 3 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

/-- Even images on the fiber. -/
noncomputable def evenImageCount (m : ℕ) : ℕ :=
  #{n ∈ oeFiber m | Nat.sqrt (n ^ 3) % 2 = 0}

/-- The fiber is an interval of odd integers: an odd `n` between two members is a member. -/
theorem oeFiber_between {m a b n : ℕ} (ha : a ∈ oeFiber m) (hb : b ∈ oeFiber m)
    (hn : n % 2 = 1) (han : a ≤ n) (hnb : n ≤ b) : n ∈ oeFiber m := by
  rw [mem_oeFiber] at ha hb ⊢
  refine ⟨hn, le_trans ha.2.1 (Nat.pow_le_pow_left han 3),
    lt_of_le_of_lt (Nat.pow_le_pow_left hnb 3) hb.2.2⟩

/-- With `n₀ = min Φ(m)` and `n₁ = max Φ(m)`, the fiber is `{n₀ + 2j : j < (n₁ - n₀)/2 + 1}`. -/
theorem oeFiber_eq_image {m : ℕ} (hne : (oeFiber m).Nonempty) :
    oeFiber m = (Finset.range ((( oeFiber m).max' hne - (oeFiber m).min' hne) / 2 + 1)).image
      (fun j => (oeFiber m).min' hne + 2 * j) := by
  set n₀ := (oeFiber m).min' hne with hn₀
  set n₁ := (oeFiber m).max' hne with hn₁
  have h₀ : n₀ ∈ oeFiber m := Finset.min'_mem _ hne
  have h₁ : n₁ ∈ oeFiber m := Finset.max'_mem _ hne
  have h₀odd : n₀ % 2 = 1 := (mem_oeFiber.mp h₀).1
  have h₁odd : n₁ % 2 = 1 := (mem_oeFiber.mp h₁).1
  have h₀₁ : n₀ ≤ n₁ := Finset.min'_le _ _ h₁
  ext n
  rw [Finset.mem_image]
  constructor
  · intro hn
    have hodd : n % 2 = 1 := (mem_oeFiber.mp hn).1
    have hlo : n₀ ≤ n := Finset.min'_le _ _ hn
    have hhi : n ≤ n₁ := Finset.le_max' _ _ hn
    refine ⟨(n - n₀) / 2, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    apply oeFiber_between h₀ h₁ (by omega) (by omega) (by omega)

/-- The fiber's cardinality is the number of enumerated indices. -/
theorem oeFiber_card {m : ℕ} (hne : (oeFiber m).Nonempty) :
    (oeFiber m).card = ((oeFiber m).max' hne - (oeFiber m).min' hne) / 2 + 1 := by
  conv_lhs => rw [oeFiber_eq_image hne]
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]

/-- The even-image count, enumerated. -/
theorem evenImageCount_eq {m : ℕ} (hne : (oeFiber m).Nonempty) :
    evenImageCount m =
      #{j ∈ Finset.range (((oeFiber m).max' hne - (oeFiber m).min' hne) / 2 + 1) |
        Nat.sqrt (((oeFiber m).min' hne + 2 * j) ^ 3) % 2 = 0} := by
  unfold evenImageCount
  conv_lhs => rw [oeFiber_eq_image hne]
  rw [Finset.filter_image, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]

/-! ### Real bounds on the fiber -/

/-- `n ∈ Φ(m)` gives `m^{4/3} ≤ n` as reals. -/
theorem fiber_ge_rpow {m n : ℕ} (hn : n ∈ oeFiber m) : (m : ℝ) ^ ((4 : ℝ) / 3) ≤ n := by
  have h := (mem_oeFiber.mp hn).2.1
  have h' : ((m : ℝ)) ^ (4 : ℕ) ≤ (n : ℝ) ^ (3 : ℕ) := by exact_mod_cast h
  have hm : (0 : ℝ) ≤ m := by positivity
  have key : ((m : ℝ) ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = (m : ℝ) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm]
    norm_num
  rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg hm _) (by positivity) (by norm_num : (3 : ℕ) ≠ 0),
    key]
  exact h'

/-- `n ∈ Φ(m)` gives `n < (m+1)^{4/3}` as reals. -/
theorem fiber_lt_rpow {m n : ℕ} (hn : n ∈ oeFiber m) : (n : ℝ) < ((m : ℝ) + 1) ^ ((4 : ℝ) / 3) := by
  have h := (mem_oeFiber.mp hn).2.2
  have h' : (n : ℝ) ^ (3 : ℕ) < ((m : ℝ) + 1) ^ (4 : ℕ) := by exact_mod_cast h
  have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have key : (((m : ℝ) + 1) ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = ((m : ℝ) + 1) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm]
    norm_num
  rw [← pow_lt_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hm _) (by norm_num : (3 : ℕ) ≠ 0),
    key]
  exact h'

/-- `√(m^{4/3}) = m^{2/3}`. -/
theorem sqrt_rpow_four_thirds (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (t ^ ((4 : ℝ) / 3)) = t ^ ((2 : ℝ) / 3) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
  norm_num

/-- Bernoulli, lower: `(m+1)^{4/3} ≥ m^{4/3} + (4/3) m^{1/3}` for `m ≥ 1`. -/
theorem rpow_four_thirds_succ_ge {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) ^ ((4 : ℝ) / 3) + 4 / 3 * (m : ℝ) ^ ((1 : ℝ) / 3) ≤ ((m : ℝ) + 1) ^ ((4 : ℝ) / 3) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := one_add_mul_self_le_rpow_one_add (s := 1 / (m : ℝ)) (by
    have : (0 : ℝ) ≤ 1 / m := by positivity
    linarith) (p := (4 : ℝ) / 3) (by norm_num)
  have e : (1 : ℝ) + 1 / m = ((m : ℝ) + 1) / m := by field_simp
  rw [e, Real.div_rpow (by positivity) hm0.le] at hb
  have hpos : 0 < (m : ℝ) ^ ((4 : ℝ) / 3) := Real.rpow_pos_of_pos hm0 _
  rw [le_div_iff₀ hpos] at hb
  have h13 : (m : ℝ) ^ ((4 : ℝ) / 3) = (m : ℝ) ^ ((1 : ℝ) / 3) * m := by
    rw [show (4 : ℝ) / 3 = 1 / 3 + 1 by norm_num, Real.rpow_add hm0, Real.rpow_one]
  calc (m : ℝ) ^ ((4 : ℝ) / 3) + 4 / 3 * (m : ℝ) ^ ((1 : ℝ) / 3)
      = (1 + 4 / 3 * (1 / (m : ℝ))) * (m : ℝ) ^ ((4 : ℝ) / 3) := by
        rw [h13]; field_simp
    _ ≤ ((m : ℝ) + 1) ^ ((4 : ℝ) / 3) := hb

/-- Bernoulli, upper: `(m+1)^{2/3} ≤ m^{2/3} + (2/3) m^{-1/3}` for `m ≥ 1`. -/
theorem rpow_two_thirds_succ_le {m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ ((2 : ℝ) / 3) ≤ (m : ℝ) ^ ((2 : ℝ) / 3) + 2 / 3 * (m : ℝ) ^ (-((1 : ℝ) / 3)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := rpow_one_add_le_one_add_mul_self (s := 1 / (m : ℝ)) (by
    have : (0 : ℝ) ≤ 1 / m := by positivity
    linarith) (p := (2 : ℝ) / 3) (by norm_num) (by norm_num)
  have e : (1 : ℝ) + 1 / m = ((m : ℝ) + 1) / m := by field_simp
  rw [e, Real.div_rpow (by positivity) hm0.le] at hb
  have hpos : 0 < (m : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hm0 _
  rw [div_le_iff₀ hpos] at hb
  have h13 : (m : ℝ) ^ ((2 : ℝ) / 3) = (m : ℝ) ^ (-((1 : ℝ) / 3)) * m := by
    rw [show (2 : ℝ) / 3 = -(1 / 3) + 1 by norm_num, Real.rpow_add hm0, Real.rpow_one]
  calc ((m : ℝ) + 1) ^ ((2 : ℝ) / 3) ≤ (1 + 2 / 3 * (1 / (m : ℝ))) * (m : ℝ) ^ ((2 : ℝ) / 3) := hb
    _ = (m : ℝ) ^ ((2 : ℝ) / 3) + 2 / 3 * (m : ℝ) ^ (-((1 : ℝ) / 3)) := by
        rw [h13]; field_simp

/-- The fiber holds at least `(2/3) m^{1/3} - 1` odd integers (`m ≥ 1`). -/
theorem fiber_card_ge {m : ℕ} (hm : 1 ≤ m) :
    2 / 3 * (m : ℝ) ^ ((1 : ℝ) / 3) - 1 ≤ (oeFiber m).card := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set L := (m : ℝ) ^ ((4 : ℝ) / 3) with hL
  set R := ((m : ℝ) + 1) ^ ((4 : ℝ) / 3) with hR
  have hL1 : 1 ≤ L := Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
  have hLR : L + 4 / 3 * (m : ℝ) ^ ((1 : ℝ) / 3) ≤ R := rpow_four_thirds_succ_ge hm
  -- the odd integers `2k + 1` with `L ≤ 2k + 1 < R`
  set k₀ := ⌈(L - 1) / 2⌉₊ with hk₀
  set k₁ := ⌈(R - 1) / 2⌉₊ with hk₁
  have hmaps : ∀ k ∈ Finset.Ico k₀ k₁, 2 * k + 1 ∈ oeFiber m := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [mem_oeFiber]
    refine ⟨by omega, ?_, ?_⟩
    · -- `L ≤ 2k + 1`, hence `m⁴ = L³ ≤ (2k+1)³`
      have h1 : (L - 1) / 2 ≤ k := le_trans (Nat.le_ceil _) (by exact_mod_cast hk.1)
      have h2 : L ≤ ((2 * k + 1 : ℕ) : ℝ) := by push_cast; linarith
      have key : L ^ (3 : ℕ) = (m : ℝ) ^ (4 : ℕ) := by
        rw [hL, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
      have h3 : L ^ (3 : ℕ) ≤ ((2 * k + 1 : ℕ) : ℝ) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (by linarith) h2 3
      rw [key] at h3
      exact_mod_cast h3
    · -- `k < (R - 1)/2`, hence `2k + 1 < R` and `(2k+1)³ < R³ = (m+1)⁴`
      have h1 : (k : ℝ) < (R - 1) / 2 := by
        have := hk.2
        rw [hk₁, Nat.lt_ceil] at this
        exact this
      have h2 : ((2 * k + 1 : ℕ) : ℝ) < R := by push_cast; linarith
      have key : R ^ (3 : ℕ) = ((m : ℝ) + 1) ^ (4 : ℕ) := by
        rw [hR, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have h3 : ((2 * k + 1 : ℕ) : ℝ) ^ (3 : ℕ) < R ^ (3 : ℕ) :=
        pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
      rw [key] at h3
      exact_mod_cast h3
  have hinj : Set.InjOn (fun k : ℕ => 2 * k + 1) ↑(Finset.Ico k₀ k₁) := by
    intro a _ b _ h
    simp only at h
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Ico] at hcard
  -- `k₁ - k₀ ≥ (R - L)/2 - 1`
  have hk₁ge : (R - 1) / 2 ≤ (k₁ : ℝ) := Nat.le_ceil _
  have hk₀lt : (k₀ : ℝ) < (L - 1) / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hk₀k₁ : k₀ ≤ k₁ := by
    rw [hk₀, hk₁]
    apply Nat.ceil_le_ceil
    have : (0 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hm0.le _
    linarith
  have hsub : ((k₁ - k₀ : ℕ) : ℝ) = (k₁ : ℝ) - k₀ := by
    rw [Nat.cast_sub hk₀k₁]
  have hcard' : ((k₁ - k₀ : ℕ) : ℝ) ≤ (oeFiber m).card := by exact_mod_cast hcard
  rw [hsub] at hcard'
  linarith

/-! ### The constants and goodness -/

/-- `A_m = (3/2) m^{2/3}`, the lower step of the fiber. -/
noncomputable def Am (m : ℕ) : ℝ := 3 / 2 * (m : ℝ) ^ ((2 : ℝ) / 3)

/-- `α_m = {A_m}`. -/
noncomputable def alpha (m : ℕ) : ℝ := Int.fract (Am m)

/-- `ε_m = m^{-1/3}`, the scale of the step drift. -/
noncomputable def eps (m : ℕ) : ℝ := (m : ℝ) ^ (-((1 : ℝ) / 3))

/-- The paper's goodness, unpacked: `‖α_m‖ ≥ 22 ε_m` and `‖α_m - 1/2‖ ≥ 2 ε_m`. -/
def Good (m : ℕ) : Prop :=
  22 * eps m ≤ alpha m ∧ alpha m ≤ 1 - 22 * eps m ∧
    (alpha m ≤ 1 / 2 - 2 * eps m ∨ 1 / 2 + 2 * eps m ≤ alpha m)

theorem eps_pos {m : ℕ} (hm : 1 ≤ m) : 0 < eps m :=
  Real.rpow_pos_of_pos (by exact_mod_cast hm) _

theorem eps_mul_cbrt {m : ℕ} (hm : 1 ≤ m) : eps m * (m : ℝ) ^ ((1 : ℝ) / 3) = 1 := by
  unfold eps
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← Real.rpow_add hm0]
  norm_num

/-- `ε_m ≤ 1/100` for `m ≥ 10^6`. -/
theorem eps_le {m : ℕ} (hm : 10 ^ 6 ≤ m) : eps m ≤ 1 / 100 := by
  unfold eps
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [Real.rpow_neg hm0.le, inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  have h : ((100 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = 100 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [← h]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  have : ((10 ^ 6 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
  norm_num at this ⊢
  linarith

/-- The upper step `(3/2)(m+1)^{2/3}` is at most `A_m + ε_m`. -/
theorem upper_step_le {m : ℕ} (hm : 1 ≤ m) :
    3 / 2 * ((m : ℝ) + 1) ^ ((2 : ℝ) / 3) ≤ Am m + eps m := by
  unfold Am eps
  have := rpow_two_thirds_succ_le hm
  linarith

/-! ### The enumerated fiber: steps in `[A_m, A_m + ε_m]`, nondecreasing -/

section Enumerated

variable {m : ℕ} (hne : (oeFiber m).Nonempty)

/-- `n_j = n₀ + 2j`. -/
noncomputable def nseq (m : ℕ) (hne : (oeFiber m).Nonempty) (j : ℕ) : ℕ :=
  (oeFiber m).min' hne + 2 * j

/-- The enumeration length `H`. -/
noncomputable def Hlen (m : ℕ) (hne : (oeFiber m).Nonempty) : ℕ :=
  ((oeFiber m).max' hne - (oeFiber m).min' hne) / 2 + 1

theorem nseq_mem {j : ℕ} (hj : j < Hlen m hne) : nseq m hne j ∈ oeFiber m := by
  rw [oeFiber_eq_image hne]
  exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hj)

theorem nseq_succ (j : ℕ) : nseq m hne (j + 1) = nseq m hne j + 2 := by
  unfold nseq; ring

/-- The step of `x` along the fiber, bounded below by `A_m`. -/
theorem step_ge {j : ℕ} (hj : j < Hlen m hne) :
    Am m ≤ xval (nseq m hne (j + 1)) - xval (nseq m hne j) := by
  rw [nseq_succ]
  have h := xval_step_ge (nseq m hne j)
  have hlo := fiber_ge_rpow (nseq_mem hne hj)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hsq : Real.sqrt ((m : ℝ) ^ ((4 : ℝ) / 3)) ≤ Real.sqrt (nseq m hne j) :=
    Real.sqrt_le_sqrt hlo
  rw [sqrt_rpow_four_thirds _ hm0] at hsq
  unfold Am
  linarith

/-- The step of `x` along the fiber, bounded above by `A_m + ε_m`. -/
theorem step_le (hm : 1 ≤ m) {j : ℕ} (hj : j + 1 < Hlen m hne) :
    xval (nseq m hne (j + 1)) - xval (nseq m hne j) ≤ Am m + eps m := by
  have h := xval_step_le (nseq m hne j)
  have hhi := fiber_lt_rpow (nseq_mem hne hj)
  rw [nseq_succ] at hhi
  push_cast at hhi
  have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hsq : Real.sqrt ((nseq m hne j : ℝ) + 2) ≤ Real.sqrt (((m : ℝ) + 1) ^ ((4 : ℝ) / 3)) :=
    Real.sqrt_le_sqrt hhi.le
  rw [sqrt_rpow_four_thirds _ hm0] at hsq
  rw [nseq_succ]
  have := upper_step_le hm
  linarith

theorem step_mono' (j : ℕ) :
    xval (nseq m hne (j + 1)) - xval (nseq m hne j) ≤
      xval (nseq m hne (j + 2)) - xval (nseq m hne (j + 1)) := by
  have e1 : nseq m hne (j + 1) = nseq m hne j + 2 := nseq_succ hne j
  have e2 : nseq m hne (j + 2) = nseq m hne j + 4 := by unfold nseq; ring
  rw [e1, e2]
  exact xval_step_mono _

/-- The number of enumerated indices is the fiber's cardinality. -/
theorem Hlen_eq : Hlen m hne = (oeFiber m).card := (oeFiber_card hne).symm

/-- The even images, enumerated. -/
theorem evenImageCount_eq' :
    evenImageCount m = #{j ∈ Finset.range (Hlen m hne) | Nat.sqrt ((nseq m hne j) ^ 3) % 2 = 0} :=
  evenImageCount_eq hne

/-- The odd images are the rest. -/
theorem oddImageCount_eq' :
    #{j ∈ Finset.range (Hlen m hne) | Nat.sqrt ((nseq m hne j) ^ 3) % 2 = 1} =
      Hlen m hne - evenImageCount m := by
  rw [evenImageCount_eq' hne]
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range (Hlen m hne)) (fun j => Nat.sqrt ((nseq m hne j) ^ 3) % 2 = 0)
  rw [Finset.card_range] at h
  have e : {j ∈ Finset.range (Hlen m hne) | ¬ Nat.sqrt ((nseq m hne j) ^ 3) % 2 = 0} =
      {j ∈ Finset.range (Hlen m hne) | Nat.sqrt ((nseq m hne j) ^ 3) % 2 = 1} := by
    apply Finset.filter_congr
    intro j _
    omega
  rw [e] at h
  omega

end Enumerated

/-! ### The theorem -/

/-- **Lemma 4.2 (fiber parity).** On a good fiber with `m ≥ 10^6`, at least `H_m/3 - 2`
images are even and at least `H_m/3 - 2` are odd. -/
theorem fiber_parity_good {m : ℕ} (hm : 10 ^ 6 ≤ m) (hgood : Good m) :
    ((oeFiber m).card : ℝ) / 3 - 2 ≤ evenImageCount m ∧
      ((oeFiber m).card : ℝ) / 3 - 2 ≤ ((oeFiber m).card : ℝ) - evenImageCount m := by
  have hm1 : 1 ≤ m := by omega
  have hε := eps_le hm
  have hεpos := eps_pos hm1
  have hprod := eps_mul_cbrt hm1
  have hcbrt0 : 0 ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  have hcbrt : (100 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := by
    -- from `ε ≤ 1/100` and `ε · m^{1/3} = 1`
    by_contra hlt
    push Not at hlt
    have : eps m * (m : ℝ) ^ ((1 : ℝ) / 3) < eps m * 100 :=
      mul_lt_mul_of_pos_left hlt hεpos
    linarith
  have hcard := fiber_card_ge hm1
  have hne : (oeFiber m).Nonempty := by
    rw [← Finset.card_pos]
    have : (1 : ℝ) ≤ (oeFiber m).card := by linarith
    exact_mod_cast this
  -- the enumeration
  set H := Hlen m hne with hHdef
  have hH : ((oeFiber m).card : ℝ) = H := by rw [hHdef, Hlen_eq hne]
  have hH1 : (2 : ℝ) / 3 * (m : ℝ) ^ ((1 : ℝ) / 3) - 2 ≤ (H : ℝ) - 1 := by linarith
  have hHpos : 1 ≤ H := by
    have : (1 : ℝ) ≤ H := by linarith
    exact_mod_cast this
  obtain ⟨hg1, hg2, hg3⟩ := hgood
  set α := alpha m with hαdef
  set ε := eps m with hεdef
  set N : ℤ := ⌊Am m⌋ with hN
  have hαN : Am m - N = α := by rw [hαdef]; unfold alpha; exact Int.self_sub_floor _
  -- the two counts as filters over the enumeration
  have hG := evenImageCount_eq' hne
  have hOdd := oddImageCount_eq' hne
  -- parity of the half-cell of `x_j`
  have hcell0 : ∀ j, Sweep.cell (xval (nseq m hne j)) ≡ 0 [ZMOD 2] ↔
      Nat.sqrt ((nseq m hne j) ^ 3) % 2 = 0 := fun j => cell_xval_even_iff _
  have hcell1 : ∀ j, Sweep.cell (xval (nseq m hne j)) ≡ 1 [ZMOD 2] ↔
      Nat.sqrt ((nseq m hne j) ^ 3) % 2 = 1 := fun j => cell_xval_odd_iff _
  -- `(H - 1) · 22ε ≥ 12` and `(H - 1) · 21ε ≥ 12`
  have h12a : 12 ≤ ((H : ℝ) - 1) * (22 * ε) := by
    have : (2 / 3 * (m : ℝ) ^ ((1 : ℝ) / 3) - 2) * (22 * ε) ≤ ((H : ℝ) - 1) * (22 * ε) :=
      mul_le_mul_of_nonneg_right hH1 (by positivity)
    have e : (2 / 3 * (m : ℝ) ^ ((1 : ℝ) / 3) - 2) * (22 * ε) = 44 / 3 - 44 * ε := by
      have := hprod
      rw [hεdef] at this ⊢
      linear_combination (44 / 3) * this
    rw [e] at this
    linarith
  have h12b : 12 ≤ ((H : ℝ) - 1) * (21 * ε) := by
    have : (2 / 3 * (m : ℝ) ^ ((1 : ℝ) / 3) - 2) * (21 * ε) ≤ ((H : ℝ) - 1) * (21 * ε) :=
      mul_le_mul_of_nonneg_right hH1 (by positivity)
    have e : (2 / 3 * (m : ℝ) ^ ((1 : ℝ) / 3) - 2) * (21 * ε) = 14 - 42 * ε := by
      have := hprod
      rw [hεdef] at this ⊢
      linear_combination 14 * this
    rw [e] at this
    linarith
  rcases hg3 with hcase | hcase
  · -- Case 1: `y_j = x_j - j N`, steps in `[α, α + ε]`, nondecreasing
    set y : ℕ → ℝ := fun j => xval (nseq m hne j) - (j : ℝ) * N with hy
    have hsteps : ∀ j, j + 1 < H → α ≤ y (j + 1) - y j ∧ y (j + 1) - y j ≤ α + ε := by
      intro j hj
      have h1 := step_ge hne (show j < Hlen m hne by omega)
      have h2 := step_le hne hm1 (show j + 1 < Hlen m hne from hj)
      simp only [hy]
      push_cast
      constructor <;> linarith
    have hmono : Sweep.MonoSteps y H := by
      intro j _
      have := step_mono' hne j
      simp only [hy]
      push_cast
      linarith
    have h12α : 12 ≤ ((H : ℝ) - 1) * α := by
      refine le_trans h12a (mul_le_mul_of_nonneg_left hg1 ?_)
      have : (1 : ℝ) ≤ H := by exact_mod_cast hHpos
      linarith
    have hres := Sweep.sweep_monotone_cell (x := y) (H := H) (a := α) (b := α + ε)
      (by linarith) (by linarith) (by linarith) (by linarith) h12α hsteps (Or.inl hmono)
    -- the half-cell of `y_j` has the parity of the half-cell of `x_j`
    have hcelly : ∀ j, Sweep.cell (y j) = Sweep.cell (xval (nseq m hne j)) - 2 * ((j : ℤ) * N) := by
      intro j
      simp only [hy, Sweep.cell]
      rw [show 2 * (xval (nseq m hne j) - (j : ℝ) * N) =
        2 * xval (nseq m hne j) - ((2 * ((j : ℤ) * N) : ℤ) : ℝ) by push_cast; ring,
        Int.floor_sub_intCast]
    have hfilt : ∀ v : ℤ, {j ∈ Finset.range H | Sweep.cell (y j) ≡ v [ZMOD 2]} =
        {j ∈ Finset.range H | Sweep.cell (xval (nseq m hne j)) ≡ v [ZMOD 2]} := by
      intro v
      apply Finset.filter_congr
      intro j _
      rw [hcelly j]
      unfold Int.ModEq
      omega
    constructor
    · have := hres 0
      rw [hfilt 0, Finset.filter_congr (fun j _ => hcell0 j), ← hG] at this
      rw [hH]; exact this
    · have := hres 1
      rw [hfilt 1, Finset.filter_congr (fun j _ => hcell1 j), hOdd] at this
      rw [hH]
      have hGle : evenImageCount m ≤ Hlen m hne := by
        rw [hG]; exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))
      rw [Nat.cast_sub hGle, ← hHdef] at this
      exact this
  · -- Case 2: `z_j = j (N + 1) - x_j`, steps in `[1 - α - ε, 1 - α]`, nonincreasing
    set z : ℕ → ℝ := fun j => (j : ℝ) * ((N : ℝ) + 1) - xval (nseq m hne j) with hz
    have hsteps : ∀ j, j + 1 < H →
        1 - α - ε ≤ z (j + 1) - z j ∧ z (j + 1) - z j ≤ 1 - α := by
      intro j hj
      have h1 := step_ge hne (show j < Hlen m hne by omega)
      have h2 := step_le hne hm1 (show j + 1 < Hlen m hne from hj)
      simp only [hz]
      push_cast
      constructor <;> linarith
    have hanti : Sweep.AntiSteps z H := by
      intro j _
      have := step_mono' hne j
      simp only [hz]
      push_cast
      linarith
    have hres := sweep_monotone_ceil z H (1 - α - ε) (1 - α)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (by
        have : ((H : ℝ) - 1) * (21 * ε) ≤ ((H : ℝ) - 1) * (1 - α - ε) := by
          apply mul_le_mul_of_nonneg_left _ (by
            have : (1 : ℝ) ≤ H := by exact_mod_cast hHpos
            linarith)
          linarith
        linarith) hsteps (Or.inr hanti)
    -- `⌈2 z_j⌉ = 2j(N+1) - ⌊2 x_j⌋`, of the parity of `⌊2 x_j⌋`
    have hceilz : ∀ j, ⌈2 * z j⌉ = 2 * ((j : ℤ) * (N + 1)) - Sweep.cell (xval (nseq m hne j)) := by
      intro j
      simp only [hz, Sweep.cell]
      rw [show 2 * ((j : ℝ) * ((N : ℝ) + 1) - xval (nseq m hne j)) =
        -(2 * xval (nseq m hne j)) + ((2 * ((j : ℤ) * (N + 1)) : ℤ) : ℝ) by push_cast; ring,
        Int.ceil_add_intCast, Int.ceil_neg]
      ring
    have hfilt : ∀ v : ℤ, {j ∈ Finset.range H | ⌈2 * z j⌉ ≡ v [ZMOD 2]} =
        {j ∈ Finset.range H | Sweep.cell (xval (nseq m hne j)) ≡ v [ZMOD 2]} := by
      intro v
      apply Finset.filter_congr
      intro j _
      rw [hceilz j]
      unfold Int.ModEq
      omega
    constructor
    · have := hres 0
      rw [hfilt 0, Finset.filter_congr (fun j _ => hcell0 j), ← hG] at this
      rw [hH]; exact this
    · have := hres 1
      rw [hfilt 1, Finset.filter_congr (fun j _ => hcell1 j), hOdd] at this
      rw [hH]
      have hGle : evenImageCount m ≤ Hlen m hne := by
        rw [hG]; exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))
      rw [Nat.cast_sub hGle, ← hHdef] at this
      exact this

end FiberParity

end Problems.Juggler
