import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Problems.Juggler.WalkChargeMax

namespace Problems.Juggler

/-!
# Defect-sum finance and the walk-charge kill criterion
(Paper A Theorem 4.6 identity + Theorem 5.9 mechanism)

The certified identity behind the finance kill tables is the
relative-defect form

`1 − 2^L/3^o ≤ (6/5) · Σ_k 1/(x_k log x_k)`

on any minimum-based cycle. This module proves it in Lean
(`cycleMin_defect_finance`) with the exact per-step floor losses in
image form: for a state `x` with image `y = T(x)`, the relative
defect `δ = (x^e − y²)/x^e` satisfies `δ ≤ 2/y`, and
`−log(1−δ) ≤ (6/5)δ` on `δ ≤ 1/6` (`neg_log_one_sub_le_sixth`), so
each step loses at most `(6/5)/y` in log terms
(`log_floorPower_even_ge_sub`, `log_floorPower_odd_ge_sub`). The
unroll is the same weight induction as `WalkTransport.lean`, run
twice: an upper invariant `log x_k ≤ w_k log n`
(`cycleMin_log_le_weight`) prices the amplification, and a charged
lower invariant `w_k(log n − C_k) ≤ log x_k`
(`cycleMin_charge_prefix`) accumulates the defect charges. Closing
the cycle at `x_L = n` gives the finance inequality.

Chaining with the defect-to-hug-charge envelope
(`cycleMin_defect_le_hug_charge`, `WalkChargeMax.lean`) yields the
**kill criterion** (`cycleMin_hug_kill_criterion`): every
minimum-based cycle at `n ≥ 400` with positive reduced log-base must
satisfy

`1 − 2^L/3^o ≤ (6/5) · Σ_k g(hugWeight k)`

at the reduced base. The kill evaluations of Paper A Theorem 5.9
check the numeric failure of this inequality per length — that
arithmetic stays verified computation; the implication is now Lean.
Not a cycle obstruction by itself and not a halt theorem.
-/

/-!
## The elementary log inequality at threshold 1/6
-/

/-- `−log(1−t) ≤ 1.2·t` for `0 ≤ t ≤ 1/6` — the paper's `6/5`
majorant of `−log(1−δ)/δ` on `[0,1/6]`. Instance of the
parameterized majorant `neg_log_one_sub_le_mul` at `c = 6/5`. -/
theorem neg_log_one_sub_le_sixth {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 6) :
    -Real.log (1 - t) ≤ 1.2 * t :=
  neg_log_one_sub_le_mul (by norm_num) h0 (by norm_num at h1 ⊢; linarith)

/-!
## Per-step floor losses, image form

Upper side: the floor only loses, `log T(x) ≤ m·log x`.
Lower side: the loss is at most `1.2/T(x)` — priced at the image,
which is what the defect sum charges.
-/

/-- Even step, upper side: `log T(x) ≤ (1/2)·log x` for even
`x ≥ 1`. -/
theorem log_floorPower_even_le {x : ℕ} (_hx : 1 ≤ x) (he : x % 2 = 0) :
    Real.log (floorPower x) ≤ Real.log x / 2 := by
  have hcell :=
    (floorPower_even_eq_iff_sq_interval (n := x) (M := floorPower x) he).mp rfl
  have h1 : 1 ≤ floorPower x := by
    by_contra h0
    have hy0 : floorPower x = 0 := by omega
    have h2 := hcell.2
    rw [hy0] at h2
    simp at h2
    omega
  have hfpR : (1 : ℝ) ≤ (floorPower x : ℝ) := by exact_mod_cast h1
  have hle : ((floorPower x : ℝ)) ^ 2 ≤ (x : ℝ) := by exact_mod_cast hcell.1
  have hlog := Real.log_le_log (by nlinarith) hle
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- Odd step, upper side: `log T(x) ≤ (3/2)·log x` for odd
`x ≥ 1`. -/
theorem log_floorPower_odd_le {x : ℕ} (_hx : 1 ≤ x) (ho : x % 2 = 1) :
    Real.log (floorPower x) ≤ 3 * Real.log x / 2 := by
  have hcell :=
    (floorPower_odd_eq_iff_cube_interval (n := x) (M := floorPower x) ho).mp rfl
  have h1 : 1 ≤ floorPower x := by
    by_contra h0
    have hy0 : floorPower x = 0 := by omega
    have h2 := hcell.2
    rw [hy0] at h2
    simp at h2
    have : x ^ 3 = 0 := by omega
    have : x = 0 := by
      by_contra hx0
      have : 1 ≤ x ^ 3 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 3 (by omega))
      omega
    omega
  have hfpR : (1 : ℝ) ≤ (floorPower x : ℝ) := by exact_mod_cast h1
  have hle : ((floorPower x : ℝ)) ^ 2 ≤ (x : ℝ) ^ 3 := by
    exact_mod_cast hcell.1
  have hlog := Real.log_le_log (by nlinarith) hle
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- Even step, lower side in image form: for even `x ≥ 441`,
`log T(x) ≥ (1/2)·log x − 1.2/T(x)`. -/
theorem log_floorPower_even_ge_sub {x : ℕ} (hx : 441 ≤ x) (he : x % 2 = 0) :
    Real.log x / 2 - 1.2 / (floorPower x : ℝ) ≤ Real.log (floorPower x) := by
  have hcell :=
    (floorPower_even_eq_iff_sq_interval (n := x) (M := floorPower x) he).mp rfl
  set y := floorPower x with hy
  have hy21 : 21 ≤ y := by
    by_contra hlt
    have h1 : (y + 1) ^ 2 ≤ 441 := by
      calc (y + 1) ^ 2 ≤ 21 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 441 := by norm_num
    exact absurd (lt_of_lt_of_le hcell.2 h1) (not_lt.mpr hx)
  have hub' : x ≤ y ^ 2 + 2 * y := by
    have h2 : (y + 1) ^ 2 = y ^ 2 + 2 * y + 1 := by ring
    have h3 : x < y ^ 2 + 2 * y + 1 := by rw [← h2]; exact hcell.2
    exact Nat.lt_succ_iff.mp h3
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hYpos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hY21 : (21 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy21
  have hle : ((y : ℝ)) ^ 2 ≤ (x : ℝ) := by exact_mod_cast hcell.1
  have hub : (x : ℝ) ≤ ((y : ℝ)) ^ 2 + 2 * y := by exact_mod_cast hub'
  set δ : ℝ := ((x : ℝ) - (y : ℝ) ^ 2) / x with hδdef
  have hδ0 : 0 ≤ δ := div_nonneg (by linarith) (le_of_lt hxpos)
  have hyy : 21 * (y : ℝ) ≤ (y : ℝ) ^ 2 := by nlinarith
  have hδ6 : δ ≤ 1 / 6 := by
    rw [hδdef, div_le_iff₀ hxpos]
    nlinarith
  have hδy : δ * y ≤ 2 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hxpos]
    nlinarith
  have h1δpos : 0 < 1 - δ := by linarith
  have hxy : ((y : ℝ)) ^ 2 = (x : ℝ) * (1 - δ) := by
    rw [hδdef]
    field_simp
    ring
  have hylog : 2 * Real.log y = Real.log x + Real.log (1 - δ) := by
    rw [show (2 : ℝ) * Real.log y = Real.log (((y : ℝ)) ^ 2) by
      rw [Real.log_pow]; push_cast; ring]
    rw [hxy, Real.log_mul (ne_of_gt hxpos) (ne_of_gt h1δpos)]
  have hneg := neg_log_one_sub_le_sixth hδ0 hδ6
  have h06 : 0.6 * δ ≤ 1.2 / (y : ℝ) := by
    rw [le_div_iff₀ hYpos]
    nlinarith
  linarith

/-- Odd step, lower side in image form: for odd `x ≥ 9`,
`log T(x) ≥ (3/2)·log x − 1.2/T(x)`. -/
theorem log_floorPower_odd_ge_sub {x : ℕ} (hx : 9 ≤ x) (ho : x % 2 = 1) :
    3 * Real.log x / 2 - 1.2 / (floorPower x : ℝ) ≤
      Real.log (floorPower x) := by
  have hcell :=
    (floorPower_odd_eq_iff_cube_interval (n := x) (M := floorPower x) ho).mp rfl
  set y := floorPower x with hy
  have hy27 : 27 ≤ y := by
    by_contra hlt
    have h1 : (y + 1) ^ 2 ≤ 729 := by
      calc (y + 1) ^ 2 ≤ 27 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 729 := by norm_num
    have h2 : 729 ≤ x ^ 3 := by
      calc (729 : ℕ) = 9 ^ 3 := by norm_num
        _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
    exact absurd (lt_of_lt_of_le hcell.2 h1) (not_lt.mpr h2)
  have hub' : x ^ 3 ≤ y ^ 2 + 2 * y := by
    have h2 : (y + 1) ^ 2 = y ^ 2 + 2 * y + 1 := by ring
    have h3 : x ^ 3 < y ^ 2 + 2 * y + 1 := by rw [← h2]; exact hcell.2
    exact Nat.lt_succ_iff.mp h3
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hXpos : (0 : ℝ) < (x : ℝ) ^ 3 := by positivity
  have hYpos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hY27 : (27 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy27
  have hle : ((y : ℝ)) ^ 2 ≤ (x : ℝ) ^ 3 := by exact_mod_cast hcell.1
  have hub : (x : ℝ) ^ 3 ≤ ((y : ℝ)) ^ 2 + 2 * y := by exact_mod_cast hub'
  set δ : ℝ := ((x : ℝ) ^ 3 - (y : ℝ) ^ 2) / (x : ℝ) ^ 3 with hδdef
  have hδ0 : 0 ≤ δ := div_nonneg (by linarith) (le_of_lt hXpos)
  have hyy : 27 * (y : ℝ) ≤ (y : ℝ) ^ 2 := by nlinarith
  have hδ6 : δ ≤ 1 / 6 := by
    rw [hδdef, div_le_iff₀ hXpos]
    nlinarith
  have hδy : δ * y ≤ 2 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hXpos]
    nlinarith
  have h1δpos : 0 < 1 - δ := by linarith
  have hxy : ((y : ℝ)) ^ 2 = (x : ℝ) ^ 3 * (1 - δ) := by
    rw [hδdef]
    field_simp
    ring
  have hylog : 2 * Real.log y = 3 * Real.log x + Real.log (1 - δ) := by
    rw [show (2 : ℝ) * Real.log y = Real.log (((y : ℝ)) ^ 2) by
      rw [Real.log_pow]; push_cast; ring]
    rw [hxy, Real.log_mul (ne_of_gt hXpos) (ne_of_gt h1δpos),
      Real.log_pow]
    push_cast
    ring
  have hneg := neg_log_one_sub_le_sixth hδ0 hδ6
  have h06 : 0.6 * δ ≤ 1.2 / (y : ℝ) := by
    rw [le_div_iff₀ hYpos]
    nlinarith
  linarith

/-!
## Upper invariant: the walk weight prices the amplification
-/

/-- On a minimum-based cycle, iterated logs never exceed the walk
weight times the base log: `log x_k ≤ w_k·log n`. -/
theorem cycleMin_log_le_weight {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∀ k, k ≤ w.length →
      Real.log (floorPower^[k] n) ≤ walkWeight w k * Real.log n := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk1
    have hk : k < w.length := hk1
    have hIH := ih (le_of_lt hk)
    have hiter : floorPower^[k + 1] n = floorPower (floorPower^[k] n) :=
      Function.iterate_succ_apply' floorPower k n
    set x := floorPower^[k] n with hxdef
    have hxge : n ≤ x := cycleMin_iterate_ge h k (le_of_lt hk)
    have hx1 : 1 ≤ x := by omega
    rw [hiter]
    cases hlet : w[k] with
    | odd =>
      have hxodd : x % 2 = 1 := follows_get_odd w h.1.1 k hk hlet
      have hstep := log_floorPower_odd_le hx1 hxodd
      rw [walkWeight_succ_odd hk hlet]
      calc Real.log (floorPower x) ≤ 3 * Real.log x / 2 := hstep
        _ ≤ 3 / 2 * (walkWeight w k * Real.log n) := by linarith
        _ = 3 / 2 * walkWeight w k * Real.log n := by ring
    | even =>
      have hxeven : x % 2 = 0 := follows_get_even w h.1.1 k hk hlet
      have hstep := log_floorPower_even_le hx1 hxeven
      rw [walkWeight_succ_even hk hlet]
      calc Real.log (floorPower x) ≤ Real.log x / 2 := hstep
        _ ≤ 1 / 2 * (walkWeight w k * Real.log n) := by linarith
        _ = walkWeight w k / 2 * Real.log n := by ring

/-!
## Charged lower invariant
-/

/-- Accumulated defect charge along the first `k` steps, priced at
the images: `C_k = Σ_{i<k} 1.2·log n/(x_{i+1}·log x_{i+1})`.
Depends only on the trajectory, not on the word. -/
noncomputable def prefixCharge (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => prefixCharge n k +
      1.2 * Real.log n /
        ((floorPower^[k + 1] n : ℝ) * Real.log (floorPower^[k + 1] n))

theorem prefixCharge_succ (n k : ℕ) :
    prefixCharge n (k + 1) = prefixCharge n k +
      1.2 * Real.log n /
        ((floorPower^[k + 1] n : ℝ) * Real.log (floorPower^[k + 1] n)) :=
  rfl

/-- Closed sum form of the prefix charge. -/
theorem prefixCharge_eq (n : ℕ) : ∀ k, prefixCharge n k =
    ∑ i ∈ Finset.range k, 1.2 * Real.log n /
      ((floorPower^[i + 1] n : ℝ) * Real.log (floorPower^[i + 1] n)) := by
  intro k
  induction k with
  | zero => simp [prefixCharge]
  | succ k ih => rw [Finset.sum_range_succ, ← ih, prefixCharge_succ]

/-- Charged transport invariant: `w_k·(log n − C_k) ≤ log x_k` with
the running defect charge. -/
theorem cycleMin_charge_prefix {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w) :
    ∀ k, k ≤ w.length →
      walkWeight w k * (Real.log n - prefixCharge n k) ≤
        Real.log (floorPower^[k] n) := by
  have hn2 : 2 ≤ n := by omega
  intro k
  induction k with
  | zero => intro _; simp [prefixCharge]
  | succ k ih =>
    intro hk1
    have hk : k < w.length := hk1
    have hIH := ih (le_of_lt hk)
    have hupper := cycleMin_log_le_weight hn2 h (k + 1) hk1
    have hiter : floorPower^[k + 1] n = floorPower (floorPower^[k] n) :=
      Function.iterate_succ_apply' floorPower k n
    set x := floorPower^[k] n with hxdef
    set z := floorPower^[k + 1] n with hzdef
    have hz : z = floorPower x := hiter
    have hxge : n ≤ x := cycleMin_iterate_ge h k (le_of_lt hk)
    have hzge : n ≤ z := cycleMin_iterate_ge h (k + 1) hk1
    have hzR : (400 : ℝ) ≤ (z : ℝ) := by
      exact_mod_cast le_trans hn hzge
    have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
    have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
    -- key comparison: the per-step loss `1.2/z` is dominated by the
    -- charge increment, priced through the upper invariant
    have hkey : 1.2 / (z : ℝ) ≤
        walkWeight w (k + 1) *
          (1.2 * Real.log n / ((z : ℝ) * Real.log z)) := by
      have h1 : 1.2 / (z : ℝ) =
          1.2 * Real.log z / ((z : ℝ) * Real.log z) := by
        rw [div_eq_div_iff (ne_of_gt hzpos)
          (ne_of_gt (mul_pos hzpos hlogz))]
        ring
      rw [h1, show walkWeight w (k + 1) *
          (1.2 * Real.log n / ((z : ℝ) * Real.log z)) =
          1.2 * (walkWeight w (k + 1) * Real.log n) /
            ((z : ℝ) * Real.log z) by ring]
      gcongr
    rw [prefixCharge_succ]
    cases hlet : w[k] with
    | odd =>
      have hxodd : x % 2 = 1 := follows_get_odd w h.1.1 k hk hlet
      have hstep : 3 * Real.log x / 2 - 1.2 / (z : ℝ) ≤ Real.log z := by
        rw [hz]
        exact log_floorPower_odd_ge_sub (by omega) hxodd
      have hWs : walkWeight w (k + 1) = 3 / 2 * walkWeight w k :=
        walkWeight_succ_odd hk hlet
      calc walkWeight w (k + 1) * (Real.log n - (prefixCharge n k +
              1.2 * Real.log n / ((z : ℝ) * Real.log z)))
          = 3 / 2 * (walkWeight w k * (Real.log n - prefixCharge n k)) -
              walkWeight w (k + 1) *
                (1.2 * Real.log n / ((z : ℝ) * Real.log z)) := by
            rw [hWs]; ring
        _ ≤ 3 / 2 * Real.log x - 1.2 / (z : ℝ) := by
            have h32 := mul_le_mul_of_nonneg_left hIH
              (by norm_num : (0 : ℝ) ≤ 3 / 2)
            linarith [hkey]
        _ ≤ Real.log z := by linarith [hstep]
    | even =>
      have hxeven : x % 2 = 0 := follows_get_even w h.1.1 k hk hlet
      have hxsq : n ^ 2 ≤ x := cycleMin_even_ge_sq hn2 h hk hxeven
      have hx441 : 441 ≤ x := by nlinarith
      have hstep : Real.log x / 2 - 1.2 / (z : ℝ) ≤ Real.log z := by
        rw [hz]
        exact log_floorPower_even_ge_sub hx441 hxeven
      have hWs : walkWeight w (k + 1) = walkWeight w k / 2 :=
        walkWeight_succ_even hk hlet
      calc walkWeight w (k + 1) * (Real.log n - (prefixCharge n k +
              1.2 * Real.log n / ((z : ℝ) * Real.log z)))
          = 1 / 2 * (walkWeight w k * (Real.log n - prefixCharge n k)) -
              walkWeight w (k + 1) *
                (1.2 * Real.log n / ((z : ℝ) * Real.log z)) := by
            rw [hWs]; ring
        _ ≤ Real.log x / 2 - 1.2 / (z : ℝ) := by
            have h12 := mul_le_mul_of_nonneg_left hIH
              (by norm_num : (0 : ℝ) ≤ 1 / 2)
            linarith [hkey]
        _ ≤ Real.log z := by linarith [hstep]

/-!
## The finance inequality and the kill criterion
-/

/-- **Defect-sum finance inequality** (the certified identity of
Paper A Theorem 4.6, Lean form): on a minimum-based cycle with
minimum `n ≥ 400`,

`1 − 2^L/3^o ≤ (6/5) · Σ_k 1/(x_k·log x_k)`. -/
theorem cycleMin_defect_finance {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w) :
    1 - (2 : ℝ) ^ w.length / 3 ^ oddCount w ≤
      1.2 * ∑ k ∈ Finset.range w.length,
        1 / ((floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n)) := by
  have hn2 : 2 ≤ n := by omega
  have hlogn : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  -- close the cycle
  have hend := cycleMin_charge_prefix hn h w.length le_rfl
  rw [cycle_iterate_period h.1] at hend
  -- reindex the charge: `Σ_{i<L} f(i+1) = Σ_{k<L} f(k)` via `x_L = x_0`
  set f : ℕ → ℝ := fun j => 1.2 * Real.log n /
    ((floorPower^[j] n : ℝ) * Real.log (floorPower^[j] n)) with hfdef
  have hf0 : f w.length = f 0 := by
    simp only [hfdef, cycle_iterate_period h.1, Function.iterate_zero_apply]
  have hshift : ∑ i ∈ Finset.range w.length, f (i + 1) =
      ∑ i ∈ Finset.range w.length, f i := by
    have h1 := Finset.sum_range_succ f w.length
    have h2 := Finset.sum_range_succ' f w.length
    rw [hf0] at h1
    linarith [h1, h2]
  have hcharge : prefixCharge n w.length =
      1.2 * Real.log n * ∑ k ∈ Finset.range w.length,
        1 / ((floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n)) := by
    rw [prefixCharge_eq]
    rw [show (∑ i ∈ Finset.range w.length, 1.2 * Real.log n /
        ((floorPower^[i + 1] n : ℝ) * Real.log (floorPower^[i + 1] n))) =
        ∑ i ∈ Finset.range w.length, f (i + 1) from rfl]
    rw [hshift, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfdef, mul_one_div]
  set S : ℝ := ∑ k ∈ Finset.range w.length,
    1 / ((floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n)) with hSdef
  set P : ℝ := (3 : ℝ) ^ oddCount w / 2 ^ w.length with hPdef
  have hWL : walkWeight w w.length = P := by
    rw [walkWeight, List.take_length, hPdef]
  have hP1 : 1 ≤ P := by
    rw [← hWL]
    exact one_le_walkWeight hn2 h le_rfl
  have hP0 : 0 < P := lt_of_lt_of_le one_pos hP1
  rw [hWL, hcharge] at hend
  -- hend : P * (log n − 1.2·log n·S) ≤ log n
  have h1 : P * (1 - 1.2 * S) ≤ 1 := by
    have hmul : (P * (1 - 1.2 * S)) * Real.log n ≤ 1 * Real.log n := by
      calc (P * (1 - 1.2 * S)) * Real.log n
          = P * (Real.log n - 1.2 * Real.log n * S) := by ring
        _ ≤ Real.log n := hend
        _ = 1 * Real.log n := by ring
    exact le_of_mul_le_mul_right hmul hlogn
  have hinv : (2 : ℝ) ^ w.length / 3 ^ oddCount w = 1 / P := by
    rw [hPdef, one_div_div]
  rw [hinv]
  -- from `P − 1.2·P·S ≤ 1` conclude `1 − 1/P ≤ 1.2·S`
  have h2 : (1 - 1 / P) * P ≤ (1.2 * S) * P := by
    have hexp : (1 - 1 / P) * P = P - 1 := by field_simp
    rw [hexp]
    nlinarith [h1]
  exact le_of_mul_le_mul_right h2 hP0

/-- **The walk-charge kill criterion** (Paper A Theorem 5.9
mechanism, Lean form): every minimum-based cycle at `n ≥ 400` with
positive reduced log-base `ν = log n − D` must satisfy

`1 − 2^L/3^o ≤ (6/5) · Σ_k g(hugWeight k)`

with the charge evaluated at the reduced base. The kill tables
verify the numeric failure of this inequality per surviving length;
that evaluation stays verified computation, the implication is
Lean. -/
theorem cycleMin_hug_kill_criterion {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w)
    (hν : 0 < Real.log n - transportDeficit n w) :
    1 - (2 : ℝ) ^ w.length / 3 ^ oddCount w ≤
      1.2 * ∑ k ∈ Finset.range w.length,
        stateCharge (Real.log n - transportDeficit n w) (hugWeight k) := by
  refine le_trans (cycleMin_defect_finance hn h) ?_
  have hchain := cycleMin_defect_le_hug_charge hn h hν
  linarith

end Problems.Juggler
