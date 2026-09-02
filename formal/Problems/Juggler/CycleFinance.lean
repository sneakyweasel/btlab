import Problems.Juggler.CycleCore
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Problems.Juggler

/-!
# Cycle finance inequality (Paper A Theorem 4.4 / Corollary 4.4c)

A cycle itinerary is formally expanding (`2^L < 3^o`) yet returns
exactly, so the multiplicative surplus must be financed by the
floor defects, which are relatively `O(1/x)` in logarithms. The
whole-cycle log unroll gives, for any `CycleMin` start `n`,

`n * log n * (3^o - 2^L) <= L * 3^o`

(`cycleMin_finance`, Theorem 4.4, constant 1), and the inv-sum
form keeps each remainder as `1/x_i`
(`cycleMin_finance_inv_sum`, Corollary 4.4c). This file is the
dyadic-cell majorant core only: the envelope induction
(`cycleMin_log_envelope`, `cycleMin_log_envelope_inv`) spends
one dyadic-cell logarithm bound (`log_le_two_log_add`,
`log(1+u) <= u`) and one prefix non-contraction fact
(`cycleMin_prefix_pow_le`, `CycleCore.lean`) per step.

The length census driven by this inequality — residual floors
`53`/`257`/`261`, the excluded lengths `9`–`83`, the
leftover `84` or `>= 85`, and the Eliahou packaging — lives in
`CycleFinanceLeftovers.lean`; the walk layer (Section 5) imports
this file only. The image-form `6/5` defect majorant of
Theorem 4.6 is `DefectFinance.lean`: two majorants, two paper
theorems, not one inequality.

Dossier: `docs/problems/juggler_cycle_finance.md`. Writeup:
Paper A (`docs/theory/juggler_finite_dynamics_note.md`)
Section 4. This is not a halt theorem.
-/

/-- The dyadic-cell logarithm bound: if `z < (y+1)^2` then
`log z ≤ 2 log y + 2/y`. The only analytic input of the finance
inequality (`log(1+u) ≤ u`). -/
theorem log_le_two_log_add {z y : ℕ} (hz : 1 ≤ z) (hy : 1 ≤ y)
    (hcell : z < (y + 1) ^ 2) :
    Real.log z ≤ 2 * Real.log y + 2 / y := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  have hcast : (z : ℝ) ≤ ((y : ℝ) + 1) ^ 2 := by
    have hle : (z : ℕ) ≤ (y + 1) ^ 2 := hcell.le
    exact_mod_cast hle
  have h1 : Real.log z ≤ 2 * Real.log ((y : ℝ) + 1) := by
    have hmono : Real.log z ≤ Real.log (((y : ℝ) + 1) ^ 2) := by
      gcongr
    rw [Real.log_pow] at hmono
    simpa using hmono
  have hsplit : Real.log (((y : ℝ) + 1) / y) =
      Real.log ((y : ℝ) + 1) - Real.log y :=
    Real.log_div (by positivity) (ne_of_gt hy0)
  have hbound : Real.log (((y : ℝ) + 1) / y) ≤ ((y : ℝ) + 1) / y - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hfrac : ((y : ℝ) + 1) / y - 1 = 1 / y := by
    field_simp
    ring
  have h2 : Real.log ((y : ℝ) + 1) ≤ Real.log y + 1 / y := by
    rw [hsplit] at hbound
    rw [hfrac] at hbound
    linarith
  have h3 : 2 * Real.log ((y : ℝ) + 1) ≤ 2 * Real.log y + 2 / y := by
    have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * Real.log ((y : ℝ) + 1) ≤ 2 * (Real.log y + 1 / y) := this
      _ = 2 * Real.log y + 2 / y := by ring
  linarith

/-- Even step: `log x ≤ 2 log T(x) + 2/T(x)`. -/
theorem log_step_even {x : ℕ} (hx : 2 ≤ x) (he : x % 2 = 0) :
    Real.log x ≤ 2 * Real.log (floorPower x) + 2 / (floorPower x) := by
  have hy : 1 ≤ floorPower x := floorPower_pos (by omega)
  have hcell :=
    (floorPower_even_eq_iff_sq_interval (n := x) (M := floorPower x) he).mp rfl
  exact log_le_two_log_add (by omega) hy hcell.2

/-- Odd step: `3 log x ≤ 2 log T(x) + 2/T(x)`. -/
theorem log_step_odd {x : ℕ} (hx : 2 ≤ x) (ho : x % 2 = 1) :
    3 * Real.log x ≤ 2 * Real.log (floorPower x) + 2 / (floorPower x) := by
  have hy : 1 ≤ floorPower x := floorPower_pos (by omega)
  have hcell :=
    (floorPower_odd_eq_iff_cube_interval (n := x) (M := floorPower x) ho).mp rfl
  have hz : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h := log_le_two_log_add hz hy hcell.2
  have hcast : ((x ^ 3 : ℕ) : ℝ) = ((x : ℝ)) ^ 3 := by push_cast; ring
  rw [hcast, Real.log_pow] at h
  simpa using h

/-- The unrolled financing envelope along a `CycleMin` prefix:
`3^{o_k} log n ≤ 2^k log x_k + k 3^{o_k} / n`. Division-free
induction; each step spends one dyadic-cell logarithm bound and one
prefix non-contraction fact. -/
theorem cycleMin_log_envelope {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∀ k, k ≤ w.length →
      (3 : ℝ) ^ oddCount (w.take k) * Real.log n ≤
        (2 : ℝ) ^ k * Real.log (floorPower^[k] n) +
          (k : ℝ) * (3 : ℝ) ^ oddCount (w.take k) / n := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk1
    have hk : k < w.length := Nat.lt_of_succ_le hk1
    have ihk := ih (Nat.le_of_lt hk)
    have htake : w.take (k + 1) = w.take k ++ [w[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      rfl
    have hx2 : 2 ≤ floorPower^[k] n := cycleItinerary_iterate_ge_two hn h.1 hk
    have hiter : floorPower^[k + 1] n = floorPower (floorPower^[k] n) :=
      Function.iterate_succ_apply' floorPower k n
    have hxk1 : n ≤ floorPower^[k + 1] n := cycleMin_iterate_ge h (k + 1) hk1
    have hpow : 2 ^ (k + 1) ≤ 3 ^ oddCount (w.take (k + 1)) :=
      cycleMin_prefix_pow_le hn h (k + 1) hk1
    have hn0 : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hx1pos : (0 : ℝ) < (floorPower^[k + 1] n : ℝ) := by
      have : 0 < floorPower^[k + 1] n := by omega
      exact_mod_cast this
    have hdiv : (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ) ≤
        (3 : ℝ) ^ oddCount (w.take (k + 1)) / n := by
      rw [div_le_div_iff₀ hx1pos hn0]
      have hmul : (2 : ℕ) ^ (k + 1) * n ≤
          3 ^ oddCount (w.take (k + 1)) * floorPower^[k + 1] n :=
        Nat.mul_le_mul hpow hxk1
      exact_mod_cast hmul
    have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    cases hb : w[k] with
    | even =>
      have hpar : (floorPower^[k] n) % 2 = 0 :=
        follows_get_even w h.1.1 k hk hb
      have hstep := log_step_even hx2 hpar
      rw [← hiter] at hstep
      have hodd : oddCount (w.take (k + 1)) = oddCount (w.take k) := by
        rw [htake, hb, oddCount_append]
        simp
      rw [hodd] at hdiv ⊢
      have hs2 := mul_le_mul_of_nonneg_left hstep h2k
      have hexpand : (2 : ℝ) ^ k *
          (2 * Real.log (floorPower^[k + 1] n) +
            2 / (floorPower^[k + 1] n : ℝ)) =
          (2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
            (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ) := by
        rw [pow_succ]; ring
      rw [hexpand] at hs2
      push_cast
      calc (3 : ℝ) ^ oddCount (List.take k w) * Real.log n
          ≤ (2 : ℝ) ^ k * Real.log (floorPower^[k] n) +
              (k : ℝ) * (3 : ℝ) ^ oddCount (List.take k w) / n := ihk
        _ ≤ ((2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ)) +
              (k : ℝ) * (3 : ℝ) ^ oddCount (List.take k w) / n :=
            add_le_add_left hs2 _
        _ ≤ ((2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              (3 : ℝ) ^ oddCount (List.take k w) / n) +
              (k : ℝ) * (3 : ℝ) ^ oddCount (List.take k w) / n := by
            gcongr
        _ = (2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              ((k : ℝ) + 1) * (3 : ℝ) ^ oddCount (List.take k w) / n := by
            ring
    | odd =>
      have hpar : (floorPower^[k] n) % 2 = 1 :=
        follows_get_odd w h.1.1 k hk hb
      have hstep := log_step_odd hx2 hpar
      rw [← hiter] at hstep
      have hodd : oddCount (w.take (k + 1)) = oddCount (w.take k) + 1 := by
        rw [htake, hb, oddCount_append]
        simp
      rw [hodd] at hdiv ⊢
      have hs2 := mul_le_mul_of_nonneg_left hstep h2k
      have hexpand : (2 : ℝ) ^ k *
          (2 * Real.log (floorPower^[k + 1] n) +
            2 / (floorPower^[k + 1] n : ℝ)) =
          (2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
            (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ) := by
        rw [pow_succ]; ring
      rw [hexpand] at hs2
      have ihk3 := mul_le_mul_of_nonneg_left ihk (by norm_num : (0 : ℝ) ≤ 3)
      have hpow_succ : (3 : ℝ) ^ (oddCount (w.take k) + 1) =
          3 * (3 : ℝ) ^ oddCount (w.take k) := by
        rw [pow_succ]; ring
      rw [hpow_succ] at hdiv ⊢
      push_cast
      calc (3 : ℝ) * (3 : ℝ) ^ oddCount (List.take k w) * Real.log n
          = 3 * ((3 : ℝ) ^ oddCount (List.take k w) * Real.log n) := by ring
        _ ≤ 3 * ((2 : ℝ) ^ k * Real.log (floorPower^[k] n) +
              (k : ℝ) * (3 : ℝ) ^ oddCount (List.take k w) / n) := ihk3
        _ = (2 : ℝ) ^ k * (3 * Real.log (floorPower^[k] n)) +
              (k : ℝ) * (3 * (3 : ℝ) ^ oddCount (List.take k w)) / n := by
            ring
        _ ≤ ((2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ)) +
              (k : ℝ) * (3 * (3 : ℝ) ^ oddCount (List.take k w)) / n :=
            add_le_add_left hs2 _
        _ ≤ ((2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              3 * (3 : ℝ) ^ oddCount (List.take k w) / n) +
              (k : ℝ) * (3 * (3 : ℝ) ^ oddCount (List.take k w)) / n := by
            gcongr
        _ = (2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              ((k : ℝ) + 1) * (3 * (3 : ℝ) ^ oddCount (List.take k w)) / n := by
            ring

/-- **Cycle finance inequality.** For any cycle taken at its
minimum: `n log n (3^o - 2^L) ≤ L 3^o`. -/
theorem cycleMin_finance {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    (n : ℝ) * Real.log n *
        ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w := by
  have henv := cycleMin_log_envelope hn h w.length le_rfl
  rw [List.take_length, cycle_iterate_period h.1] at henv
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hstep : ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) * Real.log n ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w / n := by linarith
  have hmul := mul_le_mul_of_nonneg_left hstep hn0.le
  calc (n : ℝ) * Real.log n *
      ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length)
      = (n : ℝ) * (((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) *
          Real.log n) := by ring
    _ ≤ (n : ℝ) * ((w.length : ℝ) * (3 : ℝ) ^ oddCount w / n) := hmul
    _ = (w.length : ℝ) * (3 : ℝ) ^ oddCount w := by
        field_simp

/-- On a `CycleMin`, every iterate through one period is at least
two (the start is, and later states are at least the start). -/
theorem cycleMin_iterate_ge_two {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hk : k ≤ w.length) :
    2 ≤ floorPower^[k] n := by
  rcases lt_or_eq_of_le hk with hlt | rfl
  · exact cycleItinerary_iterate_ge_two hn h.1 hlt
  · rw [cycle_iterate_period h.1]
    exact hn

/-- Inv-sum envelope: each dyadic-cell defect is kept as `1/x_{i+1}`
instead of being replaced by `1/n`. At `k = L` this is
`(3^o - 2^L) log n ≤ 3^o ∑ 1/x_i`. Paper A Corollary 4.4c. -/
theorem cycleMin_log_envelope_inv {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∀ k, k ≤ w.length →
      (3 : ℝ) ^ oddCount (w.take k) * Real.log n ≤
        (2 : ℝ) ^ k * Real.log (floorPower^[k] n) +
          (3 : ℝ) ^ oddCount (w.take k) *
            ∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk1
    have hk : k < w.length := Nat.lt_of_succ_le hk1
    have ihk := ih (Nat.le_of_lt hk)
    have htake : w.take (k + 1) = w.take k ++ [w[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      rfl
    have hx2 : 2 ≤ floorPower^[k] n := cycleMin_iterate_ge_two hn h (Nat.le_of_lt hk)
    have hx21 : 2 ≤ floorPower^[k + 1] n := cycleMin_iterate_ge_two hn h hk1
    have hiter : floorPower^[k + 1] n = floorPower (floorPower^[k] n) :=
      Function.iterate_succ_apply' floorPower k n
    have hpow : 2 ^ (k + 1) ≤ 3 ^ oddCount (w.take (k + 1)) :=
      cycleMin_prefix_pow_le hn h (k + 1) hk1
    have hx1pos : (0 : ℝ) < (floorPower^[k + 1] n : ℝ) := by
      have : 0 < floorPower^[k + 1] n := by omega
      exact_mod_cast this
    have h2le3 : (2 : ℝ) ^ (k + 1) ≤ (3 : ℝ) ^ oddCount (w.take (k + 1)) := by
      exact_mod_cast hpow
    have hsum : ∑ i ∈ Finset.range (k + 1), (1 : ℝ) / (floorPower^[i + 1] n) =
        (∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n)) +
          1 / (floorPower^[k + 1] n) :=
      Finset.sum_range_succ (fun i => (1 : ℝ) / (floorPower^[i + 1] n)) k
    have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    cases hb : w[k] with
    | even =>
      have hpar : (floorPower^[k] n) % 2 = 0 :=
        follows_get_even w h.1.1 k hk hb
      have hstep := log_step_even hx2 hpar
      rw [← hiter] at hstep
      have hodd : oddCount (w.take (k + 1)) = oddCount (w.take k) := by
        rw [htake, hb, oddCount_append]
        simp
      rw [hodd] at h2le3 ⊢
      have hs2 := mul_le_mul_of_nonneg_left hstep h2k
      have hexpand : (2 : ℝ) ^ k *
          (2 * Real.log (floorPower^[k + 1] n) +
            2 / (floorPower^[k + 1] n : ℝ)) =
          (2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
            (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ) := by
        rw [pow_succ]; ring
      rw [hexpand] at hs2
      have hdef :
          (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ) ≤
            (3 : ℝ) ^ oddCount (w.take k) / (floorPower^[k + 1] n : ℝ) := by
        exact div_le_div_of_nonneg_right h2le3 hx1pos.le
      rw [hsum]
      push_cast
      calc (3 : ℝ) ^ oddCount (List.take k w) * Real.log n
          ≤ (2 : ℝ) ^ k * Real.log (floorPower^[k] n) +
              (3 : ℝ) ^ oddCount (List.take k w) *
                ∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n) := ihk
        _ ≤ ((2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ)) +
              (3 : ℝ) ^ oddCount (List.take k w) *
                ∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n) :=
            add_le_add_left hs2 _
        _ ≤ ((2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              (3 : ℝ) ^ oddCount (List.take k w) /
                (floorPower^[k + 1] n : ℝ)) +
              (3 : ℝ) ^ oddCount (List.take k w) *
                ∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n) := by
            gcongr
        _ = (2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              (3 : ℝ) ^ oddCount (List.take k w) *
                ((∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n)) +
                  1 / (floorPower^[k + 1] n)) := by
            ring
    | odd =>
      have hpar : (floorPower^[k] n) % 2 = 1 :=
        follows_get_odd w h.1.1 k hk hb
      have hstep := log_step_odd hx2 hpar
      rw [← hiter] at hstep
      have hodd : oddCount (w.take (k + 1)) = oddCount (w.take k) + 1 := by
        rw [htake, hb, oddCount_append]
        simp
      rw [hodd] at h2le3 ⊢
      have hs2 := mul_le_mul_of_nonneg_left hstep h2k
      have hexpand : (2 : ℝ) ^ k *
          (2 * Real.log (floorPower^[k + 1] n) +
            2 / (floorPower^[k + 1] n : ℝ)) =
          (2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
            (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ) := by
        rw [pow_succ]; ring
      rw [hexpand] at hs2
      have ihk3 := mul_le_mul_of_nonneg_left ihk (by norm_num : (0 : ℝ) ≤ 3)
      have hpow_succ : (3 : ℝ) ^ (oddCount (w.take k) + 1) =
          3 * (3 : ℝ) ^ oddCount (w.take k) := by
        rw [pow_succ]; ring
      rw [hpow_succ] at h2le3 ⊢
      have hdef :
          (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ) ≤
            3 * (3 : ℝ) ^ oddCount (w.take k) /
              (floorPower^[k + 1] n : ℝ) :=
        div_le_div_of_nonneg_right h2le3 hx1pos.le
      rw [hsum]
      push_cast
      calc (3 : ℝ) * (3 : ℝ) ^ oddCount (List.take k w) * Real.log n
          = 3 * ((3 : ℝ) ^ oddCount (List.take k w) * Real.log n) := by ring
        _ ≤ 3 * ((2 : ℝ) ^ k * Real.log (floorPower^[k] n) +
              (3 : ℝ) ^ oddCount (List.take k w) *
                ∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n)) := ihk3
        _ = (2 : ℝ) ^ k * (3 * Real.log (floorPower^[k] n)) +
              3 * (3 : ℝ) ^ oddCount (List.take k w) *
                ∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n) := by
            ring
        _ ≤ ((2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              (2 : ℝ) ^ (k + 1) / (floorPower^[k + 1] n : ℝ)) +
              3 * (3 : ℝ) ^ oddCount (List.take k w) *
                ∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n) :=
            add_le_add_left hs2 _
        _ ≤ ((2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              3 * (3 : ℝ) ^ oddCount (List.take k w) /
                (floorPower^[k + 1] n : ℝ)) +
              3 * (3 : ℝ) ^ oddCount (List.take k w) *
                ∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n) := by
            gcongr
        _ = (2 : ℝ) ^ (k + 1) * Real.log (floorPower^[k + 1] n) +
              3 * (3 : ℝ) ^ oddCount (List.take k w) *
                ((∑ i ∈ Finset.range k, (1 : ℝ) / (floorPower^[i + 1] n)) +
                  1 / (floorPower^[k + 1] n)) := by
            ring

/-- **Inv-sum finance inequality.** Same cell-log defects as
`cycleMin_finance`, remainders kept as `1/x_{i+1}`.
`(3^o - 2^L) log n ≤ 3^o ∑ 1/x_i`. -/
theorem cycleMin_finance_inv_sum {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) * Real.log n ≤
      (3 : ℝ) ^ oddCount w *
        ∑ i ∈ Finset.range w.length, (1 : ℝ) / (floorPower^[i + 1] n) := by
  have henv := cycleMin_log_envelope_inv hn h w.length le_rfl
  rw [List.take_length, cycle_iterate_period h.1] at henv
  linarith


end Problems.Juggler

