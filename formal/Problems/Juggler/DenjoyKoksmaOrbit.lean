/-
# Denjoy–Koksma: the orbit half

`DenjoyKoksma.lean` proves the analytic half and names what is missing: the *geometric* fact
that the rotation orbit `x, x+θ, …, x+(q−1)θ` visits each of the `q` cells once, which is
where `|θ − p/q| ≤ 1/q²` is used.  This file supplies it, and assembles the two halves into
the inequality Paper A's Theorem 5.7 quotes as KNOWN.

The naive form of the geometric fact is false.  With cells `[j/q, (j+1)/q)` anchored at `0`,
`q = 2`, `θ = 0.7`, `p = 1` and `x = 0.49`, both orbit points land in `[0, ½)`.  Two things
fix it: the cells must be anchored at `x`, and which way the cells are half-open must follow
the sign of `δ = θ − p/q`.  Writing `kθ = ⌊kp/q⌋ + (kp mod q)/q + kδ`, the point `k` sits at
the *left endpoint* of cell `kp mod q` displaced by `kδ`, and `|kδ| ≤ (q−1)/q² < 1/q` is less
than one cell width — so it stays in that cell when `δ ≥ 0` and falls into the previous one
when `δ ≤ 0`.  Hence `orbitCell`, which is `k·p mod q` shifted by `−1` in the negative case.
-/

import Problems.Juggler.DenjoyKoksma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open Set MeasureTheory intervalIntegral

namespace Problems.Juggler

/-- The cell the `k`-th orbit point lands in: `k·p mod q`, shifted back one when
`δ = θ − p/q` is negative. -/
def orbitCell (p q : ℕ) (neg : Bool) (k : ℕ) : ℕ :=
  if neg then (k * p + (q - 1)) % q else (k * p) % q

theorem orbitCell_lt {p q : ℕ} (hq : 0 < q) (neg : Bool) (k : ℕ) :
    orbitCell p q neg k < q := by
  unfold orbitCell
  split <;> exact Nat.mod_lt _ hq

/-- The cell map is injective on `range q`, because `p` is invertible mod `q`. -/
theorem orbitCell_inj {p q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime p q) {neg : Bool}
    {j k : ℕ} (hj : j < q) (hk : k < q) (h : orbitCell p q neg j = orbitCell p q neg k) :
    j = k := by
  have hmul : j * p % q = k * p % q := by
    unfold orbitCell at h
    cases neg with
    | false => simpa using h
    | true =>
      simp only [if_pos rfl] at h
      have := (Nat.ModEq.add_right_cancel' (q - 1) (h : Nat.ModEq q _ _))
      simpa [Nat.ModEq] using this
  have : j ≡ k [MOD q] := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.Coprime] using hcop.symm) hmul
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] using this

/-- **The orbit visits each cell once.**  With cells anchored at `x`, the `k`-th orbit point
lies in cell `orbitCell p q neg k`, once shifted by an integer. -/
theorem orbit_mem_cell {p q : ℕ} (hq : 0 < q) {θ δ x : ℝ} {neg : Bool}
    (hθ : θ = (p : ℝ) / q + δ) (hsmall : |δ| ≤ 1 / (q : ℝ) ^ 2)
    (hsign : if neg then δ ≤ 0 else 0 ≤ δ) {k : ℕ} (hk : k < q) :
    ∃ m : ℤ, x + k * θ + m ∈
      Icc (x + (orbitCell p q neg k : ℝ) / q) (x + ((orbitCell p q neg k : ℝ) + 1) / q) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  set d : ℕ := k * p / q with hd
  set r : ℕ := k * p % q with hr
  have hnat : q * d + r = k * p := by rw [hd, hr]; exact Nat.div_add_mod _ _
  have hprod : q * (d + 1) = q * d + q := by ring
  have hrlt : r < q := by rw [hr]; exact Nat.mod_lt _ hq
  have hdm : ((k : ℝ) * p) = q * d + r := by exact_mod_cast hnat.symm
  have hkp : (k : ℝ) * θ = d + r / q + k * δ := by
    rw [hθ]; field_simp; nlinarith [hdm]
  have hkq : (k : ℝ) ≤ q - 1 := by
    have : (k : ℝ) + 1 ≤ q := by exact_mod_cast hk
    linarith
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hdisp : |(k : ℝ) * δ| ≤ 1 / q := by
    rw [abs_mul, abs_of_nonneg hk0]
    have h1 : (k : ℝ) * |δ| ≤ ((q:ℝ) - 1) * (1 / (q:ℝ)^2) :=
      mul_le_mul hkq hsmall (abs_nonneg δ) (by linarith)
    have h2 : ((q:ℝ) - 1) * (1 / (q:ℝ)^2) ≤ 1 / q := by
      have hsq : (0:ℝ) < 1 / (q:ℝ)^2 := by positivity
      have hid : ((q:ℝ) - 1) * (1 / (q:ℝ)^2) = 1 / q - 1 / (q:ℝ)^2 := by
        field_simp
      rw [hid]; linarith
    linarith
  have hlo : -(1 / (q:ℝ)) ≤ (k:ℝ) * δ := (abs_le.mp hdisp).1
  have hhi : (k:ℝ) * δ ≤ 1 / q := (abs_le.mp hdisp).2
  cases neg with
  | false =>
    have hδ0 : 0 ≤ δ := by simpa using hsign
    have hpos : (0:ℝ) ≤ k * δ := mul_nonneg hk0 hδ0
    have hcell : orbitCell p q false k = r := by simp [orbitCell, hr]
    refine ⟨-d, ?_⟩
    rw [hcell]
    have hsplit : ((r:ℝ) + 1) / q = r / q + 1 / q := by ring
    constructor <;> push_cast <;> rw [hkp] <;> [linarith; (rw [hsplit]; linarith)]
  | true =>
    have hδ0 : δ ≤ 0 := by simpa using hsign
    have hnp : (k:ℝ) * δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0 hδ0
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · have h1 : k * p + (q - 1) = q * d + (q - 1) := by omega
      have hcell : orbitCell p q true k = q - 1 := by
        rw [orbitCell, if_pos rfl, h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have hqm : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
        have h1q : (1:ℕ) ≤ q := hq
        push_cast [Nat.cast_sub h1q]; ring
      have hr0R : (r : ℝ) = 0 := by exact_mod_cast hr0
      have hA : ((q:ℝ) - 1) / q = 1 - 1 / q := by field_simp
      have hB : ((q:ℝ) - 1 + 1) / q = 1 := by
        have hcancel : (q:ℝ) - 1 + 1 = q := by ring
        rw [hcancel]; field_simp
      refine ⟨-d + 1, ?_⟩
      rw [hcell]
      constructor <;> push_cast <;> rw [hkp, hqm, hr0R, zero_div] <;>
        [(rw [hA]; linarith); (rw [hB]; linarith)]
    · have h1 : k * p + (q - 1) = q * (d + 1) + (r - 1) := by omega
      have hcell : orbitCell p q true k = r - 1 := by
        rw [orbitCell, if_pos rfl, h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have hrm : ((r - 1 : ℕ) : ℝ) = (r:ℝ) - 1 := by
        push_cast [Nat.cast_sub hrpos]; ring
      have hA : ((r:ℝ) - 1) / q = r / q - 1 / q := by ring
      have hB : ((r:ℝ) - 1 + 1) / q = r / q := by ring
      refine ⟨-d, ?_⟩
      rw [hcell]
      constructor <;> push_cast <;> rw [hkp, hrm] <;>
        [(rw [hA]; linarith); (rw [hB]; linarith)]


/-- **Denjoy–Koksma with the cells reached through a map.**  The `n` sample points are indexed
by `k`, and `τ k` names the cell point `k` lands in; injectivity of `τ` on `range n` is what
replaces "one point per cell".  This is the form a rotation supplies, and taking it avoids
having to invert the permutation. -/
theorem denjoy_koksma_cellmap
    {f : ℝ → ℝ} {n : ℕ} {c : ℕ → ℝ} (hc : StrictMono c) (z : ℕ → ℝ) (τ : ℕ → ℕ)
    (hτlt : ∀ k < n, τ k < n)
    (hτinj : ∀ j < n, ∀ k < n, τ j = τ k → j = k)
    (hz : ∀ k < n, z k ∈ Icc (c (τ k)) (c (τ k + 1)))
    (hbv : ∀ i < n, BoundedVariationOn f (Icc (c i) (c (i + 1))))
    (hint : ∀ i < n, IntervalIntegrable f MeasureTheory.volume (c i) (c (i + 1))) :
    |∑ k ∈ Finset.range n, (c (τ k + 1) - c (τ k)) * f (z k) - ∫ t in (c 0)..(c n), f t|
      ≤ ∑ i ∈ Finset.range n,
          (c (i + 1) - c i) * (eVariationOn f (Icc (c i) (c (i + 1)))).toReal := by
  have hinj : ∀ j ∈ Finset.range n, ∀ k ∈ Finset.range n, τ j = τ k → j = k := by
    intro j hj k hk h
    exact hτinj j (Finset.mem_range.mp hj) k (Finset.mem_range.mp hk) h
  have himg : (Finset.range n).image τ = Finset.range n := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hτlt k (Finset.mem_range.mp hk))
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hre : ∀ g : ℕ → ℝ, ∑ k ∈ Finset.range n, g (τ k) = ∑ i ∈ Finset.range n, g i := by
    intro g
    conv_rhs => rw [← himg]
    rw [Finset.sum_image hinj]
  have hI : ∑ k ∈ Finset.range n, ∫ t in (c (τ k))..(c (τ k + 1)), f t
      = ∫ t in (c 0)..(c n), f t := by
    rw [hre fun i => ∫ t in (c i)..(c (i + 1)), f t]
    exact intervalIntegral.sum_integral_adjacent_intervals hint
  have hV : ∑ k ∈ Finset.range n,
      (c (τ k + 1) - c (τ k)) * (eVariationOn f (Icc (c (τ k)) (c (τ k + 1)))).toReal
      = ∑ i ∈ Finset.range n,
        (c (i + 1) - c i) * (eVariationOn f (Icc (c i) (c (i + 1)))).toReal :=
    hre fun i => (c (i + 1) - c i) * (eVariationOn f (Icc (c i) (c (i + 1)))).toReal
  rw [← hI, ← hV, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro k hk
  have hk' : k < n := Finset.mem_range.mp hk
  have hτk : τ k < n := hτlt k hk'
  have hlt : c (τ k) < c (τ k + 1) := hc (Nat.lt_succ_self _)
  have hba : (0:ℝ) < c (τ k + 1) - c (τ k) := by linarith
  have hcell := value_sub_mean_le_variation hlt (hbv _ hτk) (hz k hk') (hint _ hτk)
  have hfac : (c (τ k + 1) - c (τ k)) * f (z k) - ∫ t in (c (τ k))..(c (τ k + 1)), f t
      = (c (τ k + 1) - c (τ k)) *
        (f (z k) - (c (τ k + 1) - c (τ k))⁻¹ * ∫ t in (c (τ k))..(c (τ k + 1)), f t) := by
    field_simp
  rw [hfac, abs_mul, abs_of_pos hba]
  exact mul_le_mul_of_nonneg_left hcell hba.le

/-- **Denjoy–Koksma for the rotation.**  This is the inequality Paper A's Section 5.5 states
and marks KNOWN: for a one-periodic `f` of bounded variation and a rational `p/q` within
`1/q²` of `θ`, the ergodic sum of length `q` differs from `q` times the mean by at most the
total variation, uniformly in the starting phase `x`. -/
theorem denjoy_koksma_rotation
    {f : ℝ → ℝ} {p q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime p q)
    {θ x : ℝ} (hquality : |θ - (p : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (hper : Function.Periodic f 1)
    (hbv : BoundedVariationOn f (Icc x (x + 1)))
    (hint : IntervalIntegrable f MeasureTheory.volume x (x + 1)) :
    |∑ k ∈ Finset.range q, f (x + k * θ) - q * ∫ t in x..(x + 1), f t|
      ≤ (eVariationOn f (Icc x (x + 1))).toReal := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  set c : ℕ → ℝ := fun i => x + (i : ℝ) / q with hcdef
  have hc : StrictMono c := by
    intro i j hij
    simp only [hcdef]
    have : (i:ℝ) < j := by exact_mod_cast hij
    gcongr
  have hc0 : c 0 = x := by simp [hcdef]
  have hcq : c q = x + 1 := by simp only [hcdef]; rw [div_self (ne_of_gt hqR)]
  have hwidth : ∀ i : ℕ, c (i + 1) - c i = 1 / q := by
    intro i; simp only [hcdef]; push_cast; field_simp; ring
  have hsub : ∀ i < q, Icc (c i) (c (i + 1)) ⊆ Icc x (x + 1) := by
    intro i hi
    apply Icc_subset_Icc
    · have : (0:ℝ) ≤ (i:ℝ) / q := by positivity
      simp only [hcdef]; linarith
    · have hle : ((i:ℝ) + 1) / q ≤ 1 := by
        rw [div_le_one hqR]; exact_mod_cast hi
      simp only [hcdef]; push_cast; linarith
  have hbvcell : ∀ i < q, BoundedVariationOn f (Icc (c i) (c (i + 1))) := fun i hi =>
    hbv.mono (hsub i hi)
  have hintcell : ∀ i < q, IntervalIntegrable f MeasureTheory.volume (c i) (c (i + 1)) := by
    intro i hi
    refine hint.mono_set ?_
    rw [uIcc_of_le (hc (Nat.lt_succ_self i)).le, uIcc_of_le (by linarith : x ≤ x + 1)]
    exact hsub i hi
  -- the sign of `δ` decides which way the cells are half-open
  set δ : ℝ := θ - (p : ℝ) / q with hδdef
  have hθ : θ = (p : ℝ) / q + δ := by rw [hδdef]; ring
  have hsmall : |δ| ≤ 1 / (q : ℝ) ^ 2 := hquality
  obtain ⟨neg, hsign⟩ : ∃ neg : Bool, if neg then δ ≤ 0 else 0 ≤ δ := by
    rcases le_or_gt δ 0 with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h.le⟩
  set τ : ℕ → ℕ := orbitCell p q neg with hτdef
  -- the orbit points, shifted into the window
  have hex : ∀ k : ℕ, ∃ m : ℤ, k < q → x + k * θ + m ∈ Icc (c (τ k)) (c (τ k + 1)) := by
    intro k
    by_cases hk : k < q
    · obtain ⟨m, hm⟩ := orbit_mem_cell (x := x) hq hθ hsmall hsign hk
      refine ⟨m, fun _ => ?_⟩
      simpa [hcdef, hτdef] using hm
    · exact ⟨0, fun h => absurd h hk⟩
  choose m hm using hex
  set z : ℕ → ℝ := fun k => x + k * θ + m k with hzdef
  have hfz : ∀ k, f (z k) = f (x + k * θ) := by
    intro k
    have := hper.sub_int_mul_eq (x := x + k * θ) (-(m k))
    simpa [hzdef, sub_eq_add_neg] using this
  have hmain := denjoy_koksma_cellmap hc z τ
    (fun k _ => orbitCell_lt hq neg k)
    (fun j hj k hk h => orbitCell_inj hq hcop hj hk h)
    (fun k hk => hm k hk) hbvcell hintcell
  -- rewrite both sides into the paper's shape
  rw [hc0, hcq] at hmain
  have hL : ∑ k ∈ Finset.range q, (c (τ k + 1) - c (τ k)) * f (z k)
      = (1 / q) * ∑ k ∈ Finset.range q, f (x + k * θ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hwidth, hfz]
  have hcellfin : ∀ i ∈ Finset.range q, eVariationOn f (Icc (c i) (c (i + 1))) ≠ ⊤ :=
    fun i hi => hbvcell i (Finset.mem_range.mp hi)
  have hR : ∑ i ∈ Finset.range q,
      (c (i + 1) - c i) * (eVariationOn f (Icc (c i) (c (i + 1)))).toReal
      = (1 / q) * (eVariationOn f (Icc x (x + 1))).toReal := by
    have step : ∀ i ∈ Finset.range q,
        (c (i + 1) - c i) * (eVariationOn f (Icc (c i) (c (i + 1)))).toReal
        = (1 / q) * (eVariationOn f (Icc (c i) (c (i + 1)))).toReal :=
      fun i _ => by rw [hwidth]
    rw [Finset.sum_congr rfl step, ← Finset.mul_sum, ← ENNReal.toReal_sum hcellfin,
      sum_eVariationOn_Icc f c hc.monotone q, hc0, hcq]
  rw [hL, hR] at hmain
  have hqinv : (0:ℝ) < 1 / q := by positivity
  have hfac : (1 / (q:ℝ)) *
      (∑ k ∈ Finset.range q, f (x + k * θ) - q * ∫ t in x..(x + 1), f t)
      = (1 / q) * ∑ k ∈ Finset.range q, f (x + k * θ) - ∫ t in x..(x + 1), f t := by
    rw [mul_sub, ← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hqR), one_mul]
  rw [← hfac, abs_mul, abs_of_pos hqinv] at hmain
  exact le_of_mul_le_mul_left hmain hqinv

/-- **The mean over the window is the mean over `[0,1]`**, so this is Theorem 5.7's `C_*`:
the ergodic sum of length `q` differs from `q·C_*` by at most the variation. -/
theorem denjoy_koksma_rotation_mean
    {f : ℝ → ℝ} {p q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime p q)
    {θ x : ℝ} (hquality : |θ - (p : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (hper : Function.Periodic f 1)
    (hbv : BoundedVariationOn f (Icc x (x + 1)))
    (hint : IntervalIntegrable f MeasureTheory.volume x (x + 1)) :
    |∑ k ∈ Finset.range q, f (x + k * θ) - q * ∫ t in (0:ℝ)..1, f t|
      ≤ (eVariationOn f (Icc x (x + 1))).toReal := by
  have hshift : ∫ t in x..(x + 1), f t = ∫ t in (0:ℝ)..1, f t := by
    simpa using Function.Periodic.intervalIntegral_add_eq hper x 0
  rw [← hshift]
  exact denjoy_koksma_rotation hq hcop hquality hper hbv hint

end Problems.Juggler
