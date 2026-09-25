/-
# Paper B, Lemma 4.3: the near-integer sum (4.3)

`docs/theory/juggler_parity_discrepancy_note.md`, Lemma 4.3, second assertion. With
`E_R(t) = min(1, 1/(R‖t‖))`, `E_R = 1` at integers, and `X(n) = n^{3/2}`, the sum of
`E_R(X(n))` over the odd `n` of an interval is `O(P log(2R)/R + P^{5/6})`.

* `abs_block_arcError_le`, `abs_prefix_arcError_le`: the proof of Theorem 3.1
  (`PaperBSingleFloorBound`) for every arc, not only `[0, 1/2)`: at most `264 a^{5/6}` on a
  block `[a, a+M)`, `M ≤ a`, and `1056 R^{5/6}` on `[0, R)`;
* `nearCount_le`: the odd starts `2r+1`, `r ∈ [r₀, r₁)`, with `‖(2r+1)^{3/2}‖ < z` number at
  most `2 z (r₁ - r₀) + 6336 r₁^{5/6}`;
* `carryWeight_le_layers`: `E_R(t) ≤ ∑_{j ≤ J} 2^{1-j} [‖t‖ < 2^j/R]` when `2^J ≥ R`;
* `sum_carryWeight_le`: the bound (4.3) with explicit constants,
  `∑ E_R((2r+1)^{3/2}) ≤ 4 (r₁ - r₀)(log₂ R + 2)/R + 25344 r₁^{5/6}` over `r ∈ [r₀, r₁)`.

The first assertion of Lemma 4.3, `b(t) = b_R(t) + O(E_R(t))`, is not proved here.
-/

import Problems.Juggler.PaperBSingleFloorBound
import Problems.Juggler.PaperBOEThirdLetter

attribute [local instance] Classical.propDecidable

namespace Problems.Juggler

namespace PaperBCarryExpansion

open Finset Real
open BTCalculus.ErdosTuran BTCalculus.FejerArc
open PaperBSingleFloor

/-! ## Arc discrepancy of the odd-start phases -/

/-- **One block, every arc.** For `1 ≤ a` and `M ≤ a`, every arc of length at most one has
discrepancy at most `264 a^{5/6}` on the block `[a, a+M)` of odd-start parameters. -/
theorem abs_block_arcError_le (a M : ℕ) (ha : 1 ≤ a) (hM : M ≤ a) {α β : ℝ} (hαβ : α ≤ β)
    (hβ : β ≤ α + 1) :
    |arcError (fun n => oddPoint ((a : ℝ) + n)) M α β| ≤ 264 * (a : ℝ) ^ (5 / 6 : ℝ) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hMa : (M : ℝ) ≤ a := by exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
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
  have hu10 : 0 ≤ u ^ 10 := by positivity
  set H := ⌊u ^ 2⌋₊ with hHdef
  have hHle : (H : ℝ) ≤ u ^ 2 := Nat.floor_le (by positivity)
  have hHlt : u ^ 2 < H + 1 := Nat.lt_floor_add_one _
  by_cases hH : 3 ≤ H
  · let lam : ℕ → ℝ := fun h => (h : ℝ) * (3 / 2) / √(2 * ((a : ℝ) + M) + 1)
    let B : ℕ → ℝ := fun h => 8 * M * √(lam h) + 8 / √(lam h)
    have hB : ∀ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ range M, fourier (h : ℤ) (oddPoint ((a : ℝ) + n))‖ ≤ B h ∧
          ‖∑ n ∈ range M, fourier (-(h : ℤ)) (oddPoint ((a : ℝ) + n))‖ ≤ B h :=
      fun h hh => block_mode_bound ha1 hMa (Finset.mem_Icc.mp hh).1
    have het := abs_arcError_le_of_modes (fun n => oddPoint ((a : ℝ) + n)) M hH B hB hαβ hβ
    have hterm : ∀ h ∈ Finset.Icc 1 H, B h / h ≤ 32 * u ^ 9 * (1 / √(h : ℝ)) := by
      intro h hh
      have h1 : (1 : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
      obtain ⟨hlo, hhi⟩ := curvature_bounds ha1 hM0 hMa h1 hua
      have := mode_term_le h1 hu1 (hMa.trans_eq hua.symm) hlo hhi
      calc B h / h ≤ 32 * u ^ 9 / √h := this
        _ = 32 * u ^ 9 * (1 / √(h : ℝ)) := by ring
    have hsum : ∑ h ∈ Finset.Icc 1 H, B h / h ≤ 64 * u ^ 10 := by
      have hsH : √(H : ℝ) ≤ u := by
        rw [show u = √(u ^ 2) by rw [sqrt_sq hu0]]
        exact sqrt_le_sqrt hHle
      calc ∑ h ∈ Finset.Icc 1 H, B h / h
          ≤ ∑ h ∈ Finset.Icc 1 H, 32 * u ^ 9 * (1 / √(h : ℝ)) := sum_le_sum hterm
        _ = 32 * u ^ 9 * ∑ h ∈ Finset.Icc 1 H, 1 / √(h : ℝ) := by rw [mul_sum]
        _ ≤ 32 * u ^ 9 * (2 * √(H : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le H) (by positivity)
        _ ≤ 32 * u ^ 9 * (2 * u) := by gcongr
        _ = 64 * u ^ 10 := by ring
    have hmain : 8 * (M : ℝ) / ((H : ℝ) + 1) ≤ 8 * u ^ 10 := by
      rw [div_le_iff₀ (by positivity)]
      have : (M : ℝ) ≤ u ^ 10 * u ^ 2 := by
        rw [show u ^ 10 * u ^ 2 = u ^ 12 by ring]
        linarith
      nlinarith
    linarith
  · have hH2 : (H : ℝ) ≤ 2 := by exact_mod_cast (show H ≤ 2 by omega)
    have hu2 : u ^ 2 ≤ 3 := by linarith
    calc |arcError (fun n => oddPoint ((a : ℝ) + n)) M α β| ≤ M := abs_arcError_le _ _ hαβ hβ
      _ ≤ u ^ 12 := hMa.trans_eq hua.symm
      _ = u ^ 2 * u ^ 10 := by ring
      _ ≤ 3 * u ^ 10 := mul_le_mul_of_nonneg_right hu2 hu10
      _ ≤ 264 * u ^ 10 := by linarith

/-- Splitting the samples `[0, a+M)` at `a` splits the arc discrepancy. -/
theorem arcError_add (z : ℕ → UnitAddCircle) (a M : ℕ) (α β : ℝ) :
    arcError z (a + M) α β = arcError z a α β + arcError (fun n => z (a + n)) M α β := by
  simp only [arcError, sampleCount, sum_range_add]
  push_cast
  ring

/-- **Every prefix, every arc.** For `r < R`, every arc of length at most one has discrepancy
at most `1056 R^{5/6}`. -/
theorem abs_prefix_arcError_le (R : ℕ) {α β : ℝ} (hαβ : α ≤ β) (hβ : β ≤ α + 1) :
    |arcError (fun r : ℕ => oddPoint (r : ℝ)) R α β| ≤ 1056 * (R : ℝ) ^ (5 / 6 : ℝ) := by
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    rcases Nat.lt_or_ge R 2 with hR | hR
    · interval_cases R
      · simp [arcError, sampleCount]
      · have h := abs_arcError_le (fun r : ℕ => oddPoint (r : ℝ)) 1 hαβ hβ
        simp only [Nat.cast_one, one_rpow] at h ⊢
        linarith
    · set a := (R + 1) / 2 with hadef
      set M := R / 2 with hMdef
      have hsplit : a + M = R := by omega
      have ha : 1 ≤ a := by omega
      have hMa : M ≤ a := by omega
      have haR : a < R := by omega
      have h1 := ih a haR
      have h2 := abs_block_arcError_le a M ha hMa hαβ hβ
      have hshift : (fun n => (fun r : ℕ => oddPoint (r : ℝ)) (a + n)) =
          fun n : ℕ => oddPoint ((a : ℝ) + n) := by
        funext n
        push_cast
        rfl
      rw [← hsplit, arcError_add, hshift, hsplit]
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
      calc _ ≤ |arcError (fun r : ℕ => oddPoint (r : ℝ)) a α β| +
            |arcError (fun n : ℕ => oddPoint ((a : ℝ) + n)) M α β| := abs_add_le _ _
        _ ≤ 1056 * (a : ℝ) ^ (5 / 6 : ℝ) + 264 * (a : ℝ) ^ (5 / 6 : ℝ) := add_le_add h1 h2
        _ ≤ 1056 * (R : ℝ) ^ (5 / 6 : ℝ) := by linarith

/-! ## Counts on an interval of odd starts -/

/-- The number of `r ∈ [r₀, r₁)` whose phase `g(r)` lies in `S` modulo one. -/
noncomputable def intervalCount (r₀ r₁ : ℕ) (S : Set UnitAddCircle) : ℝ :=
  ∑ r ∈ Finset.Ico r₀ r₁, if oddPoint (r : ℝ) ∈ S then (1 : ℝ) else 0

/-- An interval count is a difference of two prefix counts. -/
theorem intervalCount_eq (r₀ r₁ : ℕ) (h : r₀ ≤ r₁) (S : Set UnitAddCircle) :
    intervalCount r₀ r₁ S =
      sampleCount (fun r : ℕ => oddPoint (r : ℝ)) r₁ S -
        sampleCount (fun r : ℕ => oddPoint (r : ℝ)) r₀ S := by
  rw [intervalCount, sampleCount, sampleCount, ← sum_range_add_sum_Ico _ h]
  ring

/-- **Every interval, every arc.** On `[r₀, r₁)` every arc of length at most one has
discrepancy at most `2112 r₁^{5/6}`. -/
theorem abs_intervalCount_sub_le (r₀ r₁ : ℕ) (h : r₀ ≤ r₁) {α β : ℝ} (hαβ : α ≤ β)
    (hβ : β ≤ α + 1) :
    |intervalCount r₀ r₁ (arc α β) - ((r₁ : ℝ) - r₀) * (β - α)| ≤
      2112 * (r₁ : ℝ) ^ (5 / 6 : ℝ) := by
  have h1 := abs_prefix_arcError_le r₁ hαβ hβ
  have h0 := abs_prefix_arcError_le r₀ hαβ hβ
  have hmono : (r₀ : ℝ) ^ (5 / 6 : ℝ) ≤ (r₁ : ℝ) ^ (5 / 6 : ℝ) :=
    rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (by norm_num)
  rw [intervalCount_eq r₀ r₁ h]
  rw [arcError] at h1 h0
  calc _ = |(sampleCount (fun r : ℕ => oddPoint (r : ℝ)) r₁ (arc α β) - r₁ * (β - α)) -
        (sampleCount (fun r : ℕ => oddPoint (r : ℝ)) r₀ (arc α β) - r₀ * (β - α))| := by
        ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ 2112 * (r₁ : ℝ) ^ (5 / 6 : ℝ) := by linarith

/-! ## Distance to the nearest integer -/

/-- `‖t‖`, the distance from `t` to the nearest integer. -/
noncomputable def nearestIntDist (t : ℝ) : ℝ := min (Int.fract t) (1 - Int.fract t)

/-- `E_R(t) = min(1, 1/(R‖t‖))`, with the value `1` at integers. -/
noncomputable def carryWeight (R : ℕ) (t : ℝ) : ℝ :=
  if (R : ℝ) * nearestIntDist t ≤ 1 then 1 else 1 / (R * nearestIntDist t)

/-- `0 ≤ ‖t‖ ≤ 1/2`. -/
theorem nearestIntDist_mem (t : ℝ) : 0 ≤ nearestIntDist t ∧ nearestIntDist t ≤ 1 / 2 := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  unfold nearestIntDist
  constructor
  · exact le_min h0 (by linarith)
  · rcases le_total (Int.fract t) (1 / 2) with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)

/-- The fractional part of `2g` in terms of that of `g`. -/
theorem fract_two_mul (g : ℝ) :
    Int.fract (2 * g) =
      if Int.fract g < 1 / 2 then 2 * Int.fract g else 2 * Int.fract g - 1 := by
  have h0 := Int.fract_nonneg g
  have h1 := Int.fract_lt_one g
  have hg : g = ⌊g⌋ + Int.fract g := (Int.floor_add_fract g).symm
  split_ifs with h
  · rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, 2 * ⌊g⌋, ?_⟩
    push_cast
    linarith
  · rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, 2 * ⌊g⌋ + 1, ?_⟩
    push_cast
    linarith

/-- A point `2g` within `z ≤ 1` of an integer puts `g` in one of three arcs of total length
`2z`: near `0`, near `1/2`, or near `1`, modulo one. -/
theorem near_mem_arcs {g z : ℝ} (hz1 : z ≤ 1) (h : nearestIntDist (2 * g) < z) :
    (g : UnitAddCircle) ∈ arc 0 (z / 2) ∨ (g : UnitAddCircle) ∈ arc (1 / 2 - z / 2) (1 / 2 + z / 2) ∨
      (g : UnitAddCircle) ∈ arc (1 - z / 2) 1 := by
  rw [PaperBOEThirdLetter.coe_mem_arc_iff_fract le_rfl (by linarith),
    PaperBOEThirdLetter.coe_mem_arc_iff_fract (by linarith) (by linarith),
    PaperBOEThirdLetter.coe_mem_arc_iff_fract (by linarith) le_rfl]
  have h0 := Int.fract_nonneg g
  have h1 := Int.fract_lt_one g
  unfold nearestIntDist at h
  rw [fract_two_mul] at h
  rw [min_lt_iff] at h
  split_ifs at h with hf
  · rcases h with h | h
    · left; constructor <;> linarith
    · right; left; constructor <;> linarith
  · rcases h with h | h
    · right; left; constructor <;> linarith
    · right; right; constructor <;> linarith

/-- **Near-integer count.** The odd starts `2r+1`, `r ∈ [r₀, r₁)`, with
`‖(2r+1)^{3/2}‖ < z` number at most `2 z (r₁ - r₀) + 6336 r₁^{5/6}`. -/
theorem nearCount_le (r₀ r₁ : ℕ) (h : r₀ ≤ r₁) {z : ℝ} (hz : 0 ≤ z) :
    ∑ r ∈ Finset.Ico r₀ r₁,
        (if nearestIntDist (2 * phaseG (r : ℝ)) < z then (1 : ℝ) else 0) ≤
      2 * z * ((r₁ : ℝ) - r₀) + 6336 * (r₁ : ℝ) ^ (5 / 6 : ℝ) := by
  have hr : (r₀ : ℝ) ≤ r₁ := by exact_mod_cast h
  have hp : 0 ≤ (r₁ : ℝ) ^ (5 / 6 : ℝ) := by positivity
  have htriv : ∑ r ∈ Finset.Ico r₀ r₁,
      (if nearestIntDist (2 * phaseG (r : ℝ)) < z then (1 : ℝ) else 0) ≤ (r₁ : ℝ) - r₀ := by
    calc _ ≤ ∑ _r ∈ Finset.Ico r₀ r₁, (1 : ℝ) := sum_le_sum (fun r _ => by split_ifs <;> norm_num)
      _ = (r₁ : ℝ) - r₀ := by simp [Nat.cast_sub h]
  rcases le_or_gt z 1 with hz1 | hz1
  · have hle : ∑ r ∈ Finset.Ico r₀ r₁,
        (if nearestIntDist (2 * phaseG (r : ℝ)) < z then (1 : ℝ) else 0) ≤
        intervalCount r₀ r₁ (arc 0 (z / 2)) +
          intervalCount r₀ r₁ (arc (1 / 2 - z / 2) (1 / 2 + z / 2)) +
          intervalCount r₀ r₁ (arc (1 - z / 2) 1) := by
      simp only [intervalCount, ← sum_add_distrib]
      apply sum_le_sum
      intro r _
      by_cases hn : nearestIntDist (2 * phaseG (r : ℝ)) < z
      · rw [if_pos hn]
        rcases near_mem_arcs hz1 hn with h1 | h1 | h1
        · rw [oddPoint, if_pos h1]
          split_ifs <;> norm_num
        · rw [oddPoint, if_pos h1]
          split_ifs <;> norm_num
        · rw [oddPoint, if_pos h1]
          split_ifs <;> norm_num
      · rw [if_neg hn]
        split_ifs <;> norm_num
    have e1 := abs_intervalCount_sub_le r₀ r₁ h (α := 0) (β := z / 2) (by linarith) (by linarith)
    have e2 := abs_intervalCount_sub_le r₀ r₁ h (α := 1 / 2 - z / 2) (β := 1 / 2 + z / 2)
      (by linarith) (by linarith)
    have e3 := abs_intervalCount_sub_le r₀ r₁ h (α := 1 - z / 2) (β := 1) (by linarith)
      (by linarith)
    have hd : 0 ≤ (r₁ : ℝ) - r₀ := by linarith
    have := (abs_le.mp e1).2
    have := (abs_le.mp e2).2
    have := (abs_le.mp e3).2
    nlinarith
  · have : (r₁ : ℝ) - r₀ ≤ 2 * z * ((r₁ : ℝ) - r₀) := by nlinarith
    linarith

/-! ## Layers and the sum (4.3) -/

/-- **Layer-cake bound.** For `R ≥ 1` and `2^J ≥ R`,
`E_R(t) ≤ ∑_{j ≤ J} 2^{1-j} [‖t‖ < 2^j/R]`. -/
theorem carryWeight_le_layers {R J : ℕ} (hR : 1 ≤ R) (hJ : R ≤ 2 ^ J) (t : ℝ) :
    carryWeight R t ≤
      ∑ j ∈ range (J + 1),
        (2 / (2 : ℝ) ^ j) * (if nearestIntDist t < (2 : ℝ) ^ j / R then 1 else 0) := by
  obtain ⟨hd0, hd1⟩ := nearestIntDist_mem t
  set d := nearestIntDist t with hd
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hex : ∃ j, d < (2 : ℝ) ^ j / R := by
    refine ⟨J + 1, ?_⟩
    rw [lt_div_iff₀ hR0]
    have : (R : ℝ) ≤ 2 ^ J := by exact_mod_cast hJ
    rw [pow_succ]
    nlinarith
  set m := Nat.find hex with hm
  have hmspec : d < (2 : ℝ) ^ m / R := Nat.find_spec hex
  have hmJ : m ≤ J := by
    apply Nat.find_min' hex
    rw [lt_div_iff₀ hR0]
    have : (R : ℝ) ≤ 2 ^ J := by exact_mod_cast hJ
    have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    nlinarith
  have hterms : ∀ j ∈ range (J + 1),
      0 ≤ (2 / (2 : ℝ) ^ j) * (if d < (2 : ℝ) ^ j / R then 1 else 0) := by
    intro j _
    split_ifs <;> positivity
  have hsingle := single_le_sum hterms (show m ∈ range (J + 1) by
    rw [mem_range]; omega)
  simp only [if_pos hmspec, mul_one] at hsingle
  refine le_trans ?_ hsingle
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  unfold carryWeight
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm0] at hmspec ⊢
    have : (R : ℝ) * d < 1 := by
      rw [pow_zero, lt_div_iff₀ hR0] at hmspec
      linarith
    rw [if_pos this.le]
    norm_num
  · have hmin : ¬ d < (2 : ℝ) ^ (m - 1) / R := Nat.find_min hex (by omega)
    have hge : (2 : ℝ) ^ (m - 1) ≤ R * d := by
      rw [not_lt, div_le_iff₀ hR0] at hmin
      linarith
    have hpow : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    split_ifs with hle
    · have h1 : (2 : ℝ) ^ (m - 1) ≤ 1 := hge.trans hle
      rw [hpow, le_div_iff₀ (by positivity)]
      linarith
    · have hpos : 0 < (R : ℝ) * d := by
        have : (1 : ℝ) ≤ 2 ^ (m - 1) := one_le_pow₀ (by norm_num)
        linarith
      rw [div_le_div_iff₀ hpos h2m, hpow]
      nlinarith

/-- `∑_{j ≤ J} 2/2^j ≤ 4`. -/
theorem sum_two_div_pow_le (J : ℕ) : ∑ j ∈ range (J + 1), (2 / (2 : ℝ) ^ j) ≤ 4 := by
  have h : ∀ n : ℕ, ∑ j ∈ range n, (2 / (2 : ℝ) ^ j) = 4 - 4 / 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, pow_succ]
      field_simp
      ring
  rw [h]
  have : 0 < 4 / (2 : ℝ) ^ (J + 1) := by positivity
  linarith

/-- **Lemma 4.3, the sum (4.3).** For `R ≥ 1` and `r₀ ≤ r₁`, over the odd starts
`n = 2r+1`, `r ∈ [r₀, r₁)`,
`∑ E_R(n^{3/2}) ≤ 4 (r₁ - r₀)(⌊log₂ R⌋ + 2)/R + 25344 r₁^{5/6}`. -/
theorem sum_carryWeight_le (R : ℕ) (hR : 1 ≤ R) (r₀ r₁ : ℕ) (h : r₀ ≤ r₁) :
    ∑ r ∈ Finset.Ico r₀ r₁, carryWeight R (2 * phaseG (r : ℝ)) ≤
      4 * ((r₁ : ℝ) - r₀) * (Nat.log 2 R + 2) / R + 25344 * (r₁ : ℝ) ^ (5 / 6 : ℝ) := by
  set J := Nat.log 2 R + 1 with hJdef
  have hJ : R ≤ 2 ^ J := (Nat.lt_pow_succ_log_self (by norm_num) R).le
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hd : 0 ≤ (r₁ : ℝ) - r₀ := by
    have : (r₀ : ℝ) ≤ r₁ := by exact_mod_cast h
    linarith
  have hp : 0 ≤ (r₁ : ℝ) ^ (5 / 6 : ℝ) := by positivity
  calc ∑ r ∈ Finset.Ico r₀ r₁, carryWeight R (2 * phaseG (r : ℝ))
      ≤ ∑ r ∈ Finset.Ico r₀ r₁, ∑ j ∈ range (J + 1), (2 / (2 : ℝ) ^ j) *
          (if nearestIntDist (2 * phaseG (r : ℝ)) < (2 : ℝ) ^ j / R then 1 else 0) :=
        sum_le_sum (fun r _ => carryWeight_le_layers hR hJ _)
    _ = ∑ j ∈ range (J + 1), (2 / (2 : ℝ) ^ j) * ∑ r ∈ Finset.Ico r₀ r₁,
          (if nearestIntDist (2 * phaseG (r : ℝ)) < (2 : ℝ) ^ j / R then (1 : ℝ) else 0) := by
        rw [sum_comm]
        simp_rw [mul_sum]
    _ ≤ ∑ j ∈ range (J + 1), (2 / (2 : ℝ) ^ j) *
          (2 * ((2 : ℝ) ^ j / R) * ((r₁ : ℝ) - r₀) + 6336 * (r₁ : ℝ) ^ (5 / 6 : ℝ)) :=
        sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (nearCount_le r₀ r₁ h (by positivity)) (by positivity))
    _ = ∑ j ∈ range (J + 1), (4 * ((r₁ : ℝ) - r₀) / R) +
          6336 * (r₁ : ℝ) ^ (5 / 6 : ℝ) * ∑ j ∈ range (J + 1), (2 / (2 : ℝ) ^ j) := by
        rw [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        have : (0 : ℝ) < 2 ^ j := by positivity
        field_simp
        ring
    _ ≤ (J + 1) * (4 * ((r₁ : ℝ) - r₀) / R) + 6336 * (r₁ : ℝ) ^ (5 / 6 : ℝ) * 4 := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        gcongr
        exact sum_two_div_pow_le J
    _ = 4 * ((r₁ : ℝ) - r₀) * (Nat.log 2 R + 2) / R + 25344 * (r₁ : ℝ) ^ (5 / 6 : ℝ) := by
        rw [hJdef]
        push_cast
        ring

end PaperBCarryExpansion

end Problems.Juggler
