import Problems.Juggler.PaperERecurrence
import BTCalculus.PowerBoxCounting

/-! # Counting and residue corollaries of Paper E Theorem 4.1

All word lengths and moduli are fixed before the parameter tends to infinity.
The counted starts belong to the explicit perfect-power family.
-/

namespace Problems.Juggler.PaperECorollaries

noncomputable section

open Finset Filter
open scoped Topology
open BTCalculus.FourierBoxCounting BTCalculus.PowerBoxCounting
open PaperEModularReturn PaperERecurrence CollatzBridge

/-- A prescribed residue at every root depth, including the exit. -/
def SignatureBox (a b M : ℕ) (r : Fin (b + 1) → ℕ) (t : ℕ) : Prop :=
  ∀ j, (r j : ℝ) / (2 * M) ≤ Int.fract (powerValue (1 + 2 * M * t) a j.val / (2 * M)) ∧
    Int.fract (powerValue (1 + 2 * M * t) a j.val / (2 * M)) < ((r j : ℝ) + 1) / (2 * M)

/-- Every prescribed residue vector has the product frequency. -/
theorem signature_density (a b M : ℕ) (hM : 0 < M) (r : Fin (b + 1) → ℕ)
    (hr : ∀ j, r j < 2 * M) :
    Tendsto (fun N => (count (SignatureBox a b M r) N : ℝ) / N) atTop
      (𝓝 ((1 / (2 * (M : ℝ))) ^ (b + 1))) := by
  have hm : (0 : ℝ) < 2 * M := by positivity
  have h := tendsto_power_fract_box_count
    (fun j : Fin (b + 1) => (3 ^ a : ℝ) / 2 ^ (j.val + 1))
    (fun _ => 1 / (2 * (M : ℝ))) (power_exponent_injective a b)
    (fun j => power_exponent_noninteger a j.val) (fun _ => by positivity) hm 1
    (fun j => (r j : ℝ) / (2 * M)) (fun j => ((r j : ℝ) + 1) / (2 * M))
    (fun _ => by positivity)
    (fun j => (div_le_one hm).2 (by exact_mod_cast (by have := hr j; omega : r j + 1 ≤ 2 * M)))
    (fun j => div_lt_div_of_pos_right (by linarith) hm)
  have hp : (∏ j : Fin (b + 1), (((r j : ℝ) + 1) / (2 * M) - (r j : ℝ) / (2 * M))) =
      (1 / (2 * (M : ℝ))) ^ (b + 1) := by
    simp_rw [← sub_div, add_sub_cancel_left]
    simp
  rw [hp] at h
  have hs (t : ℕ) : (2 : ℝ) * M * t + 1 = ((1 + 2 * M * t : ℕ) : ℝ) := by
    push_cast
    ring
  simp_rw [hs, one_div_mul_eq_div] at h
  change Tendsto (fun N => (count (fun t => ∀ j : Fin (b + 1),
    (r j : ℝ) / (2 * M) ≤ Int.fract (powerValue (1 + 2 * M * t) a j.val / (2 * M)) ∧
    Int.fract (powerValue (1 + 2 * M * t) a j.val / (2 * M)) <
      ((r j : ℝ) + 1) / (2 * M)) N : ℝ) / N) _ _
  simpa only [powerValue] using h

/-- Signature parameters beyond the common expansion threshold. -/
def SignatureParameter (a b M : ℕ) (r : Fin (b + 1) → ℕ) (t : ℕ) : Prop :=
  SignatureBox a b M r t ∧ 2 ^ (2 ^ (b + 1)) ≤ 1 + 2 * M * t

/-- The threshold removes finitely many parameters and preserves signature density. -/
theorem signature_parameter_density (a b M : ℕ) (hM : 0 < M)
    (r : Fin (b + 1) → ℕ) (hr : ∀ j, r j < 2 * M) :
    Tendsto (fun N => (count (SignatureParameter a b M r) N : ℝ) / N) atTop
      (𝓝 ((1 / (2 * (M : ℝ))) ^ (b + 1))) := by
  apply density_congr_eventually _ (signature_density a b M hM r hr)
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ (b + 1)))] with t ht
  have hs : 2 ^ (2 ^ (b + 1)) ≤ 1 + 2 * M * t := by nlinarith
  simp only [SignatureParameter, hs, and_true]

/-- The signature box is an assertion about exact integer roots. -/
theorem signature_roots {a b M t : ℕ} (hM : 0 < M) (r : Fin (b + 1) → ℕ)
    (hr : ∀ j, r j < 2 * M) (h : SignatureBox a b M r t) (j : Fin (b + 1)) :
    (Nat.sqrt^[j.val + 1] ((1 + 2 * M * t) ^ (3 ^ a))) % (2 * M) = r j := by
  rw [power_root_eq_floor]
  apply floor_mod_of_box (by positivity) (by omega) (hr j)
  · simpa only [powerValue, Nat.cast_mul, Nat.cast_ofNat] using (h j).1
  · simpa only [powerValue, Nat.cast_mul, Nat.cast_ofNat] using (h j).2

/-- Prescribed even residues give genuine modular returns and every intermediate residue. -/
theorem modular_return_of_signature {k b M t : ℕ} (hM : 0 < M)
    (hex : 2 ^ (k + 1 + b) < 3 ^ (k + 1))
    (hsize : 2 ^ (2 ^ (b + 1)) ≤ 1 + 2 * M * t)
    (r : Fin (b + 1) → ℕ) (hr : ∀ j, r j < 2 * M)
    (heven : ∀ j : Fin (b + 1), j.val < b → r j % 2 = 0)
    (hexit : r (Fin.last b) = 1) (hbox : SignatureBox (k + 1) b M r t) :
    let n := (1 + 2 * M * t) ^ (2 ^ k)
    ModularReturn (k + 1) b M n ∧
      ∀ j : Fin (b + 1), (floorPower^[k + 1 + j.val] n) % (2 * M) = r j := by
  have hs : (1 + 2 * M * t) % 2 = 1 := by simp [Nat.add_mod, Nat.mul_mod]
  have hm := signature_roots hM r hr hbox
  have hg : ∀ j < b, (Nat.sqrt^[j + 1] ((1 + 2 * M * t) ^ (3 ^ (k + 1)))) % 2 = 0 := by
    intro j hj
    have hj' := congrArg (fun n => n % 2) (hm ⟨j, by omega⟩)
    rw [Nat.mod_mod_of_dvd _ (by omega : 2 ∣ 2 * M)] at hj'
    exact hj'.trans (heven ⟨j, by omega⟩ hj)
  obtain ⟨hi, hend⟩ := actual_run hs hg
  have hex' : 2 ^ k * 2 ^ (b + 1) < 3 ^ (k + 1) := by
    rwa [← pow_add, show k + (b + 1) = k + 1 + b by omega]
  have hgt := root_endpoint_gt hsize hex'
  rw [← hend] at hgt
  have hsM : (1 + 2 * M * t) % (2 * M) = 1 := by
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · refine ⟨by simp [Nat.pow_mod, hs], hi, run_above_start hi hgt.le, hgt, ?_, ?_⟩
    · simp [Nat.pow_mod, hsM, Nat.mod_eq_of_lt (show 1 < 2 * M by omega)]
    · rw [hend]
      simpa only [Fin.val_last, hexit] using hm (Fin.last b)
  · intro j
    have hj := (actual_run (b := j.val) hs (fun i hi => hg i (by omega))).2
    rw [hj]
    exact hm j

/-- Every admissible residue signature occurs at arbitrarily large genuine returns. -/
theorem signature_returns_infinite {a b M : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hex : 2 ^ (a + b) < 3 ^ a) (r : Fin (b + 1) → ℕ)
    (hr : ∀ j, r j < 2 * M)
    (heven : ∀ j : Fin (b + 1), j.val < b → r j % 2 = 0)
    (hexit : r (Fin.last b) = 1) (B : ℕ) :
    {n : ℕ | B < n ∧ ModularReturn a b M n ∧
      ∀ j : Fin (b + 1), (floorPower^[a + j.val] n) % (2 * M) = r j}.Infinite := by
  cases a with
  | zero => omega
  | succ k =>
    apply Set.infinite_iff_exists_gt.mpr
    intro C
    obtain ⟨t, ht, hbox⟩ := exists_ge_of_density (by positivity)
      (signature_density (k + 1) b M hM r hr)
      (max (2 ^ (2 ^ (b + 1))) (max (B + 1) (C + 1)))
    have hts : t ≤ 1 + 2 * M * t := by nlinarith
    have hsn : 1 + 2 * M * t ≤ (1 + 2 * M * t) ^ (2 ^ k) :=
      Nat.le_self_pow (by positivity) _
    have hsize : 2 ^ (2 ^ (b + 1)) ≤ 1 + 2 * M * t := by omega
    have hreturn := modular_return_of_signature hM hex hsize r hr heven hexit hbox
    refine ⟨(1 + 2 * M * t) ^ (2 ^ k), ⟨by omega, hreturn⟩, by omega⟩

/-- The original return box has its exact positive parameter density. -/
theorem return_density (a b M : ℕ) (hM : 0 < M) :
    Tendsto (fun N => (count (ReturnBox a b M) N : ℝ) / N) atTop
      (𝓝 (1 / ((2 : ℝ) ^ (b + 1) * M))) := by
  classical
  have hm : (0 : ℝ) < 2 * M := by positivity
  let p : Fin (b + 1) → ℝ := fun j => (3 ^ a : ℝ) / 2 ^ (j.val + 1)
  let w : Fin (b + 1) → ℝ := fun j => if j.val = b then 1 / (2 * M) else 1 / 2
  let lo : Fin (b + 1) → ℝ := fun j => if j.val = b then 1 / (2 * M) else 0
  let hi : Fin (b + 1) → ℝ := fun j => if j.val = b then 2 / (2 * M) else 1 / 2
  have hlo : ∀ j, 0 ≤ lo j := by intro j; dsimp [lo]; split_ifs <;> positivity
  have hhi : ∀ j, hi j ≤ 1 := by
    intro j
    dsimp [hi]
    split_ifs
    · exact (div_le_one hm).2 (by exact_mod_cast (by omega : 2 ≤ 2 * M))
    · norm_num
  have hbox : ∀ j, lo j < hi j := by
    intro j
    dsimp [lo, hi]
    split_ifs
    · exact div_lt_div_of_pos_right (by norm_num) hm
    · norm_num
  have h := tendsto_power_fract_box_count p w (power_exponent_injective a b)
    (fun j => power_exponent_noninteger a j.val)
    (fun j => by dsimp only [w]; split_ifs <;> positivity) hm 1 lo hi hlo hhi hbox
  have hp : (∏ j : Fin (b + 1), (hi j - lo j)) = 1 / ((2 : ℝ) ^ (b + 1) * M) := by
    rw [Fin.prod_univ_castSucc]
    have he (j : Fin b) : hi j.castSucc - lo j.castSucc = (1 / 2 : ℝ) := by
      simp [hi, lo, ne_of_lt j.isLt]
    simp_rw [he]
    simp only [hi, lo, Fin.val_last, ↓reduceIte, Fin.prod_const]
    rw [← sub_div]
    norm_num
    rw [pow_succ]
    field_simp
    simp
  rw [hp] at h
  have hs (t : ℕ) : (2 : ℝ) * M * t + 1 = ((1 + 2 * M * t : ℕ) : ℝ) := by
    push_cast
    ring
  have he : (fun t : ℕ => ∀ j, lo j ≤ Int.fract (w j * (2 * M * (t : ℝ) + 1) ^ p j) ∧
      Int.fract (w j * (2 * M * (t : ℝ) + 1) ^ p j) < hi j) = ReturnBox a b M := by
    funext t
    apply propext
    simp_rw [hs]
    constructor
    · intro ht
      have hl := ht (Fin.last b)
      simp only [lo, hi, w, p, Fin.val_last, ↓reduceIte, one_div_mul_eq_div] at hl
      refine ⟨hl.1, hl.2, ?_⟩
      intro j hj
      have hh := (ht ⟨j, by omega⟩).2
      simpa only [hi, w, p, if_neg (ne_of_lt hj), one_div_mul_eq_div, powerValue] using hh
    · rintro ⟨hl, hh, he⟩ j
      by_cases hj : j.val = b
      · simpa only [lo, hi, w, p, if_pos hj, hj, one_div_mul_eq_div, powerValue] using And.intro hl hh
      · have hjb : j.val < b := by omega
        simpa only [lo, hi, w, p, if_neg hj, one_div_mul_eq_div, powerValue] using
          And.intro (Int.fract_nonneg (powerValue (1 + 2 * M * t) a j.val / 2)) (he j.val hjb)
  simpa only [he] using h

/-- Retain only parameters beyond the proved expansion threshold. -/
def ReturnParameter (a b M t : ℕ) : Prop :=
  ReturnBox a b M t ∧ 2 ^ (2 ^ (b + 1)) ≤ 1 + 2 * M * t

theorem return_parameter_density (a b M : ℕ) (hM : 0 < M) :
    Tendsto (fun N => (count (ReturnParameter a b M) N : ℝ) / N) atTop
      (𝓝 (1 / ((2 : ℝ) ^ (b + 1) * M))) := by
  apply density_congr_eventually _ (return_density a b M hM)
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ (b + 1)))] with t ht
  have hs : 2 ^ (2 ^ (b + 1)) ≤ 1 + 2 * M * t := by nlinarith
  simp only [ReturnParameter, hs, and_true]

/-- The finite set counted in Corollary 4.2, at a physical start cutoff X. -/
def returnStarts (a b M : ℕ) (X : ℝ) : Finset ℕ :=
  powerStarts (ReturnParameter a b M) (2 * M) (2 ^ (a - 1)) X

/-- Every counted start has the actual expanding, non-descending modular return. -/
theorem returnStarts_actual {a b M n : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hex : 2 ^ (a + b) < 3 ^ a) {X : ℝ} (hX : 1 ≤ X)
    (hn : n ∈ returnStarts a b M X) : (n : ℝ) ≤ X ∧ ModularReturn a b M n := by
  obtain ⟨hnX, t, ht, rfl⟩ := (mem_powerStarts (by positivity) (by positivity) hX).1 hn
  refine ⟨hnX, ?_⟩
  cases a with
  | zero => omega
  | succ k =>
    simpa only [Nat.add_sub_cancel, ModularReturn] using modular_return_of_box hM hex ht.2 ht.1

/-- Corollary 4.2: the explicit sparse family has its exact leading constant. -/
theorem return_starts_asymptotic (a b M : ℕ) (hM : 0 < M) :
    Tendsto (fun X : ℝ => ((returnStarts a b M X).card : ℝ) /
      X ^ ((2 ^ (a - 1) : ℕ) : ℝ)⁻¹) atTop
        (𝓝 (1 / ((2 : ℝ) ^ (b + 2) * (M : ℝ) ^ 2))) := by
  have h := tendsto_powerStarts_card (by positivity : 0 < 2 * M)
    (by positivity : 0 < 2 ^ (a - 1)) (return_parameter_density a b M hM)
  have he : (1 / ((2 : ℝ) ^ (b + 1) * M)) / (2 * M) =
      1 / ((2 : ℝ) ^ (b + 2) * (M : ℝ) ^ 2) := by
    rw [show b + 2 = (b + 1) + 1 by omega, pow_succ]
    ring
  simpa only [Nat.cast_mul, Nat.cast_ofNat, he, returnStarts] using h

/-- The constructed returns occur in every sufficiently large fixed relative interval. -/
theorem return_in_multiplicative_interval {a b M : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hex : 2 ^ (a + b) < 3 ^ a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∃ n : ℕ, X < n ∧ (n : ℝ) ≤ (1 + ε) * X ∧
      ModularReturn a b M n := by
  have h := eventually_powerStarts_interval (by positivity : 0 < 2 * M)
    (by positivity : 0 < 2 ^ (a - 1)) (by positivity)
    (show 1 < 1 + ε by linarith) (return_parameter_density a b M hM)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X h hX
  obtain ⟨n, hn, hXn⟩ := h
  have hcX : 1 ≤ (1 + ε) * X := by nlinarith
  have hn' := returnStarts_actual ha hM hex hcX hn
  exact ⟨n, hXn, hn'.1, hn'.2⟩

end
end Problems.Juggler.PaperECorollaries
