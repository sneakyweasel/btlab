import Problems.Collatz.FibreUnitComparison

/-! # Subcritical periodic weights and the loss at a fixed integer

A normalized finite weight with `L h ≥ q h` gives the complete lower
bound `C_d(a) ≥ q^d h(a)`. A family with `q → 1` forces divergence at
one fixed root if its values there stay above a fixed multiple of `1-q`.
The required family is an explicit open premise, not a finite-certificate result.
-/

noncomputable section

namespace Problems.Collatz.FibreMinorants

open Finset FibreMass FibreActual FibreUnitComparison Filter
open scoped Classical Topology

private theorem project_residue (r a : ℕ) :
    project r 1 (residue (r+1) a) = residue r a := by
  apply Fin.ext
  exact Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 3 (by omega : r ≤ r+1))

/-- A normalized nonnegative finite periodic weight satisfying the complete
subcritical inequality gives an all-depth lower bound at every positive
integer. All exponents are included; the rate and weight are hypotheses. -/
theorem coarse_geometric_lower (plus : Bool) (r : ℕ) (h : Level r → ℝ)
    (hh : ∀ b, 0 ≤ h b) (h1 : ∀ b, h b ≤ 1) {q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ b : Level (r+1), q * h (project r 1 b) ≤ transfer plus r h b)
    (d : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    q^d * h (residue r a) ≤ coarse plus d a := by
  induction d generalizing a with
  | zero => simpa [coarse, iterate] using h1 (residue r a)
  | succ d ih =>
      have hc := iterate_nonneg plus 1 (fun _ => by norm_num : ∀ _ : Level 1, (0:ℝ) ≤ 1) d
      have hs := hstep (residue (r+1) a)
      rw [project_residue] at hs
      calc
        q^(d+1) * h (residue r a) = q^d * (q*h (residue r a)) := by rw [pow_succ]; ring
        _ ≤ q^d * transfer plus r h (residue (r+1) a) :=
          mul_le_mul_of_nonneg_left hs (pow_nonneg hq d)
        _ = ∑' k, q^d * row plus r k h (residue (r+1) a) := by
          rw [transfer, tsum_mul_left]
        _ ≤ ∑' k, row plus (1+d) k (iterate plus 1 (fun _ => 1) d)
            (residue (1+d+1) a) := by
          apply Summable.tsum_le_tsum _
            ((row_summable plus r hh _).mul_left (q^d)) (row_summable plus (1+d) hc _)
          intro k
          rw [row_eq_branchWeight plus r k h ha, row_eq_branchWeight plus (1+d) k _ ha]
          unfold branchWeight
          split_ifs with had
          · have ht := mul_le_mul_of_nonneg_left (ih (child_pos plus k ha had))
              (show 0 ≤ coefficient k by unfold coefficient; positivity)
            simpa only [coarse, mul_assoc, mul_comm, mul_left_comm] using ht
          · simp
        _ = coarse plus (d+1) a := rfl

private theorem not_summable_of_geometric_minorants {f q : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hlim : Tendsto q atTop (𝓝 1))
    (hminor : ∀ i d, c*(1-q i)*(q i)^d ≤ f d) : ¬Summable f := by
  intro hs
  have htail (D i : ℕ) : c*(q i)^D ≤ ∑' n, f (n+D) := by
    have hg := summable_geometric_of_lt_one (hq0 i) (hq1 i)
    have hsum := Summable.tsum_le_tsum (fun n => hminor i (n+D))
      (((summable_nat_add_iff D).mpr hg).mul_left (c*(1-q i)))
      ((summable_nat_add_iff D).mpr hs)
    have he : (∑' n, c*(1-q i)*(q i)^(n+D)) = c*(q i)^D := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one (hq0 i) (hq1 i)]
      have hne : 1 - q i ≠ 0 := ne_of_gt (sub_pos.mpr (hq1 i))
      field_simp [hne]
    rwa [he] at hsum
  have hle (D : ℕ) : c ≤ ∑' n, f (n+D) := by
    have ht : Tendsto (fun i => c*(q i)^D) atTop (𝓝 c) := by
      simpa using tendsto_const_nhds.mul (hlim.pow D)
    exact le_of_tendsto ht (Eventually.of_forall (htail D))
  have hz : c ≤ 0 := ge_of_tendsto (tendsto_sum_nat_add f) (Eventually.of_forall hle)
  linarith

/-- A family of actual periodic subcritical weights forces coefficient
divergence at one fixed positive integer if its rates tend to one and its
normalized weight at that integer is at least `c*(1-rate)`, for one `c>0`.
No such limiting family is supplied by this theorem or by finitely many checks. -/
theorem coarse_not_summable_of_weights (plus : Bool) {a : ℕ} (ha : 1 ≤ a)
    (r : ℕ → ℕ) (h : (i : ℕ) → Level (r i) → ℝ) (q : ℕ → ℝ)
    (hh : ∀ i b, 0 ≤ h i b) (h1 : ∀ i b, h i b ≤ 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hlim : Tendsto q atTop (𝓝 1))
    (hstep : ∀ i (b : Level (r i+1)),
      q i * h i (project (r i) 1 b) ≤ transfer plus (r i) (h i) b)
    {c : ℝ} (hc : 0 < c)
    (hanchor : ∀ i, c*(1-q i) ≤ h i (residue (r i) a)) :
    ¬Summable (fun d => coarse plus d a) := by
  apply not_summable_of_geometric_minorants hc hq0 hq1 hlim
  intro i d
  calc
    c*(1-q i)*(q i)^d ≤ h i (residue (r i) a)*(q i)^d :=
      mul_le_mul_of_nonneg_right (hanchor i) (pow_nonneg (hq0 i) d)
    _ ≤ coarse plus d a := by
      simpa only [mul_comm] using coarse_geometric_lower plus (r i) (h i)
        (hh i) (h1 i) (hq0 i) (hstep i) d ha

end Problems.Collatz.FibreMinorants
