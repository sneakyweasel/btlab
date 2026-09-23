import Problems.Collatz.FibreActual

/-! # Bounded stopping cannot repair uniform inverse-fibre reproduction

The envelope includes every positive halving exponent and permits a separate
stopping decision at every node. A forced first step followed by any common
finite stopping budget still has a deficient unit residue, for either sign.
The conclusion concerns homogeneous coefficients; unbounded stopping and
coefficient-series divergence at a fixed integer remain open.
-/

noncomputable section

namespace Problems.Collatz.FibreStopping

open Finset FibreMass FibreActual
open scoped Classical

/-- The largest homogeneous terminal reward with at most `d` inverse steps,
including the option to stop immediately. The terminal weight is periodic. -/
def envelope (plus : Bool) (r : ℕ) (h : Level r → ℝ) :
    (d : ℕ) → Level (r+d) → ℝ
  | 0 => h
  | d+1 => fun a => max (h (project r (d+1) a))
      (transfer plus (r+d) (envelope plus r h d) a)

private theorem envelope_nonneg (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (d : ℕ) (a : Level (r+d)) :
    0 ≤ envelope plus r h d a := by
  cases d with
  | zero => exact hh a
  | succ d => exact (hh _).trans (le_max_left _ _)

private theorem base_le_envelope (plus : Bool) (r : ℕ) (h : Level r → ℝ)
    (d m : ℕ) : h (residue r m) ≤ envelope plus r h d (residue (r+d) m) := by
  cases d with
  | zero => exact le_rfl
  | succ d => simpa only [envelope, project_residue] using
      (le_max_left (h (project r (d+1) (residue (r+(d+1)) m)))
        (transfer plus (r+d) (envelope plus r h d) (residue (r+(d+1)) m)))

private theorem envelope_zero (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    {h : Level r → ℝ} (hz : ∀ b, b.val % 3 = 0 → h b = 0)
    (d : ℕ) (a : Level (r+d)) (ha : a.val % 3 = 0) :
    envelope plus r h d a = 0 := by
  cases d with
  | zero => exact hz a ha
  | succ d => simp only [envelope, hz _ (project_nonunit hr _ a ha),
      transfer_zero plus (r+d) _ a ha, max_self]

private theorem transfer_compare (plus : Bool) {r t : ℕ}
    {h : Level r → ℝ} {g : Level t → ℝ}
    (hh : ∀ b, 0 ≤ h b) (hg : ∀ b, 0 ≤ g b)
    (hle : ∀ n, 1 ≤ n → h (residue r n) ≤ g (residue t n))
    {m : ℕ} (hm : 1 ≤ m) :
    transfer plus r h (residue (r+1) m) ≤
      transfer plus t g (residue (t+1) m) := by
  apply Summable.tsum_le_tsum _ (row_summable plus r hh _) (row_summable plus t hg _)
  intro k
  rw [row_eq_branchWeight plus r k h hm, row_eq_branchWeight plus t k g hm]
  apply mul_le_mul_of_nonneg_left _ (by unfold coefficient; positivity)
  unfold branchWeight
  split_ifs with ha
  · exact hle _ (child_pos plus k hm ha)
  · exact le_rfl

private theorem envelope_mono (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (d m : ℕ) (hm : 1 ≤ m) :
    envelope plus r h d (residue (r+d) m) ≤
      envelope plus r h (d+1) (residue (r+(d+1)) m) := by
  induction d generalizing m with
  | zero => exact base_le_envelope plus r h 1 m
  | succ d ih =>
      simp only [envelope, project_residue]
      apply max_le_max le_rfl
      exact transfer_compare plus (envelope_nonneg plus r hh d)
        (envelope_nonneg plus r hh (d+1)) (fun n hn => ih n hn) hm

private theorem residue_representative (r : ℕ) (a : Level r) :
    residue r (a.val+3^r) = a := by
  apply Fin.ext
  simp [residue, Nat.mod_eq_of_lt a.isLt]

/-- Even the optimal bounded stopping envelope has a deficient forced-first-step
unit residue. The horizon and periodic terminal weight are arbitrary; positivity
is needed only at the repeated one-halving residue. -/
theorem bounded_stopping_deficit (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    {h : Level r → ℝ} (hh : ∀ b, 0 ≤ h b)
    (hz : ∀ b, b.val % 3 = 0 → h b = 0) (hs : 0 < h (spike plus r))
    (d : ℕ) : ∃ a : Level (r+d+1), a.val % 3 ≠ 0 ∧
      transfer plus (r+d) (envelope plus r h d) a < h (project r (d+1) a) := by
  have hsp : 0 < envelope plus r h d (spike plus (r+d)) := by
    cases d with
    | zero => exact hs
    | succ d =>
        apply lt_of_lt_of_le hs
        simpa only [envelope, project_spike plus hr] using
          (le_max_left (h (project r (d+1) (spike plus (r+(d+1)))))
            (transfer plus (r+d) (envelope plus r h d) (spike plus (r+(d+1)))))
  obtain ⟨a, ha, hdef⟩ := exists_deficit plus (show 1 ≤ r+d by omega)
    (envelope_nonneg plus r hh d) (envelope_zero plus hr hz d) hsp (by omega : 1 ≤ 1)
  refine ⟨a, ha, ?_⟩
  change transfer plus (r+d) (envelope plus r h d) a <
    envelope plus r h d (project (r+d) 1 a) at hdef
  let m := a.val+3^(r+d+1)
  have hm : 1 ≤ m := by
    dsimp [m]
    have : 0 < 3^(r+d+1) := by positivity
    omega
  have ham : residue (r+d+1) m = a := residue_representative _ a
  have hproj : project (r+d) 1 a = residue (r+d) m := by
    rw [← ham, project_residue]
  have hbase : project r (d+1) a = residue r m := by
    rw [← ham]
    exact project_residue r (d+1) m
  rw [hproj, ← ham] at hdef
  rw [hbase, ← ham]
  cases d with
  | zero => exact hdef
  | succ d =>
      have hmono := transfer_compare plus (envelope_nonneg plus r hh d)
        (envelope_nonneg plus r hh (d+1))
        (fun n hn => envelope_mono plus r hh d n hn) hm
      simp only [envelope, project_residue] at hdef
      exact (lt_max_iff.mp hdef).resolve_right (not_lt_of_ge hmono)

/-- A bounded inverse-tree policy may stop at once or choose a different
remaining policy for every positive halving exponent, hence for every branch. -/
inductive Policy : ℕ → Type
  | stop (d : ℕ) : Policy d
  | expand {d : ℕ} (children : ℕ → Policy d) : Policy (d+1)

/-- Complete homogeneous payoff using algebraic integer children. At a positive
odd target these are exactly the actual odd-return predecessors. Inadmissible
branches have zero weight; no exponent is truncated. -/
def payoff (plus : Bool) (r : ℕ) (h : Level r → ℝ) : {d : ℕ} → Policy d → ℕ → ℝ
  | _, .stop _, m => h (residue r m)
  | _, .expand children, m => ∑' k, if Admissible plus k m then
      coefficient k * payoff plus r h (children k) (child plus k m) else 0

/-- Every branch-dependent policy is bounded by the finite-level envelope.
The proof also establishes nonnegativity and convergence of every branch sum. -/
theorem payoff_bounds (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) {d : ℕ} (policy : Policy d) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ payoff plus r h policy m ∧
      payoff plus r h policy m ≤ envelope plus r h d (residue (r+d) m) := by
  induction policy generalizing m with
  | stop d => exact ⟨hh _, base_le_envelope plus r h d m⟩
  | @expand d children ih =>
      have hnn (k : ℕ) : 0 ≤ if Admissible plus k m then
          coefficient k * payoff plus r h (children k) (child plus k m) else 0 := by
        split_ifs with ha
        · exact mul_nonneg (by unfold coefficient; positivity)
            (ih k (child_pos plus k hm ha)).1
        · exact le_rfl
      have hle (k : ℕ) : (if Admissible plus k m then
          coefficient k * payoff plus r h (children k) (child plus k m) else 0) ≤
          row plus (r+d) k (envelope plus r h d) (residue (r+d+1) m) := by
        rw [row_eq_branchWeight plus (r+d) k _ hm]
        unfold branchWeight
        split_ifs with ha
        · exact mul_le_mul_of_nonneg_left (ih k (child_pos plus k hm ha)).2
            (by unfold coefficient; positivity)
        · simp
      have hsum := row_summable plus (r+d) (envelope_nonneg plus r hh d)
        (residue (r+d+1) m)
      have hs := Summable.of_nonneg_of_le hnn hle hsum
      refine ⟨tsum_nonneg hnn, ?_⟩
      exact (Summable.tsum_le_tsum hle hs hsum).trans (le_max_right _ _)

/-- At each positive target the envelope is attained by a bounded policy,
so its deficit applies to the true optimum, not merely a chosen rule. -/
theorem envelope_attained (plus : Bool) (r : ℕ) (h : Level r → ℝ)
    (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ policy : Policy d, payoff plus r h policy m =
      envelope plus r h d (residue (r+d) m) := by
  induction d generalizing m with
  | zero => exact ⟨.stop 0, rfl⟩
  | succ d ih =>
      by_cases hc : transfer plus (r+d) (envelope plus r h d)
          (residue (r+(d+1)) m) ≤ h (residue r m)
      · exact ⟨.stop (d+1), by simp only [payoff, envelope, project_residue, max_eq_left hc]⟩
      · let children (k : ℕ) : Policy d := if ha : Admissible plus k m then
          Classical.choose (ih (child_pos plus k hm ha)) else .stop d
        refine ⟨.expand children, ?_⟩
        change (∑' k, if Admissible plus k m then
          coefficient k * payoff plus r h (children k) (child plus k m) else 0) = _
        simp only [envelope, project_residue, max_eq_right (le_of_lt (lt_of_not_ge hc))]
        apply tsum_congr
        intro k
        change _ = row plus (r+d) k (envelope plus r h d) (residue (r+d+1) m)
        rw [row_eq_branchWeight plus (r+d) k _ hm]
        unfold branchWeight
        by_cases ha : Admissible plus k m
        · dsimp only [children]
          simp only [dif_pos ha, if_pos ha]
          rw [Classical.choose_spec (ih (child_pos plus k hm ha))]
        · simp [ha]

/-- A forced first inverse step followed by arbitrary bounded policies is no
larger than the continuation value of the optimal stopping envelope. -/
theorem forced_payoff_le (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) {d : ℕ} (children : ℕ → Policy d)
    {m : ℕ} (hm : 1 ≤ m) : payoff plus r h (.expand children) m ≤
      transfer plus (r+d) (envelope plus r h d) (residue (r+d+1) m) := by
  have hnn (k : ℕ) : 0 ≤ if Admissible plus k m then
      coefficient k * payoff plus r h (children k) (child plus k m) else 0 := by
    split_ifs with ha
    · exact mul_nonneg (by unfold coefficient; positivity)
        (payoff_bounds plus r hh (children k) (child_pos plus k hm ha)).1
    · exact le_rfl
  have hle (k : ℕ) : (if Admissible plus k m then
      coefficient k * payoff plus r h (children k) (child plus k m) else 0) ≤
      row plus (r+d) k (envelope plus r h d) (residue (r+d+1) m) := by
    rw [row_eq_branchWeight plus (r+d) k _ hm]
    unfold branchWeight
    split_ifs with ha
    · exact mul_le_mul_of_nonneg_left
        (payoff_bounds plus r hh (children k) (child_pos plus k hm ha)).2
        (by unfold coefficient; positivity)
    · simp
  have hs := row_summable plus (r+d) (envelope_nonneg plus r hh d)
    (residue (r+d+1) m)
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnn hle hs) hs

/-- One unit residue defeats every forced-first-step policy with the stated
common finite budget, at every positive integer in that residue. Policies may
depend on the actual target and the complete inverse history. This theorem
does not concern policies without a common finite horizon. -/
theorem bounded_policy_deficit (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    {h : Level r → ℝ} (hh : ∀ b, 0 ≤ h b)
    (hz : ∀ b, b.val % 3 = 0 → h b = 0) (hs : 0 < h (spike plus r))
    (d : ℕ) : ∃ a : Level (r+d+1), a.val % 3 ≠ 0 ∧
      ∀ m : ℕ, 1 ≤ m → residue (r+d+1) m = a →
        ∀ children : ℕ → Policy d,
          payoff plus r h (.expand children) m < h (residue r m) := by
  obtain ⟨a, ha, hd⟩ := bounded_stopping_deficit plus hr hh hz hs d
  refine ⟨a, ha, fun m hm ham children => ?_⟩
  have hb := forced_payoff_le plus r hh children hm
  rw [ham] at hb
  have hp : project r (d+1) a = residue r m := by
    rw [← ham]
    exact project_residue r (d+1) m
  exact hb.trans_lt (by simpa only [hp] using hd)

end Problems.Collatz.FibreStopping
