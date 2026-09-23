import Problems.Collatz.FibreMinorants

/-! # Greatest bounded periodic subsolutions

At a fixed ternary level and nonnegative rate there is one greatest bounded
unit-supported subsolution. It dominates every candidate at every root.
This order reduction supplies no near-critical limit or root lower bound.
-/

noncomputable section

namespace Problems.Collatz.FibreSubsolutions

open Finset FibreMass FibreActual
open scoped Classical

/-- The unit indicator at an arbitrary ternary level, used as the fixed cap. -/
def unitCap (r : ℕ) (b : Level r) : ℝ := if b.val % 3 = 0 then 0 else 1

/-- A bounded nonnegative periodic weight whose complete inverse transfer
reproduces at least the specified rate. Zero is allowed; no positive root
value, convergence of rates or termination conclusion is part of this predicate. -/
structure Subsolution (plus : Bool) (r : ℕ) (q : ℝ) (h : Level r → ℝ) : Prop where
  nonneg : ∀ b, 0 ≤ h b
  le_cap : ∀ b, h b ≤ unitCap r b
  reproduce : ∀ b : Level (r+1), q*h (project r 1 b) ≤ transfer plus r h b

private theorem cap_nonneg (r : ℕ) (b : Level r) : 0 ≤ unitCap r b := by
  unfold unitCap; split_ifs <;> norm_num

private theorem cap_le_one (r : ℕ) (b : Level r) : unitCap r b ≤ 1 := by
  unfold unitCap; split_ifs <;> norm_num

private theorem zero_subsolution (plus : Bool) (r : ℕ) (q : ℝ) :
    Subsolution plus r q (fun _ => 0) := by
  refine ⟨fun _ => le_rfl, cap_nonneg r, ?_⟩
  intro b
  simp [transfer, row]

private theorem transfer_mono (plus : Bool) (r : ℕ) {h g : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (hg : ∀ b, 0 ≤ g b) (hle : ∀ b, h b ≤ g b)
    (a : Level (r+1)) : transfer plus r h a ≤ transfer plus r g a := by
  apply Summable.tsum_le_tsum _ (row_summable plus r hh a) (row_summable plus r hg a)
  intro k
  unfold row
  apply mul_le_mul_of_nonneg_left _ (by unfold coefficient; positivity)
  apply sum_le_sum
  intro b hb
  split_ifs
  · exact hle b
  · rfl

private def values (plus : Bool) (r : ℕ) (q : ℝ) (b : Level r) : Set ℝ :=
  {v | ∃ h, Subsolution plus r q h ∧ v = h b}

/-- A pointwise increase of a subsolution remains feasible if it stays below
the cap and its required output is already supplied by the old transfer.
In particular, downward rounding of such an increasing update is safe. -/
theorem subsolution_of_between (plus : Bool) (r : ℕ) (q : ℝ)
    {h g : Level r → ℝ} (hh : Subsolution plus r q h)
    (hle : ∀ b, h b ≤ g b) (hcap : ∀ b, g b ≤ unitCap r b)
    (hstep : ∀ b : Level (r+1), q*g (project r 1 b) ≤ transfer plus r h b) :
    Subsolution plus r q g := by
  have hg := fun b => (hh.nonneg b).trans (hle b)
  exact ⟨hg, hcap, fun b => (hstep b).trans (transfer_mono plus r hh.nonneg hg hle b)⟩

private theorem values_nonempty (plus : Bool) (r : ℕ) (q : ℝ) (b : Level r) :
    (values plus r q b).Nonempty := ⟨0, fun _ => 0, zero_subsolution plus r q, rfl⟩

private theorem values_bddAbove (plus : Bool) (r : ℕ) (q : ℝ) (b : Level r) :
    BddAbove (values plus r q b) := by
  refine ⟨unitCap r b, ?_⟩
  rintro v ⟨h, hh, rfl⟩
  exact hh.le_cap b

/-- The coordinatewise supremum of all bounded unit-supported subsolutions.
Its feasibility and greatest-element property are proved below. -/
def maximalWeight (plus : Bool) (r : ℕ) (q : ℝ) (b : Level r) : ℝ :=
  sSup (values plus r q b)

/-- Every feasible periodic weight is bounded by the same maximal weight,
so optimizing different root coordinates does not require different tables. -/
theorem le_maximalWeight (plus : Bool) (r : ℕ) (q : ℝ) {h : Level r → ℝ}
    (hh : Subsolution plus r q h) (b : Level r) : h b ≤ maximalWeight plus r q b :=
  le_csSup (values_bddAbove plus r q b) ⟨h, hh, rfl⟩

/-- The maximal table obeys the fixed pointwise cap and is nonnegative. -/
theorem maximalWeight_bounds (plus : Bool) (r : ℕ) (q : ℝ) (b : Level r) :
    0 ≤ maximalWeight plus r q b ∧ maximalWeight plus r q b ≤ unitCap r b := by
  refine ⟨le_maximalWeight plus r q (zero_subsolution plus r q) b, ?_⟩
  apply csSup_le (values_nonempty plus r q b)
  rintro v ⟨h, hh, rfl⟩
  exact hh.le_cap b

/-- At every nonnegative rate the coordinatewise supremum is itself a
subsolution. This proves simultaneous optimality at every residue, without
asserting that the maximum is positive or that rates can approach one. -/
theorem maximalWeight_subsolution (plus : Bool) (r : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    Subsolution plus r q (maximalWeight plus r q) := by
  have hn := fun b => (maximalWeight_bounds plus r q b).1
  refine ⟨hn, fun b => (maximalWeight_bounds plus r q b).2, ?_⟩
  intro b
  rcases eq_or_lt_of_le hq with he | hpos
  · subst q
    simpa only [zero_mul] using transfer_nonneg plus r hn b
  · rw [mul_comm q]
    apply (le_div_iff₀ hpos).mp
    apply csSup_le (values_nonempty plus r q (project r 1 b))
    rintro v ⟨h, hh, rfl⟩
    apply (le_div_iff₀ hpos).mpr
    have ht := (hh.reproduce b).trans (transfer_mono plus r hh.nonneg hn
      (le_maximalWeight plus r q hh) b)
    simpa only [mul_comm] using ht

/-- A smaller required rate can only increase the greatest feasible table. -/
theorem maximalWeight_antitone_rate (plus : Bool) (r : ℕ) {p q : ℝ}
    (hq : 0 ≤ q) (hpq : p ≤ q) (b : Level r) :
    maximalWeight plus r q b ≤ maximalWeight plus r p b := by
  have hh := maximalWeight_subsolution plus r hq
  apply le_maximalWeight plus r p (h := maximalWeight plus r q) _ b
  refine ⟨hh.nonneg, hh.le_cap, ?_⟩
  intro a
  exact (mul_le_mul_of_nonneg_right hpq (hh.nonneg _)).trans (hh.reproduce a)

private theorem cap_project {r : ℕ} (hr : 1 ≤ r) (b : Level (r+1)) :
    unitCap r (project r 1 b) = unitCap (r+1) b := by
  have he : (b.val % 3^r) % 3 = b.val % 3 :=
    Nat.mod_mod_of_dvd b.val (Nat.pow_dvd_pow 3 hr)
  simp only [unitCap, project, he]

/-- A feasible periodic table remains feasible when copied to the next
ternary level. The rate and the value at each ordinary integer are preserved. -/
theorem subsolution_lift (plus : Bool) {r : ℕ} (hr : 1 ≤ r) (q : ℝ)
    {h : Level r → ℝ} (hh : Subsolution plus r q h) :
    Subsolution plus (r+1) q (fun b => h (project r 1 b)) := by
  have hg : ∀ b : Level (r+1), 0 ≤ h (project r 1 b) := fun b => hh.nonneg _
  refine ⟨hg, fun b => (hh.le_cap _).trans_eq (cap_project hr b), ?_⟩
  intro b
  let m := b.val + 3^(r+1+1)
  have hm : 1 ≤ m := by
    dsimp [m]
    have hp : 0 < 3^(r+1+1) := by positivity
    omega
  have he : residue (r+1+1) m = b := by
    apply Fin.ext
    simp [residue, m, Nat.mod_eq_of_lt b.isLt]
  have ht := transfer_le_of_residue_le plus hh.nonneg hg (fun n hn => by
    rw [project_residue]) hm
  have hs := hh.reproduce (residue (r+1) m)
  rw [project_residue] at hs
  rw [← he, project_residue, project_residue]
  exact hs.trans ht

/-- At a fixed nonnegative rate, adding one ternary digit cannot reduce the
best attainable weight at any prescribed positive integer. -/
theorem maximalWeight_mono_level (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    {q : ℝ} (hq : 0 ≤ q) (a : ℕ) :
    maximalWeight plus r q (residue r a) ≤
      maximalWeight plus (r+1) q (residue (r+1) a) := by
  have ht := le_maximalWeight plus (r+1) q
    (subsolution_lift plus hr q (maximalWeight_subsolution plus r hq)) (residue (r+1) a)
  simpa only [project_residue] using ht

/-- The greatest bounded subsolution supplies the strongest lower bound of
this periodic form at every root, at the chosen level and rate. No positive
value or near-critical limiting family is asserted by this implication. -/
theorem maximalWeight_geometric_lower (plus : Bool) (r : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (d : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    q^d * maximalWeight plus r q (residue r a) ≤ FibreUnitComparison.coarse plus d a := by
  have hh := maximalWeight_subsolution plus r hq
  exact FibreMinorants.coarse_geometric_lower plus r _ hh.nonneg
    (fun b => (hh.le_cap b).trans (cap_le_one r b)) hq hh.reproduce d ha

/-- The remaining arithmetic target can be stated using just the canonical
greatest tables: near-critical rates and a uniform positive root-to-deficit
ratio imply coefficient divergence. The root estimate remains a hypothesis. -/
theorem coarse_not_summable_of_maximalWeight (plus : Bool) {a : ℕ} (ha : 1 ≤ a)
    (r : ℕ → ℕ) (q : ℕ → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hlim : Filter.Tendsto q Filter.atTop (nhds 1)) {c : ℝ} (hc : 0 < c)
    (hanchor : ∀ i, c*(1-q i) ≤ maximalWeight plus (r i) (q i) (residue (r i) a)) :
    ¬Summable (fun d => FibreUnitComparison.coarse plus d a) := by
  have hh := fun i => maximalWeight_subsolution plus (r i) (hq0 i)
  exact FibreMinorants.coarse_not_summable_of_weights plus ha r
    (fun i => maximalWeight plus (r i) (q i)) q (fun i => (hh i).nonneg)
    (fun i b => ((hh i).le_cap b).trans (cap_le_one (r i) b))
    hq0 hq1 hlim (fun i => (hh i).reproduce) hc hanchor

end Problems.Collatz.FibreSubsolutions
