import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Finset.Max

/-!
# Integration along a finite cumulative jump profile

Splitting at the final jump proves the fundamental theorem of calculus
with every jump increment and both endpoint values retained. This is the
finite-cutoff input for the occupation law of the tilted Beatty profile.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset

/-- A finite left-continuous cumulative jump profile with initial height `c`. -/
noncomputable def finiteJumpProfile (s : Finset ℕ) (phase w : ℕ → ℝ)
    (c t : ℝ) : ℝ := c + ∑ i ∈ s, if phase i < t then w i else 0

/-- Nonnegative finite jump weights give a monotone profile. -/
theorem finiteJumpProfile_monotone {phase w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (s : Finset ℕ) (c : ℝ) : Monotone (finiteJumpProfile s phase w c) := by
  intro x y hxy
  unfold finiteJumpProfile
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : phase i < x
  · simp [hx, hx.trans_le hxy]
  · simp only [hx, if_false]
    split_ifs <;> simp [hw i]

/-- The initial height and retained total mass bound a finite positive profile. -/
theorem finiteJumpProfile_bounds {phase w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (s : Finset ℕ) (c t : ℝ) :
    c ≤ finiteJumpProfile s phase w c t ∧
      finiteJumpProfile s phase w c t ≤ c + ∑ i ∈ s, w i := by
  unfold finiteJumpProfile
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hw i])
  · apply add_le_add_right
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp [hw i]

/-- Once all retained phases precede the argument, the finite profile is
its initial height plus the full retained mass. -/
theorem finiteJumpProfile_eq_total {s : Finset ℕ} {phase w : ℕ → ℝ} {c t : ℝ}
    (h : ∀ i ∈ s, phase i < t) :
    finiteJumpProfile s phase w c t = c + ∑ i ∈ s, w i := by
  unfold finiteJumpProfile
  congr 1
  exact Finset.sum_congr rfl fun i hi => if_pos (h i hi)

/-- The fundamental theorem along a finite positive jump profile. The
integrand is a derivative only between jumps, so their increments must
be subtracted explicitly. No ordering of the index set is assumed. -/
theorem finiteJumpProfile_integral_chain {phase w : ℕ → ℝ}
    (hi : Function.Injective phase) (hw : ∀ i, 0 ≤ w i)
    {P D : ℝ → ℝ → ℝ}
    (hD : ∀ c, 0 < c → Continuous (fun t => D t c))
    (hP : ∀ c, 0 < c → ∀ t, HasDerivAt (fun t => P t c) (D t c) t)
    (s : Finset ℕ) {c a b : ℝ} (hc : 0 < c) (hab : a ≤ b)
    (hp : ∀ i ∈ s, phase i ∈ Ioo a b) :
    IntervalIntegrable (fun t => D t (finiteJumpProfile s phase w c t)) volume a b ∧
    (∫ t in a..b, D t (finiteJumpProfile s phase w c t)) =
      P b (c + ∑ i ∈ s, w i) - P a c -
        ∑ i ∈ s, (P (phase i) (finiteJumpProfile s phase w c (phase i) + w i) -
          P (phase i) (finiteJumpProfile s phase w c (phase i))) := by
  classical
  induction s using Finset.strongInductionOn generalizing a b with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa [finiteJumpProfile] using
        And.intro ((hD c hc).intervalIntegrable a b)
          (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hP c hc t)
            ((hD c hc).intervalIntegrable a b))
    obtain ⟨k, hk, hmax⟩ := s.exists_max_image phase hs
    have hkphase := hp k hk
    have hrest : ∀ i ∈ s.erase k, phase i ∈ Ioo a (phase k) := by
      intro i hi'
      obtain ⟨hne, his⟩ := Finset.mem_erase.mp hi'
      exact ⟨(hp i his).1, lt_of_le_of_ne (hmax i his) (fun h => hne (hi h))⟩
    obtain ⟨hint, heq⟩ := ih (s.erase k) (Finset.erase_ssubset hk)
      hkphase.1.le hrest
    have hsplit (t : ℝ) : finiteJumpProfile s phase w c t =
        finiteJumpProfile (s.erase k) phase w c t + (if phase k < t then w k else 0) := by
      unfold finiteJumpProfile
      have h := Finset.sum_erase_add s (fun i => if phase i < t then w i else 0) hk
      linarith
    have hbefore (t : ℝ) (ht : t ≤ phase k) :
        finiteJumpProfile s phase w c t = finiteJumpProfile (s.erase k) phase w c t := by
      rw [hsplit, if_neg (not_lt_of_ge ht), add_zero]
    have hafter (t : ℝ) (ht : phase k < t) :
        finiteJumpProfile s phase w c t = c + ∑ i ∈ s, w i :=
      finiteJumpProfile_eq_total (fun i his => (hmax i his).trans_lt ht)
    have hleft : IntervalIntegrable
        (fun t => D t (finiteJumpProfile s phase w c t)) volume a (phase k) :=
      hint.congr_uIoo (by
        rw [uIoo_of_le hkphase.1.le]
        intro t ht
        dsimp only
        rw [hbefore t ht.2.le])
    have htotal : 0 < c + ∑ i ∈ s, w i :=
      add_pos_of_pos_of_nonneg hc (Finset.sum_nonneg fun i _ => hw i)
    have hright : IntervalIntegrable
        (fun t => D t (finiteJumpProfile s phase w c t)) volume (phase k) b :=
      ((hD _ htotal).intervalIntegrable (phase k) b).congr_uIoo (by
        rw [uIoo_of_le hkphase.2.le]
        intro t ht
        dsimp only
        rw [hafter t ht.1])
    refine ⟨hleft.trans hright, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
    have hli : (∫ t in a..phase k, D t (finiteJumpProfile s phase w c t)) =
        ∫ t in a..phase k, D t (finiteJumpProfile (s.erase k) phase w c t) :=
      intervalIntegral.integral_congr_Ioo_of_le hkphase.1.le
        (fun t ht => by rw [hbefore t ht.2.le])
    have hri : (∫ t in phase k..b, D t (finiteJumpProfile s phase w c t)) =
        P b (c + ∑ i ∈ s, w i) - P (phase k) (c + ∑ i ∈ s, w i) := by
      rw [intervalIntegral.integral_congr_Ioo_of_le hkphase.2.le
        (fun t ht => show D t (finiteJumpProfile s phase w c t) =
          D t (c + ∑ i ∈ s, w i) by rw [hafter t ht.1])]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hP _ htotal t) ((hD _ htotal).intervalIntegrable (phase k) b)
    rw [hli, heq, hri]
    have hmass := Finset.sum_erase_add s w hk
    have hat : finiteJumpProfile s phase w c (phase k) = c + ∑ i ∈ s.erase k, w i := by
      rw [hbefore _ le_rfl]
      exact finiteJumpProfile_eq_total fun i hi' => (hrest i hi').2
    rw [← Finset.sum_erase_add s (fun i =>
      P (phase i) (finiteJumpProfile s phase w c (phase i) + w i) -
        P (phase i) (finiteJumpProfile s phase w c (phase i))) hk]
    have hsum : (∑ i ∈ s.erase k,
        (P (phase i) (finiteJumpProfile s phase w c (phase i) + w i) -
          P (phase i) (finiteJumpProfile s phase w c (phase i)))) =
        ∑ i ∈ s.erase k,
        (P (phase i) (finiteJumpProfile (s.erase k) phase w c (phase i) + w i) -
          P (phase i) (finiteJumpProfile (s.erase k) phase w c (phase i))) := by
      apply Finset.sum_congr rfl
      intro i hi'
      rw [hbefore _ (hrest i hi').2.le]
    have hheight : c + (∑ i ∈ s.erase k, w i) + w k = c + ∑ i ∈ s, w i := by
      linarith [hmass]
    rw [hsum, hat, hheight]
    ring

end Problems.Juggler.BeattyPhase
