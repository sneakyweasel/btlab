/-
# Theorem 5.7 as one statement

Every input to Paper A's Theorem 5.7 is now Lean — the Denjoy–Koksma inequality, its orbit
half, the observable's variation, the block composition, the Ostrowski assembly, and Lemma
5.6's rotation identification — but the display itself was still a chain a reader had to
compose.  This file states it once.

## The definition, and what is and is not a theorem about it

The laboratory had no `C_L`.  `stateCharge` (`WalkChargeMax.lean`) is Theorem 5.4's envelope
charge `1/(exp(Wν)·W·ν)`, a different normalisation: `blockObservable n' u` equals
`n'·(log n')·stateCharge (log n') (2^u)`, proportional but not equal.  So `hugCharge` below is
a *definition*, and the honest reading of what it rests on is:

* it is the average of Theorem 5.7's own observable along the exponent walk — that much is
  by construction;
* the walk positions are the *budgeted* word's, because the budgeted word is the hug word
  (`budgetedWord_eq_hugWord`), which is a theorem;
* and the `k`-th term of the rotation's ergodic sum at phase `0` is that observable at the
  `k`-th walk position (`periodicObservable_hugWalk`), which is a theorem.

What is *not* a theorem is that Paper A's phrase "charge per letter" denotes this average
rather than some other normalisation of it.  That is a modelling choice, and the two named
theorems are what make it the defensible one.

## Statements

* `hugCharge_sub_circleMean_le` — `|C_L − C_*| ≤ 2·s(L)/L` for every `L > 0`, no window
  hypothesis, with `s(L)` the Ostrowski digit sum.
* `hugCharge_sub_circleMean_window` — on the certified window the digit cap makes it `94/L`.
-/

import Problems.Juggler.OstrowskiBlocks
import Problems.Juggler.HugRotation

namespace Problems.Juggler

/-- The exponent-walk position after `k` steps: `u_k = a_k·log₂3 − k`. -/
noncomputable def hugWalkPos (k : ℕ) : ℝ :=
  (hugOdds k : ℝ) * (Real.log 3 / Real.log 2) - (k : ℝ)

/-- **`C_L`.**  The charge per letter of the hug word of length `L`: the average of the
observable along the exponent walk. -/
noncomputable def hugCharge (n' : ℝ) (L : ℕ) : ℝ :=
  (∑ k ∈ Finset.range L, blockObservable n' (hugWalkPos k)) / L

/-- **`C_*`.**  The mean of the observable over the circle. -/
noncomputable def circleMean (n' : ℝ) : ℝ := ∫ t in (0:ℝ)..1, periodicObservable n' t

/-- The rotation's ergodic sum at phase `0` is the walk sum, termwise. -/
theorem sum_periodicObservable_eq_walk (n' : ℝ) (L : ℕ) :
    ∑ k ∈ Finset.range L, periodicObservable n' ((0:ℝ) + (k : ℝ) * walkTheta)
      = ∑ k ∈ Finset.range L, blockObservable n' (hugWalkPos k) :=
  Finset.sum_congr rfl fun k _ => by
    rw [zero_add, periodicObservable_hugWalk, hugWalkPos]

/-- **Theorem 5.7, in one statement.**  For every length, the charge per letter is within
`2 s(L)/L` of the circle mean, where `s(L)` is the Ostrowski digit sum of `L`. -/
theorem hugCharge_sub_circleMean_le {n' : ℝ} (hn : 1 < n') {L : ℕ} (hL : 0 < L) :
    |hugCharge n' L - circleMean n'|
      ≤ 2 * ((∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i : ℕ) : ℝ) / L := by
  have hLR : (0:ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hinv : (0:ℝ) < 1 / (L : ℝ) := by positivity
  have h := theta_block_envelope_of_length hn L 0
  rw [sum_periodicObservable_eq_walk] at h
  simp only [hugCharge, circleMean]
  have hfac : (∑ k ∈ Finset.range L, blockObservable n' (hugWalkPos k)) / (L : ℝ)
        - ∫ t in (0:ℝ)..1, periodicObservable n' t
      = (1 / (L : ℝ)) * ((∑ k ∈ Finset.range L, blockObservable n' (hugWalkPos k))
          - (L : ℝ) * ∫ t in (0:ℝ)..1, periodicObservable n' t) := by
    field_simp
  rw [hfac, abs_mul, abs_of_pos hinv]
  calc (1 / (L : ℝ)) * |(∑ k ∈ Finset.range L, blockObservable n' (hugWalkPos k))
          - (L : ℝ) * ∫ t in (0:ℝ)..1, periodicObservable n' t|
      ≤ (1 / (L : ℝ)) *
          (((∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i : ℕ) : ℝ) * 2) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hinv)
    _ = 2 * ((∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i : ℕ) : ℝ) / L := by
        ring

/-- **On the certified window the bound is `94/L`.**  The digit cap `s(L) ≤ 47` is
structural, so this holds for every `L < 301994` with no scan. -/
theorem hugCharge_sub_circleMean_window {n' : ℝ} (hn : 1 < n') {L : ℕ}
    (hL : 0 < L) (hLw : L < 301994) :
    |hugCharge n' L - circleMean n'| ≤ 94 / L := by
  have hLR : (0:ℝ) < (L : ℝ) := by exact_mod_cast hL
  refine (hugCharge_sub_circleMean_le hn hL).trans ?_
  have hcap : ((∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i : ℕ) : ℝ) ≤ 47 := by
    exact_mod_cast theta_digitSum_le hLw
  rw [div_le_div_iff₀ hLR hLR]
  nlinarith

end Problems.Juggler
