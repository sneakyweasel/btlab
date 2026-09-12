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
  hypothesis, with `s(L)` the 13-level Ostrowski digit sum.
* `hugCharge_sub_circleMean_window` — on `L < 301994` the digit cap makes it `94/L`.
* `hugCharge_sub_circleMean_extended` — on the printed window `[50508, 16785921)` the
  mixed `q₁₃` list makes it `94/50508`.
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

/-- **Theorem 5.7 for the mixed `q₁₃` list.**  The charge per letter is
within `2(b + s(r))/L` of the circle mean. -/
theorem hugCharge_sub_circleMean_extended_le {n' : ℝ} (hn : 1 < n') {L : ℕ}
    (hL : 0 < L) :
    |hugCharge n' L - circleMean n'|
      ≤ 2 * ((ostroBlocksExtended L).length : ℝ) / L := by
  have hLR : (0:ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hinv : (0:ℝ) < 1 / (L : ℝ) := by positivity
  have h := theta_block_envelope_extended hn L 0
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
      ≤ (1 / (L : ℝ)) * (((ostroBlocksExtended L).length : ℝ) * 2) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hinv)
    _ = 2 * ((ostroBlocksExtended L).length : ℝ) / L := by
        ring

/-- **Theorem 5.8's named window instance.**  On the printed half-open
window `[50508, q₁₄)` the mixed-list digit cap gives the uniform bound
`94/50508`.  The binding term is `94/50508` on `L < q₁₃`; the tail is
`2(b+47)/(b q₁₃) ≤ 96/q₁₃`. -/
theorem hugCharge_sub_circleMean_extended {n' : ℝ} (hn : 1 < n') {L : ℕ}
    (hLo : 50508 ≤ L) (_hHi : L < 16785921) :
    |hugCharge n' L - circleMean n'| ≤ 94 / 50508 := by
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℕ) < 50508) hLo
  have hLR : (0:ℝ) < (L : ℝ) := by exact_mod_cast hL
  refine (hugCharge_sub_circleMean_extended_le hn hL).trans ?_
  have hlen : (ostroBlocksExtended L).length ≤ L / 301994 + 47 :=
    ostroBlocksExtended_digitSum_le L
  by_cases hsmall : L < 301994
  · have hb : L / 301994 = 0 := Nat.div_eq_of_lt hsmall
    have hcap : (ostroBlocksExtended L).length ≤ 47 := by
      simpa [hb] using hlen
    have hnum : ((ostroBlocksExtended L).length : ℝ) ≤ 47 := by exact_mod_cast hcap
    have hLlo : (50508 : ℝ) ≤ L := by exact_mod_cast hLo
    have hstep : (2:ℝ) * (ostroBlocksExtended L).length / L ≤ 94 / L := by
      rw [div_le_div_iff₀ hLR hLR]
      nlinarith
    have hwin : (94:ℝ) / L ≤ 94 / 50508 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLlo
    exact hstep.trans hwin
  · push Not at hsmall
    set b := L / 301994
    have hbpos : 1 ≤ b := (Nat.one_le_div_iff (by norm_num : (0:ℕ) < 301994)).mpr hsmall
    have hbR : (0:ℝ) < (b : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) hbpos)
    have hLbR : (301994 : ℝ) * b ≤ L := by
      exact_mod_cast (show 301994 * b ≤ L by simpa [b] using Nat.mul_div_le L 301994)
    have hnum : ((ostroBlocksExtended L).length : ℝ) ≤ (b : ℝ) + 47 := by
      exact_mod_cast hlen
    have hden : (0:ℝ) < (301994 : ℝ) * b := mul_pos (by norm_num) hbR
    have hstep : (2:ℝ) * (ostroBlocksExtended L).length / L
        ≤ (2:ℝ) * ((b : ℝ) + 47) / ((301994 : ℝ) * b) := by
      rw [div_le_div_iff₀ hLR hden]
      nlinarith
    have htail : (2:ℝ) * ((b : ℝ) + 47) / ((301994 : ℝ) * b) ≤ 96 / 301994 := by
      rw [div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 301994)]
      nlinarith [show (1:ℝ) ≤ b by exact_mod_cast hbpos]
    have hcmp : (96:ℝ) / 301994 ≤ 94 / 50508 := by norm_num
    exact (hstep.trans htail).trans hcmp

end Problems.Juggler
