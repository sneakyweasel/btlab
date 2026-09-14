import Mathlib.Algebra.Order.Chebyshev
import Problems.Juggler.FateOneSidedAtoms
import Problems.Juggler.FateCylinderEnergy

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The bias energy supplies the exceptional atoms (Section 10(d))

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Section 10(d): "an additional
quantitative bound on these sums can supply an exceptional-atom estimate". This file is that
step, exactly. The *bias energy* at depth `t` is `Σ_{|w|=t} D(w)²` with `D(w) = #[wO] - #[w]/2`
over the odd starts of `(y, 2y]` (`Energy.biasEnergy`); by `CylinderEnergy.sum_bias_sq` it is
the paper's `C_{t+1}/2 - C_t/4` (`Energy.biasEnergy_eq`). The atoms that violate the share
bound `#[wO] ≤ q #[w]` for a share `q > 1/2` have `D(w) > (q - 1/2) #[w]`, so their squared
masses are bounded by the energy over `(q - 1/2)²`, and Cauchy–Schwarz over at most `2^t`
atoms bounds their total mass (`Energy.mass_violators_le`):

`(Σ_{w violating} #[w])² ≤ 2^t · biasEnergy / (q - 1/2)²`.

Hence an energy bound `biasEnergy(t) ≤ (q - 1/2)² exc² / 2^t` at every depth `1 ≤ t < d`
gives the one-sided hypothesis with exceptional atoms of mass `exc` and no error term
(`Energy.oneSidedShareExc_of_energy`), which `FateOneSidedAtoms` runs to the conjecture:
`Energy.energy_implies_conjecture` needs the energy bound with `exc = y (log y)^{-B}` at all
large scales, `1/2 < q < p_C`, `B > C log₂ x + 1 + e` and `7/10 < e < e_{C,q}`, and nothing
else.

What this changes. The pincer's rate-side question is now a single second-moment statement
about how cylinders split, `Σ_{|w|=t} D(w)² ≤ (q - 1/2)² y² (log y)^{-2B} / 2^t` for
`t < ⌈C L(y)⌉`, rather than a per-cylinder share bound. For comparison, fair splitting with
square-root fluctuations has `Σ D(w)² ≈ y`, while the bound allows `y² (log y)^{-C - 2B}`.
Nothing here proves the energy bound; it is Appendix C's question in its weakest dress so
far. Not a halt theorem.
-/

namespace OneSided

/-- A share bound with exceptional atoms and a smaller error is one with a larger error. -/
theorem OneSidedShareExc.mono_err {y : ℕ} {L q err err' exc : ℝ} {d : ℕ}
    (h : OneSidedShareExc y L q err exc d) (hle : err ≤ err') :
    OneSidedShareExc y L q err' exc d := by
  intro t ht1 htd
  obtain ⟨E, hE, hshare⟩ := h t ht1 htd
  exact ⟨E, hE, fun w hw hbad hwE => le_trans (hshare w hw hbad hwE) (by linarith)⟩

end OneSided

namespace Energy

/-- The bias energy at depth `t`: `Σ_{|w|=t} (#[wO] - #[w]/2)²` over the odd starts of
`(y, 2y]`. -/
noncomputable def biasEnergy (y t : ℕ) : ℝ :=
  ∑ w ∈ allWords t,
    (((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ) - (cylinder y t w).card / 2) ^ 2

/-- The atoms of depth `t` that violate the share bound `#[wO] ≤ q #[w]`. -/
noncomputable def violators (y t : ℕ) (q : ℝ) : Finset (List Branch) :=
  (allWords t).filter fun w =>
    q * (cylinder y t w).card < ((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ)

/-- There are `2^t` words of length `t`. -/
theorem card_allWords : ∀ t, ((allWords t).card : ℝ) = 2 ^ t
  | 0 => by simp [allWords]
  | t + 1 => by
      have h := OneSided.sum_allWords_succ (fun _ => (1 : ℝ)) t
      simp only [sum_const, nsmul_eq_mul, mul_one] at h
      rw [h, card_allWords t]
      ring

/-- **Cauchy–Schwarz on the violators.** For a share `q > 1/2`,
`(Σ_{w violating} #[w])² ≤ 2^t · biasEnergy / (q - 1/2)²`. -/
theorem mass_violators_le (y t : ℕ) {q : ℝ} (hq : 1 / 2 < q) :
    (∑ w ∈ violators y t q, ((cylinder y t w).card : ℝ)) ^ 2
      ≤ 2 ^ t * (biasEnergy y t / (q - 1 / 2) ^ 2) := by
  have hε0 : 0 < q - 1 / 2 := by linarith
  -- a violator has `D(w) > (q - 1/2) #[w] ≥ 0`
  have hsq : ∀ w ∈ violators y t q, ((cylinder y t w).card : ℝ) ^ 2
      ≤ (((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ) - (cylinder y t w).card / 2) ^ 2
        / (q - 1 / 2) ^ 2 := by
    intro w hw
    rw [violators, mem_filter] at hw
    obtain ⟨-, hlt⟩ := hw
    rw [le_div_iff₀ (by positivity)]
    have hN0 : (0 : ℝ) ≤ (cylinder y t w).card := Nat.cast_nonneg _
    have hbias : (q - 1 / 2) * (cylinder y t w).card
        ≤ ((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ) - (cylinder y t w).card / 2 := by
      linarith
    have h0 : 0 ≤ (q - 1 / 2) * (cylinder y t w).card := mul_nonneg hε0.le hN0
    calc ((cylinder y t w).card : ℝ) ^ 2 * (q - 1 / 2) ^ 2
        = ((q - 1 / 2) * (cylinder y t w).card) ^ 2 := by ring
      _ ≤ (((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ)
            - (cylinder y t w).card / 2) ^ 2 := pow_le_pow_left₀ h0 hbias 2
  have hcard : ((violators y t q).card : ℝ) ≤ 2 ^ t := by
    rw [← card_allWords t]
    exact_mod_cast card_filter_le _ _
  have hsum : ∑ w ∈ violators y t q, ((cylinder y t w).card : ℝ) ^ 2
      ≤ biasEnergy y t / (q - 1 / 2) ^ 2 := by
    calc ∑ w ∈ violators y t q, ((cylinder y t w).card : ℝ) ^ 2
        ≤ ∑ w ∈ violators y t q,
            (((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ) - (cylinder y t w).card / 2) ^ 2
              / (q - 1 / 2) ^ 2 := sum_le_sum hsq
      _ = (∑ w ∈ violators y t q,
            (((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ)
              - (cylinder y t w).card / 2) ^ 2) / (q - 1 / 2) ^ 2 := by rw [sum_div]
      _ ≤ (∑ w ∈ allWords t,
            (((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ)
              - (cylinder y t w).card / 2) ^ 2) / (q - 1 / 2) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun w _ _ => sq_nonneg _)
      _ = biasEnergy y t / (q - 1 / 2) ^ 2 := rfl
  calc (∑ w ∈ violators y t q, ((cylinder y t w).card : ℝ)) ^ 2
      ≤ (violators y t q).card * ∑ w ∈ violators y t q, ((cylinder y t w).card : ℝ) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ 2 ^ t * (biasEnergy y t / (q - 1 / 2) ^ 2) :=
        mul_le_mul hcard hsum (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)

/-- **Energy implies exceptional atoms.** If the bias energy at every depth `1 ≤ t < d` is at
most `(q - 1/2)² exc² / 2^t`, the violators of the share bound `#[wO] ≤ q #[w]` have total
mass at most `exc` at each depth, so the one-sided hypothesis holds with exceptional atoms of
mass `exc` and no error term, for every `L`. -/
theorem oneSidedShareExc_of_energy {y d : ℕ} {L q exc : ℝ} (hq : 1 / 2 < q) (hexc : 0 ≤ exc)
    (h : ∀ t, 1 ≤ t → t < d → biasEnergy y t ≤ (q - 1 / 2) ^ 2 * exc ^ 2 / 2 ^ t) :
    OneSided.OneSidedShareExc y L q 0 exc d := by
  intro t ht1 htd
  refine ⟨violators y t q, ?_, ?_⟩
  · have hε0 : 0 < q - 1 / 2 := by linarith
    have hcs := mass_violators_le y t hq
    have hb := h t ht1 htd
    have hfilter : (allWords t).filter (· ∈ violators y t q) = violators y t q := by
      rw [filter_mem_eq_inter]
      exact inter_eq_right.mpr (fun w hw => by rw [violators, mem_filter] at hw; exact hw.1)
    rw [hfilter]
    have hmass0 : 0 ≤ ∑ w ∈ violators y t q, ((cylinder y t w).card : ℝ) :=
      sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hsq : (∑ w ∈ violators y t q, ((cylinder y t w).card : ℝ)) ^ 2 ≤ exc ^ 2 := by
      calc (∑ w ∈ violators y t q, ((cylinder y t w).card : ℝ)) ^ 2
          ≤ 2 ^ t * (biasEnergy y t / (q - 1 / 2) ^ 2) := hcs
        _ ≤ 2 ^ t * (((q - 1 / 2) ^ 2 * exc ^ 2 / 2 ^ t) / (q - 1 / 2) ^ 2) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by positivity))
              (by positivity)
        _ = exc ^ 2 := by
            have hne : q - 1 / 2 ≠ 0 := hε0.ne'
            have hne2 : q * 2 - 1 ≠ 0 := by intro h; linarith
            field_simp
    exact (pow_le_pow_iff_left₀ hmass0 hexc (by norm_num)).mp hsq
  · intro w hw _ hwV
    rw [violators, mem_filter] at hwV
    push Not at hwV
    rw [add_zero]
    exact hwV hw

/-! ### The paper's `C_t` -/

/-- The word count of `CylinderEnergy` over the odd starts of `(y, 2y]` is the cylinder. -/
theorem wordCount_cylinder (y t : ℕ) {w : List Branch} (hw : w.length = t) :
    CylinderEnergy.wordCount (cylinder y 0 []) w = (cylinder y t w).card := by
  unfold CylinderEnergy.wordCount cylinder
  rw [hw, filter_filter]
  congr 1
  apply filter_congr
  intro n _
  simp [itinerary_zero]

/-- The bias energy is the paper's `C_{t+1}/2 - C_t/4`, with `C_t = Σ_{|w|=t} #[w]²`
(`CylinderEnergy.sum_bias_sq`). -/
theorem biasEnergy_eq (y t : ℕ) :
    biasEnergy y t = CylinderEnergy.energy (cylinder y 0 []) (t + 1) / 2
      - CylinderEnergy.energy (cylinder y 0 []) t / 4 := by
  rw [← CylinderEnergy.sum_bias_sq]
  unfold biasEnergy CylinderEnergy.bias
  refine sum_congr rfl fun w hw => ?_
  have hlen : w.length = t := mem_allWords.mp hw
  rw [wordCount_cylinder y t hlen, wordCount_cylinder y (t + 1) (by simp [hlen])]

/-! ### At the paper's scales -/

/-- The energy hypothesis at the scale `y`: at every depth `1 ≤ t < d(y) = ⌈C L(y)⌉`, the
bias energy is at most `(q - 1/2)² (y (log y)^{-B})² / 2^t`. -/
def EnergyBound (N₀ : ℕ) (C q B : ℝ) (y : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t < depth C N₀ y →
    biasEnergy y t ≤ (q - 1 / 2) ^ 2 * ((y : ℝ) / Real.log y ^ B) ^ 2 / 2 ^ t

/-- The energy hypothesis gives `H_q(C, A)` with exceptional atoms of mass `y (log y)^{-B}`,
for every `A`. -/
theorem oneSidedBoundExc_of_energy {N₀ : ℕ} {C q B : ℝ} {y : ℕ} (hq : 1 / 2 < q)
    (h : EnergyBound N₀ C q B y) (A : ℝ) : OneSided.OneSidedBoundExc N₀ C q A B y :=
  OneSided.OneSidedShareExc.mono_err (oneSidedShareExc_of_energy hq (by positivity) h)
    (by positivity)

/-- **The conjecture from the energy bound, with the contagion bound as a hypothesis.** -/
theorem energy_conj_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q B e : ℝ) (hC : 5 ≤ C)
    (hq : 1 / 2 < q) (hqp : q < pC C)
    (hB : C * Real.logb 2 (OneSided.tilt (pC C) q) + 1 + e < B)
    (he : e < OneSided.oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → EnergyBound N₀ C q B y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  obtain ⟨y₁, hy₁⟩ := hH
  exact OneSided.exc_conj_of_contagion hN hfloor C q
    (C * (1 + Real.logb 2 (OneSided.tilt (pC C) q)) + 1 + e + 1) B e hC (by linarith) hqp
    (by linarith) hB he ⟨y₁, fun y hy => oneSidedBoundExc_of_energy hq (hy₁ y hy) _⟩
    hlam0 hlam1 hlam hlow

/-- **The conjecture from the energy bound, with nothing else assumed.** If at all large
scales above a certified floor the bias energy at every depth `1 ≤ t < ⌈C L(y)⌉` is at most
`(q - 1/2)² y² (log y)^{-2B} / 2^t`, with `C ≥ 5`, `1/2 < q < p_C`, `B > C log₂ x + 1 + e` and
`7/10 < e < e_{C,q}`, then every positive integer reaches `1`. -/
theorem energy_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q B e : ℝ) (hC : 5 ≤ C)
    (hq : 1 / 2 < q) (hqp : q < pC C)
    (hB : C * Real.logb 2 (OneSided.tilt (pC C) q) + 1 + e < B)
    (he : e < OneSided.oneSidedExponent C q) (he7 : 7 / 10 < e)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → EnergyBound N₀ C q B y) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  obtain ⟨y₁, hy₁⟩ := hH
  exact OneSided.exc_implies_conjecture hN hfloor C q
    (C * (1 + Real.logb 2 (OneSided.tilt (pC C) q)) + 1 + e + 1) B e hC (by linarith) hqp
    (by linarith) hB he he7 ⟨y₁, fun y hy => oneSidedBoundExc_of_energy hq (hy₁ y hy) _⟩

end Energy

end Problems.Juggler
