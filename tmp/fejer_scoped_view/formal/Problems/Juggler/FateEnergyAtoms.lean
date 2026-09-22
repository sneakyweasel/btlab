import Mathlib.Algebra.Order.Chebyshev
import Problems.Juggler.FateOneSidedAtoms
import Problems.Juggler.FateCylinderEnergy

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The bias energy of the bad cylinders supplies the exceptional atoms (Section 10(d))

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Section 10(d): "an additional
quantitative bound on these sums can supply an exceptional-atom estimate". This file is that
step, exactly, for the energy restricted to the `L`-bad words, which is where Paper C's
hypotheses live. The *bias energy* of a set `S` of words of length `t` is
`Σ_{w ∈ S} D(w)²` with `D(w) = #[wO] - #[w]/2` over the odd starts of `(y, 2y]`
(`Energy.energyOn`); over all words (`Energy.biasEnergy`) it is the paper's
`C_{t+1}/2 - C_t/4` by `CylinderEnergy.sum_bias_sq` (`Energy.biasEnergy_eq`), and over the
`L`-bad words it is `Energy.badEnergy`. The bad atoms that violate the share bound
`#[wO] ≤ q #[w]` for a share `q > 1/2` have `D(w) > (q - 1/2) #[w]`, so their squared masses
are bounded by the bad energy over `(q - 1/2)²`, and Cauchy–Schwarz over at most `2^t` atoms
bounds their total mass (`Energy.mass_violators_le`):

`(Σ_{w bad, violating} #[w])² ≤ 2^t · badEnergy / (q - 1/2)²`.

Hence `badEnergy(t) ≤ (q - 1/2)² exc² / 2^t` at every depth `1 ≤ t < d` gives the one-sided
hypothesis with exceptional atoms of mass `exc` and no error term
(`Energy.oneSidedShareExc_of_energy`), which `FateOneSidedAtoms` runs to the conjecture:
`Energy.energy_implies_conjecture` needs the bad energy bound with `exc = y (log y)^{-B}` at
the depths below `⌈C L(y)⌉` at all large scales (`Energy.EnergyBound`), `1/2 < q < p_C`,
`B > C log₂ x + 1 + e` and `27/40 < e < e_{C,q}`, and nothing else.

Why the restriction to bad words is not optional. An orbit that has reached `1` has an
all-`O` tail (`J(1) = 1` is odd), so its cylinder is fully biased at every later depth; the
exact enumeration of `research.juggler_sequence.cylinder_energy_measure` finds the
unrestricted energy at the worst-case value `C_t/4` from depth about `20` on at every scale
computed. The unrestricted bound (`badEnergy ≤ biasEnergy`, `Energy.badEnergy_le_biasEnergy`)
is a sufficient condition that nothing satisfies once a positive fraction of the starts has
reached `1` within `d(y)` steps. The bad-restricted statistic excludes exactly those orbits:
a start that has entered the floor has crossed the envelope (Lemma 8.1), so its word is not
bad. Nothing here proves the bad energy bound; it is Appendix C's question as a second
moment. Not a halt theorem.
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

/-- The bias `D(w) = #[wO] - #[w]/2` of a cylinder of depth `t` at the scale `y`. -/
noncomputable def bias (y t : ℕ) (w : List Branch) : ℝ :=
  ((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ) - (cylinder y t w).card / 2

/-- The bias energy `Σ_{w ∈ S} D(w)²` of a set of words of depth `t`. -/
noncomputable def energyOn (y t : ℕ) (S : Finset (List Branch)) : ℝ :=
  ∑ w ∈ S, bias y t w ^ 2

/-- The bias energy over all words of depth `t`. -/
noncomputable def biasEnergy (y t : ℕ) : ℝ := energyOn y t (allWords t)

/-- The bias energy over the `L`-bad words of depth `t`. -/
noncomputable def badEnergy (y : ℕ) (L : ℝ) (t : ℕ) : ℝ :=
  energyOn y t ((allWords t).filter (LBad L))

/-- The `L`-bad atoms of depth `t` that violate the share bound `#[wO] ≤ q #[w]`. -/
noncomputable def violators (y : ℕ) (L : ℝ) (t : ℕ) (q : ℝ) : Finset (List Branch) :=
  (allWords t).filter fun w =>
    LBad L w ∧ q * (cylinder y t w).card < ((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ)

theorem badEnergy_le_biasEnergy (y : ℕ) (L : ℝ) (t : ℕ) :
    badEnergy y L t ≤ biasEnergy y t :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)

/-- There are `2^t` words of length `t`. -/
theorem card_allWords : ∀ t, ((allWords t).card : ℝ) = 2 ^ t
  | 0 => by simp [allWords]
  | t + 1 => by
      have h := OneSided.sum_allWords_succ (fun _ => (1 : ℝ)) t
      simp only [sum_const, nsmul_eq_mul, mul_one] at h
      rw [h, card_allWords t]
      ring

/-- **Cauchy–Schwarz on the bad violators.** For a share `q > 1/2`,
`(Σ_{w bad, violating} #[w])² ≤ 2^t · badEnergy / (q - 1/2)²`. -/
theorem mass_violators_le (y : ℕ) (L : ℝ) (t : ℕ) {q : ℝ} (hq : 1 / 2 < q) :
    (∑ w ∈ violators y L t q, ((cylinder y t w).card : ℝ)) ^ 2
      ≤ 2 ^ t * (badEnergy y L t / (q - 1 / 2) ^ 2) := by
  have hε0 : 0 < q - 1 / 2 := by linarith
  -- a violator has `D(w) > (q - 1/2) #[w] ≥ 0`
  have hsq : ∀ w ∈ violators y L t q,
      ((cylinder y t w).card : ℝ) ^ 2 ≤ bias y t w ^ 2 / (q - 1 / 2) ^ 2 := by
    intro w hw
    rw [violators, mem_filter] at hw
    obtain ⟨-, -, hlt⟩ := hw
    rw [le_div_iff₀ (by positivity)]
    have hN0 : (0 : ℝ) ≤ (cylinder y t w).card := Nat.cast_nonneg _
    have hbias : (q - 1 / 2) * (cylinder y t w).card ≤ bias y t w := by
      unfold bias
      linarith
    have h0 : 0 ≤ (q - 1 / 2) * (cylinder y t w).card := mul_nonneg hε0.le hN0
    calc ((cylinder y t w).card : ℝ) ^ 2 * (q - 1 / 2) ^ 2
        = ((q - 1 / 2) * (cylinder y t w).card) ^ 2 := by ring
      _ ≤ bias y t w ^ 2 := pow_le_pow_left₀ h0 hbias 2
  have hcard : ((violators y L t q).card : ℝ) ≤ 2 ^ t := by
    rw [← card_allWords t]
    exact_mod_cast card_filter_le _ _
  have hsub : violators y L t q ⊆ (allWords t).filter (LBad L) := by
    intro w hw
    rw [violators, mem_filter] at hw
    rw [mem_filter]
    exact ⟨hw.1, hw.2.1⟩
  have hsum : ∑ w ∈ violators y L t q, ((cylinder y t w).card : ℝ) ^ 2
      ≤ badEnergy y L t / (q - 1 / 2) ^ 2 := by
    calc ∑ w ∈ violators y L t q, ((cylinder y t w).card : ℝ) ^ 2
        ≤ ∑ w ∈ violators y L t q, bias y t w ^ 2 / (q - 1 / 2) ^ 2 := sum_le_sum hsq
      _ = (∑ w ∈ violators y L t q, bias y t w ^ 2) / (q - 1 / 2) ^ 2 := by rw [sum_div]
      _ ≤ (∑ w ∈ (allWords t).filter (LBad L), bias y t w ^ 2) / (q - 1 / 2) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => sq_nonneg _)
      _ = badEnergy y L t / (q - 1 / 2) ^ 2 := rfl
  calc (∑ w ∈ violators y L t q, ((cylinder y t w).card : ℝ)) ^ 2
      ≤ (violators y L t q).card
          * ∑ w ∈ violators y L t q, ((cylinder y t w).card : ℝ) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ 2 ^ t * (badEnergy y L t / (q - 1 / 2) ^ 2) :=
        mul_le_mul hcard hsum (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)

/-- **Energy implies exceptional atoms.** If the bad energy at every depth `1 ≤ t < d` is at
most `(q - 1/2)² exc² / 2^t`, the bad violators of the share bound `#[wO] ≤ q #[w]` have total
mass at most `exc` at each depth, so the one-sided hypothesis holds with exceptional atoms of
mass `exc` and no error term. -/
theorem oneSidedShareExc_of_energy {y d : ℕ} {L q exc : ℝ} (hq : 1 / 2 < q) (hexc : 0 ≤ exc)
    (h : ∀ t, 1 ≤ t → t < d → badEnergy y L t ≤ (q - 1 / 2) ^ 2 * exc ^ 2 / 2 ^ t) :
    OneSided.OneSidedShareExc y L q 0 exc d := by
  intro t ht1 htd
  refine ⟨violators y L t q, ?_, ?_⟩
  · have hε0 : 0 < q - 1 / 2 := by linarith
    have hcs := mass_violators_le y L t hq
    have hb := h t ht1 htd
    have hfilter : (allWords t).filter (· ∈ violators y L t q) = violators y L t q := by
      rw [filter_mem_eq_inter]
      exact inter_eq_right.mpr (fun w hw => by rw [violators, mem_filter] at hw; exact hw.1)
    rw [hfilter]
    have hmass0 : 0 ≤ ∑ w ∈ violators y L t q, ((cylinder y t w).card : ℝ) :=
      sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hsq : (∑ w ∈ violators y L t q, ((cylinder y t w).card : ℝ)) ^ 2 ≤ exc ^ 2 := by
      calc (∑ w ∈ violators y L t q, ((cylinder y t w).card : ℝ)) ^ 2
          ≤ 2 ^ t * (badEnergy y L t / (q - 1 / 2) ^ 2) := hcs
        _ ≤ 2 ^ t * (((q - 1 / 2) ^ 2 * exc ^ 2 / 2 ^ t) / (q - 1 / 2) ^ 2) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb (by positivity))
              (by positivity)
        _ = exc ^ 2 := by
            have hne : q - 1 / 2 ≠ 0 := hε0.ne'
            have hne2 : q * 2 - 1 ≠ 0 := by intro h; linarith
            field_simp
    exact (pow_le_pow_iff_left₀ hmass0 hexc (by norm_num)).mp hsq
  · intro w hw hbad hwV
    rw [violators, mem_filter] at hwV
    push Not at hwV
    rw [add_zero]
    exact hwV hw hbad

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

/-- The unrestricted bias energy is the paper's `C_{t+1}/2 - C_t/4`, with
`C_t = Σ_{|w|=t} #[w]²` (`CylinderEnergy.sum_bias_sq`). -/
theorem biasEnergy_eq (y t : ℕ) :
    biasEnergy y t = CylinderEnergy.energy (cylinder y 0 []) (t + 1) / 2
      - CylinderEnergy.energy (cylinder y 0 []) t / 4 := by
  rw [← CylinderEnergy.sum_bias_sq]
  unfold biasEnergy energyOn bias CylinderEnergy.bias
  refine sum_congr rfl fun w hw => ?_
  have hlen : w.length = t := mem_allWords.mp hw
  rw [wordCount_cylinder y t hlen, wordCount_cylinder y (t + 1) (by simp [hlen])]

/-! ### At the paper's scales -/

/-- The energy hypothesis at the scale `y`: at every depth `1 ≤ t < d(y) = ⌈C L(y)⌉`, the
bias energy of the `L(y)`-bad words is at most `(q - 1/2)² (y (log y)^{-B})² / 2^t`. -/
def EnergyBound (N₀ : ℕ) (C q B : ℝ) (y : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t < depth C N₀ y →
    badEnergy y (scaleL N₀ y) t ≤ (q - 1 / 2) ^ 2 * ((y : ℝ) / Real.log y ^ B) ^ 2 / 2 ^ t

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
scales above a certified floor the bias energy of the `L(y)`-bad words at every depth
`1 ≤ t < ⌈C L(y)⌉` is at most `(q - 1/2)² y² (log y)^{-2B} / 2^t`, with `C ≥ 5`,
`1/2 < q < p_C`, `B > C log₂ x + 1 + e` and `27/40 < e < e_{C,q}`, then every positive integer
reaches `1`. -/
theorem energy_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q B e : ℝ) (hC : 5 ≤ C)
    (hq : 1 / 2 < q) (hqp : q < pC C)
    (hB : C * Real.logb 2 (OneSided.tilt (pC C) q) + 1 + e < B)
    (he : e < OneSided.oneSidedExponent C q) (he7 : 27 / 40 < e)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → EnergyBound N₀ C q B y) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  obtain ⟨y₁, hy₁⟩ := hH
  exact OneSided.exc_implies_conjecture hN hfloor C q
    (C * (1 + Real.logb 2 (OneSided.tilt (pC C) q)) + 1 + e + 1) B e hC (by linarith) hqp
    (by linarith) hB he he7 ⟨y₁, fun y hy => oneSidedBoundExc_of_energy hq (hy₁ y hy) _⟩

end Energy

end Problems.Juggler
