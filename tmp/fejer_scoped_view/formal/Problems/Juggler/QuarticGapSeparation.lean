import Problems.Juggler.QuarticCells
import Problems.Juggler.CubicLogGrid

namespace Problems.Juggler.QuarticGapSeparation

open scoped BigOperators
open QuarticCells (B logEta)

/-!
A nonnegative transitive rotation cocycle gives an actual lower bound on
adjacent gaps. Exact integer B cells then exclude repeated cell values.
The sorted power-envelope construction is a separate interface.
-/

noncomputable def logError {L : ℕ} (c : Fin L → ℕ) (A : ℝ) (i : Fin L) : ℝ :=
  Real.log (Real.log (c i : ℝ)) - (i.val : ℝ) * A / (L : ℝ)

theorem adjacent_gap_lower {L : ℕ}
    (σ τ : Equiv.Perm (Fin L))
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcomm : Function.Commute σ τ) (w δ : Fin L → ℝ) (A Λ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hw : ∀ i, w (σ i) - w i = Λ / (L : ℝ) - δ i) (i : Fin L) :
    (A - ((L : ℝ) - 1) * Λ) / (L : ℝ) ≤
      w (τ i) - w i + A / (L : ℝ) := by
  have hb := (CubicGrid.adjacent_gap_bounds σ hσ τ hcomm w δ Λ
    (A / (L : ℝ)) hδ hsum hw i i).2
  have hl := (abs_le.mp hb).1
  have he : A / (L : ℝ) - (1 - 1 / (L : ℝ)) * Λ =
      (A - ((L : ℝ) - 1) * Λ) / (L : ℝ) := by
    have hn : (L : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)
    field_simp
  rw [← he]
  linarith

theorem logError_interior_gap {L : ℕ} [NeZero L]
    (c : Fin L → ℕ) (A : ℝ) {i j : Fin L} (hij : j.val = i.val + 1) :
    logError c A (finRotate L i) - logError c A i + A / (L : ℝ) =
      Real.log (Real.log (c j : ℝ)) - Real.log (Real.log (c i : ℝ)) := by
  have hr : finRotate L i = j := by
    apply Fin.ext
    rw [CubicGrid.finRotate_val, Nat.mod_eq_of_lt (by omega : i.val + 1 < L)]
    omega
  have hc : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij
  rw [hr]
  simp only [logError, hc]
  ring

theorem B_injective_of_adjacent_gaps {L m : ℕ} (c : Fin L → ℕ)
    (hmono : StrictMono c) (hm : 1 < m)
    (hmin : ∀ i, m ≤ c i) (hBmin : ∀ i, m ≤ B (c i))
    (hgap : ∀ i j : Fin L, j.val = i.val + 1 →
      logEta m ≤ Real.log (Real.log (c j : ℝ)) -
        Real.log (Real.log (c i : ℝ))) : Function.Injective (fun i => B (c i)) := by
  have impossible {i j : Fin L} (hij : i < j) (hcell : B (c i) = B (c j)) : False := by
    have hv : i.val + 1 < L := by have := j.isLt; exact lt_of_le_of_lt hij this
    let k : Fin L := ⟨i.val + 1, hv⟩
    have hik : i ≤ k := by simp only [Fin.le_def, k]; omega
    have hkj : k ≤ j := by
      have hval : i.val < j.val := hij
      change i.val + 1 ≤ j.val
      omega
    have hkcell : B (c k) = B (c i) := by
      apply le_antisymm
      · rw [hcell]
        exact QuarticCells.B_mono (hmono.monotone hkj)
      · exact QuarticCells.B_mono (hmono.monotone hik)
    have hlt := QuarticCells.same_cell_loglog_lt_min hm (hmin k) (hmin i)
      (hBmin i) hkcell rfl
    have hle := hgap i k rfl
    linarith
  intro i j hcell
  rcases lt_trichotomy i j with hij | heq | hji
  · exact False.elim (impossible hij hcell)
  · exact heq
  · exact False.elim (impossible hji hcell.symm)

theorem B_injective_of_cocycle {L m : ℕ} [NeZero L]
    (c : Fin L → ℕ) (hmono : StrictMono c) (hm : 1 < m)
    (hmin : ∀ i, m ≤ c i) (hBmin : ∀ i, m ≤ B (c i))
    (σ : Equiv.Perm (Fin L))
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcomm : Function.Commute σ (finRotate L)) (δ : Fin L → ℝ) (A Λ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hw : ∀ i, logError c A (σ i) - logError c A i = Λ / (L : ℝ) - δ i)
    (hsmall : ((L : ℝ) - 1) * Λ + (L : ℝ) * logEta m ≤ A) :
    Function.Injective (fun i => B (c i)) := by
  apply B_injective_of_adjacent_gaps c hmono hm hmin hBmin
  intro i j hij
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_neZero L
  have heta : logEta m ≤ (A - ((L : ℝ) - 1) * Λ) / (L : ℝ) := by
    apply (le_div_iff₀ hL).mpr
    nlinarith
  have hbound := adjacent_gap_lower σ (finRotate L) hσ hcomm (logError c A) δ A Λ
    hδ hsum hw i
  rw [logError_interior_gap c A hij] at hbound
  exact heta.trans hbound

theorem B_ge_of_lower_power {m x : ℕ} (h : m ^ 4 ≤ x ^ 3) : m ≤ B x := by
  by_contra hn
  have hcell := (ReturnCells.oe_cell x).2
  change x ^ 3 < (B x + 1) ^ 4 at hcell
  have hp := Nat.pow_le_pow_left (show B x + 1 ≤ m by omega) 4
  omega

theorem section_B_injective_of_cocycle {L m : ℕ} [NeZero L]
    (c : Fin L → ℕ) (hmono : StrictMono c) (hm : 1 < m)
    (hmin : ∀ i, m ≤ c i) (hsection : ∀ i, m ^ 4 ≤ c i ^ 3)
    (σ : Equiv.Perm (Fin L))
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcomm : Function.Commute σ (finRotate L)) (δ : Fin L → ℝ) (A Λ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hw : ∀ i, logError c A (σ i) - logError c A i = Λ / (L : ℝ) - δ i)
    (hsmall : ((L : ℝ) - 1) * Λ + (L : ℝ) * logEta m ≤ A) :
    Function.Injective (fun i => B (c i)) :=
  B_injective_of_cocycle c hmono hm hmin (fun i => B_ge_of_lower_power (hsection i))
    σ hσ hcomm δ A Λ hδ hsum hw hsmall

end Problems.Juggler.QuarticGapSeparation
