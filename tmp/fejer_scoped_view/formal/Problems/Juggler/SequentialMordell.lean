import Problems.Juggler.CycleDiophantine
import Problems.Juggler.GlobalDefect

namespace Problems.Juggler

/-!
# Consecutive odd near-Mordell steps

An odd Juggler step is the existing local identity
`x^3 = T(x)^2 + ρ` with `ρ < 2T(x)+1`. Two consecutive odd
steps give a second copy of the same identity. The polynomial
`(x^3-ρ)^3 = (z^2+σ)^2` is `y^6 = y^6`. The sequential defect
`x^9 - z^4` is `globalDefect` of the itinerary `OO`.

The peak slack `x^3 = (p^{2^r}+ε)^2 + δ` needs an even maximum.
A second odd step has an odd landing, so that law does not apply.

This file does not claim that every start reaches `1`.
-/

def oddMordellStep (x y ρ : ℕ) : Prop :=
  x % 2 = 1 ∧ floorPower x = y ∧ ρ = localDefectOdd x

def twoOddMordellSteps (x y z ρ σ : ℕ) : Prop :=
  oddMordellStep x y ρ ∧ oddMordellStep y z σ

def sequentialDefect (x z : ℕ) : ℕ :=
  x ^ 9 - z ^ 4

theorem oddMordellStep_add {x y ρ : ℕ} (h : oddMordellStep x y ρ) :
    x ^ 3 = y ^ 2 + ρ := by
  rcases h with ⟨hodd, hT, hρ⟩
  have hadd := localDefectOdd_add hodd
  simpa [hT, hρ] using hadd.symm

theorem oddMordellStep_lt {x y ρ : ℕ} (h : oddMordellStep x y ρ) :
    ρ < 2 * y + 1 := by
  rcases h with ⟨hodd, hT, hρ⟩
  have hlt := localDefectOdd_lt_succ hodd
  simpa [hT, hρ] using hlt

theorem oddMordellStep_iff {x y ρ : ℕ} :
    oddMordellStep x y ρ ↔
      x % 2 = 1 ∧ floorPower x = y ∧
        x ^ 3 = y ^ 2 + ρ ∧ ρ < 2 * y + 1 := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, oddMordellStep_add h, oddMordellStep_lt h⟩
  · intro ⟨hodd, hT, heq, _hlt⟩
    refine ⟨hodd, hT, ?_⟩
    have hρ : localDefectOdd x = x ^ 3 - y ^ 2 := by
      simp [localDefectOdd, hT]
    have hle : y ^ 2 ≤ x ^ 3 := by
      have := heq
      omega
    have : ρ = x ^ 3 - y ^ 2 := by
      have hsum := heq
      omega
    simpa [hρ] using this

/-- On an odd-to-odd step the remainder is even. The peak law
`peakOddDefect_odd` is the opposite parity, and needs an even max. -/
theorem odd_remainder_even {x y ρ : ℕ} (h : oddMordellStep x y ρ)
    (hy : y % 2 = 1) : ρ % 2 = 0 := by
  have heq := oddMordellStep_add h
  have hx3 : x ^ 3 % 2 = 1 := by simp [Nat.pow_mod, h.1]
  have hy2 : y ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hy]
  omega

/-- Substitution: both sides equal `y^6`. -/
theorem two_step_mordell_identity {x y z ρ σ : ℕ}
    (h : twoOddMordellSteps x y z ρ σ) :
    (x ^ 3 - ρ) ^ 3 = (z ^ 2 + σ) ^ 2 := by
  have heq1 := oddMordellStep_add h.1
  have heq2 := oddMordellStep_add h.2
  have hL : x ^ 3 - ρ = y ^ 2 := by
    rw [heq1]
    exact Nat.add_sub_cancel (y ^ 2) ρ
  have hR : z ^ 2 + σ = y ^ 3 := heq2.symm
  calc
    (x ^ 3 - ρ) ^ 3 = (y ^ 2) ^ 3 := by rw [hL]
    _ = y ^ 6 := by ring
    _ = (y ^ 3) ^ 2 := by ring
    _ = (z ^ 2 + σ) ^ 2 := by rw [hR]

theorem follows_oo {x y z : ℕ}
    (hx : x % 2 = 1) (hT : floorPower x = y)
    (hy : y % 2 = 1) (_hS : floorPower y = z) :
    follows x [.odd, .odd] := by
  refine ⟨hx, ?_⟩
  rw [hT]
  exact ⟨hy, trivial⟩

theorem image_oo {x y z : ℕ}
    (hT : floorPower x = y) (hS : floorPower y = z) :
    image x [.odd, .odd] = z := by
  simp [image, hT, hS]

/-- `Γ = x^9 - z^4` is the OO global defect. -/
theorem sequential_defect_eq_global {x z : ℕ}
    (hw : follows x [.odd, .odd]) (hz : image x [.odd, .odd] = z) :
    sequentialDefect x z = globalDefect x [.odd, .odd] := by
  have hid := global_defect_identity hw
  have hodd : oddCount [.odd, .odd] = 2 := by simp
  have hlen : ([.odd, .odd] : List Branch).length = 2 := by simp
  have hid' :
      x ^ 9 = z ^ 4 + globalDefect x [.odd, .odd] := by
    simpa [hodd, hlen, hz, pow_two] using hid
  unfold sequentialDefect
  rw [hid']
  exact Nat.add_sub_cancel_left (z ^ 4) _

theorem sequential_power_identity {x y z ρ σ : ℕ}
    (h : twoOddMordellSteps x y z ρ σ) :
    sequentialDefect x z = globalDefect x [.odd, .odd] := by
  have hx := h.1.1
  have hT := h.1.2.1
  have hy := h.2.1
  have hS := h.2.2.1
  exact sequential_defect_eq_global (follows_oo hx hT hy hS) (image_oo hT hS)

/-- Peak `δ` is odd only when the maximum is even. An odd-odd
Mordell landing makes `δ` even, so the peak slack is not this
sequential defect. -/
theorem peak_needs_even_max {x y : ℕ}
    (hodd : x % 2 = 1) (hT : floorPower x = y) (hy : y % 2 = 1) :
    peakOddDefect x y % 2 = 0 := by
  have hadd := peakOddDefect_add hodd hT
  have hx3 : x ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hodd]
  have hy2 : y ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hy]
  omega

theorem two_odd_steps_not_peak_shape {x y z ρ σ : ℕ}
    (h : twoOddMordellSteps x y z ρ σ) :
    y % 2 = 1 ∧ peakOddDefect x y % 2 = 0 :=
  ⟨h.2.1, peak_needs_even_max h.1.1 h.1.2.1 h.2.1⟩

end Problems.Juggler
