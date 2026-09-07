import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ZMod.Basic

namespace Problems.Juggler

open Finset

/-!
# The depth-one main term: its exact arithmetic layer

Ledger row `J-depth-one-main-term` records that the first letter after an
odd start is exact.  Its proof has two tiers.  The analytic tier is the van
der Corput B-process with its remainders and an Erdős–Turán step, and stays
prose.  The tier below it is arithmetic and finite, and is what this file
proves:

* the B-process **dual of `F(M) = α M^{3/2}` is a cubic with rational
  coefficient**, namely `-4ν³/(27α²)` at the stationary point
  `M_ν = (2ν/3α)²` (`dual_phase`, `dual_phase_half`).  This is what makes
  the dual sum a complete cubic Gauss sum rather than a generic one, and it
  is exactly where the exponent `3/2` enters: its dual exponent is the
  integer `3`;
* at `α = 1/2` the modulus is `27` and the **complete cubic sum is `9`**
  (`completeCubicSum_eq_nine`).  The reason is structural rather than
  numerical: the six nonzero cube classes mod `27` fall into two triples in
  arithmetic progression of common difference `9`, and `ζ⁹` is a primitive
  cube root of unity, so each triple sums to zero;
* the main-term constant `(4√8/27)(3/4)^{3/2}` printed in the note is
  exactly **`√6/9`** (`depthOneConstant_eq_sqrt_six_div_nine`), a closed
  form the note does not record;
* the parity twist on odd starts shifts the dual frequency by `1/2`, and
  `2` is invertible modulo `27k²` for odd `k`, so the twisted and untwisted
  complete sums coincide (`sum_affine_reindex`, `two_isUnit`).  That
  coincidence is what cancels the two `X^{3/4}` terms over odd `M`.

Nothing here asserts the asymptotic itself.  The character convention
`e θ = exp(2πiθ)` matches the Hardy–Littlewood layer on prove2.me, so the
statements travel in both directions.
-/

/-- The standard additive character `e(θ) = exp(2πiθ)`. -/
noncomputable def e (θ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * θ)

@[simp] theorem e_zero : e 0 = 1 := by simp [e]

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [e, Complex.ofReal_add, mul_add]
  exact Complex.exp_add _ _

theorem e_pow (x : ℝ) (m : ℕ) : e x ^ m = e (m * x) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, ← e_add]
      push_cast
      ring_nf

/-- `e` kills the integers, so it is `1`-periodic. -/
theorem e_intCast (n : ℤ) : e n = 1 := by
  simp only [e]
  rw [Complex.exp_eq_one_iff]
  exact ⟨n, by push_cast; ring⟩

@[simp] theorem e_one : e 1 = 1 := by
  simpa using e_intCast 1

theorem e_sub_intCast (x : ℝ) (n : ℤ) : e (x - n) = e x := by
  have hx : x - (n : ℝ) + (n : ℝ) = x := by ring
  calc e (x - n) = e (x - n) * e n := by rw [e_intCast, mul_one]
    _ = e (x - n + n) := (e_add _ _).symm
    _ = e x := by rw [hx]

/-! ## The B-process dual is a rational cubic -/

/-- The stationary point of `α M^{3/2} - νM`: writing `M = s²` with `s ≥ 0`,
the phase derivative `(3/2)αs` equals `ν` exactly at `s = 2ν/(3α)`. -/
theorem stationary_point {α ν s : ℝ} (hα : α ≠ 0) :
    3 / 2 * α * s = ν ↔ s = 2 * ν / (3 * α) := by
  have h3 : (3 : ℝ) * α ≠ 0 := by simpa using hα
  rw [eq_div_iff h3]
  constructor
  · intro h; linear_combination 2 * h
  · intro h; linear_combination h / 2

/-- **The dual phase.**  At the stationary point `M_ν = s²`, `s = 2ν/(3α)`,
the Legendre value `α M_ν^{3/2} - ν M_ν` equals `-4ν³/(27α²)`: a cubic in
the dual variable with coefficient rational whenever `α` is. -/
theorem dual_phase {α ν s : ℝ} (hα : α ≠ 0) (hs : s = 2 * ν / (3 * α)) :
    α * s ^ 3 - ν * s ^ 2 = -4 * ν ^ 3 / (27 * α ^ 2) := by
  subst hs
  field_simp
  ring

/-- At `α = 1/2` the dual phase is `-16ν³/27`: modulus `27`. -/
theorem dual_phase_half (ν : ℝ) :
    -4 * ν ^ 3 / (27 * ((1 : ℝ) / 2) ^ 2) = -16 * ν ^ 3 / 27 := by
  rw [show (27 : ℝ) * ((1 : ℝ) / 2) ^ 2 = 27 / 4 by norm_num]
  ring

/-! ## The complete cubic sum at modulus 27 -/

/-- The primitive `27`-th root of unity used by the dual sum. -/
noncomputable def zeta27 : ℂ := e (1 / 27)

theorem zeta27_pow_27 : zeta27 ^ 27 = 1 := by
  rw [zeta27, e_pow, show ((27 : ℕ) : ℝ) * (1 / 27) = 1 by norm_num, e_one]

/-- Powers of `ζ` only see the exponent modulo `27`. -/
theorem zeta27_pow_mod (a : ℕ) : zeta27 ^ a = zeta27 ^ (a % 27) := by
  conv_lhs => rw [← Nat.div_add_mod a 27]
  rw [pow_add, pow_mul, zeta27_pow_27, one_pow, one_mul]

/-- `ζ⁹` is a primitive cube root of unity, so `1 + ζ⁹ + ζ¹⁸ = 0`.  This is
the whole reason the complete cubic sum is real and equal to `9`. -/
theorem zeta27_nine_sum : 1 + zeta27 ^ 9 + zeta27 ^ 18 = 0 := by
  have hcube : (zeta27 ^ 9) ^ 3 = 1 := by
    rw [← pow_mul]; exact zeta27_pow_27
  have hne : zeta27 ^ 9 ≠ 1 := by
    rw [zeta27, e_pow, e]
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2pi : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
    have hcancel : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((1 : ℂ) / 3)
        = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
      push_cast at hn ⊢
      linear_combination hn
    have hthird : (1 : ℂ) / 3 = (n : ℂ) := mul_left_cancel₀ h2pi hcancel
    have hthirdR : (1 : ℝ) / 3 = (n : ℝ) := by exact_mod_cast hthird
    have h3n : (3 : ℤ) * n = 1 := by
      have : (3 : ℝ) * (n : ℝ) = 1 := by linarith
      exact_mod_cast this
    omega
  have hfac : (zeta27 ^ 9 - 1) * (1 + zeta27 ^ 9 + zeta27 ^ 18) = 0 := by
    have hsq : zeta27 ^ 18 = (zeta27 ^ 9) ^ 2 := by rw [← pow_mul]
    rw [hsq]
    linear_combination hcube
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- Each term of the dual sum, as a power of `ζ` with reduced exponent. -/
theorem dual_term (r : ℕ) :
    e (-16 * (r : ℝ) ^ 3 / 27) = zeta27 ^ (11 * r ^ 3 % 27) := by
  have hsplit : -16 * (r : ℝ) ^ 3 / 27 = 11 * (r : ℝ) ^ 3 / 27 - ((r ^ 3 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hsplit, e_sub_intCast, ← zeta27_pow_mod, zeta27, e_pow]
  push_cast
  ring_nf

/-- **The complete cubic Gauss sum of the depth-one dual is `9`.**
`∑_{r mod 27} e(-16r³/27) = 9`.  Nine residues cube to `0`, and the
remaining eighteen contribute two triples in arithmetic progression of
difference `9`, each killed by `zeta27_nine_sum`. -/
theorem completeCubicSum_eq_nine :
    ∑ r ∈ range 27, e (-16 * (r : ℝ) ^ 3 / 27) = 9 := by
  have hterm : ∀ r ∈ range 27, e (-16 * (r : ℝ) ^ 3 / 27) = zeta27 ^ (11 * r ^ 3 % 27) :=
    fun r _ => dual_term r
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  linear_combination (3 * zeta27 ^ 2 + 3 * zeta27 ^ 7) * zeta27_nine_sum

/-! ## The main-term constant -/

/-- The constant the note prints, `(4√8/27)(3/4)^{3/2}`, written with the
half-power expanded. -/
noncomputable def depthOneConstant : ℝ :=
  4 * Real.sqrt 8 / 27 * (3 / 4 * Real.sqrt (3 / 4))

/-- **The constant is exactly `√6/9`.**  Numerically `0.2721655…`, matching
the four digits the note measures. -/
theorem depthOneConstant_eq_sqrt_six_div_nine :
    depthOneConstant = Real.sqrt 6 / 9 := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have h34 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
    rw [show (3 : ℝ) / 4 = 3 * (1 / 2) ^ 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
    ring
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
  rw [depthOneConstant, h8, h34, h6]
  ring

/-! ## The parity twist does not change a complete sum -/

/-- Reindexing a complete sum by an invertible affine substitution.  This is
the step the note calls "`2ν+1` runs over a complete residue system". -/
theorem sum_affine_reindex {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) (c : ZMod n)
    (f : ZMod n → ℂ) :
    ∑ x : ZMod n, f ((u : ZMod n) * x + c) = ∑ x : ZMod n, f x := by
  refine Fintype.sum_equiv ⟨fun x => (u : ZMod n) * x + c,
    fun y => (↑u⁻¹ : ZMod n) * (y - c), ?_, ?_⟩ _ _ (fun x => rfl)
  · intro x
    simp [← mul_assoc]
  · intro y
    simp [mul_sub, ← mul_assoc]

/-- `2` is invertible modulo `27k²` whenever `k` is odd: the modulus of the
twisted dual sum is odd, so the half-integer shift is a permutation. -/
theorem two_isUnit {k : ℕ} (hk : Odd k) : IsUnit (2 : ZMod (27 * k ^ 2)) := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  haveI : NeZero (27 * k ^ 2) := ⟨by positivity⟩
  have hodd : Odd (27 * k ^ 2) := (by decide : Odd 27).mul hk.pow
  have hmod : (27 * k ^ 2) % 2 = 1 := Nat.odd_iff.mp hodd
  have hnd : ¬ (2 ∣ 27 * k ^ 2) := by omega
  have hcop : Nat.Coprime 2 (27 * k ^ 2) := (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  have hu := (ZMod.isUnit_iff_coprime 2 (27 * k ^ 2)).mpr (by simpa using hcop)
  simpa using hu

end Problems.Juggler
