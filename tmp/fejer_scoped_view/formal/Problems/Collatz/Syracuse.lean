import Problems.Collatz.Accelerated
import Problems.Engine.ControlObstruction
import Problems.Engine.ControlWord
import Problems.Engine.ParameterDomain

namespace Problems.Collatz

/-- Adapter name for the accelerated odd-only map. Same definition as ``acceleratedT``. -/
abbrev syracuseS : ℕ → ℕ := acceleratedT

theorem syracuseS_mul (n : ℕ) :
    syracuseS n * 2 ^ padicValNat 2 (3 * n + 1) = 3 * n + 1 :=
  acceleratedT_mul n

theorem syracuseS_odd {n : ℕ} (hn : Odd n) (hpos : 0 < n) :
    Odd (syracuseS n) :=
  acceleratedT_odd hn hpos

/-- Exact one-point identity. Not a Collatz convergence theorem. -/
theorem syracuseS_one : syracuseS 1 = 1 := by
  have hmul := acceleratedT_mul 1
  have hval : padicValNat 2 (3 * 1 + 1) = 2 := by native_decide
  have : syracuseS 1 * 2 ^ 2 = 4 := by
    simpa [hval] using hmul
  omega

/-- Generic Engine iff specialized to ``q = 3x+1``. KNOWN arithmetic;
not a theorem that ``syracuseS`` equals the closed form on all odd
positives, and not a Collatz convergence result. -/
theorem syracuseS_parameter_iff
    {x : ℤ} {k : ℕ} (hq : (3 : ℤ) * x + 1 ≠ 0) :
    (∃ y : ℤ, (2 : ℤ) ^ k * y = 3 * x + 1 ∧ ¬ (2 : ℤ) ∣ y) ↔
      padicValInt 2 (3 * x + 1) = k :=
  Problems.Engine.mul_pow_eq_iff_padicValInt (b := 2) hq

/-- Two certified one-step clearing relations compose. KNOWN arithmetic
via the generic Engine lemma; not a cycle theorem and not convergence. -/
theorem syracuse_compose_two
    {k0 k1 : ℕ} {x0 x1 x2 : ℤ}
    (h0 : (2 : ℤ) ^ k0 * x1 = 3 * x0 + 1)
    (h1 : (2 : ℤ) ^ k1 * x2 = 3 * x1 + 1) :
    (2 : ℤ) ^ k0 * (2 : ℤ) ^ k1 * x2 =
      (3 : ℤ) * 3 * x0 + ((3 : ℤ) * 1 + (2 : ℤ) ^ k0 * 1) :=
  Problems.Engine.compose_two_affine h0 h1

/-- Length-one cycle constraint implies a divisibility condition. KNOWN
arithmetic via the generic Engine lemma; not a classification of cycles. -/
theorem syracuse_len_one_cycle_dvd {k : ℕ} {x : ℤ}
    (h : (2 : ℤ) ^ k * x = 3 * x + 1) :
    ((2 : ℤ) ^ k - 3) ∣ (1 : ℤ) :=
  Problems.Engine.cycle_constraint_dvd h

/-- Two-step remainder independent of the last exponent. KNOWN arithmetic
via the generic Engine lemma; not a cycle classification. -/
theorem syracuse_last_step_remainder
    {k0 k1 : ℕ} {x0 x1 x2 : ℤ}
    (h0 : (2 : ℤ) ^ k0 * x1 = 3 * x0 + 1)
    (h1 : (2 : ℤ) ^ k1 * x2 = 3 * x1 + 1) :
    (2 : ℤ) ^ k0 * (2 : ℤ) ^ k1 * x2 =
      (3 : ℤ) * 3 * x0 + ((3 : ℤ) * 1 + 1 * (2 : ℤ) ^ k0) :=
  Problems.Engine.last_step_remainder h0 h1

/-- Absolute-value cycle obstruction specialized to a two-step remainder.
KNOWN arithmetic; not a claim that all nontrivial cycles are excluded. -/
theorem syracuse_cycle_abs_obstruction
    {k0 k1 : ℕ} {x : ℤ}
    (hne : (3 : ℤ) * 1 + 1 * (2 : ℤ) ^ k0 ≠ 0)
    (hbound :
      |(3 : ℤ) * 1 + 1 * (2 : ℤ) ^ k0| <
        |(2 : ℤ) ^ k0 * (2 : ℤ) ^ k1 - 3 * 3|)
    (h : (2 : ℤ) ^ k0 * (2 : ℤ) ^ k1 * x =
      (3 : ℤ) * 3 * x + ((3 : ℤ) * 1 + 1 * (2 : ℤ) ^ k0)) :
    False :=
  Problems.Engine.cycle_abs_obstruction hne hbound h

/-- Two-step remainder elimination. KNOWN arithmetic via the generic
Engine lemma; not a cycle classification. -/
theorem syracuse_dvd_constant_of_dvd_remainder
    {k0 k1 : ℕ}
    (h : ((2 : ℤ) ^ k0 * (2 : ℤ) ^ k1 - 3 * 3) ∣ ((1 : ℤ) * (3 + (2 : ℤ) ^ k0))) :
    ((2 : ℤ) ^ k0 * (2 : ℤ) ^ k1 - 3 * 3) ∣
      ((1 : ℤ) * 3 * ((2 : ℤ) ^ k1 + 3)) :=
  Problems.Engine.dvd_constant_of_dvd_remainder (b := 2) (p := 3) (r := 1) h

end Problems.Collatz
