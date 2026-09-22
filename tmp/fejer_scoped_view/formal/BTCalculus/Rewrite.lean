import BTCalculus.Integral
import BTCalculus.Algebra

namespace BTCalculus

open Representation.Words

/-- Soundness of ``D(I_a(x)) → x``. -/
theorem rewrite_D_I (a : Trit) (x : ℤ) : DZ (IZ a x) = x :=
  D_after_I a x

/-- Soundness of ``D(S(x)) → x``. -/
theorem rewrite_D_S (x : ℤ) : DZ (SZ x) = x :=
  D_after_S_int x

/-- Soundness of ``N(N(x)) → x``. -/
theorem rewrite_N_N (x : ℤ) : -(-x) = x :=
  neg_neg x

/-- Soundness of ``N(S(x)) → S(N(x))``. -/
theorem rewrite_N_S (x : ℤ) : -(SZ x) = SZ (-x) := by
  unfold SZ
  ring

/-- Soundness of ``I_0(x) → S(x)``. -/
theorem rewrite_I0_S (x : ℤ) : IZ Trit.zero x = SZ x := by
  simp [IZ, SZ, Trit.toInt]

/-- Soundness of ``N(I_-(x)) → I_+(N(x))``. -/
theorem rewrite_N_Im (x : ℤ) : -(IZ Trit.minus x) = IZ Trit.plus (-x) := by
  simp [IZ, Trit.toInt]
  ring

/-- Soundness of ``N(I_+(x)) → I_-(N(x))``. -/
theorem rewrite_N_Ip (x : ℤ) : -(IZ Trit.plus x) = IZ Trit.minus (-x) := by
  simp [IZ, Trit.toInt]
  ring

/-- Soundness of the tree rule ``N(D(x)) → D(N(x))``.

Newman confluence of the enlarged operator-fragment TRS is
``OpFrag.confluent`` / ``OpFrag.unique_normal_form`` in
``BTCalculus/OpFragNewman.lean``. -/
theorem rewrite_N_D (x : ℤ) : DZ (-x) = -(DZ x) := by
  have hx := decomp x
  have hnx := decomp (-x)
  have hlsd : lsdZ (-x) = -lsdZ x := by
    apply lsdZ_unique
    · rcases lsdZ_is_trit x with h | h | h <;> simp [h]
    · have := (lsdZ_mod x).neg
      simpa using this
  have : -x = -lsdZ x + 3 * (-DZ x) := by
    linarith [decomp x]
  have hdecomp := decomp (-x)
  have : DZ (-x) = (-x - lsdZ (-x)) / 3 := rfl
  rw [this, hlsd]
  have : -x - -lsdZ x = 3 * (-DZ x) := by
    linarith [decomp x]
  rw [this]
  exact Int.mul_ediv_cancel_left _ (by decide : (3 : ℤ) ≠ 0)

end BTCalculus
