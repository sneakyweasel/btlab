import BTCalculus.Integral

namespace Problems.BalancedTernary

open BTCalculus
open Representation.Words

/-!
Integer iterates of ``F = N ∘ I_0 ∘ D``. The preferred family
``I_a ∘ D ∘ I_b`` collapses to ``I_a`` by ``D_after_I``. The surviving
word satisfies ``F² = P_0`` and every orbit has size at most 3.
-/

def signedP0 (n : ℤ) : ℤ :=
  -PZ Trit.zero n

theorem fab_eq_section (a b : Trit) (n : ℤ) :
    IZ a (DZ (IZ b n)) = IZ a n := by
  rw [D_after_I]

theorem PZ_zero_eq (n : ℤ) : PZ Trit.zero n = n - lsdZ n := by
  unfold PZ IZ
  simp [Trit.toInt]
  simpa [SZ] using S_after_D_int n

theorem signedP0_eq_lsd_sub (n : ℤ) : signedP0 n = lsdZ n - n := by
  unfold signedP0
  have h := PZ_zero_eq n
  linarith

theorem signedP0_eq_neg_P0 (n : ℤ) : signedP0 n = -PZ Trit.zero n :=
  rfl

theorem sub_lsd_mod (n : ℤ) : n - lsdZ n ≡ 0 [ZMOD 3] := by
  have h := Int.ModEq.sub (lsdZ_mod n) (Int.ModEq.refl (lsdZ n))
  simpa using h

theorem signedP0_mod (n : ℤ) : signedP0 n ≡ 0 [ZMOD 3] := by
  rw [signedP0_eq_lsd_sub]
  have h := Int.ModEq.sub (lsdZ_mod n).symm (Int.ModEq.refl n)
  simpa using h

theorem lsdZ_signedP0 (n : ℤ) : lsdZ (signedP0 n) = 0 :=
  lsdZ_unique (Or.inr (Or.inl rfl)) (signedP0_mod n)

theorem lsdZ_P0 (n : ℤ) : lsdZ (n - lsdZ n) = 0 :=
  lsdZ_unique (Or.inr (Or.inl rfl)) (sub_lsd_mod n)

theorem signedP0_sq_eq_P0 (n : ℤ) :
    signedP0 (signedP0 n) = PZ Trit.zero n := by
  rw [signedP0_eq_lsd_sub (signedP0 n), lsdZ_signedP0, zero_sub, signedP0_eq_lsd_sub]
  have h := PZ_zero_eq n
  linarith

theorem signedP0_cube_eq_self (n : ℤ) :
    signedP0 (signedP0 (signedP0 n)) = signedP0 n := by
  have hlsd := lsdZ_signedP0 (signedP0 n)
  rw [signedP0_eq_lsd_sub (signedP0 (signedP0 n)), hlsd, zero_sub, signedP0_sq_eq_P0]
  exact signedP0_eq_neg_P0 n

theorem signedP0_orbit_finite (n x : ℤ)
    (hx : x = n ∨ x = signedP0 n ∨ x = signedP0 (signedP0 n)) :
    signedP0 x = n ∨ signedP0 x = signedP0 n ∨
      signedP0 x = signedP0 (signedP0 n) := by
  rcases hx with h | h | h
  · subst h
    exact Or.inr (Or.inl rfl)
  · subst h
    exact Or.inr (Or.inr rfl)
  · subst h
    rw [signedP0_cube_eq_self]
    exact Or.inr (Or.inl rfl)

end Problems.BalancedTernary
