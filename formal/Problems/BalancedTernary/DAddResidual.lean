import BTCalculus.Algebra
import BTCalculus.Normalization

namespace Problems.BalancedTernary

open BTCalculus

/-!
Residual completion of ``D(x+y)``. The unary factorization through
``(D(x),D(y))`` is already ``add_not_DLocal``. This file records the
discovered residual ``D(lsd x + lsd y)``, its 3-state streaming
closure, and the obstruction to using ``lsd(x+y)`` alone.
-/

def dAddNext (s a b : ℤ) : ℤ :=
  DZ (s + a + b)

def dAddOut (s a b : ℤ) : ℤ :=
  lsdZ (s + a + b)

/-- The carry of `addDigit a b` on trits is `D (a + b)`. -/
theorem addDigit_snd_eq_DZ {a b : ℤ} (ha : isTrit a) (hb : isTrit b) :
    (addDigit a b).2 = DZ (a + b) := by
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp [ha, hb, addDigit, DZ, lsdZ]

/-- After discovery, the residual agrees with the existing two-digit table. -/
theorem dAdd_eq_addDigit {a b : ℤ} (ha : isTrit a) (hb : isTrit b) :
    dAddNext 0 a b = (addDigit a b).2 ∧
      dAddOut 0 a b = (addDigit a b).1 := by
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp [dAddNext, dAddOut, ha, hb, addDigit, DZ, lsdZ]

/-- Residual-aware replacement for the rejected tree rule ``D(x+y)→D(x)+D(y)``. -/
theorem dAdd_repaired (x y : ℤ) :
    DZ (x + y) = DZ x + DZ y + DZ (lsdZ x + lsdZ y) := by
  rw [D_add]
  exact congrArg (fun t => DZ x + DZ y + t)
    (addDigit_snd_eq_DZ (lsdZ_is_trit x) (lsdZ_is_trit y))

/-- The three fibre values `D(0+0) = 0`, `D(1+1) = 1`, `D(-1 + -1) = -1`. -/
theorem dAdd_fiber_three :
    DZ (0 + 0) = 0 ∧
      DZ (1 + 1) = 1 ∧
      DZ ((-1 : ℤ) + (-1)) = -1 ∧
      DZ (0 : ℤ) = 0 ∧
      DZ (1 : ℤ) = 0 ∧
      DZ (-1) = 0 := by
  native_decide

/-- On the slice ``D(x)=D(y)=0``, the observable ``D(x+y)`` takes three
values, so no 1-state or 2-state residual can repair locality. -/
theorem dAdd_minimal_residual :
    DZ 0 = DZ 1 ∧ DZ 1 = DZ (-1) ∧
      DZ (0 + 0) ≠ DZ (1 + 1) ∧
      DZ (1 + 1) ≠ DZ ((-1 : ℤ) + (-1)) ∧
      DZ (0 + 0) ≠ DZ ((-1 : ℤ) + (-1)) := by
  native_decide

def DLocalLsdSum (H : ℤ → ℤ → ℤ) : Prop :=
  ∃ G : ℤ → ℤ → ℤ → ℤ, ∀ x y, H x y = G (DZ x) (DZ y) (lsdZ (x + y))

/-- ``R = lsd(x+y)`` is not a sufficient residual. Witness ``(1,1)`` vs ``(0,-1)``. -/
theorem dAdd_not_lsd_sum_local : ¬ DLocalLsdSum fun x y => DZ (x + y) := by
  rintro ⟨G, hG⟩
  have h11 := hG 1 1
  have h0m := hG (0 : ℤ) (-1)
  have d1 : DZ (1 : ℤ) = 0 := by native_decide
  have d0 : DZ (0 : ℤ) = 0 := by native_decide
  have dm : DZ (-1) = 0 := by native_decide
  have l11 : lsdZ ((1 : ℤ) + 1) = -1 := by native_decide
  have l0m : lsdZ ((0 : ℤ) + (-1)) = -1 := by native_decide
  have h2 : DZ ((1 : ℤ) + 1) = 1 := by native_decide
  have hm1 : DZ ((0 : ℤ) + (-1)) = 0 := by native_decide
  simp [d1, d0, dm, l11, l0m, h2, hm1] at h11 h0m
  exact absurd (h11.trans h0m.symm) (by decide : (1 : ℤ) ≠ 0)

/-- On the diagonal `a = b` the residual step is `D (s + 2a)`. -/
theorem dAdd_diagonal (s a : ℤ) :
    dAddNext s a a = DZ (s + 2 * a) := by
  simp [dAddNext]
  ring_nf

/-- Closure: if `s`, `a`, `b` are trits then `dAddNext s a b` is a trit. -/
theorem dAdd_residual_closure {s a b : ℤ}
    (hs : isTrit s) (ha : isTrit a) (hb : isTrit b) :
    isTrit (dAddNext s a b) := by
  rcases hs with hs | hs | hs <;> rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb <;>
      (simp [dAddNext, hs, ha, hb, isTrit, DZ, lsdZ]; try native_decide)

/-- The emitted digit of the residual step is always a trit. -/
theorem dAdd_out_is_trit (s a b : ℤ) :
    isTrit (dAddOut s a b) :=
  lsdZ_is_trit (s + a + b)

end Problems.BalancedTernary
