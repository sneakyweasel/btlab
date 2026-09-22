import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Generic 2-dimensional vector-affine algebra over ``ℤ``.

GENERIC THEOREM: composition and the cycle identity are integer
matrix algebra. They are not Euclidean-algorithm theorems and not
map theorems on a dynamical system.

EUCLIDEAN SPECIALIZATION / KNOWN MATHEMATICS: ``euclideanMatrix``
records the usual quotient step ``(a,b) ↦ (b, a - q b)``.
-/

structure Vec2 where
  x : ℤ
  y : ℤ
deriving Repr

structure Mat2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving Repr

def apply2 (M : Mat2) (v : Vec2) : Vec2 :=
  ⟨M.a * v.x + M.b * v.y, M.c * v.x + M.d * v.y⟩

def mul2 (C A : Mat2) : Mat2 :=
  ⟨C.a * A.a + C.b * A.c, C.a * A.b + C.b * A.d,
   C.c * A.a + C.d * A.c, C.c * A.b + C.d * A.d⟩

def add2 (u v : Vec2) : Vec2 := ⟨u.x + v.x, u.y + v.y⟩

def subM (M N : Mat2) : Mat2 :=
  ⟨M.a - N.a, M.b - N.b, M.c - N.c, M.d - N.d⟩

def id2 : Mat2 := ⟨1, 0, 0, 1⟩

def neg2 (v : Vec2) : Vec2 := ⟨-v.x, -v.y⟩

def det2 (M : Mat2) : ℤ := M.a * M.d - M.b * M.c

/-- ``z = C(Ax + b) + d = (CA)x + (Cb + d)``. -/
theorem compose_two_vector_affine (A C : Mat2) (b d x : Vec2) :
    add2 (apply2 C (add2 (apply2 A x) b)) d =
      add2 (apply2 (mul2 C A) x) (add2 (apply2 C b) d) := by
  simp [apply2, mul2, add2]
  constructor <;> ring

/-- Closing ``Mx + c = x`` yields ``(M - I)x = -c``. -/
theorem cycle_of_vector_affine (M : Mat2) (c x : Vec2)
    (h : add2 (apply2 M x) c = x) :
    apply2 (subM M id2) x = neg2 c := by
  have hx := congrArg Vec2.x h
  have hy := congrArg Vec2.y h
  simp [apply2, subM, id2, add2, neg2] at hx hy ⊢
  constructor <;> linarith

/-- Cramer's first coordinate: ``Δ x = s u - q v``. -/
theorem vector_cycle_cramer_x (M : Mat2) (c x : Vec2)
    (h : apply2 (subM M id2) x = neg2 c) :
    det2 (subM M id2) * x.x =
      (subM M id2).d * (-c.x) - (subM M id2).b * (-c.y) := by
  have hx := congrArg Vec2.x h
  have hy := congrArg Vec2.y h
  simp [apply2, subM, id2, neg2, det2] at hx hy ⊢
  linear_combination (M.d - 1) * hx - M.b * hy

theorem vector_cycle_dvd (M : Mat2) (c x : Vec2)
    (h : add2 (apply2 M x) c = x)
    (_hne : det2 (subM M id2) ≠ 0) :
    det2 (subM M id2) ∣
      ((subM M id2).d * (-c.x) - (subM M id2).b * (-c.y)) := by
  refine ⟨x.x, ?_⟩
  have hc := vector_cycle_cramer_x M c x (cycle_of_vector_affine M c x h)
  exact hc.symm

/-- If the Cramer numerator is not divisible by ``Δ ≠ 0``, there is no
integer cycle solution. -/
theorem vector_cycle_impossible {M : Mat2} {c : Vec2}
    (hne : det2 (subM M id2) ≠ 0)
    (hnd : ¬ det2 (subM M id2) ∣
      ((subM M id2).d * (-c.x) - (subM M id2).b * (-c.y))) :
    ¬ ∃ x, add2 (apply2 M x) c = x := by
  rintro ⟨x, hx⟩
  exact hnd (vector_cycle_dvd M c x hx hne)

/-- Shear matrices compose by adding the off-diagonal parameter. -/
theorem shear_compose (k m : ℤ) :
    mul2 ⟨1, m, 0, 1⟩ ⟨1, k, 0, 1⟩ = ⟨1, k + m, 0, 1⟩ := by
  simp [mul2]

/-- Inconsistent 2×2 cycle for a shear with nonzero offset. -/
theorem shear_offset_inconsistent {k y : ℤ}
    (h : k * y = -1 ∧ (0 : ℤ) = -1) : False := by
  omega

/-! EUCLIDEAN SPECIALIZATION. KNOWN MATHEMATICS: the quotient step. -/

def euclideanMatrix (q : ℤ) : Mat2 := ⟨0, 1, 1, -q⟩

theorem euclidean_step_matrix (a b q r : ℤ) (h : a = q * b + r) :
    apply2 (euclideanMatrix q) ⟨a, b⟩ = ⟨b, r⟩ := by
  simp [euclideanMatrix, apply2, h]

end Problems.Engine
