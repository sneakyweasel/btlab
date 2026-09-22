import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Problems.Engine.VectorAffine

namespace Problems.Engine

/-!
GENERIC THEOREM: recursive matrix-word composition and integer-image
obstructions. These are not Euclidean-algorithm theorems.
-/

/-- Prefix update ``M' = A M``, ``c' = A c + b``. -/
theorem recursive_matrix_word_step (A M : Mat2) (b c x : Vec2) :
    add2 (apply2 A (add2 (apply2 M x) c)) b =
      add2 (apply2 (mul2 A M) x) (add2 (apply2 A c) b) :=
  compose_two_vector_affine M A c b x

/-- If the second row of ``M - I`` vanishes and ``c.y ≠ 0``, there is no
integer cycle. -/
theorem kernel_row_cycle_impossible {M : Mat2} {c x : Vec2}
    (hc : (subM M id2).c = 0) (hd : (subM M id2).d = 0) (hy : c.y ≠ 0)
    (h : add2 (apply2 M x) c = x) : False := by
  have hcycle := cycle_of_vector_affine M c x h
  have hy2 := congrArg Vec2.y hcycle
  have hc' : M.c = 0 := by simpa [subM, id2] using hc
  have hd' : M.d - 1 = 0 := by simpa [subM, id2] using hd
  simp [apply2, subM, id2, neg2, hc'] at hy2
  have : (0 : ℤ) = -c.y := by
    simpa [hd'] using hy2
  exact hy (by linarith)

/-- A common divisor of every entry of ``M - I`` divides each coordinate
of ``c``. -/
theorem entry_gcd_divides_translation {M : Mat2} {c x : Vec2} {d : ℤ}
    (h : add2 (apply2 M x) c = x)
    (ha : d ∣ (subM M id2).a) (hb : d ∣ (subM M id2).b)
    (hc : d ∣ (subM M id2).c) (hd : d ∣ (subM M id2).d) :
    d ∣ c.x ∧ d ∣ c.y := by
  have hcycle := cycle_of_vector_affine M c x h
  constructor
  · have hdiv : d ∣ (subM M id2).a * x.x + (subM M id2).b * x.y :=
      dvd_add (dvd_mul_of_dvd_left ha x.x) (dvd_mul_of_dvd_left hb x.y)
    have hx := congrArg Vec2.x hcycle
    have : d ∣ (apply2 (subM M id2) x).x := by simpa [apply2] using hdiv
    have hneg : d ∣ (neg2 c).x := by
      rw [hx] at this
      exact this
    have hneg' : d ∣ -c.x := by simpa [neg2] using hneg
    exact Iff.mp dvd_neg hneg'
  · have hdiv : d ∣ (subM M id2).c * x.x + (subM M id2).d * x.y :=
      dvd_add (dvd_mul_of_dvd_left hc x.x) (dvd_mul_of_dvd_left hd x.y)
    have hy := congrArg Vec2.y hcycle
    have : d ∣ (apply2 (subM M id2) x).y := by simpa [apply2] using hdiv
    have hneg : d ∣ (neg2 c).y := by
      rw [hy] at this
      exact this
    have hneg' : d ∣ -c.y := by simpa [neg2] using hneg
    exact Iff.mp dvd_neg hneg'

theorem entry_gcd_cycle_impossible {M : Mat2} {c : Vec2} {d : ℤ}
    (ha : d ∣ (subM M id2).a) (hb : d ∣ (subM M id2).b)
    (hc : d ∣ (subM M id2).c) (hd : d ∣ (subM M id2).d)
    (hnd : ¬ d ∣ c.x) :
    ¬ ∃ x, add2 (apply2 M x) c = x := by
  rintro ⟨x, hx⟩
  exact hnd (entry_gcd_divides_translation hx ha hb hc hd).1

def shear (k : ℤ) : Mat2 := ⟨1, k, 0, 1⟩

def shearB : Vec2 := ⟨0, 1⟩

theorem shear_offset_y_succ (k : ℤ) (c : Vec2) :
    (add2 (apply2 (shear k) c) shearB).y = c.y + 1 := by
  simp [shear, shearB, apply2, add2]

theorem shear_sub_second_row (s : ℤ) :
    (subM (shear s) id2).c = 0 ∧ (subM (shear s) id2).d = 0 := by
  simp [shear, subM, id2]

/-- Shear with a nonzero vertical offset cannot close a cycle. -/
theorem shear_offset_y_cycle_impossible {s : ℤ} {c x : Vec2}
    (hy : c.y ≠ 0) (h : add2 (apply2 (shear s) x) c = x) : False :=
  kernel_row_cycle_impossible
    (shear_sub_second_row s).1 (shear_sub_second_row s).2 hy h

/-- Any shear word of positive vertical translation is cycle-impossible. -/
theorem shear_word_class_impossible {s n : ℤ} (hn : n ≠ 0) :
    ¬ ∃ x, add2 (apply2 (shear s) x) ⟨0, n⟩ = x := by
  rintro ⟨x, hx⟩
  exact shear_offset_y_cycle_impossible hn hx

end Problems.Engine
