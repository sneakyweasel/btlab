import Representation.Words
import Operators.DigitDerivative
import BTCalculus.Trit

namespace BTCalculus

open Representation.Words
open Operators.DigitDerivative

/-- Balanced residue of an integer: ``n % 3`` mapped into ``{-1,0,+1}``. -/
def lsdZ (n : ℤ) : ℤ :=
  if n % 3 = 2 then (-1 : ℤ) else n % 3

def DZ (n : ℤ) : ℤ :=
  (n - lsdZ n) / 3

def SZ (n : ℤ) : ℤ :=
  3 * n

theorem emod3_bound (n : ℤ) : 0 ≤ n % 3 ∧ n % 3 < 3 := by
  refine ⟨Int.emod_nonneg n (by decide : (3 : ℤ) ≠ 0), ?_⟩
  exact Int.emod_lt_of_pos n (by decide : (0 : ℤ) < 3)

theorem emod3_cases (n : ℤ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  have h := emod3_bound n
  omega

theorem lsdZ_is_trit (n : ℤ) :
    lsdZ n = -1 ∨ lsdZ n = 0 ∨ lsdZ n = 1 := by
  unfold lsdZ
  rcases emod3_cases n with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

theorem minus_one_emod3 : (-1 : ℤ) % 3 = 2 := by decide

theorem lsdZ_mod (n : ℤ) : n ≡ lsdZ n [ZMOD 3] := by
  unfold lsdZ
  split_ifs with h
  · change n % 3 = (-1 : ℤ) % 3
    simp [h, minus_one_emod3]
  · change n % 3 = (n % 3) % 3
    simp

theorem trit_mod_unique {a b : ℤ}
    (ha : a = -1 ∨ a = 0 ∨ a = 1)
    (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (h : a ≡ b [ZMOD 3]) : a = b := by
  rcases ha with rfl | rfl | rfl
  · rcases hb with rfl | rfl | rfl
    · rfl
    · simp [Int.ModEq] at h
    · simp [Int.ModEq] at h
  · rcases hb with rfl | rfl | rfl
    · simp [Int.ModEq] at h
    · rfl
    · simp [Int.ModEq] at h
  · rcases hb with rfl | rfl | rfl
    · simp [Int.ModEq] at h
    · simp [Int.ModEq] at h
    · rfl

theorem lsdZ_unique {n a : ℤ}
    (ha : a = -1 ∨ a = 0 ∨ a = 1)
    (h : n ≡ a [ZMOD 3]) : lsdZ n = a := by
  have hn := lsdZ_mod n
  have ht := lsdZ_is_trit n
  exact trit_mod_unique ht ha (hn.symm.trans h)

theorem three_dvd_sub_lsd (n : ℤ) : (3 : ℤ) ∣ n - lsdZ n := by
  exact (Int.modEq_iff_dvd.mp (lsdZ_mod n).symm)

/-- Exact digit decomposition. -/
theorem decomp (n : ℤ) : n = lsdZ n + 3 * DZ n := by
  unfold DZ
  have hdvd := three_dvd_sub_lsd n
  have hmod : (n - lsdZ n) % 3 = 0 := Int.dvd_iff_emod_eq_zero.mp hdvd
  have hdiv := Int.ediv_mul_add_emod (n - lsdZ n) 3
  rw [hmod, add_zero] at hdiv
  linarith

theorem D_after_S_int (n : ℤ) : DZ (SZ n) = n := by
  unfold DZ SZ lsdZ
  have hmod : (3 * n) % 3 = 0 := by
    simp
  simp [hmod]

theorem S_after_D_int (n : ℤ) : SZ (DZ n) = n - lsdZ n := by
  unfold SZ
  have h := decomp n
  linarith

/-- Word-level ``D`` drops a freshly appended LSD. -/
theorem D_after_append (d : Trit) (w : List Trit) :
    dropLSD (w ++ [d]) = w :=
  dropLSD_snoc d w

end BTCalculus
