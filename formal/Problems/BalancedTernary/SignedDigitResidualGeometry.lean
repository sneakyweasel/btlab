import Problems.BalancedTernary.SignedDigitResidual

namespace Problems.BalancedTernary

open BTCalculus

/-!
Origin-reachable geometry of ``F_{λ,U_m}`` inside the finite envelope.
This file does not repeat the finite/infinite phase law.
-/

def foldSigned (gain : ℤ) : List ℤ → ℤ → ℤ
  | [], s => s
  | u :: rest, s => foldSigned gain rest (signedNext gain s u)

theorem foldSigned_nil (gain s : ℤ) : foldSigned gain [] s = s :=
  rfl

theorem foldSigned_append (gain s : ℤ) (left right : List ℤ) :
    foldSigned gain (left ++ right) s =
      foldSigned gain right (foldSigned gain left s) := by
  induction left generalizing s with
  | nil => simp [foldSigned]
  | cons u rest ih => simp [foldSigned, ih]

/-- One positive ``λ=1`` step: from ``k`` the letter ``2(k+1)`` reaches ``k+1``. -/
theorem lambda1_step_up (k : ℕ) :
    signedNext 1 (k : ℤ) (2 * ((k : ℤ) + 1)) = (k : ℤ) + 1 := by
  have hsum : (k : ℤ) + 2 * ((k : ℤ) + 1) = 3 * (k : ℤ) + 2 := by ring
  simp [signedNext, hsum, DZ_three_mul_add_two]

theorem lambda1_step_down (k : ℕ) :
    signedNext 1 (-(k : ℤ)) (-(2 * ((k : ℤ) + 1))) = -((k : ℤ) + 1) := by
  have hsum : -(k : ℤ) + -(2 * ((k : ℤ) + 1)) = -(3 * (k : ℤ) + 2) := by ring
  simp [signedNext]
  rw [hsum, DZ_neg, DZ_three_mul_add_two]
  ring

def lambda1Climb : ℕ → ℤ
  | 0 => 0
  | n + 1 => signedNext 1 (lambda1Climb n) (2 * ((n : ℤ) + 1))

theorem lambda1Climb_eq : ∀ n : ℕ, lambda1Climb n = n
  | 0 => rfl
  | n + 1 => by
    simp [lambda1Climb, lambda1Climb_eq n, lambda1_step_up]

def lambda1Word : ℕ → List ℤ
  | 0 => []
  | n + 1 => lambda1Word n ++ [2 * ((n : ℤ) + 1)]

theorem lambda1Word_fold (n : ℕ) :
    foldSigned 1 (lambda1Word n) 0 = lambda1Climb n := by
  induction n with
  | zero => simp [lambda1Word, lambda1Climb, foldSigned]
  | succ n ih =>
    simp [lambda1Word, lambda1Climb, foldSigned_append, ih, foldSigned]

theorem lambda1Word_abs_le {m n : ℕ} (h : n ≤ m / 2) :
    ∀ u ∈ lambda1Word n, u.natAbs ≤ m := by
  induction n with
  | zero => simp [lambda1Word]
  | succ n ih =>
    intro u hu
    have hn : n ≤ m / 2 := by omega
    simp [lambda1Word] at hu
    rcases hu with hu | hu
    · exact ih hn u hu
    · have : u = 2 * ((n : ℤ) + 1) := hu
      have h2 : 2 * (n + 1) ≤ m := by
        have : n + 1 ≤ m / 2 := h
        have : 2 * (n + 1) ≤ 2 * (m / 2) := Nat.mul_le_mul_left 2 this
        have : 2 * (m / 2) ≤ m := by omega
        omega
      subst hu
      simp
      exact_mod_cast h2

/-- Every nonnegative point of the ``λ=1`` box is reached by an admissible word. -/
theorem lambda1_interval_reachable (m n : ℕ) (h : n ≤ m / 2) :
    ∃ word : List ℤ, (∀ u ∈ word, u.natAbs ≤ m) ∧ foldSigned 1 word 0 = n := by
  refine ⟨lambda1Word n, lambda1Word_abs_le h, ?_⟩
  simpa [lambda1Climb_eq] using lambda1Word_fold n

theorem lambda1Word_neg_fold : ∀ n : ℕ,
    foldSigned 1 ((lambda1Word n).map (fun u => -u)) 0 = -lambda1Climb n
  | 0 => by simp [lambda1Word, lambda1Climb, foldSigned]
  | n + 1 => by
    rw [lambda1Word, List.map_append, foldSigned_append, lambda1Word_neg_fold n]
    simp [foldSigned]
    rw [lambda1Climb_eq n, lambda1_step_down]
    simp [lambda1Climb, lambda1Climb_eq n, lambda1_step_up]

/-- Every nonpositive point of the `lambda=1` box is reached by an admissible word;
the negative half of `lambda1_interval_reachable`. -/
theorem lambda1_interval_reachable_neg (m n : ℕ) (h : n ≤ m / 2) :
    ∃ word : List ℤ, (∀ u ∈ word, u.natAbs ≤ m) ∧
      foldSigned 1 word 0 = - (n : ℤ) := by
  refine ⟨(lambda1Word n).map (fun u => -u), ?_, ?_⟩
  · intro u hu
    rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
    simpa [Int.natAbs_neg] using lambda1Word_abs_le h v hv
  · simpa [lambda1Climb_eq] using lambda1Word_neg_fold n

/-- After one step the residual always lies on ``λℤ``. -/
theorem reachable_subset_lattice (gain s u : ℤ) :
    signedNext gain s u = gain * DZ (s + u) :=
  rfl

/-- One even ``λ=2`` step: from ``2k`` the letter ``k+2`` reaches ``2(k+1)``. -/
theorem lambda2_step_up (k : ℕ) :
    signedNext 2 (2 * (k : ℤ)) ((k : ℤ) + 2) = 2 * ((k : ℤ) + 1) := by
  have hsum : 2 * (k : ℤ) + ((k : ℤ) + 2) = 3 * (k : ℤ) + 2 := by ring
  simp [signedNext, hsum, DZ_three_mul_add_two]

def lambda2Climb : ℕ → ℤ
  | 0 => 0
  | n + 1 => signedNext 2 (lambda2Climb n) ((n : ℤ) + 2)

theorem lambda2Climb_eq : ∀ n : ℕ, lambda2Climb n = 2 * (n : ℤ)
  | 0 => by simp [lambda2Climb]
  | n + 1 => by
    simp [lambda2Climb, lambda2Climb_eq n, lambda2_step_up]

def lambda2Word : ℕ → List ℤ
  | 0 => []
  | n + 1 => lambda2Word n ++ [(n : ℤ) + 2]

theorem lambda2Word_fold (n : ℕ) :
    foldSigned 2 (lambda2Word n) 0 = lambda2Climb n := by
  induction n with
  | zero => simp [lambda2Word, lambda2Climb, foldSigned]
  | succ n ih =>
    simp [lambda2Word, lambda2Climb, foldSigned_append, ih, foldSigned]

theorem lambda2Word_abs_le {m n : ℕ} (h : n ≤ m.pred) :
    ∀ u ∈ lambda2Word n, u.natAbs ≤ m := by
  induction n with
  | zero => simp [lambda2Word]
  | succ n ih =>
    intro u hu
    have hn : n ≤ m.pred := Nat.le_of_succ_le h
    simp [lambda2Word] at hu
    rcases hu with hu | hu
    · exact ih hn u hu
    · have hu' : u = (n : ℤ) + 2 := hu
      rw [hu']
      have hnn : 0 ≤ (n : ℤ) + 2 := by omega
      have habs : ((n : ℤ) + 2).natAbs = n + 2 := by
        have := Int.natAbs_of_nonneg hnn
        exact_mod_cast this
      rw [habs]
      cases m with
      | zero =>
        simp at h
      | succ k =>
        simp [Nat.pred_succ] at h
        omega

/-- Every nonnegative even point of the sharp ``λ=2`` box is reached. -/
theorem lambda2_even_reachable (m n : ℕ) (h : n ≤ m.pred) :
    ∃ word : List ℤ, (∀ u ∈ word, u.natAbs ≤ m) ∧
      foldSigned 2 word 0 = 2 * (n : ℤ) := by
  refine ⟨lambda2Word n, lambda2Word_abs_le h, ?_⟩
  simpa [lambda2Climb_eq] using lambda2Word_fold n

/-- ``U={2}`` at ``λ=1``: the symmetric box is ``[-1,1]``, but ``-1`` is not hit. -/
theorem singleton_two_steps :
    signedNext 1 0 2 = 1 ∧ signedNext 1 1 2 = 1 := by
  native_decide

theorem singleton_two_misses_neg_one :
    (1 : ℤ) = signedNext 1 0 2 ∧ signedNext 1 0 2 ≠ -1 := by
  have h := singleton_two_steps
  omega

end Problems.BalancedTernary
