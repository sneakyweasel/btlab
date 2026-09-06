/-
Unread-tail energy of Γ_NP and the constructional step identity.

    E_i(s) = s₁ q_{i-2} + s₂ q_{i-1} + s₃ q_i

with `q_j = 0` for underflow, and

    E_{i-1}(T_w s) = E_i(s) - w q_{i-1}.

This is the covariance of the place-value recurrence with the residual
matrix `A`, not a bound on the live set `L₀`. The multi-step form

    E_n(fold w s) = E_{n+k}(s) - ∑_j w_j q_{n+k-1-j}

is KNOWN packaging of `energy_step`. From the origin, `E_i` is minus
the consumed prefix valuation. Acceptance at remaining 0 is that the
full difference word sums to 0.

The integer controls `w` with `E_{n-1}(T_w s)` in a fixed interval
are consecutive (`energy_control_interval`). That is not a bound on
`L₀`.

Homogeneous residual motion is energy-neutral in the sliding index
(`energy_homogeneous`): `E_n(A^k s) = E_{n+k}(s)`. Consecutive
adjoints are independent: `det(u_n,u_{n-1},u_{n-2}) = 3^{n-2}` for
`n ≥ 2` (`adjointDet_eq`). Neighboring energies invert `s` over `ℚ`.
That is not a bound on `L₀`.

From the origin the residual is the control particular
(`origin_particular`): `s_k = −∑ A^{k-1-j} e₃ w_j`. The impulse is
the place-value vector (`iterateA_e3`):
`A^r e₃ = (3 q_{r-1}, 3 q_{r-2}+q_{r-1}, q_r)`. That is the
Ostrowski convolution of `w` against `q`, not a bound on `L₀`.

The recurrence word `B* = [1, -2, -1, -3]` has MSD consumed sum
zero (`recurrence_word_zero`): `q_{n+3}-2q_{n+2}-q_{n+1}-3q_n = 0`.
That is `q_rec`, not a live expanding family.

From the origin, the third coordinate of the particular is minus
the consumed valuation (`particular_s3`):
`(particularSum ws).2.2 = -consumedSum ws.length ws`. So `val=0`
iff `c_B` lies on `F = {s₃ = 0}`. That does not force `c_B = 0`.

MSD concatenation splits at two starts (`consumedSum_append`).
Complete-word value is not a monoid:
`val(UV) = val(V) - E_{|V|}(c_U)` (`val_concat_energy`).

From any incoming residual, `(T_B(s))₃ = E_{|B|}(s) - val(B)`
(`fold_s3`). That is `energy_telescope` at remaining 0, not a
block transducer API.

The recurrence word is a reset (`recurrence_word_reset`):
`particularSum B* = 0`. Powers stay at the origin, so
`(B*)^k · (1,-2)` has particular the hub (`reset_pow_then_hub`).
An origin reset does not change the particular of a suffix
(`reset_prefix`): `T_R(0)=0` implies `T_{RU}(0)=T_U(0)`.
Equal unread-tail energy implies the same landing on `F`
(`same_energy_same_OnF`). Length-`n` suffix acceptance is
classified by `E_n`, not by the residual coordinates. That is
not a bound on `L₀`.
-/

import Problems.Ostrowski.NP.Recurrence
import Problems.Ostrowski.NP.Residual

namespace Ostrowski.NP

/-- `q_{n-k}` with value `0` when `k > n`. -/
def qShift (n k : ℕ) : ℤ :=
  if k ≤ n then q (n - k) else 0

theorem qShift_zero (n : ℕ) : qShift n 0 = q n := by
  simp [qShift]

theorem qShift_of_le {n k : ℕ} (h : k ≤ n) : qShift n k = q (n - k) := by
  simp [qShift, h]

theorem qShift_of_not_le {n k : ℕ} (h : ¬ k ≤ n) : qShift n k = 0 := by
  simp [qShift, h]

theorem qShift_one_of_pos {i : ℕ} (hi : 0 < i) : qShift i 1 = q (i - 1) := by
  have : 1 ≤ i := Nat.succ_le_of_lt hi
  simp [qShift, this]

/-- `E_i(s) = s₁ q_{i-2} + s₂ q_{i-1} + s₃ q_i`. -/
def energy (i : ℕ) : State → ℤ
  | (s1, s2, s3) => qShift i 2 * s1 + qShift i 1 * s2 + q i * s3

theorem energy_zero (s1 s2 s3 : ℤ) : energy 0 (s1, s2, s3) = s3 := by
  simp [energy, qShift, q]

/-- Coefficient row `u_i = (q_{i-2}, q_{i-1}, q_i)`. -/
def adjointU (i : ℕ) : ℤ × ℤ × ℤ :=
  (qShift i 2, qShift i 1, q i)

/-- Left action of
`A = [[0, 0, 3], [1, 0, 1], [0, 1, 2]]` on a row vector. -/
def mulRowA (u : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (u.2.1, u.2.2, 3 * u.1 + u.2.1 + 2 * u.2.2)

theorem energy_eq_dot (i : ℕ) (s1 s2 s3 : ℤ) :
    energy i (s1, s2, s3) =
      (adjointU i).1 * s1 + (adjointU i).2.1 * s2 + (adjointU i).2.2 * s3 :=
  rfl

private theorem adjoint_covariance_succ_succ (n : ℕ) :
    mulRowA (adjointU (n + 2)) = adjointU (n + 3) := by
  have h2 : 2 ≤ n + 2 := Nat.le_add_left 2 n
  have h2' : 2 ≤ n + 3 := Nat.le_add_left 2 (n + 1)
  have h1 : 1 ≤ n + 2 := Nat.le_add_left 1 (n + 1)
  have h1' : 1 ≤ n + 3 := Nat.le_add_left 1 (n + 2)
  simp [mulRowA, adjointU, qShift, h2, h2', h1, h1', q_rec n]
  ring

/-- `u_{i-1} A = u_i` for `i ≥ 1`. -/
theorem adjoint_covariance (i : ℕ) (hi : 0 < i) :
    mulRowA (adjointU (i - 1)) = adjointU i := by
  match i with
  | 0 => cases hi
  | 1 => simp [mulRowA, adjointU, qShift, q]
  | 2 => simp [mulRowA, adjointU, qShift, q]
  | n + 3 =>
    simpa using adjoint_covariance_succ_succ n

private theorem adjoint_components (i : ℕ) (hi : 0 < i) :
    qShift (i - 1) 1 = qShift i 2 ∧
      q (i - 1) = qShift i 1 ∧
        3 * qShift (i - 1) 2 + qShift (i - 1) 1 + 2 * q (i - 1) = q i := by
  have h := adjoint_covariance i hi
  simp [mulRowA, adjointU] at h
  exact h

/-- Constructional identity: `E_{i-1}(T_w s) = E_i(s) - w q_{i-1}`. -/
theorem energy_step (i : ℕ) (hi : 0 < i) (w s1 s2 s3 : ℤ) :
    energy (i - 1) (step w (s1, s2, s3)) =
      energy i (s1, s2, s3) - w * q (i - 1) := by
  obtain ⟨h1, h2, h3⟩ := adjoint_components i hi
  simp only [energy, step]
  rw [← h1, ← h2, ← h3]
  ring

theorem energy_step_state (i : ℕ) (hi : 0 < i) (w : ℤ) (s : State) :
    energy (i - 1) (step w s) = energy i s - w * q (i - 1) := by
  rcases s with ⟨s1, s2, s3⟩
  simpa using energy_step i hi w s1 s2 s3

/-- MSD word applied from the left: first control is the highest remaining place. -/
def foldSteps (ws : List ℤ) (s : State) : State :=
  ws.foldl (fun acc w => step w acc) s

theorem foldSteps_nil (s : State) : foldSteps [] s = s :=
  rfl

theorem foldSteps_cons (w : ℤ) (ws : List ℤ) (s : State) :
    foldSteps (w :: ws) s = foldSteps ws (step w s) :=
  rfl

/-- `∑_t ws[t] * q (start - 1 - t)`. Matches Python `consumed_sum`. -/
def consumedSum : ℕ → List ℤ → ℤ
  | _, [] => 0
  | start, w :: rest => w * q (start - 1) + consumedSum (start - 1) rest

/-- After an MSD word of length `k` from remaining `n+k`,
`E_n(fold s) = E_{n+k}(s) - ∑_j w_j q_{n+k-1-j}`.

KNOWN packaging of `energy_step`, not a bound on `L₀`. -/
theorem energy_telescope (n : ℕ) (ws : List ℤ) (s : State) :
    energy n (foldSteps ws s) =
      energy (n + ws.length) s - consumedSum (n + ws.length) ws := by
  induction ws generalizing n s with
  | nil =>
    simp [foldSteps, consumedSum]
  | cons w rest ih =>
    have hlen : n + (w :: rest).length = n + rest.length + 1 := by
      simp [List.length_cons, Nat.add_assoc]
    rw [foldSteps_cons, hlen, ih, consumedSum]
    have hsub : n + rest.length + 1 - 1 = n + rest.length :=
      Nat.add_sub_cancel _ _
    have hstep := energy_step_state (n + rest.length + 1) (Nat.succ_pos _) w s
    simp [hsub] at hstep ⊢
    rw [hstep]
    ring

/-- MSD recurrence word `B* = (1,-2,-1,-3)`.
`val(B*) = q_{n+3}-2q_{n+2}-q_{n+1}-3q_n = 0`. KNOWN `q_rec`, not `L₀`. -/
def recurrenceWord : List ℤ :=
  [1, -2, -1, -3]

theorem recurrence_word_zero (n : ℕ) :
    consumedSum (n + 4) recurrenceWord = 0 := by
  have h4 : n + 4 - 1 = n + 3 := by omega
  have h3 : n + 3 - 1 = n + 2 := by omega
  have h2 : n + 2 - 1 = n + 1 := by omega
  have h1 : n + 1 - 1 = n := Nat.add_sub_cancel n 1
  simp [consumedSum, recurrenceWord, h4, h3, h2, h1]
  rw [q_rec]
  ring

/-- The set of integer controls `w` with `E_{n-1}(T_w s)` in a fixed
interval `[lo, hi]` is consecutive. This is `energy_step` plus `q > 0`,
not a bound on `L₀`. -/
theorem energy_control_interval (n : ℕ) (hn : 0 < n) (lo hi w₁ w₂ w : ℤ)
    (s : State)
    (h1 : lo ≤ energy (n - 1) (step w₁ s) ∧ energy (n - 1) (step w₁ s) ≤ hi)
    (h2 : lo ≤ energy (n - 1) (step w₂ s) ∧ energy (n - 1) (step w₂ s) ≤ hi)
    (hw₁ : w₁ ≤ w) (hw₂ : w ≤ w₂) :
    lo ≤ energy (n - 1) (step w s) ∧ energy (n - 1) (step w s) ≤ hi := by
  have hq : (0 : ℤ) < q (n - 1) := q_pos (n - 1)
  have hq' : (0 : ℤ) ≤ q (n - 1) := le_of_lt hq
  rw [energy_step_state n hn w₁ s] at h1
  rw [energy_step_state n hn w₂ s] at h2
  rw [energy_step_state n hn w s]
  have hmul₁ : w₁ * q (n - 1) ≤ w * q (n - 1) :=
    Int.mul_le_mul_of_nonneg_right hw₁ hq'
  have hmul₂ : w * q (n - 1) ≤ w₂ * q (n - 1) :=
    Int.mul_le_mul_of_nonneg_right hw₂ hq'
  constructor
  · have : energy n s - w₂ * q (n - 1) ≤ energy n s - w * q (n - 1) := by
      linarith
    linarith [h2.1]
  · have : energy n s - w * q (n - 1) ≤ energy n s - w₁ * q (n - 1) := by
      linarith
    linarith [h1.2]

/-- `∑ q`-weights of a zero word vanish. -/
theorem consumedSum_replicate_zero (start k : ℕ) :
    consumedSum start (List.replicate k 0) = 0 := by
  induction k generalizing start with
  | zero => simp [consumedSum]
  | succ k ih =>
    simp [consumedSum, List.replicate_succ, ih]

/-- Homogeneous motion `A^k = T_0^k` preserves energy in the sliding
index: `E_n(A^k s) = E_{n+k}(s)`. This is `energy_telescope` on the
zero word, not a bound on `L₀`. -/
theorem energy_homogeneous (n k : ℕ) (s : State) :
    energy n (foldSteps (List.replicate k 0) s) = energy (n + k) s := by
  have h := energy_telescope n (List.replicate k 0) s
  simpa [consumedSum_replicate_zero, List.length_replicate] using h

/-- Determinant of three row vectors. -/
def tripleDet (u v w : ℤ × ℤ × ℤ) : ℤ :=
  u.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1) -
    u.2.1 * (v.1 * w.2.2 - v.2.2 * w.1) +
      u.2.2 * (v.1 * w.2.1 - v.2.1 * w.1)

/-- `det(u_n, u_{n-1}, u_{n-2})`. -/
def adjointDet (n : ℕ) : ℤ :=
  tripleDet (adjointU n) (adjointU (n - 1)) (adjointU (n - 2))

theorem adjointU_ge_two (n : ℕ) (hn : 2 ≤ n) :
    adjointU n = (q (n - 2), q (n - 1), q n) := by
  have h1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 2) hn
  simp [adjointU, qShift, hn, h1]

private theorem adjointDet_two : adjointDet 2 = 1 := by
  simp [adjointDet, tripleDet, adjointU, qShift, q]

private theorem adjointDet_three : adjointDet 3 = 3 := by
  simp [adjointDet, tripleDet, adjointU, qShift, q, q_rec]

private theorem adjointDet_succ_of_four (n : ℕ) (hn : 4 ≤ n) :
    adjointDet (n + 1) = 3 * adjointDet n := by
  have h2n : 2 ≤ n := by omega
  have h2n1 : 2 ≤ n - 1 := by omega
  have h2n2 : 2 ≤ n - 2 := by omega
  have h2np1 : 2 ≤ n + 1 := by omega
  have hsub1 : n + 1 - 1 = n := by omega
  have hsub2 : n + 1 - 2 = n - 1 := by omega
  have hrec : q (n + 1) = 2 * q n + q (n - 1) + 3 * q (n - 2) := by
    have hleft : q (n + 1) = q ((n - 2) + 3) := by
      congr 1
      omega
    rw [hleft, q_rec]
    have hy : n - 2 + 2 = n := by omega
    have hz : n - 2 + 1 = n - 1 := by omega
    rw [hy, hz]
  have hrec_n : q n = 2 * q (n - 1) + q (n - 2) + 3 * q (n - 3) := by
    have hleft : q n = q ((n - 3) + 3) := by
      congr 1
      omega
    rw [hleft, q_rec]
    have hy : n - 3 + 2 = n - 1 := by omega
    have hz : n - 3 + 1 = n - 2 := by omega
    rw [hy, hz]
  have hrec_nm1 : q (n - 1) = 2 * q (n - 2) + q (n - 3) + 3 * q (n - 4) := by
    have hleft : q (n - 1) = q ((n - 4) + 3) := by
      congr 1
      omega
    rw [hleft, q_rec]
    have hy : n - 4 + 2 = n - 2 := by omega
    have hz : n - 4 + 1 = n - 3 := by omega
    rw [hy, hz]
  have hU_np1 : adjointU (n + 1) = (q (n - 1), q n, q (n + 1)) := by
    rw [adjointU_ge_two (n + 1) h2np1]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · have : n + 1 - 2 = n - 1 := hsub2
      simp [this]
    · have : n + 1 - 1 = n := hsub1
      simp [this]
  have hU_n : adjointU n = (q (n - 2), q (n - 1), q n) :=
    adjointU_ge_two n h2n
  have hU_nm1 : adjointU (n - 1) = (q (n - 3), q (n - 2), q (n - 1)) := by
    rw [adjointU_ge_two (n - 1) h2n1]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · have : n - 1 - 2 = n - 3 := by omega
      simp [this]
    · have : n - 1 - 1 = n - 2 := by omega
      simp [this]
  have hU_nm2 : adjointU (n - 2) = (q (n - 4), q (n - 3), q (n - 2)) := by
    rw [adjointU_ge_two (n - 2) h2n2]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · have : n - 2 - 2 = n - 4 := by omega
      simp [this]
    · have : n - 2 - 1 = n - 3 := by omega
      simp [this]
  rw [adjointDet, adjointDet, hsub1, hsub2, hU_np1, hU_n, hU_nm1, hU_nm2,
    hrec, hrec_n, hrec_nm1]
  unfold tripleDet
  ring

private theorem adjointDet_succ (n : ℕ) (hn : 2 ≤ n) :
    adjointDet (n + 1) = 3 * adjointDet n := by
  rcases n with (_ | _ | _ | _ | m)
  · omega
  · omega
  · simp [adjointDet_two, adjointDet_three]
  · have h4 : adjointDet 4 = 9 := by
      simp [adjointDet, tripleDet, adjointU, qShift, q, q_rec]
    simp [adjointDet_three, h4]
  · exact adjointDet_succ_of_four (m + 4) (by omega)

/-- Consecutive adjoints are independent: `det = 3^{n-2}` for `n ≥ 2`.
Neighboring energies invert `s` over `ℚ`. Not a bound on `L₀`. -/
theorem adjointDet_eq (n : ℕ) (hn : 2 ≤ n) :
    adjointDet n = (3 : ℤ) ^ (n - 2) := by
  have h : ∀ k : ℕ, adjointDet (k + 2) = (3 : ℤ) ^ k := by
    intro k
    induction k with
    | zero =>
      simpa using adjointDet_two
    | succ k ih =>
      have hk : 2 ≤ k + 2 := Nat.le_add_left _ _
      have hidx : k + 1 + 2 = k + 2 + 1 := by omega
      rw [hidx, adjointDet_succ (k + 2) hk, ih, pow_succ, mul_comm]
  have := h (n - 2)
  have hn2 : n - 2 + 2 = n := by omega
  rwa [hn2] at this

theorem adjointDet_ne_zero (n : ℕ) (hn : 2 ≤ n) : adjointDet n ≠ 0 := by
  rw [adjointDet_eq n hn]
  exact pow_ne_zero _ (by decide)

def addState (s t : State) : State :=
  (s.1 + t.1, s.2.1 + t.2.1, s.2.2 + t.2.2)

def subState (s t : State) : State :=
  (s.1 - t.1, s.2.1 - t.2.1, s.2.2 - t.2.2)

def smulState (k : ℤ) (s : State) : State :=
  (k * s.1, k * s.2.1, k * s.2.2)

/-- Homogeneous residual matrix `A`. `step 0 = A`. -/
def applyA (s : State) : State :=
  step 0 s

def iterateA : ℕ → State → State
  | 0, s => s
  | n + 1, s => applyA (iterateA n s)

def e3 : State :=
  (0, 0, 1)

theorem addState_origin (s : State) : addState s origin = s := by
  rcases s with ⟨s1, s2, s3⟩
  simp [addState, origin]

theorem addState_origin_left (s : State) : addState origin s = s := by
  rcases s with ⟨s1, s2, s3⟩
  simp [addState, origin]

theorem iterateA_origin (k : ℕ) : iterateA k origin = origin := by
  induction k with
  | zero =>
    rfl
  | succ k ih =>
    simp [iterateA]
    rw [ih]
    simp [applyA, step, origin]

theorem addState_comm (s t : State) : addState s t = addState t s := by
  rcases s with ⟨_,_,_⟩
  rcases t with ⟨_,_,_⟩
  simp [addState, add_comm]

private theorem prod3_eq {a b c a' b' c' : ℤ}
    (h1 : a = a') (h2 : b = b') (h3 : c = c') :
    ((a, b, c) : State) = (a', b', c') := by
  simp [h1, h2, h3]

theorem applyA_add (s t : State) :
    applyA (addState s t) = addState (applyA s) (applyA t) := by
  rcases s with ⟨s1, s2, s3⟩
  rcases t with ⟨t1, t2, t3⟩
  simp only [applyA, addState, step]
  apply prod3_eq <;> ring

theorem applyA_smul (k : ℤ) (s : State) :
    applyA (smulState k s) = smulState k (applyA s) := by
  rcases s with ⟨s1, s2, s3⟩
  simp only [applyA, smulState, step]
  apply prod3_eq <;> ring

theorem applyA_sub (s t : State) :
    applyA (subState s t) = subState (applyA s) (applyA t) := by
  rcases s with ⟨s1, s2, s3⟩
  rcases t with ⟨t1, t2, t3⟩
  simp only [applyA, subState, step]
  apply prod3_eq <;> ring

theorem iterateA_add (n : ℕ) (s t : State) :
    iterateA n (addState s t) = addState (iterateA n s) (iterateA n t) := by
  induction n generalizing s t with
  | zero =>
    simp [iterateA]
  | succ n ih =>
    simp [iterateA, ih, applyA_add]

theorem iterateA_smul (n : ℕ) (k : ℤ) (s : State) :
    iterateA n (smulState k s) = smulState k (iterateA n s) := by
  induction n generalizing s with
  | zero =>
    simp [iterateA]
  | succ n ih =>
    simp [iterateA, ih, applyA_smul]

theorem iterateA_sub (n : ℕ) (s t : State) :
    iterateA n (subState s t) = subState (iterateA n s) (iterateA n t) := by
  induction n generalizing s t with
  | zero =>
    simp [iterateA]
  | succ n ih =>
    simp [iterateA, ih, applyA_sub]

theorem iterateA_applyA (n : ℕ) (s : State) :
    iterateA n (applyA s) = iterateA (n + 1) s := by
  induction n generalizing s with
  | zero =>
    simp [iterateA]
  | succ n ih =>
    simp [iterateA, ih]

theorem step_affine (w : ℤ) (s : State) :
    step w s = subState (applyA s) (smulState w e3) := by
  rcases s with ⟨s1, s2, s3⟩
  simp [step, applyA, subState, smulState, e3]

theorem step_origin (w : ℤ) : step w origin = smulState (-w) e3 := by
  simp [step, origin, smulState, e3]

theorem addState_sub_smul (s : State) (w : ℤ) (t u : State) :
    addState (subState s (smulState w t)) u =
      addState s (addState (smulState (-w) t) u) := by
  rcases s with ⟨_,_,_⟩
  rcases t with ⟨_,_,_⟩
  rcases u with ⟨_,_,_⟩
  simp only [addState, subState, smulState]
  apply prod3_eq <;> ring

theorem addState_neg_smul (w : ℤ) (t p : State) :
    addState (smulState (-w) t) p = subState p (smulState w t) := by
  rcases t with ⟨_,_,_⟩
  rcases p with ⟨_,_,_⟩
  simp only [addState, subState, smulState]
  apply prod3_eq <;> ring

/-- Affine unfolding: `T_ws(s) = A^{|ws|} s + T_ws(0)`. -/
theorem foldSteps_affine (ws : List ℤ) (s : State) :
    foldSteps ws s =
      addState (iterateA ws.length s) (foldSteps ws origin) := by
  induction ws generalizing s with
  | nil =>
    simp [foldSteps, iterateA, addState_origin]
  | cons w rest ih =>
    calc
      foldSteps (w :: rest) s
          = foldSteps rest (step w s) :=
            foldSteps_cons w rest s
      _ = addState (iterateA rest.length (step w s)) (foldSteps rest origin) :=
            ih (step w s)
      _ = addState
            (iterateA rest.length (subState (applyA s) (smulState w e3)))
            (foldSteps rest origin) := by
            rw [step_affine]
      _ = addState
            (subState (iterateA rest.length (applyA s))
              (iterateA rest.length (smulState w e3)))
            (foldSteps rest origin) := by
            rw [iterateA_sub]
      _ = addState
            (subState (iterateA (rest.length + 1) s)
              (smulState w (iterateA rest.length e3)))
            (foldSteps rest origin) := by
            rw [iterateA_applyA, iterateA_smul]
      _ = addState (iterateA (rest.length + 1) s)
            (addState (smulState (-w) (iterateA rest.length e3))
              (foldSteps rest origin)) :=
            addState_sub_smul _ _ _ _
      _ = addState (iterateA (w :: rest).length s)
            (addState (smulState (-w) (iterateA rest.length e3))
              (foldSteps rest origin)) := by
            simp [List.length_cons]
      _ = addState (iterateA (w :: rest).length s)
            (addState (iterateA rest.length (smulState (-w) e3))
              (foldSteps rest origin)) := by
            rw [← iterateA_smul]
      _ = addState (iterateA (w :: rest).length s)
            (addState (iterateA rest.length (step w origin))
              (foldSteps rest origin)) := by
            rw [← step_origin]
      _ = addState (iterateA (w :: rest).length s)
            (foldSteps rest (step w origin)) := by
            rw [← ih (step w origin)]
      _ = addState (iterateA (w :: rest).length s)
            (foldSteps (w :: rest) origin) := by
            rw [foldSteps_cons]

/-- Control particular from the origin:
`s = −∑_j A^{k-1-j} e₃ w_j`. KNOWN variation of constants, not `L₀`. -/
def particularSum : List ℤ → State
  | [] => origin
  | w :: rest =>
      subState (particularSum rest) (smulState w (iterateA rest.length e3))

theorem origin_particular (ws : List ℤ) :
    foldSteps ws origin = particularSum ws := by
  induction ws with
  | nil =>
    simp [foldSteps, particularSum]
  | cons w rest ih =>
    have haff := foldSteps_affine rest (step w origin)
    rw [foldSteps_cons, haff, step_origin, iterateA_smul, ih]
    simp only [particularSum]
    exact addState_neg_smul w (iterateA rest.length e3) (particularSum rest)

theorem energy_origin (i : ℕ) : energy i origin = 0 := by
  simp [energy, origin]

theorem energy_zero_state (s : State) : energy 0 s = s.2.2 := by
  rcases s with ⟨s1, s2, s3⟩
  simpa using energy_zero s1 s2 s3

/-- From the origin, `(c_B)₃ = -val(B)`. KNOWN energy at `n=0`, not `L₀`. -/
theorem particular_s3 (ws : List ℤ) :
    (particularSum ws).2.2 = -consumedSum ws.length ws := by
  have tel := energy_telescope 0 ws origin
  rw [origin_particular, energy_zero_state] at tel
  simp [energy_origin] at tel
  simpa using tel

/-- From any start state, `(T_B(s))₃ = E_{|B|}(s) - val(B)`.
KNOWN `energy_telescope` at remaining 0, not `L₀`. -/
theorem fold_s3 (ws : List ℤ) (s : State) :
    (foldSteps ws s).2.2 =
      energy ws.length s - consumedSum ws.length ws := by
  have tel := energy_telescope 0 ws s
  rw [energy_zero_state] at tel
  simpa using tel

/-- Length-`n` suffix acceptance is classified by the energy, not by residual
coordinates: `foldSteps ws s` lands on `F` exactly when `energy |ws| s` equals the
consumed sum of `ws`. -/
theorem fold_on_F_iff (ws : List ℤ) (s : State) :
    OnF (foldSteps ws s) ↔
      energy ws.length s = consumedSum ws.length ws := by
  constructor
  · intro h
    have hs3 := fold_s3 ws s
    simp [OnF] at h
    linarith
  · intro h
    have hs3 := fold_s3 ws s
    simp [OnF]
    linarith

/-- Length-`|ws|` landing on `F` is classified by `E_{|ws|}`, not by `s`.
KNOWN `fold_on_F_iff`, not a Myhill–Nerode calculus and not `L₀`. -/
theorem same_energy_same_OnF (ws : List ℤ) (s t : State)
    (h : energy ws.length s = energy ws.length t) :
    OnF (foldSteps ws s) ↔ OnF (foldSteps ws t) := by
  simp [fold_on_F_iff, h]

theorem foldSteps_append (u v : List ℤ) (s : State) :
    foldSteps (u ++ v) s = foldSteps v (foldSteps u s) := by
  simp [foldSteps, List.foldl_append]

/-- Concatenation of particulars: `c_{UV} = A^{|V|} c_U + c_V`. -/
theorem particular_concat (u v : List ℤ) :
    particularSum (u ++ v) =
      addState (iterateA v.length (particularSum u)) (particularSum v) := by
  rw [← origin_particular, ← origin_particular, ← origin_particular,
    foldSteps_append]
  exact foldSteps_affine v (foldSteps u origin)

/-- Origin reset prefixes do not change the particular of a suffix.
KNOWN `particular_concat` at `c_R=0`, not `L₀`. -/
theorem reset_prefix (r u : List ℤ) (hr : particularSum r = origin) :
    particularSum (r ++ u) = particularSum u := by
  rw [particular_concat, hr, iterateA_origin, addState_origin_left]

theorem energy_add (i : ℕ) (s t : State) :
    energy i (addState s t) = energy i s + energy i t := by
  rcases s with ⟨s1, s2, s3⟩
  rcases t with ⟨t1, t2, t3⟩
  simp only [energy, addState]
  ring

theorem iterateA_eq_fold_zero (k : ℕ) (s : State) :
    iterateA k s = foldSteps (List.replicate k 0) s := by
  induction k generalizing s with
  | zero =>
    simp [iterateA, foldSteps]
  | succ k ih =>
    rw [List.replicate_succ, foldSteps_cons, ← ih (step 0 s)]
    simpa [applyA] using (iterateA_applyA k s).symm

theorem energy_iterateA (n k : ℕ) (s : State) :
    energy n (iterateA k s) = energy (n + k) s := by
  rw [iterateA_eq_fold_zero]
  exact energy_homogeneous n k s

/-- Two-start MSD split. Not `val(U) + C val(V)`. KNOWN, not `L₀`. -/
theorem consumedSum_append (n : ℕ) (u v : List ℤ) :
    consumedSum (n + u.length + v.length) (u ++ v) =
      consumedSum (n + u.length + v.length) u +
        consumedSum (n + v.length) v := by
  induction u generalizing n with
  | nil =>
    simp [consumedSum]
  | cons w rest ih =>
    have hidx : n + (w :: rest).length + v.length =
        n + rest.length + v.length + 1 := by
      simp [List.length_cons]
      omega
    have hsub : n + (w :: rest).length + v.length - 1 =
        n + rest.length + v.length := by
      rw [hidx]
      omega
    have hL :
        consumedSum (n + (w :: rest).length + v.length) ((w :: rest) ++ v) =
          w * q (n + (w :: rest).length + v.length - 1) +
            consumedSum (n + (w :: rest).length + v.length - 1)
              (rest ++ v) := by
      simp [List.cons_append, consumedSum]
    have hR :
        consumedSum (n + (w :: rest).length + v.length) (w :: rest) =
          w * q (n + (w :: rest).length + v.length - 1) +
            consumedSum (n + (w :: rest).length + v.length - 1) rest :=
      rfl
    rw [hL, hR, hsub, ih n]
    ring

/-- `val(UV) = val(V) - E_{|V|}(c_U)`. KNOWN packaging, not `L₀`. -/
theorem val_concat_energy (u v : List ℤ) :
    consumedSum (u ++ v).length (u ++ v) =
      consumedSum v.length v - energy v.length (particularSum u) := by
  have hs3 := particular_s3 (u ++ v)
  have hcat := particular_concat u v
  have hlin := energy_add 0 (iterateA v.length (particularSum u)) (particularSum v)
  have hA : energy 0 (iterateA v.length (particularSum u)) =
      energy v.length (particularSum u) := by
    simpa using energy_iterateA 0 v.length (particularSum u)
  have hv := particular_s3 v
  have hz := energy_zero_state (particularSum (u ++ v))
  have hzv := energy_zero_state (particularSum v)
  have hcoord :
      (particularSum (u ++ v)).2.2 =
        energy v.length (particularSum u) + (particularSum v).2.2 := by
    rw [← hz, hcat, hlin, hA, hzv]
  rw [hs3, hv] at hcoord
  linarith

theorem val_concat_zero_iff (u v : List ℤ) :
    consumedSum (u ++ v).length (u ++ v) = 0 ↔
      energy v.length (particularSum u) = consumedSum v.length v := by
  have h := val_concat_energy u v
  constructor <;> intro <;> linarith

theorem val_zero_on_F (ws : List ℤ)
    (h : consumedSum ws.length ws = 0) : OnF (particularSum ws) := by
  simp [OnF, particular_s3, h]

theorem reset_val_zero (ws : List ℤ) (h : particularSum ws = origin) :
    consumedSum ws.length ws = 0 := by
  have hs3 := particular_s3 ws
  simp [h, origin] at hs3
  linarith

/-- Hub `(1,-2) ↦ (-3,-1,0)`. Regression, not infinitude. -/
theorem hub_nonreset :
    particularSum [1, -2] = (-3, -1, 0) ∧
      ((-3 : ℤ), -1, 0) ≠ origin ∧
      consumedSum 2 [1, -2] = 0 := by
  refine ⟨?eq, ?ne, ?val⟩
  · simp [particularSum, iterateA, applyA, step, e3, origin, smulState, subState]
  · simp [origin]
  · simp [consumedSum, q]

/-- `B*` is a reset. KNOWN four-step evaluation, not `L₀`. -/
theorem recurrence_word_reset : particularSum recurrenceWord = origin := by
  rw [← origin_particular]
  simp [foldSteps, recurrenceWord, step, origin]

/-- `(B*)^k` stays at the origin. KNOWN packaging of the reset, not `L₀`. -/
theorem reset_pow_origin (k : ℕ) :
    particularSum (List.replicate k recurrenceWord).flatten = origin := by
  induction k with
  | zero =>
    simp [particularSum]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, particular_concat,
      recurrence_word_reset, iterateA_origin, addState_origin_left, ih]

/-- `(B*)^k · (1,-2)` has particular the hub. Not a bound on `L₀`. -/
theorem reset_pow_then_hub (k : ℕ) :
    particularSum ((List.replicate k recurrenceWord).flatten ++ [1, -2]) =
      (-3, -1, 0) := by
  rw [reset_prefix _ _ (reset_pow_origin k)]
  exact hub_nonreset.1

/-- Complete-word zero-value is not a monoid. Witness `(1,-2)(1,-2)`. -/
theorem complete_zero_not_monoid :
    consumedSum 2 [1, -2] = 0 ∧
      consumedSum 4 ([1, -2] ++ [1, -2]) ≠ 0 := by
  constructor
  · simp [consumedSum, q]
  · have h3 : q 3 = 15 := by
      rw [show (3 : ℕ) = 0 + 3 from rfl, q_rec]
      simp [q]
    simp [consumedSum, q, h3]

/-- Impulse `A^r e₃` as a place-value triple. Underflow of `q` is 0. -/
def impulsePlace (r : ℕ) : State :=
  (3 * qShift r 1, 3 * qShift r 2 + qShift r 1, q r)

theorem qShift_succ_one (n : ℕ) : qShift (n + 1) 1 = q n := by
  have : 1 ≤ n + 1 := Nat.le_add_left 1 n
  simp [qShift, this]

theorem qShift_succ_two (n : ℕ) : qShift (n + 1) 2 = qShift n 1 := by
  by_cases h : 1 ≤ n
  · have h2 : 2 ≤ n + 1 := by omega
    simp [qShift, h2, h]
  · have : n = 0 := by omega
    subst this
    simp [qShift]

theorem q_succ_impulse (n : ℕ) :
    q (n + 1) = 3 * qShift n 2 + qShift n 1 + 2 * q n := by
  match n with
  | 0 =>
    simp [qShift, q]
  | 1 =>
    simp [qShift, q]
  | n + 2 =>
    have h1 : 1 ≤ n + 2 := by omega
    have h2 : 2 ≤ n + 2 := by omega
    simp [qShift, h1, h2]
    rw [q_rec]
    ring

/-- `A^r e₃ = (3 q_{r-1}, 3 q_{r-2}+q_{r-1}, q_r)`.
KNOWN place-value dictionary for `origin_particular`, not `L₀`. -/
theorem iterateA_e3 (r : ℕ) : iterateA r e3 = impulsePlace r := by
  induction r with
  | zero =>
    simp [iterateA, e3, impulsePlace, qShift, q]
  | succ n ih =>
    have hA :
        applyA (impulsePlace n) = impulsePlace (n + 1) := by
      simp [applyA, step, impulsePlace, qShift_succ_one, qShift_succ_two,
        q_succ_impulse]
    simpa [iterateA, ih] using hA

end Ostrowski.NP
