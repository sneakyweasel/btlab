/-
Kernel family `t_n = (q_{n-1}, -q_{n-2}, 0)` on `F`, with unique integer
predecessor first coordinate. Unread-tail inequalities `lo(n) ≤ E_n ≤ hi(n)`
are not formalized here.

The integer reverse of `T_w` is `explicitPredecessor`
(`unique_predecessor`). On `F` this is `predecessor_on_F`. That is
inversion of `step`, not a bound on `L₀`.
-/

import Problems.Ostrowski.NP.Recurrence
import Problems.Ostrowski.NP.Residual

namespace Ostrowski.NP

/-- `q_{-1} = 0`, and `qPrev (k+1) = q k`. Avoids wrapping `Nat` at `n = 1`. -/
def qPrev : ℕ → ℤ
  | 0 => 0
  | n + 1 => q n

theorem qPrev_zero : qPrev 0 = 0 := rfl
theorem qPrev_succ (n : ℕ) : qPrev (n + 1) = q n := rfl

theorem qPrev_of_pos {n : ℕ} (hn : 0 < n) : qPrev n = q (n - 1) := by
  cases n with
  | zero => exact (lt_irrefl 0 hn).elim
  | succ n => rfl

/-- `t_n = (q_{n-1}, -q_{n-2}, 0)` for `n ≥ 1`. Matches Python `kernel_family_state`. -/
def kernelTarget (n : ℕ) (_hn : 0 < n) : State :=
  (q (n - 1), -qPrev (n - 1), 0)

theorem kernelTarget_fst (n : ℕ) (hn : 0 < n) :
    (kernelTarget n hn).1 = q (n - 1) :=
  rfl

theorem kernel_on_F (n : ℕ) (hn : 0 < n) : OnF (kernelTarget n hn) :=
  rfl

/-- Energy on `F`: `E_n(a,b,0) = a q_{n-2} + b q_{n-1}`. -/
def energyOnF (n : ℕ) (_hn : 0 < n) (s1 s2 : ℤ) : ℤ :=
  qPrev (n - 1) * s1 + q (n - 1) * s2

theorem kernel_energy_zero (n : ℕ) (hn : 0 < n) :
    energyOnF n hn (kernelTarget n hn).1 (kernelTarget n hn).2.1 = 0 := by
  simp [energyOnF, kernelTarget]
  ring

theorem kernel_ne_origin (n : ℕ) (hn : 0 < n) : kernelTarget n hn ≠ origin := by
  intro h
  have hf : (kernelTarget n hn).1 = origin.1 := congrArg Prod.fst h
  simp [kernelTarget, origin] at hf
  exact q_ne_zero (n - 1) hf

/-- Integer reverse of `T_w`, using Euclidean `ediv`. -/
def explicitPredecessor (t : State) (w : ℤ) : State :=
  (t.2.1 - t.1 / 3, t.2.2 + w - 2 * (t.1 / 3), t.1 / 3)

theorem step_s3 (w : ℤ) (s : State) : (step w s).1 = 3 * s.2.2 := by
  rcases s with ⟨_, _, _⟩
  rfl

/-- If `step w s = t` then `s` is the integer reverse `explicitPredecessor t w`:
the step map is invertible over the integers. Inversion of `step`, not a bound on `L_0`. -/
theorem unique_predecessor (w : ℤ) (s t : State) (h : step w s = t) :
    s = explicitPredecessor t w := by
  rcases s with ⟨s1, s2, s3⟩
  rcases t with ⟨t1, t2, t3⟩
  simp [step, explicitPredecessor] at h ⊢
  obtain ⟨h1, h23⟩ := h
  obtain ⟨h2, h3⟩ := h23
  have hs3 : s3 = t1 / 3 := by
    have : t1 = 3 * s3 := h1.symm
    rw [this, Int.mul_ediv_cancel_left s3 (by decide : (3 : ℤ) ≠ 0)]
  refine ⟨?_, ?_, hs3⟩
  · linarith
  · linarith

theorem predecessor_fst (w : ℤ) (s t : State) (h : step w s = t) :
    s.1 = t.2.1 - t.1 / 3 := by
  have := unique_predecessor w s t h
  rcases s with ⟨_, _, _⟩
  rcases t with ⟨_, _, _⟩
  simp [explicitPredecessor] at this
  exact this.1

/-- On `F`, the unique integer predecessor is `(b - a/3, w - 2(a/3), a/3)`.
KNOWN inversion of `step`, not `L₀`. -/
theorem predecessor_on_F (a b w : ℤ) (s : State)
    (h : step w s = (a, b, 0)) :
    s = (b - a / 3, w - 2 * (a / 3), a / 3) := by
  simpa [explicitPredecessor] using unique_predecessor w s (a, b, 0) h

/-- Shared first coordinate of every integer preimage of `t_n`. -/
def kernelPredFst (n : ℕ) (_hn : 0 < n) : ℤ :=
  -qPrev (n - 1) - q (n - 1) / 3

theorem kernel_pred_fst (n : ℕ) (hn : 0 < n) (w : ℤ) (s : State)
    (h : step w s = kernelTarget n hn) :
    s.1 = kernelPredFst n hn := by
  have := predecessor_fst w s (kernelTarget n hn) h
  simp [kernelPredFst, kernelTarget] at this ⊢
  exact this

theorem kernelPredFst_dvd_three_iff (n : ℕ) (hn : 0 < n)
    (hdvd : (3 : ℤ) ∣ q (n - 1)) :
    (3 : ℤ) ∣ kernelPredFst n hn ↔
      (9 : ℤ) ∣ q (n - 1) + 3 * qPrev (n - 1) := by
  obtain ⟨k, hk⟩ := hdvd
  have hdiv : q (n - 1) / 3 = k := by
    rw [hk, Int.mul_ediv_cancel_left k (by decide : (3 : ℤ) ≠ 0)]
  constructor
  · intro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    simp [kernelPredFst, hdiv] at hm
    linarith [hk]
  · intro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    simp [kernelPredFst, hdiv]
    linarith [hk]

end Ostrowski.NP
