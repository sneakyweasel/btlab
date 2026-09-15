/-
# Why the jump amplitudes repeat: a step that costs nothing

`J-sturmian-zero-step-leaves-the-raw-jump-invariant` measured that the raw
jump behind `psi`'s amplitude at `k` is unchanged at `k+1` whenever the Sturmian
word `s_k` vanishes, to floating-point zero at 32 positions.  The reason is this
file, and it is elementary: nothing about limits, nothing about `psi`.

Write `N_d` for the number of words of length `d` with `o_t >= ceil(t*beta)` at
every `t <= d`, where `o_t` counts odd letters, and `P_d = N_d / 2^d`.  If the
barrier does not rise at step `d` — that is, `ceil((d+1)*beta) = ceil(d*beta)` —
then **every** surviving word extends in **both** ways, because `o` cannot
decrease.  So `(w, x) ↦ w ++ [x]` is a bijection onto the survivors of length
`d+1`, giving `N_(d+1) = 2 * N_d` and hence `P_(d+1) = P_d` exactly.

The measured identity follows at once: the two depths whose phase brackets
`k*beta` both have a non-rising barrier when `s_k = 0`, so each of `P` at those
depths is individually unchanged, and so is any combination of them.

* `survives_succ_of_no_rise` is the content: survival to `d` plus a non-rising
  barrier gives survival to `d+1`, for either letter, since the count is
  monotone.
* `barrierRise_eq_zero_iff` characterises the non-rising step by the phase, which
  is what ties it to the Sturmian word.

What is NOT formalised here is the cardinality bookkeeping `N_(d+1) = 2 * N_d`.
That step is the observation that the extension map is a bijection, which is
immediate from `survives_succ_of_no_rise` together with the fact that a survivor
of length `d+1` restricts to one of length `d`; it is recorded in the ledger row
rather than in Lean.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Problems.Juggler

namespace PaperBBarrierStep

/-- The barrier at depth `t`: a surviving word needs at least this many odd letters. -/
noncomputable def barrier (b : ℝ) (t : ℕ) : ℤ := ⌈(t : ℝ) * b⌉

/-- How much the barrier rises in one step. -/
noncomputable def barrierRise (b : ℝ) (t : ℕ) : ℤ := barrier b (t + 1) - barrier b t

/-- **A non-rising step costs nothing.**  If the barrier does not rise at `d`, then any
odd-count history that survives to `d` also survives to `d+1`, whatever the next letter
is — the count is monotone, so no choice can fall below a barrier that did not move.
This is the whole reason the raw jump repeats. -/
theorem survives_succ_of_no_rise {b : ℝ} {d : ℕ} {o : ℕ → ℤ}
    (hrise : barrierRise b d = 0)
    (hmono : ∀ t, o t ≤ o (t + 1))
    (hsurv : ∀ t ≤ d, barrier b t ≤ o t) :
    ∀ t ≤ d + 1, barrier b t ≤ o t := by
  intro t ht
  rcases Nat.lt_or_ge t (d + 1) with h | h
  · exact hsurv t (by omega)
  · have htd : t = d + 1 := by omega
    subst htd
    have : barrier b (d + 1) = barrier b d := by
      have := hrise
      simp only [barrierRise] at this
      omega
    rw [this]
    exact le_trans (hsurv d le_rfl) (hmono d)

/-- Conversely a survivor to `d+1` survives to `d`, so the extension map is onto the
survivors of one more letter.  Together with `survives_succ_of_no_rise` this is the
bijection that makes the count double. -/
theorem survives_of_survives_succ {b : ℝ} {d : ℕ} {o : ℕ → ℤ}
    (hsurv : ∀ t ≤ d + 1, barrier b t ≤ o t) :
    ∀ t ≤ d, barrier b t ≤ o t := fun t ht => hsurv t (by omega)

/-- **When the barrier does not rise.**  Exactly when the next point has not yet passed
the current ceiling.  For `b = beta` this is the Sturmian condition that indexes the
measured `s_k`; stated this way it needs no fractional parts. -/
theorem noRise_iff_le_ceil {b : ℝ} {t : ℕ} (hb : 0 ≤ b) :
    barrierRise b t = 0 ↔ ((t : ℝ) + 1) * b ≤ (barrier b t : ℝ) := by
  have hmono : (t : ℝ) * b ≤ ((t : ℝ) + 1) * b := by nlinarith
  constructor
  · intro h
    have : barrier b (t + 1) = barrier b t := by
      simp only [barrierRise] at h; omega
    have hle := Int.le_ceil (((t : ℝ) + 1) * b)
    simp only [barrier] at this ⊢
    rw [← this]
    exact_mod_cast hle
  · intro h
    have h1 : barrier b (t + 1) ≤ barrier b t := by
      simp only [barrier]
      refine Int.ceil_le.mpr ?_
      push_cast
      exact_mod_cast h
    have h2 : barrier b t ≤ barrier b (t + 1) := by
      simp only [barrier]
      refine Int.ceil_le_ceil ?_
      push_cast
      exact hmono
    simp only [barrierRise]
    omega

/-- **A rising step kills exactly the words sitting on the barrier that draw `E`.**
If the barrier rises at `d`, a survivor to `d` fails to reach `d+1` precisely when its
count is exactly the barrier and the next letter contributes nothing.  Every other
survivor extends both ways, as in `survives_succ_of_no_rise`.

Counting consequence, one line and not formalised here: writing `N_d` for the survivors
of length `d` and `M_d` for those of them on the barrier, each survivor has two
extensions and exactly the `M_d` on-barrier ones lose a single extension, so

    `N_(d+1) = 2 * N_d - barrierRise * M_d`

uniformly in both cases, and dividing by `2^(d+1)` gives
`P_(d+1) = P_d - barrierRise * Q_d / 2` with `Q_d = M_d / 2^d` the mass on the barrier.
Verified as an exact integer identity for `d = 1 .. 39` in the tests. -/
theorem dies_iff_on_barrier {b : ℝ} {d : ℕ} {o : ℕ → ℤ} {x : ℤ}
    (hrise : barrierRise b d = 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hstep : o (d + 1) = o d + x)
    (hsurv : barrier b d ≤ o d) :
    ¬ (barrier b (d + 1) ≤ o (d + 1)) ↔ (o d = barrier b d ∧ x = 0) := by
  have hb : barrier b (d + 1) = barrier b d + 1 := by
    simp only [barrierRise] at hrise; omega
  rw [hb, hstep]
  omega

/-- **Off the barrier, a rising step costs nothing either.**  The complement of
`dies_iff_on_barrier`: a survivor strictly above the barrier extends both ways even when
the barrier rises, which is why only the on-barrier mass appears in the count. -/
theorem survives_succ_of_above_barrier {b : ℝ} {d : ℕ} {o : ℕ → ℤ} {x : ℤ}
    (hrise : barrierRise b d = 1)
    (hx0 : 0 ≤ x)
    (hstep : o (d + 1) = o d + x)
    (habove : barrier b d < o d) :
    barrier b (d + 1) ≤ o (d + 1) := by
  have hb : barrier b (d + 1) = barrier b d + 1 := by
    simp only [barrierRise] at hrise; omega
  rw [hb, hstep]
  omega

/-- The two updates on the conditional profile, indexed by whether the barrier rises.
`rise = false` shifts mass up; `rise = true` shifts it down and drops what falls below
the barrier.  Both average the two neighbours, which is the fair coin. -/
noncomputable def update (rise : Bool) (pi : ℕ → ℝ) : ℕ → ℝ :=
  fun m => if rise then (pi m + pi (m + 1)) / 2
           else (pi m + (if m = 0 then 0 else pi (m - 1))) / 2

/-- **A non-rising step halves the boundary value.**  `m = 0` is reachable only from
`m = 0`, so `update false pi 0 = pi 0 / 2` with no other contribution.  Since the
non-rising update also preserves total mass, no renormalisation intervenes, and a
PERTURBATION of the boundary value halves too -- which is why `R`'s jump amplitudes
satisfy `a_(k+1) = a_k / 2` exactly at every `k` where the Sturmian word vanishes. -/
theorem update_false_at_zero (pi : ℕ → ℝ) : update false pi 0 = pi 0 / 2 := by
  simp [update]

/-- The difference of two profiles inherits it, which is the statement the jump rule
needs: whatever the two words agree on afterwards, a boundary gap halves per
non-rising step. -/
theorem update_false_sub_at_zero (pi sigma : ℕ → ℝ) :
    update false pi 0 - update false sigma 0 = (pi 0 - sigma 0) / 2 := by
  simp [update]; ring

/-- A rising step does NOT halve it: the boundary picks up the neighbour, so no rule of
this kind holds at `s_k = 1`, matching the measured ratios there, which do not settle. -/
theorem update_true_at_zero (pi : ℕ → ℝ) :
    update true pi 0 = (pi 0 + pi 1) / 2 := by
  simp [update]

end PaperBBarrierStep

end Problems.Juggler
