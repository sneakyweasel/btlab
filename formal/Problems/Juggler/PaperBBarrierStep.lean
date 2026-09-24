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
* `noRise_iff_le_ceil` characterises the non-rising step as `(t+1)·b ≤ ⌈t·b⌉`,
  the Sturmian condition that ties it to the word, stated without fractional parts.

The cardinality bookkeeping is formalised separately in
`PaperBCertificateRecursion.lean`: `neverNegCount_add_minimalCertCount` gives
the exact extension recurrence and `minimalCertCount_succ` identifies its lost
words with `onBarrierCount`. This module proves the individual step rules;
the separate module proves the Finset cardinality identities.
`PaperBBarrierMass.lean` connects these counts to the ceiling barrier and
formalises the mass-preserving update and fractional-part phase conditions.
The measured amplitude identities remain outside this formalisation.
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


/-! ### The ratio cone, and where it fails

A coupling or Birkhoff argument for the quasi-stationary limit would run on a cone of profiles
with controlled decay.  The natural one is the ratio cone `pi (m+1) <= s * pi m`.  Both updates
preserve it in the BULK, and for a reason with no content beyond addition: the updated value at a
site is an average of two neighbouring old values, and the bound at the two sites adds.

It fails at the barrier, and `boundary_ratio_at_least_one` says how: a non-rising step sends mass
up, so at `m = 0` the updated ratio is at least `1`, exceeding any `s < 1`.  The defect is exactly
one site wide, which the measurements confirm -- bulk ratios sit at the initial value to four
decimals while the ratio at `m = 0` oscillates over `0.45, 1.45, 0.86, 1.67`.

None of this yields a contraction.  Measured on the light-tail class, the Hilbert projective
metric decays POLYNOMIALLY and not geometrically -- fitting `log d_H` against `d` and against
`log d` over `d = 2000..12000` gives residual standard deviations `0.20` and `0.011`, a factor of
twenty in favour of the polynomial, with exponents `-1.87, -1.96, -1.61`.  So Birkhoff contraction
fails even after the cone restriction, which is the same criticality as
`J-no-exponential-weight-restores-the-gap` seen from the projective side.  What survives is that
the distance is summable, and a summable non-contractive argument is a different proof.
-/

/-- **A rising step preserves the ratio cone.**  Adding the bound at the two sites is the whole
proof: the updated value at a site is an average of the two old neighbours. -/
theorem update_true_ratio {pi : ℕ → ℝ} {s : ℝ} {m : ℕ}
    (h1 : pi (m + 1) ≤ s * pi m) (h2 : pi (m + 2) ≤ s * pi (m + 1)) :
    update true pi (m + 1) ≤ s * update true pi m := by
  simp only [update]
  norm_num
  linarith

/-- **A non-rising step preserves it too, away from the barrier.** -/
theorem update_false_ratio {pi : ℕ → ℝ} {s : ℝ} {m : ℕ}
    (h1 : pi (m + 1) ≤ s * pi m) (h2 : pi (m + 2) ≤ s * pi (m + 1)) :
    update false pi (m + 2) ≤ s * update false pi (m + 1) := by
  simp only [update, Bool.false_eq_true]
  norm_num
  linarith

/-- **And at the barrier it fails.**  A non-rising step sends mass up, so the ratio at `m = 0` is
at least one and no cone with `s < 1` survives there.  The defect is one site wide. -/
theorem boundary_ratio_at_least_one {pi : ℕ → ℝ} (h : 0 ≤ pi 1) :
    update false pi 0 ≤ update false pi 1 := by
  simp only [update, Bool.false_eq_true]
  norm_num
  linarith

end PaperBBarrierStep

end Problems.Juggler
