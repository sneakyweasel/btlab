/-
# Paper B: transposing two barrier letters costs exactly the mass on the barrier

`PaperBCertificateRecursion` decomposes the survivors one letter at a time. This file
looks at the same walk from the side, and asks what changes when two *adjacent* barrier
letters are exchanged rather than appended.

The question is not decorative. The measured prefactor of
`J-paper-b-meander-prefactor-is-almost-periodic` is a function `psi` of the rotation
coordinate `frac (d * beta)`, `beta = log 2 / log 3`, and `psi` is discontinuous: the
barrier word read backwards from `d` is determined by that coordinate, and as the
coordinate crosses a point of the orbit the word does not change arbitrarily -- two
neighbouring letters swap, rise-then-flat becoming flat-then-rise. Nothing else moves,
and in particular the number of rising letters, hence the barrier height, is unchanged.
So the
size of a discontinuity of `psi` is the cost of one transposition, and that cost is what
is computed here.

**The profile.** Track survivors by their surplus above the barrier. A word of length `k`
with `o` odd letters survives when `3 ^ o` is at least `2 ^ k` at every prefix, so writing
`h = o - ceil (k * beta)` the surviving words of length `k` are graded by `h : Nat`, and
one further letter acts on the grading by

  `stepFlat v h = v h + v (h-1)`      barrier flat, nothing killed
  `stepRise v h = v (h+1) + v h`      barrier rises, and the walkers at `h = 0`
                                      that do not climb fall through it

`stepFlat` is the doubling map: no survivor is lost. `stepRise` loses exactly the value
of the profile at `h = 0`, which is the count of survivors sitting *on* the barrier.

**The transposition.** `stepRise (stepFlat v)` and `stepFlat (stepRise v)` agree at every
height except `0`, and at `0` they differ by `v 0` -- the barrier mass, and nothing else
(`stepRise_stepFlat_eq_add_barrierMass`). Both orders kill once and climb once; they differ
only in whether the climb happened before or after the kill, and that matters to exactly
the walkers standing on the barrier at the moment of the swap.

Because every later letter acts linearly (`run_add`), the whole difference between the two
transposed histories is the history of a *point mass at the barrier*
(`run_stepRise_stepFlat`). That is the content: a discontinuity of `psi` is not a new
quantity, it is the survivor problem run again from a single walker on the barrier.

**What is not here.** The word `beta` does not appear in any statement below, and no real
number does. Which pairs of letters get transposed at which coordinate is a fact about the
Sturmian barrier word, proved for the letters themselves in `PaperBSturmianBarrier`; the
asymptotics that turn `run` into `psi` are measured, not proved, and live with
`J-paper-b-meander-prefactor-is-almost-periodic`. This file proves only the exchange cost,
which is finite, exact and about natural numbers.
-/
import Mathlib.Tactic

namespace Problems.Juggler

namespace JumpTransposition

/-- Survivors graded by their surplus `h` above the barrier. Counts, so `Nat`. -/
abbrev Profile := ℕ → ℕ

/-- One step against a barrier letter that does **not** rise, so a walker at
height `h` arrives from `h` by staying or from `h - 1` by climbing, and nobody is killed. -/
def stepFlat (v : Profile) : Profile
  | 0 => v 0
  | h + 1 => v (h + 1) + v h

/-- One step against a barrier letter that **rises** by one, so a walker at
height `h` arrives from `h + 1` by staying or from `h` by climbing. The walkers at height
`0` that do not climb fall through the barrier and are lost. -/
def stepRise (v : Profile) : Profile := fun h => v (h + 1) + v h

/-- The survivors sitting exactly **on** the barrier, as a profile: a point mass at `0`. -/
def barrierMass (v : Profile) : Profile
  | 0 => v 0
  | _ + 1 => 0

@[simp] theorem barrierMass_zero (v : Profile) : barrierMass v 0 = v 0 := rfl

@[simp] theorem barrierMass_succ (v : Profile) (h : ℕ) : barrierMass v (h + 1) = 0 := rfl

theorem barrierMass_eq_ite (v : Profile) (h : ℕ) :
    barrierMass v h = if h = 0 then v 0 else 0 := by
  cases h <;> simp

@[simp] theorem stepFlat_zero (v : Profile) : stepFlat v 0 = v 0 := rfl

@[simp] theorem stepFlat_succ (v : Profile) (h : ℕ) :
    stepFlat v (h + 1) = v (h + 1) + v h := rfl

@[simp] theorem stepRise_apply (v : Profile) (h : ℕ) : stepRise v h = v (h + 1) + v h := rfl

/-- **The exchange cost.** Climbing before killing and killing before climbing agree at
every height above the barrier, and differ at the barrier by exactly the mass standing on
it. Everything is `Nat`; the two orders are genuinely comparable, one dominating the
other. -/
theorem stepRise_stepFlat_eq_add_barrierMass (v : Profile) (h : ℕ) :
    stepRise (stepFlat v) h = stepFlat (stepRise v) h + barrierMass v h := by
  cases h <;> simp

/-- Killing before climbing never counts more than climbing before killing. -/
theorem stepFlat_stepRise_le (v : Profile) (h : ℕ) :
    stepFlat (stepRise v) h ≤ stepRise (stepFlat v) h := by
  rw [stepRise_stepFlat_eq_add_barrierMass]; exact Nat.le_add_right _ _

/-- A barrier word, read in the order its letters are applied; `true` is a rise. -/
def run : List Bool → Profile → Profile
  | [], v => v
  | b :: w, v => run w (if b then stepRise v else stepFlat v)

@[simp] theorem run_nil (v : Profile) : run [] v = v := rfl

@[simp] theorem run_cons_true (w : List Bool) (v : Profile) :
    run (true :: w) v = run w (stepRise v) := rfl

@[simp] theorem run_cons_false (w : List Bool) (v : Profile) :
    run (false :: w) v = run w (stepFlat v) := rfl

theorem stepFlat_add (u v : Profile) : stepFlat (u + v) = stepFlat u + stepFlat v := by
  funext h
  cases h with
  | zero => simp [Pi.add_apply]
  | succ k => simp [Pi.add_apply]; omega

theorem stepRise_add (u v : Profile) : stepRise (u + v) = stepRise u + stepRise v := by
  funext h; simp [Pi.add_apply]; omega

/-- Every letter acts linearly, so a whole history does. -/
theorem run_add (w : List Bool) : ∀ u v : Profile, run w (u + v) = run w u + run w v := by
  induction w with
  | nil => intro u v; rfl
  | cons b w ih =>
      intro u v
      cases b
      · simp [stepFlat_add, ih]
      · simp [stepRise_add, ih]

/-- **What a discontinuity costs.** Transposing one adjacent rise-then-flat pair of barrier
letters changes the whole later history by exactly the history of a single point mass on
the barrier at the moment of the swap. -/
theorem run_stepRise_stepFlat (w : List Bool) (v : Profile) :
    run w (stepRise (stepFlat v))
      = run w (stepFlat (stepRise v)) + run w (barrierMass v) := by
  have h : stepRise (stepFlat v) = stepFlat (stepRise v) + barrierMass v := by
    funext h; exact stepRise_stepFlat_eq_add_barrierMass v h
  rw [h, run_add]

/-- The transposed history is never the larger one. -/
theorem run_stepFlat_stepRise_le (w : List Bool) (v : Profile) (h : ℕ) :
    run w (stepFlat (stepRise v)) h ≤ run w (stepRise (stepFlat v)) h := by
  rw [run_stepRise_stepFlat]; exact Nat.le_add_right _ _

/-- A point mass on the barrier is unmoved by a rising letter: the walker must climb, and
climbing from the barrier lands back on the barrier. This is why the history opened by a
transposition is the survivor problem itself, started from one walker, rather than some
other problem. -/
theorem stepRise_barrierMass (v : Profile) : stepRise (barrierMass v) = barrierMass v := by
  funext h
  cases h with
  | zero => simp
  | succ k => cases k <;> simp

/-- Totals over a height window, the quantity the counts are read through. -/
def total (H : ℕ) (v : Profile) : ℕ := ∑ h ∈ Finset.range H, v h

theorem total_add (H : ℕ) (u v : Profile) :
    total H (u + v) = total H u + total H v := by
  simp [total, Pi.add_apply, Finset.sum_add_distrib]

/-- The exchange cost at the level of totals. -/
theorem total_run_stepRise_stepFlat (H : ℕ) (w : List Bool) (v : Profile) :
    total H (run w (stepRise (stepFlat v)))
      = total H (run w (stepFlat (stepRise v))) + total H (run w (barrierMass v)) := by
  rw [run_stepRise_stepFlat, total_add]

theorem total_succ (H : ℕ) (v : Profile) : total (H + 1) v = total H v + v H :=
  Finset.sum_range_succ _ _

/-- A flat letter counts each window once and the window below it once more: nothing is
killed, and the only asymmetry is that the top height has nowhere to have come from. -/
theorem total_stepFlat (H : ℕ) (v : Profile) :
    total (H + 1) (stepFlat v) = total (H + 1) v + total H v := by
  induction H with
  | zero => simp [total]
  | succ k ih =>
      have h1 := total_succ (k + 1) (stepFlat v)
      have h2 := total_succ (k + 1) v
      have h3 := total_succ k v
      have h4 := stepFlat_succ v k
      omega

/-- A rising letter loses exactly the barrier mass `v 0`, and nothing else. -/
theorem total_stepRise (H : ℕ) (v : Profile) :
    total (H + 1) (stepRise v) + v 0 = total (H + 1) v + total (H + 1) v + v (H + 1) := by
  induction H with
  | zero => simp [total]; omega
  | succ k ih =>
      have h1 := total_succ (k + 1) (stepRise v)
      have h3 := total_succ (k + 1) v
      have h4 := stepRise_apply v (k + 1)
      omega

/-- **A Sturmian zero kills nothing.** Below a window the profile has not reached, a
flat letter exactly doubles the total. This is the whole content of the observed law that
jump amplitudes are multiplied by a clean factor across such a step.

Not a duplicate of `sum_neverNegWords_succ_of_window_empty` in
`PaperBCertificateRecursion`, though the two were mistaken for one another on
2026-09-19 and neither file said otherwise. They are incomparable, and meet at
exactly one point.

That one prints `∑_{v ∈ S_{d+1}} f v = ∑_{w ∈ S_d} (f (w ++ [E]) + f (w ++ [O]))`
for every additive commutative monoid and every `f`: general in the FUNCTIONAL,
specific to the survivor word set, and hypothesised on the certificate window being
empty. This one is the counting functional alone, but on an abstract graded
`Profile` with no word set in sight, and its hypothesis `v H = 0` is a truncation
width — it says the window `total (H+1)` is wide enough to hold the shifted mass,
not that the step is free. Freeness is not a hypothesis here at all; it is carried
by which operator is applied, `stepFlat` rather than `stepRise`.

So neither implies the other. The word-set theorem cannot reach an abstract profile,
and one functional cannot reach all of them. They coincide when that one is taken at
`f ≡ 1` and this one at the survivor height profile, where both read `N_{d+1} = 2 N_d`.
The transposition results below need the abstract carrier, because a transposition
rearranges the barrier word and there is no single `d` whose word set to sum over. -/
theorem total_stepFlat_eq_two_mul (H : ℕ) (v : Profile) (hv : v H = 0) :
    total (H + 1) (stepFlat v) = 2 * total (H + 1) v := by
  rw [total_stepFlat, total_succ, hv]; omega

/-- Against a rising letter the total doubles less the barrier mass, exactly. -/
theorem total_stepRise_add_barrierMass (H : ℕ) (v : Profile) (hv : v (H + 1) = 0) :
    total (H + 1) (stepRise v) + v 0 = 2 * total (H + 1) v := by
  rw [total_stepRise, hv]; omega

end JumpTransposition

end Problems.Juggler
