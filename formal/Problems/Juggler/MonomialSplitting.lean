import Mathlib.Tactic

namespace Problems.Juggler

/-!
# Monomial splitting constants (Paper B, Lemmas 3.8 and 3.9)

The two-term test (Lemma 3.8) and the three-term sublevel splitting
(Lemma 3.9) of the parity-discrepancy note carry constants `c₆(E)`,
`c₇(E)`, `ρ₀(E)` that the manuscript leaves implicit ("in terms of `E`
alone"). For the exponent set actually used,

  `E = {3/4, 5/4, 11/8, 3/2, 15/8}`,

they are finite exact computations. This module discharges the two the
argument really rests on, both pure linear algebra over `ℚ` — and one of
which is where the audit ledger already found an error (the `ℓ¹` norm
`288` had been printed where the `ℓ^∞` norm `232` is what the argument
needs).

* `step5b_curvature_inverse` — the inversion behind Lemma 3.9 for the
  Step-5b triple `(5/4, 11/8, 3/2)`: the curvature coefficients
  `A, B, C` are recovered from `(f'', n f''', n² f'''')` by the printed
  integer matrix.
* `step5b_curvature_norm` — its `ℓ^∞` operator norm bound, i.e.
  `max(|A|, |B|, |C|) ≤ 232 · max(|f''|, |n f'''|, |n² f''''|)`, which is
  Lemma 3.9's `c₇ = 1/232`. The manuscript's weaker `c₇ = 1/288` follows
  a fortiori (`step5b_c7_printed`).
* `c6_eleven_eighths_five_fourths` — the extremal case of Lemma 3.8's
  `c₆`: over the ordered pairs of `E` the minimum is `1/14`, attained at
  `(α, β) = (11/8, 5/4)`, so `ρ₀(E) ≤ 1/112` is admissible.

No analytic estimate is claimed here; these are the finite constants the
human proof quotes.
-/

section Lemma39

/-- **Lemma 3.9, Step-5b triple.** For `(α, β, γ) = (5/4, 11/8, 3/2)`
the exponents `x = α - 2` are `-3/4, -5/8, -1/2`, and the system

  `u = A + B + C`,  `v = Σ xᵢ Aᵢ`,  `w = Σ xᵢ(xᵢ - 1) Aᵢ`

inverts to the integer matrix printed in the note. -/
theorem step5b_curvature_inverse (A B C u v w : ℝ)
    (hu : u = A + B + C)
    (hv : v = (-3/4) * A + (-5/8) * B + (-1/2) * C)
    (hw : w = (-3/4) * ((-3/4) - 1) * A + (-5/8) * ((-5/8) - 1) * B
            + (-1/2) * ((-1/2) - 1) * C) :
    A = 10 * u + 68 * v + 32 * w ∧
    B = -24 * u - 144 * v - 64 * w ∧
    C = 15 * u + 76 * v + 32 * w := by
  subst hu hv hw
  refine ⟨by ring, by ring, by ring⟩

/-- **Lemma 3.9, the constant `c₇`.** The `ℓ^∞` operator norm of the
inverse is the maximal absolute row sum, `max(110, 232, 123) = 232`, so
at every point one of the three derivative orders is at least `1/232` of
the largest curvature term. -/
theorem step5b_curvature_norm (A B C u v w : ℝ)
    (hu : u = A + B + C)
    (hv : v = (-3/4) * A + (-5/8) * B + (-1/2) * C)
    (hw : w = (-3/4) * ((-3/4) - 1) * A + (-5/8) * ((-5/8) - 1) * B
            + (-1/2) * ((-1/2) - 1) * C) :
    max |A| (max |B| |C|) ≤ 232 * max |u| (max |v| |w|) := by
  obtain ⟨hA, hB, hC⟩ := step5b_curvature_inverse A B C u v w hu hv hw
  set M := max |u| (max |v| |w|) with hMdef
  have hu1 : |u| ≤ M := le_max_left _ _
  have hv1 : |v| ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hw1 : |w| ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg u) hu1
  obtain ⟨hu2, hu3⟩ := abs_le.mp hu1
  obtain ⟨hv2, hv3⟩ := abs_le.mp hv1
  obtain ⟨hw2, hw3⟩ := abs_le.mp hw1
  refine max_le ?_ (max_le ?_ ?_)
  · rw [hA, abs_le]; constructor <;> linarith
  · rw [hB, abs_le]; constructor <;> linarith
  · rw [hC, abs_le]; constructor <;> linarith

/-- The manuscript's Step 5b quotes the weaker `c₇ = 1/288`; it follows
from `step5b_curvature_norm` since `232 ≤ 288`. -/
theorem step5b_c7_printed (A B C u v w : ℝ)
    (hu : u = A + B + C)
    (hv : v = (-3/4) * A + (-5/8) * B + (-1/2) * C)
    (hw : w = (-3/4) * ((-3/4) - 1) * A + (-5/8) * ((-5/8) - 1) * B
            + (-1/2) * ((-1/2) - 1) * C) :
    max |A| (max |B| |C|) ≤ 288 * max |u| (max |v| |w|) := by
  have h := step5b_curvature_norm A B C u v w hu hv hw
  have hM0 : (0:ℝ) ≤ max |u| (max |v| |w|) :=
    le_trans (abs_nonneg u) (le_max_left _ _)
  linarith

end Lemma39

section Lemma38

/-- **Lemma 3.8, the constant `c₆`.** With `p = α - 2`, `q = β - 2` the
lemma needs `min_{s>0} max(|1 - s|, |p - q s|) > 0`. Over the ordered
pairs of `E` the minimum is `1/14`, attained at `(α, β) = (11/8, 5/4)`,
where `p = -5/8`, `q = -3/4`; the two V-shapes cross at `s = 13/14`. -/
theorem c6_eleven_eighths_five_fourths (s : ℝ) :
    (1/14 : ℝ) ≤ max |1 - s| |(3/4) * s - 5/8| := by
  rcases le_or_gt (1/14 : ℝ) |1 - s| with h | h
  · exact le_max_of_le_left h
  · -- `|1 - s| < 1/14` pins `s > 13/14`, where the second V-shape is
    -- already at least `1/14`.
    refine le_max_of_le_right ?_
    obtain ⟨h1, h2⟩ := abs_lt.mp h
    have : (1/14 : ℝ) ≤ (3/4) * s - 5/8 := by linarith
    exact le_trans this (le_abs_self _)

/-- The value `1/14` is attained, so `c₆ = 1/14` is sharp for this pair
and `ρ₀(E) ≤ c₆/8 = 1/112` is the admissible perturbation size. -/
theorem c6_eleven_eighths_five_fourths_attained :
    max |1 - (13/14 : ℝ)| |(3/4) * (13/14 : ℝ) - 5/8| = 1/14 := by
  norm_num

end Lemma38

end Problems.Juggler
