import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Problems.Juggler

/-!
# Numerics for the fate-contagion paper: roots by powering, Bernoulli at a point

Paper C (`docs/theory/juggler_fate_almost_all_note.md`) certifies its real-exponent
constants (`2^{1/3} ≤ 1.26`, `u^{2/3} ≥ 10^4` for `u ≥ 10^6`, `log₂ 3 ≤ 8/5`, `m^{4/3} ≤ n` on
the fiber) by one move, "raise both sides to the `n`-th power, where `p n` is an integer",
and it steps its fibers by Bernoulli's inequality `(1 + s)^p ⋚ 1 + p s` written at a point
`a`: `(a + h)^p ⋚ a^p + p a^{p-1} h`. Lemmas 4.2, 4.3 and 8.2 each carried private copies of
those two moves; this module holds them once.

`rpow_le_iff_pow` and its three siblings turn `x^p ≤ c` (or `c ≤ x^p`, strict or not) into
`x^{p n} ≤ c^n` for a natural `n ≠ 0`, where `norm_num` finishes once `p n` is a numeral.
`bernoulli_ge` / `bernoulli_le` are the tangent-line inequalities at `a > 0`, with the
exponent `p - 1` supplied as `q` so that a caller states it in the form it wants. Nothing
here is specific to the Juggler map, and nothing here is a statement about the map.
-/

namespace Numerics

/-! ### Roots by powering -/

/-- `x^p ≤ c ↔ x^{p n} ≤ c^n` for `x, c ≥ 0` and a natural `n ≠ 0`. -/
theorem rpow_le_iff_pow {x c p : ℝ} {n : ℕ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hn : n ≠ 0) :
    x ^ p ≤ c ↔ x ^ (p * n) ≤ c ^ n := by
  rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg hx _) hc hn, ← Real.rpow_natCast (x ^ p) n,
    ← Real.rpow_mul hx]

/-- `c ≤ x^p ↔ c^n ≤ x^{p n}` for `x, c ≥ 0` and a natural `n ≠ 0`. -/
theorem le_rpow_iff_pow {x c p : ℝ} {n : ℕ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hn : n ≠ 0) :
    c ≤ x ^ p ↔ c ^ n ≤ x ^ (p * n) := by
  rw [← pow_le_pow_iff_left₀ hc (Real.rpow_nonneg hx _) hn, ← Real.rpow_natCast (x ^ p) n,
    ← Real.rpow_mul hx]

/-- `x^p < c ↔ x^{p n} < c^n` for `x, c ≥ 0` and a natural `n ≠ 0`. -/
theorem rpow_lt_iff_pow {x c p : ℝ} {n : ℕ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hn : n ≠ 0) :
    x ^ p < c ↔ x ^ (p * n) < c ^ n := by
  rw [← pow_lt_pow_iff_left₀ (Real.rpow_nonneg hx _) hc hn, ← Real.rpow_natCast (x ^ p) n,
    ← Real.rpow_mul hx]

/-- `c < x^p ↔ c^n < x^{p n}` for `x, c ≥ 0` and a natural `n ≠ 0`. -/
theorem lt_rpow_iff_pow {x c p : ℝ} {n : ℕ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hn : n ≠ 0) :
    c < x ^ p ↔ c ^ n < x ^ (p * n) := by
  rw [← pow_lt_pow_iff_left₀ hc (Real.rpow_nonneg hx _) hn, ← Real.rpow_natCast (x ^ p) n,
    ← Real.rpow_mul hx]

/-! ### Bernoulli at a point -/

/-- Bernoulli at a point, lower: `a^p + p a^q h ≤ (a + h)^p` for `a > 0`, `h ≥ -a`, and
`p = q + 1 ≥ 1`. -/
theorem bernoulli_ge {a h p q : ℝ} (ha : 0 < a) (hh : -a ≤ h) (hp : 1 ≤ p) (hq : p = q + 1) :
    a ^ p + p * a ^ q * h ≤ (a + h) ^ p := by
  have hs : -1 ≤ h / a := by rw [le_div_iff₀ ha]; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs hp
  have e : (1 : ℝ) + h / a = (a + h) / a := by field_simp
  rw [e, Real.div_rpow (by linarith) ha.le, le_div_iff₀ (Real.rpow_pos_of_pos ha _)] at hb
  have hpq : a ^ p = a ^ q * a := by rw [hq, Real.rpow_add ha, Real.rpow_one]
  calc a ^ p + p * a ^ q * h = (1 + p * (h / a)) * a ^ p := by rw [hpq]; field_simp
    _ ≤ (a + h) ^ p := hb

/-- Bernoulli at a point, upper: `(a + h)^p ≤ a^p + p a^q h` for `a > 0`, `h ≥ -a`,
`0 ≤ p ≤ 1` and `p = q + 1`. -/
theorem bernoulli_le {a h p q : ℝ} (ha : 0 < a) (hh : -a ≤ h) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : p = q + 1) : (a + h) ^ p ≤ a ^ p + p * a ^ q * h := by
  have hs : -1 ≤ h / a := by rw [le_div_iff₀ ha]; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hp0 hp1
  have e : (1 : ℝ) + h / a = (a + h) / a := by field_simp
  rw [e, Real.div_rpow (by linarith) ha.le, div_le_iff₀ (Real.rpow_pos_of_pos ha _)] at hb
  have hpq : a ^ p = a ^ q * a := by rw [hq, Real.rpow_add ha, Real.rpow_one]
  calc (a + h) ^ p ≤ (1 + p * (h / a)) * a ^ p := hb
    _ = a ^ p + p * a ^ q * h := by rw [hpq]; field_simp

end Numerics

end Problems.Juggler
