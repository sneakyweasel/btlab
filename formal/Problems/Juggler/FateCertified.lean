import Mathlib.Analysis.Complex.ExponentialBounds
import Problems.Juggler.FatePressureCorollary

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# A certified instance of the unconditional criteria at `C = 30`

The unconditional corollaries of Paper C (`docs/theory/juggler_fate_almost_all_note.md`) all
carry the side condition `e(C) > 7/10` on the Chernoff exponent
`e(C) = C D(p_C ‖ 1/2)/log 2`, and the paper's numerical tables for it are an audit script.
This file removes the script from the chain for one concrete constant: every bound here is a
rational inequality between integers, closed by `norm_num`, so the resulting statements rest
on nothing but the kernel.

The device is that a logarithm is certified by an integer power comparison. If `E ≤ e` and
`x^n ≤ E^m` then `n log x ≤ m` (`Certified.log_le_of_pow_le`), and symmetrically with
`e ≤ E` (`Certified.le_log_of_pow_le`); `Certified.e_ge` and `Certified.e_le` pin `e` between
`2.718` and `2.719` from Mathlib's `Real.exp_one_gt_d9`. Six such comparisons certify
everything:

| fact | certificate |
|---|---|
| `log 2 ≤ 7/10` | `2^10 ≤ 2.718^7` |
| `2/3 ≤ log 2` | `2.719^2 ≤ 2^3` |
| `84/53 ≤ log₂ 3` | `2^84 ≤ 3^53` |
| `log₂ 3 ≤ 149/94` | `3^94 ≤ 2^149` |
| `19/100 ≤ log(3049/2500)` | `2.719^19 ≤ (3049/2500)^100` |
| `log(39/50) ≥ -1/4` | `(50/39)^4 ≤ 2.718` |

From the third and fourth, `p = p_30` lies in `[0.6098, 0.61]` (`Certified.pC_thirty_ge`,
`Certified.pC_thirty_le`); with the last two and the sandwich `Certified.klHalf_ge_of`,
`D(p ‖ 1/2) ≥ 0.018312`, and with `log 2 ≤ 7/10` that gives
`e(30) > 7/10` (`Certified.chernoffExponent_thirty_gt`), the whole point. Two more bounds in
the other direction give `e(30) < 13/10` (`Certified.chernoffExponent_thirty_lt`), which makes
the side condition `A > C + e(C)` explicit as `A ≥ 32`.

So: `Certified.cylinder_bound_thirty`, `Certified.pressure_thirty` and
`Certified.one_sided_thirty` are the three unconditional criteria with every constant a
numeral. At `q = 1/2` the one-sided exponent is the Chernoff one
(`Certified.oneSidedExponent_half`), and `log₂` of the re-centring tilt is at most `13/20`
(`Certified.logb_tilt_thirty_le`), which makes that criterion's condition on `A` explicit as
`A ≥ 52`.

What this is not. `C = 30` is an instance, not the least: the audit finds `e(C) > 7/10` first
at `C = 23`, and the paper's own threshold `e(C) > 1 - λ**` first at `C = 19`; both remain
audit statements about `λ**` and are not formalized. The bounds here are deliberately loose
(the true value is `e(30) ≈ 1.05`) because loose bounds have small certificates. Nothing here
proves any of the three hypotheses, and nothing here is a halt theorem.
-/

namespace Certified

/-! ### Rational bounds on `e`, and logarithms from integer powers -/

theorem e_ge : (2718 : ℝ) / 1000 ≤ Real.exp 1 :=
  le_trans (by norm_num) Real.exp_one_gt_d9.le

theorem e_le : Real.exp 1 ≤ (2719 : ℝ) / 1000 :=
  le_trans Real.exp_one_lt_d9.le (by norm_num)

/-- **An upper bound on a logarithm, certified by integers.** If `E ≤ e` and `x^n ≤ E^m`
then `n log x ≤ m`. -/
theorem log_le_of_pow_le {x E : ℝ} (hx : 0 < x) (hE : 0 < E) (hEe : E ≤ Real.exp 1)
    {m n : ℕ} (h : x ^ n ≤ E ^ m) : (n : ℝ) * Real.log x ≤ m := by
  have h1 : Real.log (x ^ n) ≤ Real.log (E ^ m) := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h1
  have h2 : Real.log E ≤ 1 := by
    have := Real.log_le_log hE hEe
    rwa [Real.log_exp] at this
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- **A lower bound on a logarithm, certified by integers.** If `e ≤ E` and `E^m ≤ x^n`
then `m ≤ n log x`. -/
theorem le_log_of_pow_le {x E : ℝ} (hEe : Real.exp 1 ≤ E)
    {m n : ℕ} (h : E ^ m ≤ x ^ n) : (m : ℝ) ≤ n * Real.log x := by
  have hE : 0 < E := lt_of_lt_of_le (Real.exp_pos 1) hEe
  have h1 : Real.log (E ^ m) ≤ Real.log (x ^ n) := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h1
  have h2 : 1 ≤ Real.log E := by
    have := Real.log_le_log (Real.exp_pos 1) hEe
    rwa [Real.log_exp] at this
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- The same for a base-two logarithm: `x^n ≤ 2^m` gives `log₂ x ≤ m/n`. -/
theorem logb_two_le {x : ℝ} (hx : 0 < x) {m n : ℕ} (hn : 0 < n) (h : x ^ n ≤ 2 ^ m) :
    Real.logb 2 x ≤ m / n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log (x ^ n) ≤ Real.log (2 ^ m) := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [Real.logb, div_le_div_iff₀ hlog2 hn']
  linarith

/-- And `2^m ≤ x^n` gives `m/n ≤ log₂ x`. -/
theorem le_logb_two {x : ℝ} {m n : ℕ} (hn : 0 < n) (h : (2 : ℝ) ^ m ≤ x ^ n) :
    (m : ℝ) / n ≤ Real.logb 2 x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log ((2 : ℝ) ^ m) ≤ Real.log (x ^ n) := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [Real.logb, div_le_div_iff₀ hn' hlog2]
  linarith

/-! ### The six certificates -/

/-- `log 2 ≤ 7/10`, from `2^10 = 1024 ≤ 1095 < 2.718^7`. -/
theorem log_two_le : Real.log 2 ≤ 7 / 10 := by
  have h := log_le_of_pow_le (x := 2) (E := 2718 / 1000) (by norm_num) (by norm_num) e_ge
    (m := 7) (n := 10) (by norm_num)
  push_cast at h
  linarith

/-- `2/3 ≤ log 2`, from `2.719^2 < 8 = 2^3`. -/
theorem le_log_two : (2 : ℝ) / 3 ≤ Real.log 2 := by
  have h := le_log_of_pow_le (x := 2) (E := 2719 / 1000) e_le
    (m := 2) (n := 3) (by norm_num)
  push_cast at h
  linarith

/-- `84/53 ≤ log₂ 3`, from `2^84 ≤ 3^53`. -/
theorem le_logb_three : (84 : ℝ) / 53 ≤ Real.logb 2 3 := by
  have h := le_logb_two (x := 3) (m := 84) (n := 53) (by norm_num) (by norm_num)
  push_cast at h
  linarith

/-- `log₂ 3 ≤ 149/94`, from `3^94 ≤ 2^149`. -/
theorem logb_three_le : Real.logb 2 3 ≤ 149 / 94 := by
  have h := logb_two_le (x := 3) (by norm_num) (m := 149) (n := 94) (by norm_num) (by norm_num)
  push_cast at h
  linarith

/-- `19/100 ≤ log (3049/2500)`, from `2.719^19 ≤ (3049/2500)^100`. -/
theorem le_log_lo : (19 : ℝ) / 100 ≤ Real.log (3049 / 2500) := by
  have h := le_log_of_pow_le (x := 3049 / 2500) (E := 2719 / 1000) e_le
    (m := 19) (n := 100) (by norm_num)
  push_cast at h
  linarith

/-- `-(1/4) ≤ log (39/50)`, from `(50/39)^4 ≤ 2.718`. -/
theorem le_log_hi : -(1 : ℝ) / 4 ≤ Real.log (39 / 50) := by
  have h := log_le_of_pow_le (x := 50 / 39) (E := 2718 / 1000) (by norm_num) (by norm_num)
    e_ge (m := 1) (n := 4) (by norm_num)
  push_cast at h
  have hlog : Real.log (50 / 39) = -Real.log (39 / 50) := by
    rw [← Real.log_inv]
    norm_num
  rw [hlog] at h
  linarith

/-- `log (61/50) ≤ 1/5`, from `(61/50)^5 ≤ 2.718`. -/
theorem log_lo_le : Real.log (61 / 50) ≤ 1 / 5 := by
  have h := log_le_of_pow_le (x := 61 / 50) (E := 2718 / 1000) (by norm_num) (by norm_num)
    e_ge (m := 1) (n := 5) (by norm_num)
  push_cast at h
  linarith

/-- `log (1951/2500) ≤ -(6/25)`, from `2.719^6 ≤ (2500/1951)^25`. -/
theorem log_hi_le : Real.log (1951 / 2500) ≤ -(6 : ℝ) / 25 := by
  have h := le_log_of_pow_le (x := 2500 / 1951) (E := 2719 / 1000) e_le
    (m := 6) (n := 25) (by norm_num)
  push_cast at h
  have hlog : Real.log (2500 / 1951) = -Real.log (1951 / 2500) := by
    rw [← Real.log_inv]
    norm_num
  rw [hlog] at h
  linarith

/-! ### The exponent at `C = 30` -/

theorem logb_three_pos : 0 < Real.logb 2 3 := by
  have := le_logb_three
  linarith

/-- `0.6098 ≤ p_30`. -/
theorem pC_thirty_ge : (3049 : ℝ) / 5000 ≤ pC 30 := by
  unfold pC
  rw [le_div_iff₀ logb_three_pos]
  have h := logb_three_le
  nlinarith

/-- `p_30 ≤ 0.61`. -/
theorem pC_thirty_le : pC 30 ≤ 61 / 100 := by
  unfold pC
  rw [div_le_iff₀ logb_three_pos]
  have h := le_logb_three
  nlinarith

/-- **A sandwich on `p` gives a lower bound on `D(p ‖ 1/2)`.** -/
theorem klHalf_ge_of {p plo phi A B : ℝ} (hlo : plo ≤ p) (hhi : p ≤ phi)
    (hplo : 0 < plo) (hphi : phi < 1) (hA0 : 0 ≤ A) (hA : A ≤ Real.log (2 * plo))
    (hB0 : B ≤ 0) (hB : B ≤ Real.log (2 * (1 - phi))) :
    plo * A + (1 - plo) * B ≤ klHalf p := by
  have hp0 : 0 < p := lt_of_lt_of_le hplo hlo
  have hp1 : p < 1 := lt_of_le_of_lt hhi hphi
  rw [klHalf_eq p hp0 hp1]
  have hL1 : A ≤ Real.log (2 * p) :=
    le_trans hA (Real.log_le_log (by linarith) (by linarith))
  have hL2 : B ≤ Real.log (2 * (1 - p)) :=
    le_trans hB (Real.log_le_log (by linarith) (by linarith))
  have hT1 : plo * A ≤ p * Real.log (2 * p) :=
    mul_le_mul hlo hL1 hA0 (by linarith)
  have hT2 : (1 - plo) * B ≤ (1 - p) * Real.log (2 * (1 - p)) := by
    have h1 : (1 - plo) * B ≤ (1 - p) * B := by nlinarith
    have h2 : (1 - p) * B ≤ (1 - p) * Real.log (2 * (1 - p)) :=
      mul_le_mul_of_nonneg_left hL2 (by linarith)
    linarith
  linarith

/-- **A sandwich on `p` gives an upper bound on `D(p ‖ 1/2)`.** -/
theorem klHalf_le_of {p plo phi A B : ℝ} (hlo : plo ≤ p) (hhi : p ≤ phi)
    (hplo : 1 / 2 < plo) (hphi : phi < 1) (hA : Real.log (2 * phi) ≤ A)
    (hB0 : B ≤ 0) (hB : Real.log (2 * (1 - plo)) ≤ B) :
    klHalf p ≤ phi * A + (1 - phi) * B := by
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := lt_of_le_of_lt hhi hphi
  rw [klHalf_eq p hp0 hp1]
  have hL1 : Real.log (2 * p) ≤ A :=
    le_trans (Real.log_le_log (by linarith) (by linarith)) hA
  have hL10 : 0 ≤ Real.log (2 * p) := by
    rw [← Real.log_one]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hL2 : Real.log (2 * (1 - p)) ≤ B :=
    le_trans (Real.log_le_log (by linarith) (by linarith)) hB
  have hT1 : p * Real.log (2 * p) ≤ phi * A :=
    mul_le_mul hhi hL1 hL10 (by linarith)
  have hT2 : (1 - p) * Real.log (2 * (1 - p)) ≤ (1 - phi) * B := by
    have h1 : (1 - p) * Real.log (2 * (1 - p)) ≤ (1 - p) * B :=
      mul_le_mul_of_nonneg_left hL2 (by linarith)
    have h2 : (1 - p) * B ≤ (1 - phi) * B := by nlinarith
    linarith
  linarith

/-- `D(p_30 ‖ 1/2) ≥ 0.018312`. -/
theorem klHalf_thirty_ge : (9156 : ℝ) / 500000 ≤ klHalf (pC 30) := by
  have h := klHalf_ge_of (p := pC 30) (plo := 3049 / 5000) (phi := 61 / 100)
    pC_thirty_ge pC_thirty_le (by norm_num) (by norm_num) (A := 19 / 100) (by norm_num)
    (by rw [show (2 : ℝ) * (3049 / 5000) = 3049 / 2500 by norm_num]; exact le_log_lo)
    (B := -1 / 4) (by norm_num)
    (by rw [show (2 : ℝ) * (1 - 61 / 100) = 39 / 50 by norm_num]; exact le_log_hi)
  norm_num at h
  linarith

/-- `D(p_30 ‖ 1/2) ≤ 0.0284`. -/
theorem klHalf_thirty_le : klHalf (pC 30) ≤ (71 : ℝ) / 2500 := by
  have h := klHalf_le_of (p := pC 30) (plo := 3049 / 5000) (phi := 61 / 100)
    pC_thirty_ge pC_thirty_le (by norm_num) (by norm_num) (A := 1 / 5)
    (by rw [show (2 : ℝ) * (61 / 100) = 61 / 50 by norm_num]; exact log_lo_le)
    (B := -6 / 25) (by norm_num)
    (by rw [show (2 : ℝ) * (1 - 3049 / 5000) = 1951 / 2500 by norm_num]; exact log_hi_le)
  norm_num at h
  linarith

/-- **The certified instance.** `e(30) > 39/50`, with no audit script in the chain; in
particular `e(30) > 7/10`, the side condition of every unconditional criterion. -/
theorem chernoffExponent_thirty_gt : 39 / 50 < chernoffExponent 30 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold chernoffExponent
  rw [lt_div_iff₀ hlog2]
  have h1 := klHalf_thirty_ge
  have h2 := log_two_le
  nlinarith

/-- `e(30) < 13/10`, so the side condition `A > C + e(C)` is met by `A ≥ 32`. -/
theorem chernoffExponent_thirty_lt : chernoffExponent 30 < 13 / 10 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold chernoffExponent
  rw [div_lt_iff₀ hlog2]
  have h1 := klHalf_thirty_le
  have h2 := le_log_two
  nlinarith

/-! ### The three unconditional criteria, with every constant a numeral -/

/-- **The conjecture from a cylinder bound at `C = 30`.** If every `O`-rooted `L(y)`-bad
cylinder of depth `⌈30 L(y)⌉` holds at most its fair share plus `y (log y)^{-A}`, at all large
scales above a certified floor, for some `A ≥ 32`, then every positive integer reaches `1`. -/
theorem cylinder_bound_thirty {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {A : ℝ} (hA : 32 ≤ A)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ 30 A y) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Production.conjecture_of_cylinder_bound hN hfloor 30 A (by norm_num)
    (by linarith [chernoffExponent_thirty_lt]) hcyl (by linarith [chernoffExponent_thirty_gt])

/-- **The conjecture from the pressure hypothesis at `C = 30`.** If the live pressure at the
tilt `p_30/(1 - p_30)` and depth `⌈30 L(y)⌉` is at most `2y a_θ^{d(y)}` at all large scales
above a certified floor, then every positive integer reaches `1`. -/
theorem pressure_thirty {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → Pressure.PressureBound N₀ 30 0 y) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Pressure.pressure_implies_conjecture hN hfloor 30 0 (71 / 100) (by norm_num)
    (by linarith [chernoffExponent_thirty_gt]) (by norm_num) hP

/-! ### The one-sided criterion at the fair share -/

/-- At `q = 1/2` the relative entropy is the paper's `D(p ‖ 1/2)`. -/
theorem klDiv_half {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    OneSided.klDiv p (1 / 2) = klHalf p := by
  unfold OneSided.klDiv
  rw [show p / (1 / 2) = 2 * p by ring, show (1 - p) / (1 - 1 / 2) = 2 * (1 - p) by ring]
  exact (klHalf_eq p hp0 hp1).symm

/-- Hence the one-sided exponent at `q = 1/2` is the Chernoff exponent. -/
theorem oneSidedExponent_half {C : ℝ} (hC : 5 ≤ C) :
    OneSided.oneSidedExponent C (1 / 2) = chernoffExponent C := by
  unfold OneSided.oneSidedExponent chernoffExponent
  rw [klDiv_half (by linarith [half_le_pC C hC]) (pC_lt_one C hC)]

/-- `log₂` of the re-centring tilt at `C = 30`, `q = 1/2`, is at most `13/20`: from
`(61/39)^20 ≤ 2^13`. -/
theorem logb_tilt_thirty_le : Real.logb 2 (OneSided.tilt (pC 30) (1 / 2)) ≤ 13 / 20 := by
  have hp_lo : (3049 : ℝ) / 5000 ≤ pC 30 := pC_thirty_ge
  have hp_hi : pC 30 ≤ 61 / 100 := pC_thirty_le
  have heq : OneSided.tilt (pC 30) (1 / 2) = pC 30 / (1 - pC 30) := by
    unfold OneSided.tilt
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    rw [div_eq_div_iff (by nlinarith) (by nlinarith)]
    ring
  have htilt_le : OneSided.tilt (pC 30) (1 / 2) ≤ 61 / 39 := by
    rw [heq]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have htilt_pos : 0 < OneSided.tilt (pC 30) (1 / 2) := by
    rw [heq]
    apply div_pos <;> linarith
  have h := logb_two_le (x := OneSided.tilt (pC 30) (1 / 2)) htilt_pos (m := 13) (n := 20)
    (by norm_num) ?_
  · push_cast at h
    linarith
  · calc OneSided.tilt (pC 30) (1 / 2) ^ 20 ≤ ((61 : ℝ) / 39) ^ 20 :=
        pow_le_pow_left₀ htilt_pos.le htilt_le 20
      _ ≤ 2 ^ (13 : ℕ) := by norm_num

/-- **The conjecture from the one-sided hypothesis at `C = 30`, `q = 1/2`.** If no `L(y)`-bad
cylinder of depth below `⌈30 L(y)⌉` sends more than half of its members, plus
`y (log y)^{-A}`, to an odd next letter, at all large scales above a certified floor, for some
`A ≥ 52`, then every positive integer reaches `1`. -/
theorem one_sided_thirty {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {A : ℝ} (hA : 52 ≤ A)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSided.OneSidedBound N₀ 30 (1 / 2) A y) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  refine OneSided.one_sided_implies_conjecture hN hfloor 30 (1 / 2) A (71 / 100) (by norm_num)
    (by norm_num) (by linarith [pC_thirty_ge]) ?_ ?_ (by norm_num) hH
  · have h := logb_tilt_thirty_le
    linarith
  · rw [oneSidedExponent_half (by norm_num)]
    linarith [chernoffExponent_thirty_gt]

end Certified

end Problems.Juggler
