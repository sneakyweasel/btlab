/-
# Paper B, Appendix A: the threshold certificate

The certificate of `docs/theory/juggler_parity_discrepancy_note.md`, Appendix A,
proved rather than bisected.

`src/research/juggler_sequence/p0_certificate.py` solves each of the thirty
printed threshold inequalities of Sections 4–6 by floating-point bisection and
takes the maximum; that maximum is `P₀`.  Bisection in `Float` was the only
inexact step in an otherwise exact chain.  It is removable: **every exponent in
the paper lies in `(1/96)ℤ`**, so substituting `P = tⁿ` for a suitable `n` turns
each row into a polynomial inequality in `t`, with no `Real.rpow` anywhere.

All thirty rows are below, each with its substitution and a *rational* threshold
`t₀` at or just above the true crossing.  The certified thresholds are therefore
slightly conservative; the largest is `row_5b_binding` at `t = 1.96`, i.e.
`P ≥ 1.96^48 = 1.07·10^14`, against the probe's `8.95·10^13`.  That row is `P₀`.

Also here: the **raised-threshold device** of Step 5b (Section 1), which
replaced the comparison `V ≥ 10|f'' - Λ|`, and the **sharpness of `|G - δ| ≤ 1`**
in Lemma 5.2b step (i) (Section 3).

Out of scope, as always: Lemma 5.2, Theorem 5.3, van der Corput, Vaaler,
Erdős–Turán, the `A`-process.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Problems.Juggler

section RaisedThreshold

/-- **Step 5b, the raised-threshold device.**  Lemma 3.9 is applied to the global
interpolant `Λ` at threshold `W = V + E`, where `E` bounds `|f - Λ|`.  Off the
sublevel set `{|Λ| ≤ W}` this returns control of `f` itself: `|f| ≥ V`, and `f`
carries the sign of `Λ`.

This is what makes the former comparison `V ≥ 10 |f - Λ|` unnecessary.  The
factor `10` was not merely margin: it forced `V` upward exactly where the Lemma
3.9 hypothesis `V ≤ c₇S/2` forced it down, so the two pinned the normalisation
`κ` near `1/3`.  With this lemma `κ` falls to `1/12`, and both `P₀` and the
non-vacuity point `P₁` improve together. -/
theorem sublevel_raised_threshold
    (f Λ : ℝ → ℝ) (E V x : ℝ)
    (hV : 0 ≤ V) (hE : |f x - Λ x| ≤ E)
    (hx : V + E < |Λ x|) :
    V ≤ |f x| ∧ (0 < Λ x → 0 < f x) ∧ (Λ x < 0 → f x < 0) := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp hE
  have hEnn : 0 ≤ E := le_trans (abs_nonneg _) hE
  refine ⟨?_, ?_, ?_⟩
  · have : |Λ x| - |f x - Λ x| ≤ |f x| := by
      have := abs_sub_abs_le_abs_sub (Λ x) (f x)
      rw [abs_sub_comm (Λ x) (f x)] at this
      linarith
    linarith
  · intro hpos
    have : V + E < Λ x := by rwa [abs_of_pos hpos] at hx
    linarith
  · intro hneg
    have : V + E < -Λ x := by rwa [abs_of_neg hneg] at hx
    linarith

/-- The device is sound for *any* nonnegative `V`, in particular for the small
`V` that the old comparison forbade: the admissible range is `[0, c₇S/2 - E]`,
not `[10E, c₇S/2]`. -/
theorem raised_threshold_admissible (E S c₇ : ℝ) (_hE : 0 ≤ E)
    (_hfeas : E ≤ c₇ * S / 2) :
    ∀ V, 0 ≤ V → V ≤ c₇ * S / 2 - E → V + E ≤ c₇ * S / 2 := by
  intro V _ hV2; linarith

end RaisedThreshold

/-! ## The thirty rows -/

section CertificateRows

/-- Monotonicity of `t ↦ tᵏ`, the only tool most rows need. -/
private theorem pow_mono_base {t t₀ : ℝ} (h₀ : 0 ≤ t₀) (ht : t₀ ≤ t) (k : ℕ) :
    t₀ ^ k ≤ t ^ k := by gcongr

/-! ### Theorem 4.1: the θ-sawtooth and the collision band -/

/-- Row `s3s1-window`.  Lemma 3.7's hypothesis `T ≥ 8(1+|B|)` at `T = P^(1/2)`
with `|B| < 1/2`.  `P = t²`, `t ≥ 12`; `P ≥ 144`. -/
theorem row_s3s1_window (t : ℝ) (ht : 12 ≤ t) : 8 * (1 + 1 / 2) ≤ t := by linarith

/-- Row `s3s1-Bsmall`.  `2.25 P^(-1/16) < 1/2`, the inequality naming the regime.
`P = t^16`, `t ≥ 4.6`; `P ≥ 4.02·10^10`. -/
theorem row_s3s1_Bsmall (t : ℝ) (ht : 4.6 ≤ t) : 2.25 / t < 1 / 2 := by
  rw [div_lt_iff₀ (by linarith)]; linarith

/-- Row `s3s2-window`.  `P^(1/2) ≥ 8(1 + 2.25 P^(1/4))`, i.e. `t² ≥ 8 + 18t`
under `P = t⁴`; first true at `t = 9 + √89 = 18.434`, printed `t ≥ 19`. -/
theorem row_s3s2_window (t : ℝ) (ht : 19 ≤ t) : 8 * (1 + 2.25 * t) ≤ t ^ 2 := by
  nlinarith [sq_nonneg (t - 19)]

/-- Row `s3s2-flat`.  Flat cost `8(1 + 2.25P^(1/4))P^(1/2) ≤ 19 P^(3/4)`, i.e.
`8t² + 18t³ ≤ 19t³`; `t ≥ 8`, `P ≥ 4096`. -/
theorem row_s3s2_flat (t : ℝ) (ht : 8 ≤ t) : 8 * t ^ 2 + 18 * t ^ 3 ≤ 19 * t ^ 3 := by
  nlinarith [sq_nonneg t]

/-- Row `s3s2-wincount`.  `0.6 P^(1/4) + 1 ≤ 0.65 P^(1/4)`; `t ≥ 20`,
`P ≥ 1.6·10^5`. -/
theorem row_s3s2_wincount (t : ℝ) (ht : 20 ≤ t) : 0.6 * t + 1 ≤ 0.65 * t := by linarith

/-- `0.5916 ≤ √0.35`, the rational substitute for the irrational constant in the
window-boundary row. -/
theorem sqrt_0_35_lower : (0.5916 : ℝ) ^ 2 ≤ 0.35 := by norm_num

/-- Row `s3s2-bdry`, first half.  Window-boundary cost
`(0.6P^(1/4)+1)(0.35 uh)^(-1/2) P^(3/8) ≤ 1.1 P^(17/32)` at `uh > P^(3/16)`,
under `P = t^32`, with `√0.35 ≥ 0.5916` so that `1.1·0.5916 = 0.65076`.
`t ≥ 1.46`, `P ≥ 1.82·10^5`. -/
theorem row_s3s2_bdry_a (t : ℝ) (ht : 1.46 ≤ t) :
    (0.6 * t ^ 8 + 1) * t ^ 9 ≤ 0.65076 * t ^ 17 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h8 : (20:ℝ) ≤ t ^ 8 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.46) ht 8
    have : (20:ℝ) ≤ (1.46:ℝ) ^ 8 := by norm_num
    linarith
  have k : 20 * t ^ 9 ≤ t ^ 17 := by
    have e : t ^ 17 = t ^ 9 * t ^ 8 := by ring
    nlinarith [pow_pos ht0 9]
  nlinarith [k]

/-- Row `s3s2-bdry`, second half.  `1.1 P^(17/32) ≤ P^(5/8)`, i.e.
`1.1 t^17 ≤ t^20`; `t ≥ 1.46`. -/
theorem row_s3s2_bdry_b (t : ℝ) (ht : 1.46 ≤ t) : 1.1 * t ^ 17 ≤ t ^ 20 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h3 : (1.1:ℝ) ≤ t ^ 3 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.46) ht 3
    have : (1.1:ℝ) ≤ (1.46:ℝ) ^ 3 := by norm_num
    linarith
  have e : t ^ 20 = t ^ 17 * t ^ 3 := by ring
  nlinarith [pow_pos ht0 17]

/-- Row `stage2-modecurv`.  Mode-versus-cell curvature ratio `0.39 P^(1/8) ≥ 4`;
`P = t^8`, `t ≥ 10.26`, `P ≥ 1.23·10^8`. -/
theorem row_stage2_modecurv (t : ℝ) (ht : 10.26 ≤ t) : (4:ℝ) ≤ 0.39 * t := by linarith

/-- Row `stage5-band`.  The collision band needs `4.5 - 1.5/(hP^(1/2)) ≥ 4.4` at
`h = 1`; `P = t²`, `t ≥ 15`, `P ≥ 225`. -/
theorem row_stage5_band (t : ℝ) (ht : 15 ≤ t) : 1.5 / t ≤ 0.1 := by
  rw [div_le_iff₀ (by linarith)]; linarith

/-! ### Theorem 4.4: Claims C and G -/

/-- Row `claimC-1`.  `P^(7/72) ≥ 3`; `P = t^72`, `t ≥ 1.17`, `P ≥ 8.1·10^4`. -/
theorem row_claimC_1 (t : ℝ) (ht : 1.17 ≤ t) : (3:ℝ) ≤ t ^ 7 := by
  have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.17) ht 7
  have : (3:ℝ) ≤ (1.17:ℝ) ^ 7 := by norm_num
  linarith

/-- Row `claimC-2`.  `41 P^(5/36) ≤ P^(1/2)`, i.e. `41 t^5 ≤ t^18` under
`P = t^36`; `t ≥ 1.34`, `P ≥ 3.8·10^4`. -/
theorem row_claimC_2 (t : ℝ) (ht : 1.34 ≤ t) : 41 * t ^ 5 ≤ t ^ 18 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h13 : (41:ℝ) ≤ t ^ 13 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.34) ht 13
    have : (41:ℝ) ≤ (1.34:ℝ) ^ 13 := by norm_num
    linarith
  have e : t ^ 18 = t ^ 5 * t ^ 13 := by ring
  nlinarith [pow_pos ht0 5]

/-- Row `claimG-pref`.  The prefactor `96 P^(-5/24) ≤ 1`; `P = t^24`, `t ≥ 2.5`,
`P ≥ 3.6·10^9`. -/
theorem row_claimG_pref (t : ℝ) (ht : 2.5 ≤ t) : (96:ℝ) ≤ t ^ 5 := by
  have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 2.5) ht 5
  have : (96:ℝ) ≤ (2.5:ℝ) ^ 5 := by norm_num
  linarith

/-- Row `claimG-P36`.  `P^(1/72 - 1/24) = P^(-1/36) ≤ 1`, i.e. `1 ≤ t` under
`P = t^36`.  Holds for every `P ≥ 1`; the content is the exponent arithmetic. -/
theorem row_claimG_P36 (t : ℝ) (ht : 1 ≤ t) : (1:ℝ) ≤ t ^ 1 := by simpa using ht

theorem claimG_P36_exponent : (1:ℚ) / 72 - 1 / 24 = -(1 / 36) := by norm_num

/-! ### Theorem 5.3: window hypotheses -/

/-- Row `st3a-window`.  Stage 3(a)'s Lemma 3.7 hypothesis
`P^(1/2)/(2h₁) ≥ 8(1+|B|)`, read as `0.5 P^(23/48) ≥ 15 P^(10/48)`;
`P = t^48`, `t ≥ 1.3`, `P ≥ 2.9·10^5`. -/
theorem row_st3a_window (t : ℝ) (ht : 1.3 ≤ t) : 15 * t ^ 10 ≤ 0.5 * t ^ 23 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h13 : (30:ℝ) ≤ t ^ 13 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.3) ht 13
    have : (30:ℝ) ≤ (1.3:ℝ) ^ 13 := by norm_num
    linarith
  have e : t ^ 23 = t ^ 10 * t ^ 13 := by ring
  nlinarith [pow_pos ht0 10]

/-- Row `st3b-window`.  The same at `0.5 P^(22/48) ≥ 15 P^(9/48)`. -/
theorem row_st3b_window (t : ℝ) (ht : 1.3 ≤ t) : 15 * t ^ 9 ≤ 0.5 * t ^ 22 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h13 : (30:ℝ) ≤ t ^ 13 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.3) ht 13
    have : (30:ℝ) ≤ (1.3:ℝ) ^ 13 := by norm_num
    linarith
  have e : t ^ 22 = t ^ 9 * t ^ 13 := by ring
  nlinarith [pow_pos ht0 9]

/-- Row `st3a-flat`.  Flat cost `16 h₁P^(1/2) + 30 k h₁h₂P^(5/8) ≤ 46 P^(3/4)`,
i.e. `16 t^25 + 30 t^36 ≤ 46 t^36` under `P = t^48`.  Holds for every `P ≥ 1`. -/
theorem row_st3a_flat (t : ℝ) (ht : 1 ≤ t) :
    16 * t ^ 25 + 30 * t ^ 36 ≤ 46 * t ^ 36 := by
  have h : t ^ 25 ≤ t ^ 36 := pow_le_pow_right₀ ht (by norm_num)
  linarith

/-- Row `st6D1-window`.  Stage 6(D1) needs `P^(1/2) ≥ 8(1 + 7P^(1/4))`, i.e.
`t² ≥ 8 + 56t`; the paper prints `P^(1/4) ≥ 56`, and `t ≥ 57` certifies it. -/
theorem row_st6D1_window (t : ℝ) (ht : 57 ≤ t) : 8 * (1 + 7 * t) ≤ t ^ 2 := by
  nlinarith [sq_nonneg (t - 57)]

/-- Row `st6D1-good`.  `72 t^(-1) P^(-1/2) ≤ 1/4` at `t = 1`; `P = t²`,
`t ≥ 288`, `P ≥ 8.3·10^4`. -/
theorem row_st6D1_good (t : ℝ) (ht : 288 ≤ t) : (72:ℝ) / t ≤ 1 / 4 := by
  rw [div_le_iff₀ (by linarith)]; linarith

/-- Row `5b-j0-window`.  At `j = 0` the sawtooth has `|B| ≤ 6`, so Lemma 3.7
needs `P^(1/2) ≥ 8(1+6) = 56`; `P = t²`, `P ≥ 3136`. -/
theorem row_5b_j0_window (t : ℝ) (ht : 56 ≤ t) : 8 * (1 + 6) ≤ t := by linarith

/-! ### Theorem 5.3, Step 5b: geometry -/

/-- Row `5b-Npieces`.  The common refinement of gap cells, anchor runs and
sawtooth windows has at most `3.5 P^(13/24)` pieces.  Under `P = t^48`: cells
`3t^26 + 2`, anchor runs `22t^15`, windows `5t^16`, against `3.5t^26`.
`t ≥ 1.46`, `P ≥ 7.7·10^7`. -/
theorem row_5b_Npieces (t : ℝ) (ht : 1.46 ≤ t) :
    3 * t ^ 26 + 2 + 22 * t ^ 15 + 5 * t ^ 16 ≤ 3.5 * t ^ 26 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h10 : (44:ℝ) ≤ t ^ 10 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.46) ht 10
    have : (44:ℝ) ≤ (1.46:ℝ) ^ 10 := by norm_num
    linarith
  have h11 : (64:ℝ) ≤ t ^ 11 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.46) ht 11
    have : (64:ℝ) ≤ (1.46:ℝ) ^ 11 := by norm_num
    linarith
  have h26 : (18000:ℝ) ≤ t ^ 26 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.46) ht 26
    have : (18000:ℝ) ≤ (1.46:ℝ) ^ 26 := by norm_num
    linarith
  have k1 : 64 * t ^ 15 ≤ t ^ 26 := by
    have e : t ^ 26 = t ^ 15 * t ^ 11 := by ring
    nlinarith [pow_pos ht0 15]
  have k2 : 44 * t ^ 16 ≤ t ^ 26 := by
    have e : t ^ 26 = t ^ 16 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 16]
  -- 22/64 + 5/44 + 2/18000 = 0.3438 + 0.1137 + 0.0001 < 0.5
  linarith

/-- Row `5b-lam0-range`, upper half.  Lemma 5.2b's `λ₀ ∈ [0.38, 2.44]` opened to
`[0.35, 2.6]`: the `O(P^(-1/4))` and the `±1` in the `β`-bounds must not push
`2.44` past `2.6`.  Clearing denominators with `P = t⁴` gives
`2.44(t+1)(3t²+1)² ≤ 23.4 t^5`; `t ≥ 17`, `P ≥ 8.4·10^4`. -/
theorem row_5b_lam0_upper (t : ℝ) (ht : 17 ≤ t) :
    2.44 * (t + 1) * (3 * t ^ 2 + 1) ^ 2 ≤ 23.4 * t ^ 5 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h4 : 17 * t ^ 4 ≤ t ^ 5 := by
    have e : t ^ 5 = t ^ 4 * t := by ring
    nlinarith [pow_pos ht0 4]
  have h3 : 289 * t ^ 3 ≤ t ^ 5 := by
    have e : t ^ 5 = t ^ 3 * t ^ 2 := by ring
    nlinarith [pow_pos ht0 3, sq_nonneg (t - 17)]
  have h2 : 4913 * t ^ 2 ≤ t ^ 5 := by
    have e : t ^ 5 = t ^ 2 * t ^ 3 := by ring
    nlinarith [pow_pos ht0 2, h3]
  have h1 : 83521 * t ≤ t ^ 5 := by
    have e : t ^ 5 = t * t ^ 4 := by ring
    nlinarith [ht0, h4]
  have h0 : (1419857:ℝ) ≤ t ^ 5 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 17) ht 5
    have : (1419857:ℝ) ≤ (17:ℝ) ^ 5 := by norm_num
    linarith
  nlinarith [h4, h3, h2, h1, h0]

/-- Row `5b-lam0-range`, lower half: `0.38(t-1)(3t²-1)² ≥ 3.15 t^5`. -/
theorem row_5b_lam0_lower (t : ℝ) (ht : 17 ≤ t) :
    3.15 * t ^ 5 ≤ 0.38 * (t - 1) * (3 * t ^ 2 - 1) ^ 2 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h4 : 17 * t ^ 4 ≤ t ^ 5 := by
    have e : t ^ 5 = t ^ 4 * t := by ring
    nlinarith [pow_pos ht0 4]
  have h3 : 289 * t ^ 3 ≤ t ^ 5 := by
    have e : t ^ 5 = t ^ 3 * t ^ 2 := by ring
    nlinarith [pow_pos ht0 3, sq_nonneg (t - 17)]
  have h0 : (1419857:ℝ) ≤ t ^ 5 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 17) ht 5
    have : (1419857:ℝ) ≤ (17:ℝ) ^ 5 := by norm_num
    linarith
  nlinarith [h4, h3, h0, pow_pos ht0 2]

/-! ### Theorem 5.3, Step 5b: the Lemma 3.9 perturbation hypothesis `ρ ≤ ρ₀`

`ρ₀ = c₇/8 = 1/1856` at the exact `c₇ = 1/232`. -/

/-- Row `39-c2`.  `|c''/2|/S ≤ ρ₀`, i.e. `(53/350) P^(-1/4) ≤ 1/1856`;
`P = t⁴`, `t ≥ 282`, `P ≥ 6.3·10^9`. -/
theorem row_39_c2 (t : ℝ) (ht : 282 ≤ t) : (53 / 350 : ℝ) ≤ t / 1856 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1856)]; linarith

/-- Row `39-c3`.  `P|c'''/2|/S ≤ ρ₀`: `(47/350) ≤ t/1856`; `t ≥ 250`. -/
theorem row_39_c3 (t : ℝ) (ht : 250 ≤ t) : (47 / 350 : ℝ) ≤ t / 1856 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1856)]; linarith

/-- Row `39-c4`.  `P²|c''''/2|/S ≤ ρ₀`: `(44/350) ≤ t/1856`; `t ≥ 234`. -/
theorem row_39_c4 (t : ℝ) (ht : 234 ≤ t) : (44 / 350 : ℝ) ≤ t / 1856 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1856)]; linarith

/-- Row `39-beta`.  The `β̃`-substitution error `2.31 P^(-1/2) ≤ ρ₀`;
`P = t²`, `t ≥ 4288`, `P ≥ 1.8·10^7`. -/
theorem row_39_beta (t : ℝ) (ht : 4288 ≤ t) : (2.31 : ℝ) ≤ t / 1856 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1856)]; linarith

/-- Row `39-wave`.  The wave remainder `(4000/7) P^(-5/6) ≤ ρ₀`; `P = t^6`,
`t ≥ 16.1`, `P ≥ 1.7·10^7`. -/
theorem row_39_wave (t : ℝ) (ht : 16.1 ≤ t) : (4000 / 7 : ℝ) ≤ t ^ 5 / 1856 := by
  have h5 : (1060572:ℝ) ≤ t ^ 5 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 16.1) ht 5
    have : (1060572:ℝ) ≤ (16.1:ℝ) ^ 5 := by norm_num
    linarith
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1856)]; linarith

/-! ### Theorem 5.3: the balance comparisons -/

/-- Row `5a-competitors`.  Every Step 5a competitor ratio is `≤ 1/4`
(domination at margin 4).  Under `P = t^48` the four ratios are
`1.3 t^(-6)`, `13 t^(-27)`, `9 t^(-52)`, `3 t^(-6)`; the last binds.
`t ≥ 1.52`, `P ≥ 5.4·10^8`. -/
theorem row_5a_competitors (t : ℝ) (ht : 1.52 ≤ t) :
    (3:ℝ) ≤ t ^ 6 / 4 ∧ (13:ℝ) ≤ t ^ 27 / 4 ∧ (9:ℝ) ≤ t ^ 52 / 4 := by
  have h6 : (12:ℝ) ≤ t ^ 6 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.52) ht 6
    have : (12:ℝ) ≤ (1.52:ℝ) ^ 6 := by norm_num
    linarith
  have h27 : (52:ℝ) ≤ t ^ 27 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.52) ht 27
    have : (52:ℝ) ≤ (1.52:ℝ) ^ 27 := by norm_num
    linarith
  have h52 : (36:ℝ) ≤ t ^ 52 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.52) ht 52
    have : (36:ℝ) ≤ (1.52:ℝ) ^ 52 := by norm_num
    linarith
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Row `5b-E<=c7S`.  The interpolant error alone against the Lemma 3.9 budget:
`E ≤ c₇S/2` at `S = 0.35 P^(-5/8)`.  Multiplying by `P^(5/8)` and substituting
`P = t^48` gives `105.8 + 0.11 t^10 ≤ (7/9280) t^20`.  This is the floor of the
method as `κ → 0`: `t ≥ 1.85`, `P ≥ 6.7·10^12`. -/
theorem row_5b_E_only (t : ℝ) (ht : 1.85 ≤ t) :
    105.8 + 0.11 * t ^ 10 ≤ (7 / 9280) * t ^ 20 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h10 : (469:ℝ) ≤ t ^ 10 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.85) ht 10
    have : (469:ℝ) ≤ (1.85:ℝ) ^ 10 := by norm_num
    linarith
  have k2 : 469 * t ^ 10 ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 10 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 10]
  have k3 : (219961:ℝ) ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 10 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 10]
  -- 0.11/469 = 2.346e-4 and 105.8/219961 = 4.810e-4; sum 7.156e-4 < 7.543e-4
  have b2 : 0.11 * t ^ 10 ≤ 0.00023455 * t ^ 20 := by linarith
  have b3 : (105.8:ℝ) ≤ 0.000481 * t ^ 20 := by linarith
  linarith

/-- Row `5a-W<=c7S`.  Step 5a's balance comparison at the larger scale
`S ≥ 0.60 P^(-5/8)`: `(1/12)√0.6 t^13 + 0.11 t^10 + 105.8 ≤ (3/2320) t^20`,
with `(1/12)√0.6 ≤ 0.06455`.  `t ≥ 1.89`, `P ≥ 1.9·10^13`. -/
theorem row_5a_binding (t : ℝ) (ht : 1.89 ≤ t) :
    0.06455 * t ^ 13 + 0.11 * t ^ 10 + 105.8 ≤ (3 / 2320) * t ^ 20 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h7 : (86:ℝ) ≤ t ^ 7 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.89) ht 7
    have : (86:ℝ) ≤ (1.89:ℝ) ^ 7 := by norm_num
    linarith
  have h10 : (580:ℝ) ≤ t ^ 10 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.89) ht 10
    have : (580:ℝ) ≤ (1.89:ℝ) ^ 10 := by norm_num
    linarith
  have k1 : 86 * t ^ 13 ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 13 * t ^ 7 := by ring
    nlinarith [pow_pos ht0 13]
  have k2 : 580 * t ^ 10 ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 10 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 10]
  have k3 : (336400:ℝ) ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 10 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 10]
  -- 7.506 + 1.897 + 3.146 = 12.549e-4 < 12.931e-4 = 3/2320
  have b1 : 0.06455 * t ^ 13 ≤ 0.0007506 * t ^ 20 := by linarith
  have b2 : 0.11 * t ^ 10 ≤ 0.00018966 * t ^ 20 := by linarith
  have b3 : (105.8:ℝ) ≤ 0.00031451 * t ^ 20 := by linarith
  linarith

/-- **Row `5b-W<=c7S`: this is `P₀`.**  Step 5b's balance comparison at the lower
end `S = 0.35 P^(-5/8)`, with `V = (1/12)S^(1/2)P^(-11/24)`,
`E = 105.8 P^(-25/24) + 0.11 P^(-5/6)` and `c₇ = 1/232`.  Multiplying by
`P^(5/8)` and substituting `P = t^48` gives
`a t^13 + 0.11 t^10 + 105.8 ≤ b t^20` with `a = (1/12)√0.35 ≤ 0.04931` and
`b = 0.35/464 = 7/9280`.

`t ≥ 1.96`, i.e. `P ≥ 1.07·10^14`; the probe's bisection reports `8.95·10^13`.
This row is the maximum over all thirty, hence `P₀`. -/
theorem row_5b_binding (t : ℝ) (ht : 1.96 ≤ t) :
    0.04931 * t ^ 13 + 0.11 * t ^ 10 + 105.8 ≤ (7 / 9280) * t ^ 20 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h7 : (111:ℝ) ≤ t ^ 7 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.96) ht 7
    have : (111:ℝ) ≤ (1.96:ℝ) ^ 7 := by norm_num
    linarith
  have h10 : (836:ℝ) ≤ t ^ 10 := by
    have h := pow_mono_base (by norm_num : (0:ℝ) ≤ 1.96) ht 10
    have : (836:ℝ) ≤ (1.96:ℝ) ^ 10 := by norm_num
    linarith
  have k1 : 111 * t ^ 13 ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 13 * t ^ 7 := by ring
    nlinarith [pow_pos ht0 13]
  have k2 : 836 * t ^ 10 ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 10 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 10]
  have k3 : (698896:ℝ) ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 10 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 10]
  -- 0.04931/111 = 4.4423e-4, so 4.45e-4 is safe; likewise 0.11/836 and 105.8/698896
  have b1 : 0.04931 * t ^ 13 ≤ 0.000445 * t ^ 20 := by linarith
  have b2 : 0.11 * t ^ 10 ≤ 0.00013158 * t ^ 20 := by linarith
  have b3 : (105.8:ℝ) ≤ 0.0001514 * t ^ 20 := by linarith
  -- 4.450 + 1.3158 + 1.5140 = 7.2798 < 7.5431 = 7/9280 (units of 1e-4)
  linarith

/-! ### Section 6 -/

/-- Row `thm63-rem`.  The Lemma 6.2 linearization remainder `P^(43/96)` is inside
`P^(1 - 1/96) = P^(95/96)`; `P = t^96`.  Holds for every `P ≥ 1`. -/
theorem row_thm63_rem (t : ℝ) (ht : 1 ≤ t) : t ^ 43 ≤ t ^ 95 :=
  pow_le_pow_right₀ ht (by norm_num)

end CertificateRows

section GapSharpness

/-- **Lemma 5.2b, step (i).**  The frozen gap satisfies `G = ⌊δ⌋ + κ` with
`κ ∈ {0,1}`, so `|G - δ| = |κ - Int.fract δ| ≤ 1`.  This is the bound that
produces the `52.3125 k(h₁+h₂)P^(-9/8)` of the interpolant error. -/
theorem gap_error_le_one (δ : ℝ) (κ : ℤ) (hκ : κ = 0 ∨ κ = 1) :
    |((⌊δ⌋ + κ : ℤ) : ℝ) - δ| ≤ 1 := by
  have hf := Int.fract_nonneg δ
  have hf' := Int.fract_lt_one δ
  have hfe : Int.fract δ = δ - ⌊δ⌋ := rfl
  rcases hκ with h | h <;> subst h <;> push_cast <;> rw [abs_le] <;>
    constructor <;> linarith

/-- The bound `1` is **attained**: at `δ` an integer and `κ = 1`. -/
theorem gap_error_one_attained : |((⌊(0:ℝ)⌋ + 1 : ℤ) : ℝ) - 0| = 1 := by norm_num

/-- **Recentring cannot halve it.**  The error `κ - Int.fract δ` ranges over a set
of diameter `> 1` — it contains `1` (at `κ = 1`, `δ = 0`) and `-3/4` (at `κ = 0`,
`δ = 3/4`) — so no constant shift `θ` of the interpolant brings every value
within `1/2`.  This is why the paper's `1` is not replaced by `1/2`. -/
theorem gap_error_not_halved_by_recentring (θ : ℝ) :
    1 / 2 < |1 - θ| ∨ 1 / 2 < |(-3 / 4 : ℝ) - θ| := by
  rcases le_or_gt θ (1 / 8) with h | h
  · left
    rw [abs_of_nonneg (by linarith)]
    linarith
  · right
    rw [abs_of_nonpos (by linarith)]
    linarith

end GapSharpness

end Problems.Juggler
