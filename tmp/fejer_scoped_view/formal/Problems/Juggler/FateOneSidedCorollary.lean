import Problems.Juggler.FateOneSided
import Problems.Juggler.FateProduction

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The conjecture from the one-sided hypothesis (Theorem 9.1's corollary)

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Theorem 9.1's consequence "hence
`e_q(C) > 1 - λ**` implies the conjecture", as the composition of two theorems already in the
corpus, in the pattern of Corollary 8.4 (`FateCylinderCorollary`).

`OneSided.one_sided_bound_kl` (Theorem 9.1, exact form) says that under the one-sided
hypothesis `H_q(C, A)` at a scale `y` the odd failures in `(y, 2y]` number at most
`(x/a_q) N e^{-d D(p_C ‖ q)} + (x-1) err (d-1) (2x)^{d-1} / x^{p_C d}` with `x` the re-centring
tilt, `d = ⌈C L(y)⌉` and `err = y (log y)^{-A}`. The Tao-type reduction needs
`y (log y)^{-e}` for all large `y`. The step between them is the absorption
(`oddFailures_le_of_one_sided`): `d ≥ C log₂ Λ` turns `e^{-dD}` into
`Λ^{-e_{C,q}}` with `e_{C,q} = C D(p_C ‖ q)/log 2` (`exp_le_rpow_scale`), `d - 1 ≤ C log₂ Λ`
turns `(2x)^{d-1}` into `Λ^{C(1 + log₂ x)}` (`pow_le_rpow_scale`), and
`log y / log N₀ ≤ Λ ≤ 2 log y / log N₀` makes the first term
`(x/a_q)(log N₀)^{e_{C,q}} y (log y)^{-e_{C,q}}` and the second at most a constant times
`y (log y)^{C(1 + log₂ x) + 1 - A}`; both exponent gaps are positive when `e < e_{C,q}` and
`A > C(1 + log₂ x) + 1 + e`.

Two corollaries. `implies_conjecture_of_contagion` keeps the contagion bound of
Theorem 5.3 as a hypothesis with an exponent `λ` satisfying `1 - λ < e`, as Corollary 8.4
does; `one_sided_implies_conjecture` discharges it through the unconditional
`Production.failures_logMass_ge` at exponent `13/40`, so that the one-sided hypothesis at all
large scales with `e_{C,q} > 27/40` gives the conjecture with nothing else assumed; and
`exact_share_implies_conjecture` is the paper's remark after Theorem 9.1, a share bound
with no error term at all, where `A` disappears.

What is not the paper's statement. The paper's Theorem 9.1 has the Azuma exponent `e_q(C)`
and the condition `A > C + e_q(C)`; here the exponent is the Chernoff one of Proposition 9.3,
which the paper records is at least `e_q(C)`, and the condition on `A` is
`A > C(1 + log₂ x) + 1 + e`, because the exact form pays the tilt on the error term too and
the factor `d - 1` is bounded by a multiple of `log y` rather than absorbed into an `ε`. The
condition is sufficient, not sharp: dividing the error by `x^{p_C d}` would lower it by
`C p_C log₂ x`, and the `+ 1` is the crude bound on `d`. The paper's numerical forms (the
least `C` at each `q`) are statements about `λ**` and the entropy function and are not
formalized. Not a halt theorem: nothing here proves the one-sided hypothesis.
-/

namespace OneSided

/-- The one-sided hypothesis `H_q(C, A)` at the scale `y`: every `L(y)`-bad cylinder of depth
`1 ≤ t < d(y) = ⌈C L(y)⌉` sends at most the share `q` of its members, plus `y (log y)^{-A}`,
to an odd next letter. -/
def OneSidedBound (N₀ : ℕ) (C q A : ℝ) (y : ℕ) : Prop :=
  OneSidedShare y (scaleL N₀ y) q (y / Real.log y ^ A) (depth C N₀ y)

/-- The paper's remark after Theorem 9.1: the share bound with no error term. -/
def OneSidedExact (N₀ : ℕ) (C q : ℝ) (y : ℕ) : Prop :=
  OneSidedShare y (scaleL N₀ y) q 0 (depth C N₀ y)

/-- The exponent `e_{C,q} = C D(p_C ‖ q) / log 2` of Proposition 9.3. -/
noncomputable def oneSidedExponent (C q : ℝ) : ℝ := C * klDiv (pC C) q / Real.log 2

/-- A share bound with a smaller error is a share bound with a larger one. -/
theorem OneSidedShare.mono {y : ℕ} {L q err err' : ℝ} {d : ℕ} (h : OneSidedShare y L q err d)
    (hle : err ≤ err') : OneSidedShare y L q err' d := by
  intro t ht1 htd w hw hbad
  exact le_trans (h t ht1 htd w hw hbad) (by linarith)

/-- The exact share bound implies `H_q(C, A)` for every `A`. -/
theorem oneSidedBound_of_exact {N₀ : ℕ} {C q : ℝ} {y : ℕ} (h : OneSidedExact N₀ C q y)
    (A : ℝ) : OneSidedBound N₀ C q A y :=
  OneSidedShare.mono h (by positivity)

/-- Gibbs' inequality: `D(p ‖ q) ≥ 0` for `0 < p, q < 1`. -/
theorem klDiv_nonneg {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ klDiv p q := by
  unfold klDiv
  have h1 : 1 - (p / q)⁻¹ ≤ Real.log (p / q) :=
    Real.one_sub_inv_le_log_of_pos (by positivity)
  have h2 : 1 - ((1 - p) / (1 - q))⁻¹ ≤ Real.log ((1 - p) / (1 - q)) :=
    Real.one_sub_inv_le_log_of_pos (by apply div_pos <;> linarith)
  rw [inv_div] at h1 h2
  have h3 : p * (1 - q / p) = p - q := by field_simp
  have h4 : (1 - p) * (1 - (1 - q) / (1 - p)) = q - p := by
    have : (1 : ℝ) - p ≠ 0 := by linarith
    field_simp
    ring
  have h1' := mul_le_mul_of_nonneg_left h1 hp0.le
  have h2' := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - p)
  linarith

/-- `e^{-dD} ≤ Λ^{-CD/log 2}` once `d ≥ C log₂ Λ` and `D ≥ 0`. -/
theorem exp_le_rpow_scale {Λ C D d : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D)
    (hd : C * Real.logb 2 Λ ≤ d) :
    Real.exp (-(d * D)) ≤ Λ ^ (-(C * D / Real.log 2)) := by
  rw [Real.rpow_def_of_pos hΛ]
  apply Real.exp_le_exp.mpr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : Real.log Λ * (-(C * D / Real.log 2)) = -(C * Real.logb 2 Λ * D) := by
    unfold Real.logb
    field_simp
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_right hd hD]

/-- `(2x)^{d-1} ≤ Λ^{C(1 + log₂ x)}` once `d - 1 ≤ C log₂ Λ`, for `x ≥ 1` and
`Λ ≥ 1`. -/
theorem pow_le_rpow_scale {Λ C x : ℝ} (hΛ : 1 ≤ Λ) (hx : 1 ≤ x) (hC : 0 ≤ C) {d : ℕ}
    (hd : (d : ℝ) - 1 ≤ C * Real.logb 2 Λ) :
    (2 * x) ^ (d - 1) ≤ Λ ^ (C * (1 + Real.logb 2 x)) := by
  have h2x : 1 ≤ 2 * x := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hcast : ((d - 1 : ℕ) : ℝ) ≤ C * Real.logb 2 Λ := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      simp only [Nat.zero_sub, Nat.cast_zero]
      exact mul_nonneg hC (Real.logb_nonneg (by norm_num) hΛ)
    · rw [Nat.cast_sub h]
      simpa using hd
  calc (2 * x) ^ (d - 1) = (2 * x) ^ ((d - 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ (2 * x) ^ (C * Real.logb 2 Λ) := Real.rpow_le_rpow_of_exponent_le h2x hcast
    _ = Λ ^ (C * (1 + Real.logb 2 x)) := by
        rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hΛ0]
        congr 1
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        rw [Real.log_mul (by norm_num) (by linarith)]
        unfold Real.logb
        field_simp

/-- **The absorption.** Under `H_q(C, A)` at all large scales, with `q < p_C`,
`A > C(1 + log₂ x) + 1 + e` for the re-centring tilt `x`, and `e < e_{C,q}`, the odd
failures in `(y, 2y]` number at most `y (log y)^{-e}` for all large `y`. -/
theorem oddFailures_le_of_one_sided {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A) (he : e < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBound N₀ C q A y) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e) := by
  obtain ⟨y₁, hy₁⟩ := hH
  have hC0 : 0 < C := by linarith
  have hp1 : pC C < 1 := pC_lt_one C hC
  have hp0 : 0 < pC C := lt_trans hq0 hqp
  have hq1 : q < 1 := lt_trans hqp hp1
  set x := tilt (pC C) q with hxdef
  have hx1 : 1 ≤ x := tilt_ge_one hq0 hqp hp1
  have hx0 : 0 < x := by linarith
  set a := 1 + (x - 1) * q with hadef
  have ha1 : 1 ≤ a := by rw [hadef]; nlinarith
  have ha0 : 0 < a := by linarith
  set D := klDiv (pC C) q with hDdef
  have hD0 : 0 ≤ D := klDiv_nonneg hp0 hp1 hq0 hq1
  set eOS := oneSidedExponent C q with heOS
  have heOSdef : eOS = C * D / Real.log 2 := rfl
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have heOS0 : 0 ≤ eOS := by rw [heOSdef]; positivity
  set κ := C * (1 + Real.logb 2 x) with hκ
  have hlogbx : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N₀))
  have hδ₁ : 0 < eOS - e := by linarith
  have hδ₂ : 0 < A - κ - 1 - e := by linarith
  -- the two constants
  set K₁ := x / a * Real.log N₀ ^ eOS with hK₁
  set K₂ := (x - 1) * (2 * C / (Real.log 2 * Real.log N₀)) * (2 / Real.log N₀) ^ κ + 1
    with hK₂
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  have hK₂0 : 0 < K₂ := by
    rw [hK₂]
    have : 0 ≤ (x - 1) * (2 * C / (Real.log 2 * Real.log N₀)) * (2 / Real.log N₀) ^ κ :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) (Real.rpow_nonneg (by positivity) _)
    linarith
  obtain ⟨u₁, -, hu₁⟩ := exists_rpow_gt hδ₁ (2 * K₁)
  obtain ⟨u₂, -, hu₂⟩ := exists_rpow_gt hδ₂ (2 * K₂)
  refine ⟨max (max y₁ N₀) (max 2 ⌈Real.exp (max u₁ u₂)⌉₊), ?_⟩
  intro y hy
  have hyy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyN : N₀ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy2 : 2 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hyexp : Real.exp (max u₁ u₂) ≤ y := by
    have h1 : ⌈Real.exp (max u₁ u₂)⌉₊ ≤ y :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlogy_ge : max u₁ u₂ ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]; exact hyexp
  have hK₁' : 2 * K₁ < Real.log y ^ (eOS - e) :=
    hu₁ _ (le_trans (le_max_left _ _) hlogy_ge)
  have hK₂' : 2 * K₂ < Real.log y ^ (A - κ - 1 - e) :=
    hu₂ _ (le_trans (le_max_right _ _) hlogy_ge)
  -- the scale and the depth
  have hd1 : 1 ≤ depth C N₀ y := one_le_depth hN (by omega) hC0
  set d := depth C N₀ y with hddef
  have hdge : C * scaleL N₀ y ≤ d := Nat.le_ceil _
  set Λ := scaleRatio N₀ y with hΛ
  have hΛdef : Λ = Real.log (2 * y) / Real.log N₀ := rfl
  have hLdef : scaleL N₀ y = Real.logb 2 Λ := rfl
  have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
    Real.log_mul (by norm_num) hy0.ne'
  have hlog2le : Real.log 2 ≤ Real.log y :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hy2)
  have hΛlo : Real.log y / Real.log N₀ ≤ Λ := by
    rw [hΛdef, hlog2y]
    apply div_le_div_of_nonneg_right _ hlogN.le
    linarith
  have hΛhi : Λ ≤ 2 * Real.log y / Real.log N₀ := by
    rw [hΛdef, hlog2y]
    apply div_le_div_of_nonneg_right _ hlogN.le
    linarith
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛdef, le_div_iff₀ hlogN, one_mul]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (by omega : N₀ ≤ 2 * y)
  have hΛpos : 0 < Λ := by linarith
  have hL0 : 0 ≤ scaleL N₀ y := by rw [hLdef]; exact Real.logb_nonneg (by norm_num) hΛ1
  have hdlt : (d : ℝ) - 1 < C * scaleL N₀ y := by
    have := Nat.ceil_lt_add_one (mul_nonneg hC0.le hL0)
    rw [hddef]
    unfold depth
    linarith
  -- Theorem 9.1 at this scale
  have hH : OneSidedShare y (scaleL N₀ y) q ((y : ℝ) / Real.log y ^ A) d := hy₁ y hyy₁
  have herr : 0 ≤ (y : ℝ) / Real.log y ^ A := by positivity
  have hmain := one_sided_bound_kl hN hfloor (by omega : 1 ≤ y) hC0 hq0 hqp hp1 herr hd1 hdge hH
  rw [← hxdef, ← hadef, ← hDdef] at hmain
  -- the atoms
  set P := Real.log y ^ (-e) with hP
  set Q₁ := Real.log y ^ (-(eOS - e)) with hQ₁
  set Q₂ := Real.log y ^ (-(A - κ - 1 - e)) with hQ₂
  have hP0 : 0 ≤ P := Real.rpow_nonneg hlogy.le _
  have hQ₁0 : 0 ≤ Q₁ := Real.rpow_nonneg hlogy.le _
  have hQ₂0 : 0 ≤ Q₂ := Real.rpow_nonneg hlogy.le _
  have hQ₁le : Q₁ ≤ 1 / (2 * K₁) := by
    rw [hQ₁, Real.rpow_neg hlogy.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hK₁'.le
  have hQ₂le : Q₂ ≤ 1 / (2 * K₂) := by
    rw [hQ₂, Real.rpow_neg hlogy.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hK₂'.le
  -- term 1: `e^{-dD} ≤ Λ^{-e_{C,q}} ≤ (log N₀)^{e_{C,q}} · P · Q₁`
  have hexp : Real.exp (-(d * D)) ≤ Λ ^ (-eOS) := by
    rw [heOSdef]
    exact exp_le_rpow_scale hΛpos hD0 hdge
  have hT1 : Λ ^ (-eOS) ≤ Real.log N₀ ^ eOS * (P * Q₁) := by
    have h1 : Λ ^ (-eOS) ≤ (Real.log y / Real.log N₀) ^ (-eOS) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hΛlo (by linarith)
    have h2 : (Real.log y / Real.log N₀) ^ (-eOS)
        = Real.log y ^ (-eOS) * Real.log N₀ ^ eOS := by
      rw [Real.div_rpow hlogy.le hlogN.le, Real.rpow_neg hlogN.le, div_inv_eq_mul]
    have h3 : Real.log y ^ (-eOS) = P * Q₁ := by
      rw [hP, hQ₁, ← Real.rpow_add hlogy]
      congr 1
      ring
    rw [h2, h3] at h1
    linarith
  have hN_le : ((cylinder y 0 []).card : ℝ) ≤ y := by exact_mod_cast card_cylinder_zero_le y
  have hterm1 : x / a * (cylinder y 0 []).card * Real.exp (-(d * D)) ≤ y * P / 2 := by
    calc x / a * (cylinder y 0 []).card * Real.exp (-(d * D))
        ≤ x / a * y * Λ ^ (-eOS) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hN_le (by positivity)) hexp
            (Real.exp_pos _).le (by positivity)
      _ ≤ x / a * y * (Real.log N₀ ^ eOS * (P * Q₁)) :=
          mul_le_mul_of_nonneg_left hT1 (by positivity)
      _ = K₁ * y * (P * Q₁) := by rw [hK₁]; ring
      _ ≤ K₁ * y * (P * (1 / (2 * K₁))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hQ₁le hP0
      _ = y * P / 2 := by field_simp
  -- term 2: `(d-1)(2x)^{d-1} / x^{p_C d} ≤ (K_d log y)(M (log y)^κ)`
  have hxp1 : 1 ≤ x ^ (pC C * d) := Real.one_le_rpow hx1 (by positivity)
  have hd_le : (d : ℝ) - 1 ≤ 2 * C / (Real.log 2 * Real.log N₀) * Real.log y := by
    have hlogΛ : Real.log Λ ≤ Λ - 1 := Real.log_le_sub_one_of_pos hΛpos
    have hL : scaleL N₀ y = Real.log Λ / Real.log 2 := rfl
    have h1 : C * scaleL N₀ y ≤ C * (Λ / Real.log 2) := by
      rw [hL]
      apply mul_le_mul_of_nonneg_left _ hC0.le
      apply div_le_div_of_nonneg_right _ hlog2.le
      linarith
    have h2 : C * (Λ / Real.log 2) ≤ C * ((2 * Real.log y / Real.log N₀) / Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ hC0.le
      exact div_le_div_of_nonneg_right hΛhi hlog2.le
    have h3 : C * ((2 * Real.log y / Real.log N₀) / Real.log 2)
        = 2 * C / (Real.log 2 * Real.log N₀) * Real.log y := by
      field_simp
    linarith
  have hpow : (2 * x) ^ (d - 1) ≤ Λ ^ κ := pow_le_rpow_scale hΛ1 hx1 hC0.le hdlt.le
  have hΛκ : Λ ^ κ ≤ (2 / Real.log N₀) ^ κ * Real.log y ^ κ := by
    calc Λ ^ κ ≤ (2 * Real.log y / Real.log N₀) ^ κ := Real.rpow_le_rpow hΛpos.le hΛhi hκ0
      _ = (2 / Real.log N₀) ^ κ * Real.log y ^ κ := by
          rw [show 2 * Real.log y / Real.log N₀ = (2 / Real.log N₀) * Real.log y by ring,
            Real.mul_rpow (by positivity) hlogy.le]
  have hT2 : Real.log y ^ (-A) * Real.log y * Real.log y ^ κ = P * Q₂ := by
    rw [hP, hQ₂, ← Real.rpow_add hlogy, ← Real.rpow_add_one hlogy.ne',
      ← Real.rpow_add hlogy]
    congr 1
    ring
  have hterm2 : (x - 1) * ((y : ℝ) / Real.log y ^ A) * ((d : ℝ) - 1) * (2 * x) ^ (d - 1)
      / x ^ (pC C * d) ≤ y * P / 2 := by
    have hx1' : 0 ≤ x - 1 := by linarith
    have hdm : 0 ≤ (d : ℝ) - 1 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      linarith
    have hpow0 : 0 ≤ (2 * x) ^ (d - 1) := by positivity
    have hA0 : 0 < Real.log y ^ A := Real.rpow_pos_of_pos hlogy _
    set Kd := 2 * C / (Real.log 2 * Real.log N₀) with hKd
    set M := (2 / Real.log N₀) ^ κ with hM
    have hM0 : 0 ≤ M := Real.rpow_nonneg (by positivity) _
    have hKd0 : 0 ≤ Kd := by positivity
    have hyA : 0 ≤ (y : ℝ) / Real.log y ^ A := by positivity
    calc (x - 1) * ((y : ℝ) / Real.log y ^ A) * ((d : ℝ) - 1) * (2 * x) ^ (d - 1)
          / x ^ (pC C * d)
        ≤ (x - 1) * ((y : ℝ) / Real.log y ^ A) * ((d : ℝ) - 1) * (2 * x) ^ (d - 1) :=
          div_le_self (mul_nonneg (mul_nonneg (mul_nonneg hx1' hyA) hdm) hpow0) hxp1
      _ ≤ (x - 1) * ((y : ℝ) / Real.log y ^ A) * (Kd * Real.log y)
            * (M * Real.log y ^ κ) := by
          apply mul_le_mul _ (le_trans hpow hΛκ) hpow0
            (mul_nonneg (mul_nonneg hx1' hyA) (by positivity))
          exact mul_le_mul_of_nonneg_left hd_le (mul_nonneg hx1' hyA)
      _ = (x - 1) * Kd * M * y * (Real.log y ^ (-A) * Real.log y * Real.log y ^ κ) := by
          rw [Real.rpow_neg hlogy.le]
          field_simp
      _ = (x - 1) * Kd * M * y * (P * Q₂) := by rw [hT2]
      _ ≤ K₂ * y * (P * Q₂) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hP0 hQ₂0)
          apply mul_le_mul_of_nonneg_right _ hy0.le
          rw [hK₂]
          linarith
      _ ≤ K₂ * y * (P * (1 / (2 * K₂))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hQ₂le hP0
      _ = y * P / 2 := by field_simp
  calc ((oddFailures y).card : ℝ) ≤ _ := hmain
    _ ≤ y * P / 2 + y * P / 2 := add_le_add hterm1 hterm2
    _ = y * Real.log y ^ (-e) := by rw [hP]; ring

/-- **Theorem 9.1's corollary, with the contagion bound as a hypothesis.** If `H_q(C, A)`
holds at all large scales with `C ≥ 5`, `0 < q < p_C`, `A > C(1 + log₂ x) + 1 + e` and
`e < e_{C,q}`, and the contagion bound of Theorem 5.3 holds for the failure set with an
exponent `λ` satisfying `1 - λ < e`, then every positive integer reaches `1`. -/
theorem implies_conjecture_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A) (he : e < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBound N₀ C q A y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  tao_rate_implies_conjecture hlam0 hlam1 hlam hlow
    (oddFailures_le_of_one_sided hN hfloor C q A e hC hq0 hqp hA he hH)

/-- **Theorem 9.1's corollary with nothing else assumed.** If `H_q(C, A)` holds at all large
scales above a certified floor, with `C ≥ 5`, `0 < q < p_C`, `A > C(1 + log₂ x) + 1 + e`
and `27/40 < e < e_{C,q}`, then every positive integer reaches `1`; the contagion side is
the unconditional Theorem 5.3 at exponent `13/40`. -/
theorem one_sided_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A) (he : e < oneSidedExponent C q)
    (he7 : 27 / 40 < e) (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBound N₀ C q A y) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Production.conjecture_of_tao_rate he7
    (oddFailures_le_of_one_sided hN hfloor C q A e hC hq0 hqp hA he hH)

/-- **The paper's remark after Theorem 9.1, with nothing else assumed.** If no `L(y)`-bad
cylinder of depth below `⌈C L(y)⌉` sends more than the share `q` of its members to an odd
next letter, at all large scales above a certified floor, with `C ≥ 5`, `0 < q < p_C` and
`e_{C,q} > 27/40`, then every positive integer reaches `1`. -/
theorem exact_share_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (heOS : 27 / 40 < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedExact N₀ C q y) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  obtain ⟨y₁, hy₁⟩ := hH
  set e := (27 / 40 + oneSidedExponent C q) / 2 with he
  set A := C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e + 1 with hA
  refine one_sided_implies_conjecture hN hfloor C q A e hC hq0 hqp (by rw [hA]; linarith)
    (by rw [he]; linarith) (by rw [he]; linarith) ⟨y₁, fun y hy => ?_⟩
  exact oneSidedBound_of_exact (hy₁ y hy) A

end OneSided

end Problems.Juggler
