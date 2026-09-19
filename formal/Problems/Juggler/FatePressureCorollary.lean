import Problems.Juggler.FatePressure
import Problems.Juggler.FateOneSidedCorollary

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The conjecture from the pressure and no-momentum hypotheses (Section 9.2's corollaries)

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), the consequences of Theorem 9.2 and
Proposition 9.3: the pressure hypothesis `P_θ(C)` and the no-momentum hypothesis
`M_{θ,q}(C)` each imply the conjecture, in the pattern of Corollary 8.4 and of the one-sided
corollary (`FateOneSidedCorollary`).

Both hypotheses live on the live weight of `LiveCountWeight`, the count of starts in
`{1, …, N}` that stay above the floor for `d` steps, sorted by itinerary. The bridge to the
failure set is `oddFailures_subset_live`: a failure never enters the floor, so the odd
failures of `(y, 2y]` are live starts of `{1, …, 2y}` at every depth. Theorem 9.2 in exact
form (`live_count_le_of_pressure`) then bounds them by `2y e^{-d D(p_C ‖ 1/2)} E`, and
Proposition 9.3 under no momentum (`juggler_count_le_of_noMomentum`, with the Markov tilt
and `tilt_pow_ratio`) by `2y e^{-d (D(p_C ‖ q) - c_x δ)}`. The absorption of a bound
`2y e^{-d(y) D} (log y)^ε` into `y (log y)^{-e}` for every `e < C D / log 2 - ε` is
`absorb`, shared by the two forms, on `OneSided.exp_le_rpow_scale`.

The paper's `E = e^{o(d)}` is quantified here as `(log y)^ε` with `ε ≥ 0` a rate loss
(`PressureBound`), and the paper's `o(d)` momentum as `δ d` (`NoMomentumBound`, the
`NoMomentum` predicate of `TiltedShare` on the live weight); the exponents are
`e(C) - ε` and `C (D(p_C ‖ q) - c_x δ) / log 2`. Each hypothesis composes with Theorem 7.2
twice: with the contagion bound as a hypothesis, and with nothing else assumed through the
unconditional Theorem 5.3 at exponent `13/40`. Not a halt theorem: nothing here bounds a
pressure or a share.
-/

namespace Pressure

/-- **Failures never enter the floor.** Above a certified floor `N₀`, an odd failure of
`(y, 2y]` is a start of `{1, …, 2y}` that is live to every depth. -/
theorem oddFailures_subset_live {N₀ : ℕ}
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y d : ℕ) :
    oddFailures y ⊆ (Icc 1 (2 * y)).filter (fun n => liveTo N₀ n d) := by
  intro n hn
  simp only [oddFailures, mem_filter, mem_Ioc] at hn
  obtain ⟨⟨hyn, hn2y⟩, -, hfail⟩ := hn
  rw [mem_filter, mem_Icc]
  refine ⟨⟨by omega, hn2y⟩, ?_⟩
  intro i _
  by_contra hle
  push Not at hle
  exact hfail (reachesOne_of_iterate rfl (hfloor _ (floorPower_iterate_pos (by omega) i) hle))

/-- The pressure hypothesis `P_θ(C)` at the scale `y`, with the paper's `e^{o(d)}` quantified
as `(log y)^ε`: the live pressure of `{1, …, 2y}` at the tilt `x = p_C/(1-p_C)` and depth
`d(y) = ⌈C L(y)⌉` is at most `2y a_θ^{d(y)} (log y)^ε`. -/
def PressureBound (N₀ : ℕ) (C ε : ℝ) (y : ℕ) : Prop :=
  livePressure N₀ (2 * y) (pC C / (1 - pC C)) (depth C N₀ y) ≤
    2 * y * ((1 + pC C / (1 - pC C)) / 2) ^ (depth C N₀ y) * Real.log y ^ ε

/-- The no-momentum hypothesis `M_{θ,q}(C)` at the scale `y`: on the live weight of
`{1, …, 2y}` at the re-centring tilt `x = p_C(1-q)/(q(1-p_C))`, the excess odd shares
`(s_x(t) - q)^+` over the depths `t < d(y)` sum to at most `δ d(y)`. -/
def NoMomentumBound (N₀ : ℕ) (C q δ : ℝ) (y : ℕ) : Prop :=
  NoMomentum (liveWeight N₀ (2 * y)) (OneSided.tilt (pC C) q) q δ (depth C N₀ y)

/-- The exponent `C (D(p_C ‖ q) - c_x δ) / log 2` of Proposition 9.3 under no momentum,
with `c_x = (x - 1)/a_q` at the re-centring tilt. -/
noncomputable def momentumExponent (C q δ : ℝ) : ℝ :=
  C * (OneSided.klDiv (pC C) q
    - (OneSided.tilt (pC C) q - 1) / (1 + (OneSided.tilt (pC C) q - 1) * q) * δ) / Real.log 2

/-- **The shared absorption.** A bound `2y e^{-d(y) D} (log y)^ε` on the odd failures of
`(y, 2y]` at all large scales, with `d(y) = ⌈C L(y)⌉` and `D ≥ 0`, is below `y (log y)^{-e}`
for every `e < C D / log 2 - ε` and all large `y`. -/
theorem absorb {N₀ : ℕ} (hN : 2 ≤ N₀) (C D ε e : ℝ) (hC : 0 < C) (hD : 0 ≤ D)
    (he : e < C * D / Real.log 2 - ε)
    (hb : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → ((oddFailures y).card : ℝ) ≤
      2 * y * Real.exp (-(depth C N₀ y * D)) * Real.log y ^ ε) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e) := by
  obtain ⟨y₁, hy₁⟩ := hb
  set eD := C * D / Real.log 2 with heD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have heD0 : 0 ≤ eD := by rw [heD]; positivity
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N₀))
  have hδ : 0 < eD - ε - e := by linarith
  set K := 2 * Real.log N₀ ^ eD with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨u, -, hu⟩ := exists_rpow_gt hδ K
  refine ⟨max (max y₁ N₀) (max 2 ⌈Real.exp u⌉₊), ?_⟩
  intro y hy
  have hyy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyN : N₀ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy2 : 2 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hyexp : Real.exp u ≤ y := by
    have h1 : ⌈Real.exp u⌉₊ ≤ y :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlogy_ge : u ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]; exact hyexp
  have hKlt : K < Real.log y ^ (eD - ε - e) := hu _ hlogy_ge
  -- the scale
  set d := depth C N₀ y with hddef
  have hdge : C * scaleL N₀ y ≤ d := Nat.le_ceil _
  set Λ := scaleRatio N₀ y with hΛ
  have hΛdef : Λ = Real.log (2 * y) / Real.log N₀ := rfl
  have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
    Real.log_mul (by norm_num) hy0.ne'
  have hlog2le : Real.log 2 ≤ Real.log y :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hy2)
  have hΛlo : Real.log y / Real.log N₀ ≤ Λ := by
    rw [hΛdef, hlog2y]
    apply div_le_div_of_nonneg_right _ hlogN.le
    linarith
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛlo
  have hexp : Real.exp (-(d * D)) ≤ Λ ^ (-eD) := by
    rw [heD]
    exact OneSided.exp_le_rpow_scale hΛpos hD hdge
  -- the atoms
  set P := Real.log y ^ (-e) with hP
  set Q := Real.log y ^ (-(eD - ε - e)) with hQ
  have hP0 : 0 ≤ P := Real.rpow_nonneg hlogy.le _
  have hQle : Q ≤ 1 / K := by
    rw [hQ, Real.rpow_neg hlogy.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le hK0 hKlt.le
  have hε0 : 0 ≤ Real.log y ^ ε := Real.rpow_nonneg hlogy.le _
  have hT : Λ ^ (-eD) * Real.log y ^ ε ≤ Real.log N₀ ^ eD * (P * Q) := by
    have h1 : Λ ^ (-eD) ≤ (Real.log y / Real.log N₀) ^ (-eD) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hΛlo (by linarith)
    have h2 : (Real.log y / Real.log N₀) ^ (-eD)
        = Real.log y ^ (-eD) * Real.log N₀ ^ eD := by
      rw [Real.div_rpow hlogy.le hlogN.le, Real.rpow_neg hlogN.le, div_inv_eq_mul]
    have h3 : Real.log y ^ (-eD) * Real.log y ^ ε = P * Q := by
      rw [hP, hQ, ← Real.rpow_add hlogy, ← Real.rpow_add hlogy]
      congr 1
      ring
    calc Λ ^ (-eD) * Real.log y ^ ε
        ≤ (Real.log y / Real.log N₀) ^ (-eD) * Real.log y ^ ε :=
          mul_le_mul_of_nonneg_right h1 hε0
      _ = Real.log N₀ ^ eD * (Real.log y ^ (-eD) * Real.log y ^ ε) := by rw [h2]; ring
      _ = Real.log N₀ ^ eD * (P * Q) := by rw [h3]
  have hKne : K ≠ 0 := hK0.ne'
  calc ((oddFailures y).card : ℝ)
      ≤ 2 * y * Real.exp (-(d * D)) * Real.log y ^ ε := hy₁ y hyy₁
    _ ≤ 2 * y * (Λ ^ (-eD) * Real.log y ^ ε) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hε0) (by positivity)
    _ ≤ 2 * y * (Real.log N₀ ^ eD * (P * Q)) := mul_le_mul_of_nonneg_left hT (by positivity)
    _ = K * y * (P * Q) := by rw [hK]; ring
    _ ≤ K * y * (P * (1 / K)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hQle hP0
    _ = y * Real.log y ^ (-e) := by rw [hP]; field_simp

/-! ### The pressure form -/

/-- **Theorem 9.2 absorbed.** Under `P_θ(C)` at all large scales with the loss `ε`, the odd
failures in `(y, 2y]` number at most `y (log y)^{-e}` for every `e < e(C) - ε` and all
large `y`. -/
theorem oddFailures_le_of_pressure {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e) := by
  obtain ⟨y₁, hy₁⟩ := hP
  have hC0 : 0 < C := by linarith
  have hp1 : pC C < 1 := pC_lt_one C hC
  have hp0 : 0 < pC C := by linarith [half_le_pC C hC]
  refine absorb hN C (klHalf (pC C)) ε e hC0 (klHalf_nonneg _ hp0 hp1) he
    ⟨max y₁ (max N₀ 2), ?_⟩
  intro y hy
  have hyy₁ : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hyN : N₀ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy2 : 2 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hd1 : 1 ≤ depth C N₀ y := one_le_depth hN (by omega) hC0
  have hdN : C * Real.logb 2 (Real.log ((2 * y : ℕ) : ℝ) / Real.log N₀)
      ≤ depth C N₀ y := by
    have h : C * scaleL N₀ y ≤ depth C N₀ y := Nat.le_ceil _
    have hc : ((2 * y : ℕ) : ℝ) = 2 * (y : ℝ) := by push_cast; ring
    rw [hc]
    exact h
  have hP' : livePressure N₀ (2 * y) (pC C / (1 - pC C)) (depth C N₀ y) ≤
      ((2 * y : ℕ) : ℝ) * ((1 + pC C / (1 - pC C)) / 2) ^ depth C N₀ y * Real.log y ^ ε := by
    have h := hy₁ y hyy₁
    unfold PressureBound at h
    push_cast
    exact h
  have hlive := live_count_le_of_pressure N₀ (2 * y) hN (by omega) C hC (depth C N₀ y) hd1 hdN
    (Real.log y ^ ε) hP'
  have hcard : ((oddFailures y).card : ℝ) ≤
      (((Icc 1 (2 * y)).filter (fun n => liveTo N₀ n (depth C N₀ y))).card : ℝ) := by
    exact_mod_cast card_le_card (oddFailures_subset_live hfloor y (depth C N₀ y))
  calc ((oddFailures y).card : ℝ) ≤ _ := hcard
    _ ≤ _ := hlive
    _ = 2 * y * Real.exp (-(depth C N₀ y * klHalf (pC C))) * Real.log y ^ ε := by
        push_cast
        ring

/-- **Theorem 9.2's corollary, with the contagion bound as a hypothesis.** -/
theorem pressure_conj_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  tao_rate_implies_conjecture hlam0 hlam1 hlam hlow
    (oddFailures_le_of_pressure hN hfloor C ε e hC he hP)

/-- **Theorem 9.2's corollary with nothing else assumed.** The pressure hypothesis `P_θ(C)`
at all large scales above a certified floor, with `C ≥ 5` and a loss `ε` such that
`27/40 < e < e(C) - ε` for some `e` (a negative `ε` is a stronger hypothesis), gives that
every positive integer reaches `1`. -/
theorem pressure_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε) (he7 : 27 / 40 < e)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Production.conjecture_of_tao_rate he7 (oddFailures_le_of_pressure hN hfloor C ε e hC he hP)

/-! ### The no-momentum form -/

/-- **Proposition 9.3 absorbed.** Under `M_{θ,q}(C)` at all large scales with the momentum
`δ`, the odd failures in `(y, 2y]` number at most `y (log y)^{-e}` for every
`0 ≤ e < C (D(p_C ‖ q) - c_x δ) / log 2` and all large `y`. -/
theorem oddFailures_le_of_noMomentum {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he0 : 0 ≤ e)
    (he : e < momentumExponent C q δ)
    (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e) := by
  obtain ⟨y₁, hy₁⟩ := hM
  have hC0 : 0 < C := by linarith
  have hp1 : pC C < 1 := pC_lt_one C hC
  have hp0 : 0 < pC C := lt_trans hq0 hqp
  set x := OneSided.tilt (pC C) q with hxdef
  have hx1 : 1 ≤ x := OneSided.tilt_ge_one hq0 hqp hp1
  have hx0 : 0 < x := by linarith
  set a := 1 + (x - 1) * q with hadef
  have ha0 : 0 < a := by nlinarith
  set c := (x - 1) / a with hcdef
  set D' := OneSided.klDiv (pC C) q - c * δ with hD'
  have heM : momentumExponent C q δ = C * D' / Real.log 2 := rfl
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD'0 : 0 ≤ D' := by
    by_contra hneg
    push Not at hneg
    have : C * D' / Real.log 2 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hC0 hneg) hlog2
    rw [heM] at he
    linarith
  refine absorb hN C D' 0 e hC0 hD'0 (by rw [heM] at he; linarith)
    ⟨max y₁ (max N₀ 2), ?_⟩
  intro y hy
  have hyy₁ : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hyN : N₀ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy2 : 2 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  have hd1 : 1 ≤ depth C N₀ y := one_le_depth hN (by omega) hC0
  have hdN : C * Real.logb 2 (Real.log ((2 * y : ℕ) : ℝ) / Real.log N₀)
      ≤ depth C N₀ y := by
    have h : C * scaleL N₀ y ≤ depth C N₀ y := Nat.le_ceil _
    have hc : ((2 * y : ℕ) : ℝ) = 2 * (y : ℝ) := by push_cast; ring
    rw [hc]
    exact h
  set d := depth C N₀ y with hddef
  set k := ⌈pC C * d⌉₊ with hk
  have hM' : NoMomentum (liveWeight N₀ (2 * y)) x q δ d := hy₁ y hyy₁
  have hcount := juggler_count_le_of_noMomentum N₀ (2 * y) x q δ hx1 hq0.le d k hM'
  -- failures are live with at least `k` odd letters
  have hsub : oddFailures y ⊆
      (Icc 1 (2 * y)).filter (fun n => liveTo N₀ n d ∧ k ≤ oddCount (itinerary n d)) := by
    intro n hn
    have hn' := oddFailures_subset_live hfloor y d hn
    rw [mem_filter, mem_Icc] at hn'
    rw [mem_filter, mem_Icc]
    refine ⟨hn'.1, hn'.2, ?_⟩
    rw [hk, Nat.ceil_le]
    exact live_oddCount_ge hN (by omega) hn'.1.2 hn'.2 C hC0 hd1 hdN
  have hcard : ((oddFailures y).card : ℝ) ≤ (((Icc 1 (2 * y)).filter
      (fun n => liveTo N₀ n d ∧ k ≤ oddCount (itinerary n d))).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  -- `x^k ≥ x^{p_C d}`, and the tilt identity
  have hxk : x ^ (pC C * d) ≤ x ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (Nat.le_ceil _)
  have hxpd : 0 < x ^ (pC C * d) := Real.rpow_pos_of_pos hx0 _
  have hnum : 0 ≤ ((2 * y : ℕ) : ℝ) * a ^ d * Real.exp (c * (δ * d)) := by positivity
  have hratio := OneSided.tilt_pow_ratio hq0 hqp hp1 d
  rw [← hxdef, ← hadef] at hratio
  calc ((oddFailures y).card : ℝ) ≤ _ := hcard
    _ ≤ ((2 * y : ℕ) : ℝ) * a ^ d * Real.exp (c * (δ * d)) / x ^ k := hcount
    _ ≤ ((2 * y : ℕ) : ℝ) * a ^ d * Real.exp (c * (δ * d)) / x ^ (pC C * d) :=
        div_le_div_of_nonneg_left hnum hxpd hxk
    _ = 2 * y * (a ^ d / x ^ (pC C * d) * Real.exp (c * (δ * d))) := by push_cast; ring
    _ = 2 * y * Real.exp (-(d * D')) * Real.log y ^ (0 : ℝ) := by
        rw [hratio, ← Real.exp_add, Real.rpow_zero, mul_one, hD']
        congr 2
        ring

/-- **Proposition 9.3's corollary, with the contagion bound as a hypothesis.** -/
theorem noMomentum_conj_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he : e < momentumExponent C q δ)
    (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  tao_rate_implies_conjecture hlam0 hlam1 hlam hlow
    (oddFailures_le_of_noMomentum hN hfloor C q δ e hC hq0 hqp (by linarith) he hM)

/-- **Proposition 9.3's corollary with nothing else assumed.** The no-momentum hypothesis
`M_{θ,q}(C)` at all large scales above a certified floor, at the re-centring tilt, with
`C ≥ 5`, `0 < q < p_C` and a momentum `δ` such that
`27/40 < e < C (D(p_C ‖ q) - c_x δ) / log 2` for some `e`, gives that every positive integer
reaches `1`. -/
theorem noMomentum_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he : e < momentumExponent C q δ)
    (he7 : 27 / 40 < e) (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Production.conjecture_of_tao_rate he7
    (oddFailures_le_of_noMomentum hN hfloor C q δ e hC hq0 hqp (by linarith) he hM)

end Pressure

end Problems.Juggler
