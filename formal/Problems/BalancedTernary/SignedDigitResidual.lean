import BTCalculus.Normalization
import Problems.BalancedTernary.FiniteStateDynamics

namespace Problems.BalancedTernary

open BTCalculus

/-!
Residual dynamics ``F_{λ,U}(s,u) = λ · DZ(s+u)`` for a bounded raw
alphabet. Doubled-trit normalization and streaming ``D(x+y)`` are
special alphabets of this map. This file does not repeat
``doubledTrit_*`` or ``dAdd_*``.
-/

/-- One residual step of `F_{gain,U}`: from residual `s` and raw letter `u`, the next
residual is `gain * DZ (s + u)`. -/
def signedNext (gain s u : ℤ) : ℤ :=
  gain * DZ (s + u)

/-- The digit emitted by a residual step: the least significant trit of `s + u`. -/
def signedOut (s u : ℤ) : ℤ :=
  lsdZ (s + u)

/-- An integer of absolute value at most `1` is a trit. -/
theorem isTrit_of_natAbs_le_one {u : ℤ} (h : u.natAbs ≤ 1) : isTrit u :=
  natAbs_le_one_iff.mp h

/-- A trit carries nothing: `DZ u = 0` whenever `u` is a trit. -/
theorem DZ_of_trit {u : ℤ} (h : isTrit u) : DZ u = 0 := by
  rcases h with h | h | h <;> simp [h, DZ, lsdZ]

/-- Trit forcing: from residual ``0``, any ``|u|≤1`` stays at ``0`` for every gain. -/
theorem origin_trit_forcing {gain u : ℤ} (hu : u.natAbs ≤ 1) :
    signedNext gain 0 u = 0 := by
  have htrit := isTrit_of_natAbs_le_one hu
  simp [signedNext, DZ_of_trit htrit]

/-- The `gain = 3` case of trit forcing: from residual `0`, any `|u| <= 1` stays at `0`. -/
theorem gain3_m1_origin {u : ℤ} (hu : u.natAbs ≤ 1) :
    signedNext 3 0 u = 0 :=
  origin_trit_forcing hu

/-- Sharp ``λ=1`` reachable/invariant radius ``⌊m/2⌋``. The looser
``⌈(m+1)/2⌉`` from ``3|DZ n|≤|n|+1`` is not required. -/
theorem lambda1_radius_div (m : ℕ) :
    (m / 2 + m + 1) / 3 ≤ m / 2 := by
  omega

/-- The sharp `lambda = 1` box is invariant: if `|s| <= m / 2` and `|u| <= m`, then
`|DZ (s + u)| <= m / 2`. -/
theorem lambda1_reachable_box {s u : ℤ} {m : ℕ}
    (hs : s.natAbs ≤ m / 2) (hu : u.natAbs ≤ m) :
    (DZ (s + u)).natAbs ≤ m / 2 := by
  have hsum : (s + u).natAbs ≤ s.natAbs + u.natAbs := Int.natAbs_add_le s u
  have hB : (s + u).natAbs ≤ m / 2 + m := by omega
  have hdz := DZ_le_of_abs_le (B := m / 2 + m) hB
  have : (m / 2 + m + 1) / 3 ≤ m / 2 := lambda1_radius_div m
  omega

/-- The `m = 2` instance of the `lambda = 1` box: `|s| <= 1` and `|u| <= 2` give
`|DZ (s + u)| <= 1`. -/
theorem lambda1_u2_residual_closure {s u : ℤ}
    (hs : s.natAbs ≤ 1) (hu : u.natAbs ≤ 2) :
    (DZ (s + u)).natAbs ≤ 1 :=
  lambda1_reachable_box (m := 2) hs hu

/-- Strict decrease of ``|s|`` outside the sharp ``λ=1`` box. -/
theorem lambda1_lyapunov {s u : ℤ} {m : ℕ}
    (hs : m + 2 ≤ 2 * s.natAbs) (hu : u.natAbs ≤ m) :
    (DZ (s + u)).natAbs < s.natAbs := by
  have hsum : (s + u).natAbs ≤ s.natAbs + u.natAbs := Int.natAbs_add_le s u
  have hB : (s + u).natAbs ≤ s.natAbs + m := by omega
  have hb := DZ_carry_bound (s + u)
  have : 3 * (DZ (s + u)).natAbs ≤ s.natAbs + m + 1 := by omega
  have hpos : 0 < s.natAbs := by omega
  omega

/-- Sufficient invariant interval for gain ``2``: radius ``2(m+1)``. -/
theorem lambda2_box_invariant {s u : ℤ} {m : ℕ}
    (hs : s.natAbs ≤ 2 * (m + 1)) (hu : u.natAbs ≤ m) :
    (2 * DZ (s + u)).natAbs ≤ 2 * (m + 1) := by
  have hsum : (s + u).natAbs ≤ s.natAbs + u.natAbs := Int.natAbs_add_le s u
  have hB : (s + u).natAbs ≤ 2 * (m + 1) + m := by omega
  have hb := DZ_carry_bound (s + u)
  have : 3 * (DZ (s + u)).natAbs ≤ 2 * (m + 1) + m + 1 := by omega
  have hmul : (2 * DZ (s + u)).natAbs = 2 * (DZ (s + u)).natAbs := by
    simp [Int.natAbs_mul]
  omega

/-- Sharp ``λ=2`` invariant radius ``2 m.pred``. -/
theorem lambda2_sharp_box {s u : ℤ} {m : ℕ}
    (hs : s.natAbs ≤ 2 * m.pred) (hu : u.natAbs ≤ m) :
    (2 * DZ (s + u)).natAbs ≤ 2 * m.pred := by
  have hsum : (s + u).natAbs ≤ s.natAbs + u.natAbs := Int.natAbs_add_le s u
  have hB : (s + u).natAbs ≤ 2 * m.pred + m := by omega
  have hb := DZ_carry_bound (s + u)
  have h3 : 3 * (DZ (s + u)).natAbs ≤ 2 * m.pred + m + 1 := by omega
  have hmul : (2 * DZ (s + u)).natAbs = 2 * (DZ (s + u)).natAbs := by
    simp [Int.natAbs_mul]
  have hdz : (DZ (s + u)).natAbs ≤ m.pred := by
    cases m with
    | zero => omega
    | succ k =>
      simp [Nat.pred_succ] at hs h3 ⊢
      omega
  omega

/-- Constant control `u = 2` at `gain = 3` advances the residual by exactly one multiple
of `3`: `signedNext 3 (3 * n) 2 = 3 * (n + 1)`. -/
theorem signedNext_gain3_control2 (n : ℤ) :
    signedNext 3 (3 * n) 2 = 3 * (n + 1) := by
  simp [signedNext, DZ_three_mul_add_two]

/-- The `gain = 3`, `u = 2` orbit from `0` in closed form: its `n`-th term is `3 * n`. -/
theorem gain3_control2_eq (n : ℕ) : carryGain3 n = 3 * (n : ℤ) :=
  carryGain3_eq n

/-- That orbit leaves every bound: for each `B` some iterate exceeds `B` in absolute value. -/
theorem gain3_control2_unbounded (B : ℕ) :
    ∃ n : ℕ, B < (carryGain3 n).natAbs :=
  carryGain3_unbounded B

/-- Finite invariant box for ``F_{λ,U_m}`` iff ``λ≤2`` or trit forcing ``m≤1``.
The matching unbounded witnesses are ``signedIterate_unbounded_of_ge_three``. -/
theorem finite_residual_condition {gain m : ℕ}
    (h : gain ≤ 2 ∨ m ≤ 1) :
    ∃ R : ℕ, ∀ s u : ℤ, s.natAbs ≤ R → u.natAbs ≤ m →
      ((gain : ℤ) * DZ (s + u)).natAbs ≤ R := by
  rcases h with hgain | hm
  · have hcases : gain = 0 ∨ gain = 1 ∨ gain = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · refine ⟨0, ?_⟩
      intro s u hs hu
      simp [h0]
    · refine ⟨m / 2, ?_⟩
      intro s u hs hu
      simp [h1, lambda1_reachable_box hs hu]
    · refine ⟨2 * m.pred, ?_⟩
      intro s u hs hu
      simpa [h2] using lambda2_sharp_box (s := s) (u := u) (m := m) hs hu
  · refine ⟨0, ?_⟩
    intro s u hs hu
    have hs0 : s = 0 := Int.natAbs_eq_zero.mp (by omega)
    have hstep := origin_trit_forcing (gain := (gain : ℤ)) (u := u) (by omega)
    simp [signedNext] at hstep
    simpa [hs0] using hstep

/-- The least significant trit is at most `1`. -/
theorem lsdZ_le_one (n : ℤ) : lsdZ n ≤ 1 := by
  rcases lsdZ_is_trit n with h | h | h <;> omega

/-- The least significant trit is at least `-1`. -/
theorem lsdZ_ge_neg_one (n : ℤ) : -1 ≤ lsdZ n := by
  rcases lsdZ_is_trit n with h | h | h <;> omega

/-- At `gain = 3` the residual step is a pure trit subtraction:
`signedNext 3 s u = s + u - lsdZ (s + u)`. -/
theorem signedNext_gain3 (s u : ℤ) :
    signedNext 3 s u = s + u - lsdZ (s + u) := by
  have h := sub_lsd_eq_three_DZ (s + u)
  simp [signedNext]
  linarith

/-- At `gain = 3` a control `u >= 2` moves the residual up by at least `1`, since the
subtracted trit is at most `1`. -/
theorem signedNext_gain3_ge {s u : ℤ} (hu : 2 ≤ u) :
    s + 1 ≤ signedNext 3 s u := by
  have hstep := signedNext_gain3 s u
  have hlsd := lsdZ_le_one (s + u)
  omega

/-- At `gain = 3` a control `u <= -2` moves the residual down by at least `1`, since the
subtracted trit is at least `-1`. -/
theorem signedNext_gain3_le {s u : ℤ} (hu : u ≤ -2) :
    signedNext 3 s u ≤ s - 1 := by
  have hstep := signedNext_gain3 s u
  have hlsd := lsdZ_ge_neg_one (s + u)
  omega

/-- The carry of an integer at least `2` is at least `1`. -/
theorem DZ_ge_one_of_ge_two {n : ℤ} (h : 2 ≤ n) : 1 ≤ DZ n := by
  have hn : n = lsdZ n + 3 * DZ n := decomp n
  have hlsd := lsdZ_le_one n
  by_contra hfail
  have : DZ n ≤ 0 := by omega
  omega

/-- The carry of an integer at most `-2` is at most `-1`. -/
theorem DZ_le_neg_one_of_le_neg_two {n : ℤ} (h : n ≤ -2) : DZ n ≤ -1 := by
  have hn : n = lsdZ n + 3 * DZ n := decomp n
  have hlsd := lsdZ_ge_neg_one n
  by_contra hfail
  have : 0 ≤ DZ n := by omega
  omega

/-- At `gain >= 4` the step is strictly expanding on the nonnegative ray: from `s >= 0`
with control `u >= 2`, the next residual is strictly larger than `s`. -/
theorem signedNext_gain_ge_four_expands {gain s u : ℤ}
    (hg : (4 : ℤ) ≤ gain) (hs : 0 ≤ s) (hu : (2 : ℤ) ≤ u) :
    s < signedNext gain s u := by
  have hsum : (2 : ℤ) ≤ s + u := by omega
  have hnn : 0 ≤ s + u := by omega
  have hdz : 1 ≤ DZ (s + u) := DZ_ge_one_of_ge_two hsum
  have hlow := DZ_carry_lower (s + u)
  have hnat : ((s + u).natAbs : ℤ) = s + u := Int.natAbs_of_nonneg hnn
  have hdzAbs : ((DZ (s + u)).natAbs : ℤ) = DZ (s + u) :=
    Int.natAbs_of_nonneg (by omega)
  have hlin : s + u - 1 ≤ 3 * DZ (s + u) := by
    have : ((s + u).natAbs : ℤ) ≤ 3 * ((DZ (s + u)).natAbs : ℤ) + 1 := by
      exact_mod_cast hlow
    omega
  have hmul : gain * (s + u - 1) ≤ 3 * (gain * DZ (s + u)) := by
    have hgain : 0 ≤ gain := by omega
    nlinarith
  have hge : (4 : ℤ) * (s + 1) ≤ gain * (s + u - 1) := by nlinarith
  have hchain : 4 * (s + 1) ≤ 3 * signedNext gain s u := by
    simpa [signedNext] using le_trans hge hmul
  by_contra hle
  have hs' : signedNext gain s u ≤ s := Int.not_lt.mp hle
  have : 4 * (s + 1) ≤ 3 * s := le_trans hchain (by nlinarith [hs'])
  omega

/-- The mirror statement at `gain >= 4`: from `s <= 0` with control `u <= -2`, the next
residual is strictly smaller than `s`. -/
theorem signedNext_gain_ge_four_contracts_neg {gain s u : ℤ}
    (hg : (4 : ℤ) ≤ gain) (hs : s ≤ 0) (hu : u ≤ -2) :
    signedNext gain s u < s := by
  have hsum : s + u ≤ -2 := by omega
  have hnn : s + u ≤ 0 := by omega
  have hdz : DZ (s + u) ≤ -1 := DZ_le_neg_one_of_le_neg_two hsum
  have hlow := DZ_carry_lower (s + u)
  have hnat' : ((s + u).natAbs : ℤ) = -(s + u) := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have hdzAbs : ((DZ (s + u)).natAbs : ℤ) = -(DZ (s + u)) := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have hlin : 3 * DZ (s + u) - 1 ≤ s + u := by
    have : ((s + u).natAbs : ℤ) ≤ 3 * ((DZ (s + u)).natAbs : ℤ) + 1 := by
      exact_mod_cast hlow
    omega
  by_contra hle
  have hs' : s ≤ gain * DZ (s + u) := by
    simpa [signedNext] using Int.not_lt.mp hle
  have hprod : DZ (s + u) * (3 - gain) ≤ u + 1 := by nlinarith
  have hlo : (1 : ℤ) ≤ DZ (s + u) * (3 - gain) := by nlinarith
  omega

/-- The constant-control orbit of `F_{gain,U}` started at residual `0`: iterate
`signedNext gain . u` from `0`. -/
def signedIterate (gain u : ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => signedNext gain (signedIterate gain u n) u

/-- The orbit starts at `0`. -/
theorem signedIterate_zero (gain u : ℤ) : signedIterate gain u 0 = 0 :=
  rfl

/-- The orbit's recurrence: each term is one `signedNext` step from the previous one. -/
theorem signedIterate_succ (gain u n) :
    signedIterate gain u (n + 1) = signedNext gain (signedIterate gain u n) u :=
  rfl

/-- At `gain = 3` with control `u >= 2`, the `n`-th iterate is at least `n`: each step
gains at least `1`. -/
theorem signedIterate_gain3_ge {u : ℤ} (hu : 2 ≤ u) :
    ∀ n : ℕ, (n : ℤ) ≤ signedIterate 3 u n := by
  intro n
  induction n with
  | zero => simp [signedIterate]
  | succ n ih =>
    have h := signedNext_gain3_ge (s := signedIterate 3 u n) hu
    have hsucc : (n + 1 : ℤ) ≤ signedIterate 3 u n + 1 := by omega
    have hstep : signedIterate 3 u n + 1 ≤ signedNext 3 (signedIterate 3 u n) u := h
    simpa [signedIterate] using le_trans hsucc hstep

/-- At `gain = 3` with control `u <= -2`, the `n`-th iterate is at most `-n`. -/
theorem signedIterate_gain3_le {u : ℤ} (hu : u ≤ -2) :
    ∀ n : ℕ, signedIterate 3 u n ≤ - (n : ℤ) := by
  intro n
  induction n with
  | zero => simp [signedIterate]
  | succ n ih =>
    have h := signedNext_gain3_le (s := signedIterate 3 u n) hu
    have : signedNext 3 (signedIterate 3 u n) u ≤ signedIterate 3 u n - 1 := h
    have : signedIterate 3 u n - 1 ≤ -((n : ℤ) + 1) := by omega
    simpa [signedIterate] using le_trans ‹signedNext 3 (signedIterate 3 u n) u ≤ signedIterate 3 u n - 1› this

/-- At `gain >= 4` with control `u >= 2`, the `n`-th iterate is at least `n`. -/
theorem signedIterate_gain_ge_four_ge {gain u : ℤ}
    (hg : (4 : ℤ) ≤ gain) (hu : (2 : ℤ) ≤ u) :
    ∀ n : ℕ, (n : ℤ) ≤ signedIterate gain u n := by
  intro n
  induction n with
  | zero => simp [signedIterate]
  | succ n ih =>
    have hs : 0 ≤ signedIterate gain u n := le_trans (Nat.cast_nonneg n) ih
    have h := signedNext_gain_ge_four_expands (gain := gain)
      (s := signedIterate gain u n) (u := u) hg hs hu
    have : (n + 1 : ℤ) ≤ signedIterate gain u n + 1 := by omega
    have : signedIterate gain u n + 1 ≤ signedNext gain (signedIterate gain u n) u := by omega
    simpa [signedIterate] using
      le_trans ‹(n + 1 : ℤ) ≤ signedIterate gain u n + 1› this

/-- At `gain >= 4` with control `u <= -2`, the `n`-th iterate is at most `-n`. -/
theorem signedIterate_gain_ge_four_le {gain u : ℤ}
    (hg : (4 : ℤ) ≤ gain) (hu : u ≤ -2) :
    ∀ n : ℕ, signedIterate gain u n ≤ - (n : ℤ) := by
  intro n
  induction n with
  | zero => simp [signedIterate]
  | succ n ih =>
    have hs : signedIterate gain u n ≤ 0 := le_trans ih (by omega)
    have h := signedNext_gain_ge_four_contracts_neg (gain := gain)
      (s := signedIterate gain u n) (u := u) hg hs hu
    have : signedNext gain (signedIterate gain u n) u ≤ signedIterate gain u n - 1 := by omega
    have : signedIterate gain u n - 1 ≤ -((n : ℤ) + 1) := by omega
    simpa [signedIterate] using
      le_trans ‹signedNext gain (signedIterate gain u n) u ≤ signedIterate gain u n - 1› this

/-- Transfer of a lower bound on a nonnegative integer to its `natAbs`. -/
theorem signedIterate_natAbs_ge_of_nonneg {x : ℤ} {n : ℕ}
    (hx : 0 ≤ x) (hn : (n : ℤ) ≤ x) : n ≤ x.natAbs := by
  have : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hx
  omega

/-- Escape at every gain `>= 3`: if `|u| >= 2`, the constant-control orbit from `0` is
unbounded -- for each bound `B` some iterate exceeds it. This is the witness matching
`finite_residual_condition`. -/
theorem signedIterate_unbounded_of_ge_three {gain u : ℤ}
    (hg : (3 : ℤ) ≤ gain) (hu : 2 ≤ u ∨ u ≤ -2) (B : ℕ) :
    ∃ n : ℕ, B < (signedIterate gain u n).natAbs := by
  refine ⟨B + 1, ?_⟩
  rcases hu with hpos | hneg
  · by_cases h3 : gain = 3
    · subst h3
      have hge := signedIterate_gain3_ge hpos (B + 1)
      have hx : 0 ≤ signedIterate 3 u (B + 1) :=
        le_trans (Nat.cast_nonneg (B + 1)) hge
      have : B + 1 ≤ (signedIterate 3 u (B + 1)).natAbs :=
        signedIterate_natAbs_ge_of_nonneg hx hge
      omega
    · have hg4 : (4 : ℤ) ≤ gain := by omega
      have hge := signedIterate_gain_ge_four_ge hg4 hpos (B + 1)
      have hx : 0 ≤ signedIterate gain u (B + 1) :=
        le_trans (Nat.cast_nonneg (B + 1)) hge
      have : B + 1 ≤ (signedIterate gain u (B + 1)).natAbs :=
        signedIterate_natAbs_ge_of_nonneg hx hge
      omega
  · by_cases h3 : gain = 3
    · subst h3
      have hle := signedIterate_gain3_le hneg (B + 1)
      have hxneg : 0 ≤ -signedIterate 3 u (B + 1) := by omega
      have hge : (B + 1 : ℤ) ≤ -signedIterate 3 u (B + 1) := by omega
      have : B + 1 ≤ (-signedIterate 3 u (B + 1)).natAbs :=
        signedIterate_natAbs_ge_of_nonneg hxneg hge
      simpa [Int.natAbs_neg] using Nat.lt_of_succ_le this
    · have hg4 : (4 : ℤ) ≤ gain := by omega
      have hle := signedIterate_gain_ge_four_le hg4 hneg (B + 1)
      have hxneg : 0 ≤ -signedIterate gain u (B + 1) := by omega
      have hge : (B + 1 : ℤ) ≤ -signedIterate gain u (B + 1) := by omega
      have : B + 1 ≤ (-signedIterate gain u (B + 1)).natAbs :=
        signedIterate_natAbs_ge_of_nonneg hxneg hge
      simpa [Int.natAbs_neg] using Nat.lt_of_succ_le this

/-- Residual and LSD output depend on the raw contribution only. -/
theorem same_raw_same_residual (gain s u v : ℤ) (huv : u = v) :
    signedNext gain s u = signedNext gain s v ∧
      signedOut s u = signedOut s v := by
  simp [huv]

/-- The finite/infinite phase law as an equivalence: a finite invariant box containing `0`
exists exactly when `gain <= 2` or `m <= 1`. Forward is `finite_residual_condition`;
the converse runs `signedIterate_unbounded_of_ge_three` out of any candidate box. -/
theorem origin_residual_box_iff (gain m : ℕ) :
    (gain ≤ 2 ∨ m ≤ 1) ↔
      ∃ R : ℕ, ∀ s u : ℤ, s.natAbs ≤ R → u.natAbs ≤ m →
        ((gain : ℤ) * DZ (s + u)).natAbs ≤ R := by
  constructor
  · exact finite_residual_condition
  · intro hR
    by_contra hfail
    have hg : 3 ≤ gain := by omega
    have hm : 2 ≤ m := by omega
    obtain ⟨R, hbox⟩ := hR
    obtain ⟨n, hn⟩ :=
      signedIterate_unbounded_of_ge_three (gain := (gain : ℤ)) (u := (m : ℤ))
        (by exact_mod_cast hg) (Or.inl (by exact_mod_cast hm)) R
    -- The iterate stays inside every invariant box if |u|≤m, starting at 0.
    have hstay : ∀ k : ℕ, (signedIterate (gain : ℤ) (m : ℤ) k).natAbs ≤ R := by
      intro k
      induction k with
      | zero => simp [signedIterate]
      | succ k ih =>
        have hu : ((m : ℤ).natAbs) ≤ m := by simp
        simpa [signedIterate, signedNext] using hbox _ (m : ℤ) ih (by simp)
    have : (signedIterate (gain : ℤ) (m : ℤ) n).natAbs ≤ R := hstay n
    omega

/-- A list of trits sums to absolute value at most its length. -/
theorem sum_trits_bound (inputs : List ℤ)
    (h : ∀ a ∈ inputs, isTrit a) :
    inputs.sum.natAbs ≤ inputs.length := by
  induction inputs with
  | nil => simp
  | cons a rest ih =>
    have ha := h a (by simp)
    have hr : ∀ b ∈ rest, isTrit b := fun b hb =>
      h b (by simp [hb])
    have ih' := ih hr
    have habs : a.natAbs ≤ 1 := isTrit_natAbs ha
    have hadd : (a + rest.sum).natAbs ≤ a.natAbs + rest.sum.natAbs :=
      Int.natAbs_add_le a rest.sum
    simp [List.sum_cons]
    omega

/-- r-way trit addition is the ``λ=1`` family on ``U_r``. -/
theorem multi_trit_carry_bound {s : ℤ} {inputs : List ℤ}
    (hs : s.natAbs ≤ inputs.length / 2)
    (htrits : ∀ a ∈ inputs, isTrit a) :
    (DZ (s + inputs.sum)).natAbs ≤ inputs.length / 2 := by
  have hu := sum_trits_bound inputs htrits
  exact lambda1_reachable_box (m := inputs.length) hs hu

/-- The residual state count `2 * (r / 2) + 1` at `r = 1, 2, 3, 4` is `1, 3, 3, 5`. -/
theorem multi_trit_carry_minimal :
    2 * (1 / 2) + 1 = 1 ∧
      2 * (2 / 2) + 1 = 3 ∧
      2 * (3 / 2) + 1 = 3 ∧
      2 * (4 / 2) + 1 = 5 := by
  native_decide

end Problems.BalancedTernary
