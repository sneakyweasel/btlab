import Problems.Juggler.FateOneSidedCorollary

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# Theorem 9.1 with exceptional atoms (Section 10(d))

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Section 10(d), first paragraph: the
proof of Theorem 9.1 "also works if the odd-share bound fails only on bad atoms of total
probability `O((log y)^{-B})` at each depth, with `B > e_q(C)`". This file carries that out
on the exponential-moment proof of `FateOneSided`, and runs the weakened hypothesis to the
conjecture as `FateOneSidedCorollary` does for the original.

`OneSided.OneSidedShareExc` is the hypothesis: at each depth `1 ≤ t < d` there is a set `E`
of words, of total cylinder mass at most `exc`, such that every `L`-bad word outside `E`
obeys the share bound `#[wO] ≤ q #[w] + err`. An exceptional bad atom sends at most its
whole mass to its odd child, which costs `(x - a_q) #[w] x^{o(w)} = (x-1)(1-q) #[w] x^{o(w)}`
in the tilted mass, so the affine recursion of `OneSided.badMass_succ_le` gains one term:

`badMass (t+1) ≤ a_q · badMass t + (x - 1) (err (2x)^t + (1 - q) exc x^t)`

(`OneSided.badMass_succ_le_exc`), and everything downstream is the same bookkeeping with
`x^{d-1} exc` next to `(2x)^{d-1} err` (`OneSided.badMass_le_exc`, `OneSided.one_sided_bound_exc`,
`OneSided.one_sided_bound_kl_exc`). The absorption `OneSided.oddFailures_le_of_exc` needs
`B > C log₂ x + 1 + e` for the exceptional mass `y (log y)^{-B}`, against
`A > C (1 + log₂ x) + 1 + e` for the error `y (log y)^{-A}`: the exceptional atoms are not
doubled at each depth, so they cost `C` less. Both conditions are sufficient and not sharp,
for the reasons given in `FateOneSidedCorollary`; the paper's `B > e_q(C)` is the Markov
absorption of the martingale proof, not restated. `OneSided.exc_implies_conjecture` is the
weakest one-sided hypothesis the paper states, run to the conjecture with nothing else
assumed. Not a halt theorem: nothing here bounds a share.
-/

namespace OneSided

/-- The one-sided hypothesis with exceptional atoms: at each depth `1 ≤ t < d` there is a
set `E` of words of total cylinder mass at most `exc` such that every `L`-bad word outside
`E` sends at most the share `q` of its members, plus `err`, to an odd next letter. -/
def OneSidedShareExc (y : ℕ) (L q err exc : ℝ) (d : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t < d → ∃ E : Finset (List Branch),
    (∑ w ∈ (allWords t).filter (· ∈ E), ((cylinder y t w).card : ℝ)) ≤ exc ∧
    ∀ w ∈ allWords t, LBad L w → w ∉ E →
      ((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ) ≤ q * (cylinder y t w).card + err

/-- The original hypothesis is the case of no exceptional atoms. -/
theorem oneSidedShareExc_of_share {y : ℕ} {L q err exc : ℝ} {d : ℕ}
    (h : OneSidedShare y L q err d) (hexc : 0 ≤ exc) : OneSidedShareExc y L q err exc d := by
  intro t ht1 htd
  refine ⟨∅, ?_, fun w hw hbad _ => h t ht1 htd w hw hbad⟩
  simp [hexc]

/-- `H_q(C, A)` with exceptional atoms of mass `y (log y)^{-B}` at the scale `y`. -/
def OneSidedBoundExc (N₀ : ℕ) (C q A B : ℝ) (y : ℕ) : Prop :=
  OneSidedShareExc y (scaleL N₀ y) q (y / Real.log y ^ A) (y / Real.log y ^ B) (depth C N₀ y)

theorem oneSidedBoundExc_of_bound {N₀ : ℕ} {C q A : ℝ} {y : ℕ}
    (h : OneSidedBound N₀ C q A y) (B : ℝ) : OneSidedBoundExc N₀ C q A B y :=
  oneSidedShareExc_of_share h (by positivity)

/-! ### The recursion with the exceptional term -/

/-- **One depth, with exceptional atoms.** Under the hypothesis at depth `1 ≤ t < d`,
`badMass (t+1) ≤ a_q · badMass t + (x - 1) (err (2x)^t + (1 - q) exc x^t)`. -/
theorem badMass_succ_le_exc {y : ℕ} {L x q err exc : ℝ} {d t : ℕ} (hx : 1 ≤ x)
    (hq1 : q ≤ 1) (herr : 0 ≤ err) (hH : OneSidedShareExc y L q err exc d) (ht1 : 1 ≤ t)
    (htd : t < d) :
    badMass y L x (t + 1)
      ≤ (1 + (x - 1) * q) * badMass y L x t
        + (x - 1) * (err * (2 * x) ^ t + (1 - q) * exc * x ^ t) := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 0 ≤ x - 1 := by linarith
  have hq1' : 0 ≤ 1 - q := by linarith
  obtain ⟨E, hEmass, hshare⟩ := hH t ht1 htd
  unfold badMass
  rw [sum_allWords_succ, mul_sum]
  have hpt : ∀ w ∈ allWords t,
      badWeight y L (t + 1) (w ++ [Branch.even]) * x ^ oddCount (w ++ [Branch.even])
        + badWeight y L (t + 1) (w ++ [Branch.odd]) * x ^ oddCount (w ++ [Branch.odd])
      ≤ (1 + (x - 1) * q) * (badWeight y L t w * x ^ oddCount w)
        + (x - 1) * err * x ^ oddCount w
        + (x - 1) * (1 - q)
          * ((if w ∈ E then badWeight y L t w else 0) * x ^ oddCount w) := by
    intro w hw
    have hlen : w.length = t := mem_allWords.mp hw
    simp only [oddCount_append]
    have hpow : 0 ≤ x ^ oddCount w := pow_nonneg hx0 _
    have hEnn := badWeight_nonneg y L (t + 1) (w ++ [Branch.even])
    have hOnn := badWeight_nonneg y L (t + 1) (w ++ [Branch.odd])
    have hE : badWeight y L (t + 1) (w ++ [Branch.even])
        ≤ (cylinder y (t + 1) (w ++ [Branch.even])).card := badWeight_le_card _ _ _ _
    have hO : badWeight y L (t + 1) (w ++ [Branch.odd])
        ≤ (cylinder y (t + 1) (w ++ [Branch.odd])).card := badWeight_le_card _ _ _ _
    have hsplitR : ((cylinder y t w).card : ℝ)
        = (cylinder y (t + 1) (w ++ [Branch.even])).card
          + (cylinder y (t + 1) (w ++ [Branch.odd])).card := by
      exact_mod_cast cylinder_split y t w hlen
    have herrnn : 0 ≤ (x - 1) * err * x ^ oddCount w := mul_nonneg (mul_nonneg hx1 herr) hpow
    simp only [oddCount_even_cons, oddCount_odd_cons, oddCount_nil, add_zero, pow_succ]
    by_cases hbad : LBad L w
    · have hw' : badWeight y L t w = (cylinder y t w).card := by
        unfold badWeight; rw [if_pos hbad]
      rw [hw']
      by_cases hwE : w ∈ E
      · -- an exceptional bad atom: its odd child is at most the whole atom
        rw [if_pos hwE, hsplitR]
        have hEx : 0 ≤ (x - 1) * (cylinder y (t + 1) (w ++ [Branch.even])).card
            * x ^ oddCount w := mul_nonneg (mul_nonneg hx1 (Nat.cast_nonneg _)) hpow
        nlinarith [mul_le_mul_of_nonneg_right hE hpow,
          mul_le_mul_of_nonneg_right hO (mul_nonneg hpow hx0), hEx, herrnn]
      · -- a bad atom that obeys the share bound
        rw [if_neg hwE]
        have hshare' := hshare w hw hbad hwE
        nlinarith [mul_le_mul_of_nonneg_right hE hpow,
          mul_le_mul_of_nonneg_right hO (mul_nonneg hpow hx0),
          mul_le_mul_of_nonneg_right hshare' (mul_nonneg hx1 hpow), hpow, hsplitR]
    · -- a parent that is not bad has no bad child
      have hE0 : badWeight y L (t + 1) (w ++ [Branch.even]) = 0 := by
        unfold badWeight
        rw [if_neg (fun h => hbad (LBad_of_LBad_append h))]
      have hO0 : badWeight y L (t + 1) (w ++ [Branch.odd]) = 0 := by
        unfold badWeight
        rw [if_neg (fun h => hbad (LBad_of_LBad_append h))]
      have hw' : badWeight y L t w = 0 := by unfold badWeight; rw [if_neg hbad]
      rw [hE0, hO0, hw']
      simp only [zero_mul, add_zero, mul_zero, zero_add, ite_self]
      exact herrnn
  -- the exceptional mass at depth `t`, tilted, is at most `exc x^t`
  have hexcsum : ∑ w ∈ allWords t, (if w ∈ E then badWeight y L t w else 0) * x ^ oddCount w
      ≤ exc * x ^ t := by
    calc ∑ w ∈ allWords t, (if w ∈ E then badWeight y L t w else 0) * x ^ oddCount w
        ≤ ∑ w ∈ allWords t,
            (if w ∈ E then ((cylinder y t w).card : ℝ) else 0) * x ^ t := by
          apply sum_le_sum
          intro w hw
          have hlen : w.length = t := mem_allWords.mp hw
          have hxo : x ^ oddCount w ≤ x ^ t := by
            apply pow_le_pow_right₀ hx
            rw [← hlen]
            exact oddCount_le_length w
          split_ifs with hwE
          · exact mul_le_mul (badWeight_le_card _ _ _ _) hxo (pow_nonneg hx0 _)
              (Nat.cast_nonneg _)
          · simp
      _ = (∑ w ∈ (allWords t).filter (· ∈ E), ((cylinder y t w).card : ℝ)) * x ^ t := by
          rw [sum_filter, sum_mul]
      _ ≤ exc * x ^ t := mul_le_mul_of_nonneg_right hEmass (pow_nonneg hx0 _)
  calc ∑ w ∈ allWords t,
        (badWeight y L (t + 1) (w ++ [Branch.even]) * x ^ oddCount (w ++ [Branch.even])
          + badWeight y L (t + 1) (w ++ [Branch.odd]) * x ^ oddCount (w ++ [Branch.odd]))
      ≤ ∑ w ∈ allWords t, ((1 + (x - 1) * q) * (badWeight y L t w * x ^ oddCount w)
          + (x - 1) * err * x ^ oddCount w
          + (x - 1) * (1 - q)
            * ((if w ∈ E then badWeight y L t w else 0) * x ^ oddCount w)) := sum_le_sum hpt
    _ = ∑ w ∈ allWords t, (1 + (x - 1) * q) * (badWeight y L t w * x ^ oddCount w)
          + (x - 1) * err * ∑ w ∈ allWords t, x ^ oddCount w
          + (x - 1) * (1 - q)
            * ∑ w ∈ allWords t,
                (if w ∈ E then badWeight y L t w else 0) * x ^ oddCount w := by
        rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum]
    _ ≤ ∑ w ∈ allWords t, (1 + (x - 1) * q) * (badWeight y L t w * x ^ oddCount w)
          + (x - 1) * err * (2 * x) ^ t + (x - 1) * (1 - q) * (exc * x ^ t) := by
        have h1 := sum_pow_oddCount_le hx t
        have hc1 : 0 ≤ (x - 1) * err := mul_nonneg hx1 herr
        have hc2 : 0 ≤ (x - 1) * (1 - q) := mul_nonneg hx1 hq1'
        nlinarith [mul_le_mul_of_nonneg_left h1 hc1, mul_le_mul_of_nonneg_left hexcsum hc2]
    _ = ∑ w ∈ allWords t, (1 + (x - 1) * q) * (badWeight y L t w * x ^ oddCount w)
          + (x - 1) * (err * (2 * x) ^ t + (1 - q) * exc * x ^ t) := by ring

/-- **Unrolled.** For `t + 1 ≤ d`,
`badMass (t+1) ≤ x a_q^t N + (x-1) t (err (2x)^t + (1-q) exc x^t)`, using `a_q ≤ 2x` and
`a_q ≤ x`. -/
theorem badMass_le_exc {y : ℕ} {L x q err exc : ℝ} {d : ℕ} (hx : 1 ≤ x) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (herr : 0 ≤ err) (hexc : 0 ≤ exc) (hH : OneSidedShareExc y L q err exc d) :
    ∀ t, t + 1 ≤ d → badMass y L x (t + 1)
      ≤ x * (1 + (x - 1) * q) ^ t * (cylinder y 0 []).card
        + (x - 1) * t * (err * (2 * x) ^ t + (1 - q) * exc * x ^ t) := by
  intro t
  induction t with
  | zero =>
      intro _
      have := badMass_one_le (y := y) (L := L) hx
      simpa using this
  | succ t ih =>
      intro htd
      have hstep := badMass_succ_le_exc hx hq1 herr hH (t := t + 1) (by omega) (by omega)
      have hprev := ih (by omega)
      have hx0 : 0 ≤ x := by linarith
      have hx1 : 0 ≤ x - 1 := by linarith
      have hq1' : 0 ≤ 1 - q := by linarith
      have ha0 : 0 ≤ 1 + (x - 1) * q := by nlinarith
      have ha2x : 1 + (x - 1) * q ≤ 2 * x := by nlinarith
      have hax : 1 + (x - 1) * q ≤ x := by nlinarith
      have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
      set a := 1 + (x - 1) * q with ha
      set N := ((cylinder y 0 []).card : ℝ) with hNdef
      set T := err * (2 * x) ^ t + (1 - q) * exc * x ^ t with hT
      set T' := err * (2 * x) ^ (t + 1) + (1 - q) * exc * x ^ (t + 1) with hT'
      have h1nn : 0 ≤ err * (2 * x) ^ t := mul_nonneg herr (pow_nonneg (by linarith) _)
      have h2nn : 0 ≤ (1 - q) * exc * x ^ t :=
        mul_nonneg (mul_nonneg hq1' hexc) (pow_nonneg hx0 _)
      have haT : a * T ≤ T' := by
        rw [hT, hT', pow_succ, pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right ha2x h1nn, mul_le_mul_of_nonneg_right hax h2nn]
      have h1 : a * badMass y L x (t + 1) ≤ a * (x * a ^ t * N + (x - 1) * t * T) :=
        mul_le_mul_of_nonneg_left hprev ha0
      have h2 : (x - 1) * (t * (a * T)) ≤ (x - 1) * (t * T') :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left haT ht0) hx1
      push_cast
      calc badMass y L x (t + 1 + 1) ≤ a * badMass y L x (t + 1) + (x - 1) * T' := hstep
        _ ≤ a * (x * a ^ t * N + (x - 1) * t * T) + (x - 1) * T' := by linarith
        _ = x * a ^ (t + 1) * N + ((x - 1) * (t * (a * T)) + (x - 1) * T') := by ring
        _ ≤ x * a ^ (t + 1) * N + ((x - 1) * (t * T') + (x - 1) * T') := by linarith
        _ = x * a ^ (t + 1) * N + (x - 1) * (t + 1) * T' := by ring

/-- **Theorem 9.1 with exceptional atoms, exact.** -/
theorem one_sided_bound_exc {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y)
    {C x q err exc : ℝ} (hC : 0 < C) (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (herr : 0 ≤ err) (hexc : 0 ≤ exc) {d : ℕ} (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d)
    (hH : OneSidedShareExc y (scaleL N₀ y) q err exc d) :
    ((oddFailures y).card : ℝ) ≤
      (x * (1 + (x - 1) * q) ^ (d - 1) * (cylinder y 0 []).card
        + (x - 1) * ((d : ℝ) - 1) * (err * (2 * x) ^ (d - 1) + (1 - q) * exc * x ^ (d - 1)))
        / x ^ (pC C * d) := by
  have h1 := oddFailures_card_le_badMass hN hfloor hy hC hx hd1 hd
  have h2 := badMass_le_exc hx hq0 hq1 herr hexc hH (d - 1) (by omega)
  rw [Nat.sub_add_cancel hd1] at h2
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd1]; simp
  rw [hcast] at h2
  have hxp : 0 < x ^ (pC C * d) := Real.rpow_pos_of_pos (by linarith) _
  exact le_trans h1 (div_le_div_of_nonneg_right h2 hxp.le)

/-- The main term at the re-centring tilt, split off: `(x a^{d-1} N + R) / x^{p d}
= (x/a) N e^{-d D(p ‖ q)} + R / x^{p d}`. -/
theorem main_term_eq {p q : ℝ} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) {d : ℕ}
    (hd1 : 1 ≤ d) (N R : ℝ) :
    (tilt p q * (1 + (tilt p q - 1) * q) ^ (d - 1) * N + R) / tilt p q ^ (p * d)
      = tilt p q / (1 + (tilt p q - 1) * q) * N * Real.exp (-(d * klDiv p q))
        + R / tilt p q ^ (p * d) := by
  have hx1 := tilt_ge_one hq0 hqp hp1
  have hx : 0 < tilt p q := by linarith
  have ha : 0 < 1 + (tilt p q - 1) * q := by nlinarith
  have hxp : 0 < tilt p q ^ (p * d) := Real.rpow_pos_of_pos hx _
  rw [add_div, ← tilt_pow_ratio hq0 hqp hp1 d]
  congr 1
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [pow_succ]
  have hxpne := hxp.ne'
  field_simp

/-- **Theorem 9.1 with exceptional atoms at the re-centring tilt.** -/
theorem one_sided_bound_kl_exc {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y)
    {C q err exc : ℝ} (hC : 0 < C) (hq0 : 0 < q) (hqp : q < pC C) (hp1 : pC C < 1)
    (herr : 0 ≤ err) (hexc : 0 ≤ exc) {d : ℕ} (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d)
    (hH : OneSidedShareExc y (scaleL N₀ y) q err exc d) :
    ((oddFailures y).card : ℝ) ≤
      tilt (pC C) q / (1 + (tilt (pC C) q - 1) * q) * (cylinder y 0 []).card
          * Real.exp (-(d * klDiv (pC C) q))
        + (tilt (pC C) q - 1) * ((d : ℝ) - 1)
          * (err * (2 * tilt (pC C) q) ^ (d - 1) + (1 - q) * exc * tilt (pC C) q ^ (d - 1))
          / tilt (pC C) q ^ (pC C * d) := by
  rw [← main_term_eq hq0 hqp hp1 hd1]
  exact one_sided_bound_exc hN hfloor hy hC (tilt_ge_one hq0 hqp hp1) hq0.le (by linarith)
    herr hexc hd1 hd hH

/-! ### The absorption -/

/-- `z^{d-1} ≤ Λ^{C log₂ z}` once `d - 1 ≤ C log₂ Λ`, for `z ≥ 1` and `Λ ≥ 1`. -/
theorem pow_le_rpow_scale_gen {Λ C z : ℝ} (hΛ : 1 ≤ Λ) (hz : 1 ≤ z) (hC : 0 ≤ C)
    {d : ℕ} (hd : (d : ℝ) - 1 ≤ C * Real.logb 2 Λ) :
    z ^ (d - 1) ≤ Λ ^ (C * Real.logb 2 z) := by
  have hΛ0 : 0 < Λ := by linarith
  have hcast : ((d - 1 : ℕ) : ℝ) ≤ C * Real.logb 2 Λ := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      simp only [Nat.zero_sub, Nat.cast_zero]
      exact mul_nonneg hC (Real.logb_nonneg (by norm_num) hΛ)
    · rw [Nat.cast_sub h]
      simpa using hd
  calc z ^ (d - 1) = z ^ ((d - 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ z ^ (C * Real.logb 2 Λ) := Real.rpow_le_rpow_of_exponent_le hz hcast
    _ = Λ ^ (C * Real.logb 2 z) := by
        rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hΛ0]
        congr 1
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        unfold Real.logb
        field_simp

/-- **One tail term.** At a scale `y ≥ max(N₀, 2)`, with `d = ⌈C L(y)⌉` and `z ≥ 1`,
`(d-1) z^{d-1} · y (log y)^{-A} ≤ K_d M_z · y (log y)^{C log₂ z + 1 - A}`. -/
theorem tail_le {N₀ y : ℕ} (hN : 2 ≤ N₀) (hyN : N₀ ≤ y) (hy2 : 2 ≤ y) {C z A : ℝ}
    (hC : 0 < C) (hz : 1 ≤ z) :
    ((depth C N₀ y : ℝ) - 1) * z ^ (depth C N₀ y - 1) * ((y : ℝ) / Real.log y ^ A)
      ≤ 2 * C / (Real.log 2 * Real.log N₀) * (2 / Real.log N₀) ^ (C * Real.logb 2 z)
        * y * Real.log y ^ (C * Real.logb 2 z + 1 - A) := by
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N₀))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hd1 : 1 ≤ depth C N₀ y := one_le_depth hN (by omega) hC
  set d := depth C N₀ y with hddef
  set Λ := scaleRatio N₀ y with hΛ
  have hΛdef : Λ = Real.log (2 * y) / Real.log N₀ := rfl
  have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
    Real.log_mul (by norm_num) hy0.ne'
  have hlog2le : Real.log 2 ≤ Real.log y :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hy2)
  have hΛhi : Λ ≤ 2 * Real.log y / Real.log N₀ := by
    rw [hΛdef, hlog2y]
    apply div_le_div_of_nonneg_right _ hlogN.le
    linarith
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛdef, le_div_iff₀ hlogN, one_mul]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (by omega : N₀ ≤ 2 * y)
  have hΛpos : 0 < Λ := by linarith
  have hL0 : 0 ≤ scaleL N₀ y := Real.logb_nonneg (by norm_num) hΛ1
  have hdlt : (d : ℝ) - 1 < C * scaleL N₀ y := by
    have := Nat.ceil_lt_add_one (mul_nonneg hC.le hL0)
    rw [hddef]
    unfold depth
    linarith
  set κ := C * Real.logb 2 z with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg hC.le (Real.logb_nonneg (by norm_num) hz)
  have hd_le : (d : ℝ) - 1 ≤ 2 * C / (Real.log 2 * Real.log N₀) * Real.log y := by
    have hlogΛ : Real.log Λ ≤ Λ - 1 := Real.log_le_sub_one_of_pos hΛpos
    have hL : scaleL N₀ y = Real.log Λ / Real.log 2 := rfl
    have h1 : C * scaleL N₀ y ≤ C * (Λ / Real.log 2) := by
      rw [hL]
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply div_le_div_of_nonneg_right _ hlog2.le
      linarith
    have h2 : C * (Λ / Real.log 2) ≤ C * ((2 * Real.log y / Real.log N₀) / Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact div_le_div_of_nonneg_right hΛhi hlog2.le
    have h3 : C * ((2 * Real.log y / Real.log N₀) / Real.log 2)
        = 2 * C / (Real.log 2 * Real.log N₀) * Real.log y := by
      field_simp
    linarith
  have hpow : z ^ (d - 1) ≤ Λ ^ κ := pow_le_rpow_scale_gen hΛ1 hz hC.le hdlt.le
  have hΛκ : Λ ^ κ ≤ (2 / Real.log N₀) ^ κ * Real.log y ^ κ := by
    calc Λ ^ κ ≤ (2 * Real.log y / Real.log N₀) ^ κ := Real.rpow_le_rpow hΛpos.le hΛhi hκ0
      _ = (2 / Real.log N₀) ^ κ * Real.log y ^ κ := by
          rw [show 2 * Real.log y / Real.log N₀ = (2 / Real.log N₀) * Real.log y by ring,
            Real.mul_rpow (by positivity) hlogy.le]
  have hdm : 0 ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    linarith
  have hpow0 : 0 ≤ z ^ (d - 1) := pow_nonneg (by linarith) _
  have hA0 : 0 < Real.log y ^ A := Real.rpow_pos_of_pos hlogy _
  set Kd := 2 * C / (Real.log 2 * Real.log N₀) with hKd
  set M := (2 / Real.log N₀) ^ κ with hM
  have hM0 : 0 ≤ M := Real.rpow_nonneg (by positivity) _
  have hKd0 : 0 ≤ Kd := by positivity
  have hyA : 0 ≤ (y : ℝ) / Real.log y ^ A := by positivity
  have hT : Real.log y ^ (-A) * Real.log y * Real.log y ^ κ = Real.log y ^ (κ + 1 - A) := by
    rw [← Real.rpow_add_one hlogy.ne', ← Real.rpow_add hlogy]
    congr 1
    ring
  calc ((d : ℝ) - 1) * z ^ (d - 1) * ((y : ℝ) / Real.log y ^ A)
      ≤ (Kd * Real.log y) * (M * Real.log y ^ κ) * ((y : ℝ) / Real.log y ^ A) := by
        apply mul_le_mul_of_nonneg_right _ hyA
        exact mul_le_mul hd_le (le_trans hpow hΛκ) hpow0 (by positivity)
    _ = Kd * M * y * (Real.log y ^ (-A) * Real.log y * Real.log y ^ κ) := by
        rw [Real.rpow_neg hlogy.le]
        field_simp
    _ = Kd * M * y * Real.log y ^ (κ + 1 - A) := by rw [hT]

/-- **The absorption with exceptional atoms.** Under `H_q(C, A)` with exceptional atoms of
mass `y (log y)^{-B}` at all large scales, with `q < p_C`, `A > C(1 + log₂ x) + 1 + e`,
`B > C log₂ x + 1 + e` and `e < e_{C,q}`, the odd failures in `(y, 2y]` number at most
`y (log y)^{-e}` for all large `y`. -/
theorem oddFailures_le_of_exc {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A B e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A)
    (hB : C * Real.logb 2 (tilt (pC C) q) + 1 + e < B) (he : e < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBoundExc N₀ C q A B y) :
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
  have hlogbx : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  set κ₂ := C * Real.logb 2 (2 * x) with hκ₂
  set κ₃ := C * Real.logb 2 x with hκ₃
  have hκ₂eq : κ₂ = C * (1 + Real.logb 2 x) := by
    rw [hκ₂, Real.logb_mul (by norm_num) hx0.ne', Real.logb_self_eq_one (by norm_num)]
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N₀))
  have hδ₁ : 0 < eOS - e := by linarith
  have hδ₂ : 0 < A - κ₂ - 1 - e := by rw [hκ₂eq]; linarith
  have hδ₃ : 0 < B - κ₃ - 1 - e := by rw [hκ₃]; linarith
  -- the constants
  set Kd := 2 * C / (Real.log 2 * Real.log N₀) with hKd
  set K₁ := x / a * Real.log N₀ ^ eOS with hK₁
  set K₂ := (x - 1) * Kd * (2 / Real.log N₀) ^ κ₂ + 1 with hK₂
  set K₃ := (x - 1) * Kd * (2 / Real.log N₀) ^ κ₃ + 1 with hK₃
  have hKd0 : 0 ≤ Kd := by positivity
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  have hK₂0 : 0 < K₂ := by
    rw [hK₂]
    have : 0 ≤ (x - 1) * Kd * (2 / Real.log N₀) ^ κ₂ :=
      mul_nonneg (mul_nonneg (by linarith) hKd0) (Real.rpow_nonneg (by positivity) _)
    linarith
  have hK₃0 : 0 < K₃ := by
    rw [hK₃]
    have : 0 ≤ (x - 1) * Kd * (2 / Real.log N₀) ^ κ₃ :=
      mul_nonneg (mul_nonneg (by linarith) hKd0) (Real.rpow_nonneg (by positivity) _)
    linarith
  obtain ⟨u₁, -, hu₁⟩ := exists_rpow_gt hδ₁ (3 * K₁)
  obtain ⟨u₂, -, hu₂⟩ := exists_rpow_gt hδ₂ (3 * K₂)
  obtain ⟨u₃, -, hu₃⟩ := exists_rpow_gt hδ₃ (3 * K₃)
  refine ⟨max (max y₁ N₀) (max 2 ⌈Real.exp (max u₁ (max u₂ u₃))⌉₊), ?_⟩
  intro y hy
  have hyy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyN : N₀ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy2 : 2 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hyexp : Real.exp (max u₁ (max u₂ u₃)) ≤ y := by
    have h1 : ⌈Real.exp (max u₁ (max u₂ u₃))⌉₊ ≤ y :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlogy_ge : max u₁ (max u₂ u₃) ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]; exact hyexp
  have hK₁' : 3 * K₁ < Real.log y ^ (eOS - e) :=
    hu₁ _ (le_trans (le_max_left _ _) hlogy_ge)
  have hK₂' : 3 * K₂ < Real.log y ^ (A - κ₂ - 1 - e) :=
    hu₂ _ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlogy_ge)
  have hK₃' : 3 * K₃ < Real.log y ^ (B - κ₃ - 1 - e) :=
    hu₃ _ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlogy_ge)
  -- the scale and the depth
  have hd1 : 1 ≤ depth C N₀ y := one_le_depth hN (by omega) hC0
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
  -- Theorem 9.1 with exceptional atoms at this scale
  have hH : OneSidedShareExc y (scaleL N₀ y) q ((y : ℝ) / Real.log y ^ A)
      ((y : ℝ) / Real.log y ^ B) d := hy₁ y hyy₁
  have herr : 0 ≤ (y : ℝ) / Real.log y ^ A := by positivity
  have hexc : 0 ≤ (y : ℝ) / Real.log y ^ B := by positivity
  have hmain := one_sided_bound_kl_exc hN hfloor (by omega : 1 ≤ y) hC0 hq0 hqp hp1 herr hexc
    hd1 hdge hH
  rw [← hxdef, ← hadef, ← hDdef] at hmain
  -- the atoms
  set P := Real.log y ^ (-e) with hP
  set Q₁ := Real.log y ^ (-(eOS - e)) with hQ₁
  set Q₂ := Real.log y ^ (-(A - κ₂ - 1 - e)) with hQ₂
  set Q₃ := Real.log y ^ (-(B - κ₃ - 1 - e)) with hQ₃
  have hP0 : 0 ≤ P := Real.rpow_nonneg hlogy.le _
  have hQ₁0 : 0 ≤ Q₁ := Real.rpow_nonneg hlogy.le _
  have hQ₂0 : 0 ≤ Q₂ := Real.rpow_nonneg hlogy.le _
  have hQ₃0 : 0 ≤ Q₃ := Real.rpow_nonneg hlogy.le _
  have hQ₁le : Q₁ ≤ 1 / (3 * K₁) := by
    rw [hQ₁, Real.rpow_neg hlogy.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hK₁'.le
  have hQ₂le : Q₂ ≤ 1 / (3 * K₂) := by
    rw [hQ₂, Real.rpow_neg hlogy.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hK₂'.le
  have hQ₃le : Q₃ ≤ 1 / (3 * K₃) := by
    rw [hQ₃, Real.rpow_neg hlogy.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hK₃'.le
  -- term 1: the main term
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
  have hterm1 : x / a * (cylinder y 0 []).card * Real.exp (-(d * D)) ≤ y * P / 3 := by
    calc x / a * (cylinder y 0 []).card * Real.exp (-(d * D))
        ≤ x / a * y * Λ ^ (-eOS) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hN_le (by positivity)) hexp
            (Real.exp_pos _).le (by positivity)
      _ ≤ x / a * y * (Real.log N₀ ^ eOS * (P * Q₁)) :=
          mul_le_mul_of_nonneg_left hT1 (by positivity)
      _ = K₁ * y * (P * Q₁) := by rw [hK₁]; ring
      _ ≤ K₁ * y * (P * (1 / (3 * K₁))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hQ₁le hP0
      _ = y * P / 3 := by field_simp
  -- terms 2 and 3: the error and the exceptional mass, through `tail_le`
  have htail2 := tail_le hN hyN hy2 hC0 (z := 2 * x) (A := A) (by linarith)
  have htail3 := tail_le hN hyN hy2 hC0 (z := x) (A := B) hx1
  rw [← hκ₂, ← hKd] at htail2
  rw [← hκ₃, ← hKd] at htail3
  have hQ₂eq : Real.log y ^ (κ₂ + 1 - A) = P * Q₂ := by
    rw [hP, hQ₂, ← Real.rpow_add hlogy]
    congr 1
    ring
  have hQ₃eq : Real.log y ^ (κ₃ + 1 - B) = P * Q₃ := by
    rw [hP, hQ₃, ← Real.rpow_add hlogy]
    congr 1
    ring
  have hxp1 : 1 ≤ x ^ (pC C * d) := Real.one_le_rpow hx1 (by positivity)
  have hterm23 : (x - 1) * ((d : ℝ) - 1)
      * (((y : ℝ) / Real.log y ^ A) * (2 * x) ^ (d - 1)
        + (1 - q) * ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1)) / x ^ (pC C * d)
      ≤ y * P / 3 + y * P / 3 := by
    have hx1' : 0 ≤ x - 1 := by linarith
    have hdm : 0 ≤ (d : ℝ) - 1 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      linarith
    have hq1' : 0 ≤ 1 - q := by linarith
    have hpow2 : 0 ≤ (2 * x) ^ (d - 1) := by positivity
    have hpow3 : 0 ≤ x ^ (d - 1) := by positivity
    have hinner : 0 ≤ ((y : ℝ) / Real.log y ^ A) * (2 * x) ^ (d - 1)
        + (1 - q) * ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1) :=
      add_nonneg (mul_nonneg herr hpow2) (mul_nonneg (mul_nonneg hq1' hexc) hpow3)
    have hdrop : (1 - q) * ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1)
        ≤ ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1) := by
      have hEX : 0 ≤ ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1) := mul_nonneg hexc hpow3
      calc (1 - q) * ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1)
          = (1 - q) * (((y : ℝ) / Real.log y ^ B) * x ^ (d - 1)) := by ring
        _ ≤ 1 * (((y : ℝ) / Real.log y ^ B) * x ^ (d - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hEX
        _ = ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1) := one_mul _
    calc (x - 1) * ((d : ℝ) - 1)
          * (((y : ℝ) / Real.log y ^ A) * (2 * x) ^ (d - 1)
            + (1 - q) * ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1)) / x ^ (pC C * d)
        ≤ (x - 1) * ((d : ℝ) - 1)
          * (((y : ℝ) / Real.log y ^ A) * (2 * x) ^ (d - 1)
            + (1 - q) * ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1)) :=
          div_le_self (mul_nonneg (mul_nonneg hx1' hdm) hinner) hxp1
      _ ≤ (x - 1) * ((d : ℝ) - 1)
          * (((y : ℝ) / Real.log y ^ A) * (2 * x) ^ (d - 1)
            + ((y : ℝ) / Real.log y ^ B) * x ^ (d - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hx1' hdm)
          linarith
      _ = (x - 1) * (((d : ℝ) - 1) * (2 * x) ^ (d - 1) * ((y : ℝ) / Real.log y ^ A)
            + ((d : ℝ) - 1) * x ^ (d - 1) * ((y : ℝ) / Real.log y ^ B)) := by ring
      _ ≤ (x - 1) * (Kd * (2 / Real.log N₀) ^ κ₂ * y * Real.log y ^ (κ₂ + 1 - A)
            + Kd * (2 / Real.log N₀) ^ κ₃ * y * Real.log y ^ (κ₃ + 1 - B)) := by
          apply mul_le_mul_of_nonneg_left _ hx1'
          exact add_le_add htail2 htail3
      _ = ((x - 1) * Kd * (2 / Real.log N₀) ^ κ₂) * y * (P * Q₂)
            + ((x - 1) * Kd * (2 / Real.log N₀) ^ κ₃) * y * (P * Q₃) := by
          rw [hQ₂eq, hQ₃eq]
          ring
      _ ≤ K₂ * y * (P * Q₂) + K₃ * y * (P * Q₃) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hP0 hQ₂0)
            apply mul_le_mul_of_nonneg_right _ hy0.le
            rw [hK₂]
            linarith
          · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hP0 hQ₃0)
            apply mul_le_mul_of_nonneg_right _ hy0.le
            rw [hK₃]
            linarith
      _ ≤ K₂ * y * (P * (1 / (3 * K₂))) + K₃ * y * (P * (1 / (3 * K₃))) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hQ₂le hP0
          · apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hQ₃le hP0
      _ = y * P / 3 + y * P / 3 := by field_simp
  calc ((oddFailures y).card : ℝ) ≤ _ := hmain
    _ ≤ y * P / 3 + (y * P / 3 + y * P / 3) := add_le_add hterm1 hterm23
    _ = y * Real.log y ^ (-e) := by rw [hP]; ring

/-- **Section 10(d)'s corollary, with the contagion bound as a hypothesis.** -/
theorem exc_conj_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A B e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A)
    (hB : C * Real.logb 2 (tilt (pC C) q) + 1 + e < B) (he : e < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBoundExc N₀ C q A B y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  tao_rate_implies_conjecture hlam0 hlam1 hlam hlow
    (oddFailures_le_of_exc hN hfloor C q A B e hC hq0 hqp hA hB he hH)

/-- **Section 10(d)'s corollary with nothing else assumed.** The one-sided hypothesis with
exceptional atoms of mass `y (log y)^{-B}` at all large scales above a certified floor, with
`C ≥ 5`, `0 < q < p_C`, `A > C(1 + log₂ x) + 1 + e`, `B > C log₂ x + 1 + e` and
`27/40 < e < e_{C,q}`, gives that every positive integer reaches `1`. -/
theorem exc_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A B e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A)
    (hB : C * Real.logb 2 (tilt (pC C) q) + 1 + e < B) (he : e < oneSidedExponent C q)
    (he7 : 27 / 40 < e)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBoundExc N₀ C q A B y) :
    ∀ n, 1 ≤ n → ReachesOne n :=
  Production.conjecture_of_tao_rate he7
    (oddFailures_le_of_exc hN hfloor C q A B e hC hq0 hqp hA hB he hH)

end OneSided

end Problems.Juggler
