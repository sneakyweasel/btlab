import Problems.Juggler.FateChernoff
import Problems.Juggler.FateCylinderEnergy
import Problems.Juggler.TiltedShare

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The one-sided form without the martingale (Theorem 9.1 by exponential moments)

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Theorem 9.1: under the one-sided
hypothesis `H_q(C, A)` — every `L(y)`-bad cylinder of depth `1 ≤ t < d(y)` sends at most the
share `q` of its members, plus `y (log y)^{-A}`, to an odd next letter — the odd failures in
`(y, 2y]` are rare. The paper proves it with the Azuma--Hoeffding inequality on a stopped
martingale, and remarks (after Proposition 9.3) that the exponential-moment method gives an
exponent at least as good. This file carries out that remark exactly, and no martingale
appears.

The device is to *kill* the words that are not bad: `badWeight` is the cylinder count on
`L`-bad words and `0` elsewhere, and `badMass y L x t = Σ_{|w|=t} badWeight(w) x^{o(w)}` is
its tilted mass. Bad words are prefix-closed, a cylinder splits into its two children, and the
hypothesis bounds the odd child of every bad parent, so for `1 ≤ t < d`

`badMass (t+1) ≤ (1 + (x-1) q) · badMass t + (x - 1) · err · (2x)^t`

(`badMass_succ_le`): the fair factor `a_q` of Proposition 9.3, plus an additive error that no
longer needs a lower bound on the live mass. Unrolling from `badMass 1 ≤ x N` gives
`badMass_le`, and Lemma 8.1 with the Markov tilt puts every odd failure in a bad cylinder of
depth `d` with at least `p_C d` odd letters (`oddFailures_card_le_badMass`), so

`#{odd failures in (y, 2y]} ≤ (x a_q^{d-1} N + (x-1) err (d-1) (2x)^{d-1}) / x^{p_C d}`

(`one_sided_bound`), exactly, at every scale, with no `ε`. At the re-centring tilt
`x = p_C(1-q)/(q(1-p_C))` the main term is `(x/a_q) N e^{-d D(p_C ‖ q)}`
(`one_sided_bound_kl`, on `tilt_exponent_eq_kl`): the exponent `C D(p_C ‖ q)/log 2` of
Proposition 9.3, which the paper records is at least the Azuma exponent `e_q(C)`.

What is different from the paper, and what is not here. The error term here carries
`(2x)^{d-1} / x^{p_C d}` where the paper's Markov step carries `2^d`: the tilt is paid on the
error too, so absorbing it into `y (log y)^{-r}` needs `A > C(1 + (1 - p_C) log₂ x) + r`
rather than the paper's `A > C + r`, a stronger hypothesis for a stronger exponent. That
absorption, the substitution `d = ⌈C L(y)⌉`, and the paper's displayed
`(log 2y/log N₀)^{-(e_q(C)-ε)}` are not formalized. Nothing here bounds a cylinder, and
nothing here is a halt theorem.
-/

namespace OneSided

/-! ### Cylinders split, and bad words are prefix-closed -/

/-- A cylinder of depth `t` splits into its two children at depth `t + 1`. -/
theorem cylinder_split (y t : ℕ) (w : List Branch) (hw : w.length = t) :
    (cylinder y t w).card
      = (cylinder y (t + 1) (w ++ [Branch.even])).card
        + (cylinder y (t + 1) (w ++ [Branch.odd])).card := by
  have key : ∀ b : Branch, cylinder y (t + 1) (w ++ [b])
      = {n ∈ cylinder y t w | bit (floorPower^[t] n) = b} := by
    intro b
    ext n
    simp only [cylinder, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hn, hodd, hit⟩
      rw [CylinderEnergy.itinerary_succ_append] at hit
      have hlen : (itinerary n t).length = w.length := by rw [itinerary_length, hw]
      obtain ⟨h1, h2⟩ := List.append_inj hit hlen
      exact ⟨⟨hn, hodd, h1⟩, by simpa using h2⟩
    · rintro ⟨⟨hn, hodd, hit⟩, hb⟩
      refine ⟨hn, hodd, ?_⟩
      rw [CylinderEnergy.itinerary_succ_append, hit, hb]
  rw [key, key, ← card_filter_add_card_filter_not (s := cylinder y t w)
    (fun n => bit (floorPower^[t] n) = Branch.even)]
  congr 1
  apply card_bij (fun n _ => n)
  · intro n hn
    rw [mem_filter] at hn ⊢
    refine ⟨hn.1, ?_⟩
    cases h : bit (floorPower^[t] n) <;> simp_all
  · intro a _ b _ h; exact h
  · intro n hn
    refine ⟨n, ?_, rfl⟩
    rw [mem_filter] at hn ⊢
    exact ⟨hn.1, by rw [hn.2]; simp⟩

/-- Badness is inherited by prefixes: a bad child has a bad parent. -/
theorem LBad_of_LBad_append {L : ℝ} {w : List Branch} {b : Branch}
    (h : LBad L (w ++ [b])) : LBad L w := by
  intro t ht htw
  have := h t ht (by simp; omega)
  rwa [List.take_append_of_le_length htw] at this

/-- A sum over the words of depth `t + 1` is a sum over the two children of each word of
depth `t`. -/
theorem sum_allWords_succ (f : List Branch → ℝ) (t : ℕ) :
    ∑ w ∈ allWords (t + 1), f w
      = ∑ w ∈ allWords t, (f (w ++ [Branch.even]) + f (w ++ [Branch.odd])) := by
  have hdisj : ∀ x ∈ allWords t, ∀ y ∈ allWords t, x ≠ y →
      Disjoint ({x ++ [Branch.even], x ++ [Branch.odd]} : Finset (List Branch))
        {y ++ [Branch.even], y ++ [Branch.odd]} := by
    intro x hx y hy hne
    have hlen : x.length = y.length := by
      rw [mem_allWords.mp hx, mem_allWords.mp hy]
    simp only [Finset.disjoint_insert_left, Finset.mem_insert, Finset.mem_singleton,
      Finset.disjoint_singleton_left]
    constructor
    · rintro (h | h)
      · exact hne (List.append_inj h hlen).1
      · exact absurd (List.append_inj h hlen).2 (by simp)
    · rintro (h | h)
      · exact absurd (List.append_inj h hlen).2 (by simp)
      · exact hne (List.append_inj h hlen).1
  rw [allWords_succ, sum_biUnion hdisj]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_pair (by simp)]

/-- The tilted count of all words: `Σ_{|w|=t} x^{o(w)} = (1 + x)^t ≤ (2x)^t` for `x ≥ 1`. -/
theorem sum_pow_oddCount_le {x : ℝ} (hx : 1 ≤ x) :
    ∀ t : ℕ, ∑ w ∈ allWords t, x ^ oddCount w ≤ (2 * x) ^ t := by
  intro t
  induction t with
  | zero => simp [allWords]
  | succ t ih =>
      rw [sum_allWords_succ]
      have : ∀ w ∈ allWords t,
          x ^ oddCount (w ++ [Branch.even]) + x ^ oddCount (w ++ [Branch.odd])
            = (1 + x) * x ^ oddCount w := by
        intro w _
        simp only [oddCount_append]
        simp
        ring
      rw [sum_congr rfl this, ← mul_sum, pow_succ]
      have h2 : 1 + x ≤ 2 * x := by linarith
      have h0 : 0 ≤ ∑ w ∈ allWords t, x ^ oddCount w :=
        sum_nonneg (fun _ _ => pow_nonneg (by linarith) _)
      calc (1 + x) * ∑ w ∈ allWords t, x ^ oddCount w
          ≤ (2 * x) * (2 * x) ^ t := mul_le_mul h2 ih h0 (by linarith)
        _ = (2 * x) ^ t * (2 * x) := by ring

/-! ### The tilted mass of the bad cylinders -/

/-- The bad weight at scale `y`: the cylinder count on `L`-bad words, `0` elsewhere. -/
noncomputable def badWeight (y : ℕ) (L : ℝ) (t : ℕ) (w : List Branch) : ℝ :=
  if LBad L w then ((cylinder y t w).card : ℝ) else 0

theorem badWeight_nonneg (y : ℕ) (L : ℝ) (t : ℕ) (w : List Branch) :
    0 ≤ badWeight y L t w := by
  unfold badWeight; split_ifs <;> positivity

theorem badWeight_le_card (y : ℕ) (L : ℝ) (t : ℕ) (w : List Branch) :
    badWeight y L t w ≤ (cylinder y t w).card := by
  unfold badWeight; split_ifs <;> simp

/-- The tilted bad mass at depth `t`: `Σ_{|w|=t, w bad} #[w]_y x^{o(w)}`. -/
noncomputable def badMass (y : ℕ) (L x : ℝ) (t : ℕ) : ℝ :=
  ∑ w ∈ allWords t, badWeight y L t w * x ^ oddCount w

/-- The paper's one-sided hypothesis `H_q(C, A)` at scale `y`, for the depths `1 ≤ t < d`:
every `L`-bad cylinder sends at most the share `q` of its members, plus `err`, to an odd next
letter. -/
def OneSidedShare (y : ℕ) (L q err : ℝ) (d : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t < d → ∀ w ∈ allWords t, LBad L w →
    ((cylinder y (t + 1) (w ++ [Branch.odd])).card : ℝ) ≤ q * (cylinder y t w).card + err

/-- **One depth.** Under the hypothesis at depth `1 ≤ t < d`,
`badMass (t+1) ≤ a_q · badMass t + (x - 1) err (2x)^t` with `a_q = 1 + (x-1) q`. -/
theorem badMass_succ_le {y : ℕ} {L x q err : ℝ} {d t : ℕ} (hx : 1 ≤ x) (herr : 0 ≤ err)
    (hH : OneSidedShare y L q err d) (ht1 : 1 ≤ t) (htd : t < d) :
    badMass y L x (t + 1)
      ≤ (1 + (x - 1) * q) * badMass y L x t + (x - 1) * err * (2 * x) ^ t := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 0 ≤ x - 1 := by linarith
  unfold badMass
  rw [sum_allWords_succ, mul_sum]
  have hpt : ∀ w ∈ allWords t,
      badWeight y L (t + 1) (w ++ [Branch.even]) * x ^ oddCount (w ++ [Branch.even])
        + badWeight y L (t + 1) (w ++ [Branch.odd]) * x ^ oddCount (w ++ [Branch.odd])
      ≤ (1 + (x - 1) * q) * (badWeight y L t w * x ^ oddCount w)
        + (x - 1) * err * x ^ oddCount w := by
    intro w hw
    have hlen : w.length = t := mem_allWords.mp hw
    simp only [oddCount_append]
    have hpow : 0 ≤ x ^ oddCount w := pow_nonneg hx0 _
    by_cases hbad : LBad L w
    · -- the bad parent: children below the split, odd child below the share
      have hsplit := cylinder_split y t w hlen
      have hshare := hH t ht1 htd w hw hbad
      have hE : badWeight y L (t + 1) (w ++ [Branch.even])
          ≤ (cylinder y (t + 1) (w ++ [Branch.even])).card := badWeight_le_card _ _ _ _
      have hO : badWeight y L (t + 1) (w ++ [Branch.odd])
          ≤ (cylinder y (t + 1) (w ++ [Branch.odd])).card := badWeight_le_card _ _ _ _
      have hw' : badWeight y L t w = (cylinder y t w).card := by
        unfold badWeight; rw [if_pos hbad]
      have hsplitR : ((cylinder y t w).card : ℝ)
          = (cylinder y (t + 1) (w ++ [Branch.even])).card
            + (cylinder y (t + 1) (w ++ [Branch.odd])).card := by exact_mod_cast hsplit
      have hEnn := badWeight_nonneg y L (t + 1) (w ++ [Branch.even])
      have hOnn := badWeight_nonneg y L (t + 1) (w ++ [Branch.odd])
      rw [hw']
      simp only [oddCount_even_cons, oddCount_odd_cons, oddCount_nil, add_zero, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right hE hpow,
        mul_le_mul_of_nonneg_right hO (mul_nonneg hpow hx0),
        mul_le_mul_of_nonneg_right hshare (mul_nonneg hx1 hpow), hpow]
    · -- a parent that is not bad has no bad child
      have hE : badWeight y L (t + 1) (w ++ [Branch.even]) = 0 := by
        unfold badWeight
        rw [if_neg (fun h => hbad (LBad_of_LBad_append h))]
      have hO : badWeight y L (t + 1) (w ++ [Branch.odd]) = 0 := by
        unfold badWeight
        rw [if_neg (fun h => hbad (LBad_of_LBad_append h))]
      have hw' : badWeight y L t w = 0 := by unfold badWeight; rw [if_neg hbad]
      rw [hE, hO, hw']
      simp only [zero_mul, add_zero, mul_zero, zero_add]
      exact mul_nonneg (mul_nonneg hx1 herr) hpow
  calc ∑ w ∈ allWords t,
        (badWeight y L (t + 1) (w ++ [Branch.even]) * x ^ oddCount (w ++ [Branch.even])
          + badWeight y L (t + 1) (w ++ [Branch.odd]) * x ^ oddCount (w ++ [Branch.odd]))
      ≤ ∑ w ∈ allWords t, ((1 + (x - 1) * q) * (badWeight y L t w * x ^ oddCount w)
          + (x - 1) * err * x ^ oddCount w) := sum_le_sum hpt
    _ = ∑ w ∈ allWords t, (1 + (x - 1) * q) * (badWeight y L t w * x ^ oddCount w)
          + (x - 1) * err * ∑ w ∈ allWords t, x ^ oddCount w := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ ∑ w ∈ allWords t, (1 + (x - 1) * q) * (badWeight y L t w * x ^ oddCount w)
          + (x - 1) * err * (2 * x) ^ t := by
        have := sum_pow_oddCount_le hx t
        have hc : 0 ≤ (x - 1) * err := mul_nonneg hx1 herr
        nlinarith [mul_le_mul_of_nonneg_left this hc]

/-! ### Unrolling, and the failures -/

/-- The odd starts of `(y, 2y]` are the cylinder of the empty word, and number at most `y`. -/
theorem card_cylinder_zero_le (y : ℕ) : (cylinder y 0 []).card ≤ y := by
  calc (cylinder y 0 []).card ≤ (Ioc y (2 * y)).card := card_filter_le _ _
    _ = y := by rw [Nat.card_Ioc]; omega

/-- **Depth one.** `badMass 1 ≤ x N`, with `N` the odd starts of `(y, 2y]`. -/
theorem badMass_one_le {y : ℕ} {L x : ℝ} (hx : 1 ≤ x) :
    badMass y L x 1 ≤ x * (cylinder y 0 []).card := by
  unfold badMass
  rw [sum_allWords_succ]
  simp only [allWords, sum_singleton, List.nil_append]
  have hsplit : ((cylinder y 0 []).card : ℝ)
      = (cylinder y 1 [Branch.even]).card + (cylinder y 1 [Branch.odd]).card := by
    have := cylinder_split y 0 [] rfl
    simp only [List.nil_append] at this
    exact_mod_cast this
  have hE := badWeight_le_card y L 1 [Branch.even]
  have hO := badWeight_le_card y L 1 [Branch.odd]
  have hEnn := badWeight_nonneg y L 1 [Branch.even]
  have hOnn := badWeight_nonneg y L 1 [Branch.odd]
  simp only [oddCount_even_cons, oddCount_odd_cons, oddCount_nil, zero_add, pow_zero, pow_one,
    mul_one]
  have h1 : badWeight y L 1 [Branch.even] ≤ x * (cylinder y 1 [Branch.even]).card :=
    le_trans hE (le_mul_of_one_le_left (Nat.cast_nonneg _) hx)
  have h2 : badWeight y L 1 [Branch.odd] * x ≤ (cylinder y 1 [Branch.odd]).card * x :=
    mul_le_mul_of_nonneg_right hO (by linarith)
  rw [hsplit]
  linarith

/-- **Unrolled.** Under the hypothesis up to depth `d`, for `t + 1 ≤ d`,
`badMass (t+1) ≤ x a_q^t N + (x-1) err t (2x)^t`, using `a_q ≤ 2x`. -/
theorem badMass_le {y : ℕ} {L x q err : ℝ} {d : ℕ} (hx : 1 ≤ x) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (herr : 0 ≤ err) (hH : OneSidedShare y L q err d) :
    ∀ t, t + 1 ≤ d → badMass y L x (t + 1)
      ≤ x * (1 + (x - 1) * q) ^ t * (cylinder y 0 []).card + (x - 1) * err * t * (2 * x) ^ t := by
  intro t
  induction t with
  | zero =>
      intro _
      have := badMass_one_le (y := y) (L := L) hx
      simpa using this
  | succ t ih =>
      intro htd
      have hstep := badMass_succ_le hx herr hH (t := t + 1) (by omega) (by omega)
      have hprev := ih (by omega)
      have hx1 : 0 ≤ x - 1 := by linarith
      have ha0 : 0 ≤ 1 + (x - 1) * q := by nlinarith
      have ha2x : 1 + (x - 1) * q ≤ 2 * x := by nlinarith
      have hN : (0 : ℝ) ≤ (cylinder y 0 []).card := Nat.cast_nonneg _
      have hc : 0 ≤ (x - 1) * err := mul_nonneg hx1 herr
      have hpow : (0 : ℝ) ≤ (2 * x) ^ t := by positivity
      have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
      have h1 : (1 + (x - 1) * q) * badMass y L x (t + 1)
          ≤ (1 + (x - 1) * q)
            * (x * (1 + (x - 1) * q) ^ t * (cylinder y 0 []).card
              + (x - 1) * err * t * (2 * x) ^ t) :=
        mul_le_mul_of_nonneg_left hprev ha0
      have h2 : (1 + (x - 1) * q) * ((x - 1) * err * t * (2 * x) ^ t)
          ≤ (2 * x) * ((x - 1) * err * t * (2 * x) ^ t) :=
        mul_le_mul_of_nonneg_right ha2x (by positivity)
      push_cast
      calc badMass y L x (t + 1 + 1)
          ≤ (1 + (x - 1) * q) * badMass y L x (t + 1) + (x - 1) * err * (2 * x) ^ (t + 1) := hstep
        _ ≤ (1 + (x - 1) * q)
              * (x * (1 + (x - 1) * q) ^ t * (cylinder y 0 []).card
                + (x - 1) * err * t * (2 * x) ^ t)
              + (x - 1) * err * (2 * x) ^ (t + 1) := by linarith
        _ ≤ x * (1 + (x - 1) * q) ^ (t + 1) * (cylinder y 0 []).card
              + (x - 1) * err * (t + 1) * (2 * x) ^ (t + 1) := by
            have e : (1 + (x - 1) * q)
                * (x * (1 + (x - 1) * q) ^ t * (cylinder y 0 []).card
                  + (x - 1) * err * t * (2 * x) ^ t)
                + (x - 1) * err * (2 * x) ^ (t + 1)
                = x * (1 + (x - 1) * q) ^ (t + 1) * (cylinder y 0 []).card
                  + ((1 + (x - 1) * q) * ((x - 1) * err * t * (2 * x) ^ t)
                    + (x - 1) * err * (2 * x) ^ (t + 1)) := by ring
            have e' : x * (1 + (x - 1) * q) ^ (t + 1) * (cylinder y 0 []).card
                + (x - 1) * err * (t + 1) * (2 * x) ^ (t + 1)
                = x * (1 + (x - 1) * q) ^ (t + 1) * (cylinder y 0 []).card
                  + ((2 * x) * ((x - 1) * err * t * (2 * x) ^ t)
                    + (x - 1) * err * (2 * x) ^ (t + 1)) := by ring
            rw [e, e']
            linarith

/-- **Lemma 8.1 with the Markov tilt.** Every odd failure in `(y, 2y]` lies in a bad cylinder
of depth `d ≥ C L(y)` whose word has at least `p_C d` odd letters, so the failures number at
most `badMass d / x^{p_C d}`. -/
theorem oddFailures_card_le_badMass {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y) {C x : ℝ}
    (hC : 0 < C) (hx : 1 ≤ x) {d : ℕ} (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d) :
    ((oddFailures y).card : ℝ) ≤ badMass y (scaleL N₀ y) x d / x ^ (pC C * d) := by
  have hx0 : 0 < x := by linarith
  have hxp : 0 < x ^ (pC C * d) := Real.rpow_pos_of_pos hx0 _
  rw [le_div_iff₀ hxp]
  have hsub := oddFailures_subset_bad_cylinders hfloor y d
  have hcard : ((oddFailures y).card : ℝ)
      ≤ ∑ w ∈ {w ∈ allWords d | EnvelopeBad N₀ (2 * y) w},
          ((cylinder y d w).card : ℝ) := by
    have h1 := card_le_card hsub
    have h2 := card_biUnion_le (s := {w ∈ allWords d | EnvelopeBad N₀ (2 * y) w})
      (t := cylinder y d)
    exact_mod_cast le_trans h1 h2
  have hterm : ∀ w ∈ {w ∈ allWords d | EnvelopeBad N₀ (2 * y) w},
      ((cylinder y d w).card : ℝ) * x ^ (pC C * d)
        ≤ badWeight y (scaleL N₀ y) d w * x ^ oddCount w := by
    intro w hw
    rw [mem_filter] at hw
    have hbad : LBad (scaleL N₀ y) w := by
      have h := LBad_of_envelopeBad hN (by omega : 2 ≤ 2 * y) hw.2
      unfold scaleL scaleRatio
      push_cast at h
      exact h
    have hodd : pC C * d ≤ oddCount w := LBad_oddCount_ge hC hd hd1 hw.1 hbad
    have hbw : badWeight y (scaleL N₀ y) d w = (cylinder y d w).card := by
      unfold badWeight; rw [if_pos hbad]
    rw [hbw]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc x ^ (pC C * d) ≤ x ^ (oddCount w : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hodd
      _ = x ^ oddCount w := Real.rpow_natCast x _
  calc ((oddFailures y).card : ℝ) * x ^ (pC C * d)
      ≤ (∑ w ∈ {w ∈ allWords d | EnvelopeBad N₀ (2 * y) w}, ((cylinder y d w).card : ℝ))
          * x ^ (pC C * d) := mul_le_mul_of_nonneg_right hcard hxp.le
    _ = ∑ w ∈ {w ∈ allWords d | EnvelopeBad N₀ (2 * y) w},
          ((cylinder y d w).card : ℝ) * x ^ (pC C * d) := sum_mul _ _ _
    _ ≤ ∑ w ∈ {w ∈ allWords d | EnvelopeBad N₀ (2 * y) w},
          badWeight y (scaleL N₀ y) d w * x ^ oddCount w := sum_le_sum hterm
    _ ≤ ∑ w ∈ allWords d, badWeight y (scaleL N₀ y) d w * x ^ oddCount w :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun w _ _ => mul_nonneg (badWeight_nonneg _ _ _ _) (pow_nonneg hx0.le _))
    _ = badMass y (scaleL N₀ y) x d := rfl

/-- **Theorem 9.1 by exponential moments, exact.** Under the one-sided hypothesis at scale `y`
with depth `d ≥ C L(y)`, above a certified floor `N₀`, the odd failures in `(y, 2y]` number at
most `(x a_q^{d-1} N + (x-1) err (d-1) (2x)^{d-1}) / x^{p_C d}` for every tilt `x ≥ 1`, with
`N` the odd starts of `(y, 2y]` and `a_q = 1 + (x-1) q`. -/
theorem one_sided_bound {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y)
    {C x q err : ℝ} (hC : 0 < C) (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (herr : 0 ≤ err)
    {d : ℕ} (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d)
    (hH : OneSidedShare y (scaleL N₀ y) q err d) :
    ((oddFailures y).card : ℝ) ≤
      (x * (1 + (x - 1) * q) ^ (d - 1) * (cylinder y 0 []).card
        + (x - 1) * err * ((d : ℝ) - 1) * (2 * x) ^ (d - 1)) / x ^ (pC C * d) := by
  have h1 := oddFailures_card_le_badMass hN hfloor hy hC hx hd1 hd
  have h2 := badMass_le hx hq0 hq1 herr hH (d - 1) (by omega)
  rw [Nat.sub_add_cancel hd1] at h2
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd1]; simp
  rw [hcast] at h2
  have hxp : 0 < x ^ (pC C * d) := Real.rpow_pos_of_pos (by linarith) _
  exact le_trans h1 (div_le_div_of_nonneg_right h2 hxp.le)

/-! ### At the re-centring tilt -/

/-- The relative entropy `D(p ‖ q) = p log(p/q) + (1-p) log((1-p)/(1-q))`. -/
noncomputable def klDiv (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- The re-centring tilt `x = p(1-q)/(q(1-p))`, at which the bound has exponent `D(p ‖ q)`. -/
noncomputable def tilt (p q : ℝ) : ℝ := p * (1 - q) / (q * (1 - p))

theorem tilt_ge_one {p q : ℝ} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) : 1 ≤ tilt p q := by
  unfold tilt
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

/-- `a_q^d / x^{p d} = e^{-d D(p ‖ q)}` at the re-centring tilt (Proposition 9.3's identity). -/
theorem tilt_pow_ratio {p q : ℝ} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) (d : ℕ) :
    (1 + (tilt p q - 1) * q) ^ d / tilt p q ^ (p * d) = Real.exp (-(d * klDiv p q)) := by
  have hx1 := tilt_ge_one hq0 hqp hp1
  have hx : 0 < tilt p q := by linarith
  have ha : 0 < 1 + (tilt p q - 1) * q := by nlinarith
  have key := tilt_exponent_eq_kl p q hq0 hqp hp1
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hx, ← Real.exp_sub]
  congr 1
  unfold klDiv tilt at *
  linear_combination (-(d : ℝ)) * key

/-- **Theorem 9.1 at the re-centring tilt.** With `q < p_C < 1` and `x = p_C(1-q)/(q(1-p_C))`,
the main term is `(x/a_q) N e^{-d D(p_C ‖ q)}`: the exponent `C D(p_C ‖ q)/log 2` per unit of
`L(y)`, which the paper records is at least the Azuma exponent `e_q(C)` of Theorem 9.1. -/
theorem one_sided_bound_kl {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y)
    {C q err : ℝ} (hC : 0 < C) (hq0 : 0 < q) (hqp : q < pC C) (hp1 : pC C < 1)
    (herr : 0 ≤ err) {d : ℕ}
    (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d) (hH : OneSidedShare y (scaleL N₀ y) q err d) :
    ((oddFailures y).card : ℝ) ≤
      tilt (pC C) q / (1 + (tilt (pC C) q - 1) * q) * (cylinder y 0 []).card
          * Real.exp (-(d * klDiv (pC C) q))
        + (tilt (pC C) q - 1) * err * ((d : ℝ) - 1) * (2 * tilt (pC C) q) ^ (d - 1)
          / tilt (pC C) q ^ (pC C * d) := by
  have hx1 := tilt_ge_one hq0 hqp hp1
  have h := one_sided_bound hN hfloor hy hC hx1 hq0.le (by linarith) herr hd1 hd hH
  have ha : 0 < 1 + (tilt (pC C) q - 1) * q := by nlinarith
  have hxp : 0 < tilt (pC C) q ^ (pC C * d) := Real.rpow_pos_of_pos (by linarith) _
  have hratio := tilt_pow_ratio hq0 hqp hp1 d
  have hmain : tilt (pC C) q * (1 + (tilt (pC C) q - 1) * q) ^ (d - 1) * (cylinder y 0 []).card
        / tilt (pC C) q ^ (pC C * d)
      = tilt (pC C) q / (1 + (tilt (pC C) q - 1) * q) * (cylinder y 0 []).card
          * Real.exp (-(d * klDiv (pC C) q)) := by
    rw [← hratio]
    have hpow : (1 + (tilt (pC C) q - 1) * q) ^ d
        = (1 + (tilt (pC C) q - 1) * q) * (1 + (tilt (pC C) q - 1) * q) ^ (d - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hd1]
    rw [hpow]
    field_simp
  rw [add_div, hmain] at h
  exact h

end OneSided

end Problems.Juggler
