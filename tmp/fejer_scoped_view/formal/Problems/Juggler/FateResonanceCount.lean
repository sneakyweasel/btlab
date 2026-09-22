import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Problems.Juggler.FateThinFibers

namespace Problems.Juggler

open Finset
open scoped Classical

namespace FiberParity

/-!
# The resonance count: Lemma 3 of the poor-fiber tail note

The poor-fiber tail note (`docs/theory/juggler_oe_poor_fiber_tail_note.md`), Lemma 3 (arc
count): for `u ≥ 10^6`, `Q ≥ 1` and `δ ∈ [0, 1/2)`, the `m ∈ (u, 2u]` for which some
`q ≤ Q` has `‖q A_m‖ ≤ δ` number at most
`(0.882 u^{2/3} + 2)(2 Q δ (2u)^{1/3} + Q(Q+1))`.

This is `bad_count_le` of `FateThinFibers` with its two goodness arcs replaced by a union
over `q ≤ Q`; it carries no new idea, only the union bound. `Resonant Q δ m` says that some
`1 ≤ q ≤ Q` puts `q A_m` within `δ` of an integer, spelled — as `Good` is — without any
distance-to-the-nearest-integer function: `∃ P : ℤ, |q A_m - P| ≤ δ`.

The proof is the note's count. `resonant_mem_arc` is the reduction: dividing `P` by `q` with
remainder `p < q` puts `A_m` within `δ/q` of the grid point `p/q` modulo one, and the shift
by `δ/q` — the trick of `bad_mem_arc` — turns that two-sided arc into the single
non-wrapping arc `[0, 2δ/q]`. `Am_window_le` is the window count of `bad_count_le` freed of
its two-case disjunction: a constant shift leaves `A_{2u} - A_{u+1}` alone, so `A_m + c`
meets at most `0.882 u^{2/3} + 2` integer windows on `(u, 2u]` (`Am_double_sub_le`).
`shifted_arc_count_le` feeds the two into `arc_count_le` with the step floor `d = ε_{2u}`
(`Am_step_ge`, `eps_antitone`). `resonance_count_one` unions the `q` arcs of one denominator,
`resonance_count_le` the `Q` denominators, with `sum_range_arc_terms` carrying the Gauss sum
`Σ_{q < Q} (q+1) = Q(Q+1)/2`; `resonance_count_le'` restates the bound with `1/ε_{2u}`
written as `(2u)^{1/3}` (`one_div_eps`), which is the note's own form.

Two deliberate slacks. The arcs are half-open and a hair wide — width `2δ/q + ε_{2u}` rather
than `2δ/q` — so that the *closed* condition `‖q A_m‖ ≤ δ` fits inside `[0, w)`; that costs
one extra point per arc and is the entire reason the second term reads `Q(Q+1)` here and
`Q(Q+1)/2` in the note. The `δ` term is the note's, exactly. Nothing else is given away.

Not a statement about good fibers, and not a bound on any parity share: the block lock
(Lemma 1) and the poor-fiber tail (Theorem 4) are not in this file, and no goodness
hypothesis appears anywhere in it. Not a halt theorem.
-/

/-! ### Resonance -/

/-- `m` is `(Q, δ)`-resonant: some `q` with `1 ≤ q ≤ Q` has `‖q A_m‖ ≤ δ`, the distance from
`q A_m` to the nearest integer. Written as `∃ P : ℤ, |q A_m - P| ≤ δ`, the house spelling of
`‖·‖` (compare `Good`, which unpacks the same notion into `Int.fract` inequalities). -/
def Resonant (Q : ℕ) (δ : ℝ) (m : ℕ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ ∃ P : ℤ, |(q : ℝ) * Am m - (P : ℝ)| ≤ δ

/-! ### Numerical bookkeeping -/

/-- `1 / ε_n = n^{1/3}`; the form in which the note writes the step floor of a dyadic
block. -/
theorem one_div_eps {n : ℕ} (hn : 1 ≤ n) : 1 / eps n = (n : ℝ) ^ ((1 : ℝ) / 3) := by
  unfold eps
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_neg hn0.le, one_div, inv_inv]

/-- The Gauss sum behind Lemma 3, already multiplied through by the per-arc bound:
`Σ_{q < Q} W (2δ/E + 2(q+1)) = W (2Qδ/E + Q(Q+1))`. -/
theorem sum_range_arc_terms (W E δ : ℝ) (Q : ℕ) :
    ∑ q ∈ Finset.range Q, W * (2 * δ / E + 2 * ((q + 1 : ℕ) : ℝ)) =
      W * (2 * (Q : ℝ) * δ / E + (Q : ℝ) * ((Q : ℝ) + 1)) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-! ### The reduction: resonance is membership in one of `q` arcs -/

/-- **Lemma 3, the reduction.** If `|q A_m - P| ≤ δ` for some integer `P`, with `1 ≤ q` and
`0 ≤ δ < 1/2`, then `A_m` lies within `δ/q` of the grid point `p/q` for some `p < q`, modulo
one; after the shift by `δ/q` that two-sided arc is the single non-wrapping arc
`[0, 2δ/q]`. This is the `q`-fold form of `bad_mem_arc`, and the shift is the same trick. -/
theorem resonant_mem_arc {q : ℕ} (hq : 1 ≤ q) {δ : ℝ} (hδ : 0 ≤ δ) (hδ2 : δ < 1 / 2)
    {m : ℕ} {P : ℤ} (hP : |(q : ℝ) * Am m - (P : ℝ)| ≤ δ) :
    ∃ p : ℕ, p < q ∧
      Int.fract (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))) ≤ 2 * δ / (q : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1r : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq0
  -- divide `P` by `q` with remainder
  obtain ⟨k, p, hpq, hPeq⟩ :
      ∃ (k : ℤ) (p : ℕ), p < q ∧ (P : ℝ) = (q : ℝ) * (k : ℝ) + (p : ℝ) := by
    have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
    have hmod0 : (0 : ℤ) ≤ P % (q : ℤ) := Int.emod_nonneg P (by omega)
    have hmodlt : P % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos P hqz
    have hdiv : (q : ℤ) * (P / (q : ℤ)) + P % (q : ℤ) = P := Int.mul_ediv_add_emod P (q : ℤ)
    refine ⟨P / (q : ℤ), (P % (q : ℤ)).toNat, by omega, ?_⟩
    have htn : (((P % (q : ℤ)).toNat : ℕ) : ℤ) = P % (q : ℤ) := Int.toNat_of_nonneg hmod0
    have hz : (q : ℤ) * (P / (q : ℤ)) + (((P % (q : ℤ)).toNat : ℕ) : ℤ) = P := by
      rw [htn]; exact hdiv
    exact_mod_cast hz.symm
  refine ⟨p, hpq, ?_⟩
  have hab := abs_le.mp hP
  -- `q` times the shifted value is `(q A_m - P) + δ`, which sits in `[0, 2δ]`
  have hqt : (q : ℝ) * (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ)) - (k : ℝ)) =
      ((q : ℝ) * Am m - (P : ℝ)) + δ := by
    rw [hPeq]
    field_simp
    ring
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ)) - (k : ℝ) :=
    ⟨_, rfl⟩
  rw [← htdef] at hqt
  have h0 : (0 : ℝ) ≤ (q : ℝ) * t := by rw [hqt]; linarith [hab.1]
  have h1 : (q : ℝ) * t ≤ 2 * δ := by rw [hqt]; linarith [hab.2]
  have ht0 : (0 : ℝ) ≤ t := by nlinarith [h0, hq0]
  have ht1 : t ≤ 2 * δ / (q : ℝ) := by
    rw [le_div_iff₀ hq0]
    linarith [h1]
  have hdivle : 2 * δ / (q : ℝ) ≤ 2 * δ := by
    rw [div_le_iff₀ hq0]
    nlinarith [mul_nonneg hδ (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)]
  have hfr : Int.fract (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))) = t := by
    rw [Int.fract_eq_iff]
    refine ⟨ht0, by linarith, k, ?_⟩
    rw [htdef]; ring
  rw [hfr]
  exact ht1

/-! ### The window count for a constant shift of `A` -/

/-- **The window count.** On `(u, 2u]` the shifted sequence `A_m + c` meets at most
`0.882 u^{2/3} + 2` integer windows, for every real shift `c`: the shift cancels in
`A_{2u} - A_{u+1}`, so this is `Am_double_sub_le` with two floors. It is the
disjunction-free form of the `hwin` block inside `bad_count_le`. -/
theorem Am_window_le {u : ℕ} (hu : 10 ^ 6 ≤ u) (c : ℝ) :
    ((⌊Am (2 * u) + c⌋ - ⌊Am (u + 1) + c⌋ + 1 : ℤ) : ℝ) ≤
      0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2 := by
  have hu1 : 1 ≤ u := by omega
  have hA : Am u ≤ Am (u + 1) := by
    have := Am_step_ge (m := u) hu1
    have := eps_pos (m := u + 1) (by omega)
    linarith
  have hdouble := Am_double_sub_le hu1
  have h1 : (⌊Am (2 * u) + c⌋ : ℝ) ≤ Am (2 * u) + c := Int.floor_le _
  have h2 : Am (u + 1) + c < (⌊Am (u + 1) + c⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  push_cast
  linarith

/-! ### One arc -/

/-- **The shifted arc count.** For `u ≥ 10^6`, a real shift `c` and a width `w ≥ 0`, the
`m ∈ (u, 2u]` with `{A_m + c} < w` number at most `(0.882 u^{2/3} + 2)(w/ε_{2u} + 1)`: the
step floor on the block is `ε_{2u}` (`Am_step_ge`, `eps_antitone`), so this is
`arc_count_le` composed with `Am_window_le`. -/
theorem shifted_arc_count_le {u : ℕ} (hu : 10 ^ 6 ≤ u) (c w : ℝ) (hw : 0 ≤ w) :
    (#{m ∈ Finset.Ioc u (2 * u) | (0 : ℝ) ≤ Int.fract (Am m + c) ∧
        Int.fract (Am m + c) < 0 + w} : ℝ) ≤
      (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) * (w / eps (2 * u) + 1) := by
  have hdpos : 0 < eps (2 * u) := eps_pos (by omega)
  have hstep : ∀ m, u < m → m < 2 * u → eps (2 * u) ≤ (Am (m + 1) + c) - (Am m + c) := by
    intro m hm hm2
    have h : eps (2 * u) ≤ Am (m + 1) - Am m := by
      refine le_trans ?_ (Am_step_ge (by omega))
      exact eps_antitone (by omega) (by omega)
    linarith
  have hA :=
    arc_count_le (fun m => Am m + c) u (2 * u) (by omega) (eps (2 * u)) 0 w hdpos hw hstep
  have hwd : (0 : ℝ) ≤ w / eps (2 * u) + 1 := by
    have := div_nonneg hw hdpos.le
    linarith
  refine le_trans hA (mul_le_mul_of_nonneg_right ?_ hwd)
  exact Am_window_le hu c

/-! ### Lemma 3, first part: one denominator -/

/-- **Lemma 3, one denominator.** For `u ≥ 10^6`, `1 ≤ q` and `0 ≤ δ < 1/2`, the
`m ∈ (u, 2u]` with `‖q A_m‖ ≤ δ` number at most
`(0.882 u^{2/3} + 2)(2δ/ε_{2u} + 2q)`. The set is covered by the `q` arcs
`{A_m - p/q + δ/q} < 2δ/q + ε_{2u}`, `p < q` (`resonant_mem_arc`), and each of them is
counted by `shifted_arc_count_le`. -/
theorem resonance_count_one {u : ℕ} (hu : 10 ^ 6 ≤ u) (q : ℕ) (hq : 1 ≤ q) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : δ < 1 / 2) :
    (#{m ∈ Finset.Ioc u (2 * u) | ∃ P : ℤ, |(q : ℝ) * Am m - (P : ℝ)| ≤ δ} : ℝ) ≤
      (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) * (2 * δ / eps (2 * u) + 2 * (q : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq0
  have hdpos : 0 < eps (2 * u) := eps_pos (by omega)
  have hEne : eps (2 * u) ≠ 0 := ne_of_gt hdpos
  have hwnn : (0 : ℝ) ≤ 2 * δ / (q : ℝ) + eps (2 * u) := by
    have h1 : (0 : ℝ) ≤ 2 * δ / (q : ℝ) := div_nonneg (by linarith) hq0.le
    linarith
  -- the cover by `q` arcs
  have hcover : {m ∈ Finset.Ioc u (2 * u) | ∃ P : ℤ, |(q : ℝ) * Am m - (P : ℝ)| ≤ δ} ⊆
      (Finset.range q).biUnion (fun p => {m ∈ Finset.Ioc u (2 * u) |
        (0 : ℝ) ≤ Int.fract (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))) ∧
        Int.fract (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))) <
          0 + (2 * δ / (q : ℝ) + eps (2 * u))}) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmIoc, P, hP⟩ := hm
    obtain ⟨p, hpq, harc⟩ := resonant_mem_arc hq hδ hδ2 hP
    rw [Finset.mem_biUnion]
    refine ⟨p, Finset.mem_range.mpr hpq,
      Finset.mem_filter.mpr ⟨hmIoc, Int.fract_nonneg _, ?_⟩⟩
    show Int.fract (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))) <
      0 + (2 * δ / (q : ℝ) + eps (2 * u))
    linarith
  -- the per-arc count is one application of `shifted_arc_count_le`
  have hper : ∀ p ∈ Finset.range q, ((#{m ∈ Finset.Ioc u (2 * u) |
        (0 : ℝ) ≤ Int.fract (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))) ∧
        Int.fract (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))) <
          0 + (2 * δ / (q : ℝ) + eps (2 * u))}) : ℝ) ≤
      (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
        ((2 * δ / (q : ℝ) + eps (2 * u)) / eps (2 * u) + 1) := fun p _ =>
    shifted_arc_count_le hu (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))
      (2 * δ / (q : ℝ) + eps (2 * u)) hwnn
  -- `q` copies of `2δ/(q ε) + 2` make `2δ/ε + 2q`
  have hscalar : (q : ℝ) * ((2 * δ / (q : ℝ) + eps (2 * u)) / eps (2 * u) + 1) =
      2 * δ / eps (2 * u) + 2 * (q : ℝ) := by
    field_simp
    ring
  calc (#{m ∈ Finset.Ioc u (2 * u) | ∃ P : ℤ, |(q : ℝ) * Am m - (P : ℝ)| ≤ δ} : ℝ)
      ≤ ∑ p ∈ Finset.range q, ((#{m ∈ Finset.Ioc u (2 * u) |
          (0 : ℝ) ≤ Int.fract (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))) ∧
          Int.fract (Am m + (δ / (q : ℝ) - (p : ℝ) / (q : ℝ))) <
            0 + (2 * δ / (q : ℝ) + eps (2 * u))}) : ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ Finset.range q, ((0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
          ((2 * δ / (q : ℝ) + eps (2 * u)) / eps (2 * u) + 1)) := Finset.sum_le_sum hper
    _ = (q : ℝ) * ((0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
          ((2 * δ / (q : ℝ) + eps (2 * u)) / eps (2 * u) + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
          ((q : ℝ) * ((2 * δ / (q : ℝ) + eps (2 * u)) / eps (2 * u) + 1)) := by ring
    _ = (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
          (2 * δ / eps (2 * u) + 2 * (q : ℝ)) := by rw [hscalar]

/-! ### Lemma 3: the union over `q ≤ Q` -/

/-- **Lemma 3 (arc count).** For `u ≥ 10^6`, every `Q` and every `δ` with `0 ≤ δ < 1/2`,
the `(Q, δ)`-resonant `m ∈ (u, 2u]` number at most
`(0.882 u^{2/3} + 2)(2 Q δ / ε_{2u} + Q(Q+1))`. The denominators are indexed as `q + 1`
over `Finset.range Q`, and each contributes `resonance_count_one`; the Gauss sum
`Σ_{q < Q} 2(q+1) = Q(Q+1)` is `sum_range_arc_terms`. -/
theorem resonance_count_le {u : ℕ} (hu : 10 ^ 6 ≤ u) (Q : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : δ < 1 / 2) :
    (#{m ∈ Finset.Ioc u (2 * u) | Resonant Q δ m} : ℝ) ≤
      (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
        (2 * (Q : ℝ) * δ / eps (2 * u) + (Q : ℝ) * ((Q : ℝ) + 1)) := by
  have hcover : {m ∈ Finset.Ioc u (2 * u) | Resonant Q δ m} ⊆
      (Finset.range Q).biUnion (fun q => {m ∈ Finset.Ioc u (2 * u) |
        ∃ P : ℤ, |((q + 1 : ℕ) : ℝ) * Am m - (P : ℝ)| ≤ δ}) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmIoc, hres⟩ := hm
    unfold Resonant at hres
    obtain ⟨q, hq1, hqQ, P, hP⟩ := hres
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Finset.mem_biUnion]
    exact ⟨q', Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨hmIoc, P, hP⟩⟩
  have hper : ∀ q ∈ Finset.range Q, ((#{m ∈ Finset.Ioc u (2 * u) |
        ∃ P : ℤ, |((q + 1 : ℕ) : ℝ) * Am m - (P : ℝ)| ≤ δ}) : ℝ) ≤
      (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
        (2 * δ / eps (2 * u) + 2 * ((q + 1 : ℕ) : ℝ)) := fun q _ =>
    resonance_count_one hu (q + 1) (by omega) hδ hδ2
  calc (#{m ∈ Finset.Ioc u (2 * u) | Resonant Q δ m} : ℝ)
      ≤ ∑ q ∈ Finset.range Q, ((#{m ∈ Finset.Ioc u (2 * u) |
          ∃ P : ℤ, |((q + 1 : ℕ) : ℝ) * Am m - (P : ℝ)| ≤ δ}) : ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ q ∈ Finset.range Q, ((0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
          (2 * δ / eps (2 * u) + 2 * ((q + 1 : ℕ) : ℝ))) := Finset.sum_le_sum hper
    _ = (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
          (2 * (Q : ℝ) * δ / eps (2 * u) + (Q : ℝ) * ((Q : ℝ) + 1)) :=
        sum_range_arc_terms (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) (eps (2 * u)) δ Q

/-- **Lemma 3, the note's form.** The same count with `1/ε_{2u}` written as `(2u)^{1/3}`:
`#{m ∈ (u, 2u] : ∃ q ≤ Q, ‖q A_m‖ ≤ δ} ≤ (0.882 u^{2/3} + 2)(2 Q δ (2u)^{1/3} + Q(Q+1))`. -/
theorem resonance_count_le' {u : ℕ} (hu : 10 ^ 6 ≤ u) (Q : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : δ < 1 / 2) :
    (#{m ∈ Finset.Ioc u (2 * u) | Resonant Q δ m} : ℝ) ≤
      (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
        (2 * (Q : ℝ) * δ * ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3) + (Q : ℝ) * ((Q : ℝ) + 1)) := by
  have h := resonance_count_le hu Q hδ hδ2
  have he : 2 * (Q : ℝ) * δ / eps (2 * u) =
      2 * (Q : ℝ) * δ * ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [← one_div_eps (n := 2 * u) (by omega)]
    ring
  rwa [he] at h

end FiberParity

end Problems.Juggler
