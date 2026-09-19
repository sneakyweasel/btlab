import Problems.Juggler.FateThinFibers

namespace Problems.Juggler

open Finset
open scoped Classical

namespace FiberParity

/-!
# The resonance count

`docs/theory/juggler_oe_poor_fiber_tail_note.md`, Lemma 3: for `u ≥ 10^6` the
`m ∈ (u, 2u]` whose `A_m = (3/2) m^{2/3}` resonates with some denominator `q ≤ Q`
at width `δ` number `O(δ u^{2/3}/ε_{2u} + Q^2 u^{2/3})`.

This introduces no new mathematical idea. `bad_count_le` covers the bad set by two
arcs and applies `arc_count_le` to each; here the resonant set is covered by one arc
per `q`, and `arc_count_le` is applied once per `q`. The note's own proof covers
`‖q α_m‖ ≤ δ` by the `q` arcs of half-width `δ/q` around the points `p/q`, which
forces a coprimality bookkeeping that is not needed: applying `arc_count_le` to
`φ = q A_m` instead of to `A_m` turns the `q` arcs into a single arc of width `2δ`,
at the cost of a step lower bound `q ε` rather than `ε`. The two routes give the same
bound, because the `q` in the step cancels the `q` in the window count.

The shift by `δ`, which turns the wrap-around arc `‖·‖ < δ` into the single arc
`[0, 2δ)`, is `bad_mem_arc`'s trick and is `resonant_mem_arc` here.

Not a statement about good fibers, and not a halt theorem: this is one half of the
poor-fiber tail, the other being the block lock, which is what supplies the `δ` and
the `Q` this module takes as given.
-/

/-! ### Resonance -/

/-- `m` is `(q, δ)`-resonant when `q A_m` lies within `δ` of an integer. -/
def Resonant (q : ℕ) (δ : ℝ) (m : ℕ) : Prop :=
  |(q : ℝ) * Am m - round ((q : ℝ) * Am m)| < δ

/-- `m` is `(Q, δ)`-resonant when some denominator `1 ≤ q ≤ Q` resonates. -/
def ResonantUpTo (Q : ℕ) (δ : ℝ) (m : ℕ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ Resonant q δ m

/-- A resonant `m` sits in a single arc of width `2δ` once `q A_m` is shifted by `δ`:
the wrap-around at an integer becomes the left endpoint. -/
theorem resonant_mem_arc {q : ℕ} {δ : ℝ} {m : ℕ} (hδ : δ < 1 / 2) (h : Resonant q δ m) :
    Int.fract ((q : ℝ) * Am m + δ) < 2 * δ := by
  set k : ℤ := round ((q : ℝ) * Am m) with hk
  rw [Resonant, abs_lt] at h
  have h0 : (0 : ℝ) ≤ (q : ℝ) * Am m + δ - (k : ℝ) := by linarith [h.1]
  have h1 : (q : ℝ) * Am m + δ - (k : ℝ) < 1 := by linarith [h.2]
  have hfr : Int.fract ((q : ℝ) * Am m + δ) = (q : ℝ) * Am m + δ - (k : ℝ) := by
    conv_lhs =>
      rw [show ((q : ℝ) * Am m + δ) = ((q : ℝ) * Am m + δ - (k : ℝ)) + (k : ℝ) by ring]
    rw [Int.fract_add_int]
    exact Int.fract_eq_self.mpr ⟨h0, h1⟩
  rw [hfr]
  linarith [h.2]

/-! ### The count at one denominator -/

/-- **The resonance count at one `q`.** For `u ≥ 10^6`, `1 ≤ q` and `0 < δ < 1/2`,
the `m ∈ (u, 2u]` that are `(q, δ)`-resonant number at most
`(0.882 q u^{2/3} + 2)(2δ/(q ε_{2u}) + 1)`.

The `q` in the two factors cancels in the leading term, which is why summing over
`q ≤ Q` costs `2Qδ/ε_{2u}` in the main term and only `Q(Q+1)/2` in the remainder. -/
theorem resonance_count_one {u q : ℕ} (hu : 10 ^ 6 ≤ u) (hq : 1 ≤ q) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    (#{m ∈ Finset.Ioc u (2 * u) | Resonant q δ m} : ℝ) ≤
      (0.882 * (q : ℝ) * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
        (2 * δ / ((q : ℝ) * eps (2 * u)) + 1) := by
  have hu1 : 1 ≤ u := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set d := eps (2 * u) with hd
  have hdpos : 0 < d := eps_pos (by omega)
  set φ : ℕ → ℝ := fun m => (q : ℝ) * Am m + δ with hφ
  -- the increments of `φ` on `(u, 2u)` are at least `q d`
  have hstep : ∀ m, u < m → m < 2 * u → (q : ℝ) * d ≤ φ (m + 1) - φ m := by
    intro m hm hm2
    have h1 : eps (m + 1) ≤ Am (m + 1) - Am m := Am_step_ge (by omega)
    have h2 : d ≤ eps (m + 1) := eps_antitone (by omega) (by omega)
    have h3 : d ≤ Am (m + 1) - Am m := le_trans h2 h1
    have h4 : (q : ℝ) * d ≤ (q : ℝ) * (Am (m + 1) - Am m) :=
      mul_le_mul_of_nonneg_left h3 hq0.le
    simp only [hφ]
    linarith
  -- resonance is membership in the single arc `[0, 2δ)`
  have hcover : {m ∈ Finset.Ioc u (2 * u) | Resonant q δ m} ⊆
      {m ∈ Finset.Ioc u (2 * u) | (0 : ℝ) ≤ Int.fract (φ m) ∧
        Int.fract (φ m) < 0 + 2 * δ} := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, Int.fract_nonneg _, ?_⟩
    have := resonant_mem_arc (q := q) (δ := δ) (m := m) hδ hm.2
    simp only [hφ]
    linarith
  have harc := arc_count_le φ u (2 * u) (by omega) ((q : ℝ) * d) 0 (2 * δ)
    (by positivity) (by positivity) hstep
  have hcard : (#{m ∈ Finset.Ioc u (2 * u) | Resonant q δ m} : ℝ) ≤
      ((⌊φ (2 * u)⌋ - ⌊φ (u + 1)⌋ + 1 : ℤ) : ℝ) * (2 * δ / ((q : ℝ) * d) + 1) := by
    refine le_trans ?_ harc
    exact_mod_cast Finset.card_le_card hcover
  -- the number of integer windows `φ` meets
  have hwin : ((⌊φ (2 * u)⌋ - ⌊φ (u + 1)⌋ + 1 : ℤ) : ℝ) ≤
      0.882 * (q : ℝ) * (u : ℝ) ^ ((2 : ℝ) / 3) + 2 := by
    have hA : Am u ≤ Am (u + 1) := by
      have h1 := Am_step_ge (m := u) hu1
      have h2 := eps_pos (m := u + 1) (by omega)
      linarith
    have hdouble := Am_double_sub_le hu1
    have h1 : (⌊φ (2 * u)⌋ : ℝ) ≤ φ (2 * u) := Int.floor_le _
    have h2 : φ (u + 1) < ⌊φ (u + 1)⌋ + 1 := Int.lt_floor_add_one _
    have hdiff : φ (2 * u) - φ (u + 1) = (q : ℝ) * (Am (2 * u) - Am (u + 1)) := by
      simp only [hφ]; ring
    have hsub : Am (2 * u) - Am (u + 1) ≤ 0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) := by linarith
    have hqsub : (q : ℝ) * (Am (2 * u) - Am (u + 1)) ≤
        (q : ℝ) * (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left hsub hq0.le
    push_cast
    linarith
  refine le_trans hcard ?_
  have hpos : (0 : ℝ) ≤ 2 * δ / ((q : ℝ) * d) + 1 := by positivity
  exact mul_le_mul_of_nonneg_right hwin hpos

/-! ### The count over every denominator up to `Q` -/

/-- **Lemma 3 (the resonance count).** For `u ≥ 10^6` and `0 < δ < 1/2`, the
`m ∈ (u, 2u]` resonant at some `q ≤ Q` number at most the sum over `q ≤ Q` of the
one-denominator bound.

Evaluated, the sum is `(0.882 u^{2/3})(2Qδ/ε_{2u}) + (0.882 u^{2/3})(Q(Q+1)/2)` plus
the `+2` remainders, which is the note's Lemma 3; it is left as a sum here so that the
Gauss evaluation is the caller's arithmetic rather than a hypothesis of this bound. -/
theorem resonance_count_le {u Q : ℕ} (hu : 10 ^ 6 ≤ u) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    (#{m ∈ Finset.Ioc u (2 * u) | ResonantUpTo Q δ m} : ℝ) ≤
      ∑ q ∈ Finset.Icc 1 Q, (0.882 * (q : ℝ) * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
        (2 * δ / ((q : ℝ) * eps (2 * u)) + 1) := by
  have hcover : {m ∈ Finset.Ioc u (2 * u) | ResonantUpTo Q δ m} ⊆
      (Finset.Icc 1 Q).biUnion
        (fun q => {m ∈ Finset.Ioc u (2 * u) | Resonant q δ m}) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨q, hq1, hqQ, hres⟩ := hm.2
    exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_Icc.mpr ⟨hq1, hqQ⟩,
      Finset.mem_filter.mpr ⟨hm.1, hres⟩⟩
  have hb : (#{m ∈ Finset.Ioc u (2 * u) | ResonantUpTo Q δ m} : ℝ) ≤
      ∑ q ∈ Finset.Icc 1 Q, (#{m ∈ Finset.Ioc u (2 * u) | Resonant q δ m} : ℝ) := by
    have h1 : #{m ∈ Finset.Ioc u (2 * u) | ResonantUpTo Q δ m} ≤
        ∑ q ∈ Finset.Icc 1 Q, #{m ∈ Finset.Ioc u (2 * u) | Resonant q δ m} :=
      le_trans (Finset.card_le_card hcover) (Finset.card_biUnion_le)
    exact_mod_cast h1
  refine le_trans hb (Finset.sum_le_sum ?_)
  intro q hq
  exact resonance_count_one hu (Finset.mem_Icc.mp hq).1 hδ0 hδ

end FiberParity

end Problems.Juggler
