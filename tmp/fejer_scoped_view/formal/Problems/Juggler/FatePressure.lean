import Problems.Juggler.FateChernoff
import Problems.Juggler.LiveCountWeight

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The pressure form of the Tao-type bound

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Theorem 9.2, in exact form.

For a start `n ≤ N` that stays above the floor `N₀` for `d` steps (`liveTo N₀ n d`),
Lemma 8.1 says its itinerary fails the envelope comparison at every prefix, so it is
`L(N)`-bad with `L(N) = log₂ (log N / log N₀)`, and for `d ≥ C L(N)` it carries at least
`p_C d` odd letters. The *live pressure* `Σ_{n ≤ N live} x^{o_d(n)}` is the generating
function `weightGen` of the live weight of `LiveCountWeight`, so the Markov tilt
`weight_markov` bounds the live count by the pressure over `x^{p_C d}`. At the tilt
`x = p_C/(1-p_C)`, with `a_θ = (1 + x)/2`, the paper's hypothesis `P_θ(C)` reads
`pressure ≤ N a_θ^d E` (the paper's `E = e^{o(d)}`), and the live count is at most
`N exp(-d D(p_C ‖ 1/2)) E`: the exponent of Theorem 8.3, by `tilt_value`.

The starts are counted in `{1, …, N}` as in `LiveCountWeight`, where the paper counts
odd starts in `(y, 2y]`; the paper's `y (log y)^{-e(C)+ε}` is the substitution of
`d = ⌈C L⌉` and `E = e^{o(d)}`, not restated. Nothing here bounds a pressure sum, and
nothing here is a halt theorem.
-/

/-- The live pressure `Σ_{n ∈ {1,…,N} live to depth d} x^{o_d(n)}`, as the generating
function of the live weight. -/
noncomputable def livePressure (N₀ N : ℕ) (x : ℝ) (d : ℕ) : ℝ :=
  weightGen (liveWeight N₀ N) x d

/-- Markov tilt on the live weight: the live starts with at least `k` odd letters number
at most the pressure over `x^k`. -/
theorem live_count_le_pressure (N₀ N : ℕ) (x : ℝ) (hx : 1 ≤ x) (d k : ℕ) :
    (((Icc 1 N).filter (fun n => liveTo N₀ n d ∧ k ≤ oddCount (itinerary n d))).card : ℝ) ≤
      livePressure N₀ N x d / x ^ k := by
  have hsum : (((Icc 1 N).filter
        (fun n => liveTo N₀ n d ∧ k ≤ oddCount (itinerary n d))).card : ℝ) =
      ∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), liveWeight N₀ N w := by
    rw [liveCount_sum_oddCount, Nat.cast_sum]
    rfl
  rw [hsum]
  exact weight_markov (liveWeight N₀ N) x d k hx (liveWeight_nonneg N₀ N)

/-- **Lemma 8.1 for live starts.** A start `1 ≤ n ≤ N` that stays above `N₀ ≥ 2` for `d`
steps has an itinerary that fails the envelope comparison at the scale `N` at every
prefix. -/
theorem envelopeBad_of_liveTo {N₀ N n d : ℕ} (hnN : n ≤ N) (hlive : liveTo N₀ n d) :
    EnvelopeBad N₀ N (itinerary n d) := by
  intro t ht
  rw [itinerary_length] at ht
  rw [itinerary_take n d t ht]
  by_contra hle
  push Not at hle
  have hlt : N₀ < floorPower^[t] n := hlive t (by rw [mem_range]; omega)
  have hbound : floorPower^[t] n ≤ N₀ := by
    have h := iterate_le_of_envelope (follows_itinerary_self n t)
      (le_trans (Nat.pow_le_pow_left hnN _) (by rw [itinerary_length]; exact hle))
    rw [itinerary_length] at h
    exact h
  omega

/-- Hence it is `L(N)`-bad, `L(N) = log₂ (log N / log N₀)`. -/
theorem LBad_of_liveTo {N₀ N n d : ℕ} (hN : 2 ≤ N₀) (hNN : 2 ≤ N) (hnN : n ≤ N)
    (hlive : liveTo N₀ n d) :
    LBad (Real.logb 2 (Real.log N / Real.log N₀)) (itinerary n d) :=
  LBad_of_envelopeBad hN hNN (envelopeBad_of_liveTo hnN hlive)

/-- A live start at depth `d ≥ C L(N)` has at least `p_C d` odd letters. -/
theorem live_oddCount_ge {N₀ N n d : ℕ} (hN : 2 ≤ N₀) (hNN : 2 ≤ N) (hnN : n ≤ N)
    (hlive : liveTo N₀ n d) (C : ℝ) (hC : 0 < C) (hd1 : 1 ≤ d)
    (hd : C * Real.logb 2 (Real.log N / Real.log N₀) ≤ d) :
    pC C * d ≤ oddCount (itinerary n d) :=
  LBad_oddCount_ge hC hd hd1 (itinerary_mem_allWords n d) (LBad_of_liveTo hN hNN hnN hlive)

/-- **Theorem 9.2 (pressure form), exact.** Floor `N₀ ≥ 2`, scale `N ≥ 2`, `C ≥ 5`, depth
`d ≥ 1` with `d ≥ C L(N)`, tilt `x = p_C/(1-p_C)`, `a = (1 + x)/2`. If the live pressure
at depth `d` is at most `N a^d E`, then the starts in `{1, …, N}` that stay above `N₀`
for `d` steps number at most `N exp(-d D(p_C ‖ 1/2)) E`. -/
theorem live_count_le_of_pressure (N₀ N : ℕ) (hN : 2 ≤ N₀) (hNN : 2 ≤ N) (C : ℝ)
    (hC : 5 ≤ C) (d : ℕ) (hd1 : 1 ≤ d)
    (hd : C * Real.logb 2 (Real.log N / Real.log N₀) ≤ d) (E : ℝ)
    (hP : livePressure N₀ N (pC C / (1 - pC C)) d ≤
      N * ((1 + pC C / (1 - pC C)) / 2) ^ d * E) :
    (((Icc 1 N).filter (fun n => liveTo N₀ n d)).card : ℝ) ≤
      N * Real.exp (-(d * klHalf (pC C))) * E := by
  set p := pC C with hp
  have hp12 : 1 / 2 ≤ p := half_le_pC C hC
  have hp1 : p < 1 := pC_lt_one C hC
  have hp0 : 0 < p := by linarith
  have h1p : 0 < 1 - p := by linarith
  set x := p / (1 - p) with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ h1p]; linarith
  have hx0 : 0 < x := by linarith
  set k := ⌈p * d⌉₊ with hk
  -- the live starts have at least `p d`, hence `k`, odd letters
  have hsub : (Icc 1 N).filter (fun n => liveTo N₀ n d) ⊆
      (Icc 1 N).filter (fun n => liveTo N₀ n d ∧ k ≤ oddCount (itinerary n d)) := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    rw [mem_filter, mem_Icc]
    refine ⟨hn.1, hn.2, ?_⟩
    rw [hk, Nat.ceil_le]
    exact live_oddCount_ge hN hNN hn.1.2 hn.2 C (by linarith) hd1 hd
  have h1 : (((Icc 1 N).filter (fun n => liveTo N₀ n d)).card : ℝ) ≤
      livePressure N₀ N x d / x ^ k := by
    refine le_trans ?_ (live_count_le_pressure N₀ N x hx1 d k)
    exact_mod_cast card_le_card hsub
  -- `E ≥ 0`, because the pressure is a nonnegative sum
  have hpress : 0 ≤ livePressure N₀ N x d :=
    weightGen_nonneg _ x (liveWeight_nonneg N₀ N) hx0.le d
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ha : 0 < (1 + x) / 2 := by positivity
  have hE : 0 ≤ E := by
    by_contra hneg
    push Not at hneg
    have : N * ((1 + x) / 2) ^ d * E < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  -- `x^k ≥ x^{p d}`, so the bound with the real exponent is weaker
  have hxk : x ^ (p * d) ≤ x ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (Nat.le_ceil _)
  have hxpd : 0 < x ^ (p * d) := Real.rpow_pos_of_pos hx0 _
  have h2 : livePressure N₀ N x d / x ^ k ≤ N * ((1 + x) / 2) ^ d * E / x ^ (p * d) := by
    calc livePressure N₀ N x d / x ^ k ≤ livePressure N₀ N x d / x ^ (p * d) :=
          div_le_div_of_nonneg_left hpress hxpd hxk
      _ ≤ N * ((1 + x) / 2) ^ d * E / x ^ (p * d) :=
          div_le_div_of_nonneg_right hP hxpd.le
  -- the tilt value: `((1+x)/2)^d / x^{p d} = exp(-d D(p ‖ 1/2))`
  have htilt : ((1 + x) / 2) ^ d / x ^ (p * d) = Real.exp (-(d * klHalf p)) := by
    have h2d : ((1 + x) / 2) ^ d = (1 + x) ^ d / 2 ^ d := by rw [div_pow]
    have hlog2 : (2 : ℝ) ^ d = Real.exp (d * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
      ring_nf
    rw [h2d, div_div, mul_comm, ← div_div, tilt_value d p hp0 hp1, hlog2, ← Real.exp_sub]
    congr 1
    unfold klHalf
    ring
  calc (((Icc 1 N).filter (fun n => liveTo N₀ n d)).card : ℝ)
      ≤ livePressure N₀ N x d / x ^ k := h1
    _ ≤ N * ((1 + x) / 2) ^ d * E / x ^ (p * d) := h2
    _ = N * (((1 + x) / 2) ^ d / x ^ (p * d)) * E := by ring
    _ = N * Real.exp (-(d * klHalf p)) * E := by rw [htilt]

end Problems.Juggler
