import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Problems.Juggler.RateFreeDensity
import Problems.Juggler.FateContagion

namespace Problems.Juggler

open Finset

/-!
# The Chernoff count of bad words and the union bound of the Tao-type reduction

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Lemma 8.2 and the
exact skeleton of Theorem 8.3.

A word `w` of length `d` is `L`-*bad* if its exponent walk
`o_t(w) log₂ 3 - t` stays above `-L` at every prefix `1 ≤ t ≤ d`. Lemma 8.2
counts them: for `C ≥ 5`, `p_C = (1 - 1/C)/log₂ 3` and `d ≥ C L`, there are at
most `2^d · 2^{-e(C) L}` of them, `e(C) = C D(p_C ‖ 1/2)/log 2`. The engine is
the Markov tilt `weight_markov` of `RateFreeDensity` on the constant weight,
whose generating function is `(1 + x)^d`; at the tilt `x = p/(1-p)` the bound
`(1 + x)^d x^{-pd}` is `exp(d h(p))` with `h` the binary entropy, and
`h(p) ≤ log 2` is Gibbs' inequality.

Theorem 8.3 then reads: an odd start in `(y, 2y]` that does not reach `1` has
an itinerary that fails the envelope comparison of Lemma 8.1 at every prefix,
so it lies in the cylinder of a bad word; the failures are covered by the bad
cylinders, and a bound on every bad cylinder (the paper's hypothesis
`H(C, A)`) bounds the failures by the number of bad words times that bound.
Everything here is exact; the asymptotic form of Theorem 8.3
(`y (log y)^{-e(C)+ε}`) is the paper's substitution of `d = ⌈C L(y)⌉` and
of the hypothesis's explicit bound, and is not restated. Nothing here bounds a
cylinder, and nothing here is a halt theorem.
-/

/-! ### The constant weight and the count of words with many odd letters -/

theorem weightGen_one (x : ℝ) (d : ℕ) : weightGen (fun _ => (1 : ℝ)) x d = (1 + x) ^ d := by
  induction d with
  | zero => simp [weightGen_zero]
  | succ d ih =>
      rw [weightGen_succ]
      have hterm : ∀ w ∈ allWords d,
          (1 : ℝ) * x ^ oddCount w + 1 * x ^ (oddCount w + 1) =
            (1 + x) * ((fun _ => (1 : ℝ)) w * x ^ oddCount w) := by
        intro w _
        simp only [one_mul]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      change (1 + x) * weightGen (fun _ => (1 : ℝ)) x d = _
      rw [ih]
      ring

/-- Markov tilt on the constant weight: at most `(1 + x)^d / x^k` words of
length `d` have at least `k` odd letters, for any `x ≥ 1`. -/
theorem count_oddCount_ge_le (d k : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    (#{w ∈ allWords d | k ≤ oddCount w} : ℝ) ≤ (1 + x) ^ d / x ^ k := by
  have h := weight_markov (fun _ => (1 : ℝ)) x d k hx (fun _ => zero_le_one)
  rw [weightGen_one] at h
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- The same with a real threshold `p d` on the odd count and a real exponent. -/
theorem count_oddCount_ge_real_le (d : ℕ) (p x : ℝ) (hp : 0 ≤ p) (hx : 1 ≤ x) :
    (#{w ∈ allWords d | p * d ≤ oddCount w} : ℝ) ≤ (1 + x) ^ d / x ^ (p * d) := by
  classical
  have hpd : 0 ≤ p * d := by positivity
  have hfilt : {w ∈ allWords d | p * d ≤ oddCount w} =
      {w ∈ allWords d | ⌈p * d⌉₊ ≤ oddCount w} := by
    apply Finset.filter_congr
    intro w _
    exact (Nat.ceil_le).symm
  rw [hfilt]
  refine le_trans (count_oddCount_ge_le d ⌈p * d⌉₊ x hx) ?_
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hx0 _)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil _)

/-! ### Binary entropy, relative entropy to the fair coin, and the optimal tilt -/

/-- Binary entropy in nats, `h(p) = -p log p - (1-p) log (1-p)`. -/
noncomputable def entropyLog (p : ℝ) : ℝ := -(p * Real.log p) - (1 - p) * Real.log (1 - p)

/-- Relative entropy to the fair coin, `D(p ‖ 1/2) = log 2 - h(p)`. -/
noncomputable def klHalf (p : ℝ) : ℝ := Real.log 2 - entropyLog p

theorem klHalf_eq (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    klHalf p = p * Real.log (2 * p) + (1 - p) * Real.log (2 * (1 - p)) := by
  unfold klHalf entropyLog
  rw [Real.log_mul (by norm_num) hp0.ne', Real.log_mul (by norm_num) (by linarith)]
  ring

/-- Gibbs' inequality for the fair coin: `h(p) ≤ log 2`, i.e. `D(p ‖ 1/2) ≥ 0`. -/
theorem klHalf_nonneg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : 0 ≤ klHalf p := by
  have h1p : 0 < 1 - p := by linarith
  have ha : Real.log ((2 * p)⁻¹) ≤ (2 * p)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hb : Real.log ((2 * (1 - p))⁻¹) ≤ (2 * (1 - p))⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at ha hb
  have ha' : p * -Real.log (2 * p) ≤ p * ((2 * p)⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left ha hp0.le
  have hb' : (1 - p) * -Real.log (2 * (1 - p)) ≤ (1 - p) * ((2 * (1 - p))⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left hb h1p.le
  have hc : p * ((2 * p)⁻¹ - 1) + (1 - p) * ((2 * (1 - p))⁻¹ - 1) = 0 := by
    field_simp
    ring
  rw [klHalf_eq p hp0 hp1]
  linarith

/-- At the tilt `x = p/(1-p)`, `(1 + x)^d / x^{p d} = exp (d h(p))`. -/
theorem tilt_value (d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (1 + p / (1 - p)) ^ d / (p / (1 - p)) ^ (p * d) = Real.exp (d * entropyLog p) := by
  have h1p : 0 < 1 - p := by linarith
  have hx : 0 < p / (1 - p) := by positivity
  have h1x : 1 + p / (1 - p) = 1 / (1 - p) := by
    field_simp
    ring
  rw [h1x]
  have hA : (1 / (1 - p)) ^ d = Real.exp (d * (-Real.log (1 - p))) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), one_div, Real.log_inv]
    ring_nf
  have hB : (p / (1 - p)) ^ (p * d) = Real.exp (p * d * (Real.log p - Real.log (1 - p))) := by
    rw [Real.rpow_def_of_pos hx, Real.log_div hp0.ne' h1p.ne']
    ring_nf
  rw [hA, hB, ← Real.exp_sub]
  congr 1
  unfold entropyLog
  ring

/-- **Lemma 8.2, the count.** For `1/2 ≤ p < 1`, at most `exp (d h(p))` words of
length `d` have at least `p d` odd letters. -/
theorem count_oddCount_ge_le_exp (d : ℕ) (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p < 1) :
    (#{w ∈ allWords d | p * d ≤ oddCount w} : ℝ) ≤ Real.exp (d * entropyLog p) := by
  have hp0 : 0 < p := by linarith
  have h1p : 0 < 1 - p := by linarith
  have hx : 1 ≤ p / (1 - p) := by
    rw [le_div_iff₀ h1p]; linarith
  rw [← tilt_value d p hp0 hp1]
  exact count_oddCount_ge_real_le d p _ hp0.le hx

/-- The same in the paper's form `2^d exp(-d D(p ‖ 1/2))`. -/
theorem count_oddCount_ge_le_kl (d : ℕ) (p : ℝ) (hp : 1 / 2 ≤ p) (hp1 : p < 1) :
    (#{w ∈ allWords d | p * d ≤ oddCount w} : ℝ) ≤ 2 ^ d * Real.exp (-(d * klHalf p)) := by
  refine le_trans (count_oddCount_ge_le_exp d p hp hp1) (le_of_eq ?_)
  have h2 : (2 : ℝ) ^ d = Real.exp (d * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  rw [h2, ← Real.exp_add]
  congr 1
  unfold klHalf
  ring

/-! ### `L`-bad words -/

open scoped Classical

/-- `w` is `L`-bad: the exponent walk `o_t log₂ 3 - t` stays above `-L` at every
prefix `1 ≤ t ≤ |w|`. -/
def LBad (L : ℝ) (w : List Branch) : Prop :=
  ∀ t, 1 ≤ t → t ≤ w.length →
    -L < (oddCount (w.take t) : ℝ) * Real.logb 2 3 - t

/-- The paper's `p_C = (1 - 1/C)/log₂ 3`. -/
noncomputable def pC (C : ℝ) : ℝ := (1 - 1 / C) / Real.logb 2 3

/-- The paper's Chernoff exponent `e(C) = C D(p_C ‖ 1/2)/log 2`. -/
noncomputable def chernoffExponent (C : ℝ) : ℝ := C * klHalf (pC C) / Real.log 2

theorem one_lt_logb_two_three : 1 < Real.logb 2 3 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  norm_num

/-- `log₂ 3 ≤ 8/5`, i.e. `3^5 ≤ 2^8`. -/
theorem logb_two_three_le : Real.logb 2 3 ≤ 8 / 5 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
  have : (2 : ℝ) ^ ((8 : ℝ) / 5) = ((2 : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [this]
  have h3 : (3 : ℝ) = ((3 : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h3]
  apply Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)

theorem pC_lt_one (C : ℝ) (hC : 5 ≤ C) : pC C < 1 := by
  unfold pC
  have hl := one_lt_logb_two_three
  rw [div_lt_one (by linarith)]
  have : 0 < 1 / C := by positivity
  linarith

theorem half_le_pC (C : ℝ) (hC : 5 ≤ C) : 1 / 2 ≤ pC C := by
  unfold pC
  have hl := logb_two_three_le
  have hl0 : 0 < Real.logb 2 3 := by linarith [one_lt_logb_two_three]
  rw [le_div_iff₀ hl0]
  have : 1 / C ≤ 1 / 5 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

/-- An `L`-bad word of length `d ≥ C L` has at least `p_C d` odd letters. -/
theorem LBad_oddCount_ge {L C : ℝ} {d : ℕ} (hC : 0 < C) (hd : C * L ≤ d) (hd1 : 1 ≤ d)
    {w : List Branch} (hw : w ∈ allWords d) (hbad : LBad L w) :
    pC C * d ≤ oddCount w := by
  have hlen : w.length = d := mem_allWords.mp hw
  have h := hbad d hd1 (by omega)
  rw [List.take_of_length_le (by omega)] at h
  have hl0 : 0 < Real.logb 2 3 := by linarith [one_lt_logb_two_three]
  unfold pC
  rw [div_mul_eq_mul_div, div_le_iff₀ hl0]
  have hLd : L ≤ d / C := by
    rw [le_div_iff₀ hC]; linarith
  have : (1 - 1 / C) * d = d - d / C := by ring
  rw [this]
  linarith

/-- **Lemma 8.2 (Chernoff), exact form.** For `C ≥ 5` and `d ≥ C L` with `d ≥ 1`, the
number of `L`-bad words of length `d` is at most `2^d · 2^{-e(C) L}`. -/
theorem LBad_count_le (L C : ℝ) (d : ℕ) (hC : 5 ≤ C) (hd : C * L ≤ d) (hd1 : 1 ≤ d) :
    (#{w ∈ allWords d | LBad L w} : ℝ) ≤ 2 ^ d * (2 : ℝ) ^ (-(chernoffExponent C * L)) := by
  classical
  have hC0 : 0 < C := by linarith
  have hp := half_le_pC C hC
  have hp1 := pC_lt_one C hC
  have hsub : {w ∈ allWords d | LBad L w} ⊆ {w ∈ allWords d | pC C * d ≤ oddCount w} := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, LBad_oddCount_ge hC0 hd hd1 hw.1 hw.2⟩
  have h1 : (#{w ∈ allWords d | LBad L w} : ℝ) ≤
      #{w ∈ allWords d | pC C * d ≤ oddCount w} := by
    exact_mod_cast Finset.card_le_card hsub
  refine le_trans h1 (le_trans (count_oddCount_ge_le_kl d (pC C) hp hp1) ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hkl := klHalf_nonneg (pC C) (by linarith) hp1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  unfold chernoffExponent
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : Real.log 2 * -(C * klHalf (pC C) / Real.log 2 * L) = -(C * L * klHalf (pC C)) := by
    field_simp
  rw [this]
  have : C * L * klHalf (pC C) ≤ d * klHalf (pC C) :=
    mul_le_mul_of_nonneg_right hd hkl
  linarith

/-! ### Theorem 8.3: the failures are covered by the bad cylinders -/

/-- The cylinder of `w` at scale `y`: odd starts in `(y, 2y]` whose realized
itinerary of length `d` is `w`. -/
noncomputable def cylinder (y d : ℕ) (w : List Branch) : Finset ℕ :=
  {n ∈ Ioc y (2 * y) | n % 2 = 1 ∧ itinerary n d = w}

/-- The odd starts in `(y, 2y]` that do not reach `1`. -/
noncomputable def oddFailures (y : ℕ) : Finset ℕ :=
  {n ∈ Ioc y (2 * y) | n % 2 = 1 ∧ ¬ReachesOne n}

/-- `w` fails the envelope comparison against the floor `N₀` at the scale `Y`
at every prefix: `N₀^{2^t} < Y^{3^{o_t}}` for all `t ≤ |w|`. This is the integer
form of `L(Y)`-badness. -/
def EnvelopeBad (N₀ Y : ℕ) (w : List Branch) : Prop :=
  ∀ t, t ≤ w.length → N₀ ^ (2 ^ t) < Y ^ (3 ^ oddCount (w.take t))

/-- **Lemma 8.1 in covering form.** If every start up to `N₀` reaches `1`, an odd
failure in `(y, 2y]` lies in the cylinder of an envelope-bad word. -/
theorem oddFailures_subset_bad_cylinders {N₀ : ℕ}
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y d : ℕ) :
    oddFailures y ⊆
      ({w ∈ allWords d | EnvelopeBad N₀ (2 * y) w}).biUnion (cylinder y d) := by
  classical
  intro n hn
  simp only [oddFailures, Finset.mem_filter, Finset.mem_Ioc] at hn
  obtain ⟨⟨hyn, hn2y⟩, hodd, hfail⟩ := hn
  rw [Finset.mem_biUnion]
  refine ⟨itinerary n d, ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨itinerary_mem_allWords n d, ?_⟩
    intro t ht
    rw [itinerary_length] at ht
    rw [itinerary_take n d t ht]
    by_contra hle
    push Not at hle
    apply hfail
    refine reachesOne_of_itinerary_envelope hfloor (by omega) (le_trans ?_ hle)
    exact Nat.pow_le_pow_left hn2y _
  · unfold cylinder
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hyn, hn2y⟩, hodd, rfl⟩

/-- **Theorem 8.3, the union bound.** Under a floor `N₀` and a bound `M` on every
envelope-bad cylinder of depth `d`, the odd failures in `(y, 2y]` number at most
(the number of envelope-bad words) times `M`. -/
theorem oddFailures_card_le {N₀ : ℕ}
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y d M : ℕ)
    (hcyl : ∀ w ∈ allWords d, EnvelopeBad N₀ (2 * y) w → (cylinder y d w).card ≤ M) :
    (oddFailures y).card ≤ #{w ∈ allWords d | EnvelopeBad N₀ (2 * y) w} * M := by
  classical
  refine le_trans (Finset.card_le_card (oddFailures_subset_bad_cylinders hfloor y d)) ?_
  refine le_trans Finset.card_biUnion_le ?_
  have := Finset.sum_le_card_nsmul {w ∈ allWords d | EnvelopeBad N₀ (2 * y) w}
    (fun w => (cylinder y d w).card) M (fun w hw => by
      rw [Finset.mem_filter] at hw
      exact hcyl w hw.1 hw.2)
  simpa [smul_eq_mul] using this

/-- Envelope-badness at the scale `Y` is `L`-badness with `L = log₂ (log Y / log N₀)`,
for `N₀ ≥ 2` and `Y ≥ 2`. -/
theorem LBad_of_envelopeBad {N₀ Y : ℕ} (hN : 2 ≤ N₀) (hY : 2 ≤ Y) {w : List Branch}
    (h : EnvelopeBad N₀ Y w) :
    LBad (Real.logb 2 (Real.log Y / Real.log N₀)) w := by
  intro t ht1 ht
  have hlt := h t ht
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast hN)
  have hlogY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
  -- take logarithms: `2^t log N₀ < 3^o log Y`
  have hcast : ((N₀ : ℝ)) ^ (2 ^ t) < ((Y : ℝ)) ^ (3 ^ oddCount (w.take t)) := by
    exact_mod_cast hlt
  have hlog := Real.log_lt_log (by positivity) hcast
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  -- hence `log N₀ / log Y < 3^o / 2^t`, and `log₂` of both sides
  set o := oddCount (w.take t)
  have hratio : Real.log N₀ / Real.log Y < (3 : ℝ) ^ o / (2 : ℝ) ^ t := by
    rw [div_lt_div_iff₀ hlogY (by positivity)]
    linarith
  have hlogb := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hratio
  have hR : Real.logb 2 ((3 : ℝ) ^ o / (2 : ℝ) ^ t) = o * Real.logb 2 3 - t := by
    rw [Real.logb_div (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    ring
  have hL1 : Real.logb 2 (Real.log N₀ / Real.log Y) =
      Real.logb 2 (Real.log N₀) - Real.logb 2 (Real.log Y) :=
    Real.logb_div hlogN.ne' hlogY.ne'
  have hL2 : Real.logb 2 (Real.log Y / Real.log N₀) =
      Real.logb 2 (Real.log Y) - Real.logb 2 (Real.log N₀) :=
    Real.logb_div hlogY.ne' hlogN.ne'
  rw [hR, hL1] at hlogb
  rw [hL2]
  linarith

/-- **Theorem 8.3, exact composite.** Floor `N₀ ≥ 2`, scale `y ≥ 1`, depth `d ≥ 1` with
`d ≥ C L`, `L = log₂ (log 2y / log N₀)`, `C ≥ 5`; if every `L`-bad cylinder of depth `d`
holds at most `M` starts, then the odd failures in `(y, 2y]` number at most
`2^d · 2^{-e(C) L} · M`. -/
theorem oddFailures_card_le_chernoff {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y d : ℕ) (hy : 1 ≤ y) (hd1 : 1 ≤ d)
    (C M : ℝ) (hC : 5 ≤ C) (hM : 0 ≤ M)
    (hd : C * Real.logb 2 (Real.log (2 * y) / Real.log N₀) ≤ d)
    (hcyl : ∀ w ∈ allWords d, LBad (Real.logb 2 (Real.log (2 * y) / Real.log N₀)) w →
      ((cylinder y d w).card : ℝ) ≤ M) :
    ((oddFailures y).card : ℝ) ≤
      2 ^ d * (2 : ℝ) ^ (-(chernoffExponent C *
        Real.logb 2 (Real.log (2 * y) / Real.log N₀))) * M := by
  classical
  set L := Real.logb 2 (Real.log (2 * y) / Real.log N₀) with hL
  -- envelope-bad words are `L`-bad, so the covering counts `L`-bad words
  have hsub : oddFailures y ⊆ ({w ∈ allWords d | LBad L w}).biUnion (cylinder y d) := by
    refine le_trans (oddFailures_subset_bad_cylinders hfloor y d) ?_
    apply Finset.biUnion_subset_biUnion_of_subset_left
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, ?_⟩
    have := LBad_of_envelopeBad hN (by omega) hw.2
    push_cast at this
    exact this
  have h1 : ((oddFailures y).card : ℝ) ≤ ∑ w ∈ {w ∈ allWords d | LBad L w},
      ((cylinder y d w).card : ℝ) := by
    have := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := {w ∈ allWords d | LBad L w}) (t := cylinder y d)
    exact_mod_cast le_trans this h2
  have h2 : ∑ w ∈ {w ∈ allWords d | LBad L w}, ((cylinder y d w).card : ℝ) ≤
      #{w ∈ allWords d | LBad L w} * M := by
    have := Finset.sum_le_card_nsmul {w ∈ allWords d | LBad L w}
      (fun w => ((cylinder y d w).card : ℝ)) M (fun w hw => by
        rw [Finset.mem_filter] at hw
        exact hcyl w hw.1 hw.2)
    simpa [nsmul_eq_mul] using this
  refine le_trans h1 (le_trans h2 ?_)
  exact mul_le_mul_of_nonneg_right (LBad_count_le L C d hC hd hd1) hM

/-! ### Theorem 8.3 in the paper's variables: `Λ(y) = log 2y / log N₀`, `L(y) = log₂ Λ(y)`,
`d(y) = ⌈C L(y)⌉` -/

/-- `Λ(y) = log 2y / log N₀`. -/
noncomputable def scaleRatio (N₀ y : ℕ) : ℝ := Real.log (2 * y) / Real.log N₀

/-- The paper's `L(y) = log₂ (log 2y / log N₀)`. -/
noncomputable def scaleL (N₀ y : ℕ) : ℝ := Real.logb 2 (scaleRatio N₀ y)

/-- The paper's depth `d(y) = ⌈C L(y)⌉`. -/
noncomputable def depth (C : ℝ) (N₀ y : ℕ) : ℕ := ⌈C * scaleL N₀ y⌉₊

/-- Odd starts have first letter `O`: an `E`-rooted cylinder of positive depth is empty. -/
theorem cylinder_even_root_empty (y d : ℕ) (w : List Branch) (hd : 1 ≤ d)
    (hw : w.head? = some .even) : cylinder y d w = ∅ := by
  ext n
  simp only [cylinder, Finset.mem_filter, Finset.mem_Ioc, Finset.notMem_empty, iff_false]
  rintro ⟨_, hodd, hit⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [itinerary_succ, bit_odd hodd] at hit
  rw [← hit] at hw
  simp at hw

/-- **Theorem 8.3, explicit form.** Floor `N₀ ≥ 2`, scale `y ≥ 2`, `C ≥ 5`, depth
`d = ⌈C L(y)⌉ ≥ 1`. If every `O`-rooted `L(y)`-bad cylinder of depth `d` holds at most
`2^{-(d-1)} y/2 + y (log y)^{-A}` starts (the hypothesis `H(C, A)` at this `y`), then the odd
failures in `(y, 2y]` number at most `y Λ^{-e(C)} + 2 Λ^C y (log y)^{-A}`, `Λ = log 2y / log N₀`.
The paper's `(y/2) Λ^{-(e(C)-ε)}` for large `y` follows by absorbing the factor `2` into
`Λ^ε` and the second term into the first when `A > C + e(C)`; that absorption is not
formalized. -/
theorem oddFailures_card_le_explicit {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y : ℕ) (hy : 2 ≤ y)
    (C A : ℝ) (hC : 5 ≤ C) (hd1 : 1 ≤ depth C N₀ y)
    (hcyl : ∀ w ∈ allWords (depth C N₀ y), w.head? = some .odd → LBad (scaleL N₀ y) w →
      ((cylinder y (depth C N₀ y) w).card : ℝ) ≤
        2 ^ (-((depth C N₀ y : ℝ) - 1)) * y / 2 + y / Real.log y ^ A) :
    ((oddFailures y).card : ℝ) ≤
      y * scaleRatio N₀ y ^ (-chernoffExponent C) +
        2 * scaleRatio N₀ y ^ C * y / Real.log y ^ A := by
  classical
  set Λ := scaleRatio N₀ y with hΛ
  set L := scaleL N₀ y with hL
  set d := depth C N₀ y with hd
  set e := chernoffExponent C with he
  have hLdef : L = Real.logb 2 Λ := rfl
  have hddef : d = ⌈C * L⌉₊ := rfl
  have hy' : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogN : 0 < Real.log N₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N₀))
  have hlog2y : 0 < Real.log (2 * y) := Real.log_pos (by push_cast; linarith)
  have hΛpos : 0 < Λ := div_pos hlog2y hlogN
  have hC0 : 0 < C := by linarith
  have hCL : 0 < C * L := Nat.ceil_pos.mp hd1
  have hLpos : 0 < L := (mul_pos_iff_of_pos_left hC0).mp hCL
  have hΛ1 : 1 < Λ := by
    rw [hLdef] at hLpos
    exact (Real.logb_pos_iff (by norm_num) hΛpos).mp hLpos
  have hdle : C * L ≤ d := Nat.le_ceil _
  have hdlt : (d : ℝ) < C * L + 1 := Nat.ceil_lt_add_one hCL.le
  have h2L : (2 : ℝ) ^ L = Λ := by
    rw [hLdef]
    exact Real.rpow_logb (by norm_num) (by norm_num) hΛpos
  have he0 : 0 ≤ e := by
    rw [he]
    unfold chernoffExponent
    have := klHalf_nonneg (pC C) (by linarith [half_le_pC C hC]) (pC_lt_one C hC)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hpow_neg : (2 : ℝ) ^ (-(e * L)) = Λ ^ (-e) := by
    rw [show -(e * L) = L * (-e) by ring, Real.rpow_mul (by norm_num), h2L]
  have hpow_d : ((2 : ℝ) ^ d) ≤ 2 * Λ ^ C := by
    rw [← Real.rpow_natCast]
    calc (2 : ℝ) ^ (d : ℝ) ≤ (2 : ℝ) ^ (C * L + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hdlt.le
      _ = 2 ^ (C * L) * 2 := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
      _ = 2 * Λ ^ C := by
          rw [show C * L = L * C by ring, Real.rpow_mul (by norm_num), h2L]
          ring
  have hΛe : Λ ^ (-e) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛ1.le (by linarith)
  have hcancel : (2 : ℝ) ^ d * 2 ^ (-((d : ℝ) - 1)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num),
      show (d : ℝ) + -((d : ℝ) - 1) = 1 by ring, Real.rpow_one]
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hA : 0 < Real.log y ^ A := Real.rpow_pos_of_pos hlogy A
  set M : ℝ := 2 ^ (-((d : ℝ) - 1)) * y / 2 + y / Real.log y ^ A with hM
  have hM0 : 0 ≤ M := by positivity
  have hcyl' : ∀ w ∈ allWords d, LBad L w → ((cylinder y d w).card : ℝ) ≤ M := by
    intro w hw hbad
    have hlen : w.length = d := mem_allWords.mp hw
    cases w with
    | nil => simp at hlen; omega
    | cons b w' =>
        cases b with
        | odd => exact hcyl (.odd :: w') hw rfl hbad
        | even =>
            rw [cylinder_even_root_empty y d _ hd1 rfl]
            simpa using hM0
  have hmain := oddFailures_card_le_chernoff hN hfloor y d (by omega) hd1 C M hC hM0 hdle hcyl'
  have hyA : 0 ≤ (y : ℝ) / Real.log y ^ A := by positivity
  have hT : Λ ^ (-e) * (2 ^ d * y / Real.log y ^ A) ≤ 2 * Λ ^ C * y / Real.log y ^ A := by
    calc Λ ^ (-e) * (2 ^ d * y / Real.log y ^ A)
        = (Λ ^ (-e) * 2 ^ d) * (y / Real.log y ^ A) := by ring
      _ ≤ (1 * (2 * Λ ^ C)) * (y / Real.log y ^ A) := by
          apply mul_le_mul_of_nonneg_right _ hyA
          exact mul_le_mul hΛe hpow_d (by positivity) (by norm_num)
      _ = 2 * Λ ^ C * y / Real.log y ^ A := by ring
  calc ((oddFailures y).card : ℝ)
      ≤ 2 ^ d * (2 : ℝ) ^ (-(e * L)) * M := hmain
    _ = Λ ^ (-e) * (2 ^ d * 2 ^ (-((d : ℝ) - 1)) * y / 2 + 2 ^ d * y / Real.log y ^ A) := by
        rw [hpow_neg, hM]; ring
    _ = y * Λ ^ (-e) + Λ ^ (-e) * (2 ^ d * y / Real.log y ^ A) := by
        rw [hcancel]; ring
    _ ≤ y * Λ ^ (-e) + 2 * Λ ^ C * y / Real.log y ^ A := by linarith

end Problems.Juggler
