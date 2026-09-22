import Problems.Juggler.CollatzPadic
import Problems.Juggler.CollatzMoments
import Problems.Collatz.PreimageCertificate12
import Problems.Collatz.PreimageBalance
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import BTCalculus.SublinearCountingMass

/-!
Exact manuscript-facing forms for Paper E: the series code, finite-source
frequencies, real exponents, and sums on the actual family of stopping words.
-/
noncomputable section

namespace Problems.Juggler.PaperECompletion

open Filter Finset CollatzBridge CollatzPadic CollatzMoments PaperBCertificates
open scoped Topology

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem itinerary_append_last (n k : ℕ) :
    itinerary n (k+1) = itinerary n k ++ [bit (floorPower^[k] n)] := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [itinerary_succ, ih, itinerary_succ, List.cons_append, Function.iterate_succ_apply]

def codeRemainder (n k : ℕ) : ℚ_[2] :=
  2^k * (code (floorPower^[k] n) : ℚ_[2]) / 3^(oddCount (itinerary n k))

/-- One term at each time, zero on even sources; the denominator counts earlier odds. -/
def seriesTerm (n k : ℕ) : ℚ_[2] :=
  if (floorPower^[k] n) % 2 = 0 then 0 else
    2^k / 3^(oddCount (itinerary n k)+1)

theorem seriesTerm_eq_remainder_sub (n k : ℕ) :
    seriesTerm n k = codeRemainder n k - codeRemainder n (k+1) := by
  have hs := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) (code_step (floorPower^[k] n))
  rcases Nat.mod_two_eq_zero_or_one (floorPower^[k] n) with hn | hn
  · simp only [if_pos hn, PadicInt.coe_mul] at hs
    change (2 : ℚ_[2]) * (code (floorPower (floorPower^[k] n)) : ℚ_[2]) =
      (code (floorPower^[k] n) : ℚ_[2]) at hs
    simp only [seriesTerm, hn, if_true, codeRemainder, itinerary_append_last,
      oddCount_append, bit_even hn, oddCount, add_zero, Function.iterate_succ_apply',
      pow_succ]
    field_simp
    linear_combination (2^k) * hs
  · simp only [if_neg (by omega : ¬(floorPower^[k] n) % 2 = 0),
      PadicInt.coe_mul, PadicInt.coe_sub, PadicInt.coe_one] at hs
    change (2 : ℚ_[2]) * (code (floorPower (floorPower^[k] n)) : ℚ_[2]) =
      3 * (code (floorPower^[k] n) : ℚ_[2]) - 1 at hs
    simp only [seriesTerm, hn, Nat.one_ne_zero, if_false, codeRemainder, itinerary_append_last,
      oddCount_append, bit_odd hn, oddCount, zero_add,
      Function.iterate_succ_apply', pow_succ]
    field_simp
    linear_combination hs

theorem norm_three : ‖(3 : ℚ_[2])‖ = 1 :=
  (Padic.norm_natCast_eq_one_iff (p := 2) (n := 3)).mpr (by decide)

theorem norm_two : ‖(2 : ℚ_[2])‖ = (1/2 : ℝ) := by
  simpa using (Padic.norm_p (p := 2))

theorem codeRemainder_norm (n k : ℕ) :
    ‖codeRemainder n k‖ ≤ (1/2 : ℝ)^k := by
  simp only [codeRemainder, norm_div, norm_mul, norm_pow, norm_three, one_pow,
    div_one, norm_two]
  simpa only [one_div, mul_one, ← PadicInt.norm_def] using
    mul_le_mul_of_nonneg_left (PadicInt.norm_le_one (code (floorPower^[k] n)))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) k)

theorem codeRemainder_tendsto (n : ℕ) :
    Tendsto (codeRemainder n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (codeRemainder_norm n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem seriesTerm_norm (n k : ℕ) : ‖seriesTerm n k‖ ≤ (1/2 : ℝ)^k := by
  unfold seriesTerm
  split_ifs
  · simp
  · simp [norm_div, norm_pow, norm_three, norm_two]

theorem series_partial_sum (n d : ℕ) :
    ∑ k ∈ range d, seriesTerm n k = (code n : ℚ_[2]) - codeRemainder n d := by
  induction d with
  | zero => simp [codeRemainder, itinerary]
  | succ d ih =>
    rw [sum_range_succ, ih, seriesTerm_eq_remainder_sub]
    ring

/-- The infinite series in (2.4), with zero terms inserted at even times. -/
theorem code_hasSum_series (n : ℕ) :
    HasSum (seriesTerm n) (code n : ℚ_[2]) := by
  have hnorm : Summable (fun k => ‖seriesTerm n k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (seriesTerm_norm n)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm).mpr
  simp only [series_partial_sum]
  simpa using tendsto_const_nhds.sub (codeRemainder_tendsto n)

/-- The exponent index is exactly the number of earlier odd times. -/
theorem oddCount_eq_earlier_odds (n k : ℕ) :
    oddCount (itinerary n k) =
      ((range k).filter (fun i => (floorPower^[i] n) % 2 = 1)).card := by
  induction k with
  | zero => simp [itinerary_zero]
  | succ k ih =>
    rw [itinerary_append_last, oddCount_append, range_add_one, filter_insert]
    rcases Nat.mod_two_eq_zero_or_one (floorPower^[k] n) with hn | hn
    · simp [hn, bit_even hn, oddCount, ih]
    · simp [hn, bit_odd hn, oddCount, ih]

def OddTime (n : ℕ) := {k : ℕ // (floorPower^[k] n) % 2 = 1}

/-- Formula (2.4) over precisely the odd times, including a finite or empty family. -/
theorem code_hasSum_odd_times (n : ℕ) :
    HasSum (fun k : OddTime n =>
      (2 : ℚ_[2])^k.val /
        3^(((range k.val).filter (fun i => (floorPower^[i] n) % 2 = 1)).card+1))
      (code n : ℚ_[2]) := by
  have hs : Function.support (seriesTerm n) ⊆ {k | (floorPower^[k] n) % 2 = 1} := by
    intro k hk
    by_contra h
    change ¬(floorPower^[k] n) % 2 = 1 at h
    have hzero : (floorPower^[k] n) % 2 = 0 := by omega
    exact hk (by simp [seriesTerm, hzero])
  have h := (hasSum_subtype_iff_of_support_subset hs).mpr (code_hasSum_series n)
  change HasSum (fun k : OddTime n => seriesTerm n k.val) (code n : ℚ_[2]) at h
  have he : (fun k : OddTime n => seriesTerm n k.val) =
      (fun k : OddTime n => (2 : ℚ_[2])^k.val /
        3^(((range k.val).filter (fun i => (floorPower^[i] n) % 2 = 1)).card+1)) := by
    funext k
    simp [seriesTerm, k.property, oddCount_eq_earlier_odds]
  rw [he] at h
  exact h

def wordFrequency (N : ℕ) (w : List Branch) : ℝ :=
  (((Icc 1 N).filter (fun n => itinerary n w.length = w)).card : ℝ) / N

def codeFrequency (N r d : ℕ) : ℝ :=
  (((Icc 1 N).filter (fun n =>
    PadicInt.toZModPow d (code n) = -(r : ZMod (2^d)))).card : ℝ) / N

theorem frequency_eq (N r d : ℕ) :
    codeFrequency N r d = wordFrequency N (parityWord r d) := by
  unfold codeFrequency wordFrequency
  rw [parityWord_length, code_cylinder_eq]

theorem frequency_limit_iff (r d : ℕ) (L : ℝ) :
    Tendsto (fun N => codeFrequency N r d) atTop (𝓝 L) ↔
      Tendsto (fun N => wordFrequency N (parityWord r d)) atTop (𝓝 L) := by
  simp only [frequency_eq]

/-- Corollary 2.3, with all finite words and every associated residue. -/
theorem all_frequency_limits_iff (d : ℕ) (L : ℝ) :
    (∀ w : List Branch, w.length = d →
      Tendsto (fun N => wordFrequency N w) atTop (𝓝 L)) ↔
    (∀ r : ℕ, Tendsto (fun N => codeFrequency N r d) atTop (𝓝 L)) := by
  constructor
  · intro h r
    exact (frequency_limit_iff r d L).mpr (h _ (parityWord_length r d))
  · intro h w hw
    obtain ⟨r, _, hr⟩ := exists_residue_of_word hw
    simpa [hr] using (frequency_limit_iff r d L).mp (h r)

/-- Convert the exact integer inequality without approximating its exponent. -/
theorem real_exponent_of_integer_powers (X N : ℕ) (h : X^21 ≤ N^25) :
    (X : ℝ) ^ ((21 : ℝ)/25) ≤ (N : ℝ) := by
  have hr : (X : ℝ)^21 ≤ (N : ℝ)^25 := by exact_mod_cast h
  have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (X : ℝ)^21) hr
    (by norm_num : (0 : ℝ) ≤ (25 : ℝ)⁻¹)
  have hleft : ((X : ℝ)^(21 : ℕ))^((25 : ℝ)⁻¹) = (X : ℝ)^((21 : ℝ)/25) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ X)]
    norm_num
  have hright : ((N : ℝ)^(25 : ℕ))^((25 : ℝ)⁻¹) = (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
    norm_num
  exact hleft ▸ hright ▸ hh

theorem ancestor_density_real {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (X : ℝ)^((21 : ℝ)/25) ≤ Problems.Collatz.PreimageDensity.ancestorCount a X := by
  obtain ⟨X₀, h⟩ := Problems.Collatz.PreimageCertificate12.ancestor_density_21_25 ha ha3
  exact ⟨X₀, fun X hX => real_exponent_of_integer_powers X _ (h X hX)⟩

/-- The logarithmic exponent printed after Theorem 6.1. -/
theorem log_exponent_of_power_ceiling {μ : ℝ} (hμ : 0 < μ)
    (h : μ^5000 < (2 : ℝ)^99) :
    50 * (Real.log μ / Real.log 2) < (99 : ℝ)/100 := by
  have hh := Real.log_lt_log (pow_pos hμ 5000) h
  rw [Real.log_pow, Real.log_pow] at hh
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ htwo).mpr
  norm_num at hh ⊢
  nlinarith

/-- The fixed-grid hypotheses imply the manuscript's logarithmic ceiling. -/
theorem certificate_log_ceiling (k : ℕ) {μ : ℝ} (hμ : 0 < μ) (hlinear : μ^50 ≤ 2)
    {w : Fin (3^k * 3) → ℝ} (hw : ∀ i, 0 < w i)
    (hr : Problems.Collatz.PreimageBalance.Rows (by positivity : 0 < 3^k)
        (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w ∨
      Problems.Collatz.PreimageBalance.RowsPlus (by positivity : 0 < 3^k)
        (μ^(-100 : ℤ)) (μ^(29 : ℤ)) (μ^(-21 : ℤ)) w) :
    50 * (Real.log μ / Real.log 2) < (99 : ℝ)/100 :=
  log_exponent_of_power_ceiling hμ
    (Problems.Collatz.PreimageBalance.certificate_power_ceiling k hμ hlinear hw hr)

/-- A finite complete binary prefix tree: every internal node has both children. -/
inductive FullPrefixTree where
  | leaf
  | split (evenTree oddTree : FullPrefixTree)

def FullPrefixTree.frontier : FullPrefixTree → Finset (List Branch)
  | .leaf => {[]}
  | .split l r => (l.frontier.image (Branch.even :: ·)) ∪
      (r.frontier.image (Branch.odd :: ·))

theorem prefix_frontiers_disjoint (l r : FullPrefixTree) :
    Disjoint (l.frontier.image (Branch.even :: ·))
      (r.frontier.image (Branch.odd :: ·)) := by
  apply disjoint_left.mpr
  intro w hw hv
  obtain ⟨u, _, rfl⟩ := mem_image.mp hw
  obtain ⟨v, _, hv⟩ := mem_image.mp hv
  cases hv

/-- Both identities (7.1) hold for every finite complete prefix tree. -/
theorem full_prefix_tree_masses (t : FullPrefixTree) :
    (∑ w ∈ t.frontier, fairWeight w) = 1 ∧
    (∑ w ∈ t.frontier, fairWeight w * multiplier w) = 1 := by
  induction t with
  | leaf => simp [FullPrefixTree.frontier, fairWeight, multiplier, oddCount]
  | split l r hl hr =>
    have himage (s : Finset (List Branch)) (b : Branch) (f : List Branch → ℝ) :
        ∑ w ∈ s.image (b :: ·), f w = ∑ w ∈ s, f (b :: w) :=
      sum_image (by intro _ _ _ _ h; exact (List.cons.inj h).2)
    simp only [FullPrefixTree.frontier, sum_union (prefix_frontiers_disjoint l r),
      himage]
    have he (w : List Branch) : fairWeight (.even :: w) = (1/2 : ℝ) * fairWeight w := by
      simp [fairWeight, pow_succ]
    have ho (w : List Branch) : fairWeight (.odd :: w) = (1/2 : ℝ) * fairWeight w := by
      simp [fairWeight, pow_succ]
    have hme (w : List Branch) :
        fairWeight (.even :: w) * multiplier (.even :: w) =
          (1/4 : ℝ) * (fairWeight w * multiplier w) := by
      simp [fairWeight, multiplier, oddCount, pow_succ]; ring
    have hmo (w : List Branch) :
        fairWeight (.odd :: w) * multiplier (.odd :: w) =
          (3/4 : ℝ) * (fairWeight w * multiplier w) := by
      simp [fairWeight, multiplier, oddCount, pow_succ]; ring
    constructor
    · simp only [he, ho, ← mul_sum, hl.1, hr.1]
      norm_num
    · simp only [hme, hmo, ← mul_sum, hl.2, hr.2]
      norm_num

def StoppingWord := {w : List Branch // IsMinimalCertificate w}

def stoppingEquiv :
    (Σ d : ℕ, ↥(minimalCertWords (d+1))) ≃ StoppingWord :=
  Equiv.ofBijective (fun v => ⟨v.2.val, (mem_filter.mp v.2.property).2⟩) (by
    constructor
    · intro ⟨d, u, hu⟩ ⟨e, v, hv⟩ heq
      have huv : u = v := congrArg Subtype.val heq
      have hd : u.length = d+1 := mem_allWords.mp (mem_filter.mp hu).1
      have he : v.length = e+1 := mem_allWords.mp (mem_filter.mp hv).1
      have hde : d = e := by have := congrArg List.length huv; omega
      subst e
      subst v
      rfl
    · intro ⟨w, hw⟩
      have hlen : w.length - 1 + 1 = w.length := by
        have := List.length_pos_iff.mpr hw.1
        omega
      refine ⟨⟨w.length-1, w, ?_⟩, rfl⟩
      exact mem_filter.mpr ⟨mem_allWords.mpr hlen.symm, hw⟩)

/-- Regrouping by length for any nonnegative stopping-word weight. -/
theorem stopping_hasSum {f : List Branch → ℝ} {a : ℝ}
    (hf : ∀ w, 0 ≤ f w)
    (ha : HasSum (fun d => ∑ w ∈ minimalCertWords (d+1), f w) a) :
    HasSum (fun w : StoppingWord => f w.val) a := by
  let F : (Σ d : ℕ, ↥(minimalCertWords (d+1))) → ℝ := fun v => f v.2.val
  have hfinite (d : ℕ) :
      HasSum (fun w : ↥(minimalCertWords (d+1)) => f w.val)
        (∑ w ∈ minimalCertWords (d+1), f w) := by
    simpa [sum_attach] using (hasSum_fintype (fun w : ↥(minimalCertWords (d+1)) => f w.val))
  have hs : Summable F := by
    apply (summable_sigma_of_nonneg (f := F) (fun v => hf v.2.val)).mpr
    refine ⟨fun d => (hfinite d).summable, ?_⟩
    have he : (fun d => ∑' w : ↥(minimalCertWords (d+1)), F ⟨d,w⟩) =
        (fun d => ∑ w ∈ minimalCertWords (d+1), f w) :=
      funext (fun d => (hfinite d).tsum_eq)
    rw [he]
    exact ha.summable
  have h : HasSum F a := ha.sigma_of_hasSum hfinite hs
  exact stoppingEquiv.hasSum_iff.mp h

/-- Proposition 7.2 in the manuscript's direct indexing by stopping words. -/
theorem stopping_word_masses :
    HasSum (fun w : StoppingWord => fairWeight w.val) 1 ∧
    Summable (fun w : StoppingWord => fairWeight w.val * multiplier w.val) ∧
    (∑' w : StoppingWord, fairWeight w.val * multiplier w.val) ≤ 3/4 := by
  have hf := stopping_hasSum (f := fairWeight) (fun w => by unfold fairWeight; positivity)
    (by simpa only [← certMass_eq_sum] using certificate_hasSum)
  have ht := stopping_hasSum (f := fun w => fairWeight w * multiplier w)
    (fun w => mul_nonneg (by unfold fairWeight; positivity) (multiplier_pos w).le)
    tilted_summable.hasSum
  refine ⟨hf, ht.summable, ?_⟩
  rw [ht.tsum_eq]
  exact stopped_moment_le

/-- Every entry of the rational-value table in Example 2.2, together with its collision. -/
theorem example22_code_table :
    (code 3 : ℚ_[2]) = 83/27 ∧ (code 5 : ℚ_[2]) = 37/9 ∧
    (code 11 : ℚ_[2]) = 17/3 ∧ (code 36 : ℚ_[2]) = 8 ∧
    (code 6 : ℚ_[2]) = 4 ∧ (code 2 : ℚ_[2]) = 2 ∧
    (code 1 : ℚ_[2]) = 1 ∧ code 4 = code 6 := by
  have h (n d : ℕ) (hd : floorPower^[d] n = 1) :
      (code n : ℚ_[2]) = (CollatzRational.codeAt n d : ℚ_[2]) := by
    rw [code_eq_terminatingCode ⟨d, hd⟩,
      CollatzRational.terminatingCode_eq_codeAt ⟨d, hd⟩ hd]
  have h3 := h 3 6 (by decide +kernel)
  have h5 := h 5 5 (by decide +kernel)
  have h11 := h 11 4 (by decide +kernel)
  have h36 := h 36 3 (by decide +kernel)
  have h6 := h 6 2 (by decide +kernel)
  have h2 := h 2 1 (by decide +kernel)
  have h1 := h 1 0 (by decide +kernel)
  norm_num [CollatzRational.codeAt, CollatzRational.pullbackWord,
    CollatzRational.pullback, itinerary, floorPower, bit] at h3 h5 h11 h36 h6 h2 h1
  exact ⟨h3, h5, h11, h36, h6, h2, h1, code_four.trans code_six.symm⟩

/-- The final assertion of Example 2.2 retains positivity and the actual ternary denominator. -/
theorem terminating_code_positive_ternary_denominator {n : ℕ} (hn : ReachesOne n) :
    ∃ q : ℚ, (code n : ℚ_[2]) = (q : ℚ_[2]) ∧ 0 < q ∧
      ∃ d : ℕ, floorPower^[d] n = 1 ∧ (q.den : ℤ) ∣ (3 : ℤ)^oddCount (itinerary n d) := by
  let d := Nat.find hn
  have hd : floorPower^[d] n = 1 := Nat.find_spec hn
  obtain ⟨hall, hpos, _⟩ := CollatzRational.terminating_bridge hn
  exact ⟨CollatzRational.terminatingCode n hn, code_eq_terminatingCode hn,
    hpos, d, hd, (hall d hd).2⟩

end Problems.Juggler.PaperECompletion
