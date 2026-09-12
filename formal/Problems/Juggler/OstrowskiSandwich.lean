import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Problems.Juggler

/-!
# Ostrowski sandwich for θ = log(3/2)/log 3

Paper A Section 5.5 decomposes hug-itinerary prefixes into blocks of
convergent denominators of `θ = log(3/2)/log 3` and applies
Denjoy–Koksma per block. The convergent data are certified there by
an interval continued fraction on a big-integer sandwich.

This file certifies that arithmetic:

* the two big-integer power inequalities
  `3^10781274 < 2^17087915` and `2^16785921 < 3^10590737`
  (`theta_sandwich_upper`, `theta_sandwich_lower`), both checked by the
  kernel through `norm_num` rather than by the compiled runtime, so the
  sandwich that carries the whole certification rests on the kernel alone;
* the resulting real sandwich
  `6195184/16785921 < θ < 6306641/17087915`
  (`lower_lt_walkTheta`, `walkTheta_lt_upper`);
* both rational endpoints have continued-fraction quotients starting
  `[2, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1]`, with further quotients
  remaining (`cf_lower_prefix`, `cf_upper_prefix`,
  `cf_lower_continues`, `cf_upper_continues`);
* the standard convergent recurrence on those quotients produces the
  denominator list
  `1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508, 125743, 176251`
  (`theta_convergent_denominators`);
* the greedy Ostrowski digit scan of Paper A Theorem 5.8: every
  window length `50508 ≤ L < 301994` decomposes into certified
  blocks with digit sum at most `37` (`window_digit_scan`,
  `window_digit_cap`), attained at `L = 275632`
  (`window_digit_max`);
* the convergent quality behind Theorem 5.7's Denjoy–Koksma
  application: numerators (`theta_convergent_numerators`),
  unimodularity (`theta_convergents_unimodular`), coprimality
  (`theta_convergents_coprime`), the approximation quality
  `|θ − p/q| < 1/q²` for all thirteen certified pairs
  (`theta_convergent_quality`), and the block-permutation fact
  (`residue_mul_bijective`, `theta_block_permutations`).

The bridge from the shared endpoint prefix to the continued fraction
of `θ` itself is the classical cylinder-interval fact (KNOWN); it is
used as prose in Paper A and is not re-proved here. Denjoy–Koksma's
variation-versus-integral inequality is likewise KNOWN — its
laboratory-specific hypotheses (block quality and permutation) are
certified above. Not a cycle obstruction and not a halt theorem.
-/

set_option exponentiation.threshold 20000000 in
/-- Upper side of the sandwich: `3^10781274 < 2^17087915`,
hence `log 2 / log 3 > 10781274 / 17087915`.

Proved by `norm_num`, so the comparison is checked by the kernel rather than by the
compiled runtime: these two inequalities carry the whole Ostrowski certification, and
`Nat` literal arithmetic is GMP-backed in the kernel, so the five-million-digit
comparison costs well under a second. Only the exponent threshold is raised, and only
for this declaration: it gates whether the power is evaluated at all, whereas
`maxRecDepth` is not consulted on this route. -/
theorem theta_sandwich_upper : (3 : ℕ) ^ 10781274 < 2 ^ 17087915 := by
  norm_num

set_option exponentiation.threshold 20000000 in
/-- Lower side of the sandwich: `2^16785921 < 3^10590737`,
hence `log 2 / log 3 < 10590737 / 16785921`.  Kernel-checked, as above. -/
theorem theta_sandwich_lower : (2 : ℕ) ^ 16785921 < 3 ^ 10590737 := by
  norm_num

/-- The rotation number of the hug walk in Paper A Section 5:
`θ = log(3/2)/log 3`. -/
noncomputable def walkTheta : ℝ := Real.log (3 / 2) / Real.log 3

/-- Real form of the lower sandwich: `6195184/16785921 < θ`. -/
theorem lower_lt_walkTheta : (6195184 : ℝ) / 16785921 < walkTheta := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have key : (16785921 : ℝ) * Real.log 2 < 10590737 * Real.log 3 := by
    have hc : ((2 : ℝ)) ^ (16785921 : ℕ) < (3 : ℝ) ^ (10590737 : ℕ) := by
      exact_mod_cast theta_sandwich_lower
    have hlt := Real.log_lt_log (by positivity) hc
    simpa [Real.log_pow] using hlt
  rw [walkTheta, Real.log_div (by norm_num) (by norm_num),
    div_lt_div_iff₀ (by norm_num) hlog3]
  nlinarith [key]

/-- Real form of the upper sandwich: `θ < 6306641/17087915`. -/
theorem walkTheta_lt_upper : walkTheta < (6306641 : ℝ) / 17087915 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have key : (10781274 : ℝ) * Real.log 3 < 17087915 * Real.log 2 := by
    have hc : ((3 : ℝ)) ^ (10781274 : ℕ) < (2 : ℝ) ^ (17087915 : ℕ) := by
      exact_mod_cast theta_sandwich_upper
    have hlt := Real.log_lt_log (by positivity) hc
    simpa [Real.log_pow] using hlt
  rw [walkTheta, Real.log_div (by norm_num) (by norm_num),
    div_lt_div_iff₀ hlog3 (by norm_num)]
  nlinarith [key]

/-- Continued-fraction quotients of the fraction `p/q ∈ (0,1)` by
Euclid, most significant first, fuel-bounded: the first quotient of
`p/q` is `⌊q/p⌋` and the tail is the expansion of `(q mod p)/p`. -/
def cfQuotients : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | _ + 1, _, 0 => []
  | fuel + 1, q, p + 1 => (q / (p + 1)) :: cfQuotients fuel (p + 1) (q % (p + 1))

/-- The certified quotient prefix of `θ` after the leading zero:
`θ = [0; 2, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, …]`. -/
def thetaQuotients : List ℕ := [2, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1]

/-- The lower endpoint opens with the certified quotients. -/
theorem cf_lower_prefix :
    (cfQuotients 64 16785921 6195184).take 12 = thetaQuotients := by
  decide +kernel

/-- The upper endpoint opens with the certified quotients. -/
theorem cf_upper_prefix :
    (cfQuotients 64 17087915 6306641).take 12 = thetaQuotients := by
  decide +kernel

/-- The lower endpoint's expansion continues past the shared prefix. -/
theorem cf_lower_continues :
    12 < (cfQuotients 64 16785921 6195184).length := by
  decide +kernel

/-- The upper endpoint's expansion continues past the shared prefix. -/
theorem cf_upper_continues :
    12 < (cfQuotients 64 17087915 6306641).length := by
  decide +kernel

/-- Convergent denominators from a quotient list by the standard
recurrence `q_n = a_n q_{n-1} + q_{n-2}`, with `q_{-1} = 0` and
`q_0 = 1` prepended to the output. -/
def convergentDenoms (as : List ℕ) : List ℕ :=
  (as.foldl
    (fun (st : ℕ × ℕ × List ℕ) a =>
      let next := a * st.2.1 + st.1
      (st.2.1, next, st.2.2 ++ [next]))
    (0, 1, [1])).2.2

/-- The certified quotients produce exactly the block-denominator
list used by Paper A Theorem 5.7 and the window digit caps of
Theorem 5.8. -/
theorem theta_convergent_denominators :
    convergentDenoms thetaQuotients =
      [1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508, 125743, 176251] := by
  decide +kernel

/-- The window endpoint `q₁₃ = 301994 = 1·176251 + 125743`, the next
denominator after the certified list. -/
theorem theta_window_endpoint : 176251 + 125743 = 301994 := by norm_num

/-!
## The window digit scan (Paper A Theorem 5.8, arithmetic core)

Theorem 5.8 controls the Denjoy–Koksma budget on the window
`50508 ≤ L < 301994` by the greedy Ostrowski digit sum `s(L)` over
the certified denominators. The scan below certifies both the
decomposition identity `L = Σ bⱼ qⱼ` and the exact cap
`s(L) ≤ 37` for every length in the window, replacing the
previously computational scan. The Denjoy–Koksma comparison that
turns `s(L)` into a charge bound stays analytic (KNOWN, prose).
-/

/-- The certified denominators, largest block first, ending in `1`
so the greedy remainder is always exhausted. -/
def thetaDenomsDesc : List ℕ :=
  [176251, 125743, 50508, 24727, 1054, 485, 84, 65, 19, 8, 3, 2, 1]

/-- Greedy Ostrowski digits of `L`: peel the largest certified
denominator repeatedly, most significant digit first. -/
def greedyDigits (L : ℕ) : List ℕ :=
  (thetaDenomsDesc.foldl
    (fun (st : ℕ × List ℕ) q => (st.1 % q, st.2 ++ [st.1 / q]))
    (L, [])).2

/-- The greedy digit sum `s(L) = Σ bⱼ`. -/
def greedyDigitSum (L : ℕ) : ℕ := (greedyDigits L).sum

/-- Reconstruction `Σ bⱼ qⱼ` of the greedy decomposition. -/
def greedyReconstruct (L : ℕ) : ℕ :=
  (((greedyDigits L).zip thetaDenomsDesc).map fun p => p.1 * p.2).sum

/-- **Reconstruction is structural, and universal.**  The fold peels `L / q` and keeps
`L % q` at each of the thirteen levels, so `Σ bⱼ qⱼ` telescopes back to `L` by the division
algorithm — for every `L`, with no window hypothesis.  This half of the old scan never
needed one. -/
theorem greedy_reconstruct_all (L : ℕ) : greedyReconstruct L = L := by
  simp [greedyReconstruct, greedyDigits, thetaDenomsDesc]
  omega

/-- **Window digit scan**: for every `L` in the window `[50508, 301994)`, the greedy digit
sum is at most `37`.  This is the one thing here that is genuinely a scan: the structural
cap of `OstrowskiNumeration` gives `47`, and `37` is the sharper constant measured on the
window.  Reconstruction, which the scan used to re-certify alongside it, is
`greedy_reconstruct_all` and holds everywhere. -/
theorem window_digit_scan :
    ((List.range' 50508 251486).all fun L =>
      decide (greedyDigitSum L ≤ 37)) = true := by
  native_decide

/-- The cap `37` is attained, at `L = 275632`. -/
theorem window_digit_max : greedyDigitSum 275632 = 37 := by decide +kernel

/-- Pointwise form of the scan: any window length decomposes
greedily into certified blocks with digit sum at most `37`. -/
theorem window_digit_cap {L : ℕ} (h1 : 50508 ≤ L) (h2 : L < 301994) :
    greedyReconstruct L = L ∧ greedyDigitSum L ≤ 37 := by
  refine ⟨greedy_reconstruct_all L, ?_⟩
  have hall := List.all_eq_true.mp window_digit_scan L
    (List.mem_range'_1.mpr ⟨h1, by omega⟩)
  exact of_decide_eq_true hall

/-!
## Convergent quality (the Denjoy–Koksma hypothesis)

Theorem 5.7 applies Denjoy–Koksma per certified block. The DK
hypothesis is that each block length is the denominator of a *good*
rational approximation: `|θ − p/q| < 1/q²`. This section certifies
that quality, and the block-permutation fact it feeds, from the
sandwich bounds — so of Theorem 5.7 only the classical
variation-versus-integral inequality itself remains prose (KNOWN).
-/

/-- Convergent numerators from a quotient list by the standard
recurrence `p_n = a_n p_{n-1} + p_{n-2}`, with `p_{-1} = 1` and
`p_0 = 0` prepended to the output. -/
def convergentNums (as : List ℕ) : List ℕ :=
  (as.foldl
    (fun (st : ℕ × ℕ × List ℕ) a =>
      let next := a * st.2.1 + st.1
      (st.2.1, next, st.2.2 ++ [next]))
    (1, 0, [0])).2.2

/-- The certified quotients produce the numerator list matching
`theta_convergent_denominators`. -/
theorem theta_convergent_numerators :
    convergentNums thetaQuotients =
      [0, 1, 1, 3, 7, 24, 31, 179, 389, 9126, 18641, 46408, 65049] := by
  decide +kernel

/-- The certified convergent pairs `(p_j, q_j)` of `θ`. -/
def thetaConvergents : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (1, 3), (3, 8), (7, 19), (24, 65), (31, 84),
   (179, 485), (389, 1054), (9126, 24727), (18641, 50508),
   (46408, 125743), (65049, 176251)]

/-- The pair list is exactly the zipped numerator/denominator
recurrences. -/
theorem thetaConvergents_eq_zip :
    thetaConvergents =
      (convergentNums thetaQuotients).zip
        (convergentDenoms thetaQuotients) := by
  decide +kernel

/-- Unimodularity of consecutive certified pairs:
`p_{j+1} q_j − p_j q_{j+1} = (−1)^j`. -/
theorem theta_convergents_unimodular :
    ∀ i < 12,
      ((thetaConvergents[i + 1]!).1 * (thetaConvergents[i]!).2 : ℤ) -
        (thetaConvergents[i]!).1 * (thetaConvergents[i + 1]!).2 =
          (-1) ^ i := by
  decide +kernel

/-- Every certified pair is coprime. -/
theorem theta_convergents_coprime :
    ∀ pq ∈ thetaConvergents, Nat.Coprime pq.1 pq.2 := by
  decide

/-- **Convergent quality** (the Denjoy–Koksma hypothesis for the
certified blocks): every certified convergent approximates `θ` to
within `1/q²`, certified against the sandwich bounds. -/
theorem theta_convergent_quality :
    ∀ pq ∈ thetaConvergents,
      |walkTheta - (pq.1 : ℝ) / pq.2| < 1 / (pq.2 : ℝ) ^ 2 := by
  have hlo := lower_lt_walkTheta
  have hhi := walkTheta_lt_upper
  intro pq hpq
  fin_cases hpq <;>
  · rw [abs_sub_lt_iff]
    constructor
    · exact lt_of_lt_of_le (sub_lt_sub_right hhi _) (by norm_num)
    · exact lt_of_lt_of_le (sub_lt_sub_left hlo _) (by norm_num)

/-!
The next θ-convergent `(p₁₃, q₁₃) = (111457, 301994)` is *not* appended
to `thetaConvergents`: that list has thirteen pairs, and the `fin_cases`
/ `decide` proofs above are written against it.  The pair is named
separately so the printed half-open window `[50508, q₁₄)` can reuse
`block_envelope` without restating the certified list.
-/

/-- The θ-convergent at `q₁₃`.  Complementary to FanLaw's
`(190537, 301994)`: `301994 − 111457 = 190537`. -/
def q13Convergent : ℕ × ℕ := (111457, 301994)

theorem q13_coprime : Nat.Coprime q13Convergent.1 q13Convergent.2 := by
  decide

/-- Quality of `(p₁₃, q₁₃)` against the same sandwich as
`theta_convergent_quality`. -/
theorem q13_convergent_quality :
    |walkTheta - (q13Convergent.1 : ℝ) / q13Convergent.2|
      < 1 / (q13Convergent.2 : ℝ) ^ 2 := by
  have hlo := lower_lt_walkTheta
  have hhi := walkTheta_lt_upper
  unfold q13Convergent
  rw [abs_sub_lt_iff]
  constructor
  · exact lt_of_lt_of_le (sub_lt_sub_right hhi _) (by norm_num)
  · exact lt_of_lt_of_le (sub_lt_sub_left hlo _) (by norm_num)

/-- Denjoy–Koksma block hypothesis at `q₁₃`. -/
theorem q13_block_hypothesis :
    0 < q13Convergent.2 ∧ Nat.Coprime q13Convergent.1 q13Convergent.2 ∧
      |walkTheta - (q13Convergent.1 : ℝ) / q13Convergent.2|
        ≤ 1 / (q13Convergent.2 : ℝ) ^ 2 :=
  ⟨by norm_num [q13Convergent], q13_coprime, le_of_lt q13_convergent_quality⟩

/-- Multiplication by a coprime residue permutes `ZMod q` — the
block-permutation fact behind Denjoy–Koksma: the `q` rotation steps
of one certified block visit the `q` grid cells bijectively. -/
theorem residue_mul_bijective (q p : ℕ) (h : Nat.Coprime p q) :
    Function.Bijective (fun i : ZMod q => (p : ZMod q) * i) :=
  (ZMod.unitOfCoprime p h).mulLeft_bijective

/-- Instance for every certified block. -/
theorem theta_block_permutations :
    ∀ pq ∈ thetaConvergents,
      Function.Bijective
        (fun i : ZMod pq.2 => ((pq.1 : ℕ) : ZMod pq.2) * i) :=
  fun pq hpq =>
    residue_mul_bijective pq.2 pq.1 (theta_convergents_coprime pq hpq)

/-!
### The grid-cell reading of the block permutation is false

`theta_block_permutations` says that `i ↦ p·i` permutes `ZMod q`, which is true and is about
*residues*.  Section 5.5 of Paper A described that as "the `q` rotation steps of one block
permute the `q` grid cells", which is about *cells* and is false: the orbit point `k θ` sits
within `1/q` of the grid point `(kp mod q)/q`, and when `θ < p/q` it sits just below, so its
cell is `(kp mod q) − 1` — except at `k = 0`, where `fract 0 = 0` keeps cell `0`.  The two
collide at the `k` with `kp ≡ 1 (mod q)`, and cell `q−1` is left empty.

It fails for seven of the thirteen certified blocks: every one with `θ < p/q`, which is every
even-indexed convergent.  The smallest is `q = 8`, `p = 3`, witnessed below at `k = 0` and
`k = 3` (and indeed `3·3 = 9 ≡ 1 mod 8`).

Denjoy–Koksma itself is unaffected — it is true, and its standard proof runs through Koksma's
inequality and the discrepancy bound `q·D_q ≤ 1` at a convergent denominator, not through a
cell permutation.  What is refuted is the bridge Paper A described, not the theorem.
-/

/-- `1/3 < θ`, from the certified lower sandwich. -/
theorem theta_gt_third : (1:ℝ)/3 < walkTheta := by
  have h := lower_lt_walkTheta
  have : (1:ℝ)/3 < (6195184 : ℝ) / 16785921 := by norm_num
  linarith

/-- `θ < 3/8`, from the certified upper sandwich. -/
theorem theta_lt_three_eighths : walkTheta < (3:ℝ)/8 := by
  have h := walkTheta_lt_upper
  have : (6306641 : ℝ) / 17087915 < (3:ℝ)/8 := by norm_num
  linarith

/-- **The grid cells are not permuted.**  At the certified block `q = 8`, `p = 3`, the orbit
points `k = 0` and `k = 3` fall in the same cell `[0, 1/8)`, so `k ↦ ⌊q · fract (k θ)⌋` is not
injective on `{0, …, 7}`.  Only `1/3 < θ < 3/8` is used, both from the sandwich. -/
theorem grid_cells_collide_at_eight :
    ⌊(8:ℝ) * Int.fract (3 * walkTheta)⌋ = ⌊(8:ℝ) * Int.fract ((0:ℕ) * walkTheta)⌋ := by
  have hlo := theta_gt_third
  have hhi := theta_lt_three_eighths
  have hfloor : ⌊3 * walkTheta⌋ = 1 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  have hfract : Int.fract (3 * walkTheta) = 3 * walkTheta - 1 := by
    rw [Int.fract, hfloor]; norm_num
  rw [hfract]
  norm_num [Int.fract]
  constructor <;> linarith

end Problems.Juggler
