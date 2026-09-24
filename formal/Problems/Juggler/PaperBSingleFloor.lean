/-
# Paper B, Theorem 3.1: the exact single-floor bridge

`docs/theory/juggler_parity_discrepancy_note.md`, Theorem 3.1. The printed
statement is an exponential-sum bound `S_O(N) = O(N^{5/6})`, then two counts.
This file is the exact half of that argument:

* `⌊n^{3/2}⌋ = Nat.sqrt(n^3)`, so the parity sign is the image parity;
* on odd starts, `S_O = M - 2 · #{word_2 = OO}`;
* `C_2 ∩ {1,…,N}` is the complement of that class, hence `N - #OO`;
* a bound `|S_O| ≤ E` moves to the two counts with error `E/2`, and the
  main terms sit within `1/4` of `N/4` and `3N/4`;
* the phase `g(r) = (1/2)(2r+1)^{3/2}` has second derivative
  `(3/2)(2r+1)^{-1/2}`, the input of the existing second-derivative test;
* at cutoff `H = Q^{1/6}` the classical block majorant is at most `3 Q^{5/6}`;
* one interval of length at most its left endpoint has an exponential-sum bound
  from the second-derivative test;
* `∑_{h=1}^H h^{-1/2} ≤ 2 √H`, the comparison a harmonic sum of those bounds needs.

The count `|S_O| = O(N^{5/6})` still needs an Erdős–Turán inequality whose main
term is `N/H`. The Fejér discrepancy in this repository has main term `N/√H`.
-/

import BTCalculus.SecondDerivative
import Problems.Juggler.Itinerary
import Problems.Juggler.MeanValues
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

namespace Problems.Juggler

namespace PaperBSingleFloor

open Finset Real

/-- Odd starts in `{1, …, N}`. -/
def oddStarts (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => n % 2 = 1)

/-- `ψ(n^{3/2})` as an integer sign: `+1` on an even image, `-1` on an odd one. -/
def imageSign (n : ℕ) : ℤ :=
  if Nat.sqrt (n ^ 3) % 2 = 0 then 1 else -1

/-- `S_O(N)`, summed over odd starts. -/
def singleFloorSum (N : ℕ) : ℤ := ∑ n ∈ oddStarts N, imageSign n

/-- `#{n ≤ N : word_2(n) = OO}`. -/
def ooCount (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n => itinerary n 2 = [.odd, .odd])).card

/-- `#(C_2 ∩ {1, …, N})`: starts whose length-two itinerary is not `OO`. -/
def c2Count (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n => itinerary n 2 ≠ [.odd, .odd])).card

/-- `⌊n^{3/2}⌋ = Nat.sqrt (n^3)`, written with `n^{3/2} = n √n`: the parity sign is the parity of an integer square root. -/
theorem floor_pow32 (n : ℕ) :
    ⌊(n : ℝ) * sqrt (n : ℝ)⌋ = ((Nat.sqrt (n ^ 3) : ℕ) : ℤ) := by
  have h : (n : ℝ) * sqrt (n : ℝ) = sqrt (((n ^ 3 : ℕ) : ℝ)) := by
    have hn : (0 : ℝ) ≤ n := by positivity
    push_cast
    rw [show (n : ℝ) ^ 3 = ((n : ℝ) * n) * n by ring, sqrt_mul (by positivity),
      sqrt_mul_self hn]
  rw [h]
  exact floor_real_sqrt_eq_nat_sqrt (a := n ^ 3)

/-- An even image `Nat.sqrt (n^3)` has sign `+1`. -/
theorem imageSign_even {n : ℕ} (h : Nat.sqrt (n ^ 3) % 2 = 0) : imageSign n = 1 := by
  simp [imageSign, h]

/-- An odd image `Nat.sqrt (n^3)` has sign `-1`. -/
theorem imageSign_odd {n : ℕ} (h : Nat.sqrt (n ^ 3) % 2 = 1) : imageSign n = -1 := by
  simp [imageSign, h]

/-- An odd start has word `OO` exactly when its image is odd. -/
theorem oo_iff_odd_image {n : ℕ} (hn : n % 2 = 1) :
    itinerary n 2 = [.odd, .odd] ↔ Nat.sqrt (n ^ 3) % 2 = 1 := by
  have hfp : floorPower n = Nat.sqrt (n ^ 3) := floorPower_odd_eq hn
  have hbit : bit n = .odd := by simp [bit, hn]
  simp only [itinerary, hbit, hfp, List.cons.injEq, true_and]
  simp [bit]

/-- The start `1` has word `OO`: `1` is a fixed point of the odd step. -/
theorem one_is_oo : itinerary 1 2 = [.odd, .odd] := by
  decide

/-- The `OO` count is the number of odd starts in `{1, …, N}` with odd image `Nat.sqrt (n^3)`; even starts never begin with `O`. -/
theorem ooCount_eq_odd_image (N : ℕ) :
    ooCount N =
      ((oddStarts N).filter (fun n => Nat.sqrt (n ^ 3) % 2 = 1)).card := by
  refine card_bij (fun n hn => n) ?_ ?_ ?_
  · intro n hn
    simp only [mem_filter, mem_Icc, oddStarts] at hn ⊢
    obtain ⟨⟨h1, hN⟩, hoo⟩ := hn
    have hodd : n % 2 = 1 := by
      have hcons : itinerary n 2 = bit n :: itinerary (floorPower n) 1 := by
        simp [itinerary]
      rw [hcons] at hoo
      simp [bit] at hoo
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · simp [h] at hoo
      · exact h
    exact ⟨⟨⟨h1, hN⟩, hodd⟩, (oo_iff_odd_image hodd).mp hoo⟩
  · intro a ha b hb hab
    exact hab
  · intro m hm
    simp only [mem_filter, oddStarts, mem_Icc] at hm
    obtain ⟨⟨⟨h1, hN⟩, hodd⟩, him⟩ := hm
    refine ⟨m, ?_, rfl⟩
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨h1, hN⟩, (oo_iff_odd_image hodd).mpr him⟩

/-- **The bridge.** `S_O = M - 2 · #OO`. -/
theorem singleFloor_bridge (N : ℕ) :
    singleFloorSum N = (oddStarts N).card - 2 * (ooCount N : ℤ) := by
  let evenImage := (oddStarts N).filter (fun n => Nat.sqrt (n ^ 3) % 2 = 0)
  let oddImage := (oddStarts N).filter (fun n => Nat.sqrt (n ^ 3) % 2 = 1)
  have hdisj : Disjoint evenImage oddImage := by
    rw [disjoint_left]
    intro n hn hm
    simp only [mem_filter, evenImage, oddImage] at hn hm
    omega
  have hunion : evenImage ∪ oddImage = oddStarts N := by
    ext n
    simp only [mem_union, mem_filter, evenImage, oddImage]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hn
      rcases Nat.mod_two_eq_zero_or_one (Nat.sqrt (n ^ 3)) with h | h
      · exact Or.inl ⟨hn, h⟩
      · exact Or.inr ⟨hn, h⟩
  have heven : ∀ n ∈ evenImage, imageSign n = 1 := by
    intro n hn
    exact imageSign_even (mem_filter.mp hn).2
  have hodd : ∀ n ∈ oddImage, imageSign n = -1 := by
    intro n hn
    exact imageSign_odd (mem_filter.mp hn).2
  have hsumE : ∑ n ∈ evenImage, imageSign n = evenImage.card := by
    rw [sum_congr rfl heven, sum_const, nsmul_one]
  have hsumO : ∑ n ∈ oddImage, imageSign n = -oddImage.card := by
    rw [sum_congr rfl hodd, sum_const]
    simp
  have hcard : evenImage.card + oddImage.card = (oddStarts N).card := by
    rw [← card_union_of_disjoint hdisj, hunion]
  have hoo : oddImage.card = ooCount N := (ooCount_eq_odd_image N).symm
  have hE : (evenImage.card : ℤ) = (oddStarts N).card - (ooCount N : ℤ) := by
    have hcast : (evenImage.card : ℤ) + (oddImage.card : ℤ) = (oddStarts N).card := by
      exact_mod_cast hcard
    rw [hoo] at hcast
    omega
  have hoddz : (oddImage.card : ℤ) = (ooCount N : ℤ) := by exact_mod_cast hoo
  rw [singleFloorSum]
  conv_lhs => rw [hunion.symm]
  rw [sum_union hdisj, hsumE, hsumO, hE, hoddz]
  ring

/-- The two length-two classes partition `{1, …, N}`. -/
theorem c2_compl (N : ℕ) : c2Count N + ooCount N = N := by
  have hdisj : Disjoint
      ((Icc 1 N).filter (fun n => itinerary n 2 ≠ [.odd, .odd]))
      ((Icc 1 N).filter (fun n => itinerary n 2 = [.odd, .odd])) := by
    rw [disjoint_left]
    intro n hn hm
    simp only [mem_filter] at hn hm
    exact hn.2 hm.2
  have hunion :
      ((Icc 1 N).filter (fun n => itinerary n 2 ≠ [.odd, .odd])) ∪
        ((Icc 1 N).filter (fun n => itinerary n 2 = [.odd, .odd])) = Icc 1 N := by
    ext n
    simp only [mem_union, mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hn
      by_cases h : itinerary n 2 = [.odd, .odd]
      · exact Or.inr ⟨hn, h⟩
      · exact Or.inl ⟨hn, h⟩
  have hcard := card_union_of_disjoint hdisj
  rw [hunion, Nat.card_Icc] at hcard
  simp only [c2Count, ooCount]
  omega

/-- `#(C_2 ∩ {1, …, N}) = N - #OO`, the complement form of `c2_compl`. -/
theorem c2Count_eq (N : ℕ) : c2Count N = N - ooCount N := by
  have h := c2_compl N
  omega

/-- A bound on `S_O` is a bound on the `OO` count about `M/2`. -/
theorem oo_count_of_sum (N : ℕ) {E : ℤ} (hE : |singleFloorSum N| ≤ E) :
    |(2 * (ooCount N : ℤ) - (oddStarts N).card : ℤ)| ≤ E := by
  rw [singleFloor_bridge] at hE
  have : (oddStarts N).card - 2 * (ooCount N : ℤ) = -((2 * (ooCount N : ℤ)) - (oddStarts N).card) := by
    omega
  rw [this, abs_neg] at hE
  exact hE

/-- Twice the certificate count is `2N - M + S_O`. -/
theorem c2_bridge (N : ℕ) :
    2 * (c2Count N : ℤ) =
      2 * (N : ℤ) - (oddStarts N).card + singleFloorSum N := by
  have hbridge := singleFloor_bridge N
  have hc2 := c2Count_eq N
  have hle : ooCount N ≤ N := by
    have h := c2_compl N
    omega
  omega

/-! ## The phase the second-derivative test consumes -/

/-- `g(r) = (1/2) (2r+1)^{3/2}`. -/
noncomputable def phaseG (r : ℝ) : ℝ := (1 / 2) * pow32 (2 * r + 1)

/-- The first derivative `g'(r) = (3/2) (2r+1)^{1/2}` wherever `2r+1 > 0`. -/
theorem hasDerivAt_phaseG {r : ℝ} (hr : 0 < 2 * r + 1) :
    HasDerivAt phaseG ((3 / 2) * sqrt (2 * r + 1)) r := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * t + 1) 2 r := by
    simpa using ((hasDerivAt_id r).const_mul 2).add_const 1
  have hpow := (hasDerivAt_pow32 hr).comp r hlin
  have h := hpow.const_mul (1 / 2)
  have hfun : (fun y => (1 / 2) * (pow32 ∘ fun t => 2 * t + 1) y) = phaseG := by
    funext t
    simp [phaseG]
  have hder : (1 / 2) * ((3 / 2) * sqrt (2 * r + 1) * 2) =
      (3 / 2) * sqrt (2 * r + 1) := by ring
  rw [hfun, hder] at h
  exact h

/-- The manuscript's second derivative: `g''(r) = (3/2) (2r+1)^{-1/2}`. -/
theorem hasDerivAt_phaseG' {r : ℝ} (hr : 0 < 2 * r + 1) :
    HasDerivAt (fun t => (3 / 2) * sqrt (2 * t + 1))
      ((3 / 2) / sqrt (2 * r + 1)) r := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * t + 1) 2 r := by
    simpa using ((hasDerivAt_id r).const_mul 2).add_const 1
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp r hlin
  have h := hs.const_mul (3 / 2)
  have hfun : (fun y => (3 / 2) * ((fun x => sqrt x) ∘ fun t => 2 * t + 1) y) =
      fun t => (3 / 2) * sqrt (2 * t + 1) := by
    funext t
    simp
  have hder : (3 / 2) * ((1 / (2 * sqrt (2 * r + 1))) * 2) =
      (3 / 2) / sqrt (2 * r + 1) := by
    have hsq : sqrt (2 * r + 1) ≠ 0 := ne_of_gt (sqrt_pos.mpr hr)
    field_simp [hsq]
  rw [hfun, hder] at h
  exact h

/-! ## Cutoff arithmetic: `H = Q^{1/6}` turns the block majorant into `O(Q^{5/6})` -/

/-- For `Q ≥ 1` and `H = Q^{1/6}`, the block majorant `Q/H + H^{1/2} Q^{3/4} + Q^{1/4}` is at most `3 Q^{5/6}`. -/
theorem dyadic_cutoff {Q : ℝ} (hQ : 1 ≤ Q) :
    Q / Q ^ (1 / 6 : ℝ) + (Q ^ (1 / 6 : ℝ)) ^ (1 / 2 : ℝ) * Q ^ (3 / 4 : ℝ)
        + Q ^ (1 / 4 : ℝ) ≤
      3 * Q ^ (5 / 6 : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have h1 : Q / Q ^ (1 / 6 : ℝ) = Q ^ (5 / 6 : ℝ) := by
    calc
      Q / Q ^ (1 / 6 : ℝ) = Q ^ (1 : ℝ) * Q ^ (-(1 / 6 : ℝ)) := by
        rw [Real.rpow_one, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hQ0)]
      _ = Q ^ ((1 : ℝ) + -(1 / 6)) := (Real.rpow_add hQ0 1 (-(1 / 6))).symm
      _ = Q ^ (5 / 6 : ℝ) := by ring_nf
  have h2 : (Q ^ (1 / 6 : ℝ)) ^ (1 / 2 : ℝ) * Q ^ (3 / 4 : ℝ) = Q ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hQ0), ← Real.rpow_add hQ0]
    norm_num
  have h3 : Q ^ (1 / 4 : ℝ) ≤ Q ^ (5 / 6 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hQ
    norm_num
  linarith [h1, h2, h3]

/-! ## One dyadic block of the second-derivative test

On an interval of length at most its left endpoint, `h · g''` varies by at most
a factor two. The existing test then bounds one exponential sum. Summing blocks
and passing through Erdős–Turán are not done here. -/

open BTCalculus.SecondDerivative BTCalculus.WeylDifferencing

/-- On `[a, a+N]` with `1 ≤ a` and `N ≤ a`, the curvature `h · g''(x)` lies between `λ = h (3/2) (2(a+N)+1)^{-1/2}` and `2λ`, the two-sided hypothesis of the second-derivative test. -/
theorem block_curvature {h N : ℕ} {a x : ℝ}
    (ha : (1 : ℝ) ≤ a) (hN : (N : ℝ) ≤ a) (hh : 1 ≤ h)
    (hx : x ∈ Set.Icc a (a + N)) :
    let lam := (h : ℝ) * (3 / 2) / sqrt (2 * (a + N) + 1)
    lam ≤ (h : ℝ) * ((3 / 2) / sqrt (2 * x + 1)) ∧
      (h : ℝ) * ((3 / 2) / sqrt (2 * x + 1)) ≤ 2 * lam := by
  intro lam
  have hx1 : 0 < 2 * x + 1 := by linarith [ha, hx.1]
  have ha1 : 0 < 2 * a + 1 := by linarith
  have hN1 : 0 < 2 * (a + N) + 1 := by linarith
  have hlo : 2 * a + 1 ≤ 2 * x + 1 := by linarith [hx.1]
  have hhi : 2 * x + 1 ≤ 2 * (a + N) + 1 := by linarith [hx.2]
  have hsq : 2 * (a + N) + 1 ≤ 4 * (2 * a + 1) := by nlinarith
  have hsqrt := sqrt_le_sqrt hsq
  have hfour : sqrt (4 * (2 * a + 1)) = 2 * sqrt (2 * a + 1) := by
    rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show sqrt (4 : ℝ) = 2 by norm_num]
  have hratio : sqrt (2 * (a + N) + 1) ≤ 2 * sqrt (2 * a + 1) := by
    simpa [hfour] using hsqrt
  have hpos : 0 < (h : ℝ) * (3 / 2) := by positivity
  have hmin : lam ≤ (h : ℝ) * ((3 / 2) / sqrt (2 * x + 1)) := by
    dsimp [lam]
    have hden : sqrt (2 * x + 1) ≤ sqrt (2 * (a + N) + 1) := sqrt_le_sqrt hhi
    have hinv : 1 / sqrt (2 * (a + N) + 1) ≤ 1 / sqrt (2 * x + 1) := by
      apply one_div_le_one_div_of_le
      · exact sqrt_pos.mpr hx1
      · exact hden
    have := mul_le_mul_of_nonneg_left hinv hpos.le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hmax : (h : ℝ) * ((3 / 2) / sqrt (2 * x + 1)) ≤
      (h : ℝ) * ((3 / 2) / sqrt (2 * a + 1)) := by
    have hden : sqrt (2 * a + 1) ≤ sqrt (2 * x + 1) := sqrt_le_sqrt hlo
    have hinv : 1 / sqrt (2 * x + 1) ≤ 1 / sqrt (2 * a + 1) := by
      apply one_div_le_one_div_of_le
      · exact sqrt_pos.mpr ha1
      · exact hden
    have := mul_le_mul_of_nonneg_left hinv hpos.le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have htwice : (h : ℝ) * ((3 / 2) / sqrt (2 * a + 1)) ≤ 2 * lam := by
    dsimp [lam]
    have hinv : 1 / sqrt (2 * a + 1) ≤ 2 / sqrt (2 * (a + N) + 1) := by
      rw [div_le_div_iff₀ (sqrt_pos.mpr ha1) (sqrt_pos.mpr hN1)]
      nlinarith [hratio, sq_nonneg (sqrt (2 * (a + N) + 1) - 2 * sqrt (2 * a + 1))]
    have := mul_le_mul_of_nonneg_left hinv hpos.le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  exact ⟨hmin, hmax.trans htwice⟩

/-- One block: length at most the left endpoint, frequency `h ≥ 1`. -/
theorem block_exponential_sum {h N : ℕ} {a : ℝ}
    (ha : (1 : ℝ) ≤ a) (hN : (N : ℝ) ≤ a) (hh : 1 ≤ h) :
    ‖∑ n ∈ range N, phase ((h : ℝ) * phaseG (a + n))‖ ≤
      8 * (N : ℝ) * sqrt ((h : ℝ) * (3 / 2) / sqrt (2 * (a + N) + 1)) +
        8 / sqrt ((h : ℝ) * (3 / 2) / sqrt (2 * (a + N) + 1)) := by
  let lam := (h : ℝ) * (3 / 2) / sqrt (2 * (a + N) + 1)
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity
  have hbound := second_derivative_sum_bound
    (fun t => (h : ℝ) * phaseG t)
    (fun t => (h : ℝ) * ((3 / 2) * sqrt (2 * t + 1)))
    (fun t => (h : ℝ) * ((3 / 2) / sqrt (2 * t + 1)))
    a N (lam := lam) (C := 2) hlam (by norm_num)
    (fun x hx => by
      have hx1 : 0 < 2 * x + 1 := by linarith [ha, hx.1]
      simpa using (hasDerivAt_phaseG hx1).const_mul (h : ℝ))
    (fun x hx => by
      have hx1 : 0 < 2 * x + 1 := by linarith [ha, hx.1]
      simpa using (hasDerivAt_phaseG' hx1).const_mul (h : ℝ))
    (fun x hx => block_curvature ha hN hh hx)
  simpa [lam, show (4 : ℝ) * 2 = 8 by norm_num] using hbound

/-- `∑_{h=1}^H h^{-1/2} ≤ 2 √H`. This is the sum that turns `h^{-1/2}` mode bounds into `H^{1/2}`. -/
theorem sum_inv_sqrt (H : ℕ) :
    ∑ h ∈ Finset.Icc 1 H, (h : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * sqrt (H : ℝ) := by
  induction H with
  | zero => simp
  | succ H ih =>
    by_cases hH : H = 0
    · simp [hH]
    · have hle1 : 1 ≤ H + 1 := by omega
      rw [sum_Icc_succ_top hle1]
      have hstep : ((H + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
          2 * sqrt ((H + 1 : ℕ) : ℝ) - 2 * sqrt (H : ℝ) := by
        have hcast : (H : ℝ) ≤ (H + 1 : ℕ) := by exact_mod_cast Nat.le_succ H
        have hsqrt_le : sqrt (H : ℝ) ≤ sqrt ((H + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt hcast
        have hden_pos : 0 < sqrt ((H + 1 : ℕ) : ℝ) + sqrt (H : ℝ) := by positivity
        have hdiff : (sqrt ((H + 1 : ℕ) : ℝ) - sqrt (H : ℝ)) *
            (sqrt ((H + 1 : ℕ) : ℝ) + sqrt (H : ℝ)) = 1 := by
          calc
            (sqrt ((H + 1 : ℕ) : ℝ) - sqrt (H : ℝ)) *
                (sqrt ((H + 1 : ℕ) : ℝ) + sqrt (H : ℝ))
              = sqrt ((H + 1 : ℕ) : ℝ) ^ 2 - sqrt (H : ℝ) ^ 2 := by ring
            _ = ((H + 1 : ℕ) : ℝ) - (H : ℝ) := by
              rw [sq_sqrt (by positivity), sq_sqrt (by positivity)]
            _ = 1 := by push_cast; ring
        have hden : sqrt ((H + 1 : ℕ) : ℝ) + sqrt (H : ℝ) ≤
            2 * sqrt ((H + 1 : ℕ) : ℝ) := by linarith
        have hpow : ((H + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
            1 / sqrt ((H + 1 : ℕ) : ℝ) := by
          rw [Real.rpow_neg (by positivity), one_div, Real.sqrt_eq_rpow]
          norm_num
        rw [hpow]
        have hgap : 2 * sqrt ((H + 1 : ℕ) : ℝ) - 2 * sqrt (H : ℝ) =
            2 / (sqrt ((H + 1 : ℕ) : ℝ) + sqrt (H : ℝ)) := by
          have hsub : 2 * sqrt ((H + 1 : ℕ) : ℝ) - 2 * sqrt (H : ℝ) =
              2 * (sqrt ((H + 1 : ℕ) : ℝ) - sqrt (H : ℝ)) := by ring
          rw [hsub, eq_div_iff hden_pos.ne']
          linear_combination 2 * hdiff
        rw [hgap]
        have hinv : 1 / (2 * sqrt ((H + 1 : ℕ) : ℝ)) ≤
            1 / (sqrt ((H + 1 : ℕ) : ℝ) + sqrt (H : ℝ)) :=
          one_div_le_one_div_of_le hden_pos hden
        calc
          1 / sqrt ((H + 1 : ℕ) : ℝ)
              = 2 * (1 / (2 * sqrt ((H + 1 : ℕ) : ℝ))) := by ring
          _ ≤ 2 * (1 / (sqrt ((H + 1 : ℕ) : ℝ) + sqrt (H : ℝ))) :=
            mul_le_mul_of_nonneg_left hinv (by norm_num)
          _ = 2 / (sqrt ((H + 1 : ℕ) : ℝ) + sqrt (H : ℝ)) := by ring
      linarith

end PaperBSingleFloor

end Problems.Juggler
