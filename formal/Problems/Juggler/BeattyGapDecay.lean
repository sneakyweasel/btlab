import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Truncating a three-halves sequence

Positive lengths comparable to `n^(-3/2)` have truncated total length
comparable to the cube root of the truncation threshold. An integral-test
tail bound and a finite initial block give both inequalities.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Finset MeasureTheory

/-- An explicit upper bound on the tail of the model three-halves series. -/
theorem three_halves_tail_le {N : ℕ} (hN : 0 < N) :
    ∑' n : ℕ, ((n : ℝ)+N+1)^(-3/2 : ℝ) ≤ 2*(N : ℝ)^(-1/2 : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x^(-3/2 : ℝ)) N
    (fun x hx y hy hxy => Real.rpow_le_rpow_of_nonpos (hNR.trans_le hx) hxy (by norm_num))
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hNR)
    (fun x hx => Real.rpow_nonneg (hNR.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-3/2 : ℝ) < -1) hNR] at h
  norm_num at h ⊢
  simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm] using h

/-- For every threshold in `(0,1]`, a summable positive sequence with
two-sided three-halves bounds has truncated sum of cube-root order.
The constants are explicit in the supplied gap bounds. -/
theorem truncated_sum_three_halves_bounds {w : ℕ → ℝ} {a b : ℝ}
    (hw : Summable w) (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ n : ℕ, a*((n : ℝ)+1)^(-3/2 : ℝ) ≤ w n)
    (hhi : ∀ n : ℕ, w n ≤ b*((n : ℝ)+1)^(-3/2 : ℝ))
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (min a 1/2)*t^(1/3 : ℝ) ≤ ∑' n, min (w n) t ∧
    (∑' n, min (w n) t) ≤ (2+2*b)*t^(1/3 : ℝ) := by
  have hn (n : ℕ) : 0 ≤ w n := (by positivity : 0 ≤ a*((n : ℝ)+1)^(-3/2 : ℝ)).trans (hlo n)
  have hs : Summable (fun n => min (w n) t) :=
    Summable.of_nonneg_of_le (fun n => le_min (hn n) ht.le) (fun _ => min_le_left _ _) hw
  let X := t^(-2/3 : ℝ)
  have hX : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num)
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hXt : X*t = t^(1/3 : ℝ) := by
    change t^(-2/3 : ℝ)*t = _
    calc
      _ = t^(-2/3 : ℝ)*t^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ht]; norm_num
  have hXp : X^(-3/2 : ℝ) = t := by
    dsimp [X]
    rw [← Real.rpow_mul ht.le]
    norm_num
  have hXh : X^(-1/2 : ℝ) = t^(1/3 : ℝ) := by
    dsimp [X]
    rw [← Real.rpow_mul ht.le]
    norm_num
  constructor
  · let N := ⌊X⌋₊
    have hN1 : 1 ≤ N := (Nat.one_le_floor_iff X).2 hX
    have hNX : (N : ℝ) ≤ X := Nat.floor_le hX0.le
    have hXN : X/2 ≤ (N : ℝ) := by
      have h := Nat.lt_floor_add_one X
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      dsimp [N] at hNR ⊢
      linarith
    have hterm (n : ℕ) (hnN : n ∈ range N) : min a 1*t ≤ min (w n) t := by
      have hnx : (n : ℝ)+1 ≤ X := by
        have hn' : n+1 ≤ N := by simpa using mem_range.1 hnN
        exact (by exact_mod_cast hn' : (n : ℝ)+1 ≤ N).trans hNX
      have hp : t ≤ ((n : ℝ)+1)^(-3/2 : ℝ) := by
        rw [← hXp]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hnx (by norm_num)
      apply le_min
      · exact (mul_le_mul_of_nonneg_right (min_le_left a 1) ht.le).trans
          ((mul_le_mul_of_nonneg_left hp ha.le).trans (hlo n))
      · simpa using mul_le_mul_of_nonneg_right (min_le_right a 1) ht.le
    calc
      (min a 1/2)*t^(1/3 : ℝ) = (X/2)*(min a 1*t) := by rw [← hXt]; ring
      _ ≤ (N : ℝ)*(min a 1*t) := mul_le_mul_of_nonneg_right hXN (by positivity)
      _ = ∑ n ∈ range N, min a 1*t := by simp
      _ ≤ ∑ n ∈ range N, min (w n) t := sum_le_sum hterm
      _ ≤ ∑' n, min (w n) t := hs.sum_le_tsum _ (fun _ _ => le_min (hn _) ht.le)
  · let N := ⌈X⌉₊
    have hXN : X ≤ (N : ℝ) := Nat.le_ceil X
    have hN : 0 < N := by exact_mod_cast hX0.trans_le hXN
    have hNX : (N : ℝ) ≤ 2*X := by
      have h := Nat.ceil_lt_add_one hX0.le
      dsimp [N]
      linarith
    have hp : (N : ℝ)^(-1/2 : ℝ) ≤ t^(1/3 : ℝ) := by
      rw [← hXh]
      exact Real.rpow_le_rpow_of_nonpos hX0 hXN (by norm_num)
    have hmodel : Summable (fun n : ℕ => ((n : ℝ)+N+1)^(-3/2 : ℝ)) := by
      have hm := (Real.summable_one_div_nat_add_rpow ((N : ℝ)+1) (3/2 : ℝ)).2 (by norm_num)
      apply hm.congr
      intro n
      rw [abs_of_nonneg (by positivity), show (-3/2 : ℝ) = -(3/2) by norm_num,
        Real.rpow_neg (by positivity), one_div]
      simp only [add_assoc]
    have htail : (∑' n, min (w (n+N)) t) ≤ b*(2*(N : ℝ)^(-1/2 : ℝ)) := by
      calc
        _ ≤ ∑' n : ℕ, b*((n : ℝ)+N+1)^(-3/2 : ℝ) :=
          (hs.comp_injective (add_left_injective N)).tsum_le_tsum (fun n =>
            (min_le_left _ _).trans (by simpa only [Nat.cast_add] using hhi (n+N)))
            (hmodel.mul_left b)
        _ = b * ∑' n : ℕ, ((n : ℝ)+N+1)^(-3/2 : ℝ) := tsum_mul_left
        _ ≤ _ := mul_le_mul_of_nonneg_left (three_halves_tail_le hN) hb.le
    calc
      _ = (∑ n ∈ range N, min (w n) t) + ∑' n, min (w (n+N)) t :=
        (hs.sum_add_tsum_nat_add N).symm
      _ ≤ (N : ℝ)*t+b*(2*(N : ℝ)^(-1/2 : ℝ)) := by
        apply add_le_add _ htail
        simpa using sum_le_sum (s := range N) (fun n _ => min_le_right (w n) t)
      _ ≤ (2*X)*t+b*(2*t^(1/3 : ℝ)) := by gcongr
      _ = (2+2*b)*t^(1/3 : ℝ) := by rw [mul_assoc, hXt]; ring

end Problems.Juggler.BeattyPhase
