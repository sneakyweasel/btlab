import BTCalculus.SecondDerivative
import BTCalculus.WeylCancellation
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Quantitative higher-derivative differencing

Derivative chains and genuine shifted differences give finite estimates on
their actual overlap intervals. The numerical bound retains freely chosen
integer differencing windows, so their optimization is a separate step.
-/

noncomputable section

namespace BTCalculus.HigherDerivative

open Finset
open BTCalculus.WeylDifferencing BTCalculus.SecondDerivative

def Chain (f : ℕ → ℝ → ℝ) (r : ℕ) (a b : ℝ) : Prop :=
  ∀ j < r, ∀ x ∈ Set.Icc a b, HasDerivAt (f j) (f (j+1) x) x

def difference (h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x+h)-f x

theorem chain_difference {f : ℕ → ℝ → ℝ} {r : ℕ} {a b h : ℝ}
    (hf : Chain f (r+1) a b) (hh : 0 ≤ h) :
    Chain (fun j => difference h (f j)) r a (b-h) := by
  intro j hj x hx
  have hx0 : x ∈ Set.Icc a b := ⟨hx.1, by linarith [hx.2]⟩
  have hxh : x+h ∈ Set.Icc a b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hd := ((hf j (by omega) (x+h) hxh).comp x
    ((hasDerivAt_id x).add_const h)).fun_sub (hf j (by omega) x hx0)
  dsimp only [difference]
  convert! hd using 1
  simp only [mul_one]

/-- Secants of the preceding derivative retain the sign and the full shift factor. -/
theorem difference_top_bounds {f : ℕ → ℝ → ℝ} {r : ℕ} {a b h lo hi : ℝ}
    (hf : Chain f (r+1) a b) (hh : 0 ≤ h)
    (hq : ∀ x ∈ Set.Icc a b, lo ≤ f (r+1) x ∧ f (r+1) x ≤ hi)
    {x : ℝ} (hx : x ∈ Set.Icc a (b-h)) :
    lo*h ≤ difference h (f r) x ∧ difference h (f r) x ≤ hi*h := by
  have hsub (y : ℝ) (hy : y ∈ Set.Icc x (x+h)) : y ∈ Set.Icc a b :=
    ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have hd := secant_bounds (f r) (f (r+1)) (show x ≤ x+h by linarith)
    (fun y hy => hf r (by omega) y (hsub y hy))
    (fun y hy => hq y (hsub y hy))
  simpa only [difference, add_sub_cancel_left] using hd

/-- A common ambient length allows differencing on successively shorter overlaps. -/
theorem uniform_differencing (z : ℕ → ℂ) {L N H : ℕ}
    (hH : 1 ≤ H) (hHL : H ≤ L) (hLN : L ≤ N)
    (hz : ∀ n < L, ‖z n‖ ≤ 1) {U : ℝ} (hU : 0 ≤ U)
    (hc : ∀ d ∈ Ico 1 H, ‖correlation z L d‖ ≤ (N : ℝ)*U) :
    ‖∑ n ∈ range L, z n‖ ≤ (N : ℝ) * Real.sqrt (2/(H : ℝ)+4*U) := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsum : ∑ d ∈ Ico 1 H, ‖correlation z L d‖ ≤ (H : ℝ) * (N*U) := by
    calc
      _ ≤ ∑ _d ∈ Ico 1 H, (N : ℝ)*U := sum_le_sum hc
      _ = ((H-1 : ℕ) : ℝ)*(N*U) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le H 1)
        (mul_nonneg hN0 hU)
  have hsq := van_der_corput hH hHL hz
  have hupper : 2*(L : ℝ)^2/H + (4*L/H)*∑ d ∈ Ico 1 H, ‖correlation z L d‖ ≤
      (N : ℝ)^2 * (2/H+4*U) := by
    calc
      _ ≤ 2*(N : ℝ)^2/H + (4*N/H)*((H : ℝ)*(N*U)) := by
        gcongr
      _ = _ := by field_simp
  have hn : 0 ≤ 2/(H : ℝ)+4*U := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hN0 (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hn]
  exact hsq.trans hupper

def nestedBound : List ℕ → ℝ → ℝ
  | [], B => B
  | H::hs, B => Real.sqrt (2/(H : ℝ)+4*nestedBound hs B)

theorem nestedBound_nonneg (hs : List ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ nestedBound hs B := by
  cases hs with
  | nil => exact hB
  | cons H hs => exact Real.sqrt_nonneg _

/-- Every derivative estimate used in the differencing tree is proved from the chain.
The ambient lower and upper scales are independent of the chosen actual shifts. -/
theorem higher_derivative_sum_bound (hs : List ℕ) (f : ℕ → ℝ → ℝ)
    (a : ℝ) {L N : ℕ} {lam C lower upper : ℝ}
    (hN : 0 < N) (hLN : L ≤ N) (hwindows : hs.sum ≤ L)
    (hpos : ∀ H ∈ hs, 1 ≤ H) (hlower : 0 < lower) (hlam : lower ≤ lam)
    (hC : 1 ≤ C) (hupper : lam * (hs.prod : ℝ) ≤ upper)
    (hf : Chain f (hs.length+2) a (a+L))
    (hq : ∀ x ∈ Set.Icc a (a+L), lam ≤ f (hs.length+2) x ∧ f (hs.length+2) x ≤ C*lam) :
    ‖∑ n ∈ range L, phase (f 0 (a+n))‖ ≤ (N : ℝ) *
      nestedBound hs (4*C*Real.sqrt upper + 8 / ((N : ℝ)*Real.sqrt lower)) := by
  induction hs generalizing f a L lam with
  | nil =>
    have hlam0 : 0 < lam := hlower.trans_le hlam
    have hcap : lam ≤ upper := by simpa using hupper
    have hs := second_derivative_sum_bound (f 0) (f 1) (f 2) a L hlam0 hC
      (hf 0 (by simp)) (hf 1 (by simp)) (by simpa using hq)
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hl : 0 < Real.sqrt lower := Real.sqrt_pos.mpr hlower
    have hsl : Real.sqrt lower ≤ Real.sqrt lam := Real.sqrt_le_sqrt hlam
    have hsu : Real.sqrt lam ≤ Real.sqrt upper := Real.sqrt_le_sqrt hcap
    have he : (N : ℝ)*(4*C*Real.sqrt upper + 8/((N : ℝ)*Real.sqrt lower)) =
        4*C*N*Real.sqrt upper + 8/Real.sqrt lower := by field_simp
    simp only [nestedBound]
    rw [he]
    apply hs.trans
    apply add_le_add
    · gcongr
    · exact div_le_div_of_nonneg_left (by norm_num) hl hsl
  | cons H hs ih =>
    have hlam0 : 0 < lam := hlower.trans_le hlam
    have hH := hpos H (by simp)
    have hHL : H ≤ L := by simpa only [List.sum_cons] using
      (Nat.le_add_right H hs.sum).trans hwindows
    have hprod : (0 : ℝ) < (hs.prod : ℝ) := by
      exact_mod_cast List.prod_pos (fun k hk => lt_of_lt_of_le Nat.zero_lt_one (hpos k (by simp [hk])))
    have hupper0 : 0 ≤ upper := by
      have hlam0 := hlower.trans_le hlam
      have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
      have he : lam * (hs.prod : ℝ) * H ≤ upper := by
        simpa only [List.prod_cons, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hupper
      exact (le_of_lt (mul_pos (mul_pos hlam0 hprod) hH0)).trans he
    have hB : 0 ≤ 4*C*Real.sqrt upper + 8/((N : ℝ)*Real.sqrt lower) := by positivity
    apply uniform_differencing (fun n => phase (f 0 (a+n))) hH hHL hLN
      (fun n _ => (phase_norm _).le) (nestedBound_nonneg hs hB)
    intro d hd
    have hd1 : 1 ≤ d := (mem_Ico.mp hd).1
    have hdH : d < H := (mem_Ico.mp hd).2
    have hdL : d ≤ L := by omega
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hsupport : a + ((L-d : ℕ) : ℝ) = (a+L) - d := by
      rw [Nat.cast_sub hdL]
      ring
    have hchain : Chain (fun j => difference d (f j)) (hs.length+2) a (a+(L-d : ℕ)) := by
      rw [hsupport]
      apply chain_difference _ hd0
      convert hf using 1
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hcurv : ∀ x ∈ Set.Icc a (a+(L-d : ℕ)),
        lam*d ≤ difference d (f (hs.length+2)) x ∧
          difference d (f (hs.length+2)) x ≤ C*(lam*d) := by
      intro x hx
      rw [hsupport] at hx
      have hf' : Chain f ((hs.length+2)+1) a (a+L) := by
        convert hf using 1
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hq' : ∀ x ∈ Set.Icc a (a+L), lam ≤ f ((hs.length+2)+1) x ∧
          f ((hs.length+2)+1) x ≤ C*lam := by
        convert hq using 1
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have h := difference_top_bounds hf' hd0 hq' hx
      simpa only [mul_assoc] using h
    have hcap : (lam*d) * (hs.prod : ℝ) ≤ upper := by
      calc
        _ ≤ (lam*H) * (hs.prod : ℝ) := by gcongr
        _ = lam * ((H::hs).prod : ℝ) := by simp [mul_assoc]
        _ ≤ upper := hupper
    have hi := ih (fun j => difference d (f j)) a (Nat.sub_le L d |>.trans hLN)
      (by simp only [List.sum_cons] at hwindows; omega)
      (fun k hk => hpos k (by simp [hk]))
      (show lower ≤ lam*d by nlinarith [hlower.trans_le hlam]) hcap hchain hcurv
    simpa only [correlation, phase_mul_conj, difference, Nat.cast_add, add_assoc] using hi

/-- Conjugation handles a derivative of constant negative sign throughout the interval. -/
theorem signed_higher_derivative_sum_bound (hs : List ℕ) (f : ℕ → ℝ → ℝ)
    (a : ℝ) {L N : ℕ} {lam C lower upper : ℝ}
    (hN : 0 < N) (hLN : L ≤ N) (hwindows : hs.sum ≤ L)
    (hpos : ∀ H ∈ hs, 1 ≤ H) (hlower : 0 < lower) (hlam : lower ≤ lam)
    (hC : 1 ≤ C) (hupper : lam * (hs.prod : ℝ) ≤ upper)
    (hf : Chain f (hs.length+2) a (a+L))
    (hq : (∀ x ∈ Set.Icc a (a+L), lam ≤ f (hs.length+2) x ∧ f (hs.length+2) x ≤ C*lam) ∨
      (∀ x ∈ Set.Icc a (a+L), -C*lam ≤ f (hs.length+2) x ∧ f (hs.length+2) x ≤ -lam)) :
    ‖∑ n ∈ range L, phase (f 0 (a+n))‖ ≤ (N : ℝ) *
      nestedBound hs (4*C*Real.sqrt upper + 8 / ((N : ℝ)*Real.sqrt lower)) := by
  rcases hq with hp | hn
  · exact higher_derivative_sum_bound hs f a hN hLN hwindows hpos hlower hlam hC hupper hf hp
  · have hc : Chain (fun j x => -f j x) (hs.length+2) a (a+L) := by
      intro j hj x hx
      exact (hf j hj x hx).neg
    have hb : ∀ x ∈ Set.Icc a (a+L),
        lam ≤ -f (hs.length+2) x ∧ -f (hs.length+2) x ≤ C*lam := by
      intro x hx
      have h := hn x hx
      constructor <;> linarith
    have h := higher_derivative_sum_bound hs (fun j x => -f j x) a
      hN hLN hwindows hpos hlower hlam hC hupper hc hb
    simpa only [phase_neg, ← map_sum, Complex.norm_conj] using h

theorem rounded_window_bounds {q : ℝ} (hq : 1 ≤ q) :
    1 ≤ ⌈q⌉₊ ∧ q ≤ (⌈q⌉₊ : ℝ) ∧ (⌈q⌉₊ : ℝ) ≤ 2*q := by
  refine ⟨Nat.ceil_pos.mpr (by linarith), Nat.le_ceil q, ?_⟩
  exact Nat.ceil_le_two_mul (by linarith)

theorem sqrt_le_div_of_mul_sq_le {x a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q)
    (hx : x*q^2 ≤ a^2) : Real.sqrt x ≤ a/q := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hq 2)).mpr hx

/-- A fully explicit third-derivative test with a real cutoff, rounded inside the proof. -/
theorem third_derivative_test (f : ℕ → ℝ → ℝ) (a : ℝ) {N : ℕ} {lam q : ℝ}
    (hlam : 0 < lam) (hq : 1 ≤ q) (hsize : 2*q ≤ N)
    (hsmall : lam*q^3 ≤ 1) (htail : q ≤ (N : ℝ)*Real.sqrt lam)
    (hf : Chain f 3 a (a+N))
    (hf3 : (∀ x ∈ Set.Icc a (a+N), lam ≤ f 3 x ∧ f 3 x ≤ 4*lam) ∨
      (∀ x ∈ Set.Icc a (a+N), -4*lam ≤ f 3 x ∧ f 3 x ≤ -lam)) :
    ‖∑ n ∈ range N, phase (f 0 (a+n))‖ ≤ 12 * N / Real.sqrt q := by
  have hq0 : 0 < q := by linarith
  have hN : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  obtain ⟨hH, hqH, hHq⟩ := rounded_window_bounds hq
  have hHN : ⌈q⌉₊ ≤ N := by exact_mod_cast hHq.trans hsize
  have hcap : lam * (([⌈q⌉₊] : List ℕ).prod : ℝ) ≤ 2*lam*q := by
    simp only [List.prod_cons, List.prod_nil, mul_one]
    nlinarith
  have he := signed_higher_derivative_sum_bound [⌈q⌉₊] f a hN le_rfl
    (by simpa using hHN) (by simpa) hlam le_rfl (by norm_num : (1 : ℝ) ≤ 4)
    hcap (by simpa using hf) (by simpa using hf3)
  have hs : Real.sqrt (2*lam*q) ≤ (3/2)/q := by
    apply sqrt_le_div_of_mul_sq_le (by norm_num) hq0
    nlinarith
  have hb : 4*4*Real.sqrt (2*lam*q) + 8/((N : ℝ)*Real.sqrt lam) ≤ 32/q := by
    calc
      _ ≤ 4*4*((3/2)/q) + 8/q := add_le_add (by gcongr)
        (div_le_div_of_nonneg_left (by norm_num) hq0 htail)
      _ = _ := by ring
  have hc : 2/(⌈q⌉₊ : ℝ) + 4*(4*4*Real.sqrt (2*lam*q) + 8/((N : ℝ)*Real.sqrt lam)) ≤
      130/q := by
    calc
      _ ≤ 2/q+4*(32/q) := add_le_add
        (div_le_div_of_nonneg_left (by norm_num) hq0 hqH) (by gcongr)
      _ = _ := by ring
  have hr : Real.sqrt (130/q) ≤ 12/Real.sqrt q := by
    apply sqrt_le_div_of_mul_sq_le (by norm_num) (Real.sqrt_pos.mpr hq0)
    rw [Real.sq_sqrt hq0.le]
    field_simp
    norm_num
  apply he.trans
  simp only [nestedBound]
  calc
    _ ≤ (N : ℝ)*(12/Real.sqrt q) := by
      gcongr
      exact (Real.sqrt_le_sqrt hc).trans hr
    _ = _ := by ring

/-- A fifth-derivative test with three actual windows and numerical constant seven. -/
theorem fifth_derivative_test (f : ℕ → ℝ → ℝ) (a : ℝ) {N : ℕ} {lam q : ℝ}
    (hlam : 0 < lam) (hq : 1 ≤ q) (hsize : 2*(q+q^2+q^4) ≤ N)
    (hsmall : lam*q^15 ≤ 1) (htail : q^4 ≤ (N : ℝ)*Real.sqrt lam)
    (hf : Chain f 5 a (a+N))
    (hf5 : (∀ x ∈ Set.Icc a (a+N), lam ≤ f 5 x ∧ f 5 x ≤ 6*lam) ∨
      (∀ x ∈ Set.Icc a (a+N), -6*lam ≤ f 5 x ∧ f 5 x ≤ -lam)) :
    ‖∑ n ∈ range N, phase (f 0 (a+n))‖ ≤ 7 * N / Real.sqrt q := by
  have hq0 : 0 < q := by linarith
  have hq2 : 1 ≤ q^2 := by nlinarith
  have hq4 : 1 ≤ q^4 := by nlinarith [sq_nonneg (q^2-1)]
  have hN : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  obtain ⟨hH1, hqH1, hHq1⟩ := rounded_window_bounds hq
  obtain ⟨hH2, hqH2, hHq2⟩ := rounded_window_bounds hq2
  obtain ⟨hH3, hqH3, hHq3⟩ := rounded_window_bounds hq4
  let hs := [⌈q⌉₊, ⌈q^2⌉₊, ⌈q^4⌉₊]
  have hsum : hs.sum ≤ N := by
    change ⌈q⌉₊ + (⌈q^2⌉₊ + ⌈q^4⌉₊) ≤ N
    exact_mod_cast (show (⌈q⌉₊ : ℝ)+((⌈q^2⌉₊ : ℝ)+(⌈q^4⌉₊ : ℝ)) ≤ N by linarith)
  have hcap : lam * (hs.prod : ℝ) ≤ 8*lam*q^7 := by
    dsimp [hs]
    simp only [mul_one, Nat.cast_mul]
    calc
      _ ≤ lam * ((2*q)*((2*q^2)*(2*q^4))) := by gcongr
      _ = _ := by ring
  have he := signed_higher_derivative_sum_bound hs f a hN le_rfl hsum
    (by intro H hH; simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hH
        rcases hH with rfl | rfl | rfl <;> assumption)
    hlam le_rfl (by norm_num : (1 : ℝ) ≤ 6) hcap
    (by simpa [hs] using hf) (by simpa [hs] using hf5)
  have hsqrt : Real.sqrt (8*lam*q^7) ≤ 3/q^4 := by
    apply sqrt_le_div_of_mul_sq_le (by norm_num) (pow_pos hq0 4)
    calc
      _ = 8*(lam*q^15) := by ring
      _ ≤ 8 := by linarith
      _ ≤ _ := by norm_num
  have hb : 4*6*Real.sqrt (8*lam*q^7) + 8/((N : ℝ)*Real.sqrt lam) ≤ 80/q^4 := by
    calc
      _ ≤ 4*6*(3/q^4) + 8/q^4 := add_le_add (by gcongr)
        (div_le_div_of_nonneg_left (by norm_num) (pow_pos hq0 4) htail)
      _ = _ := by ring
  have h3 : Real.sqrt (2/(⌈q^4⌉₊ : ℝ)+4*(4*6*Real.sqrt (8*lam*q^7) +
      8/((N : ℝ)*Real.sqrt lam))) ≤ 18/q^2 := by
    calc
      _ ≤ Real.sqrt (322/q^4) := Real.sqrt_le_sqrt (by calc
        _ ≤ 2/q^4+4*(80/q^4) := add_le_add
          (div_le_div_of_nonneg_left (by norm_num) (pow_pos hq0 4) hqH3) (by gcongr)
        _ = _ := by ring)
      _ ≤ _ := by
        apply sqrt_le_div_of_mul_sq_le (by norm_num) (pow_pos hq0 2)
        field_simp
        nlinarith [pow_pos hq0 4]
  have h2 : Real.sqrt (2/(⌈q^2⌉₊ : ℝ)+4*(18/q^2)) ≤ 9/q := by
    calc
      _ ≤ Real.sqrt (74/q^2) := Real.sqrt_le_sqrt (by calc
        _ ≤ 2/q^2+4*(18/q^2) := add_le_add_left
          (div_le_div_of_nonneg_left (by norm_num) (pow_pos hq0 2) hqH2) _
        _ = _ := by ring)
      _ ≤ _ := by
        apply sqrt_le_div_of_mul_sq_le (by norm_num) hq0
        field_simp
        nlinarith [sq_pos_of_pos hq0]
  have h1 : Real.sqrt (2/(⌈q⌉₊ : ℝ)+4*(9/q)) ≤ 7/Real.sqrt q := by
    calc
      _ ≤ Real.sqrt (38/q) := Real.sqrt_le_sqrt (by calc
        _ ≤ 2/q+4*(9/q) := add_le_add_left
          (div_le_div_of_nonneg_left (by norm_num) hq0 hqH1) _
        _ = _ := by ring)
      _ ≤ _ := by
        apply sqrt_le_div_of_mul_sq_le (by norm_num) (Real.sqrt_pos.mpr hq0)
        rw [Real.sq_sqrt hq0.le]
        field_simp
        norm_num
  apply he.trans
  simp only [hs, nestedBound]
  calc
    _ ≤ (N : ℝ)*Real.sqrt (2/(⌈q⌉₊ : ℝ)+4*(9/q)) := by
      gcongr
      exact (Real.sqrt_le_sqrt (by linarith [h3])).trans h2
    _ ≤ (N : ℝ)*(7/Real.sqrt q) := by gcongr
    _ = _ := by ring

theorem inverse_root_cap {lam q : ℝ} (hlam : 0 < lam) (hq0 : 0 ≤ q)
    {r : ℕ} (hr : 0 < r) (hq : q ≤ lam^(-(1/(r : ℝ)))) : lam*q^r ≤ 1 := by
  calc
    _ ≤ lam*(lam^(-(1/(r : ℝ))))^r := by gcongr
    _ = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      have he : -(1/(r : ℝ))*(r : ℝ) = -1 := by field_simp
      rw [he, Real.rpow_neg_one, mul_inv_cancel₀ hlam.ne']

def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

theorem fourthRoot_pos {x : ℝ} (hx : 0 < x) : 0 < fourthRoot x :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx)

theorem fourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) : (fourthRoot x)^4 = x := by
  calc
    _ = ((Real.sqrt (Real.sqrt x))^2)^2 := by dsimp [fourthRoot]; ring
    _ = (Real.sqrt x)^2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg x)]
    _ = x := Real.sq_sqrt hx

theorem pow_four_le_of_le_fourthRoot {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q)
    (hqx : q ≤ fourthRoot x) : q^4 ≤ x := by
  rw [← fourthRoot_pow_four hx]
  gcongr

def thirdCutoff (N : ℕ) (lam : ℝ) : ℝ :=
  min (lam^(-(1/3 : ℝ))) (min ((N : ℝ)/2) ((N : ℝ)*Real.sqrt lam))

def fifthCutoff (N : ℕ) (lam : ℝ) : ℝ :=
  min (lam^(-(1/15 : ℝ)))
    (min (fourthRoot ((N : ℝ)/6)) (fourthRoot ((N : ℝ)*Real.sqrt lam)))

theorem thirdCutoff_pos {N : ℕ} (hN : 0 < N) {lam : ℝ} (hlam : 0 < lam) :
    0 < thirdCutoff N lam := by
  unfold thirdCutoff
  positivity

theorem fifthCutoff_pos {N : ℕ} (hN : 0 < N) {lam : ℝ} (hlam : 0 < lam) :
    0 < fifthCutoff N lam := by
  unfold fifthCutoff
  exact lt_min (Real.rpow_pos_of_pos hlam _) (lt_min
    (fourthRoot_pos (by positivity)) (fourthRoot_pos (by positivity)))

theorem small_cutoff_bound (f : ℕ → ℝ) (N : ℕ) {q K : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hK : 1 ≤ K) :
    ‖∑ n ∈ range N, phase (f n)‖ ≤ K*N/Real.sqrt q := by
  have h := norm_phase_sum_le_card f (range N)
  simp only [card_range] at h
  apply h.trans
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hq0)).mpr
  have hs : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- All positive curvature scales and all positive lengths are covered; the cutoff is explicit. -/
theorem third_derivative_bound (f : ℕ → ℝ → ℝ) (a : ℝ) {N : ℕ} {lam : ℝ}
    (hN : 0 < N) (hlam : 0 < lam) (hf : Chain f 3 a (a+N))
    (hf3 : (∀ x ∈ Set.Icc a (a+N), lam ≤ f 3 x ∧ f 3 x ≤ 4*lam) ∨
      (∀ x ∈ Set.Icc a (a+N), -4*lam ≤ f 3 x ∧ f 3 x ≤ -lam)) :
    ‖∑ n ∈ range N, phase (f 0 (a+n))‖ ≤ 12*N/Real.sqrt (thirdCutoff N lam) := by
  have hq0 := thirdCutoff_pos hN hlam
  by_cases hq : 1 ≤ thirdCutoff N lam
  · have h1 : thirdCutoff N lam ≤ lam^(-(1/3 : ℝ)) := min_le_left _ _
    have h2 : thirdCutoff N lam ≤ (N : ℝ)/2 := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : thirdCutoff N lam ≤ (N : ℝ)*Real.sqrt lam := (min_le_right _ _).trans (min_le_right _ _)
    exact third_derivative_test f a hlam hq (by linarith)
      (inverse_root_cap hlam hq0.le (by norm_num : 0 < (3 : ℕ)) (by simpa using h1)) h3 hf hf3
  · exact small_cutoff_bound (fun n => f 0 (a+n)) N hq0 (not_le.mp hq).le (by norm_num)

/-- Three differencing steps and the second-derivative test give an unconditional finite
fifth-derivative bound, with no assumed cancellation or window-existence premise. -/
theorem fifth_derivative_bound (f : ℕ → ℝ → ℝ) (a : ℝ) {N : ℕ} {lam : ℝ}
    (hN : 0 < N) (hlam : 0 < lam) (hf : Chain f 5 a (a+N))
    (hf5 : (∀ x ∈ Set.Icc a (a+N), lam ≤ f 5 x ∧ f 5 x ≤ 6*lam) ∨
      (∀ x ∈ Set.Icc a (a+N), -6*lam ≤ f 5 x ∧ f 5 x ≤ -lam)) :
    ‖∑ n ∈ range N, phase (f 0 (a+n))‖ ≤ 7*N/Real.sqrt (fifthCutoff N lam) := by
  have hq0 := fifthCutoff_pos hN hlam
  by_cases hq : 1 ≤ fifthCutoff N lam
  · have h1 : fifthCutoff N lam ≤ lam^(-(1/15 : ℝ)) := min_le_left _ _
    have h2 : fifthCutoff N lam ≤ fourthRoot ((N : ℝ)/6) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have h3 : fifthCutoff N lam ≤ fourthRoot ((N : ℝ)*Real.sqrt lam) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hq4 := pow_four_le_of_le_fourthRoot (by positivity : 0 ≤ (N : ℝ)/6) hq0.le h2
    have htail := pow_four_le_of_le_fourthRoot
      (by positivity : 0 ≤ (N : ℝ)*Real.sqrt lam) hq0.le h3
    have hsize : 2*(fifthCutoff N lam+(fifthCutoff N lam)^2+(fifthCutoff N lam)^4) ≤ N := by
      have hq2 : fifthCutoff N lam ≤ (fifthCutoff N lam)^2 := by nlinarith
      have hq24 : (fifthCutoff N lam)^2 ≤ (fifthCutoff N lam)^4 := by
        nlinarith [sq_nonneg ((fifthCutoff N lam)^2-1)]
      linarith
    exact fifth_derivative_test f a hlam hq hsize
      (inverse_root_cap hlam hq0.le (by norm_num : 0 < (15 : ℕ)) (by simpa using h1)) htail hf hf5
  · exact small_cutoff_bound (fun n => f 0 (a+n)) N hq0 (not_le.mp hq).le (by norm_num)

def integerCount (A B : ℝ) : ℕ := (⌊B⌋-⌊A⌋).toNat
def integerStart (A : ℝ) : ℝ := (⌊A⌋ : ℝ)+1

/-- The finite sum over real endpoints has exactly the floor-difference length. -/
theorem integer_sum_eq_range (f : ℝ → ℝ) (A B : ℝ) :
    (∑ n ∈ Finset.Ioc ⌊A⌋ ⌊B⌋, phase (f (n : ℝ))) =
      ∑ n ∈ range (integerCount A B), phase (f (integerStart A+n)) := by
  symm
  apply sum_bij (fun (n : ℕ) _ => ⌊A⌋+1+(n : ℤ))
  · intro n hn
    simp only [mem_range, integerCount] at hn
    simp only [Finset.mem_Ioc]
    omega
  · intro i _ j _ hij
    omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    refine ⟨(n-⌊A⌋-1).toNat, ?_, ?_⟩
    · simp only [mem_range, integerCount]
      omega
    · omega
  · intro n _
    congr 1
    congr 1
    simp [integerStart, Int.cast_add]

/-- One unit of right support supplies the final increment required by the derivative test. -/
theorem integer_support {A B : ℝ} (hAB : A ≤ B) :
    Set.Icc (integerStart A) (integerStart A+integerCount A B) ⊆ Set.Icc A (B+1) := by
  have hf : ⌊A⌋ ≤ ⌊B⌋ := Int.floor_mono hAB
  have hn : ((integerCount A B : ℕ) : ℤ) = ⌊B⌋-⌊A⌋ := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hf)
  have hnR : ((integerCount A B : ℕ) : ℝ) = (⌊B⌋ : ℝ)-(⌊A⌋ : ℝ) := by exact_mod_cast hn
  intro x hx
  dsimp only [integerStart] at hx
  rw [hnR] at hx
  constructor
  · linarith [Int.lt_floor_add_one A, hx.1]
  · linarith [Int.floor_le B, hx.2]

/-- Third-derivative cancellation for the actual integers in a real half-open interval. -/
theorem third_derivative_real_interval (f : ℕ → ℝ → ℝ) {A B lam : ℝ}
    (hAB : A ≤ B) (hN : 0 < integerCount A B) (hlam : 0 < lam)
    (hf : Chain f 3 A (B+1))
    (hf3 : (∀ x ∈ Set.Icc A (B+1), lam ≤ f 3 x ∧ f 3 x ≤ 4*lam) ∨
      (∀ x ∈ Set.Icc A (B+1), -4*lam ≤ f 3 x ∧ f 3 x ≤ -lam)) :
    ‖∑ n ∈ Finset.Ioc ⌊A⌋ ⌊B⌋, phase (f 0 (n : ℝ))‖ ≤
      12*integerCount A B/Real.sqrt (thirdCutoff (integerCount A B) lam) := by
  rw [integer_sum_eq_range]
  apply third_derivative_bound f (integerStart A) hN hlam
  · exact fun j hj x hx => hf j hj x (integer_support hAB hx)
  · exact hf3.imp (fun h x hx => h x (integer_support hAB hx))
      (fun h x hx => h x (integer_support hAB hx))

/-- Fifth-derivative cancellation for the actual integers in a real half-open interval. -/
theorem fifth_derivative_real_interval (f : ℕ → ℝ → ℝ) {A B lam : ℝ}
    (hAB : A ≤ B) (hN : 0 < integerCount A B) (hlam : 0 < lam)
    (hf : Chain f 5 A (B+1))
    (hf5 : (∀ x ∈ Set.Icc A (B+1), lam ≤ f 5 x ∧ f 5 x ≤ 6*lam) ∨
      (∀ x ∈ Set.Icc A (B+1), -6*lam ≤ f 5 x ∧ f 5 x ≤ -lam)) :
    ‖∑ n ∈ Finset.Ioc ⌊A⌋ ⌊B⌋, phase (f 0 (n : ℝ))‖ ≤
      7*integerCount A B/Real.sqrt (fifthCutoff (integerCount A B) lam) := by
  rw [integer_sum_eq_range]
  apply fifth_derivative_bound f (integerStart A) hN hlam
  · exact fun j hj x hx => hf j hj x (integer_support hAB hx)
  · exact hf5.imp (fun h x hx => h x (integer_support hAB hx))
      (fun h x hx => h x (integer_support hAB hx))

theorem inv_sqrt_min {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1/Real.sqrt (min x y) = max (1/Real.sqrt x) (1/Real.sqrt y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_left]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt h)
  · rw [min_eq_right h, max_eq_right]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hy) (Real.sqrt_le_sqrt h)

theorem inv_sqrt_rpow {x : ℝ} (hx : 0 < x) (p : ℝ) :
    1/Real.sqrt (x^p) = x^(-p/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le, one_div, ← Real.rpow_neg hx.le]
  congr 1
  ring

theorem inv_sqrt_eq_rpow {x : ℝ} (hx : 0 < x) :
    1/Real.sqrt x = x^(-(1/2 : ℝ)) := by
  simpa only [Real.rpow_one, neg_div] using inv_sqrt_rpow hx 1

theorem inv_sqrt_fourthRoot {x : ℝ} (hx : 0 < x) :
    1/Real.sqrt (fourthRoot x) = x^(-(1/8 : ℝ)) := by
  simp only [fourthRoot, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, one_div, ← Real.rpow_neg hx.le]
  norm_num

/-- The third-derivative estimate in explicit power-rate form. -/
theorem third_derivative_rate (f : ℕ → ℝ → ℝ) (a : ℝ) {N : ℕ} {lam : ℝ}
    (hN : 0 < N) (hlam : 0 < lam) (hf : Chain f 3 a (a+N))
    (hf3 : (∀ x ∈ Set.Icc a (a+N), lam ≤ f 3 x ∧ f 3 x ≤ 4*lam) ∨
      (∀ x ∈ Set.Icc a (a+N), -4*lam ≤ f 3 x ∧ f 3 x ≤ -lam)) :
    ‖∑ n ∈ range N, phase (f 0 (a+n))‖ ≤ 12*N *
      max (lam^(1/6 : ℝ)) (max (((N : ℝ)/2)^(-(1/2 : ℝ)))
        (((N : ℝ)*Real.sqrt lam)^(-(1/2 : ℝ)))) := by
  have h := third_derivative_bound f a hN hlam hf hf3
  rw [div_eq_mul_one_div, thirdCutoff,
    inv_sqrt_min (Real.rpow_pos_of_pos hlam _) (by positivity),
    inv_sqrt_min (by positivity : 0 < (N : ℝ)/2) (by positivity),
    inv_sqrt_rpow hlam, inv_sqrt_eq_rpow (by positivity : 0 < (N : ℝ)/2),
    inv_sqrt_eq_rpow (by positivity : 0 < (N : ℝ)*Real.sqrt lam)] at h
  norm_num at h ⊢
  exact h

/-- The fifth-derivative estimate in explicit power-rate form. -/
theorem fifth_derivative_rate (f : ℕ → ℝ → ℝ) (a : ℝ) {N : ℕ} {lam : ℝ}
    (hN : 0 < N) (hlam : 0 < lam) (hf : Chain f 5 a (a+N))
    (hf5 : (∀ x ∈ Set.Icc a (a+N), lam ≤ f 5 x ∧ f 5 x ≤ 6*lam) ∨
      (∀ x ∈ Set.Icc a (a+N), -6*lam ≤ f 5 x ∧ f 5 x ≤ -lam)) :
    ‖∑ n ∈ range N, phase (f 0 (a+n))‖ ≤ 7*N *
      max (lam^(1/30 : ℝ)) (max (((N : ℝ)/6)^(-(1/8 : ℝ)))
        (((N : ℝ)*Real.sqrt lam)^(-(1/8 : ℝ)))) := by
  have h := fifth_derivative_bound f a hN hlam hf hf5
  rw [div_eq_mul_one_div, fifthCutoff,
    inv_sqrt_min (Real.rpow_pos_of_pos hlam _) (lt_min
      (fourthRoot_pos (by positivity)) (fourthRoot_pos (by positivity))),
    inv_sqrt_min (fourthRoot_pos (by positivity : 0 < (N : ℝ)/6))
      (fourthRoot_pos (by positivity)),
    inv_sqrt_rpow hlam, inv_sqrt_fourthRoot (by positivity : 0 < (N : ℝ)/6),
    inv_sqrt_fourthRoot (by positivity : 0 < (N : ℝ)*Real.sqrt lam)] at h
  norm_num at h ⊢
  exact h

end BTCalculus.HigherDerivative
