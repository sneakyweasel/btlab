import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Problems.Juggler.OstrowskiSandwich

set_option maxRecDepth 4000000

namespace Problems.Juggler

/-!
# General Ostrowski numeration and the structural digit cap

Paper A Theorem 5.8 bounds the Denjoy–Koksma budget on the window
by the greedy Ostrowski digit sum `s(L)`, using the structural cap
`b_j ≤ a_{j+1}` on greedy digits. This file proves that cap in
Lean, for *arbitrary* denominator sequences satisfying the
convergent recurrence — not just the certified θ list — and
instantiates it: every `L < 301994` has greedy digit sum at
most `47`, with the exact decomposition `L = Σ bⱼ qⱼ`.

The general half (`ostroRem_lt`, `ostroDigit_le`, `ostro_sum_eq`,
`ostro_digitSum_le`) is problem-independent numeration over any
`q, a : ℕ → ℕ` with `q` monotone and `q (j+1) ≤ a (j+1) · q j +
q (j-1)`; a future deeper certified quotient list reuses it
unchanged. The θ instance closes the window at
`q₁₃ = 301994 = 1·176251 + 125743` (`theta_window_endpoint`).

This subsumes the digit-cap step of Theorem 5.8 (previously a
human proof); the Denjoy–Koksma comparison stays analytic
(KNOWN). The scan `window_digit_scan` remains the sharper bound
(`≤ 37`) on the window. Not a cycle obstruction and not a halt
theorem.
-/

section General

variable (q a : ℕ → ℕ)

/-- Greedy remainder: `ostroRem q L n i` is what is left of `L`
after greedily peeling levels `n, n-1, …, n-i+1`. -/
def ostroRem (L n : ℕ) : ℕ → ℕ
  | 0 => L
  | i + 1 => ostroRem L n i % q (n - i)

/-- Greedy digit at step `i`, that is at level `n - i`. -/
def ostroDigit (L n i : ℕ) : ℕ := ostroRem q L n i / q (n - i)

/-- Remainder invariant: starting below `q (n+1)`, the remainder
before processing level `n - i` stays below `q (n - i + 1)`. -/
theorem ostroRem_lt (h0 : 0 < q 0) (hmono : ∀ j, q j ≤ q (j + 1))
    {L n : ℕ} (hL : L < q (n + 1)) (i : ℕ) :
    ostroRem q L n i < q (n - i + 1) := by
  have hq : Monotone q := monotone_nat_of_le_succ hmono
  induction i with
  | zero => simpa [ostroRem] using hL
  | succ i ih =>
    have hpos : 0 < q (n - i) := lt_of_lt_of_le h0 (hq (Nat.zero_le _))
    have hlt : ostroRem q L n (i + 1) < q (n - i) :=
      Nat.mod_lt _ hpos
    exact lt_of_lt_of_le hlt (hq (by omega))

/-- **Structural digit cap**: greedy digits obey `b_j ≤ a_{j+1}`
whenever the denominators satisfy the convergent recurrence bound
`q (j+1) ≤ a (j+1) · q j + q (j-1)`. -/
theorem ostroDigit_le (h0 : 0 < q 0) (hmono : ∀ j, q j ≤ q (j + 1))
    (hrec : ∀ j, q (j + 1) ≤ a (j + 1) * q j + q (j - 1))
    {L n : ℕ} (hL : L < q (n + 1)) (i : ℕ) :
    ostroDigit q L n i ≤ a (n - i + 1) := by
  have hq : Monotone q := monotone_nat_of_le_succ hmono
  have hpos : 0 < q (n - i) := lt_of_lt_of_le h0 (hq (Nat.zero_le _))
  have hR : ostroRem q L n i < q (n - i + 1) := ostroRem_lt q h0 hmono hL i
  have hprev : q (n - i - 1) ≤ q (n - i) := hq (Nat.sub_le _ _)
  have hkey : ostroRem q L n i < (a (n - i + 1) + 1) * q (n - i) := by
    have := hrec (n - i)
    nlinarith
  have hdiv : ostroRem q L n i / q (n - i) < a (n - i + 1) + 1 :=
    (Nat.div_lt_iff_lt_mul hpos).mpr hkey
  exact Nat.lt_succ_iff.mp hdiv

/-- Partial reconstruction: at every stage the processed digits
plus the current remainder recover `L`. -/
theorem ostro_reconstruct (L n : ℕ) :
    ∀ m, L = (∑ i ∈ Finset.range m, ostroDigit q L n i * q (n - i)) +
      ostroRem q L n m := by
  intro m
  induction m with
  | zero => simp [ostroRem]
  | succ m ih =>
    have hsplit : ostroRem q L n m =
        ostroDigit q L n m * q (n - m) + ostroRem q L n (m + 1) := by
      have h := Nat.div_add_mod (ostroRem q L n m) (q (n - m))
      calc ostroRem q L n m
          = q (n - m) * (ostroRem q L n m / q (n - m)) +
            ostroRem q L n m % q (n - m) := h.symm
        _ = ostroDigit q L n m * q (n - m) + ostroRem q L n (m + 1) := by
            rw [ostroDigit, Nat.mul_comm]; rfl
    rw [Finset.sum_range_succ]
    omega

/-- **Exact decomposition**: with `q 0 = 1` the greedy digits
reconstruct `L` exactly. -/
theorem ostro_sum_eq (hq0 : q 0 = 1) (L n : ℕ) :
    L = ∑ i ∈ Finset.range (n + 1), ostroDigit q L n i * q (n - i) := by
  have h := ostro_reconstruct q L n (n + 1)
  have hzero : ostroRem q L n (n + 1) = 0 := by
    show ostroRem q L n n % q (n - n) = 0
    rw [Nat.sub_self, hq0]
    exact Nat.mod_one _
  omega

/-- **Digit-sum cap**: the greedy digit sum is bounded by the sum
of the quotients along the levels used. -/
theorem ostro_digitSum_le (h0 : 0 < q 0) (hmono : ∀ j, q j ≤ q (j + 1))
    (hrec : ∀ j, q (j + 1) ≤ a (j + 1) * q j + q (j - 1))
    {L n : ℕ} (hL : L < q (n + 1)) :
    ∑ i ∈ Finset.range (n + 1), ostroDigit q L n i ≤
      ∑ i ∈ Finset.range (n + 1), a (n - i + 1) :=
  Finset.sum_le_sum fun i _ => ostroDigit_le q a h0 hmono hrec hL i

end General

/-!
## The θ instance

Denominators are the certified list of `theta_convergent_denominators`,
closed at the window endpoint `q₁₃ = 301994`; quotients are the
certified `thetaQuotients` with the closing quotient `a₁₃ = 1`
(`176251 + 125743 = 301994`). Beyond the window both functions are
constant, which keeps the hypotheses trivially true there.
-/

private theorem getD_of_length_le {l : List ℕ} {j : ℕ}
    (h : l.length ≤ j) (d : ℕ) : l.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

/-- The certified θ denominators as a function, constant `301994`
past the window. -/
def thetaDenomFn (j : ℕ) : ℕ :=
  [1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508, 125743,
    176251].getD j 301994

/-- The certified θ quotients as a function (`a 1 = 2, …`), with
the window-closing quotient `a 13 = 1` and constant `1` beyond;
index `0` is unused. -/
def thetaQuotFn (j : ℕ) : ℕ :=
  [1, 2, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1].getD j 1

theorem thetaDenomFn_mono : ∀ j, thetaDenomFn j ≤ thetaDenomFn (j + 1) := by
  intro j
  rcases Nat.lt_or_ge j 13 with h | h
  · interval_cases j <;> decide
  · unfold thetaDenomFn
    rw [getD_of_length_le (by simp; omega), getD_of_length_le (by simp; omega)]

theorem thetaDenomFn_rec : ∀ j,
    thetaDenomFn (j + 1) ≤ thetaQuotFn (j + 1) * thetaDenomFn j +
      thetaDenomFn (j - 1) := by
  intro j
  rcases Nat.lt_or_ge j 13 with h | h
  · interval_cases j <;> decide
  · have h1 : thetaDenomFn (j + 1) = 301994 :=
      getD_of_length_le (by simp; omega) _
    have h2 : thetaDenomFn j = 301994 :=
      getD_of_length_le (by simp; omega) _
    have h3 : thetaQuotFn (j + 1) = 1 :=
      getD_of_length_le (by simp; omega) _
    simp [h1, h2, h3]

/-- **Window-independent digit cap** (Paper A Theorem 5.8,
digit-cap step): every `L < 301994` has greedy Ostrowski digit sum
at most `47 = a₁ + ⋯ + a₁₃` over the certified blocks. Structural —
no scan. -/
theorem theta_digitSum_le {L : ℕ} (hL : L < 301994) :
    ∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i ≤ 47 := by
  have hq13 : thetaDenomFn (12 + 1) = 301994 := by decide
  have h := ostro_digitSum_le thetaDenomFn thetaQuotFn (by decide)
    thetaDenomFn_mono thetaDenomFn_rec (n := 12) (L := L) (by omega)
  have hsum : ∑ i ∈ Finset.range (12 + 1), thetaQuotFn (12 - i + 1) = 47 := by
    decide
  calc ∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i
      = ∑ i ∈ Finset.range (12 + 1), ostroDigit thetaDenomFn L 12 i := rfl
    _ ≤ ∑ i ∈ Finset.range (12 + 1), thetaQuotFn (12 - i + 1) := h
    _ = 47 := hsum

/-- Exact decomposition on the window: the greedy digits over the
certified denominators reconstruct `L`. -/
theorem theta_sum_eq (L : ℕ) :
    L = ∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i *
      thetaDenomFn (12 - i) :=
  ostro_sum_eq thetaDenomFn (by decide) L 12

/-- The function-form digits agree with the fold-form
`greedyDigitSum` of `OstrowskiSandwich.lean` everywhere below the
window endpoint, so the scan cap `37` and the structural cap `47`
speak about the same object. -/
theorem greedy_eq_ostro_below_window :
    ((List.range 301994).all fun L =>
      decide (greedyDigitSum L =
        ∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i)) = true := by
  native_decide

/-- Fold-form corollary: every `L < 301994` has
`greedyDigitSum L ≤ 47`, structurally. -/
theorem greedyDigitSum_le {L : ℕ} (hL : L < 301994) :
    greedyDigitSum L ≤ 47 := by
  have hall := List.all_eq_true.mp greedy_eq_ostro_below_window L
    (List.mem_range.mpr hL)
  have heq := of_decide_eq_true hall
  have := theta_digitSum_le hL
  omega

end Problems.Juggler
