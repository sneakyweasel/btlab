import Problems.Collatz.PreimageGrowth
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! A strict rational grid rate gives an eventual ordinary ancestor bound.
The conclusion is stated with integer powers, so no numerical logarithm
or floating-point exponent comparison enters the proof. -/
namespace Problems.Collatz.PreimageDensity

open PreimageGrid PreimageGrowth

noncomputable def ancestorCount (a X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter (fun n => PreimageDomain.Reaches n a)).card

theorem capped_count_le_ancestorCount (a X : ℕ) : count a X ≤ ancestorCount a X := by
  classical
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hn, k, hk, _⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hn, k, hk⟩

theorem eventually_mul_pow_le {A B : ℕ} (hB : 0 < B) (hAB : B < A) (K : ℕ) :
    ∃ J, ∀ j, J ≤ j → K * B^j ≤ A^j := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr : (1 : ℝ) < (A : ℝ) / B := (lt_div_iff₀ hBr).mpr (by
    simpa only [one_mul] using (show (B : ℝ) < A by exact_mod_cast hAB))
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (K : ℝ) hr
  rw [div_pow] at hJ
  have hb : K * B^J ≤ A^J := by
    exact_mod_cast ((lt_div_iff₀ (pow_pos hBr J)).mp hJ).le
  refine ⟨J, ?_⟩
  intro j hj
  obtain ⟨s, rfl⟩ : ∃ s, j = J + s := ⟨j-J, by omega⟩
  calc K * B^(J+s) = (K * B^J) * B^s := by ring
    _ ≤ A^J * A^s := Nat.mul_le_mul hb (Nat.pow_le_pow_left hAB.le s)
    _ = A^(J+s) := (pow_add _ _ _).symm

/-- Interpolate a dyadic count bound and absorb its fixed constants. -/
theorem density_of_dyadic_growth (F : ℕ → ℕ) (hF : Monotone F)
    {A Q B D d e J₀ : ℕ} (hQ : 0 < Q) (hB : 0 < B) (hD : 0 < D)
    (hgap : 2^e * Q < A)
    (hgrid : ∀ j, J₀ ≤ j → A^j ≤ F (B * 2^j)^d * D * Q^j) :
    ∃ X₀, ∀ X, X₀ ≤ X → X^e ≤ (F X)^d := by
  obtain ⟨J, hJ⟩ := eventually_mul_pow_le (by positivity : 0 < 2^e * Q)
    hgap ((2*B)^e * D)
  let L := max J J₀
  refine ⟨B * 2^L, ?_⟩
  intro X hX
  have hdiv : 2^L ≤ X / B := (Nat.le_div_iff_mul_le hB).mpr (by nlinarith)
  let j := Nat.log 2 (X / B)
  have hLj : L ≤ j := Nat.le_log_of_pow_le (by norm_num) hdiv
  have hdivpos : X / B ≠ 0 := by have := Nat.one_le_two_pow (n := L); omega
  have hlo : 2^j ≤ X / B := Nat.pow_log_le_self 2 hdivpos
  have hhi : X / B < 2^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hYX : B * 2^j ≤ X := by
    have := Nat.div_mul_le_self X B
    nlinarith
  have hXY : X ≤ 2*B*2^j := by
    have hrem := Nat.mod_lt X hB
    have hdecomp := Nat.mod_add_div X B
    rw [pow_succ] at hhi
    nlinarith
  have hlow := hJ j (by dsimp [L] at hLj; omega)
  have hupp := hgrid j (by dsimp [L] at hLj; omega)
  have hpow : (2*B*2^j)^e ≤ F (B*2^j)^d := by
    apply Nat.le_of_mul_le_mul_right (c := D * Q^j) _ (by positivity)
    calc (2*B*2^j)^e * (D*Q^j) = ((2*B)^e * D) * (2^e * Q)^j := by
          simp only [mul_pow]
          ring
      _ ≤ A^j := hlow
      _ ≤ F (B*2^j)^d * (D*Q^j) := by simpa only [mul_assoc] using hupp
  exact (Nat.pow_le_pow_left hXY e).trans
    (hpow.trans (Nat.pow_le_pow_left (hF hYX) d))

theorem cap_dyadic (j : ℕ) : cap (50*j) = 10000 * 2^j := by
  simp [cap, rung, table, mul_comm]

/-- The certificate's strict rate absorbs every fixed root and cutoff constant. -/
theorem density_of_weight_system {p q Cmax d e : ℕ} {w : ℕ → ℕ}
    (hpq : q ≤ p) (hq : 1 ≤ q) (hw : WeightSystem p q Cmax w)
    (hgap : 2^e * q^(50*d) < p^(50*d))
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    ∃ X₀, ∀ X, X₀ ≤ X → X^e ≤ (count a X)^d := by
  obtain ⟨r, X₀, hr, hwr, hg⟩ := growth_for_target hpq hq hw ha ha3
  have hp : 0 < p := by omega
  have hC : 0 < Cmax := by
    have h1 := hw.1 1 (by norm_num)
    omega
  let B := 10000*r
  have hB : 0 < B := by dsimp [B]; positivity
  apply density_of_dyadic_growth (count a) (fun _ _ h => count_mono h)
    (A := p^(50*d)) (Q := q^(50*d)) (B := B) (D := (Cmax*p^100)^d) (J₀ := X₀)
    (by positivity) hB (by positivity) hgap
  intro j hj
  have htwoall : ∀ v : ℕ, v ≤ 2^v := by
    intro v
    induction v with
    | zero => norm_num
    | succ v ih =>
        rw [pow_succ]
        have := Nat.one_le_two_pow (n := v)
        omega
  have htwo := htwoall j
  have hX : X₀ ≤ cap (50*j) * r := by
    rw [cap_dyadic]
    nlinarith
  have hcount := hg (50*j) hX
  rw [cap_dyadic] at hcount
  have hY : 10000 * 2^j * r = B * 2^j := by dsimp [B]; ring
  rw [hY] at hcount
  have hplain : p^(50*j) ≤ count a (B*2^j) * (Cmax*p^100) * q^(50*j) := by
    have hpow : 1 ≤ q^100 := Nat.one_le_pow _ _ hq
    calc p^(50*j) ≤ w r * p^(50*j) := Nat.le_mul_of_pos_left _ hwr
      _ ≤ w r * p^(50*j) * q^100 := Nat.le_mul_of_pos_right _ hpow
      _ ≤ count a (B*2^j) * (Cmax*q^(50*j)*p^100) := hcount
      _ = _ := by ring
  calc (p^(50*d))^j = (p^(50*j))^d := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
    _ ≤ (count a (B*2^j) * (Cmax*p^100) * q^(50*j))^d := Nat.pow_le_pow_left hplain d
    _ = (count a (B*2^j))^d * (Cmax*p^100)^d * (q^(50*d))^j := by
        simp only [mul_pow]
        congr 1
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring

end Problems.Collatz.PreimageDensity
