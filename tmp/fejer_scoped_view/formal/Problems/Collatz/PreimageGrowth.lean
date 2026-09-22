import Problems.Collatz.PreimageDomain

/-!
# Growth from a signed grid weight certificate

The root induction and integer power normalization adapt M. Sharpe's
MIT-licensed Collatz/KLGrid.lean. The signed recurrences and closed domain
are the locally proved PreimageGrid and PreimageDomain modules.
https://github.com/msharpe248/collatz/blob/main/lean/Collatz/KLGrid.lean

MIT License, Copyright (c) 2026 M. Sharpe

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

namespace Problems.Collatz.PreimageGrowth

open PreimageScale PreimageGrid PreimageDomain

/-- A weight system on actual fertile roots; finite residue tables can supply it. -/
def WeightSystem (p q Cmax : ℕ) (w : ℕ → ℕ) : Prop :=
  (∀ a, a % 3 = 1 → 1 ≤ w a ∧ w a ≤ Cmax) ∧
  ∀ a, a % 3 = 1 →
    (a % 9 = 4 → w a * p^100 ≤ w (4*a) * q^100) ∧
    (a % 9 = 7 → w a * p^100 ≤ w (4*a) * q^100 +
      w (2 * minusOddPreimage a) * (p^79 * q^21)) ∧
    (a % 9 = 1 → w a * p^100 * q^29 ≤ w (4*a) * q^129 +
      w (minusOddPreimage a) * p^129)

theorem count_pos {a X : ℕ} (ha : 1 ≤ a) (hX : a ≤ X) : 1 ≤ count a X := by
  classical
  apply Finset.one_le_card.mpr
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha, hX⟩, ?_⟩⟩
  refine ⟨0, rfl, ?_⟩
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  exact hX

theorem pow_swap {p q t : ℕ} (hpq : q ≤ p) (ht : t ≤ 100) :
    p^t * q^100 ≤ q^t * p^100 := by
  have hp : p^100 = p^t * p^(100-t) := by rw [← pow_add]; congr 1; omega
  have hq : q^100 = q^t * q^(100-t) := by rw [← pow_add]; congr 1; omega
  rw [hp, hq]
  calc p^t * (q^t * q^(100-t)) = (p^t * q^t) * q^(100-t) := by ring
    _ ≤ (p^t * q^t) * p^(100-t) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpq _)
    _ = q^t * (p^t * p^(100-t)) := by ring

/-- A certificate forces growth throughout the closed actual inverse-tree domain. -/
theorem growth_root {r p q Cmax : ℕ} {w : ℕ → ℕ}
    (hpq : q ≤ p) (hq : 1 ≤ q) (hw : WeightSystem p q Cmax w)
    (hd : ∀ a, Roots r a → 4096 ≤ a ∧ Nonperiodic a) :
    ∀ t a, Roots r a → w a * p^t * q^100 ≤
      count a (cap t * a) * (Cmax * q^t * p^100) := by
  have hg : ∀ n t a, measure t a = n → Roots r a →
      w a * p^t * q^100 ≤ count a (cap t * a) * (Cmax * q^t * p^100) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t a hn ha
      have had := hd a ha
      have hb := hw.1 a ha.1
      have hcnt : 1 ≤ count a (cap t * a) :=
        count_pos (by omega) (by nlinarith [cap_ge_four t])
      rcases lt_or_ge t 100 with ht | ht
      · calc w a * p^t * q^100 = w a * (p^t * q^100) := by ring
          _ ≤ Cmax * (p^t * q^100) := Nat.mul_le_mul_right _ hb.2
          _ ≤ Cmax * (q^t * p^100) := Nat.mul_le_mul_left _ (pow_swap hpq (by omega))
          _ = 1 * (Cmax * q^t * p^100) := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ hcnt
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 100 := ⟨t-100, by omega⟩
        have hm := measure_children had.1 ha.1 s
        have ih4 := ih (measure s (4*a)) (by omega) s (4*a) rfl (roots_four ha)
        have hc := hw.2 a ha.1
        have hcases : a % 9 = 4 ∨ a % 9 = 7 ∨ a % 9 = 1 := by have := ha.1; omega
        rcases hcases with h4 | h7 | h1
        · have hrec := count_four a s
          calc w a * p^(s+100) * q^100 = (w a * p^100) * (p^s * q^100) := by ring
            _ ≤ (w (4*a) * q^100) * (p^s * q^100) := Nat.mul_le_mul_right _ (hc.1 h4)
            _ = (w (4*a) * p^s * q^100) * q^100 := by ring
            _ ≤ (count (4*a) (cap s * (4*a)) * (Cmax * q^s * p^100)) * q^100 :=
              Nat.mul_le_mul_right _ ih4
            _ = count (4*a) (cap s * (4*a)) * (Cmax * q^(s+100) * p^100) := by ring
            _ ≤ _ := Nat.mul_le_mul_right _ hrec
        · have ih2 := ih (measure (s+79) (2 * minusOddPreimage a)) (by omega)
            (s+79) (2 * minusOddPreimage a) rfl (roots_doubled_odd ha h7)
          have hrec := count_doubled_odd (t := s) had.1 ha.1 had.2
          calc w a * p^(s+100) * q^100 = (w a * p^100) * (p^s * q^100) := by ring
            _ ≤ (w (4*a) * q^100 + w (2 * minusOddPreimage a) * (p^79 * q^21)) *
                (p^s * q^100) := Nat.mul_le_mul_right _ (hc.2.1 h7)
            _ = (w (4*a) * p^s * q^100) * q^100 +
                (w (2 * minusOddPreimage a) * p^(s+79) * q^100) * q^21 := by ring
            _ ≤ (count (4*a) (cap s * (4*a)) * (Cmax * q^s * p^100)) * q^100 +
                (count (2 * minusOddPreimage a) (cap (s+79) * (2 * minusOddPreimage a)) *
                  (Cmax * q^(s+79) * p^100)) * q^21 :=
              Nat.add_le_add (Nat.mul_le_mul_right _ ih4) (Nat.mul_le_mul_right _ ih2)
            _ = (count (4*a) (cap s * (4*a)) +
                count (2 * minusOddPreimage a) (cap (s+79) * (2 * minusOddPreimage a))) *
                (Cmax * q^(s+100) * p^100) := by ring
            _ ≤ _ := Nat.mul_le_mul_right _ hrec
        · have iho := ih (measure (s+129) (minusOddPreimage a)) (by omega)
            (s+129) (minusOddPreimage a) rfl (roots_odd ha h1)
          have hrec := count_odd (t := s) had.1 ha.1 had.2
          have hq29 : 0 < q^29 := by positivity
          apply Nat.le_of_mul_le_mul_right (c := q^29) _ hq29
          calc (w a * p^(s+100) * q^100) * q^29 =
                (w a * p^100 * q^29) * (p^s * q^100) := by ring
            _ ≤ (w (4*a) * q^129 + w (minusOddPreimage a) * p^129) *
                (p^s * q^100) := Nat.mul_le_mul_right _ (hc.2.2 h1)
            _ = (w (4*a) * p^s * q^100) * q^129 +
                (w (minusOddPreimage a) * p^(s+129) * q^100) := by ring
            _ ≤ (count (4*a) (cap s * (4*a)) * (Cmax * q^s * p^100)) * q^129 +
                (count (minusOddPreimage a) (cap (s+129) * minusOddPreimage a) *
                  (Cmax * q^(s+129) * p^100)) :=
              Nat.add_le_add (Nat.mul_le_mul_right _ ih4) iho
            _ = ((count (4*a) (cap s * (4*a)) +
                count (minusOddPreimage a) (cap (s+129) * minusOddPreimage a)) *
                (Cmax * q^(s+100) * p^100)) * q^29 := by ring
            _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hrec)
  exact fun t a ha => hg (measure t a) t a rfl ha

/-- The grid growth reaches every positive unit target, including cycle members. -/
theorem growth_for_target {p q Cmax : ℕ} {w : ℕ → ℕ}
    (hpq : q ≤ p) (hq : 1 ≤ q) (hw : WeightSystem p q Cmax w)
    {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    ∃ r X₀, 4096 ≤ r ∧ 1 ≤ w r ∧ ∀ t, X₀ ≤ cap t * r →
      w r * p^t * q^100 ≤ count a (cap t * r) * (Cmax * q^t * p^100) := by
  obtain ⟨r, hr, _, hd, X₀, hX₀⟩ := closed_domain_for_target ha ha3
  refine ⟨r, X₀, (hd r hr).1, (hw.1 r hr.1).1, ?_⟩
  intro t ht
  exact (growth_root hpq hq hw hd t r hr).trans
    (Nat.mul_le_mul_right _ (hX₀ (cap t * r) ht))

end Problems.Collatz.PreimageGrowth
