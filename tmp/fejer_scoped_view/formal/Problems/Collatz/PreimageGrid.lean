import Problems.Collatz.PreimageScale
import Mathlib.Data.Nat.Log

/-!
# Actual signed inverse trees on a grid with strict slack

The cap table and the root-induction measure follow M. Sharpe's MIT-licensed
`Collatz/Grid50.lean` and `Collatz/KLGrid.lean`:
https://github.com/msharpe248/collatz/tree/main/lean/Collatz
The signed cutoff comparison below is different: it retains `2*a+1` and
uses `a >= 4096`. No growth certificate or small-root boundary is assumed
to have been discharged.

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

namespace Problems.Collatz.PreimageGrid

set_option exponentiation.threshold 1000

open PreimageScale
open scoped Classical

def TreeMem (a X n : ℕ) : Prop :=
  ∃ j, (negT^[j]) n = a ∧ ∀ i ≤ j, (negT^[i]) n ≤ X

noncomputable def tree (a X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (TreeMem a X)

noncomputable def count (a X : ℕ) : ℕ := (tree a X).card

def Nonperiodic (a : ℕ) : Prop := ∀ d, 0 < d → (negT^[d]) a ≠ a

theorem tree_mono {a X Y : ℕ} (hXY : X ≤ Y) : tree a X ⊆ tree a Y := by
  intro n hn
  obtain ⟨hn, j, hj, hb⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
    (Finset.mem_Icc.mp hn).2.trans hXY⟩, j, hj, fun i hi => (hb i hi).trans hXY⟩

theorem count_mono {a X Y : ℕ} (hXY : X ≤ Y) : count a X ≤ count a Y :=
  Finset.card_le_card (tree_mono hXY)

theorem tree_extend {a b X : ℕ} (hab : TreeMem a X b) : tree b X ⊆ tree a X := by
  intro n hn
  obtain ⟨hn, j, hj, hb⟩ := Finset.mem_filter.mp hn
  obtain ⟨k, hk, ha⟩ := hab
  apply Finset.mem_filter.mpr
  refine ⟨hn, k + j, by rw [Function.iterate_add_apply, hj, hk], ?_⟩
  intro i hi
  by_cases hij : i ≤ j
  · exact hb i hij
  · rw [show i = (i - j) + j by omega, Function.iterate_add_apply, hj]
    exact ha (i - j) (by omega)

theorem hit_time_unique {a n i j : ℕ} (ha : Nonperiodic a)
    (hi : (negT^[i]) n = a) (hj : (negT^[j]) n = a) : i = j := by
  have hordered : ∀ p q, p ≤ q → (negT^[p]) n = a → (negT^[q]) n = a → p = q := by
    intro p q hpq hp hq
    by_contra hne
    apply ha (q - p) (by omega)
    calc
      (negT^[q - p]) a = (negT^[q - p]) ((negT^[p]) n) := by rw [hp]
      _ = (negT^[q]) n := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hpq]
      _ = a := hq
  rcases le_total i j with h | h
  · exact hordered i j h hi hj
  · exact (hordered j i h hj hi).symm

theorem negT_double (a : ℕ) : negT (2 * a) = a := by simp [negT]

theorem negT_four (a : ℕ) : (negT^[2]) (4 * a) = a := by
  simp [show 4 * a = 2 * (2 * a) by omega, Function.iterate_succ_apply, negT_double]

theorem four_path {a X : ℕ} (hX : 4 * a ≤ X) : TreeMem a X (4 * a) := by
  refine ⟨2, ?_, ?_⟩
  · norm_num [show 4 * a = 2 * (2 * a) by omega, Function.iterate_succ_apply,
      negT_double]
  · intro i hi
    interval_cases i <;>
      simp [show 4 * a = 2 * (2 * a) by omega, Function.iterate_succ_apply,
        negT_double] <;> omega

theorem odd_path {a X : ℕ} (ha : a % 3 = 1) (hX : 4 * a ≤ X) :
    TreeMem a X (minusOddPreimage a) := by
  have he := minus_preimage_exact ha
  refine ⟨1, by simpa using he.2.2, ?_⟩
  intro i hi
  interval_cases i <;> simp [he.2.2] <;> omega

theorem doubled_odd_path {a X : ℕ} (ha : a % 3 = 1) (hX : 4 * a ≤ X) :
    TreeMem a X (2 * minusOddPreimage a) := by
  have he := minus_preimage_exact ha
  refine ⟨2, ?_, ?_⟩
  · simpa [Function.iterate_succ_apply, negT_double] using he.2.2
  · intro i hi
    interval_cases i <;> simp [Function.iterate_succ_apply, negT_double, he.2.2] <;> omega

/-- The two actual subtrees are disjoint at a nonperiodic root. -/
theorem odd_trees_disjoint {a X : ℕ} (ha : a % 3 = 1) (hnp : Nonperiodic a) :
    Disjoint (tree (4 * a) X) (tree (minusOddPreimage a) X) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  obtain ⟨_, j, hj, _⟩ := Finset.mem_filter.mp hn
  obtain ⟨_, k, hk, _⟩ := Finset.mem_filter.mp hm
  have he := minus_preimage_exact ha
  have h4 := negT_four a
  have hja : (negT^[2 + j]) n = a := by rw [Function.iterate_add_apply, hj, h4]
  have hka : (negT^[1 + k]) n = a := by
    rw [Function.iterate_add_apply, hk]
    simpa using he.2.2
  have ht := hit_time_unique hnp hja hka
  have hk' : (negT^[k]) n = 2 * a := by
    rw [show k = 1 + j by omega, Function.iterate_add_apply, hj]
    simp [show 4 * a = 2 * (2 * a) by omega, negT_double]
  have : minusOddPreimage a = 2 * a := hk.symm.trans hk'
  omega

theorem doubled_odd_trees_disjoint {a X : ℕ} (ha : a % 3 = 1)
    (hnp : Nonperiodic a) :
    Disjoint (tree (4 * a) X) (tree (2 * minusOddPreimage a) X) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  obtain ⟨_, j, hj, _⟩ := Finset.mem_filter.mp hn
  obtain ⟨_, k, hk, _⟩ := Finset.mem_filter.mp hm
  have he := minus_preimage_exact ha
  have h4 := negT_four a
  have ho : (negT^[2]) (2 * minusOddPreimage a) = a := (two_step_preimage ha).1
  have hja : (negT^[2 + j]) n = a := by rw [Function.iterate_add_apply, hj, h4]
  have hka : (negT^[2 + k]) n = a := by rw [Function.iterate_add_apply, hk, ho]
  have ht := hit_time_unique hnp hja hka
  have hjk : j = k := by omega
  rw [hjk, hk] at hj
  omega

theorem count_split {a u v X : ℕ} (hu : TreeMem a X u) (hv : TreeMem a X v)
    (hd : Disjoint (tree u X) (tree v X)) : count u X + count v X ≤ count a X := by
  rw [count, count, ← Finset.card_union_of_disjoint hd]
  exact Finset.card_le_card (Finset.union_subset (tree_extend hu) (tree_extend hv))

def table : List ℕ :=
  [10000, 10140, 10281, 10425, 10570, 10718, 10867, 11019, 11173, 11329,
   11487, 11647, 11810, 11975, 12142, 12311, 12483, 12658, 12834, 13013,
   13195, 13379, 13566, 13755, 13947, 14142, 14340, 14540, 14743, 14948,
   15157, 15369, 15583, 15801, 16021, 16245, 16472, 16702, 16935, 17171,
   17411, 17654, 17901, 18150, 18404, 18661, 18921, 19185, 19453, 19725]

def rung (j : ℕ) : ℕ := table.getD j 10000
def cap (t : ℕ) : ℕ := 2 ^ (t / 50) * rung (t % 50)

theorem cap_ge_four (t : ℕ) : 4 ≤ cap t := by
  have hr : ∀ j < 50, 10000 ≤ rung j := by decide
  have hp : 1 ≤ 2 ^ (t / 50) := Nat.one_le_two_pow
  have hj := hr (t % 50) (Nat.mod_lt _ (by norm_num))
  unfold cap
  nlinarith

theorem cap_quad (t : ℕ) : cap (t + 100) = 4 * cap t := by
  unfold cap
  rw [show (t + 100) / 50 = t / 50 + 2 by omega,
    show (t + 100) % 50 = t % 50 by omega, pow_add]
  ring

/-- Strict slack, strengthened to absorb the signed offset at roots ≥ 4096. -/
theorem cap_signed_advance (t : ℕ) : 8193 * cap (t + 29) ≤ 12288 * cap t := by
  have htab : ∀ j < 50,
      8193 * (2 ^ ((j + 29) / 50) * rung ((j + 29) % 50)) ≤ 12288 * rung j := by decide
  have hj := htab (t % 50) (Nat.mod_lt _ (by norm_num))
  have hd : (t + 29) / 50 = t / 50 + (t % 50 + 29) / 50 := by omega
  have hm : (t + 29) % 50 = (t % 50 + 29) % 50 := by omega
  unfold cap
  rw [hd, hm, pow_add]
  nlinarith [Nat.mul_le_mul_left (2 ^ (t / 50)) hj]

theorem cap_signed_retard (t : ℕ) : 16386 * cap t ≤ 12288 * cap (t + 21) := by
  have htab : ∀ j < 50,
      16386 * rung j ≤ 12288 * (2 ^ ((j + 21) / 50) * rung ((j + 21) % 50)) := by decide
  have hj := htab (t % 50) (Nat.mod_lt _ (by norm_num))
  have hd : (t + 21) / 50 = t / 50 + (t % 50 + 21) / 50 := by omega
  have hm : (t + 21) % 50 = (t % 50 + 21) % 50 := by omega
  unfold cap
  rw [hd, hm, pow_add]
  nlinarith [Nat.mul_le_mul_left (2 ^ (t / 50)) hj]

theorem signed_child_ratio {a b : ℕ} (ha : 4096 ≤ a) (hb : 3 * b = 2 * a + 1) :
    12288 * b ≤ 8193 * a := by omega

theorem odd_cap_fits {a t : ℕ} (ha : 4096 ≤ a) (h3 : a % 3 = 1) :
    cap (t + 129) * minusOddPreimage a ≤ cap (t + 100) * a := by
  have hb := signed_child_ratio ha (minus_preimage_exact h3).1
  have hc := cap_signed_advance (t + 100)
  rw [show t + 100 + 29 = t + 129 by omega] at hc
  nlinarith [Nat.mul_le_mul_left (cap (t + 129)) hb, Nat.mul_le_mul_right a hc]

theorem doubled_odd_cap_fits {a t : ℕ} (ha : 4096 ≤ a) (h3 : a % 3 = 1) :
    cap (t + 79) * (2 * minusOddPreimage a) ≤ cap (t + 100) * a := by
  have hb := signed_child_ratio ha (minus_preimage_exact h3).1
  have hc := cap_signed_retard (t + 79)
  rw [show t + 79 + 21 = t + 100 by omega] at hc
  nlinarith [Nat.mul_le_mul_left (2 * cap (t + 79)) hb, Nat.mul_le_mul_right a hc]

theorem count_four (a t : ℕ) :
    count (4 * a) (cap t * (4 * a)) ≤ count a (cap (t + 100) * a) := by
  have hX : cap t * (4 * a) = cap (t + 100) * a := by rw [cap_quad]; ring
  rw [hX]
  apply Finset.card_le_card (tree_extend (four_path ?_))
  nlinarith [cap_ge_four (t + 100)]

/-- The advanced branch is retained, for actual height-truncated integer trees. -/
theorem count_odd {a t : ℕ} (ha : 4096 ≤ a) (h3 : a % 3 = 1) (hnp : Nonperiodic a) :
    count (4 * a) (cap t * (4 * a)) +
      count (minusOddPreimage a) (cap (t + 129) * minusOddPreimage a) ≤
        count a (cap (t + 100) * a) := by
  have hX : cap t * (4 * a) = cap (t + 100) * a := by rw [cap_quad]; ring
  have hb : 4 * a ≤ cap (t + 100) * a := by nlinarith [cap_ge_four (t + 100)]
  rw [hX]
  exact (Nat.add_le_add_left (count_mono (odd_cap_fits ha h3)) _).trans
    (count_split (four_path hb) (odd_path h3 hb) (odd_trees_disjoint h3 hnp))

theorem count_doubled_odd {a t : ℕ} (ha : 4096 ≤ a) (h3 : a % 3 = 1)
    (hnp : Nonperiodic a) :
    count (4 * a) (cap t * (4 * a)) +
      count (2 * minusOddPreimage a) (cap (t + 79) * (2 * minusOddPreimage a)) ≤
        count a (cap (t + 100) * a) := by
  have hX : cap t * (4 * a) = cap (t + 100) * a := by rw [cap_quad]; ring
  have hb : 4 * a ≤ cap (t + 100) * a := by nlinarith [cap_ge_four (t + 100)]
  rw [hX]
  exact (Nat.add_le_add_left (count_mono (doubled_odd_cap_fits ha h3)) _).trans
    (count_split (four_path hb) (doubled_odd_path h3 hb) (doubled_odd_trees_disjoint h3 hnp))

def rootSize (a : ℕ) : ℕ := Nat.log 2 (a ^ 498)
def measure (t a : ℕ) : ℕ := 10 * t + rootSize a

private theorem log_two_mul {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    Nat.log 2 (2 ^ k * n) = k + Nat.log 2 n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 ^ (k + 1) * n = (2 ^ k * n) * 2 by rw [pow_succ]; ring,
        Nat.log_mul_base (by norm_num) (by positivity), ih]
      omega

theorem rootSize_double {a : ℕ} (ha : 0 < a) : rootSize (2 * a) = rootSize a + 498 := by
  unfold rootSize
  rw [mul_pow, log_two_mul (by positivity)]
  omega

theorem rootSize_four {a : ℕ} (ha : 0 < a) : rootSize (4 * a) = rootSize a + 996 := by
  rw [show 4 * a = 2 * (2 * a) by omega, rootSize_double (by omega), rootSize_double ha]

/-- The numeric slack survives the plus-one in the negative-map predecessor. -/
theorem signed_power_slack : (2 : ℕ) ^ 291 * 8193 ^ 498 < 12288 ^ 498 := by norm_num

theorem rootSize_odd {a b : ℕ} (ha : 4096 ≤ a) (hb : 3 * b = 2 * a + 1) :
    rootSize b + 291 ≤ rootSize a := by
  have hbpos : 0 < b := by omega
  have hp := Nat.pow_le_pow_left (signed_child_ratio ha hb) 498
  rw [mul_pow, mul_pow] at hp
  have hs := Nat.mul_lt_mul_of_pos_right signed_power_slack
    (show 0 < b ^ 498 by positivity)
  have hlarge : 8193 ^ 498 * (2 ^ 291 * b ^ 498) < 8193 ^ 498 * a ^ 498 := by
    calc _ = (2 ^ 291 * 8193 ^ 498) * b ^ 498 := by ring
      _ < 12288 ^ 498 * b ^ 498 := hs
      _ ≤ _ := hp
  have hsmall : 2 ^ 291 * b ^ 498 < a ^ 498 := Nat.lt_of_mul_lt_mul_left hlarge
  have hl := Nat.pow_log_le_self 2 (show b ^ 498 ≠ 0 by positivity)
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 2 ^ (rootSize b + 291) = 2 ^ 291 * 2 ^ (Nat.log 2 (b ^ 498)) := by
        rw [rootSize, pow_add]; ring
    _ ≤ 2 ^ 291 * b ^ 498 := Nat.mul_le_mul_left _ hl
    _ ≤ a ^ 498 := hsmall.le

/-- All three child calls strictly lower one natural-number measure,
including the call at the advanced grid time. -/
theorem measure_children {a : ℕ} (ha : 4096 ≤ a) (h3 : a % 3 = 1) (t : ℕ) :
    measure t (4 * a) + 4 ≤ measure (t + 100) a ∧
    measure (t + 79) (2 * minusOddPreimage a) + 3 ≤ measure (t + 100) a ∧
    measure (t + 129) (minusOddPreimage a) + 1 ≤ measure (t + 100) a := by
  have he := (minus_preimage_exact h3).1
  have hf := rootSize_four (show 0 < a by omega)
  have ho := rootSize_odd ha he
  have hd := rootSize_double (show 0 < minusOddPreimage a by omega)
  unfold measure
  omega

/-- Which of the two count inequalities returns to the fertile residue classes. -/
theorem fertile_children {a : ℕ} (ha : a % 3 = 1) :
    (4 * a) % 3 = 1 ∧
    (a % 9 = 1 → minusOddPreimage a % 3 = 1) ∧
    (a % 9 = 7 → (2 * minusOddPreimage a) % 3 = 1) ∧
    (a % 9 = 4 → minusOddPreimage a % 3 = 0) := by
  have he := (minus_preimage_exact ha).1
  omega

theorem nonperiodic_preimage {a b d : ℕ} (ha : Nonperiodic a)
    (hb : (negT^[d]) b = a) : Nonperiodic b := by
  intro p hp he
  apply ha p hp
  calc
    (negT^[p]) a = (negT^[p]) ((negT^[d]) b) := by rw [hb]
    _ = (negT^[d]) ((negT^[p]) b) := by
      rw [← Function.iterate_add_apply, Nat.add_comm p d, Function.iterate_add_apply]
    _ = a := by rw [he, hb]

end Problems.Collatz.PreimageGrid
