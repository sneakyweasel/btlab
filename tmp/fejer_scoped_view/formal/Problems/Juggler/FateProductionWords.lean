/-
# Paper C's finite production words, and their prefix-freeness

Paper C (`docs/theory/juggler_fate_almost_all_note.md`) builds Theorem 1 out of six finite
productions, defined at the end of Section 5 as

  `V_k = (OE)^(k-1) OEE`,   `1 ≤ k ≤ 6`,   `rho_k = (1/2)(3/4)^k`,

and it uses their prefix-freeness twice as a load-bearing step: "Production words must be
prefix-free" when the candidate list is drawn up, "These six words are prefix-free" when the six
are fixed, and "Finally the prefix-free words give disjoint source sets, and the subtraction in
(5.9) proves (5.10)" at the end of Appendix D. Until now the assertion was written only and the
words themselves were not defined anywhere under `formal/`.

This module defines them and proves the property, for the whole family rather than for the six:
`Vword i` is a prefix of `Vword j` only when `i = j` (`Vword_prefix_iff`). The six words Paper C
uses are `Vword 0` through `Vword 5`, indexed from zero, so `Vword i` is the paper's `V_(i+1)`.

**What this is not.** It is the combinatorial step only. The analytic content of Appendix D --
the two-sided asymptotic for each fixed word, the logarithmic coefficient `c_k = 3^(-k)`, and the
landing windows with their iterated ceiling endpoints -- is written proof and is untouched here.
Disjointness of the *source sets* follows from prefix-freeness only together with that analytic
layer, which this module does not formalise. Nothing here bounds a Juggler orbit, excludes a
cycle, or proves termination.
-/
import Problems.Juggler.ItineraryStats

namespace Problems.Juggler

namespace FateProductionWords

open Branch

/-- Paper C's production words `V_k = (OE)^(k-1) OEE`, indexed from zero: `Vword i` is the
paper's `V_(i+1)`, so the six it uses are `Vword 0` through `Vword 5`. -/
def Vword : ℕ → List Branch
  | 0 => [.odd, .even, .even]
  | k + 1 => .odd :: .even :: Vword k

@[simp] theorem Vword_zero : Vword 0 = [.odd, .even, .even] := rfl

@[simp] theorem Vword_succ (k : ℕ) : Vword (k + 1) = .odd :: .even :: Vword k := rfl

/-- `V_(k+1)` has length `2k + 3`: the `k` copies of `OE` and the closing `OEE`. -/
theorem Vword_length (k : ℕ) : (Vword k).length = 2 * k + 3 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Vword_succ, List.length_cons, ih]; omega

/-- `V_(k+1)` carries `k + 1` odd letters. -/
theorem Vword_oddCount (k : ℕ) : oddCount (Vword k) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Vword_succ, oddCount_odd_cons, oddCount_even_cons, ih]

/-- Every production word starts with an odd letter. -/
theorem Vword_eq_odd_cons (k : ℕ) : ∃ t, Vword k = .odd :: t := by
  cases k with
  | zero => exact ⟨[.even, .even], rfl⟩
  | succ k => exact ⟨.even :: Vword k, rfl⟩

/-- **The production words are prefix-free.** `V_i` is a prefix of `V_j` only when `i = j`; in
particular the six words Paper C fixes, `Vword 0` through `Vword 5`, are pairwise prefix-free.
The reason is that `V_i` closes with a second `E` exactly where `V_j`, for `j > i`, opens another
`OE`. -/
theorem Vword_prefix_iff {i j : ℕ} (h : Vword i <+: Vword j) : i = j := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => rfl
    | succ k =>
      exfalso
      obtain ⟨t, ht⟩ := h
      obtain ⟨u, hu⟩ := Vword_eq_odd_cons k
      rw [Vword_zero, Vword_succ, hu] at ht
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
      exact absurd ht.2.2.1 (by simp)
  | succ i ih =>
    obtain ⟨t, ht⟩ := h
    cases j with
    | zero =>
      exfalso
      obtain ⟨u, hu⟩ := Vword_eq_odd_cons i
      rw [Vword_succ, Vword_zero, hu] at ht
      simp only [List.cons_append, List.cons.injEq] at ht
      exact absurd ht.2.2.1 (by simp)
    | succ k =>
      have hik : Vword i <+: Vword k := by
        refine ⟨t, ?_⟩
        rw [Vword_succ, Vword_succ] at ht
        simpa only [List.cons_append, List.cons.injEq, true_and] using ht
      exact congrArg Nat.succ (ih hik)

/-- The six words Paper C uses, pairwise: none is a prefix of another. Kernel evaluation. -/
theorem Vword_six_prefixFree :
    ∀ i < 6, ∀ j < 6, i ≠ j → ¬ (Vword i <+: Vword j) := by
  decide +kernel

/-- The six words, written out. `Vword 0 = OEE` and each step prepends `OE`. -/
theorem Vword_five :
    Vword 5 = [.odd, .even, .odd, .even, .odd, .even, .odd, .even, .odd, .even,
               .odd, .even, .even] := by
  decide +kernel

end FateProductionWords

end Problems.Juggler
