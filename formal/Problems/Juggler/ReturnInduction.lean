import Problems.Juggler.EvenCountThree

namespace Problems.Juggler.ReturnInduction

/-- The two-interval presentation of rotation by `b` on `a+b` ranks. -/
def rankStep (a b i : ℕ) : ℕ := if i < a then i + b else i - a

theorem rankStep_invariant {a b i : ℕ} (hi : i < a + b) :
    rankStep a b i < a + b := by
  unfold rankStep
  split_ifs <;> omega

/-- Exact positive first return to the prefix of length `a`, when `b<a`.
The words on the two new branches are respectively `A` and `AB`. -/
theorem left_subtractive_first_return {a b i : ℕ}
    (_hb : 0 < b) (hba : b < a) (hi : i < a) :
    let k := if i < a - b then 1 else 2
    (rankStep a b)^[k] i = rankStep (a - b) b i ∧
      rankStep (a - b) b i < a ∧
      (∀ j, 0 < j → j < k → a ≤ (rankStep a b)^[j] i) := by
  by_cases hic : i < a - b
  · simp only [hic, if_true, Function.iterate_one]
    have ha : i < a := hi
    simp only [rankStep, if_pos ha, if_pos hic]
    exact ⟨True.intro, by omega, by intro j hj hj1; omega⟩
  · simp only [hic, if_false]
    have hsecond : ¬ i + b < a := by omega
    have htwo : (rankStep a b)^[2] i = i - (a - b) := by
      change rankStep a b (rankStep a b i) = i - (a - b)
      simp only [rankStep, if_pos hi, if_neg hsecond]
      omega
    have hnew : rankStep (a - b) b i = i - (a - b) := by simp [rankStep, hic]
    refine ⟨htwo.trans hnew.symm, by rw [hnew]; omega, ?_⟩
    intro j hj hj2
    have hj1 : j = 1 := by omega
    subst j
    simp only [Function.iterate_one, rankStep, if_pos hi]
    omega

/-- Exact positive first return to the prefix of length `b`, when `a<b`.
The words on the two new branches are respectively `AB` and `B`. -/
theorem right_subtractive_first_return {a b i : ℕ}
    (ha : 0 < a) (hab : a < b) (hi : i < b) :
    let k := if i < a then 2 else 1
    (rankStep a b)^[k] i = rankStep a (b - a) i ∧
      rankStep a (b - a) i < b ∧
      (∀ j, 0 < j → j < k → b ≤ (rankStep a b)^[j] i) := by
  by_cases hia : i < a
  · simp only [hia, if_true]
    have hsecond : ¬ i + b < a := by omega
    have htwo : (rankStep a b)^[2] i = i + (b - a) := by
      change rankStep a b (rankStep a b i) = i + (b - a)
      simp only [rankStep, if_pos hia, if_neg hsecond]
      omega
    have hnew : rankStep a (b - a) i = i + (b - a) := by simp [rankStep, hia]
    refine ⟨htwo.trans hnew.symm, by rw [hnew]; omega, ?_⟩
    intro j hj hj2
    have hj1 : j = 1 := by omega
    subst j
    simp only [Function.iterate_one, rankStep, if_pos hia]
    omega
  · simp only [hia, if_false, Function.iterate_one]
    simp only [rankStep, if_neg hia]
    exact ⟨True.intro, by omega, by intro j hj hj1; omega⟩

/-- At equality the first return is `AB` and the induced rank map is fixed. -/
theorem equal_first_return {a i : ℕ} (hi : i < a) :
    (rankStep a a)^[2] i = i ∧ a ≤ rankStep a a i := by
  have hsecond : ¬ i + a < a := by omega
  change rankStep a a (rankStep a a i) = i ∧ a ≤ rankStep a a i
  simp only [rankStep, if_pos hi, if_neg hsecond]
  omega

theorem left_weight {a b u v : ℕ} (hba : b ≤ a) :
    (a - b) * u + b * (u + v) = a * u + b * v := by
  have := Nat.sub_add_cancel hba
  nlinarith

theorem right_weight {a b u v : ℕ} (hab : a ≤ b) :
    a * (u + v) + (b - a) * v = a * u + b * v := by
  have := Nat.sub_add_cancel hab
  nlinarith

/-- The first substitution preserves total expanded length and both letter counts. -/
theorem left_word_statistics {a b : ℕ} (hba : b ≤ a) (A B : List Branch) :
    (a - b) * A.length + b * (A ++ B).length = a * A.length + b * B.length ∧
      (a - b) * oddCount A + b * oddCount (A ++ B) =
        a * oddCount A + b * oddCount B ∧
      (a - b) * evenCount A + b * evenCount (A ++ B) =
        a * evenCount A + b * evenCount B := by
  simp only [List.length_append, oddCount_append, evenCount_append]
  exact ⟨left_weight hba, left_weight hba, left_weight hba⟩

/-- The second substitution preserves the same three expanded statistics. -/
theorem right_word_statistics {a b : ℕ} (hab : a ≤ b) (A B : List Branch) :
    a * (A ++ B).length + (b - a) * B.length = a * A.length + b * B.length ∧
      a * oddCount (A ++ B) + (b - a) * oddCount B =
        a * oddCount A + b * oddCount B ∧
      a * evenCount (A ++ B) + (b - a) * evenCount B =
        a * evenCount A + b * evenCount B := by
  simp only [List.length_append, oddCount_append, evenCount_append]
  exact ⟨right_weight hab, right_weight hab, right_weight hab⟩

end Problems.Juggler.ReturnInduction
