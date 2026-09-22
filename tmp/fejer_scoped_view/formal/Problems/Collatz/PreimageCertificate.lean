import Problems.Collatz.PreimageGrowth

/-! Exact finite residue checks imply the weight system on actual signed roots. -/
namespace Problems.Collatz.PreimageCertificate

open PreimageScale PreimageGrowth

def Row (c : ℕ → ℕ) (i : ℕ) : Prop :=
  let m := 3 * i + 1
  let c4 := c (4 * m % 531441)
  let b := (2 * m + 1) / 3 % 177147
  let d := (4 * m + 2) / 3 % 177147
  let cb := min (c b) (min (c (b + 177147)) (c (b + 354294)))
  let cd := min (c d) (min (c (d + 177147)) (c (d + 354294)))
  1 ≤ c m ∧ c m ≤ 1000000000000 ∧
    (m % 9 = 4 → c m * 5059^100 ≤ c4 * 5000^100) ∧
    (m % 9 = 7 → c m * 5059^100 ≤ c4 * 5000^100 + cd * (5059^79 * 5000^21)) ∧
    (m % 9 = 1 → c m * 5059^100 * 5000^29 ≤ c4 * 5000^129 + cb * 5059^129)

theorem min_lifts_le (c : ℕ → ℕ) (b : ℕ) :
    min (c (b % 177147)) (min (c (b % 177147 + 177147))
      (c (b % 177147 + 354294))) ≤ c (b % 531441) := by
  have hmod : b % 531441 % 177147 = b % 177147 :=
    Nat.mod_mod_of_dvd _ (by norm_num)
  have h : b % 531441 = b % 177147 ∨
      b % 531441 = b % 177147 + 177147 ∨
      b % 531441 = b % 177147 + 354294 := by omega
  rcases h with h | h | h <;> rw [h]
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- No estimate on a class infimum is used; the actual child's lift is selected. -/
theorem weightSystem_of_rows (c : ℕ → ℕ) (hc : ∀ i < 177147, Row c i) :
    WeightSystem 5059 5000 1000000000000 (fun a => c (a % 531441)) := by
  have hrow : ∀ a, a % 3 = 1 → Row c (a % 531441 / 3) := by
    intro a ha
    exact hc _ (by omega)
  constructor
  · intro a ha
    have h := hrow a ha
    have hm : 3 * (a % 531441 / 3) + 1 = a % 531441 := by omega
    simp only [Row, hm] at h
    exact ⟨h.1, h.2.1⟩
  · intro a ha
    have h := hrow a ha
    have hm : 3 * (a % 531441 / 3) + 1 = a % 531441 := by omega
    simp only [Row, hm] at h
    have h9 : a % 531441 % 9 = a % 9 := Nat.mod_mod_of_dvd _ (by norm_num)
    have h4 : 4 * (a % 531441) % 531441 = 4 * a % 531441 := by omega
    have he := (minus_preimage_exact ha).1
    have ho : minusOddPreimage a % 177147 =
        (2 * (a % 531441) + 1) / 3 % 177147 := by omega
    have hd : (2 * minusOddPreimage a) % 177147 =
        (4 * (a % 531441) + 2) / 3 % 177147 := by omega
    have hlo := min_lifts_le c (minusOddPreimage a)
    have hld := min_lifts_le c (2 * minusOddPreimage a)
    rw [ho] at hlo
    rw [hd] at hld
    rw [h9, h4] at h
    refine ⟨h.2.2.1, ?_, ?_⟩
    · intro h7
      exact (h.2.2.2.1 h7).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hld) _)
    · intro h1
      exact (h.2.2.2.2 h1).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlo) _)

end Problems.Collatz.PreimageCertificate
