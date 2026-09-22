import Problems.Collatz.PreimageCheck12Part0
import Problems.Collatz.PreimageCheck12Part1
import Problems.Collatz.PreimageCheck12Part2
import Problems.Collatz.PreimageCheck12Part3
import Problems.Collatz.PreimageCertificate
import Problems.Collatz.PreimageDensity

namespace Problems.Collatz.PreimageCertificate12
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000
open PreimageWeights12 PreimageGrowth PreimageCertificate

theorem all_rows : ∀ i < 177147, row i := by
  intro i hi
  by_cases h0 : i < 44288
  · exact PreimageCheck12Part0.checked i (by omega) h0
  by_cases h1 : i < 88576
  · exact PreimageCheck12Part1.checked i (by omega) h1
  by_cases h2 : i < 132864
  · exact PreimageCheck12Part2.checked i (by omega) h2
  exact PreimageCheck12Part3.checked i (by omega) hi

theorem weight_system : WeightSystem 5059 5000 1000000000000
    (fun a => c (a % 531441)) :=
  weightSystem_of_rows c all_rows

theorem target_growth {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    ∃ r X₀, 4096 ≤ r ∧ 1 ≤ c (r % 531441) ∧ ∀ t, X₀ ≤ PreimageGrid.cap t * r →
      c (r % 531441) * 5059^t * 5000^100 ≤
        PreimageGrid.count a (PreimageGrid.cap t * r) *
          (1000000000000 * 5000^t * 5059^100) :=
  growth_for_target (by norm_num) (by norm_num) weight_system ha ha3

theorem rate_gap : (2 : ℕ)^21 * 5000^1250 < 5059^1250 := by norm_num

/-- Every sufficiently large natural cutoff has at least X^(21/25) capped ancestors. -/
theorem density_21_25 {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    ∃ X₀, ∀ X, X₀ ≤ X → X^21 ≤ (PreimageGrid.count a X)^25 :=
  PreimageDensity.density_of_weight_system (p := 5059) (q := 5000) (d := 25) (e := 21)
    (by norm_num) (by norm_num)
    weight_system rate_gap ha ha3

/-- The ordinary positive ancestor count is at least the capped ancestor count. -/
theorem ancestor_density_21_25 {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :
    ∃ X₀, ∀ X, X₀ ≤ X → X^21 ≤ (PreimageDensity.ancestorCount a X)^25 := by
  obtain ⟨X₀, hX₀⟩ := density_21_25 ha ha3
  exact ⟨X₀, fun X hX => (hX₀ X hX).trans
    (Nat.pow_le_pow_left (PreimageDensity.capped_count_le_ancestorCount a X) 25)⟩

end Problems.Collatz.PreimageCertificate12
