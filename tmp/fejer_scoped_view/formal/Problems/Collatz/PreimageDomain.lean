import Problems.Collatz.PreimageGrid
import Problems.Collatz.PreimageBarrier
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# A closed root domain for every positive unit target

Two distinct predecessors cannot both be periodic. This gives a fertile
nonperiodic ancestor for every target prime to 3, even when the target is
periodic. Doubling it above the finite barrier produces a domain whose
selected predecessors stay above the strict grid's threshold. A fixed
path transfers capped counts to the original target for all large cutoffs.
The growth induction and a numerical certificate remain separate work.
-/

namespace Problems.Collatz.PreimageDomain

open PreimageScale PreimageGrid
open scoped Classical

def Reaches (n a : ℕ) : Prop := ∃ k, (negT^[k]) n = a

theorem reaches_refl (a : ℕ) : Reaches a a := ⟨0, rfl⟩

theorem reaches_trans {a b c : ℕ} (hab : Reaches a b) (hbc : Reaches b c) :
    Reaches a c := by
  obtain ⟨j, hj⟩ := hab
  obtain ⟨k, hk⟩ := hbc
  exact ⟨k + j, by rw [Function.iterate_add_apply, hj, hk]⟩

theorem iterate_two_pow (k a : ℕ) : (negT^[k]) (2 ^ k * a) = a := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [pow_succ', mul_assoc, Function.iterate_succ_apply, negT_double, ih]

/-- Two distinct predecessors cannot both lie on cycles. -/
theorem one_nonperiodic_predecessor {a b c : ℕ} (hb : negT b = a)
    (hc : negT c = a) (hne : b ≠ c) : Nonperiodic b ∨ Nonperiodic c := by
  by_cases hnb : Nonperiodic b
  · exact Or.inl hnb
  by_cases hnc : Nonperiodic c
  · exact Or.inr hnc
  unfold Nonperiodic at hnb hnc
  push Not at hnb hnc
  obtain ⟨p, hp, hpb⟩ := hnb
  obtain ⟨q, hq, hqc⟩ := hnc
  have hp' : Function.IsPeriodicPt negT p b := hpb
  have hq' : Function.IsPeriodicPt negT q c := hqc
  exact False.elim (hne (hp'.eq_of_apply_eq hq' hp hq (hb.trans hc.symm)))

/-- At most three doublings reach a residue with two predecessors prime to 3. -/
theorem productive_doubling {a : ℕ} (ha : a % 3 ≠ 0) :
    ∃ k ≤ 3, (2 ^ k * a) % 9 = 1 ∨ (2 ^ k * a) % 9 = 7 := by
  have hr : a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨
      a % 9 = 7 ∨ a % 9 = 8 := by omega
  rcases hr with h | h | h | h | h | h
  · exact ⟨0, by omega, by simpa using Or.inl h⟩
  · refine ⟨3, by omega, ?_⟩
    norm_num [Nat.mul_mod, h]
  · refine ⟨2, by omega, ?_⟩
    norm_num [Nat.mul_mod, h]
  · refine ⟨1, by omega, ?_⟩
    norm_num [Nat.mul_mod, h]
  · exact ⟨0, by omega, by simpa using Or.inr h⟩
  · refine ⟨1, by omega, ?_⟩
    norm_num [Nat.mul_mod, h]

theorem nonperiodic_unit_ancestor {a : ℕ} (ha : 0 < a) (h3a : a % 3 ≠ 0) :
    ∃ n, 0 < n ∧ n % 3 ≠ 0 ∧ Nonperiodic n ∧ Reaches n a := by
  obtain ⟨k, _, hk⟩ := productive_doubling h3a
  let z := 2 ^ k * a
  have hz : 0 < z := by dsimp [z]; positivity
  have hz9 : z % 9 = 1 ∨ z % 9 = 7 := hk
  have hz3 : z % 3 = 1 := by omega
  have he := minus_preimage_exact hz3
  have hcpos : 0 < minusOddPreimage z := by omega
  have hc3 : minusOddPreimage z % 3 ≠ 0 := by omega
  have hne : 2 * z ≠ minusOddPreimage z := by omega
  have hza : Reaches z a := ⟨k, iterate_two_pow k a⟩
  rcases one_nonperiodic_predecessor (negT_double z) he.2.2 hne with hn | hn
  · refine ⟨2 * z, by omega, by omega, hn, ?_⟩
    exact reaches_trans ⟨1, by simpa using negT_double z⟩ hza
  · refine ⟨minusOddPreimage z, hcpos, hc3, hn, ?_⟩
    exact reaches_trans ⟨1, by simpa using he.2.2⟩ hza

theorem fertile_nonperiodic_ancestor {a : ℕ} (ha : 0 < a) (h3a : a % 3 ≠ 0) :
    ∃ n, 0 < n ∧ n % 3 = 1 ∧ Nonperiodic n ∧ Reaches n a := by
  obtain ⟨n, hn, hn3, hnp, hna⟩ := nonperiodic_unit_ancestor ha h3a
  by_cases h1 : n % 3 = 1
  · exact ⟨n, hn, h1, hnp, hna⟩
  · refine ⟨2 * n, by omega, by omega, ?_, ?_⟩
    · exact nonperiodic_preimage hnp (d := 1) (by simpa using negT_double n)
    · exact reaches_trans ⟨1, by simpa using negT_double n⟩ hna

/-- Every positive target prime to 3 has a large fertile nonperiodic ancestor.
No classification of all cycles is used. -/
theorem large_root_for_target {a : ℕ} (ha : 0 < a) (h3a : a % 3 ≠ 0) :
    ∃ r, 2 ^ 19 < r ∧ r % 3 = 1 ∧ Nonperiodic r ∧ Reaches r a := by
  obtain ⟨n, hn, hn3, hnp, hna⟩ := fertile_nonperiodic_ancestor ha h3a
  refine ⟨2 ^ 20 * n, ?_, ?_, ?_, ?_⟩
  · norm_num
    omega
  · norm_num [Nat.mul_mod, hn3]
  · exact nonperiodic_preimage hnp (iterate_two_pow 20 n)
  · exact reaches_trans ⟨20, iterate_two_pow 20 n⟩ hna

/-- Fertile roots in the inverse tree of a fixed root. -/
def Roots (r n : ℕ) : Prop := n % 3 = 1 ∧ Reaches n r

theorem root_mem {r : ℕ} (hr : r % 3 = 1) : Roots r r :=
  ⟨hr, reaches_refl r⟩

theorem roots_nonperiodic {r n : ℕ} (hr : Nonperiodic r) (hn : Roots r n) :
    Nonperiodic n := by
  obtain ⟨k, hk⟩ := hn.2
  exact nonperiodic_preimage hr hk

theorem roots_above_threshold
    {r n : ℕ} (hr : 2 ^ 19 < r) (hn : Roots r n) : 4096 ≤ n := by
  obtain ⟨k, hk⟩ := hn.2
  by_contra h
  have hb := PreimageBarrier.small_orbits_bounded (n := n) (by omega) k
  rw [hk] at hb
  omega

theorem roots_four {r n : ℕ} (hn : Roots r n) : Roots r (4 * n) :=
  ⟨(fertile_children hn.1).1, reaches_trans ⟨2, negT_four n⟩ hn.2⟩

theorem roots_odd {r n : ℕ} (hn : Roots r n) (h9 : n % 9 = 1) :
    Roots r (minusOddPreimage n) := by
  refine ⟨(fertile_children hn.1).2.1 h9, reaches_trans ?_ hn.2⟩
  exact ⟨1, by simpa using (minus_preimage_exact hn.1).2.2⟩

theorem roots_doubled_odd {r n : ℕ} (hn : Roots r n) (h9 : n % 9 = 7) :
    Roots r (2 * minusOddPreimage n) :=
  ⟨(fertile_children hn.1).2.2.1 h9, reaches_trans ⟨2, (two_step_preimage hn.1).1⟩ hn.2⟩

/-- A fixed finite connecting path imposes only a fixed cutoff threshold. -/
theorem reaches_bounded {r a : ℕ} (hra : Reaches r a) :
    ∃ X₀, ∀ X, X₀ ≤ X → TreeMem a X r := by
  obtain ⟨d, hd⟩ := hra
  refine ⟨∑ i ∈ Finset.range (d + 1), (negT^[i]) r, ?_⟩
  intro X hX
  refine ⟨d, hd, ?_⟩
  intro i hi
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((negT^[j]) r))
    (Finset.mem_range.mpr (by omega))).trans hX

theorem count_transfer {r a : ℕ} (hra : Reaches r a) :
    ∃ X₀, ∀ X, X₀ ≤ X → count r X ≤ count a X := by
  obtain ⟨X₀, hX₀⟩ := reaches_bounded hra
  exact ⟨X₀, fun X hX => Finset.card_le_card (tree_extend (hX₀ X hX))⟩

/-- All root hypotheses needed by the strict-grid recurrence hold uniformly. -/
theorem closed_domain_for_target
    {a : ℕ} (ha : 0 < a) (h3a : a % 3 ≠ 0) :
    ∃ r, Roots r r ∧ Reaches r a ∧
      (∀ n, Roots r n → 4096 ≤ n ∧ Nonperiodic n) ∧
      (∃ X₀, ∀ X, X₀ ≤ X → count r X ≤ count a X) := by
  obtain ⟨r, hr, hr3, hnp, hra⟩ := large_root_for_target ha h3a
  exact ⟨r, root_mem hr3, hra,
    fun n hn => ⟨roots_above_threshold hr hn, roots_nonperiodic hnp hn⟩,
    count_transfer hra⟩

end Problems.Collatz.PreimageDomain
