import Problems.Juggler.Dynamics

namespace Problems.Juggler

/-!
# The exact landing window of a nested production (Appendix D.1)

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Appendix D.1, equations (D.1) and
(D.2). Along a word `V_k = (OE)^{k-1}OEE` the two-step map is `F(u) = ⌊u^{3/4}⌋`, so that
`J^{2i}(n) = F^i(n)`, and the appendix's first claim is an exact one: the integers whose
`F`-image lands in `[a, b)` are exactly the integers of `[Φ(a), Φ(b))`, where
`Φ(a) = ⌈a^{4/3}⌉`.

Here `F` is `cell34 n = ⌊√⌊√(n³)⌋⌋`, the integer form of `⌊n^{3/4}⌋`, and `Φ` is
`windowStart a`, the least `n` with `a⁴ ≤ n³` — which is what `⌈a^{4/3}⌉` means in exact
arithmetic, and needs no real number to say. The pair is a Galois connection,
`windowStart a ≤ n ↔ a⁴ ≤ n³` and `a ≤ cell34 n ↔ a⁴ ≤ n³`, and (D.1) falls out
(`exact_endpoints`, `setOf_cell34_mem_Ico`); iterating it gives the nested window (D.2)
(`exact_endpoints_iterate`, `setOf_iterate_mem_Ico`).

What is exact here is the window. The appendix's use of it is not: the smooth comparison
`|I_k(m)| = ρ_k^{-1} m^{1/ρ_k - 1}(1 + o(1))` of (D.3), the endpoint error `O_k(P^{1-s})`,
the multiplicity of an inner-layer integer and the production inequality (5.2) they feed are
not formalized and are not in this file. The parity conditions of `V_k` are imposed
separately: `cell34_eq_floorPower_two` is the only statement here that mentions the map, and
it says that `J² = F` exactly on an `OE` step. Nothing here is a halt theorem.
-/

namespace LandingWindow

/-- `F(u) = ⌊u^{3/4}⌋` as an integer operation: `⌊√⌊√(u³)⌋⌋`. -/
def cell34 (n : ℕ) : ℕ := ((n ^ 3).sqrt).sqrt

/-- On an `OE` step the two-step map is `F`: `J²(n) = ⌊n^{3/4}⌋` for odd `n` with even
image. This is the only place the dynamics enters; the rest is arithmetic. -/
theorem cell34_eq_floorPower_two {n : ℕ} (hodd : n % 2 = 1) (heven : (n ^ 3).sqrt % 2 = 0) :
    floorPower (floorPower n) = cell34 n := by
  rw [floorPower_odd_eq hodd, floorPower_even_eq heven, cell34]

/-- `a ≤ ⌊n^{3/4}⌋` is the exact inequality `a⁴ ≤ n³`. -/
theorem le_cell34_iff {a n : ℕ} : a ≤ cell34 n ↔ a ^ 4 ≤ n ^ 3 := by
  rw [cell34, Nat.le_sqrt', Nat.le_sqrt', ← pow_mul]

/-- `⌊n^{3/4}⌋ < b` is the exact inequality `n³ < b⁴`. -/
theorem cell34_lt_iff {b n : ℕ} : cell34 n < b ↔ n ^ 3 < b ^ 4 := by
  rw [← not_le, le_cell34_iff, not_le]

theorem windowStart_exists (a : ℕ) : ∃ n, a ^ 4 ≤ n ^ 3 := by
  refine ⟨a ^ 2, ?_⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · calc a ^ 4 ≤ a ^ 6 := Nat.pow_le_pow_right ha (by norm_num)
      _ = (a ^ 2) ^ 3 := by ring

/-- `Φ(a) = ⌈a^{4/3}⌉`: the least integer whose cube is at least `a⁴`. -/
def windowStart (a : ℕ) : ℕ := Nat.find (windowStart_exists a)

/-- The Galois connection defining `Φ`. -/
theorem windowStart_le_iff {a n : ℕ} : windowStart a ≤ n ↔ a ^ 4 ≤ n ^ 3 := by
  constructor
  · intro h
    exact le_trans (Nat.find_spec (windowStart_exists a)) (Nat.pow_le_pow_left h 3)
  · exact fun h => Nat.find_le h

theorem lt_windowStart_iff {b n : ℕ} : n < windowStart b ↔ n ^ 3 < b ^ 4 := by
  rw [← not_le, windowStart_le_iff, not_le]

/-- **Equation (D.1), the exact endpoints.** `a ≤ F(n) < b` exactly when
`Φ(a) ≤ n < Φ(b)`. -/
theorem exact_endpoints {a b n : ℕ} :
    (a ≤ cell34 n ∧ cell34 n < b) ↔ (windowStart a ≤ n ∧ n < windowStart b) := by
  rw [le_cell34_iff, cell34_lt_iff, windowStart_le_iff, lt_windowStart_iff]

/-- Equation (D.1) as the set identity the appendix writes:
`{n : a ≤ F(n) < b} = [Φ(a), Φ(b)) ∩ ℤ`. -/
theorem setOf_cell34_mem_Ico (a b : ℕ) :
    {n : ℕ | a ≤ cell34 n ∧ cell34 n < b} = Set.Ico (windowStart a) (windowStart b) := by
  ext n
  simpa [Set.mem_Ico] using exact_endpoints

/-- **Equation (D.2), the nested window.** Iterating (D.1): the integers whose `i`-fold
`F`-image lands in `[a, b)` are exactly those of `[Φ^i(a), Φ^i(b))`. -/
theorem exact_endpoints_iterate (i : ℕ) {a b : ℕ} : ∀ n : ℕ,
    (a ≤ cell34^[i] n ∧ cell34^[i] n < b) ↔
      (windowStart^[i] a ≤ n ∧ n < windowStart^[i] b) := by
  induction i with
  | zero => intro n; simp
  | succ i ih =>
      intro n
      rw [Function.iterate_succ_apply, ih (cell34 n), Function.iterate_succ_apply',
        Function.iterate_succ_apply', exact_endpoints]

/-- Equation (D.2) as a set identity. -/
theorem setOf_iterate_mem_Ico (i a b : ℕ) :
    {n : ℕ | a ≤ cell34^[i] n ∧ cell34^[i] n < b} =
      Set.Ico (windowStart^[i] a) (windowStart^[i] b) := by
  ext n
  simpa [Set.mem_Ico] using exact_endpoints_iterate i n

end LandingWindow

end Problems.Juggler
