import Problems.Juggler.BeattyAtomBounds

/-!
# Level structure of isolated slopes

`IsoLevels ν G B` enumerates the good indices `g 0 < g 1 < …` of an isolated
slope. The first good denominator is at least `B`, and each good denominator
dominates a power of the previous one:
`(2 Q_(g l + 1))^((l+2)²) ≤ Q_(g (l+1))`.

At a good index `k`:
* the next denominator satisfies `Q_k^ν ≤ Q_(k+1) ≤ 4 Q_k^ν`;
* the error `θ = Q_k α - P_k` satisfies `1/(2Q_(k+1)) ≤ |θ| ≤ 1/Q_(k+1)`;
* `P_k/Q_k` is reduced.

Strictly between good indices the partial quotients are `1`, so consecutive
denominators at most double.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set

/-- An enumeration of the good indices with a size floor and sparsity. -/
structure IsoLevels (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] (B : ℝ) where
  g : ℕ → ℕ
  mono : StrictMono g
  one_le : 1 ≤ g 0
  good_iff : ∀ k, G k ↔ ∃ l, g l = k
  big : B ≤ (isoDen ν G (g 0) : ℝ)
  sparse : ∀ l, ((2 : ℝ) * isoDen ν G (g l + 1)) ^ ((l + 2) ^ 2) ≤ isoDen ν G (g (l + 1))

namespace IsoLevels

variable {ν B : ℝ} {G : ℕ → Prop} [DecidablePred G] (Lv : IsoLevels ν G B)

/-- Good indices are at least one. -/
theorem one_le_g (l : ℕ) : 1 ≤ Lv.g l :=
  Lv.one_le.trans (Lv.mono.monotone (Nat.zero_le l))

/-- Enumerated indices are good. -/
theorem good (l : ℕ) : G (Lv.g l) := (Lv.good_iff _).2 ⟨l, rfl⟩

/-- Indices strictly between consecutive good indices are not good. -/
theorem not_good {l k : ℕ} (h1 : Lv.g l < k) (h2 : k < Lv.g (l + 1)) : ¬ G k := by
  rw [Lv.good_iff]
  rintro ⟨j, rfl⟩
  have a := Lv.mono.lt_iff_lt.1 h1
  have b := Lv.mono.lt_iff_lt.1 h2
  omega

end IsoLevels

variable {ν : ℝ} {G : ℕ → Prop} [DecidablePred G]

/-- Denominators are at least one from index one on. -/
theorem isoDen_pos (k : ℕ) : 0 < isoDen ν G (k + 1) := by
  have := cfDen_succ_pos (isoQuot_succ_ge ν G) k
  rwa [cfDen_isoQuot] at this

/-- Isolated-slope denominators are nondecreasing. -/
theorem isoDen_mono : Monotone (isoDen ν G) := by
  refine monotone_nat_of_le_succ fun k => ?_
  have := cfDen_le_succ (isoQuot_succ_ge ν G) k
  rwa [cfDen_isoQuot, cfDen_isoQuot] at this

/-- Between good indices denominators at most double. -/
theorem isoDen_succ_le_two {k : ℕ} (hk : 1 ≤ k) (hg : ¬ G k) :
    (isoDen ν G (k + 1) : ℝ) ≤ 2 * isoDen ν G k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h : isoDen ν G (n + 2) = 1 * isoDen ν G (n + 1) + isoDen ν G n := by
    simp [isoDen, hg]
  have hle : (isoDen ν G n : ℝ) ≤ isoDen ν G (n + 1) := by exact_mod_cast isoDen_mono (Nat.le_succ n)
  rw [show n + 1 + 1 = n + 2 by ring, h]
  push_cast; linarith

/-- Good-level growth `Q_k^ν ≤ Q_(k+1) ≤ 4 Q_k^ν`. -/
theorem isoDen_good_growth (hν : 1 ≤ ν) {k : ℕ} (hk : 1 ≤ k) (hg : G k) :
    (isoDen ν G k : ℝ) ^ ν ≤ isoDen ν G (k + 1) ∧
      (isoDen ν G (k + 1) : ℝ) ≤ 4 * (isoDen ν G k : ℝ) ^ ν := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h1, h2⟩ := isoDen_growth (G := G) hν n
  exact ⟨h2 hg, h1⟩

/-- The error at index `k`: `|Q_k α - P_k| = cfErr k`, between `1/(2Q_(k+1))` and `1/Q_(k+1)`. -/
theorem iso_err_bounds (k : ℕ) :
    1 / (2 * (isoDen ν G (k + 1) : ℝ)) ≤
        |(isoDen ν G k : ℝ) * isoSlope ν G - cfNum (isoQuot ν G) k| ∧
      |(isoDen ν G k : ℝ) * isoSlope ν G - cfNum (isoQuot ν G) k| ≤
        1 / (isoDen ν G (k + 1) : ℝ) := by
  have ha := isoQuot_succ_ge ν G
  have he := abs_cf_err ha k
  rw [cfDen_isoQuot] at he
  unfold isoSlope
  rw [he]
  have h1 := cfErr_ge ha k
  have h2 := cfErr_le ha k
  rw [cfDen_isoQuot] at h1 h2
  exact ⟨h1, h2⟩

/-- Reduced convergents. -/
theorem iso_coprime (k : ℕ) (hk : 1 ≤ k) :
    Nat.Coprime ((cfNum (isoQuot ν G) k : ℤ)).natAbs (isoDen ν G k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have := (cf_goodConvergents (isoQuot_succ_ge ν G)).coprime n
  rwa [cfDen_isoQuot] at this

/-- Convergent numerator and denominator are coprime integers. -/
theorem iso_isCoprime (k : ℕ) (hk : 1 ≤ k) :
    IsCoprime ((cfNum (isoQuot ν G) k : ℤ)) ((isoDen ν G k : ℕ) : ℤ) := by
  have h := iso_coprime (ν := ν) (G := G) k hk
  rw [Int.isCoprime_iff_gcd_eq_one]
  rw [Int.gcd, Int.natAbs_natCast]
  exact h

/-- Convergent approximation `|α - P_k/Q_k| ≤ 1/Q_k²`. -/
theorem iso_approx (k : ℕ) (hk : 1 ≤ k) :
    |isoSlope ν G - ((cfNum (isoQuot ν G) k : ℤ) : ℝ) / isoDen ν G k| ≤
      1 / (isoDen ν G k : ℝ) ^ 2 := by
  have hQ : (0 : ℝ) < isoDen ν G k := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    exact_mod_cast isoDen_pos n
  have hmono : (isoDen ν G k : ℝ) ≤ isoDen ν G (k + 1) := by
    exact_mod_cast isoDen_mono (Nat.le_succ k)
  have h := (iso_err_bounds (ν := ν) (G := G) k).2
  have h' : |(isoDen ν G k : ℝ) * isoSlope ν G - cfNum (isoQuot ν G) k| ≤ 1 / (isoDen ν G k : ℝ) :=
    h.trans (one_div_le_one_div_of_le hQ hmono)
  have e : isoSlope ν G - ((cfNum (isoQuot ν G) k : ℤ) : ℝ) / isoDen ν G k =
      ((isoDen ν G k : ℝ) * isoSlope ν G - cfNum (isoQuot ν G) k) / isoDen ν G k := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos hQ, div_le_iff₀ hQ]
  calc _ ≤ 1 / (isoDen ν G k : ℝ) := h'
    _ = 1 / (isoDen ν G k : ℝ) ^ 2 * isoDen ν G k := by field_simp

end Problems.Juggler.BeattySlope
