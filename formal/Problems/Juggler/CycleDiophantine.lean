import Problems.Juggler.CycleExtrema

namespace Problems.Juggler

/-!
# Peak Diophantine defects

The sequential peak identity

`x^3 = (p^{2^r} + ε)^2 + δ`

is the exact slack of the existing lower cell `x^3 ≥ p^{2^{r+1}}`.
Parity of `δ` and `ε` is the existing odd/even cell arithmetic.
A nontrivial cycle cannot visit `{1,…,11}`, so the top landing
satisfies `p ≥ 13`.

This is not a halt theorem, not a cycle-impossibility theorem, and
not a remainder-dynamics object.
-/

def peakOddDefect (x M : ℕ) : ℕ := x ^ 3 - M ^ 2

def topEvenDefect (M p r : ℕ) : ℕ := M - p ^ (2 ^ r)

theorem peakOddDefect_eq_local {x M : ℕ} (_hodd : x % 2 = 1)
    (hT : floorPower x = M) :
    peakOddDefect x M = localDefectOdd x := by
  simp [peakOddDefect, localDefectOdd, hT]

theorem peakOddDefect_add {x M : ℕ} (hodd : x % 2 = 1)
    (hT : floorPower x = M) :
    x ^ 3 = M ^ 2 + peakOddDefect x M := by
  have hle : M ^ 2 ≤ x ^ 3 :=
    ((floorPower_odd_eq_iff_cube_interval hodd).mp hT).1
  simpa [peakOddDefect] using (Nat.add_sub_of_le hle).symm

theorem peakOddDefect_lt {x M : ℕ} (hodd : x % 2 = 1)
    (hT : floorPower x = M) :
    peakOddDefect x M < 2 * M + 1 := by
  have hlt := localDefectOdd_lt_succ hodd
  simpa [peakOddDefect_eq_local hodd hT, hT] using hlt

theorem peakOddDefect_odd {x M : ℕ} (hodd : x % 2 = 1) (hM : M % 2 = 0)
    (hT : floorPower x = M) :
    peakOddDefect x M % 2 = 1 := by
  have hadd := peakOddDefect_add hodd hT
  have hx3 : x ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hodd]
  have hM2 : M ^ 2 % 2 = 0 := by simp [Nat.pow_mod, hM]
  omega

theorem peakOddDefect_pos {x M : ℕ} (hodd : x % 2 = 1) (hM : M % 2 = 0)
    (hT : floorPower x = M) :
    0 < peakOddDefect x M := by
  have hoddδ := peakOddDefect_odd hodd hM hT
  omega

theorem topEvenDefect_add {M p r : ℕ} (hle : p ^ (2 ^ r) ≤ M) :
    M = p ^ (2 ^ r) + topEvenDefect M p r :=
  (Nat.add_sub_of_le hle).symm

theorem topEvenDefect_pos {p M r : ℕ}
    (hp : p % 2 = 1) (hM : M % 2 = 0)
    (hlo : p ^ (2 ^ r) ≤ M) :
    0 < topEvenDefect M p r := by
  have hlt := cycle_top_window_strict hp hM hlo
  simpa [topEvenDefect] using Nat.sub_pos_of_lt hlt

theorem topEvenDefect_lt {M p r : ℕ}
    (hlo : p ^ (2 ^ r) ≤ M) (hhi : M < (p + 1) ^ (2 ^ r)) :
    topEvenDefect M p r < (p + 1) ^ (2 ^ r) - p ^ (2 ^ r) :=
  Nat.sub_lt_sub_right hlo hhi

theorem topEvenDefect_odd {p M r : ℕ}
    (hp : p % 2 = 1) (hM : M % 2 = 0)
    (hlo : p ^ (2 ^ r) ≤ M) :
    topEvenDefect M p r % 2 = 1 := by
  have hadd := topEvenDefect_add hlo
  have hpow : (p ^ (2 ^ r)) % 2 = 1 := odd_iff_pow_two_depth_odd.mp hp
  omega

/-- Sequential peak identity. Not a path-sum remainder balance. -/
theorem peak_diophantine_compose {x M p r : ℕ}
    (hodd : x % 2 = 1) (hT : floorPower x = M)
    (hle : p ^ (2 ^ r) ≤ M) :
    x ^ 3 =
      (p ^ (2 ^ r) + topEvenDefect M p r) ^ 2 + peakOddDefect x M := by
  have hδ := peakOddDefect_add hodd hT
  have hε := topEvenDefect_add hle
  rw [← hε]
  exact hδ

/-- Exact slack of `x^3 ≥ p^{2^{r+1}}`. This is the envelope cell. -/
theorem peak_diophantine_slack {x M p r : ℕ}
    (hodd : x % 2 = 1) (hT : floorPower x = M)
    (hle : p ^ (2 ^ r) ≤ M) :
    x ^ 3 - p ^ (2 ^ (r + 1)) =
      2 * topEvenDefect M p r * p ^ (2 ^ r) +
        topEvenDefect M p r ^ 2 + peakOddDefect x M := by
  have hsum :
      p ^ (2 ^ (r + 1)) +
        (2 * topEvenDefect M p r * p ^ (2 ^ r) +
          topEvenDefect M p r ^ 2 + peakOddDefect x M) =
        x ^ 3 := by
    calc
      p ^ (2 ^ (r + 1)) +
            (2 * topEvenDefect M p r * p ^ (2 ^ r) +
              topEvenDefect M p r ^ 2 + peakOddDefect x M)
          = (p ^ (2 ^ r)) ^ 2 +
              (2 * topEvenDefect M p r * p ^ (2 ^ r) +
                topEvenDefect M p r ^ 2 + peakOddDefect x M) := by
          rw [pow_two_succ_sq p r]
      _ = (p ^ (2 ^ r) + topEvenDefect M p r) ^ 2 + peakOddDefect x M := by
          ring
      _ = x ^ 3 := (peak_diophantine_compose hodd hT hle).symm
  rw [← hsum, Nat.add_sub_cancel_left]

theorem cycle_peak_diophantine {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r p x, 1 ≤ r ∧
      p = floorPower^[r] n ∧
        x = floorPower^[w.length - 1] n ∧
          x ^ 3 =
            (p ^ (2 ^ r) + topEvenDefect n p r) ^ 2 +
              peakOddDefect x n := by
  have ⟨r, p, x, hr1, hpdef, hxdef, _, _, hlo, _, _, _⟩ :=
    cycle_top_nested_cell hn h
  have hxodd : x % 2 = 1 := by
    simpa [hxdef] using cycleMax_predecessor_odd hn h
  have hTx : floorPower x = n := by
    simpa [hxdef] using cycleMax_predecessor_apply hn h
  refine ⟨r, p, x, hr1, hpdef, hxdef, ?_⟩
  exact peak_diophantine_compose hxodd hTx (by simpa [hpdef] using hlo)

theorem cycle_peak_diophantine_slack {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r p x, 1 ≤ r ∧
      p = floorPower^[r] n ∧
        x = floorPower^[w.length - 1] n ∧
          x ^ 3 - p ^ (2 ^ (r + 1)) =
            2 * topEvenDefect n p r * p ^ (2 ^ r) +
              topEvenDefect n p r ^ 2 + peakOddDefect x n := by
  have ⟨r, p, x, hr1, hpdef, hxdef, _, _, hlo, _, _, _⟩ :=
    cycle_top_nested_cell hn h
  have hxodd : x % 2 = 1 := by
    simpa [hxdef] using cycleMax_predecessor_odd hn h
  have hTx : floorPower x = n := by
    simpa [hxdef] using cycleMax_predecessor_apply hn h
  refine ⟨r, p, x, hr1, hpdef, hxdef, ?_⟩
  exact peak_diophantine_slack hxodd hTx (by simpa [hpdef] using hlo)

/-- Cycle-only upgrade `2 ≤ p` to `13 ≤ p`. Not a modular obstruction. -/
theorem cycle_top_landing_ge_thirteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r p, 1 ≤ r ∧ p = floorPower^[r] n ∧ p % 2 = 1 ∧ 13 ≤ p := by
  have ⟨r, _u, p, _x, hr1, _hw, hpdef, _hx, hpodd, _hp2, _hxodd, _hx2,
      _hpx, _hxn, _hTx, _himg, _hC⟩ :=
    cycle_top_three_level hn h
  have h12 : 12 ≤ p := by
    simpa [hpdef] using cycleItinerary_iterate_not_lt_twelve hn h.1 (i := r)
  have hp13 : 13 ≤ p := by
    have : p % 2 = 1 := hpodd
    omega
  exact ⟨r, p, hr1, hpdef, hpodd, hp13⟩

end Problems.Juggler
