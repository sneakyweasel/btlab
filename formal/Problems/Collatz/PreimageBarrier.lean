import Problems.Collatz.NegativeMCycles

/-!
# A finite orbit barrier for the signed inverse-tree domain

Every orbit starting below 4096 remains strictly below 2^19. The finite
certificate only follows each start until a smaller state or an explicit
cycle is reached; strong induction supplies the remainder of its orbit.
The small blocks bound reduction memory. All computation is kernel checked.
This auxiliary boundary check does not raise a termination floor.
-/

namespace Problems.Collatz.PreimageBarrier

def cycleStates : List ℕ := [0, 1, 5, 7, 10, 17, 25, 37, 55, 82, 41, 61, 91, 136, 68, 34]

theorem cycleStates_closed : ∀ n ∈ cycleStates, negT n ∈ cycleStates := by decide

theorem cycleStates_below : ∀ n ∈ cycleStates, n < 2 ^ 19 := by decide

def barrierCheck (lower : ℕ) : ℕ → ℕ → Bool
  | 0, n => decide (n < lower ∨ n ∈ cycleStates)
  | fuel + 1, n =>
      if n < lower ∨ n ∈ cycleStates then true
      else decide (n < 2 ^ 19) && barrierCheck lower fuel (negT n)

theorem barrierCheck_sound {lower fuel n : ℕ}
    (hlower : ∀ m < lower, ∀ k, (negT^[k]) m < 2 ^ 19)
    (h : barrierCheck lower fuel n = true) : ∀ k, (negT^[k]) n < 2 ^ 19 := by
  have hc : ∀ n ∈ cycleStates, ∀ k, (negT^[k]) n < 2 ^ 19 := by
    intro n hn k
    have hm : ∀ j, (negT^[j]) n ∈ cycleStates := by
      intro j
      induction j with
      | zero => exact hn
      | succ j ih =>
          rw [Function.iterate_succ_apply']
          exact cycleStates_closed _ ih
    exact cycleStates_below _ (hm k)
  have hstop : ∀ m, m < lower ∨ m ∈ cycleStates → ∀ k, (negT^[k]) m < 2 ^ 19 := by
    intro m hm
    exact hm.elim (hlower m) (hc m)
  induction fuel generalizing n with
  | zero =>
      simp only [barrierCheck, decide_eq_true_eq] at h
      exact hstop n h
  | succ fuel ih =>
      by_cases hn : n < lower ∨ n ∈ cycleStates
      · exact hstop n hn
      · simp only [barrierCheck, hn, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
        intro k
        cases k with
        | zero => exact h.1
        | succ k =>
            rw [Function.iterate_succ_apply]
            exact ih h.2 k

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem barrier_chunk_0 : ∀ n < 256,
    barrierCheck (0 + n) 114 (0 + n) = true := by decide +kernel

private theorem barrier_chunk_1 : ∀ n < 256,
    barrierCheck (256 + n) 114 (256 + n) = true := by decide +kernel

private theorem barrier_chunk_2 : ∀ n < 256,
    barrierCheck (512 + n) 114 (512 + n) = true := by decide +kernel

private theorem barrier_chunk_3 : ∀ n < 256,
    barrierCheck (768 + n) 114 (768 + n) = true := by decide +kernel

private theorem barrier_chunk_4 : ∀ n < 256,
    barrierCheck (1024 + n) 114 (1024 + n) = true := by decide +kernel

private theorem barrier_chunk_5 : ∀ n < 256,
    barrierCheck (1280 + n) 114 (1280 + n) = true := by decide +kernel

private theorem barrier_chunk_6 : ∀ n < 256,
    barrierCheck (1536 + n) 114 (1536 + n) = true := by decide +kernel

private theorem barrier_chunk_7 : ∀ n < 256,
    barrierCheck (1792 + n) 114 (1792 + n) = true := by decide +kernel

private theorem barrier_chunk_8 : ∀ n < 256,
    barrierCheck (2048 + n) 114 (2048 + n) = true := by decide +kernel

private theorem barrier_chunk_9 : ∀ n < 256,
    barrierCheck (2304 + n) 114 (2304 + n) = true := by decide +kernel

private theorem barrier_chunk_10 : ∀ n < 256,
    barrierCheck (2560 + n) 114 (2560 + n) = true := by decide +kernel

private theorem barrier_chunk_11 : ∀ n < 256,
    barrierCheck (2816 + n) 114 (2816 + n) = true := by decide +kernel

private theorem barrier_chunk_12 : ∀ n < 256,
    barrierCheck (3072 + n) 114 (3072 + n) = true := by decide +kernel

private theorem barrier_chunk_13 : ∀ n < 256,
    barrierCheck (3328 + n) 114 (3328 + n) = true := by decide +kernel

private theorem barrier_chunk_14 : ∀ n < 256,
    barrierCheck (3584 + n) 114 (3584 + n) = true := by decide +kernel

private theorem barrier_chunk_15 : ∀ n < 256,
    barrierCheck (3840 + n) 114 (3840 + n) = true := by decide +kernel

theorem small_barrier_certificate : ∀ n < 4096, barrierCheck n 114 n = true := by
  have hchunks : ∀ j < 16, ∀ n < 256, barrierCheck (256 * j + n) 114 (256 * j + n) = true := by
    intro j hj
    interval_cases j
    · exact barrier_chunk_0
    · exact barrier_chunk_1
    · exact barrier_chunk_2
    · exact barrier_chunk_3
    · exact barrier_chunk_4
    · exact barrier_chunk_5
    · exact barrier_chunk_6
    · exact barrier_chunk_7
    · exact barrier_chunk_8
    · exact barrier_chunk_9
    · exact barrier_chunk_10
    · exact barrier_chunk_11
    · exact barrier_chunk_12
    · exact barrier_chunk_13
    · exact barrier_chunk_14
    · exact barrier_chunk_15
  intro n hn
  have h := hchunks (n / 256) (by omega) (n % 256) (Nat.mod_lt _ (by norm_num))
  have he : 256 * (n / 256) + n % 256 = n := by omega
  simpa only [he] using h

theorem small_orbits_bounded {n : ℕ} (hn : n < 4096) (k : ℕ) :
    (negT^[k]) n < 2 ^ 19 := by
  have hb : ∀ m, m < 4096 → ∀ j, (negT^[j]) m < 2 ^ 19 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm
        exact barrierCheck_sound (fun v hv => ih v hv (by omega))
          (small_barrier_certificate m hm)
  exact hb n hn k

end Problems.Collatz.PreimageBarrier
