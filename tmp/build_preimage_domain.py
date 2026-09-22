from pathlib import Path

root = Path(__file__).resolve().parents[1]
barrier = r'''import Problems.Collatz.NegativeMCycles

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

'''
for j in range(16):
    barrier += f'private theorem barrier_chunk_{j} : ∀ n < 256,\n    barrierCheck ({256*j} + n) 114 ({256*j} + n) = true := by decide +kernel\n\n'
barrier += r'''theorem small_barrier_certificate : ∀ n < 4096, barrierCheck n 114 n = true := by
  have hchunks : ∀ j < 16, ∀ n < 256, barrierCheck (256 * j + n) 114 (256 * j + n) = true := by
    intro j hj
    interval_cases j
'''
for j in range(16):
    barrier += f'    · exact barrier_chunk_{j}\n'
barrier += r'''  intro n hn
  have h := hchunks (n / 256) (by omega) (n % 256) (Nat.mod_lt _ (by norm_num))
  convert h using 1 <;> congr 1 <;> omega

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
'''
(root / 'formal/Problems/Collatz/PreimageBarrier.lean').write_text(barrier, encoding='utf-8')

domain = (root / 'formal/PreimageDomainScratch.lean').read_text(encoding='utf-8')
domain = domain.replace('import Problems.Collatz.PreimageGrid',
                        'import Problems.Collatz.PreimageGrid\nimport Problems.Collatz.PreimageBarrier')
domain = domain.replace('namespace Problems.Collatz.PreimageDomain', r'''/-!
# A closed root domain for every positive unit target

Two distinct predecessors cannot both be periodic. This gives a fertile
nonperiodic ancestor for every target prime to 3, even when the target is
periodic. Doubling it above the finite barrier produces a domain whose
selected predecessors stay above the strict grid's threshold. A fixed
path transfers capped counts to the original target for all large cutoffs.
The growth induction and a numerical certificate remain separate work.
-/

namespace Problems.Collatz.PreimageDomain''', 1)
domain = domain.replace('    (barrier : ∀ m < 4096, ∀ k, (negT^[k]) m < 2 ^ 19)\n', '')
domain = domain.replace('have hb := barrier n (by omega) k',
                        'have hb := PreimageBarrier.small_orbits_bounded (n := n) (by omega) k')
domain = domain.replace('roots_above_threshold barrier hr hn', 'roots_above_threshold hr hn')
(root / 'formal/Problems/Collatz/PreimageDomain.lean').write_text(domain, encoding='utf-8')
