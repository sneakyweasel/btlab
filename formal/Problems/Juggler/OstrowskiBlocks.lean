/-
# Ostrowski digits as Denjoy–Koksma blocks

`theta_block_envelope` (`JumpVariation.lean`) takes a `List (ℕ × ℕ)` of certified convergents
and bounds the ergodic sum over `(blocks.map Prod.snd).sum` letters by `blocks.length * 2`.
Paper A feeds it a specific list: the Ostrowski decomposition `L = Σⱼ bⱼqⱼ`, a pair repeated
once per digit, so that the two readings become `L` and `s(L)`.

That assembly was the last mechanical step in Theorem 5.7's chain, and Theorem 5.8's row named
it as the "Denjoy--Koksma comparison". It is this file.

* `thetaPair` — the certified pair at a level, `thetaConvergents` read by index. Its second
  component *is* `thetaDenomFn`, which is what lets the numeration and the envelope meet.
* `ostroBlocks` — level `i` contributes `ostroDigit thetaDenomFn L 12 i` copies of the pair at
  level `12 - i`, matching the association in `theta_sum_eq`.
* `ostroBlocks_snd_sum` — the denominators sum to `L`, from `theta_sum_eq`.
* `ostroBlocks_length` — the length is the digit sum `s(L)`.
* `theta_block_envelope_of_length` — the display for an arbitrary length, with no window
  hypothesis: the ergodic sum of `L` letters is within `2 s(L)` of `L · C_*`.
* `theta_block_envelope_window` — on the certified window `L < 301994` the digit cap
  `theta_digitSum_le` turns that into the constant `94 = 2 · 47`.

The general list lemmas at the top are stated for a `flatMap` of `replicate`s because that is
the shape "a pair repeated once per digit" has; nothing in them is about `θ`.
-/

import Problems.Juggler.OstrowskiNumeration
import Problems.Juggler.JumpVariation

namespace Problems.Juggler

/-! ### A `flatMap` of `replicate`s: length, mapped sum, membership -/

theorem length_flatMap_replicate (d : ℕ → ℕ) (p : ℕ → ℕ × ℕ) :
    ∀ n : ℕ,
      ((List.range n).flatMap fun i => List.replicate (d i) (p i)).length
        = ∑ i ∈ Finset.range n, d i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih,
      Finset.sum_range_succ]
    simp

theorem sum_map_snd_flatMap_replicate (d : ℕ → ℕ) (p : ℕ → ℕ × ℕ) :
    ∀ n : ℕ,
      (((List.range n).flatMap fun i => List.replicate (d i) (p i)).map Prod.snd).sum
        = ∑ i ∈ Finset.range n, d i * (p i).2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    simp [List.map_replicate, List.sum_replicate, mul_comm]

theorem mem_flatMap_replicate {d : ℕ → ℕ} {p : ℕ → ℕ × ℕ} {n : ℕ} {x : ℕ × ℕ}
    (h : x ∈ (List.range n).flatMap fun i => List.replicate (d i) (p i)) :
    ∃ i < n, x = p i := by
  rw [List.mem_flatMap] at h
  obtain ⟨i, hi, hx⟩ := h
  exact ⟨i, List.mem_range.mp hi, (List.eq_of_mem_replicate hx)⟩

/-! ### The θ instance -/

/-- The certified convergent pair at level `j`. -/
def thetaPair (j : ℕ) : ℕ × ℕ := thetaConvergents.getD j (0, 1)

theorem thetaPair_mem {j : ℕ} (h : j ≤ 12) : thetaPair j ∈ thetaConvergents := by
  interval_cases j <;> decide

/-- The bridge: the pair's denominator is the numeration's denominator. -/
theorem thetaPair_snd {j : ℕ} (h : j ≤ 12) : (thetaPair j).2 = thetaDenomFn j := by
  interval_cases j <;> decide

/-- **The Ostrowski block list.**  Level `i` contributes one copy of the pair at level
`12 - i` for each of its digits, matching `theta_sum_eq`. -/
def ostroBlocks (L : ℕ) : List (ℕ × ℕ) :=
  (List.range 13).flatMap fun i =>
    List.replicate (ostroDigit thetaDenomFn L 12 i) (thetaPair (12 - i))

theorem ostroBlocks_mem {L : ℕ} {pq : ℕ × ℕ} (h : pq ∈ ostroBlocks L) :
    pq ∈ thetaConvergents := by
  obtain ⟨i, _, rfl⟩ := mem_flatMap_replicate h
  exact thetaPair_mem (Nat.sub_le 12 i)

/-- The denominators sum to `L` — this is `theta_sum_eq`. -/
theorem ostroBlocks_snd_sum (L : ℕ) : ((ostroBlocks L).map Prod.snd).sum = L := by
  rw [ostroBlocks, sum_map_snd_flatMap_replicate]
  have hterm : ∀ i ∈ Finset.range 13,
      ostroDigit thetaDenomFn L 12 i * (thetaPair (12 - i)).2
        = ostroDigit thetaDenomFn L 12 i * thetaDenomFn (12 - i) :=
    fun i _ => by rw [thetaPair_snd (Nat.sub_le 12 i)]
  rw [Finset.sum_congr rfl hterm]
  exact (theta_sum_eq L).symm

/-- The length is the greedy digit sum `s(L)`. -/
theorem ostroBlocks_length (L : ℕ) :
    (ostroBlocks L).length = ∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i := by
  rw [ostroBlocks, length_flatMap_replicate]

/-- **Theorem 5.7's display at a given length.**  No window hypothesis: for every `L`, the
ergodic sum of `L` letters is within `2 s(L)` of `L` times the mean. -/
theorem theta_block_envelope_of_length {n' : ℝ} (hn : 1 < n') (L : ℕ) (x : ℝ) :
    |∑ k ∈ Finset.range L, periodicObservable n' (x + k * walkTheta)
       - (L : ℝ) * ∫ t in (0:ℝ)..1, periodicObservable n' t|
      ≤ (∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i : ℕ) * 2 := by
  have h := theta_block_envelope hn (ostroBlocks L) (fun _ hpq => ostroBlocks_mem hpq) x
  rw [ostroBlocks_snd_sum, ostroBlocks_length] at h
  exact h

/-- **On the certified window the bound is a constant.**  `s(L) ≤ 47`, so the ergodic sum of
`L < 301994` letters is within `94` of `L · C_*`, uniformly in the starting phase. -/
theorem theta_block_envelope_window {n' : ℝ} (hn : 1 < n') {L : ℕ} (hL : L < 301994) (x : ℝ) :
    |∑ k ∈ Finset.range L, periodicObservable n' (x + k * walkTheta)
       - (L : ℝ) * ∫ t in (0:ℝ)..1, periodicObservable n' t| ≤ 94 := by
  refine (theta_block_envelope_of_length hn L x).trans ?_
  have hcap : (∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i) ≤ 47 :=
    theta_digitSum_le hL
  have : ((∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i : ℕ) : ℝ) ≤ 47 := by
    exact_mod_cast hcap
  linarith

end Problems.Juggler
