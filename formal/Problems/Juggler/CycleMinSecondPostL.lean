import Problems.Juggler.CycleMinEnvelopes
import Problems.Juggler.CycleFinanceLeftovers

namespace Problems.Juggler.CycleMinEnvelopes

open Problems.Juggler Problems.Juggler.OOOSquare

/-!
# The second post-L OOE on a cycle minimum, with no side condition

`cycleMin_m_ooe` needs the continuation `v` after `M·OOE` to be nonempty. The
empty case would be a whole cycle of length 17, which
`no_cycle_itinerary_length_le_eighteen` already excludes. So on every cycle
minimum with a prefix `M·OOE`, the landing `r` lies in `[n, n^2)` and either
`n` has finite progress or the continuation starts with `O`.
-/

/-- **`CycleMin (n, M·OOE·v)` for any `v`:** `n ≤ r < n^2`, and finite progress or
`v` starts with `O`. The empty continuation is a length-17 cycle, excluded. -/
theorem cycleMin_m_ooe_any {n : ℕ} {v : List Branch} (hn : 2 ≤ n)
    (hmin : CycleMin n (mWord ++ ooePow 1 ++ v)) :
    (n ≤ image n (mWord ++ ooePow 1) ∧ image n (mWord ++ ooePow 1) < n ^ 2) ∧
      (FiniteProgress n ∨ v.head? = some .odd) := by
  rcases eq_or_ne v [] with rfl | hv
  · exfalso
    apply no_cycle_itinerary_length_le_eighteen hn _ hmin.1
    rw [List.append_nil, m_ooePow_length]; norm_num
  · exact cycleMin_m_ooe hn hv hmin

end Problems.Juggler.CycleMinEnvelopes
