import Problems.Juggler.WalkChargeItineraries
import Problems.Juggler.MinimumRelative

namespace Problems.Juggler

/-!
# Above-anchor walk: hug domination for open trajectories

Ports the discrete walk layer of Paper A Section 5 from minimum-based
cycles to open (non-closing) trajectory prefixes. The hypothesis is
`AboveAnchor n w` — every realized state along `w` stays at or above
the anchor `n` — with no cycle assumption.

The content is the composition of two existing facts:

* prefix non-contraction on a never-descending segment
  (`aboveAnchor_prefix_pow_le`, `CycleCore.lean`): the exponent walk
  stays nonnegative, exactly the `CycleMin` hypothesis of
  `cycleMin_prefix_pow_le` without the cycle;
* hug minimality (`hugOdds_least`) then forces every above-anchor
  prefix to dominate the exact hug itinerary in odd count
  (`aboveAnchor_prefix_odds_ge_hug`).

The transport envelope on the same hypothesis is
`aboveAnchor_transport` / `aboveAnchor_flight_envelope`
(`WalkTransport.lean`).

This constrains *hypothetical* never-descending trajectory segments only.
It is not a halt theorem, not a descent-certificate existence claim,
and not a cycle obstruction; it does not modify Paper A.
-/

/-- **Open trajectories dominate the hug itinerary.** Every prefix of a
never-descending trajectory segment carries at least as many odd letters
as the exact hug itinerary of the same length. The open-trajectory form
of `cycleMin_prefix_odds_ge_hug`: the hug adversary prices not only
hypothetical cycles but every hypothetical descent-free flight. -/
theorem aboveAnchor_prefix_odds_ge_hug {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : AboveAnchor n w) :
    ∀ k, k ≤ w.length → hugOdds k ≤ oddCount (w.take k) :=
  fun k hk => hugOdds_least (aboveAnchor_prefix_pow_le hn h k hk)

/-- Full-itinerary instance: an above-anchor itinerary of length `L` has at
least `hugOdds L` odd letters. -/
theorem aboveAnchor_odds_ge_hug {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : AboveAnchor n w) :
    hugOdds w.length ≤ oddCount w := by
  simpa using aboveAnchor_prefix_odds_ge_hug hn h w.length le_rfl

end Problems.Juggler
