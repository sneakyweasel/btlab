/-
# The cycle period bounds are one semiconvergent family

The laboratory's successive cycle period lower bounds — `176251`, then `478245`,
then `780239` — are not three separate discoveries.  They are `j = 0, 1, 2` of a
single family of semiconvergent denominators of `β = log 2 / log 3`, and the
family's length is fixed by one partial quotient.

This file is the integer arithmetic behind that, and only that.  Everything here
is exact and decidable; nothing analytic, nothing about `β` itself, and nothing
that excludes any cycle.

* `betaDenoms` lists the convergent denominators `q₀ … q₁₅` of `β`.
* `denomsRec` checks each against `q_{k+1} = a_{k+1} q_k + q_{k-1}` from the
  partial quotients, so the list is not a table of magic numbers.
* `familyClosed` is the fact that makes the count finite: the semiconvergents
  `q₁₃ + j q₁₄` reach `q₁₅` exactly at `j = a₁₅ = 55`, so the family has `56`
  members and stops.
* `periodBoundsAreFamily` identifies the three published bounds as `j = 0, 1, 2`.

Why it matters and what it does not say.  The family is the sequence the
existing route must walk, one certified descent floor at a time, so `53`
members remain after the three already cleared.  That is a statement about the
cost of a route, not about cycles: nothing here proves any period bound, and the
bounds themselves rest on the certified floors recorded elsewhere.

The Diophantine input — that these denominators are the ones a near-closing
cycle needs, and that they sit on the opposite side of `β` from the
non-contracting staircase — is measured rather than proved, and is recorded in
`J-the-cycle-staircase-split-is-a-sign-condition`.  This file assumes none of it.
-/

import Mathlib.Tactic

namespace Problems.Juggler

namespace PeriodFamily

/-- Partial quotients `a₁ … a₁₅` of `β = log 2 / log 3`, after the leading `a₀ = 0`.
Stable to eighty terms across 200- and 400-digit arithmetic; only these are used. -/
def betaQuotients : List ℕ := [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55]

/-- Convergent denominators `q₀ … q₁₅` of `β`. -/
def betaDenoms : List ℕ :=
  [1, 1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508, 125743, 176251, 301994, 16785921]

/-- One step of the convergent recurrence. -/
def recStep (a qk qkm1 : ℕ) : ℕ := a * qk + qkm1

/-- **The list is generated, not asserted.**  Every denominator from `q₂` on is
`a_k q_{k-1} + q_{k-2}`, so `betaDenoms` is determined by `betaQuotients`. -/
theorem denomsRec :
    ∀ k, 2 ≤ k → k < betaDenoms.length →
      betaDenoms.getD k 0
        = recStep (betaQuotients.getD (k - 1) 0)
            (betaDenoms.getD (k - 1) 0) (betaDenoms.getD (k - 2) 0) := by
  decide

/-- `q₁₃`, the first member of the family and the first published period bound. -/
theorem q13 : betaDenoms.getD 13 0 = 176251 := by decide

/-- `q₁₄`, the step of the family. -/
theorem q14 : betaDenoms.getD 14 0 = 301994 := by decide

/-- `a₁₅ = 55`, the partial quotient that fixes the family's length. -/
theorem a15 : betaQuotients.getD 14 0 = 55 := by decide

/-- **The family closes.**  The semiconvergents `q₁₃ + j q₁₄` reach `q₁₅` exactly
at `j = 55`, which is why the family is finite and has `56` members rather than
continuing indefinitely. -/
theorem familyClosed : 176251 + 55 * 301994 = 16785921 := by norm_num

/-- The `j`-th member of the family. -/
def fanMember (j : ℕ) : ℕ := 176251 + j * 301994

/-- **The three published period bounds are `j = 0, 1, 2`.**  `J-cyclemin-walk-charge-instance`
at `176251`, then `478245`, then `780239`. -/
theorem periodBoundsAreFamily :
    (fanMember 0, fanMember 1, fanMember 2) = (176251, 478245, 780239) := by
  norm_num [fanMember]

/-- The next member, which a certified floor at `554000000` would bank. -/
theorem nextMember : fanMember 3 = 1082233 := by norm_num [fanMember]

/-- The family's last member is `q₁₅`. -/
theorem lastMember : fanMember 55 = betaDenoms.getD 15 0 := by decide

/-- **`53` remain** after `j = 0, 1, 2` are cleared: the family has `56` members,
`j = 0 … 55`. -/
theorem remaining : (Finset.range 56).card - 3 = 53 := by decide

/-- The family is strictly increasing, so the members really are successive
bounds rather than a set to be searched in any order. -/
theorem member_strictMono : StrictMono fanMember := by
  intro i j hij
  simp only [fanMember]
  omega

end PeriodFamily

end Problems.Juggler
