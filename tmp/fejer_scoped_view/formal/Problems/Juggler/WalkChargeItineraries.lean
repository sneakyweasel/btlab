import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Problems.Juggler.CycleCore

namespace Problems.Juggler

/-!
# Walk-charge words: the exact hug itinerary and the itinerary identity

Paper A Section 5 (the walk-charge envelope) prices the coupled
exponent walk of a minimum-based cycle by the *hug itinerary*: take an
even letter exactly when it is legal (`u ≥ 1`). In integer form the
rule at position `k` with `a` odd letters already used is even iff
`3^a ≥ 2^(k+1)`.

This file certifies the discrete side of Paper A Lemma 5.6 (word
identity) and the combinatorial core of Theorem 5.4 (hug exchange):

* the exact rule keeps the walk in the unit window: at every prefix
  length `k`, `2^k ≤ 3^(hugOdds k) < 3·2^k`
  (`hugOdds_pow_ge`, `hugOdds_pow_lt`);
* hence `hugOdds k` is the least odd budget admissible at `k`
  (`hugOdds_least`), the integer form of
  `o_min(k) = ⌈k log 2 / log 3⌉`;
* the budgeted hug itinerary at `(L, hugOdds L)` equals the exact
  `L`-prefix (`budgetedWord_eq_hugWord`): the budget never binds;
* the hug itinerary is prefix-minimal among admissible exponent walks
  (`hugOdds_le_of_admissible`);
* every minimum-based cycle itinerary dominates the hug itinerary prefixwise
  (`cycleMin_prefix_odds_ge_hug`, via `cycleMin_prefix_pow_le`);
* the survivor-lattice generators of `RunSurvivorLattice.lean` are
  hug pairs (`hugOdds_lattice_base`, `hugOdds_1054`, `hugOdds_seed`).

It does not define the real charge, does not prove that the hug itinerary
maximises it (the analytic half of Theorem 5.4), and is not a cycle
obstruction or a halt theorem.
-/

/-- Exact rotation rule: the letter at position `k` with `a` odd
letters already used is even iff `2^(k+1) ≤ 3^a` (that is, `u ≥ 1`). -/
def hugIsEven (a k : ℕ) : Bool := decide (2 ^ (k + 1) ≤ 3 ^ a)

theorem hugIsEven_true_iff {a k : ℕ} :
    hugIsEven a k = true ↔ 2 ^ (k + 1) ≤ 3 ^ a := by
  simp [hugIsEven]

theorem hugIsEven_false_iff {a k : ℕ} :
    hugIsEven a k = false ↔ 3 ^ a < 2 ^ (k + 1) := by
  simp [hugIsEven]

/-- Number of odd letters among the first `k` letters of the exact
hug itinerary. -/
def hugOdds : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let a := hugOdds k
    a + if hugIsEven a k then 0 else 1

theorem hugOdds_succ (k : ℕ) :
    hugOdds (k + 1) = hugOdds k + if hugIsEven (hugOdds k) k then 0 else 1 :=
  rfl

/-- Letter of the exact hug itinerary at position `k` (`true` = even). -/
def hugLetter (k : ℕ) : Bool := hugIsEven (hugOdds k) k

/-- The exact hug itinerary of length `L`. -/
def hugWord (L : ℕ) : List Bool := (List.range L).map hugLetter

theorem hugOdds_succ_of_even {k : ℕ} (h : hugLetter k = true) :
    hugOdds (k + 1) = hugOdds k := by
  rw [hugOdds_succ, hugLetter] at *
  simp [h]

theorem hugOdds_succ_of_odd {k : ℕ} (h : hugLetter k = false) :
    hugOdds (k + 1) = hugOdds k + 1 := by
  rw [hugOdds_succ, hugLetter] at *
  simp [h]

/-- Lower window invariant: the exact rule never lets the walk go
negative — `2^k ≤ 3^(hugOdds k)`, that is `u_k ≥ 0`. -/
theorem hugOdds_pow_ge (k : ℕ) : 2 ^ k ≤ 3 ^ hugOdds k := by
  induction k with
  | zero => norm_num [hugOdds]
  | succ k ih =>
    cases h : hugLetter k with
    | true =>
      have h' : 2 ^ (k + 1) ≤ 3 ^ hugOdds k := by
        rw [hugLetter] at h
        exact hugIsEven_true_iff.mp h
      rw [hugOdds_succ_of_even h]
      exact h'
    | false =>
      rw [hugOdds_succ_of_odd h, pow_succ, pow_succ]
      omega

/-- Upper window invariant: the exact rule never overshoots —
`3^(hugOdds k) < 3·2^k`, the subtraction-free form of
`3^(hugOdds k − 1) < 2^k`, that is `u_k < 1 + α`. -/
theorem hugOdds_pow_lt (k : ℕ) : 3 ^ hugOdds k < 3 * 2 ^ k := by
  induction k with
  | zero => norm_num [hugOdds]
  | succ k ih =>
    cases h : hugLetter k with
    | true =>
      rw [hugOdds_succ_of_even h, pow_succ]
      omega
    | false =>
      have h' : 3 ^ hugOdds k < 2 ^ (k + 1) := by
        rw [hugLetter] at h
        exact hugIsEven_false_iff.mp h
      rw [pow_succ] at h'
      rw [hugOdds_succ_of_odd h, pow_succ, pow_succ]
      omega

/-- Minimality: `hugOdds k` is the least odd budget with
`2^k ≤ 3^a`. This is the integer form of
`o_min(k) = ⌈k log 2 / log 3⌉` and the "forcing exactly `o_min`
odds" clause of Paper A Lemma 5.6. -/
theorem hugOdds_least {k a : ℕ} (h : 2 ^ k ≤ 3 ^ a) : hugOdds k ≤ a := by
  by_contra hcon
  have hlt : a < hugOdds k := Nat.lt_of_not_le hcon
  have h1 : 3 ^ (a + 1) ≤ 3 ^ hugOdds k :=
    Nat.pow_le_pow_right (by norm_num) hlt
  have h2 : 3 ^ hugOdds k < 3 * 2 ^ k := hugOdds_pow_lt k
  rw [pow_succ] at h1
  omega

/-- Strict lower window for positive prefix lengths: powers of two
and three never meet, so `2^k < 3^(hugOdds k)`. Hence `hugOdds k` is
exactly the finance table's `o_min(k) = min {o : 3^o > 2^k}`:
it satisfies the strict inequality, and `hugOdds_least` gives
minimality among all such budgets. -/
theorem hugOdds_pow_gt {k : ℕ} (hk : 1 ≤ k) : 2 ^ k < 3 ^ hugOdds k := by
  refine Nat.lt_of_le_of_ne (hugOdds_pow_ge k) fun heq => ?_
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega : k ≠ 0)
  rw [heq] at h2
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  omega

/-- Combinatorial core of the hug exchange (Paper A Theorem 5.4):
the exact hug itinerary is prefix-minimal among admissible exponent
walks. Admissibility of an odd-count profile `a` at prefix `k` is
`u_k ≥ 0`, in integer form `2^k ≤ 3^(a k)`. -/
theorem hugOdds_le_of_admissible (a : ℕ → ℕ) (k : ℕ)
    (ha : 2 ^ k ≤ 3 ^ a k) : hugOdds k ≤ a k :=
  hugOdds_least ha

/-- **Cycle itineraries dominate the hug itinerary** (corollary of
`cycleMin_prefix_pow_le` and `hugOdds_least`): on a minimum-based
cycle itinerary, every prefix carries at least as many odd letters as the
exact hug itinerary of the same length. This is the cycle-native form of
the hug adversary — the rotation itinerary is the pointwise cheapest
odd-count profile any hypothetical cycle can present. -/
theorem cycleMin_prefix_odds_ge_hug {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∀ k, k ≤ w.length → hugOdds k ≤ oddCount (w.take k) :=
  fun k hk => hugOdds_least (cycleMin_prefix_pow_le hn h k hk)

/-- Full-itinerary instance: a minimum-based cycle itinerary of length `L` has
at least `hugOdds L` odd letters. -/
theorem cycleMin_odds_ge_hug {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    hugOdds w.length ≤ oddCount w := by
  have h1 := cycleMin_prefix_odds_ge_hug hn h w.length le_rfl
  simpa using h1

/-- One step adds at most one odd letter. -/
theorem hugOdds_succ_le (k : ℕ) : hugOdds (k + 1) ≤ hugOdds k + 1 := by
  rw [hugOdds_succ]
  cases hugIsEven (hugOdds k) k <;> simp

/-- The odd count is monotone in the prefix length. -/
theorem hugOdds_mono {j k : ℕ} (h : j ≤ k) : hugOdds j ≤ hugOdds k := by
  induction k with
  | zero => simp [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · calc hugOdds j ≤ hugOdds k := ih (Nat.lt_succ_iff.mp hlt)
        _ ≤ hugOdds (k + 1) := by rw [hugOdds_succ]; exact Nat.le_add_right _ _
    · have hj : j = k + 1 := Nat.le_antisymm h hge
      simp [hj]

/-- The odd count grows at most linearly:
`hugOdds (j + m) ≤ hugOdds j + m`. -/
theorem hugOdds_add_le (j m : ℕ) : hugOdds (j + m) ≤ hugOdds j + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : j + (m + 1) = (j + m) + 1 := by ring
    rw [h1]
    calc hugOdds ((j + m) + 1) ≤ hugOdds (j + m) + 1 := hugOdds_succ_le _
      _ ≤ (hugOdds j + m) + 1 := Nat.add_le_add_right ih 1
      _ = hugOdds j + (m + 1) := by ring

/-- Budgeted hug rule at total length `L`, odd budget `o`, position
`k`, with `a` odd letters already used: forced even when the odd
budget is exhausted, forced odd when the remaining letters must all
be odd, otherwise the exact rule. -/
def budgetedIsEven (L o k a : ℕ) : Bool :=
  if o ≤ a then true
  else if L - k ≤ o - a then false
  else hugIsEven a k

/-- Number of odd letters among the first `k` letters of the
budgeted hug itinerary at `(L, o)`. -/
def budgetedOdds (L o : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let a := budgetedOdds L o k
    a + if budgetedIsEven L o k a then 0 else 1

theorem budgetedOdds_succ (L o k : ℕ) :
    budgetedOdds L o (k + 1) =
      budgetedOdds L o k +
        if budgetedIsEven L o k (budgetedOdds L o k) then 0 else 1 :=
  rfl

/-- The budgeted hug itinerary at `(L, o)`. -/
def budgetedWord (L o : ℕ) : List Bool :=
  (List.range L).map fun k => budgetedIsEven L o k (budgetedOdds L o k)

/-- At the exact budget `o = hugOdds L`, neither budget clause fires:
the budgeted rule at position `k < L` with the exact count agrees
with the exact letter. -/
theorem budgetedIsEven_hug {L k : ℕ} (hk : k < L) :
    budgetedIsEven L (hugOdds L) k (hugOdds k) = hugLetter k := by
  cases h : hugLetter k with
  | true =>
    -- The exact letter is even: the exhausted-budget clause returns
    -- even, and the forced-odd clause cannot fire because the odd
    -- gap to `L` is strictly smaller than the remaining length.
    have hstep : hugOdds (k + 1) = hugOdds k := hugOdds_succ_of_even h
    have hlin : hugOdds L ≤ hugOdds (k + 1) + (L - (k + 1)) := by
      have h1 := hugOdds_add_le (k + 1) (L - (k + 1))
      rwa [Nat.add_sub_cancel' hk] at h1
    by_cases hb : hugOdds L ≤ hugOdds k
    · simp [budgetedIsEven, hb]
    · have hgap : ¬ (L - k ≤ hugOdds L - hugOdds k) := by omega
      rw [hugLetter] at h
      simp [budgetedIsEven, hb, hgap, h]
  | false =>
    -- The exact letter is odd: the budget is not exhausted, and both
    -- remaining branches return odd.
    have hstep : hugOdds (k + 1) = hugOdds k + 1 := hugOdds_succ_of_odd h
    have hmono : hugOdds (k + 1) ≤ hugOdds L := hugOdds_mono hk
    have hb : ¬ hugOdds L ≤ hugOdds k := by omega
    rw [hugLetter] at h
    by_cases hgap : L - k ≤ hugOdds L - hugOdds k <;>
      simp [budgetedIsEven, hb, hgap, h]

/-- At the exact budget, the budgeted and exact odd counts agree at
every prefix. -/
theorem budgetedOdds_eq_hugOdds (L : ℕ) :
    ∀ k, k ≤ L → budgetedOdds L (hugOdds L) k = hugOdds k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hkL : k < L := hk
    have hcount := ih (Nat.le_of_lt hkL)
    rw [budgetedOdds_succ, hcount, budgetedIsEven_hug hkL, hugOdds_succ,
      hugLetter]

/-- **Itinerary identity** (Paper A Lemma 5.6, discrete side): the
budgeted hug itinerary at `(L, hugOdds L)` equals the exact hug
`L`-prefix. Together with `hugOdds_pow_ge` and `hugOdds_least` this
says the exact rule forces exactly the minimal admissible odd
budget, so the budget never binds. -/
theorem budgetedWord_eq_hugWord (L : ℕ) :
    budgetedWord L (hugOdds L) = hugWord L := by
  unfold budgetedWord hugWord
  apply List.map_congr_left
  intro k hk
  have hkL : k < L := List.mem_range.mp hk
  rw [budgetedOdds_eq_hugOdds L k (Nat.le_of_lt hkL), budgetedIsEven_hug hkL]

/-- Sanity instance: the record length `L = 84` has exact odd budget
`53`, matching the finance table. -/
theorem hugOdds_84 : hugOdds 84 = 53 := by decide +kernel

/-- Sanity instance: the generator `L = 1054` has exact odd budget
`665`, matching `three_pow_step_gt_two_pow_step`. -/
theorem hugOdds_1054 : hugOdds 1054 = 665 := by decide +kernel

/-- Sanity instance: the window seed `L = 50508` has exact odd
budget `31867`, matching the finance table. -/
theorem hugOdds_seed : hugOdds 50508 = 31867 := by decide +kernel

/-- Lattice bridge: the survivor-lattice base point `(Lstar, Ostar) =
(25781, 16266)` of `RunSurvivorLattice.lean` is a hug pair — its odd
count is the exact hug count at its length. Together with
`hugOdds_1054` (the step generator `(1054, 665)`) and `hugOdds_seed`
(the seed `(50508, 31867) = 2·(25781, 16266) − (1054, 665)`), all
survivor-lattice generators lie on the hug diagonal
`o = hugOdds L`. -/
theorem hugOdds_lattice_base : hugOdds 25781 = 16266 := by decide +kernel

/-- The hug counts along the certified convergent denominators of
`θ` (`theta_convergent_denominators` in `OstrowskiSandwich.lean`):
these are the finance table's `o_min` values at each block length. -/
theorem hugOdds_convergent_denoms :
    [1, 2, 3, 8, 19, 65, 84, 485, 1054].map hugOdds =
      [1, 2, 2, 6, 12, 42, 53, 307, 665] := by decide +kernel

end Problems.Juggler
