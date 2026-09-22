# Coverage review queue

Resolved rows -- rows that name their declarations -- whose declarations may not state
the whole claim.  The rule for `EXACT — LEAN VERIFIED` is that the Lean theorem covers
the English statement, and nothing checked it: the proposal digest names the two ways a
join records a part as the whole and leaves both to the reader.  Here Jev is asked four
yes/no questions over each row and every declaration it names: whether the declarations
cover the claim, whether the claim asserts more than they state, whether a declaration
is narrower than the claim, and whether one is a different result.

A row is listed when coverage is below 0.5, lowest first: below
0.25 it is filed as not covered, between the two as doubtful.  The other
three answers are shown as the reading to check first.  Jev returns probabilities, not
a reading: the list is where to look, and the ruling is the reviewer's.  Answer by
extending `decl` to the declarations that together state the claim, narrowing the
statement to what the declarations prove, or retagging to `EXACT — HUMAN PROOF`; then
rerun `jev-coverage`, which re-asks a row whose statement or declarations changed.

A short claim filed as not covered is the likeliest mis-join and is worth reading first.
A long one usually summarizes a paper section and says more than one theorem proves,
which is what the ledger's list-valued `decl` exists to record.  `REFUTED` rows are not
asked: their declaration is the refutation.

Jev (jev-1.13.0, last asked 2026-09-22) has answered
249 of the 251 resolved rows: 131 covered,
66 doubtful, 52 not covered; 118 are
listed below.

## 1. `J-paper-b-screen-is-a-walk-condition` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.65; different result 0.09.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** All three conditions of Paper B section 7's screen are functions of the exponent walk u_t = o_t log2(3) - t alone, and two of them are unit conditions on it. With e_t = 2^(u_t) (J-paper-b-E-is-the-exponent-walk): the branch-run condition e_{s-1} < 2 is u_{s-1} < 1, an absolute height; the linearisation criterion E < 2 is u_{t-1} - u_s < 1, a climb; and the 9/4 stopping threshold e_{t-1} - e_s > 9/4 is 2^(u_{t-1}) - 2^(u_s) > 9/4. Checked over every word of length 3 to 11: 4204 letters with a blocked defect, no mismatch on any of the three. Non-contraction is a condition on the same walk (1 <= e_t, i.e. u_t >= 0), so the property defining a contractor and the property tripping the branch-run hypothesis are one constraint at thresholds 0 and 1. At step two the first forces the second: a pref  *(truncated; read the ledger row)*

**Declarations.** `noncontracting_two_forces` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:260`

> A prefix that has not contracted by step two is `OO`, and then `e_2 = 9/4`, which already exceeds the branch-run threshold `2`.

```lean
theorem noncontracting_two_forces (c d : Letter)
    (h₁ : 1 ≤ iter [c]) (h₂ : 1 ≤ iter [c, d]) :
    c = Letter.O ∧ d = Letter.O ∧ iter [c, d] = 9 / 4
```

**And.** `two_lt_nine_quarters` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:273`

> The threshold itself: `9/4` is above the `2` at which branch runs stop existing, so the second letter of a non-contracting word already sits above it. `3 > 2 ^ (3/2)` is the same fact in the walk's coordinates.

```lean
theorem two_lt_nine_quarters : (2 : ℚ) < 9 / 4
```

## 2. `J-paper-b-count-is-the-level-zero-bad-count` &mdash; covers 0.04

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.35; different result 0.09.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** Paper B's non-contracting word count and Paper C's bad-word count are one function at two levels. N_d of Proposition 7.1 counts length-d words whose walk u_t = o_t log2(3) - t stays at or above 0; bad_word_count(L, d) counts those whose walk never reaches -L. Both are the same dynamic program over (steps, odd letters), written independently in paper_b_prefix_count and collision_large_sieve, and N_d = bad_word_count(0, d) exactly for d = 1 to 16 (1, 1, 2, 3, 4, 8, 13, 19, 38, 64, 128, 226, 367, 734, 1295, 2114). The agreement is exact and not approximate although one bound is strict and the other is not, because u_t = 0 would need 3^(o_t) = 2^t, which forces o_t = t = 0 (`three_pow_eq_two_pow`, `iter_eq_one_iff`, kernel-checked): the walk is never back at its starting level after a letter,   *(truncated; read the ledger row)*

**Declarations.** `iter_eq_one_iff` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:226`

> The walk is never back at its starting level after a letter: `e_t = 1` only for the empty word.

```lean
theorem iter_eq_one_iff (w : List Letter) : iter w = 1 ↔ w = []
```

**And.** `three_pow_eq_two_pow` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:215`

> `3 ^ a = 2 ^ n` only for `a = n = 0`.

```lean
theorem three_pow_eq_two_pow {a n : ℕ} (h : 3 ^ a = 2 ^ n) : a = 0 ∧ n = 0
```

**And.** `one_le_iff_one_lt` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:236`

> Hence on a non-empty word the two readings of non-contraction agree.

```lean
theorem one_le_iff_one_lt {w : List Letter} (hw : w ≠ []) :
    1 ≤ iter w ↔ 1 < iter w
```

## 3. `J-cycle-oe-quotient-parity-carry` &mdash; covers 0.07

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.39; different result 0.21.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Proposition E.2. For positive y and y^4<=N<(y+1)^4, let u=isqrt(N), c=u-y^2, d=(N-y^4) div (2y^2), h=min(d,2y). Then 0<=c<=2y and c<=h<=c+2. The exact 0/1/2 correction is recovered by the two adjacent square comparisons (baseline_zero_iff, baseline_one_iff, baseline_two_iff). For odd y, the hidden source u is even iff c is odd (square_guard_iff). With N=x^3 and an odd OE source, this is the exact internal guard. Kernel-verified quantified bounds and recovery; the sharpness example 93->896->29 is separately checked finite arithmetic. No arbitrary-word closure or cycle theorem is asserted.

**Declarations.** `baseline_bounds` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:17`

```lean
theorem baseline_bounds {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    N.sqrt ≤ baseline N y ∧ baseline N y ≤ N.sqrt + 2
```

**And.** `baseline` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:14`

> A clipped quotient provides three adjacent candidates for the integer root.

```lean
def baseline (N y : ℕ) : ℕ
```

**And.** `baseline_correction` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:55`

```lean
theorem baseline_correction {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    ∃ κ : ℕ, κ ≤ 2 ∧ baseline N y = N.sqrt + κ
```

**And.** `baseline_zero_iff` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:61`

```lean
theorem baseline_zero_iff {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    baseline N y = N.sqrt ↔ baseline N y ^ 2 ≤ N
```

**And.** `baseline_one_iff` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:72`

```lean
theorem baseline_one_iff {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    baseline N y = N.sqrt + 1 ↔
      (baseline N y - 1) ^ 2 ≤ N ∧ N < baseline N y ^ 2
```

**And.** `baseline_two_iff` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:89`

```lean
theorem baseline_two_iff {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    baseline N y = N.sqrt + 2 ↔ N < (baseline N y - 1) ^ 2
```

**And.** `square_guard_iff` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:102`

```lean
theorem square_guard_iff {N y : ℕ} (hy : y % 2 = 1)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    N.sqrt % 2 = 0 ↔ (N.sqrt - y ^ 2) % 2 = 1
```

## 4. `J-fate-recursion-lemma` &mdash; covers 0.07

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.53; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Lemma 5.1 (recursion lemma). Let e_i ∈ [e_min, e_max] with 0 < e_min and e_max < 1, c_i real, λ > 0 with ζ := Σ_i c_i e_i^λ - 1 > 0, t_1 > 0, c_0 > 0. Let g : ℝ → ℝ satisfy g(t) ≥ Σ_i (c_i - η_i(t)) g(e_i t) - η_0(t) for all t ≥ t_1, where 0 ≤ η_i(t) ≤ c_i, Σ_i η_i(t) e_i^λ ≤ ζ/3 and η_0(t) ≤ (2ζ/3) c_0 for t ≥ t_1, and g ≥ c_0 on [e_min t_1, t_1]. Then g(t) ≥ c_0 t_1^{-λ} t^λ for all t ≥ e_min t_1 (recursion_lemma). The proof is the paper's induction on N over [e_min t_1, t_1 e_max^{-N}], with exists_pow_lt_of_lt_one supplying N. Weaker hypotheses than the paper's: e_min, e_max are bounds rather than the extrema, λ < 1 and g ≥ 0 are not needed. Kernel-checked, axioms propext, Classical.choice, Quot.sound only. This is the abstract analytic step of Theorem 5.3; the three-source ine  *(truncated; read the ledger row)*

**Declaration.** `recursion_lemma` &mdash; kernel-checked, `Problems/Juggler/FateRecursion.lean:37`

> Paper C Lemma 5.1 (recursion lemma), with the range of the contraction factors given by two bounds `emin ≤ e i ≤ emax` rather than by a finite minimum and maximum. `K = c₀ * t₁ ^ (-λ)`.

```lean
theorem recursion_lemma {r : ℕ} (e c : Fin r → ℝ) (η : Fin r → ℝ → ℝ)
    (η₀ : ℝ → ℝ) (g : ℝ → ℝ) (lam t₁ c₀ emin emax : ℝ)
    (hlam : 0 < lam) (ht₁ : 0 < t₁) (hc₀ : 0 < c₀)
    (hemin : 0 < emin) (hemax : emax < 1)
    (he_lo : ∀ i, emin ≤ e i) (he_hi : ∀ i, e i ≤ emax)
    (hζ : 0 < ∑ i, c i * e i ^ lam - 1)
    (hη_lo : ∀ t, t₁ ≤ t → ∀ i, 0 ≤ η i t)
    (hη_hi : ∀ t, t₁ ≤ t → ∀ i, η i t ≤ c i)
    (hη₀ : ∀ t, t₁ ≤ t → η₀ t ≤ 2 * (∑ i, c i * e i ^ lam - 1) / 3 * c₀)
    (hηsum : ∀ t, t₁ ≤ t → ∑ i, η i t * e i ^ lam ≤ (∑ i, c i * e i ^ lam - 1) / 3)
    (hseed : ∀ t, emin * t₁ ≤ t → t ≤ t₁ → c₀ ≤ g t)
    (hrec : ∀ t, t₁ ≤ t → ∑ i, (c i - η i t) * g (e i * t) - η₀ t ≤ g t) :
```

## 5. `J-fate-energy-atoms` &mdash; covers 0.08

*Reads as: the claim asserts more than the declarations state (0.84).*

*Claim broader 0.84; declaration narrower 0.61; different result 0.39.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Section 10(d): the bias energy of the L-bad words supplies the exceptional atoms. energyOn y t S = sum over w in S of bias(w)^2 with bias(w) = #[wO] - #[w]/2 over the odd starts of (y, 2y]; biasEnergy y t is the sum over all words of length t, equal to the paper's C_{t+1}/2 - C_t/4 with C_t = sum of #[w]^2 (biasEnergy_eq, on CylinderEnergy.sum_bias_sq; wordCount_cylinder identifies the word count over the odd starts with the cylinder); badEnergy y L t is the sum over the L-bad words, at most the unrestricted one (badEnergy_le_biasEnergy). For a share q > 1/2, a bad atom violating #[wO] <= q #[w] has bias(w) > (q - 1/2) #[w], so the squared masses of the bad violators sum to at most badEnergy / (q - 1/2)^2, and Cauchy-Schwarz over the at most 2^t atoms of depth t (card_allWords) giv  *(truncated; read the ledger row)*

**Declarations.** `energy_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:234`

> **The conjecture from the energy bound, with nothing else assumed.** If at all large scales above a certified floor the bias energy of the `L(y)`-bad words at every depth `1 ≤ t < ⌈C L(y)⌉` is at most `(q - 1/2)² y² (log y)^{-2B} / 2^t`, with `C ≥ 5`, `1/2 < q < p_C`, `B > C log₂ x + 1 + e` and `27/40 < e < e_{C,q}`, then every positive integer reaches `1`.

```lean
theorem energy_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q B e : ℝ) (hC : 5 ≤ C)
    (hq : 1 / 2 < q) (hqp : q < pC C)
    (hB : C * Real.logb 2 (OneSided.tilt (pC C) q) + 1 + e < B)
    (he : e < OneSided.oneSidedExponent C q) (he7 : 27 / 40 < e)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → EnergyBound N₀ C q B y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `OneSidedShareExc.mono_err` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:49`

> A share bound with exceptional atoms and a smaller error is one with a larger error.

```lean
theorem OneSidedShareExc.mono_err {y : ℕ} {L q err err' exc : ℝ} {d : ℕ}
    (h : OneSidedShareExc y L q err exc d) (hle : err ≤ err') :
    OneSidedShareExc y L q err' exc d
```

**And.** `badEnergy_le_biasEnergy` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:80`

```lean
theorem badEnergy_le_biasEnergy (y : ℕ) (L : ℝ) (t : ℕ) :
    badEnergy y L t ≤ biasEnergy y t
```

**And.** `card_allWords` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:85`

> There are `2^t` words of length `t`.

```lean
theorem card_allWords : ∀ t, ((allWords t).card : ℝ) = 2 ^ t
  | 0 => by simp [allWords]
  | t + 1 => by
```

**And.** `mass_violators_le` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:95`

> **Cauchy–Schwarz on the bad violators.** For a share `q > 1/2`, `(Σ_{w bad, violating} #[w])² ≤ 2^t · badEnergy / (q - 1/2)²`.

```lean
theorem mass_violators_le (y : ℕ) (L : ℝ) (t : ℕ) {q : ℝ} (hq : 1 / 2 < q) :
    (∑ w ∈ violators y L t q, ((cylinder y t w).card : ℝ)) ^ 2
      ≤ 2 ^ t * (badEnergy y L t / (q - 1 / 2) ^ 2)
```

**And.** `oneSidedShareExc_of_energy` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:142`

> **Energy implies exceptional atoms.** If the bad energy at every depth `1 ≤ t < d` is at most `(q - 1/2)² exc² / 2^t`, the bad violators of the share bound `#[wO] ≤ q #[w]` have total mass at most `exc` at each depth, so the one-sided hypothesis holds with exceptional atoms of mass `exc` and no error term.

```lean
theorem oneSidedShareExc_of_energy {y d : ℕ} {L q exc : ℝ} (hq : 1 / 2 < q) (hexc : 0 ≤ exc)
    (h : ∀ t, 1 ≤ t → t < d → badEnergy y L t ≤ (q - 1 / 2) ^ 2 * exc ^ 2 / 2 ^ t) :
    OneSided.OneSidedShareExc y L q 0 exc d
```

**And.** `wordCount_cylinder` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:176`

> The word count of `CylinderEnergy` over the odd starts of `(y, 2y]` is the cylinder.

```lean
theorem wordCount_cylinder (y t : ℕ) {w : List Branch} (hw : w.length = t) :
    CylinderEnergy.wordCount (cylinder y 0 []) w = (cylinder y t w).card
```

**And.** `biasEnergy_eq` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:187`

> The unrestricted bias energy is the paper's `C_{t+1}/2 - C_t/4`, with `C_t = Σ_{|w|=t} #[w]²` (`CylinderEnergy.sum_bias_sq`).

```lean
theorem biasEnergy_eq (y t : ℕ) :
    biasEnergy y t = CylinderEnergy.energy (cylinder y 0 []) (t + 1) / 2
      - CylinderEnergy.energy (cylinder y 0 []) t / 4
```

**And.** `EnergyBound` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:200`

> The energy hypothesis at the scale `y`: at every depth `1 ≤ t < d(y) = ⌈C L(y)⌉`, the bias energy of the `L(y)`-bad words is at most `(q - 1/2)² (y (log y)^{-B})² / 2^t`.

```lean
def EnergyBound (N₀ : ℕ) (C q B : ℝ) (y : ℕ) : Prop
```

**And.** `oneSidedBoundExc_of_energy` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:206`

> The energy hypothesis gives `H_q(C, A)` with exceptional atoms of mass `y (log y)^{-B}`, for every `A`.

```lean
theorem oneSidedBoundExc_of_energy {N₀ : ℕ} {C q B : ℝ} {y : ℕ} (hq : 1 / 2 < q)
    (h : EnergyBound N₀ C q B y) (A : ℝ) : OneSided.OneSidedBoundExc N₀ C q A B y
```

**And.** `energy_conj_of_contagion` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:212`

> **The conjecture from the energy bound, with the contagion bound as a hypothesis.**

```lean
theorem energy_conj_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q B e : ℝ) (hC : 5 ≤ C)
    (hq : 1 / 2 < q) (hqp : q < pC C)
    (hB : C * Real.logb 2 (OneSided.tilt (pC C) q) + 1 + e < B)
    (he : e < OneSided.oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → EnergyBound N₀ C q B y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 6. `J-ooo-residual-cube` &mdash; covers 0.08

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.67; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** An odd state z ≥ (n+1)^2 has odd-step image at least (n+1)^3. Consequently, on OOO at q ≥ 5 the residual is T^3(q) ≥ (q+1)^3, not merely the next-square bound of ooo_suffix_threshold. On a CycleMin whose first odd run has length at least three, the first three-odd residual is at least (n+1)^3. Lean: odd_ge_succ_sq_floorPower_ge_cube, ooo_residual_ge_cube in Preimages.lean; cycleMin_ooo_residual_ge_cube in CycleMinObstruction.lean. The smallest universal local-overshoot A on CycleMin is 2, not 3. Not a halt theorem and not a contained-run prohibition.

**Declaration.** `cycleMin_ooo_residual_ge_cube` &mdash; kernel-checked, `Problems/Juggler/CycleMinObstruction.lean:41`

> On a `CycleMin` whose first odd run has length at least three, the first three-odd residual is at least `(n+1)^3`.

```lean
theorem cycleMin_ooo_residual_ge_cube {n a : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (ha : 3 ≤ a)
    (h : CycleMin n (oddEvenBlock a 1 ++ v)) :
    (n + 1) ^ 3 ≤ image n (List.replicate 3 Branch.odd)
```

## 7. `J-residual-floor-two-hundred-fifty-seven` &mdash; covers 0.08

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.54; different result 0.21.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Every positive integer strictly below 257 reaches 1 under the Juggler map (reachesOne_of_lt_two_hundred_fifty_seven). Evens below 2809 already reduce to the residual class {1,…,52}; the odd seeds 53,55,…,255 are finite orbit certificates. This is a finite certificate, not a halt theorem. Combined with cycleMin_finance and log 257 > 61/11 it excludes cycle lengths 19 and 38. The Lean constant 1 only needs n ln n > 1411.63 to kill length 19, so the smallest such n is 255; the Python 6/5 table has n_max(19) = 297.

**Declarations.** `reachesOne_of_lt_two_hundred_fifty_seven` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:325`

> Every positive residual strictly below 257 is ReachesOne. This is a finite certificate, not a halt theorem. Combined with cycleMin_finance it excludes cycle length 19.

```lean
theorem reachesOne_of_lt_two_hundred_fifty_seven {y : ℕ}
    (hpos : 1 ≤ y) (hy : y < 257) : ReachesOne y
```

**And.** `reachesOne_n53` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:16`

```lean
theorem reachesOne_n53 : ReachesOne 53
```

**And.** `reachesOne_n55` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:19`

```lean
theorem reachesOne_n55 : ReachesOne 55
```

**And.** `reachesOne_n57` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:22`

```lean
theorem reachesOne_n57 : ReachesOne 57
```

**And.** `reachesOne_n59` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:25`

```lean
theorem reachesOne_n59 : ReachesOne 59
```

**And.** `reachesOne_n61` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:28`

```lean
theorem reachesOne_n61 : ReachesOne 61
```

**And.** `reachesOne_n63` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:31`

```lean
theorem reachesOne_n63 : ReachesOne 63
```

**And.** `reachesOne_n65` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:34`

```lean
theorem reachesOne_n65 : ReachesOne 65
```

**And.** `reachesOne_n67` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:37`

```lean
theorem reachesOne_n67 : ReachesOne 67
```

**And.** `reachesOne_n69` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:40`

```lean
theorem reachesOne_n69 : ReachesOne 69
```

**And.** `reachesOne_n71` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:43`

```lean
theorem reachesOne_n71 : ReachesOne 71
```

**And.** `reachesOne_n73` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:46`

```lean
theorem reachesOne_n73 : ReachesOne 73
```

**And.** `reachesOne_n75` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:49`

```lean
theorem reachesOne_n75 : ReachesOne 75
```

**And.** `reachesOne_n77` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:52`

```lean
theorem reachesOne_n77 : ReachesOne 77
```

**And.** `reachesOne_n79` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:55`

```lean
theorem reachesOne_n79 : ReachesOne 79
```

**And.** `reachesOne_n81` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:58`

```lean
theorem reachesOne_n81 : ReachesOne 81
```

**And.** `reachesOne_n83` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:61`

```lean
theorem reachesOne_n83 : ReachesOne 83
```

**And.** `reachesOne_n85` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:64`

```lean
theorem reachesOne_n85 : ReachesOne 85
```

**And.** `reachesOne_n87` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:67`

```lean
theorem reachesOne_n87 : ReachesOne 87
```

**And.** `reachesOne_n89` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:70`

```lean
theorem reachesOne_n89 : ReachesOne 89
```

**And.** `reachesOne_n91` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:73`

```lean
theorem reachesOne_n91 : ReachesOne 91
```

**And.** `reachesOne_n93` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:76`

```lean
theorem reachesOne_n93 : ReachesOne 93
```

**And.** `reachesOne_n95` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:79`

```lean
theorem reachesOne_n95 : ReachesOne 95
```

**And.** `reachesOne_n97` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:82`

```lean
theorem reachesOne_n97 : ReachesOne 97
```

**And.** `reachesOne_n99` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:85`

```lean
theorem reachesOne_n99 : ReachesOne 99
```

**And.** `reachesOne_n101` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:88`

```lean
theorem reachesOne_n101 : ReachesOne 101
```

**And.** `reachesOne_n103` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:91`

```lean
theorem reachesOne_n103 : ReachesOne 103
```

**And.** `reachesOne_n105` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:94`

```lean
theorem reachesOne_n105 : ReachesOne 105
```

**And.** `reachesOne_n107` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:97`

```lean
theorem reachesOne_n107 : ReachesOne 107
```

**And.** `reachesOne_n109` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:100`

```lean
theorem reachesOne_n109 : ReachesOne 109
```

**And.** `reachesOne_n111` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:103`

```lean
theorem reachesOne_n111 : ReachesOne 111
```

**And.** `reachesOne_n113` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:106`

```lean
theorem reachesOne_n113 : ReachesOne 113
```

**And.** `reachesOne_n115` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:109`

```lean
theorem reachesOne_n115 : ReachesOne 115
```

**And.** `reachesOne_n117` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:112`

```lean
theorem reachesOne_n117 : ReachesOne 117
```

**And.** `reachesOne_n119` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:115`

```lean
theorem reachesOne_n119 : ReachesOne 119
```

**And.** `reachesOne_n121` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:118`

```lean
theorem reachesOne_n121 : ReachesOne 121
```

**And.** `reachesOne_n123` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:121`

```lean
theorem reachesOne_n123 : ReachesOne 123
```

**And.** `reachesOne_n125` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:124`

```lean
theorem reachesOne_n125 : ReachesOne 125
```

**And.** `reachesOne_n127` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:127`

```lean
theorem reachesOne_n127 : ReachesOne 127
```

**And.** `reachesOne_n129` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:130`

```lean
theorem reachesOne_n129 : ReachesOne 129
```

**And.** `reachesOne_n131` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:133`

```lean
theorem reachesOne_n131 : ReachesOne 131
```

**And.** `reachesOne_n133` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:136`

```lean
theorem reachesOne_n133 : ReachesOne 133
```

**And.** `reachesOne_n135` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:139`

```lean
theorem reachesOne_n135 : ReachesOne 135
```

**And.** `reachesOne_n137` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:142`

```lean
theorem reachesOne_n137 : ReachesOne 137
```

**And.** `reachesOne_n139` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:145`

```lean
theorem reachesOne_n139 : ReachesOne 139
```

**And.** `reachesOne_n141` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:148`

```lean
theorem reachesOne_n141 : ReachesOne 141
```

**And.** `reachesOne_n143` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:151`

```lean
theorem reachesOne_n143 : ReachesOne 143
```

**And.** `reachesOne_n145` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:154`

```lean
theorem reachesOne_n145 : ReachesOne 145
```

**And.** `reachesOne_n147` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:157`

```lean
theorem reachesOne_n147 : ReachesOne 147
```

**And.** `reachesOne_n149` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:160`

```lean
theorem reachesOne_n149 : ReachesOne 149
```

**And.** `reachesOne_n151` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:163`

```lean
theorem reachesOne_n151 : ReachesOne 151
```

**And.** `reachesOne_n153` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:166`

```lean
theorem reachesOne_n153 : ReachesOne 153
```

**And.** `reachesOne_n155` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:169`

```lean
theorem reachesOne_n155 : ReachesOne 155
```

**And.** `reachesOne_n157` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:172`

```lean
theorem reachesOne_n157 : ReachesOne 157
```

**And.** `reachesOne_n159` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:175`

```lean
theorem reachesOne_n159 : ReachesOne 159
```

**And.** `reachesOne_n161` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:178`

```lean
theorem reachesOne_n161 : ReachesOne 161
```

**And.** `reachesOne_n163` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:181`

```lean
theorem reachesOne_n163 : ReachesOne 163
```

**And.** `reachesOne_n165` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:184`

```lean
theorem reachesOne_n165 : ReachesOne 165
```

**And.** `reachesOne_n167` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:187`

```lean
theorem reachesOne_n167 : ReachesOne 167
```

**And.** `reachesOne_n169` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:190`

```lean
theorem reachesOne_n169 : ReachesOne 169
```

**And.** `reachesOne_n171` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:193`

```lean
theorem reachesOne_n171 : ReachesOne 171
```

**And.** `reachesOne_n173` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:196`

```lean
theorem reachesOne_n173 : ReachesOne 173
```

**And.** `reachesOne_n175` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:199`

```lean
theorem reachesOne_n175 : ReachesOne 175
```

**And.** `reachesOne_n177` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:202`

```lean
theorem reachesOne_n177 : ReachesOne 177
```

**And.** `reachesOne_n179` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:205`

```lean
theorem reachesOne_n179 : ReachesOne 179
```

**And.** `reachesOne_n181` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:208`

```lean
theorem reachesOne_n181 : ReachesOne 181
```

**And.** `reachesOne_n183` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:211`

```lean
theorem reachesOne_n183 : ReachesOne 183
```

**And.** `reachesOne_n185` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:214`

```lean
theorem reachesOne_n185 : ReachesOne 185
```

**And.** `reachesOne_n187` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:217`

```lean
theorem reachesOne_n187 : ReachesOne 187
```

**And.** `reachesOne_n189` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:220`

```lean
theorem reachesOne_n189 : ReachesOne 189
```

**And.** `reachesOne_n191` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:223`

```lean
theorem reachesOne_n191 : ReachesOne 191
```

**And.** `reachesOne_n193` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:226`

```lean
theorem reachesOne_n193 : ReachesOne 193
```

**And.** `reachesOne_n195` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:229`

```lean
theorem reachesOne_n195 : ReachesOne 195
```

**And.** `reachesOne_n197` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:232`

```lean
theorem reachesOne_n197 : ReachesOne 197
```

**And.** `reachesOne_n199` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:235`

```lean
theorem reachesOne_n199 : ReachesOne 199
```

**And.** `reachesOne_n201` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:238`

```lean
theorem reachesOne_n201 : ReachesOne 201
```

**And.** `reachesOne_n203` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:241`

```lean
theorem reachesOne_n203 : ReachesOne 203
```

**And.** `reachesOne_n205` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:244`

```lean
theorem reachesOne_n205 : ReachesOne 205
```

**And.** `reachesOne_n207` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:247`

```lean
theorem reachesOne_n207 : ReachesOne 207
```

**And.** `reachesOne_n209` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:250`

```lean
theorem reachesOne_n209 : ReachesOne 209
```

**And.** `reachesOne_n211` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:253`

```lean
theorem reachesOne_n211 : ReachesOne 211
```

**And.** `reachesOne_n213` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:256`

```lean
theorem reachesOne_n213 : ReachesOne 213
```

**And.** `reachesOne_n215` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:259`

```lean
theorem reachesOne_n215 : ReachesOne 215
```

**And.** `reachesOne_n217` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:262`

```lean
theorem reachesOne_n217 : ReachesOne 217
```

**And.** `reachesOne_n219` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:265`

```lean
theorem reachesOne_n219 : ReachesOne 219
```

**And.** `reachesOne_n221` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:268`

```lean
theorem reachesOne_n221 : ReachesOne 221
```

**And.** `reachesOne_n223` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:271`

```lean
theorem reachesOne_n223 : ReachesOne 223
```

**And.** `reachesOne_n225` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:274`

```lean
theorem reachesOne_n225 : ReachesOne 225
```

**And.** `reachesOne_n227` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:277`

```lean
theorem reachesOne_n227 : ReachesOne 227
```

**And.** `reachesOne_n229` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:280`

```lean
theorem reachesOne_n229 : ReachesOne 229
```

**And.** `reachesOne_n231` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:283`

```lean
theorem reachesOne_n231 : ReachesOne 231
```

**And.** `reachesOne_n233` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:286`

```lean
theorem reachesOne_n233 : ReachesOne 233
```

**And.** `reachesOne_n235` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:289`

```lean
theorem reachesOne_n235 : ReachesOne 235
```

**And.** `reachesOne_n237` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:292`

```lean
theorem reachesOne_n237 : ReachesOne 237
```

**And.** `reachesOne_n239` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:295`

```lean
theorem reachesOne_n239 : ReachesOne 239
```

**And.** `reachesOne_n241` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:298`

```lean
theorem reachesOne_n241 : ReachesOne 241
```

**And.** `reachesOne_n243` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:301`

```lean
theorem reachesOne_n243 : ReachesOne 243
```

**And.** `reachesOne_n245` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:304`

```lean
theorem reachesOne_n245 : ReachesOne 245
```

**And.** `reachesOne_n247` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:307`

```lean
theorem reachesOne_n247 : ReachesOne 247
```

**And.** `reachesOne_n249` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:310`

```lean
theorem reachesOne_n249 : ReachesOne 249
```

**And.** `reachesOne_n251` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:313`

```lean
theorem reachesOne_n251 : ReachesOne 251
```

**And.** `reachesOne_n253` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:316`

```lean
theorem reachesOne_n253 : ReachesOne 253
```

**And.** `reachesOne_n255` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:319`

```lean
theorem reachesOne_n255 : ReachesOne 255
```

**And.** `non_reachesOne_ge_two_hundred_fifty_seven` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:464`

> A positive non-ReachesOne value cannot lie in {1,…,256}.

```lean
theorem non_reachesOne_ge_two_hundred_fifty_seven {n : ℕ}
    (hn : 1 ≤ n) (hfail : ¬ReachesOne n) : 257 ≤ n
```

## 8. `J-cubic-equal-gap-oo-triple` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.48; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every odd t>=9, the three sources t^2-4, t^2, t^2+4 and images t^3-6t, t^3, t^3+6t are odd, CubicReturn.O hits those images, the lower remainders are 12t^2-64, 0, 12t^2+64, and the three upper complements are 2t^3-12t^2-12t+65, 2t^3+1, 2t^3-12t^2+12t-63. Adjacent pairs have source gap 4, image gap 6t and gcd 2. The two raw complement changes 12t^2+12t-64 and 12t^2-12t+64 are positive and each plus its matching complement equals 2t^3+1. This is the integer content of the Result 15 OO family only. The normalized log-log comparison RC48, signed orientation and any cycle theorem remain written.

**Declaration.** `oo_equal_gap_triple` &mdash; kernel-checked, `Problems/Juggler/CriticalCostKernel.lean:279`

> Exact equal-gap OO triple of Result 15. Integer cells, remainders, complements and opposite raw complement signs; the log-log comparison RC48 remains written.

```lean
theorem oo_equal_gap_triple {t : ℕ} (ht : 9 ≤ t) (hodd : t % 2 = 1) :
    let xm
```

## 9. `J-cycle-periodic-return-height-strip` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.54; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Theorem 3.39. For every actual cycle with attained minimum m>=5 and maximum M<m^3, t=isqrt(M) and z=F_OOE(m) satisfy t^3+2<=[z(z-2)]^2 and M+2<=(t+1)^2 (cycleMin_exact_return_seam). The periodic E-image section is exactly C intersect [m,O(m)); its extrema return images have a strict odd gap, derived from actual periodicity and injectivity rather than assumed. For m>=7, m^15<(m^3-M)^8 (cycleMin_height_strip), equivalently M<m^3-m^(15/8); the all-states version is cycleMin_all_states_height_strip. Every threshold cycle in the complementary top strip has a wrong-parity state (threshold_cycle_wrong_parity). Exact OE/OOE cells identify the odd endpoint z. The sharper fractional bound for t, maximum-odd-integer ceiling restatement, and full rank adjacency are separately written consequen  *(truncated; read the ledger row)*

**Declarations.** `cycleMin_height_strip` &mdash; kernel-checked, `Problems/Juggler/CubicReturnStrip.lean:24`

> A cycle spelled by the repository's exact `CycleMin` predicate has the same height restriction, without an additional parity or return hypothesis.

```lean
theorem cycleMin_height_strip {m M : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 7 ≤ m) (hM : M < m ^ 3)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    m ^ 15 < (m ^ 3 - M) ^ 8
```

**And.** `height_strip` &mdash; kernel-checked, `Problems/Juggler/CubicReturnStrip.lean:8`

> Exact first-return ordering excludes the terminal strip of a cubic band. The integer conclusion is equivalent to `M < m³ - m^(15/8)`.

```lean
theorem height_strip {C : Set ℕ} {m M : ℕ}
    (D : PeriodicExtrema C m M) (hm : 7 ≤ m) (hM : M < m ^ 3) :
    m ^ 15 < (m ^ 3 - M) ^ 8
```

**And.** `periodicOrbit_height_strip` &mdash; kernel-checked, `Problems/Juggler/CubicReturnStrip.lean:15`

> The height-strip restriction applies to every ordinary actual periodic orbit.

```lean
theorem periodicOrbit_height_strip {m M k : ℕ} (hm : 7 ≤ m) (hk : 0 < k)
    (hp : floorPower^[k] m = m) (hM : M < m ^ 3)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    m ^ 15 < (m ^ 3 - M) ^ 8
```

**And.** `cycleMin_all_states_height_strip` &mdash; kernel-checked, `Problems/Juggler/CubicReturnStrip.lean:32`

> No choice of a maximum is needed in the all-states formulation.

```lean
theorem cycleMin_all_states_height_strip {m : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 7 ≤ m)
    (hcubic : ∀ j < w.length, floorPower^[j] m < m ^ 3) :
    ∀ j < w.length, m ^ 15 < (m ^ 3 - floorPower^[j] m) ^ 8
```

**And.** `threshold_cycle_wrong_parity` &mdash; kernel-checked, `Problems/Juggler/CubicReturnStrip.lean:43`

> An exact threshold cycle in the excluded strip must fail actual source parity at some state of its period. This statement concerns only the specified strip.

```lean
theorem threshold_cycle_wrong_parity {b m M k : ℕ} (hb : 3 ≤ b) (hm : 7 ≤ m)
    (hx : InCubicBand b m) (hk : 0 < k)
    (hp : (thresholdMap b)^[k] m = m) (hM : M < m ^ 3)
    (hbound : ∀ j < k,
      m ≤ (thresholdMap b)^[j] m ∧ (thresholdMap b)^[j] m ≤ M)
    (hmax : ∃ j < k, (thresholdMap b)^[j] m = M)
    (hstrip : (m ^ 3 - M) ^ 8 ≤ m ^ 15) :
    ∃ j < k, ¬ (((thresholdMap b)^[j] m) % 2 = 1 ↔
      (thresholdMap b)^[j] m < b ^ 2)
```

## 10. `J-cycle-threshold-common-period` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.51; different result 0.28.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For a fixed integer b>=3, all primitive cycles of the size-switched threshold map S_b have the same period L, branch counts (o,e), and minimum-based ceiling mechanical word. If there are t cycles, they interlace: each occupies one rank residue class modulo t in the sorted union of all periodic points. Proof: on that finite invariant union, branch image separation and injectivity give rank addition by E, the total upper-branch count; t=gcd(N,E), L=N/t, e=E/t. No uniqueness, uniform wrong-parity intersection or actual Juggler cycle exclusion follows. Consolidated in Paper A Section 3.10 and formalized in the seven Cubic modules. The cited declarations and supporting modules are compiled kernel proofs. The illustrative asymptotic comparison and universal wrong-parity question are not promoted  *(truncated; read the ledger row)*

**Declarations.** `rankRotation_orbit_iff_residue` &mdash; kernel-checked, `Problems/Juggler/CubicInterlacing.lean:80`

> Two ranks belong to the same orbit exactly when their gcd residues agree.

```lean
theorem rankRotation_orbit_iff_residue {L e : ℕ} (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) (i j : Fin L) :
    (∃ k : ℕ, p^[k] i = j) ↔ i.val % L.gcd e = j.val % L.gcd e
```

**And.** `rankRotation_orbit_representatives` &mdash; kernel-checked, `Problems/Juggler/CubicInterlacing.lean:95`

> Ranks 0 through g-1 give exactly one representative for each orbit.

```lean
theorem rankRotation_orbit_representatives {L e : ℕ} (hL : 0 < L)
    (p : Fin L → Fin L) (hrot : ∀ i, (p i).val = (i.val + e) % L)
    (i : Fin L) :
    ∃! r : Fin (L.gcd e), ∃ k : ℕ,
      p^[k] ⟨r.val, lt_of_lt_of_le r.isLt (Nat.le_of_dvd hL (Nat.gcd_dvd_left L e))⟩ = i
```

**And.** `rankRotation_orbit_upper_card` &mdash; kernel-checked, `Problems/Juggler/CubicInterlacing.lean:171`

> Every orbit has e/g upper ranks, even when the translation has several cycles.

```lean
theorem rankRotation_orbit_upper_card {L e : ℕ} (he : e ≤ L)
    (p : Fin L → Fin L) (hrot : ∀ i, (p i).val = (i.val + e) % L)
    (i : Fin L) :
    (((Finset.range (L / L.gcd e)).image (fun k => p^[k] i)).filter
      (fun j => L - e ≤ j.val)).card = e / L.gcd e
```

**And.** `rankResidue_interlaces` &mdash; kernel-checked, `Problems/Juggler/CubicInterlacing.lean:182`

> Sorted residue classes alternate in the same order in every block of g ranks.

```lean
theorem rankResidue_interlaces {g r s q : ℕ} (hrs : r < s) (hs : s < g) :
    q * g + r < q * g + s ∧ q * g + s < (q + 1) * g + r
```

**And.** `rankRotation_orbit_finset` &mdash; kernel-checked, `Problems/Juggler/CubicInterlacing.lean:57`

> A full least-period orbit fills its entire gcd residue class.

```lean
theorem rankRotation_orbit_finset {L e : ℕ} (p : Fin L → Fin L)
    (hrot : ∀ i, (p i).val = (i.val + e) % L) (i : Fin L) :
    (Finset.range (L / L.gcd e)).image (fun k => p^[k] i) =
      Finset.univ.filter (fun j : Fin L => j.val % L.gcd e = i.val % L.gcd e)
```

**And.** `rankResidue_range_card` &mdash; kernel-checked, `Problems/Juggler/CubicInterlacing.lean:14`

```lean
theorem rankResidue_range_card {N g r : ℕ} (hg : 0 < g) (hd : g ∣ N)
    (hr : r < g) :
    ((Finset.range N).filter (fun x => x % g = r)).card = N / g
```

**And.** `rankResidue_fin_card` &mdash; kernel-checked, `Problems/Juggler/CubicInterlacing.lean:39`

```lean
theorem rankResidue_fin_card {N g r : ℕ} (hg : 0 < g) (hd : g ∣ N)
    (hr : r < g) :
    (Finset.univ.filter (fun x : Fin N => x.val % g = r)).card = N / g
```

**And.** `rankResidue_parameterization` &mdash; kernel-checked, `Problems/Juggler/CubicInterlacing.lean:111`

> The increasing positions in a residue class are r, g+r, 2g+r, and so forth.

```lean
theorem rankResidue_parameterization {L g r : ℕ} (hg : 0 < g)
    (hd : g ∣ L) (hr : r < g) (i : Fin L) :
    i.val % g = r ↔ ∃! q : Fin (L / g), i.val = q.val * g + r
```

**And.** `rankResidue_upper_card` &mdash; kernel-checked, `Problems/Juggler/CubicInterlacing.lean:133`

> The upper tail has the same residue proportions when its length is divisible by g.

```lean
theorem rankResidue_upper_card {L e g r : ℕ} (he : e ≤ L) (hg : 0 < g)
    (hL : g ∣ L) (he' : g ∣ e) (hr : r < g) :
    (Finset.univ.filter (fun x : Fin L => x.val % g = r ∧ L - e ≤ x.val)).card =
      e / g
```

## 11. `OST-np-adjoint-window-det` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.52; different result 0.71.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP and n≥2, the determinant of consecutive adjoints (u_n, u_{n-1}, u_{n-2}) equals 3^{n-2}, so neighboring energies invert s over Q; this is not a bound on L_0

**Declarations.** `adjointDet_eq` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:335`

> Consecutive adjoints are independent: `det = 3^{n-2}` for `n ≥ 2`. Neighboring energies invert `s` over `ℚ`. Not a bound on `L₀`.

```lean
theorem adjointDet_eq (n : ℕ) (hn : 2 ≤ n) :
    adjointDet n = (3 : ℤ) ^ (n - 2)
```

**And.** `adjointDet` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:248`

> `det(u_n, u_{n-1}, u_{n-2})`.

```lean
def adjointDet (n : ℕ) : ℤ
```

**And.** `adjointDet_ne_zero` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:350`

```lean
theorem adjointDet_ne_zero (n : ℕ) (hn : 2 ≤ n) : adjointDet n ≠ 0
```

**And.** `energy_eq_dot` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:101`

```lean
theorem energy_eq_dot (i : ℕ) (s1 s2 s3 : ℤ) :
    energy i (s1, s2, s3) =
      (adjointU i).1 * s1 + (adjointU i).2.1 * s2 + (adjointU i).2.2 * s3
```

## 12. `J-cycle-absolute-cell-grid-charge` &mdash; covers 0.11

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.61; different result 0.21.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** For a primitive exact threshold cycle S_b, or an actual Juggler cycle with minimum m>1 and maximum M<m^3, let L,o be its period and lower/odd count, T=log 3, Lambda=o log 3-L log 2>0, and A=(log m) exp(-(1-1/L)Lambda)>0. Then Lambda < exp(-A)/A times the finite sum over 0<=i<L of exp(-i T(A+1)/L), and exp(A) A(A+1)Lambda < A+1+L/T. The exact upper unit cells bound each logarithmic defect by 1/(y log y); the sorted grid bounds the total by a geometric sum. Along sequences with log m tending to infinity, log m=o(L), and Lambda log m tending to zero, this yields m(log m)^2 Lambda <= (1+o(1))L/log 3. In the explicitly conditional regime Lambda~c/L and polynomially growing m, this narrows the necessary scale to m(log m)^2<=(1+o(1))L^2/(c log 3). No uniform lower bound of order 1/L for Lambda is  *(truncated; read the ledger row)*

**Declarations.** `power_cells_grid_charge` &mdash; kernel-checked, `Problems/Juggler/CubicUpperCells.lean:250`

> The exact finite and closed upper-cell charges from primitive power-cell data.

```lean
theorem power_cells_grid_charge [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hlower : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2) :
    let A
```

**And.** `power_cells_scaled_charge` &mdash; kernel-checked, `Problems/Juggler/CubicUpperCells.lean:271`

> A denominator-free exact corollary of the closed charge.

```lean
theorem power_cells_scaled_charge [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hlower : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2) :
    let A
```

**And.** `logCellDefect_lt_logEta` &mdash; kernel-checked, `Problems/Juggler/CubicUpperCells.lean:11`

> The strict upper square cell bounds the logarithmic defect by its target capacity.

```lean
theorem logCellDefect_lt_logEta
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o : ℕ)
    (hc : ∀ i, 1 < c i)
    (hupper : ∀ i, c i ^ (if i.val < o then 3 else 1) < (c (σ i) + 1) ^ 2)
    (i : Fin L) : logCellDefect c σ o i < LogCells.logEta (c (σ i))
```

**And.** `inv_log_sum_le_grid` &mdash; kernel-checked, `Problems/Juggler/CubicUpperCells.lean:183`

> The grid supplies a finite, unlinearized upper-cell charge majorant.

```lean
theorem inv_log_sum_le_grid [NeZero L]
    (c : Fin L → ℝ) (o : ℕ) (hc : ∀ i, 1 < c i)
    (hgrid : ∀ i, |logGridError c (c 0) i| ≤
      (1 - 1 / (L : ℝ)) * logGridSurplus L o) :
    (∑ i, 1 / (c i * Real.log (c i))) ≤
      ∑ i : Fin L,
        Real.exp (-(logGridScale (L
```

**And.** `grid_charge_le_geometric` &mdash; kernel-checked, `Problems/Juggler/CubicUpperCells.lean:198`

> The finite unlinearized charge is bounded by the finite geometric charge.

```lean
theorem grid_charge_le_geometric [NeZero L] {A : ℝ} (hA : 0 < A) :
    (∑ i : Fin L,
      Real.exp (-(A * Real.exp ((i.val : ℝ) * Real.log 3 / (L : ℝ))) -
        (i.val : ℝ) * Real.log 3 / (L : ℝ)) / A) ≤
      Real.exp (-A) / A *
        ∑ i : Fin L, Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ)))
```

**And.** `geometric_grid_charge_lt` &mdash; kernel-checked, `Problems/Juggler/CubicUpperCells.lean:208`

> Strict finite-to-closed geometric charge comparison.

```lean
theorem geometric_grid_charge_lt [NeZero L] {A : ℝ} (hA : 0 < A) :
    Real.exp (-A) / A *
        (∑ i : Fin L, Real.exp (-(A + 1) * ((i.val : ℝ) * Real.log 3 / (L : ℝ)))) <
      Real.exp (-A) / A * (1 + (L : ℝ) / (Real.log 3 * (A + 1)))
```

**And.** `threshold_cycle_upper_charge` &mdash; kernel-checked, `Problems/Juggler/CubicUpperCells.lean:382`

> Compatibility projection to the original threshold charge conclusion.

```lean
theorem threshold_cycle_upper_charge [NeZero L]
    {b : ℕ} (hb : 1 < b) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand b (c i))
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, (thresholdMap b)^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i < b ^ 2)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o ∧
      UpperCellChargeBounds (L
```

**And.** `cubicBand_cycle_upper_charge` &mdash; kernel-checked, `Problems/Juggler/CubicUpperCells.lean:433`

> Compatibility projection to the original actual-cycle charge conclusion.

```lean
theorem cubicBand_cycle_upper_charge [NeZero L]
    {m : ℕ} (hm : 1 < m) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand m (c i))
    (hstep : ∀ i, c (σ i) = floorPower (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, floorPower^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o ∧
      UpperCellChargeBounds (L
```

## 13. `J-cycle-quartic-formal-budget` &mdash; covers 0.11

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.55; different result 0.5.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** A finite injective actual-block substitution with nonnegative actual defects and one omitted positive defect gives a strict defect budget. Given the explicit component count/total calibration and displacement bounds, the budget gives a normalized gap witness above tau. With A=log(3/2), actual loglog source gaps, integer OE cells and the small-product condition, the witness has an unselected B valley. The strict budget is derived from the certificate, not assumed. Constructing all certificate fields and original-cycle count identities for arbitrary primitive quartic cycles remains unformalized; this is not an unconditional cycle exclusion. Additional pointwise and finite-sum support inequalities hold for supplied real pair records: k<=u, 0<=v, D<=u+v and coefficient bounds give located min/  *(truncated; read the ledger row)*

**Declarations.** `BlockSubstitution.strict_budget` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:43`

> A positive omitted actual block makes the substitution budget strict.

```lean
theorem BlockSubstitution.strict_budget {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s) :
    (∑ i ∈ periodic, d i) + (∑ i ∈ periodic, s i) < ∑ a ∈ actual, D a
```

**And.** `BlockSubstitution.component_budget` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:94`

> The component inequality is derived from the finite actual-block partition.

```lean
theorem BlockSubstitution.component_budget {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    {e n Λ lam Δ A Γ : ℝ} (he : 0 < e)
    (htotal : ∑ a ∈ actual, D a = Λ)
    (hformal : ∑ i ∈ periodic, d i = lam)
    (hshift : -Γ ≤ ∑ i ∈ periodic, s i)
    (hcal : e * lam = n * Λ + Δ * A) :
    Δ * A < (e - n) * Λ + e * Γ
```

**And.** `BlockSubstitution.unselected_valley_witness` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:287`

> A projection fixed on selected valleys turns the unequal-cell witness into a hole.

```lean
theorem BlockSubstitution.unselected_valley_witness {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    (negative : Finset β) (displacement : β → ℝ) (source predecessor : β → ℕ)
    (selected : Set ℕ) {m : ℕ} {e n Λ lam Δ : ℝ}
    (hm : 1 < m) (he : 2 ≤ e) (hΛ : 0 < Λ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hsmall : (e - 1) * Λ + e * QuarticCells.logEta (m : ℝ) ≤ Real.log (3 / 2 : ℝ))
    (htotal : ∑ a ∈ actual, D a = Λ)
    (hformal : ∑ i ∈ periodic, d i = lam)
    (hshift : -(∑ i ∈ negative, loglogGap (source i) (predecessor i)) ≤
      ∑ i ∈ periodic, s i)
```

**And.** `located_pair_lower` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:315`

> A located lower charge and a pair demand give a signed support bound.

```lean
theorem located_pair_lower {a b α u v k D : ℝ}
    (ha : α ≤ a) (hb : α ≤ b) (hu : k ≤ u)
    (hv : 0 ≤ v) (hsum : D ≤ u + v) :
    a * k + min a b * (D - k) + α * (u + v - D) ≤ a * u + b * v
```

**And.** `located_pair_upper` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:328`

> The same located charge gives the corresponding upper support bound.

```lean
theorem located_pair_upper {a b β u v k D : ℝ}
    (ha : a ≤ β) (hb : b ≤ β) (hu : k ≤ u)
    (hv : 0 ≤ v) (hsum : D ≤ u + v) :
    a * u + b * v ≤ a * k + max a b * (D - k) + β * (u + v - D)
```

**And.** `located_pairs_lower` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:341`

> Summing disjoint pair records retains the exact total residual term.

```lean
theorem located_pairs_lower {ι : Type*} (S : Finset ι)
    (a b u v k D : ι → ℝ) (α : ℝ)
    (ha : ∀ i ∈ S, α ≤ a i) (hb : ∀ i ∈ S, α ≤ b i)
    (hu : ∀ i ∈ S, k i ≤ u i) (hv : ∀ i ∈ S, 0 ≤ v i)
    (hsum : ∀ i ∈ S, D i ≤ u i + v i) :
    (∑ i ∈ S, (a i * k i + min (a i) (b i) * (D i - k i))) +
        α * ((∑ i ∈ S, (u i + v i)) - ∑ i ∈ S, D i) ≤
      ∑ i ∈ S, (a i * u i + b i * v i)
```

**And.** `located_pairs_upper` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:355`

> The finite upper bound uses the same located and flexible charges.

```lean
theorem located_pairs_upper {ι : Type*} (S : Finset ι)
    (a b u v k D : ι → ℝ) (β : ℝ)
    (ha : ∀ i ∈ S, a i ≤ β) (hb : ∀ i ∈ S, b i ≤ β)
    (hu : ∀ i ∈ S, k i ≤ u i) (hv : ∀ i ∈ S, 0 ≤ v i)
    (hsum : ∀ i ∈ S, D i ≤ u i + v i) :
    (∑ i ∈ S, (a i * u i + b i * v i)) ≤
      (∑ i ∈ S, (a i * k i + max (a i) (b i) * (D i - k i))) +
        β * ((∑ i ∈ S, (u i + v i)) - ∑ i ∈ S, D i)
```

**And.** `calibrated_component_budget` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:86`

> Calibrating the strict component budget produces the signed loss inequality.

```lean
theorem calibrated_component_budget {e n Λ lam Δ A Γ : ℝ}
    (he : 0 < e) (hbudget : lam - Γ < Λ)
    (hcal : e * lam = n * Λ + Δ * A) :
    Δ * A < (e - n) * Λ + e * Γ
```

**And.** `weighted_gap_witness` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:109`

> Positive displacements turn a strict total gap into a normalized witness.

```lean
theorem weighted_gap_witness {ι : Type*} (S : Finset ι)
    (displacement gap : ι → ℝ) {Δ τ : ℝ}
    (hτ : 0 ≤ τ) (hd : ∀ i ∈ S, 0 < displacement i)
    (hsum : ∑ i ∈ S, displacement i ≤ Δ)
    (hgap : Δ * τ < ∑ i ∈ S, gap i) :
    ∃ i ∈ S, τ < gap i / displacement i
```

**And.** `weighted_uncovered_witness` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:129`

> A unit lower bound and the covered-cell cap identify an uncovered witness.

```lean
theorem weighted_uncovered_witness {ι : Type*} (S : Finset ι)
    (displacement gap : ι → ℝ) (covered : ι → Prop) {Δ τ η : ℝ}
    (hη : 0 ≤ η) (hητ : η ≤ τ)
    (hd : ∀ i ∈ S, 1 ≤ displacement i)
    (hsum : ∑ i ∈ S, displacement i ≤ Δ)
    (hgap : Δ * τ < ∑ i ∈ S, gap i)
    (hcovered : ∀ i ∈ S, covered i → gap i < η) :
    ∃ i ∈ S, ¬ covered i ∧ τ < gap i / displacement i
```

**And.** `gapThreshold_ge` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:158`

> The small-product hypothesis gives the positive covered-cell threshold.

```lean
theorem gapThreshold_ge {e n Λ Δ A η : ℝ}
    (he : 2 ≤ e) (hΛ : 0 < Λ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hsmall : (e - 1) * Λ + e * η ≤ A) :
    η ≤ gapThreshold e n Λ Δ A
```

**And.** `gapThreshold_sum_lt` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:177`

> A calibrated strict budget is the weighted sum threshold used above.

```lean
theorem gapThreshold_sum_lt {ι : Type*} (S : Finset ι) (gap : ι → ℝ)
    {e n Λ Δ A : ℝ} (he : 0 < e) (hΔ : 0 < Δ)
    (hbudget : Δ * A < (e - n) * Λ + e * ∑ i ∈ S, gap i) :
    Δ * gapThreshold e n Λ Δ A < ∑ i ∈ S, gap i
```

**And.** `BlockSubstitution.uncovered_component_witness` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:188`

> A finite actual-block certificate yields the normalized uncovered witness.

```lean
theorem BlockSubstitution.uncovered_component_witness {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    (negative : Finset β) (displacement gap : β → ℝ) (covered : β → Prop)
    {e n Λ lam Δ A η : ℝ}
    (he : 2 ≤ e) (hΛ : 0 < Λ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hη : 0 ≤ η) (hsmall : (e - 1) * Λ + e * η ≤ A)
    (htotal : ∑ a ∈ actual, D a = Λ)
    (hformal : ∑ i ∈ periodic, d i = lam)
    (hshift : -(∑ i ∈ negative, gap i) ≤ ∑ i ∈ periodic, s i)
    (hcal : e * lam = n * Λ + Δ * A)
```

**And.** `BlockSubstitution.unequal_cell_witness` &mdash; kernel-checked, `Problems/Juggler/QuarticLossBudget.lean:255`

> Exact integer B cells discharge the covered-gap premise of the finite budget.

```lean
theorem BlockSubstitution.unequal_cell_witness {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    (negative : Finset β) (displacement : β → ℝ) (source predecessor : β → ℕ)
    {m : ℕ} {e n Λ lam Δ : ℝ}
    (hm : 1 < m) (he : 2 ≤ e) (hΛ : 0 < Λ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hsmall : (e - 1) * Λ + e * QuarticCells.logEta (m : ℝ) ≤ Real.log (3 / 2 : ℝ))
    (htotal : ∑ a ∈ actual, D a = Λ)
    (hformal : ∑ i ∈ periodic, d i = lam)
    (hshift : -(∑ i ∈ negative, loglogGap (source i) (predecessor i)) ≤
      ∑ i ∈ periodic, s i)
```

## 14. `J-cycle-direction-change-batches` &mdash; covers 0.12

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.44; different result 0.4.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For a guarded sorted OOE/OE return model with positive counts a,b and least source at least m>=2^24, the first maximal left and right batches have quotient2 and nonzero remainders: a=2b+r,b=2r+s,0<s<r<b. dc_rank_stages proves this from exact guarded rank equations and compiled growth/decrease inequalities, including terminal equality. periodicExtrema_return_model constructs this model for an actual cycle with M<m^3. periodicExtrema_dc_transfers proves that the left steps recycle one seam and the next two right steps genuinely transfer it through C. The broader unguarded threshold-model version remains written; this Lean row states the guarded version.

**Declarations.** `dc_rank_stages` &mdash; kernel-checked, `Problems/Juggler/ReturnQuotients.lean:77`

> The first two accelerated batches are forced by exact map inequalities.

```lean
theorem dc_rank_stages {a b m : ℕ} {y : ℕ → ℕ}
    (h : RankedReturn a b y wordA wordB) (ha : 0 < a) (hb : 0 < b)
    (hm : 2 ^ 24 ≤ m) (hy : m ≤ y 0) :
    ∃ r s, 0 < s ∧ s < r ∧ r < b ∧ a = 2 * b + r ∧ b = 2 * r + s ∧
      RankedReturn r b y wordA wordC ∧ RankedReturn r s y wordD wordC
```

**And.** `force_two_left` &mdash; kernel-checked, `Problems/Juggler/ReturnQuotients.lean:24`

> Two left steps and the following direction change, including terminal exclusion.

```lean
theorem force_two_left (ha : 0 < a) (hb : 0 < b) (hm : m ≤ y 0)
    (hd₁ : ∀ x, m ≤ x → follows x (U ++ V) → image x (U ++ V) < x)
    (hd₂ : ∀ x, m ≤ x → follows x (U ++ (U ++ V)) →
      image x (U ++ (U ++ V)) < x)
    (hg : ∀ x, m ≤ x → follows x (U ++ (U ++ (U ++ V))) →
      x < image x (U ++ (U ++ (U ++ V)))) :
    2 * b < a ∧ a < 3 * b ∧
      RankedReturn (a - 2 * b) b y U (U ++ (U ++ V))
```

**And.** `force_two_right` &mdash; kernel-checked, `Problems/Juggler/ReturnQuotients.lean:41`

> Two right steps and the following direction change, with positive remainder.

```lean
theorem force_two_right (ha : 0 < a) (hab : a < b) (hm : m ≤ y 0)
    (hg : ∀ x, m ≤ x → follows x ((U ++ V) ++ V) →
      x < image x ((U ++ V) ++ V))
    (hd : ∀ x, m ≤ x → follows x (((U ++ V) ++ V) ++ V) →
      image x (((U ++ V) ++ V) ++ V) < x) :
    2 * a < b ∧ b < 3 * a ∧
      RankedReturn a (b - 2 * a) y ((U ++ V) ++ V) V
```

## 15. `J-cyclemin-walk-ostrowski-arithmetic` &mdash; covers 0.12

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.45; different result 0.3.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Certified quotient arithmetic behind the Denjoy–Koksma block envelope (Paper A Theorem 5.7) and the window digit caps (Theorem 5.8). Lean proves: the big-integer sandwich 3^10781274 < 2^17087915 and 2^16785921 < 3^10590737 (theta_sandwich_upper/lower, norm_num, kernel-checked); the real bounds 6195184/16785921 < log(3/2)/log 3 < 6306641/17087915 (lower_lt_walkTheta, walkTheta_lt_upper, via Real.log monotonicity); both rational endpoints open with the continued-fraction quotients [2,1,2,2,3,1,5,2,23,2,2,1] and continue past them (cf_lower_prefix, cf_upper_prefix, cf_lower_continues, cf_upper_continues); and the standard convergent recurrence on those quotients yields the block-denominator list 1,2,3,8,19,65,84,485,1054,24727,50508,125743,176251 (theta_convergent_denominators); and the greed  *(truncated; read the ledger row)*

**Declarations.** `theta_sandwich_upper` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:64`

> Upper side of the sandwich: `3^10781274 < 2^17087915`, hence `log 2 / log 3 > 10781274 / 17087915`. Proved by `norm_num`, so the comparison is checked by the kernel rather than by the compiled runtime: these two inequalities carry the whole Ostrowski certification, and `Nat` literal arithmetic is GMP-backed in the kernel, so the five-million-digit comparison costs well under a second. Only the exponent threshold is raised, and only for this declaration: it gates whether the power is evaluated at all, whereas `maxRecDepth` is not consulted on this route.

```lean
theorem theta_sandwich_upper : (3 : ℕ) ^ 10781274 < 2 ^ 17087915
```

**And.** `lower_lt_walkTheta` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:78`

> Real form of the lower sandwich: `6195184/16785921 < θ`.

```lean
theorem lower_lt_walkTheta : (6195184 : ℝ) / 16785921 < walkTheta
```

**And.** `walkTheta_lt_upper` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:90`

> Real form of the upper sandwich: `θ < 6306641/17087915`.

```lean
theorem walkTheta_lt_upper : walkTheta < (6306641 : ℝ) / 17087915
```

**And.** `cf_lower_prefix` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:114`

> The lower endpoint opens with the certified quotients.

```lean
theorem cf_lower_prefix :
    (cfQuotients 64 16785921 6195184).take 12 = thetaQuotients
```

**And.** `cf_upper_prefix` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:119`

> The upper endpoint opens with the certified quotients.

```lean
theorem cf_upper_prefix :
    (cfQuotients 64 17087915 6306641).take 12 = thetaQuotients
```

**And.** `cf_lower_continues` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:124`

> The lower endpoint's expansion continues past the shared prefix.

```lean
theorem cf_lower_continues :
    12 < (cfQuotients 64 16785921 6195184).length
```

**And.** `cf_upper_continues` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:129`

> The upper endpoint's expansion continues past the shared prefix.

```lean
theorem cf_upper_continues :
    12 < (cfQuotients 64 17087915 6306641).length
```

**And.** `theta_convergent_denominators` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:146`

> The certified quotients produce exactly the block-denominator list used by Paper A Theorem 5.7 and the window digit caps of Theorem 5.8.

```lean
theorem theta_convergent_denominators :
    convergentDenoms thetaQuotients =
      [1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508, 125743, 176251]
```

**And.** `window_digit_max` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:202`

> The sharp constant `37` is attained, at `L = 275632`, kernel-checked at its witness. It is no longer certified as an upper bound over the window: the scan that did so, `window_digit_scan`, was the Juggler layer's last `native_decide` and was retired on 14 September 2026. The pointwise bound is now `window_digit_cap` in `OstrowskiNumeration`, at the structural cap `47`. Kernel reduction of the scan as it stood was priced again before retiring it and is still out of range: `decide +kernel` takes 6.0 s for a thousand lengths and 33.2 s for four thousand, net of imports, so the full 251486 extrapolates to over half an hour and superlinearly.

```lean
theorem window_digit_max : greedyDigitSum 275632 = 37
```

**And.** `theta_convergent_numerators` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:227`

> The certified quotients produce the numerator list matching `theta_convergent_denominators`.

```lean
theorem theta_convergent_numerators :
    convergentNums thetaQuotients =
      [0, 1, 1, 3, 7, 24, 31, 179, 389, 9126, 18641, 46408, 65049]
```

**And.** `thetaConvergents_eq_zip` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:240`

> The pair list is exactly the zipped numerator/denominator recurrences.

```lean
theorem thetaConvergents_eq_zip :
    thetaConvergents =
      (convergentNums thetaQuotients).zip
        (convergentDenoms thetaQuotients)
```

**And.** `theta_convergents_unimodular` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:248`

> Unimodularity of consecutive certified pairs: `p_{j+1} q_j − p_j q_{j+1} = (−1)^j`.

```lean
theorem theta_convergents_unimodular :
    ∀ i < 12,
      ((thetaConvergents[i + 1]!).1 * (thetaConvergents[i]!).2 : ℤ) -
        (thetaConvergents[i]!).1 * (thetaConvergents[i + 1]!).2 =
          (-1) ^ i
```

**And.** `theta_convergents_coprime` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:256`

> Every certified pair is coprime.

```lean
theorem theta_convergents_coprime :
    ∀ pq ∈ thetaConvergents, Nat.Coprime pq.1 pq.2
```

**And.** `theta_convergent_quality` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:263`

> **Convergent quality** (the Denjoy–Koksma hypothesis for the certified blocks): every certified convergent approximates `θ` to within `1/q²`, certified against the sandwich bounds.

```lean
theorem theta_convergent_quality :
    ∀ pq ∈ thetaConvergents,
      |walkTheta - (pq.1 : ℝ) / pq.2| < 1 / (pq.2 : ℝ) ^ 2
```

**And.** `residue_mul_bijective` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:313`

> Multiplication by a coprime residue permutes `ZMod q` — the block-permutation fact behind Denjoy–Koksma: the `q` rotation steps of one certified block visit the `q` grid cells bijectively.

```lean
theorem residue_mul_bijective (q p : ℕ) (h : Nat.Coprime p q) :
    Function.Bijective (fun i : ZMod q => (p : ZMod q) * i)
```

**And.** `theta_block_permutations` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:318`

> Instance for every certified block.

```lean
theorem theta_block_permutations :
    ∀ pq ∈ thetaConvergents,
      Function.Bijective
        (fun i : ZMod pq.2 => ((pq.1 : ℕ) : ZMod pq.2) * i)
```

**And.** `theta_sandwich_lower` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:70`

> Lower side of the sandwich: `2^16785921 < 3^10590737`, hence `log 2 / log 3 < 10590737 / 16785921`. Kernel-checked, as above.

```lean
theorem theta_sandwich_lower : (2 : ℕ) ^ 16785921 < 3 ^ 10590737
```

**And.** `greedy_reconstruct_all` &mdash; kernel-checked, `Problems/Juggler/OstrowskiSandwich.lean:190`

> **Reconstruction is structural, and universal.** The fold peels `L / q` and keeps `L % q` at each of the thirteen levels, so `Σ bⱼ qⱼ` telescopes back to `L` by the division algorithm — for every `L`, with no window hypothesis. This half of the old scan never needed one.

```lean
theorem greedy_reconstruct_all (L : ℕ) : greedyReconstruct L = L
```

## 16. `J-cycle-later-return-height` &mdash; covers 0.13

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.47; different result 0.25.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Theorem3.40(ii): Every actual Juggler cycle with minimum m>=2^128 and maximum M<m^3 satisfies M<m^3-(1/2)m^theta, theta=381/128-3^41/2^65>127/64, also M<m^3-(1/2)m^(127/64) and m^127<[2(m^3-M)]^64. The forced next batch has r=3s+u,0<u<s. The unconditional 65-letter W=D^3C loss is below6/5 and its genuine third transfer forces d0>=8 and d0>(2/5)m^(13/128+1-3^41/2^65). The full actual placement, guards and cell transport are kernel checked; ordinary periodic-orbit and CycleMin wrappers are included. This theorem retains its much larger cutoff and does not exclude all cubic or taller cycles or increase the period/descent floor.

**Declarations.** `lr_cycle_height` &mdash; kernel-checked, `Problems/Juggler/ReturnTransferHeight.lean:139`

> The unconditional actual-cycle LR strip with exact and clean exponents.

```lean
theorem lr_cycle_height {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^128 ≤ m) (hM : M<m^3) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(381/128-(3:ℝ)^41/2^65) ∧
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(127/64 : ℝ) ∧
      m^127 < (2*(m^3-M))^64
```

**And.** `lr_cycle_gap` &mdash; kernel-checked, `Problems/Juggler/ReturnTransferHeight.lean:121`

> Every actual cubic cycle on the LR domain supplies the third gap bound.

```lean
theorem lr_cycle_gap {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^128 ≤ m) (hM : M<m^3) :
    8 ≤ ReturnCells.ooe m-ReturnCells.oe M.sqrt ∧
    (2/5 : ℝ)*(m : ℝ)^(13/128+1-(3:ℝ)^41/2^65) <
      (ReturnCells.ooe m-ReturnCells.oe M.sqrt : ℕ)
```

**And.** `periodicOrbit_lr_height` &mdash; kernel-checked, `Problems/Juggler/ReturnTransferHeight.lean:157`

> Ordinary finite-period orbit hypotheses suffice for both LR exponents.

```lean
theorem periodicOrbit_lr_height {m M k : ℕ} (hk : 0<k)
    (hp : floorPower^[k] m=m)
    (hbound : ∀ j<k,m≤floorPower^[j] m ∧ floorPower^[j] m≤M)
    (hmax : ∃ j<k,floorPower^[j] m=M) (hm : 2^128≤m) (hM : M<m^3) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(381/128-(3:ℝ)^41/2^65) ∧
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(127/64 : ℝ) ∧
      m^127 < (2*(m^3-M))^64
```

## 17. `J-fate-one-sided-conjecture` &mdash; covers 0.13

*Reads as: the claim asserts more than the declarations state (0.68).*

*Claim broader 0.68; declaration narrower 0.6; different result 0.27.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Theorem 9.1's consequence, the conjecture from the one-sided hypothesis, in the pattern of Corollary 8.4. OneSidedBound N_0 C q A y is H_q(C, A) at the scale y: every L(y)-bad cylinder of depth 1 <= t < ceil(C L(y)) sends at most q #[w] + y (log y)^{-A} of its members to an odd next letter; oneSidedExponent C q = C D(p_C || q) / log 2 is the Chernoff exponent of Proposition 9.3. Absorption (oddFailures_le_of_one_sided): under H_q(C, A) at all large scales, with C >= 5, 0 < q < p_C, A > C (1 + log_2 x) + 1 + e for the re-centring tilt x = p_C (1-q)/(q (1-p_C)), and e < C D(p_C || q) / log 2, the odd failures in (y, 2y] number at most y (log y)^{-e} for all large y; on Gibbs' inequality D(p || q) >= 0 (klDiv_nonneg), exp(-d D) <= Lambda^{-C D / log 2} for d >= C log_2 Lambda (exp_le_  *(truncated; read the ledger row)*

**Declarations.** `one_sided_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:356`

> **Theorem 9.1's corollary with nothing else assumed.** If `H_q(C, A)` holds at all large scales above a certified floor, with `C ≥ 5`, `0 < q < p_C`, `A > C(1 + log₂ x) + 1 + e` and `27/40 < e < e_{C,q}`, then every positive integer reaches `1`; the contagion side is the unconditional Theorem 5.3 at exponent `13/40`.

```lean
theorem one_sided_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A) (he : e < oneSidedExponent C q)
    (he7 : 27 / 40 < e) (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBound N₀ C q A y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `OneSidedBound` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:53`

> The one-sided hypothesis `H_q(C, A)` at the scale `y`: every `L(y)`-bad cylinder of depth `1 ≤ t < d(y) = ⌈C L(y)⌉` sends at most the share `q` of its members, plus `y (log y)^{-A}`, to an odd next letter.

```lean
def OneSidedBound (N₀ : ℕ) (C q A : ℝ) (y : ℕ) : Prop
```

**And.** `OneSidedExact` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:57`

> The paper's remark after Theorem 9.1: the share bound with no error term.

```lean
def OneSidedExact (N₀ : ℕ) (C q : ℝ) (y : ℕ) : Prop
```

**And.** `klDiv_nonneg` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:75`

> Gibbs' inequality: `D(p ‖ q) ≥ 0` for `0 < p, q < 1`.

```lean
theorem klDiv_nonneg {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ klDiv p q
```

**And.** `exp_le_rpow_scale` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:93`

> `e^{-dD} ≤ Λ^{-CD/log 2}` once `d ≥ C log₂ Λ` and `D ≥ 0`.

```lean
theorem exp_le_rpow_scale {Λ C D d : ℝ} (hΛ : 0 < Λ) (hD : 0 ≤ D)
    (hd : C * Real.logb 2 Λ ≤ d) :
    Real.exp (-(d * D)) ≤ Λ ^ (-(C * D / Real.log 2))
```

**And.** `pow_le_rpow_scale` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:107`

> `(2x)^{d-1} ≤ Λ^{C(1 + log₂ x)}` once `d - 1 ≤ C log₂ Λ`, for `x ≥ 1` and `Λ ≥ 1`.

```lean
theorem pow_le_rpow_scale {Λ C x : ℝ} (hΛ : 1 ≤ Λ) (hx : 1 ≤ x) (hC : 0 ≤ C) {d : ℕ}
    (hd : (d : ℝ) - 1 ≤ C * Real.logb 2 Λ) :
    (2 * x) ^ (d - 1) ≤ Λ ^ (C * (1 + Real.logb 2 x))
```

**And.** `oddFailures_le_of_one_sided` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:132`

> **The absorption.** Under `H_q(C, A)` at all large scales, with `q < p_C`, `A > C(1 + log₂ x) + 1 + e` for the re-centring tilt `x`, and `e < e_{C,q}`, the odd failures in `(y, 2y]` number at most `y (log y)^{-e}` for all large `y`.

```lean
theorem oddFailures_le_of_one_sided {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A) (he : e < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBound N₀ C q A y) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)
```

**And.** `implies_conjecture_of_contagion` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:339`

> **Theorem 9.1's corollary, with the contagion bound as a hypothesis.** If `H_q(C, A)` holds at all large scales with `C ≥ 5`, `0 < q < p_C`, `A > C(1 + log₂ x) + 1 + e` and `e < e_{C,q}`, and the contagion bound of Theorem 5.3 holds for the failure set with an exponent `λ` satisfying `1 - λ < e`, then every positive integer reaches `1`.

```lean
theorem implies_conjecture_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A) (he : e < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBound N₀ C q A y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `exact_share_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:369`

> **The paper's remark after Theorem 9.1, with nothing else assumed.** If no `L(y)`-bad cylinder of depth below `⌈C L(y)⌉` sends more than the share `q` of its members to an odd next letter, at all large scales above a certified floor, with `C ≥ 5`, `0 < q < p_C` and `e_{C,q} > 27/40`, then every positive integer reaches `1`.

```lean
theorem exact_share_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (heOS : 27 / 40 < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedExact N₀ C q y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 18. `BTC-op-fragment-nd-nf` &mdash; covers 0.14

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.23; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** the operator-fragment tree TRS {D, I_a, S, N} including N(D(x))→D(N(x)) is terminating and locally confluent; every term has a unique syntactic normal form

**Declarations.** `unique_normal_form` &mdash; kernel-checked, `BTCalculus/OpFragNewman.lean:381`

> Unique syntactic normal form of an operator-fragment term.

```lean
theorem unique_normal_form (t : OpFrag) :
    ∃ n, Normal n ∧ ReflTransGen Step t n ∧
      ∀ n', Normal n' → ReflTransGen Step t n' → n' = n
```

**And.** `locally_confluent` &mdash; kernel-checked, `BTCalculus/OpFragNewman.lean:198`

> Local confluence by induction on the peak term.

```lean
theorem locally_confluent {a b c : OpFrag} (hb : Step a b) (hc : Step a c) :
    Join (ReflTransGen Step) b c
```

## 19. `J-cycle-finance-inequality` &mdash; covers 0.14

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.35; different result 0.26.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** On a Juggler CycleMin start n ≥ 2 with word w of length L and oddCount o, the dyadic-cell logarithm bound log z ≤ 2 log y + 2/y unrolls to n · log n · (3^o − 2^L) ≤ L · 3^o (Paper A Theorem 4.4; Lean cycleMin_finance). Every cycle state is at least 12 and the rotated minimum is odd, so the minimum is at least 13 and 13 log 13 > 65/2, hence (65/2)(3^o − 2^L) ≤ L · 3^o for every CycleItinerary (cycle_finance_min_thirteen). This is the whole-cycle financing of the formal expansion 2^L < 3^o by relative floor defects. It is not a halt theorem, not an exclusion of every length, and not the computational 6/5 table used for L ≤ 10^5.

**Declarations.** `cycleMin_finance` &mdash; kernel-checked, `Problems/Juggler/CycleFinance.lean:210`

> **Cycle finance inequality.** For any cycle taken at its minimum: `n log n (3^o - 2^L) ≤ L 3^o`.

```lean
theorem cycleMin_finance {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    (n : ℝ) * Real.log n *
        ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w
```

**And.** `log_le_two_log_add` &mdash; kernel-checked, `Problems/Juggler/CycleFinance.lean:42`

> The dyadic one-step-preimage logarithm bound: if `z < (y+1)^2` then `log z ≤ 2 log y + 2/y`. The only analytic input of the finance inequality (`log(1+u) ≤ u`).

```lean
theorem log_le_two_log_add {z y : ℕ} (hz : 1 ≤ z) (hy : 1 ≤ y)
    (hcell : z < (y + 1) ^ 2) :
    Real.log z ≤ 2 * Real.log y + 2 / y
```

**And.** `cycleMin_log_envelope` &mdash; kernel-checked, `Problems/Juggler/CycleFinance.lean:97`

> The unrolled financing envelope along a `CycleMin` prefix: `3^{o_k} log n ≤ 2^k log x_k + k 3^{o_k} / n`. Division-free induction; each step spends one dyadic one-step-preimage logarithm bound and one prefix non-contraction fact.

```lean
theorem cycleMin_log_envelope {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∀ k, k ≤ w.length →
      (3 : ℝ) ^ oddCount (w.take k) * Real.log n ≤
        (2 : ℝ) ^ k * Real.log (floorPower^[k] n) +
          (k : ℝ) * (3 : ℝ) ^ oddCount (w.take k) / n
```

## 20. `J-cycle-subtractive-return-step` &mdash; covers 0.14

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.54; different result 0.28.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Appendix E.2, formal core. For rankStep(a,b,i)=i+b when i<a and i-a otherwise, a>b gives the first return on [0,a) as rankStep(a-b,b), in one or two iterations with every earlier positive iterate outside. For b>a the first return on [0,b) is rankStep(a,b-a); equal counts give a two-step identity. Weighted word lengths and O/E statistics are preserved by A,AB or AB,B substitution. Kernel-verified return iterates and first-visit properties; full accelerated towers and their global partition remain written.

**Declarations.** `left_subtractive_first_return` &mdash; kernel-checked, `Problems/Juggler/ReturnInduction.lean:15`

> Exact positive first return to the prefix of length `a`, when `b<a`. The words on the two new branches are respectively `A` and `AB`.

```lean
theorem left_subtractive_first_return {a b i : ℕ}
    (_hb : 0 < b) (hba : b < a) (hi : i < a) :
    let k
```

**And.** `rankStep` &mdash; kernel-checked, `Problems/Juggler/ReturnInduction.lean:6`

> The two-interval presentation of rotation by `b` on `a+b` ranks.

```lean
def rankStep (a b i : ℕ) : ℕ
```

**And.** `right_subtractive_first_return` &mdash; kernel-checked, `Problems/Juggler/ReturnInduction.lean:42`

> Exact positive first return to the prefix of length `b`, when `a<b`. The words on the two new branches are respectively `AB` and `B`.

```lean
theorem right_subtractive_first_return {a b i : ℕ}
    (ha : 0 < a) (hab : a < b) (hi : i < b) :
    let k
```

**And.** `equal_first_return` &mdash; kernel-checked, `Problems/Juggler/ReturnInduction.lean:67`

> At equality the first return is `AB` and the induced rank map is fixed.

```lean
theorem equal_first_return {a i : ℕ} (hi : i < a) :
    (rankStep a a)^[2] i = i ∧ a ≤ rankStep a a i
```

**And.** `left_word_statistics` &mdash; kernel-checked, `Problems/Juggler/ReturnInduction.lean:85`

> The first substitution preserves total expanded length and both letter counts.

```lean
theorem left_word_statistics {a b : ℕ} (hba : b ≤ a) (A B : List Branch) :
    (a - b) * A.length + b * (A ++ B).length = a * A.length + b * B.length ∧
      (a - b) * oddCount A + b * oddCount (A ++ B) =
        a * oddCount A + b * oddCount B ∧
      (a - b) * evenCount A + b * evenCount (A ++ B) =
        a * evenCount A + b * evenCount B
```

**And.** `right_word_statistics` &mdash; kernel-checked, `Problems/Juggler/ReturnInduction.lean:95`

> The second substitution preserves the same three expanded statistics.

```lean
theorem right_word_statistics {a b : ℕ} (hab : a ≤ b) (A B : List Branch) :
    a * (A ++ B).length + (b - a) * B.length = a * A.length + b * B.length ∧
      a * oddCount (A ++ B) + (b - a) * oddCount B =
        a * oddCount A + b * oddCount B ∧
      a * evenCount (A ++ B) + (b - a) * evenCount B =
        a * evenCount A + b * evenCount B
```

## 21. `J-cycle-terminal-mixed-gap` &mdash; covers 0.14

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.49; different result 0.53.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Every actual positive periodic orbit with minimum m>=3, attained maximum M<m^3 and all states in [m,M] supplies a primitive terminal two-base section {m,v}. The supplied period need not be least. The original adjacent pair follows induced words U,V with U(m)=v and V(v)=m, and guarded factors UV=P OE Q, VU=P EO Q. Their common prefix reaches the globally adjacent largest odd/smallest even pair (h,s), with O(h)=M and E(s)=m. The common suffix returns (floor(sqrt M),O(m)) to (m,v), and 0<O(m)-floor(sqrt M)<s-h. The periodic-set interface explicitly requires connectedness; the ordinary-orbit interface derives it. Primitive termination, original-set adjacency, exact cut identification and every guard are kernel checked. No contraction of the complete prefix/mixed/suffix passage or no-cycle conc  *(truncated; read the ledger row)*

**Declarations.** `mixed_gap` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:167`

```lean
theorem mixed_gap {m h s : ℕ}
    (hh1 : 1 ≤ h) (hh : h < m^2) (hs : m^2 < s) :
    ((m^3).sqrt : ℤ) - ReturnCells.oe h < (s : ℤ) - h
```

**And.** `periodicExtrema_terminal_cut` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:310`

> Connected actual cubic periodic sets supply the entire primitive terminal construction and its global odd/even cut identification.

```lean
theorem periodicExtrema_terminal_cut {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    (hconnected : ∀ x ∈ C, ∀ z ∈ C, ∃ k, floorPower^[k] x = z) :
    Nonempty (TerminalCut C m M)
```

**And.** `periodicOrbit_terminal_cut` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:370`

> An ordinary positive actual period suffices; the given period need not be least, since the complete orbit set is reduced to its primitive permutation.

```lean
theorem periodicOrbit_terminal_cut {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) (hm : 3 ≤ m) (hM : M < m ^ 3) :
    Nonempty (TerminalCut (Set.range (fun j : ℕ => floorPower^[j] m)) m M)
```

**And.** `TerminalOrbitCut` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:323`

> A terminal cut tied to the same complete sorted orbit witness. Its word totals count distinct primitive states, not the supplied period.

```lean
structure TerminalOrbitCut {m M k : ℕ} (S : ReturnSeams.PeriodicOrbitModel m M k)
    extends TerminalCut (Set.range (fun j : ℕ => floorPower^[j] m)) m M where
  length_total : lowerWord.length + upperWord.length = S.length
  odd_total : oddCount lowerWord + oddCount upperWord =
    (Finset.univ.filter (fun i => S.state i % 2 = 1)).card
  even_total : evenCount lowerWord + evenCount upperWord =
    (Finset.univ.filter (fun i => S.state i % 2 = 0)).card
  least_period : S.length = Function.minimalPeriod floorPower m

end Problems.Juggler.ReturnTerminal

namespace Problems.Juggler.ReturnSeams.PeriodicOrbitModel
```

**And.** `terminal_cut_from_section` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:224`

> A primitive guarded section produces the complete cut while retaining all three expanded word totals.

```lean
theorem terminal_cut_from_section {C : Set ℕ} {m M a b : ℕ} {y : ℕ → ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    (ha : 0 < a) (hb : 0 < b) (h0 : y 0 = m)
    (hr : ReturnSeams.RankedReturn a b y [.odd, .odd, .even] [.odd, .even])
    (hsection : ReturnSeams.PrefixSection C (a + b) y) (hcop : Nat.Coprime a b) :
    ∃ T : TerminalCut C m M,
      T.lowerWord.length + T.upperWord.length = 3 * a + 2 * b ∧
      oddCount T.lowerWord + oddCount T.upperWord = 2 * a + b ∧
      evenCount T.lowerWord + evenCount T.upperWord = a + b
```

**And.** `periodicOrbit_terminal_totals` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:360`

> Ordinary period data constructs a shared model and its primitive terminal cut.

```lean
theorem periodicOrbit_terminal_totals {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) (hm : 3 ≤ m) (hM : M < m ^ 3) :
    ∃ S : ReturnSeams.PeriodicOrbitModel m M k, Nonempty (TerminalOrbitCut S)
```

**And.** `cycleMin_terminal_totals` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:379`

> Closed minimum itineraries retain primitive totals even when the word repeats.

```lean
theorem cycleMin_terminal_totals {m M : ℕ} {w : List Branch} (h : CycleMin m w)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) (hm : 3 ≤ m) (hM : M < m ^ 3) :
    ∃ S : ReturnSeams.PeriodicOrbitModel m M w.length, Nonempty (TerminalOrbitCut S)
```

**And.** `TerminalCut` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:174`

> The complete terminal geometry, with every path interpreted on the original actual periodic set. This record contains no contraction premise for the prefix.

```lean
structure TerminalCut (C : Set ℕ) (m M : ℕ) where
  next : ℕ
  lowerWord : List Branch
  upperWord : List Branch
  commonPrefix : List Branch
  suffix : List Branch
  highOdd : ℕ
  lowEven : ℕ
  source_adjacent : AdjacentIn C m next
  induced : ReturnWordFactorization.InducedPair lowerWord upperWord
  factorization : ReturnWordFactorization.Factorization lowerWord upperWord commonPrefix suffix
  lower_guard : follows m lowerWord
```

**And.** `AdjacentIn.image` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:60`

> Every actual common prefix preserves the original adjacency.

```lean
theorem AdjacentIn.image {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    {x y : ℕ} {P : List Branch} (h : AdjacentIn C x y)
    (hx : follows x P) (hy : follows y P) :
    AdjacentIn C (image x P) (image y P)
```

**And.** `AdjacentIn.cut_extrema` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:73`

> A globally adjacent odd/even pair is the absolute cut and maps to the extrema.

```lean
theorem AdjacentIn.cut_extrema {C : Set ℕ} {m M h s : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    (hadj : AdjacentIn C h s) (hho : h % 2 = 1) (hse : s % 2 = 0) :
    h < m ^ 2 ∧ m ^ 2 < s ∧
      (∀ x ∈ C, x % 2 = 1 → x ≤ h) ∧
      (∀ x ∈ C, x % 2 = 0 → s ≤ x) ∧
      floorPower h = M ∧ floorPower s = m
```

**And.** `terminal_cut` &mdash; kernel-checked, `Problems/Juggler/ReturnTerminal.lean:337`

> The fixed sorted orbit witness supplies terminal geometry and primitive totals.

```lean
theorem terminal_cut {m M k : ℕ} (S : PeriodicOrbitModel m M k)
    (hm : 3 ≤ m) (hM : M < m ^ 3) :
    Nonempty (ReturnTerminal.TerminalOrbitCut S)
```

## 22. `J-cycle-unit-perturbation` &mdash; covers 0.14

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.56; different result 0.19.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every odd integer b>=3, let D_b consist of odd integers in [b,b^2] and even integers in [b^2+1,b^3-1], and let P_b(z) be its largest element <=z for b<=z<=b^3. Define R_b(x)=P_b(x^(3/2)) on odd x and P_b(sqrt x) on even x. This finite map has no fixed point and has a nontrivial cycle; every edge has R_b(x) in {J(x),J(x)-1}. Every primitive cycle uses its actual source parity, has M<m^3, rank rotation, coprime counts and the ceiling mechanical word. Thus one-sided power-rounding error <2 admits such cycles at every scale. Inclusion of odd b^2 is essential at the projection seam. R_b is a different map; it is NOT proved that every R_b cycle has an altered edge, and no actual Juggler no-cycle statement follows. Consolidated in Paper A Section 3.10 and formalized in the seven Cubic modules  *(truncated; read the ledger row)*

**Declarations.** `cubicRounding_exists_primitive` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:301`

> A least-period formulation also certifies distinctness before return.

```lean
theorem cubicRounding_exists_primitive {b : ℕ} (hb : 3 ≤ b) (ho : b % 2 = 1) :
    ∃ x L : ℕ, cubicParityDomain b x ∧ 2 ≤ L ∧
      (cubicRounding b)^[L] x = x ∧
      (∀ i < L, ∀ j < L,
        (cubicRounding b)^[i] x = (cubicRounding b)^[j] x → i = j) ∧
      ∀ i j : ℕ, (cubicRounding b)^[j] x < ((cubicRounding b)^[i] x) ^ 3
```

**And.** `cubicRounding_eq_or_pred` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:99`

```lean
theorem cubicRounding_eq_or_pred (b x : ℕ) :
    cubicRounding b x = floorPower x ∨ cubicRounding b x = floorPower x - 1
```

**And.** `cubicRounding_real_loss` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:357`

```lean
theorem cubicRounding_real_loss (b x : ℕ) :
    0 ≤ cubicBranchValue x - cubicRounding b x ∧
    cubicBranchValue x - cubicRounding b x < 2
```

**And.** `cubicRounding_finite_invariant_rotation` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:205`

> Any finite invariant subset on which the altered map is injective has this sorted form.

```lean
theorem cubicRounding_finite_invariant_rotation {b : ℕ} (hb : 3 ≤ b)
    (hbodd : b % 2 = 1) (s : Finset ℕ)
    (hdom : ∀ x ∈ s, cubicParityDomain b x)
    (hclosed : ∀ x ∈ s, cubicRounding b x ∈ s)
    (hinj : Set.InjOn (cubicRounding b) s) :
    ∃ (p : Equiv.Perm (Fin s.card)) (o : ℕ), o ≤ s.card ∧
      (∀ i, s.orderEmbOfFin rfl (p i) = cubicRounding b (s.orderEmbOfFin rfl i)) ∧
      (∀ i, s.orderEmbOfFin rfl i % 2 = 1 ↔ i.val < o) ∧
      (Finset.univ.filter (fun i => s.orderEmbOfFin rfl i % 2 = 1)).card = o ∧
      (∀ i, (p i).val = (i.val + (s.card - o)) % s.card)
```

**And.** `cubicParityDomain` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:16`

> Odd states through the square seam, followed by even states below the cube.

```lean
def cubicParityDomain (b x : ℕ) : Prop
```

**And.** `cubicParityProject` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:21`

> Downward projection on the prescribed source-parity domain.

```lean
def cubicParityProject (b n : ℕ) : ℕ
```

**And.** `cubicRounding` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:25`

> The parity-preserving altered successor.

```lean
def cubicRounding (b x : ℕ) : ℕ
```

**And.** `cubicRounding_mem` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:94`

```lean
theorem cubicRounding_mem {b x : ℕ} (hb : 3 ≤ b) (ho : b % 2 = 1)
    (hx : cubicParityDomain b x) : cubicParityDomain b (cubicRounding b x)
```

**And.** `cubicRounding_no_fixed` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:239`

```lean
theorem cubicRounding_no_fixed {b x : ℕ} (hb : 3 ≤ b)
    (hx : cubicParityDomain b x) : cubicRounding b x ≠ x
```

**And.** `cubicRounding_iterate_mem` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:245`

```lean
theorem cubicRounding_iterate_mem {b x : ℕ} (hb : 3 ≤ b) (ho : b % 2 = 1)
    (hx : cubicParityDomain b x) (k : ℕ) :
    cubicParityDomain b ((cubicRounding b)^[k] x)
```

## 23. `J-cycle-ooe-exact-remainder-repair` &mdash; covers 0.15

*Reads as: the claim asserts more than the declarations state (0.82).*

*Claim broader 0.82; declaration narrower 0.5; different result 0.38.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Proposition E.5 and ER1. For an exact first root u=isqrt(x^3)>=3, retained remainder R=x^3-u^2, and validated OE suffix endpoint z, the correction error C-Delta=eta^2(t+2u)/(4z^2) is in [0,5/6). The signed corrected floor q is d or d-1, where d=floor((u^3-z^4)/(2z^2)). corrected_quotient_integer proves q=(isqrt(K^2*x^3)-2z^4) floor-divided by 4z^2, K=2x^3-3R. endpoint_validation certifies z via z^8<=(x^3-R)^3<(z+1)^8; record_initializes checks an independently supplied square/remainder witness. The executable recoverPeak evaluates this integer quotient and the four candidate fourth-power cells; recoverPeak_eq proves exact recovery of v=isqrt(u^3). For odd initial x, both hidden OOE source guards hold iff R is even and recoverPeak is even. Initial record and endpoint validity are ex  *(truncated; read the ledger row)*

**Declarations.** `recoverPeak_guard_iff` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:473`

```lean
theorem recoverPeak_guard_iff {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) (hx : x % 2 = 1) :
    (u % 2 = 1 ∧ (u ^ 3).sqrt % 2 = 0) ↔
      (R % 2 = 0 ∧ recoverPeak x z R % 2 = 0)
```

**And.** `correction_identity` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:139`

```lean
theorem correction_identity (t u z : ℝ) (hz : z ≠ 0) :
    3 * t * (t ^ 2 - u ^ 2) / (4 * z ^ 2) -
        (t ^ 3 - u ^ 3) / (2 * z ^ 2) =
      (t - u) ^ 2 * (t + 2 * u) / (4 * z ^ 2)
```

**And.** `correction_error_bound` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:146`

```lean
theorem correction_error_bound {t u z : ℝ} (hu : 3 ≤ u)
    (htu : u ≤ t) (hut : t < u + 1) (huz : u ≤ z ^ 2) :
    0 ≤ (t - u) ^ 2 * (t + 2 * u) / (4 * z ^ 2) ∧
      (t - u) ^ 2 * (t + 2 * u) / (4 * z ^ 2) < 5 / 6
```

**And.** `exact_remainder_correction` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:161`

```lean
theorem exact_remainder_correction {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    let t
```

**And.** `exact_quotient_gap` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:210`

```lean
theorem exact_quotient_gap {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    (((u ^ 3 - z ^ 4) / (2 * z ^ 2) : ℕ) : ℤ) = correctedQuotient x z R ∨
      (((u ^ 3 - z ^ 4) / (2 * z ^ 2) : ℕ) : ℤ) =
        correctedQuotient x z R + 1
```

**And.** `corrected_baseline_bounds` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:242`

```lean
theorem corrected_baseline_bounds {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    (u ^ 3).sqrt ≤ correctedBaseline x z R ∧
      correctedBaseline x z R ≤ (u ^ 3).sqrt + 3
```

**And.** `corrected_baseline_correction` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:261`

```lean
theorem corrected_baseline_correction {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    ∃ κ : ℕ, κ ≤ 3 ∧ correctedBaseline x z R = (u ^ 3).sqrt + κ
```

**And.** `integerQuotient` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:388`

> Integer floor division, including a possibly negative numerator.

```lean
def integerQuotient (x z R : ℕ) : ℤ
```

**And.** `corrected_quotient_integer` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:392`

```lean
theorem corrected_quotient_integer {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    correctedQuotient x z R = integerQuotient x z R
```

**And.** `endpoint_validation` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:273`

```lean
theorem endpoint_validation {x u z R : ℕ} (hu : u = (x ^ 3).sqrt)
    (hR : R = x ^ 3 - u ^ 2) :
    ReturnCells.oe u = z ↔
      z ^ 8 ≤ (x ^ 3 - R) ^ 3 ∧ (x ^ 3 - R) ^ 3 < (z + 1) ^ 8
```

**And.** `record_initializes` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:379`

```lean
theorem record_initializes {x u R : ℕ}
    (he : x ^ 3 = u ^ 2 + R) (hR : R ^ 2 ≤ 4 * u ^ 2) :
    u = (x ^ 3).sqrt
```

**And.** `recoverPeak` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:457`

> A fully integer short-block recovery using the retained absolute remainder.

```lean
def recoverPeak (x z R : ℕ) : ℕ
```

**And.** `recoverPeak_eq` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:460`

```lean
theorem recoverPeak_eq {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) :
    recoverPeak x z R = (u ^ 3).sqrt
```

## 24. `J-fate-contagion-elementary` &mdash; covers 0.15

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.5; different result 0.23.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The production inequality of Paper C Section 5.1 without its exponential sums, and the unconditional theorem it yields. Of the three families of members of A on (sqrt x, x], the E-images of the members at scale t/2 (Lemma 3.1; Production.family_E) and the OE-fibers of the members at scale 3t/4 (Lemma 4.2 on good fibers, Lemma 4.3 for the bad; Production.family_OE, on the per-fiber bound (2/9)(1 - (25/2) m^{-1/3})/m) need no analysis. With the paper's sqrt x read as floor(e^{t/2}) (sqrt_floor_exp) they give, for t >= 40, g_A(t) >= (1 - 4e^{-t/4}) g_A(t/2) + (2/9 - (50/9)e^{-t/8}) g_A(3t/4) - eta_0(t) with eta_0(t) = 2e^{-t/2} + (4/9)e^{-3t/4} + 136 e^{-t/8}, every error explicit (production_two). Lemma 5.1 (recursion_lemma) on these two productions, with 2^{-13/40} + (2/9)(3/4)^{13/40} > 1   *(truncated; read the ledger row)*

**Declarations.** `logMass_contagion_elementary` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:630`

> **Elementary contagion, as a log-mass bound.** For every nonempty backward-closed `A` and `0 < λ ≤ 13/40` there are `K > 0` and `x₀` with `Σ_{n ∈ A, n ≤ x} 1/n ≥ K (log x)^λ` for all `x ≥ x₀`. This is Theorem 5.3 of the paper with `13/40` in place of `λ** ≈ 0.4926`, and with no hypothesis: the block-average family and the ladder, which need the exponential sums, are what lift the exponent.

```lean
theorem logMass_contagion_elementary {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 13 / 40) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → K * Real.log x ^ lam ≤ logMass A x
```

**And.** `sqrt_floor_exp` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:41`

> `⌊√⌊e^t⌋⌋ = ⌊e^{t/2}⌋`: the integer half-scale is what the paper's `√x` means.

```lean
theorem sqrt_floor_exp (t : ℝ) : Nat.sqrt ⌊Real.exp t⌋₊ = ⌊Real.exp (t / 2)⌋₊
```

**And.** `family_E` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:76`

> **Family 1.** For `s₁ = ⌊√y⌋` and `s₂ = ⌊√s₁⌋`, the `E`-blocks of the members of `A` in `(s₂, s₁ - 1]` lie in `(s₁, y]`, are disjoint, and carry log-mass at least `(1 - 2/s₂) Σ_{m ∈ A ∩ (s₂, s₁-1]} 1/m`.

```lean
theorem family_E {A : ℕ → Prop} (hA : BackwardClosed A) {y : ℕ} (hs₂ : 1 ≤ Nat.sqrt (Nat.sqrt y)) :
    (1 - 2 / (Nat.sqrt (Nat.sqrt y) : ℝ)) *
        ∑ m ∈ {m ∈ Ioc (Nat.sqrt (Nat.sqrt y)) (Nat.sqrt y - 1) | A m}, (1 : ℝ) / m
      ≤ ∑ n ∈ {n ∈ Ioc (Nat.sqrt y) y | A n ∧ n % 2 = 0}, (1 : ℝ) / n
```

**And.** `good_fiber_logMass_ge` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:129`

> A good fiber `Φ(m)`, `m ≥ 10⁶`, carries even-image log-mass at least `(2/9)(1 - (25/2) m^{-1/3})/m`: at least `H_m/3 - 2 ≥ (2/9)m^{1/3} - 7/3` even images (Lemmas 4.2 and 4.2's fiber bound), each above `1/(u⁴ + 2u)` for `u = m^{1/3}`.

```lean
theorem good_fiber_logMass_ge {m : ℕ} (hm : 10 ^ 6 ≤ m) (hg : Good m) :
    2 / 9 * (1 - 25 / 2 * eps m) / m
      ≤ ∑ n ∈ {n ∈ oeFiber m | (n ^ 3).sqrt % 2 = 0}, (1 : ℝ) / n
```

**And.** `family_OE` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:192`

> **Family 3.** For `U = ⌊√y''⌋ ≥ 10⁶` and any shell `(s, y]` that contains every fiber `Φ(m)` with `U < m ≤ y'' - 1`, the even-image parts of the good fibers of the members of `A` in `(U, y'' - 1]` are disjoint odd members of `A` in the shell, of total log-mass at least `(2/9)(1 - (25/2) U^{-1/3}) (Σ_{m ∈ A ∩ (U, y''-1]} 1/m - 306 U^{-1/3})`: Lemma 4.2 on the good fibers, Lemma 4.3 for the bad ones.

```lean
theorem family_OE {A : ℕ → Prop} (hA : BackwardClosed A) {y'' s y : ℕ}
    (hU : 10 ^ 6 ≤ Nat.sqrt y'')
    (hfib : ∀ m, Nat.sqrt y'' < m → m ≤ y'' - 1 → ∀ n ∈ oeFiber m, s < n ∧ n ≤ y) :
    2 / 9 * (1 - 25 / 2 * eps (Nat.sqrt y'')) *
        (∑ m ∈ {m ∈ Ioc (Nat.sqrt y'') (y'' - 1) | A m}, (1 : ℝ) / m
          - 306 * eps (Nat.sqrt y''))
      ≤ ∑ n ∈ {n ∈ Ioc s y | A n ∧ n % 2 = 1}, (1 : ℝ) / n
```

**And.** `production_two` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:328`

> **The production inequality with two productions.** For `t ≥ 40`, `(1 - 4e^{-t/4}) g_A(t/2) + (2/9 - (50/9)e^{-t/8}) g_A(3t/4) - errAdd t ≤ g_A(t)`: family 1 through Lemma 3.1, family 3 through Lemmas 4.2 and 4.3, with every error explicit and no hypothesis.

```lean
theorem production_two {A : ℕ → Prop} (hA : BackwardClosed A) {t : ℝ} (ht : 40 ≤ t) :
    (1 - errE t) * gA A (t / 2) + (2 / 9 - errOE t) * gA A (3 * t / 4) - errAdd t ≤ gA A t
```

**And.** `zeta2_pos` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:525`

> `ζ(13/40) = 2^{-13/40} + (2/9)(3/4)^{13/40} - 1 > 0`, by two rational bounds: `0.798 ≤ (1/2)^{13/40}` since `0.798^{40} ≤ 2^{-13}`, and `0.91 ≤ (3/4)^{13/40}` since `0.91^{40} ≤ (3/4)^{13}`; then `0.798 + (2/9)(0.91) = 1.000222 > 1`. `13/40 = 0.325` against the true root `0.3261209621…` of `2^{-λ} + (2/9)(3/4)^λ = 1`, so this certificate reaches `99.6%` of what the two-production inequality can give. The earlier certificate was `λ = 3/10`, which reached `92%`.

```lean
theorem zeta2_pos : 0 < ∑ i, coef2 i * rate2 i ^ ((13 : ℝ) / 40) - 1
```

**And.** `zeta2_antitone` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:537`

> `ζ` is antitone in `λ`: both rates lie below `1`.

```lean
theorem zeta2_antitone {lam lam' : ℝ} (h : lam ≤ lam') :
    ∑ i, coef2 i * rate2 i ^ lam' - 1 ≤ ∑ i, coef2 i * rate2 i ^ lam - 1
```

**And.** `contagion_elementary` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:577`

> **Elementary contagion.** For every nonempty backward-closed `A` and `0 < λ ≤ 13/40` there are `K > 0` and `t₁` with `g_A(t) ≥ K t^λ` for all `t ≥ t₁`. No hypothesis: the seed is Lemma 5.2, the recursion is Lemma 5.1 on the two productions `E` and `OE`, and the production inequality is `production_two`, whose inputs are Lemmas 3.1, 4.2 and 4.3.

```lean
theorem contagion_elementary {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ} (ha : 1 ≤ a)
    (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 13 / 40) :
    ∃ K : ℝ, 0 < K ∧ ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t, t₁ ≤ t → K * t ^ lam ≤ gA A t
```

**And.** `failures_logMass_ge` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:648`

> **Corollary 5.5(2) at exponent `13/40`, unconditional.** If some positive integer does not reach `1`, the failures have log-mass at least `K (log x)^{13/40}` up to `x` for all large `x`: the failure set is backward-closed (Lemma 2.1) and nonempty.

```lean
theorem failures_logMass_ge {a : ℕ} (ha : 1 ≤ a) (hfail : ¬ReachesOne a) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 13 / 40) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x
```

**And.** `conjecture_of_tao_rate` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:662`

> **Theorem 7.2 with its contagion hypothesis discharged.** If the odd failures in `(y, 2y]` number at most `y (log y)^{-e}` for all large `y`, for some `e > 27/40`, then every positive integer reaches `1`. The contagion bound at exponent `13/40` is `failures_logMass_ge`, so nothing is assumed beyond the rate; the paper's conditional form needs `e > 0.51` and the production inequality (5.2). The threshold is `1 - λ` for the `λ` the contagion bound reaches, so lifting that exponent to `13/40` lowered it from `7/10` to `27/40`.

```lean
theorem conjecture_of_tao_rate {e : ℝ} (he : 27 / 40 < e)
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `conjecture_of_cylinder_bound` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:671`

> **Corollary 8.4 with its contagion hypothesis discharged.** A cylinder bound `H(C, A)` at all large scales with `A > C + e(C)` and `e(C) > 27/40`, above a certified floor `N₀`, gives the conjecture; nothing else is assumed.

```lean
theorem conjecture_of_cylinder_bound {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C A : ℝ) (hC : 5 ≤ C)
    (hA : C + chernoffExponent C < A)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ C A y)
    (he : 27 / 40 < chernoffExponent C) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 25. `J-cubic-critical-localization-kernels` &mdash; covers 0.16

*Reads as: the claim asserts more than the declarations state (0.77).*

*Claim broader 0.77; declaration narrower 0.57; different result 0.28.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Conditional kernels: a positive integer gap below 2^(H+1) has binary valuation at most H. A finite rank path below 780239, with successors adding 287963 modulo 780239, supplied valuation caps 25 below 204313 and 19 below 83650, and supplied suffixHeight(d)=d+1+(d-1)*287963/780239 lower bounds (natural subtraction) has at most 21 vertices. Finite block lengths summing 780237 and bounded by 21 need at least 37155 blocks; supplied correction/support inequalities give T>=37157 and S>=18577. Generic disjoint-window hitting implies floor(n/w) event count, with an interval-filtered variant; the fixed R arc yields 14380. Explicit injective witnesses or disjoint responsible pairs transfer event count to deviation count. Real gap-cap certification, extraction of critical-free cycle blocks and actual  *(truncated; read the ledger row)*

**Declarations.** `valuation_le_of_lt_pow_succ` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:16`

> A strict power ceiling bounds the binary valuation of a positive gap.

```lean
theorem valuation_le_of_lt_pow_succ {l H : ℕ}
    (hl : 0 < l) (hbound : l < 2 ^ (H + 1)) :
    padicValNat 2 l ≤ H
```

**And.** `valuation_le_twenty_five` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:25`

> The first certified rank ceiling supplies a valuation bound of 25.

```lean
theorem valuation_le_twenty_five {l : ℕ}
    (hl : 0 < l) (hbound : l < 2 ^ 26) :
    padicValNat 2 l ≤ 25
```

**And.** `valuation_le_nineteen` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:31`

> The second certified rank ceiling supplies a valuation bound of 19.

```lean
theorem valuation_le_nineteen {l : ℕ}
    (hl : 0 < l) (hbound : l < 2 ^ 20) :
    padicValNat 2 l ≤ 19
```

**And.** `suffixHeight` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:37`

> The fixed-count lower valuation of the first gap in a suffix of `d` edges.

```lean
def suffixHeight (d : ℕ) : ℕ
```

**And.** `three_rank_low` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:41`

> Every three successive ranks meet the low interval at the fixed counts.

```lean
theorem three_rank_low {i : ℕ} (hi : i < 780239) :
    i < 287963 ∨ (i + 287963) % 780239 < 287963 ∨
      ((i + 287963) % 780239 + 287963) % 780239 < 287963
```

**And.** `highlow_two_step_tiny` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:47`

> The upper portion of the low interval reaches the tiny interval in two steps.

```lean
theorem highlow_two_step_tiny {i : ℕ} (ha : 204313 ≤ i) (he : i < 287963) :
    ((i + 287963) % 780239 + 287963) % 780239 = i - 204313 ∧
      i - 204313 < 83650
```

**And.** `block_length_le_twenty_one` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:53`

> A finite path with the two certified caps has at most twenty-one vertices.

```lean
theorem block_length_le_twenty_one (n : ℕ) (idx v : ℕ → ℕ)
    (hrank : ∀ t < n, idx t < 780239)
    (hnext : ∀ t, t + 1 < n → idx (t + 1) = (idx t + 287963) % 780239)
    (hsmall : ∀ t < n, idx t < 204313 → v t ≤ 25)
    (htiny : ∀ t < n, idx t < 83650 → v t ≤ 19)
    (hcost : ∀ t d, t + d < n → suffixHeight d ≤ v t) :
    n ≤ 21
```

**And.** `fixed_block_count_lower` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:90`

> A bounded finite block cover of the fixed number of even gaps needs this many blocks.

```lean
theorem fixed_block_count_lower {ι : Type*} [Fintype ι] (length : ι → ℕ)
    (hsum : ∑ i, length i = 780237) (hbound : ∀ i, length i ≤ 21) :
    37155 ≤ Fintype.card ι
```

**And.** `fixed_nonzero_lower` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:99`

> The two additional noncritical corrections are retained as an explicit premise.

```lean
theorem fixed_nonzero_lower {C T : ℕ} (hC : 37155 ≤ C) (hfilter : C + 2 ≤ T) :
    37157 ≤ T
```

**And.** `fixed_deviation_lower` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:104`

> The three-level support cover is retained as an explicit premise.

```lean
theorem fixed_deviation_lower {C S : ℕ} (hC : 37155 ≤ C) (hcover : C ≤ 1 + 2 * S) :
    18577 ≤ S
```

**And.** `block_hits_card` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:109`

> Hitting each disjoint full-width block gives a cardinality lower bound.

```lean
theorem block_hits_card {S : Finset ℕ} {b n w : ℕ}
    (hit : ∀ j : Fin (n / w),
      ∃ i ∈ S, b + w * j.val ≤ i ∧ i < b + w * (j.val + 1)) :
    n / w ≤ S.card
```

**And.** `window_hits_card` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:138`

> Every complete width-w subwindow of an interval hits S.

```lean
theorem window_hits_card {S : Finset ℕ} {b n w : ℕ}
    (hit : ∀ j : ℕ, j + w ≤ n →
      ∃ i ∈ S, b + j ≤ i ∧ i < b + j + w) :
    n / w ≤ S.card
```

**And.** `window_hits_interval_card` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:154`

> The witnesses belong to the queried interval, so its filtered count suffices.

```lean
theorem window_hits_interval_card {S : Finset ℕ} {b n w : ℕ}
    (hit : ∀ j : ℕ, j + w ≤ n →
      ∃ i ∈ S, b + j ≤ i ∧ i < b + j + w) :
    n / w ≤ (S.filter fun i => b ≤ i ∧ i < b + n).card
```

**And.** `r_arc_critical_count` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:164`

> The source-time R arc has length 301994.

```lean
theorem r_arc_critical_count {S : Finset ℕ} {b : ℕ}
    (hit : ∀ j : ℕ, j + 21 ≤ 301994 →
      ∃ i ∈ S, b + j ≤ i ∧ i < b + j + 21) :
    14380 ≤ S.card
```

**And.** `r_arc_interval_critical_count` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:173`

> The fixed R-arc bound retains membership in the original time interval.

```lean
theorem r_arc_interval_critical_count {S : Finset ℕ}
    (hit : ∀ j : ℕ, j + 21 ≤ 301994 →
      ∃ i ∈ S, 478245 + j ≤ i ∧ i < 478245 + j + 21) :
    14380 ≤ (S.filter fun i => 478245 ≤ i ∧ i < 780239).card
```

**And.** `injective_deviation_count` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:182`

> An explicitly injective choice of a responsible deviation preserves count.

```lean
theorem injective_deviation_count {α β : Type*} [DecidableEq α] [DecidableEq β]
    {C : Finset α} {D : Finset β} (f : α → β)
    (hmem : ∀ i ∈ C, f i ∈ D)
    (hinj : Set.InjOn f (C : Set α)) :
    C.card ≤ D.card
```

**And.** `disjoint_pair_deviation_count` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:190`

> Disjoint pairs prevent one deviation from paying for two selected events.

```lean
theorem disjoint_pair_deviation_count {α β : Type*}
    [DecidableEq α] [DecidableEq β] {C : Finset α} {D : Finset β}
    (pair : α → Finset β)
    (hdisj : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → Disjoint (pair i) (pair j))
    (hcover : ∀ i ∈ C, ∃ j ∈ D, j ∈ pair i) :
    C.card ≤ D.card
```

**And.** `r_arc_deviation_count` &mdash; kernel-checked, `Problems/Juggler/CubicCriticalLocation.lean:213`

> The localized critical count transfers through supplied disjoint pairs.

```lean
theorem r_arc_deviation_count {α : Type*} [DecidableEq α]
    {C : Finset ℕ} {D : Finset α} {b : ℕ}
    (hit : ∀ j : ℕ, j + 21 ≤ 301994 →
      ∃ i ∈ C, b + j ≤ i ∧ i < b + j + 21)
    (pair : ℕ → Finset α)
    (hdisj : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → Disjoint (pair i) (pair j))
    (hcover : ∀ i ∈ C, ∃ j ∈ D, j ∈ pair i) :
    14380 ≤ D.card
```

## 26. `J-cycle-later-return-certificate` &mdash; covers 0.16

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.63; different result 0.78.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** For a prescribed word with full ideal exponent 0<p<1 and every proper tail q_j=p/p_j<1, two traces whose sources and proper states are at least m>=1 satisfy 0<=F(z)-F(w)<p*m^(p-1)*(z-w)+K_W(m), where K_W=1+sum(q_j*m^(q_j-1)). The condition 2*p*m^(p-1)+K_W<=2 forces strict contraction on gaps at least two. For p>1/2 and a proper prefix this sufficient certificate requires m>(2p)^(1/(1-p)); hence it cannot hold uniformly at a fixed minimum for a family with p approaching one from below. This is a limitation of the one-sided error estimate, not a counterexample to true paired contraction or a claim that every possible later upper word has these exponents. The exact transported loss, paired bound and necessary finite minimum threshold are kernel checked in ReturnWordLoss, retaining the publish  *(truncated; read the ledger row)*

**Declarations.** `certificate_requires_large_minimum` &mdash; kernel-checked, `Problems/Juggler/ReturnWordLoss.lean:408`

```lean
theorem certificate_requires_large_minimum {m : ℝ} (hm : 0 < m)
    {w : List Branch} (hw : 2 ≤ w.length) (hp : exponent w < 1)
    (hc : 2 * (exponent w * m ^ (exponent w - 1)) + budget m w ≤ 2) :
    (2 * exponent w) ^ (1 / (1 - exponent w)) < m
```

**And.** `eval_mono` &mdash; kernel-checked, `Problems/Juggler/ReturnWordLoss.lean:77`

```lean
theorem eval_mono (w : List Branch) : Monotone (eval w)
```

**And.** `paired_bound` &mdash; kernel-checked, `Problems/Juggler/ReturnWordLoss.lean:180`

```lean
theorem paired_bound {m : ℝ} (hm : 0 < m) {w : List Branch} (hw : w ≠ [])
    (ht : ConcaveTails w) (hp : exponent w ≤ 1) {x y : ℕ}
    (hx : 0 < x) (hmx : m ≤ x) (hxy : x ≤ y) (ha : InnerAbove m x w) :
    (eval w y : ℝ) - eval w x <
      exponent w * m ^ (exponent w - 1) * ((y : ℝ) - x) + budget m w
```

**And.** `loss_exact` &mdash; kernel-checked, `Problems/Juggler/ReturnWordLoss.lean:241`

```lean
theorem loss_exact (w : List Branch) (x : ℕ) :
    (x : ℝ) ^ exponent w - (eval w x : ℝ) = transportedLoss x w
```

## 27. `J-cycle-quartic-formal-cells` &mdash; covers 0.16

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.51; different result 0.22.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Exact guarded F/G return comparisons: for distinct ordered actual periodic sources, an earlier F and later G invert exactly when their B=OE cell agrees; each periodic cell has at most one G and an F inverts at most one G. The auxiliary OE source cell is exact, and sources in the same cell with valley at least m>1 have loglog gap below logEta(m)=log(log(m+1)/log(m)); logEta is positive, decreasing and below 1/(m log m). The global cell-prefix permutation and resulting gcd/height restrictions remain written results. The shared cube excludes x^3=(v^2+1)^2+1 modulo7. For every odd x, even h and odd v with h^2<=x^3 and v^2<=h, either h^2+3<=x^3 or v^2+3<=h, and (v^2+1)^2+3<=x^3; this specializes to the actual O(x), B(x) cells. The new logarithmic pair correction and its full cycle-budget assemb  *(truncated; read the ledger row)*

**Declarations.** `periodic_inversion_iff_cell` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:135`

```lean
theorem periodic_inversion_iff_cell {C : Set ℕ} {m M x y : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hx : x ∈ C) (hy : y ∈ C)
    (hF : FGuard x) (hG : GGuard y) (hxy : x ≤ y) :
    G y < F x ↔ B x = B y
```

**And.** `periodic_G_cell_unique` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:148`

```lean
theorem periodic_G_cell_unique {C : Set ℕ} {m M x y : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hx : x ∈ C) (hy : y ∈ C)
    (hGx : GGuard x) (hGy : GGuard y) (hcell : B x = B y) : x = y
```

**And.** `periodic_F_inverts_at_most_one_G` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:155`

```lean
theorem periodic_F_inverts_at_most_one_G {C : Set ℕ} {m M x y z : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M)
    (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hF : FGuard x) (hGy : GGuard y) (hGz : GGuard z)
    (hxy : x ≤ y) (hxz : x ≤ z)
    (hyi : G y < F x) (hzi : G z < F x) : y = z
```

**And.** `same_cell_loglog_lt_min` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:224`

```lean
theorem same_cell_loglog_lt_min {m x y v : ℕ}
    (hm : 1 < m) (hmx : m ≤ x) (hmy : m ≤ y) (hmv : m ≤ v)
    (hxc : B x = v) (hyc : B y = v) :
    Real.log (Real.log (x : ℝ)) - Real.log (Real.log (y : ℝ)) < logEta m
```

**And.** `cube_ne_square_successor_square_successor` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:233`

> The shared cube and square forbid simultaneous unit remainders.

```lean
theorem cube_ne_square_successor_square_successor (x v : ℕ) :
    x ^ 3 ≠ (v ^ 2 + 1) ^ 2 + 1
```

**And.** `guarded_OE_remainder_dichotomy` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:243`

> Two actual parity switches leave at least one remainder at least three.

```lean
theorem guarded_OE_remainder_dichotomy {x h v : ℕ}
    (hx : x % 2 = 1) (hh : h % 2 = 0) (hv : v % 2 = 1)
    (hO : h ^ 2 ≤ x ^ 3) (hE : v ^ 2 ≤ h) :
    h ^ 2 + 3 ≤ x ^ 3 ∨ v ^ 2 + 3 ≤ h
```

**And.** `guarded_OE_lower_cube` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:256`

> A parity-guarded OE pair has a strictly improved lower cube face.

```lean
theorem guarded_OE_lower_cube {x h v : ℕ}
    (hx : x % 2 = 1) (hh : h % 2 = 0) (hv : v % 2 = 1)
    (hO : h ^ 2 ≤ x ^ 3) (hE : v ^ 2 ≤ h) :
    (v ^ 2 + 1) ^ 2 + 3 ≤ x ^ 3
```

**And.** `actual_OE_lower_cube` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:271`

```lean
theorem actual_OE_lower_cube {x : ℕ}
    (hx : x % 2 = 1) (hO : O x % 2 = 0) (hB : B x % 2 = 1) :
    (B x ^ 2 + 1) ^ 2 + 3 ≤ x ^ 3
```

**And.** `B_eq_iff` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:73`

```lean
theorem B_eq_iff {x v : ℕ} :
    B x = v ↔ v ^ 4 ≤ x ^ 3 ∧ x ^ 3 < (v + 1) ^ 4
```

**And.** `B_source_cell` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:77`

```lean
theorem B_source_cell (x : ℕ) :
    B x ^ 2 ≤ O x ∧ O x < (B x + 1) ^ 2
```

**And.** `logEta_pos` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:183`

```lean
theorem logEta_pos {v : ℝ} (hv : 1 < v) : 0 < logEta v
```

**And.** `logEta_antitone` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:186`

```lean
theorem logEta_antitone {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    logEta v ≤ logEta u
```

**And.** `logEta_lt_inv` &mdash; kernel-checked, `Problems/Juggler/QuarticCells.lean:190`

```lean
theorem logEta_lt_inv {v : ℝ} (hv : 1 < v) :
    logEta v < 1 / (v * Real.log v)
```

## 28. `J-cycle-threshold-relaxation` &mdash; covers 0.16

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.68; different result 0.19.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For each integer b>=3, the size-switched map S_b on integers b<=x<b^3 uses floor(sqrt(x^3)) for x<b^2 and floor(sqrt(x)) otherwise. This finite interval is invariant and S_b has no fixed point, so it has a primitive cycle of length at least two at arbitrarily large minima. Its cycles have the separated-image rank rotation, coprime branch counts and ceiling mechanical words; 3^o>2^L. S_b is not Juggler: a full cycle is a Juggler cycle iff every low state is odd and every high state even. This parity compatibility is not established, and the construction refutes only attempts to get no-cycle from the listed parity-relaxed properties alone. Consolidated in Paper A Section 3.10 and formalized in the seven Cubic modules. The cited declarations and supporting modules are compiled kernel proofs.   *(truncated; read the ledger row)*

**Declarations.** `thresholdMap_exists_primitive` &mdash; kernel-checked, `Problems/Juggler/CubicBand.lean:430`

> The existence assertion can be stated with a primitive period and distinct pre-return states.

```lean
theorem thresholdMap_exists_primitive {b : ℕ} (hb : 3 ≤ b) :
    ∃ x L, InCubicBand b x ∧ 2 ≤ L ∧ (thresholdMap b)^[L] x = x ∧
      ∀ i j, i < L → j < L →
        (thresholdMap b)^[i] x = (thresholdMap b)^[j] x → i = j
```

**And.** `threshold_sorted_rotation` &mdash; kernel-checked, `Problems/Juggler/CubicBand.lean:273`

> Rotation follows from closure alone after sorting; the cutoff is the branch count.

```lean
theorem threshold_sorted_rotation {b L : ℕ}
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand b (c i))
    (hstep : ∀ i, c (p i) = thresholdMap b (c i)) :
    ∃ o ≤ L, (∀ i, c i < b ^ 2 ↔ i.val < o) ∧
      (Finset.univ.filter (fun i => c i < b ^ 2)).card = o ∧
      (∀ i, (p i).val = (i.val + (L - o)) % L)
```

**And.** `thresholdMap_eq_floorPower_iff` &mdash; kernel-checked, `Problems/Juggler/CubicBand.lean:390`

> At a state in the band, equality with Juggler is exactly parity compatibility.

```lean
theorem thresholdMap_eq_floorPower_iff {b x : ℕ} (hb : 3 ≤ b)
    (hx : InCubicBand b x) :
    thresholdMap b x = floorPower x ↔ (x % 2 = 1 ↔ x < b ^ 2)
```

**And.** `thresholdMap` &mdash; kernel-checked, `Problems/Juggler/CubicBand.lean:15`

> A parity-relaxed map: its branch is chosen by size.

```lean
def thresholdMap (b x : ℕ) : ℕ
```

**And.** `thresholdMap_invariant` &mdash; kernel-checked, `Problems/Juggler/CubicBand.lean:30`

```lean
theorem thresholdMap_invariant {b x : ℕ} (hb : 3 ≤ b)
    (hx : InCubicBand b x) : InCubicBand b (thresholdMap b x)
```

**And.** `thresholdMap_ne_self` &mdash; kernel-checked, `Problems/Juggler/CubicBand.lean:42`

```lean
theorem thresholdMap_ne_self {b x : ℕ} (hb : 3 ≤ b)
    (hx : InCubicBand b x) : thresholdMap b x ≠ x
```

**And.** `thresholdMap_image_separation` &mdash; kernel-checked, `Problems/Juggler/CubicBand.lean:83`

> Weak branch-image separation; injectivity on periodic points removes ties.

```lean
theorem thresholdMap_image_separation {b x y : ℕ}
    (hx : InCubicBand b x) (hy : InCubicBand b y)
    (hhi : b ^ 2 ≤ x) (hlo : y < b ^ 2) :
    thresholdMap b x ≤ thresholdMap b y
```

**And.** `threshold_iterates_eq_of_compatible` &mdash; kernel-checked, `Problems/Juggler/CubicBand.lean:410`

> Exact compatibility along a threshold orbit identifies its iterates with Juggler.

```lean
theorem threshold_iterates_eq_of_compatible {b x : ℕ} (hb : 3 ≤ b)
    (hx : InCubicBand b x)
    (hcompatible : ∀ k, ((thresholdMap b)^[k] x) % 2 = 1 ↔
      (thresholdMap b)^[k] x < b ^ 2) :
    ∀ k, (thresholdMap b)^[k] x = floorPower^[k] x
```

## 29. `J-fate-one-sided-moments` &mdash; covers 0.16

*Reads as: the claim asserts more than the declarations state (0.84).*

*Claim broader 0.84; declaration narrower 0.52; different result 0.41.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Theorem 9.1 (the one-sided form) in exact form, by exponential moments and without the martingale, carrying out the paper's remark after Proposition 9.3. For a tilt x >= 1 let badMass(t) be the sum over the L-bad words w of length t of #[w] x^{o(w)}, the tilted mass of the bad cylinders of depth t. Under the one-sided hypothesis OneSidedShare (every L-bad cylinder of depth 1 <= t < d sends at most q #[w] + err of its members to an odd next letter), bad words being prefix-closed and a cylinder splitting into its two children, badMass(t+1) <= (1 + (x-1) q) badMass(t) + (x-1) err (2x)^t (badMass_succ_le), which unrolls to badMass(t+1) <= x (1 + (x-1) q)^t N + (x-1) err t (2x)^t with N the odd starts of (y, 2y] (badMass_le). Lemma 8.1 and the Markov tilt put every odd failure of (y, 2y  *(truncated; read the ledger row)*

**Declarations.** `one_sided_bound` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:366`

> **Theorem 9.1 by exponential moments, exact.** Under the one-sided hypothesis at scale `y` with depth `d ≥ C L(y)`, above a certified floor `N₀`, the odd failures in `(y, 2y]` number at most `(x a_q^{d-1} N + (x-1) err (d-1) (2x)^{d-1}) / x^{p_C d}` for every tilt `x ≥ 1`, with `N` the odd starts of `(y, 2y]` and `a_q = 1 + (x-1) q`.

```lean
theorem one_sided_bound {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y)
    {C x q err : ℝ} (hC : 0 < C) (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (herr : 0 ≤ err)
    {d : ℕ} (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d)
    (hH : OneSidedShare y (scaleL N₀ y) q err d) :
    ((oddFailures y).card : ℝ) ≤
      (x * (1 + (x - 1) * q) ^ (d - 1) * (cylinder y 0 []).card
        + (x - 1) * err * ((d : ℝ) - 1) * (2 * x) ^ (d - 1)) / x ^ (pC C * d)
```

**And.** `cylinder_split` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:54`

> A cylinder of depth `t` splits into its two children at depth `t + 1`.

```lean
theorem cylinder_split (y t : ℕ) (w : List Branch) (hw : w.length = t) :
    (cylinder y t w).card
      = (cylinder y (t + 1) (w ++ [Branch.even])).card
        + (cylinder y (t + 1) (w ++ [Branch.odd])).card
```

**And.** `LBad_of_LBad_append` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:87`

> Badness is inherited by prefixes: a bad child has a bad parent.

```lean
theorem LBad_of_LBad_append {L : ℝ} {w : List Branch} {b : Branch}
    (h : LBad L (w ++ [b])) : LBad L w
```

**And.** `OneSidedShare` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:161`

> The paper's one-sided hypothesis `H_q(C, A)` at scale `y`, for the depths `1 ≤ t < d`: every `L`-bad cylinder sends at most the share `q` of its members, plus `err`, to an odd next letter.

```lean
def OneSidedShare (y : ℕ) (L q err : ℝ) (d : ℕ) : Prop
```

**And.** `badMass_succ_le` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:167`

> **One depth.** Under the hypothesis at depth `1 ≤ t < d`, `badMass (t+1) ≤ a_q · badMass t + (x - 1) err (2x)^t` with `a_q = 1 + (x-1) q`.

```lean
theorem badMass_succ_le {y : ℕ} {L x q err : ℝ} {d t : ℕ} (hx : 1 ≤ x) (herr : 0 ≤ err)
    (hH : OneSidedShare y L q err d) (ht1 : 1 ≤ t) (htd : t < d) :
    badMass y L x (t + 1)
      ≤ (1 + (x - 1) * q) * badMass y L x t + (x - 1) * err * (2 * x) ^ t
```

**And.** `badMass_le` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:262`

> **Unrolled.** Under the hypothesis up to depth `d`, for `t + 1 ≤ d`, `badMass (t+1) ≤ x a_q^t N + (x-1) err t (2x)^t`, using `a_q ≤ 2x`.

```lean
theorem badMass_le {y : ℕ} {L x q err : ℝ} {d : ℕ} (hx : 1 ≤ x) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (herr : 0 ≤ err) (hH : OneSidedShare y L q err d) :
    ∀ t, t + 1 ≤ d → badMass y L x (t + 1)
      ≤ x * (1 + (x - 1) * q) ^ t * (cylinder y 0 []).card + (x - 1) * err * t * (2 * x) ^ t
```

**And.** `oddFailures_card_le_badMass` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:318`

> **Lemma 8.1 with the Markov tilt.** Every odd failure in `(y, 2y]` lies in a bad cylinder of depth `d ≥ C L(y)` whose word has at least `p_C d` odd letters, so the failures number at most `badMass d / x^{p_C d}`.

```lean
theorem oddFailures_card_le_badMass {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y) {C x : ℝ}
    (hC : 0 < C) (hx : 1 ≤ x) {d : ℕ} (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d) :
    ((oddFailures y).card : ℝ) ≤ badMass y (scaleL N₀ y) x d / x ^ (pC C * d)
```

**And.** `tilt_pow_ratio` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:397`

> `a_q^d / x^{p d} = e^{-d D(p ‖ q)}` at the re-centring tilt (Proposition 9.3's identity).

```lean
theorem tilt_pow_ratio {p q : ℝ} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) (d : ℕ) :
    (1 + (tilt p q - 1) * q) ^ d / tilt p q ^ (p * d) = Real.exp (-(d * klDiv p q))
```

**And.** `one_sided_bound_kl` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:411`

> **Theorem 9.1 at the re-centring tilt.** With `q < p_C < 1` and `x = p_C(1-q)/(q(1-p_C))`, the main term is `(x/a_q) N e^{-d D(p_C ‖ q)}`: the exponent `C D(p_C ‖ q)/log 2` per unit of `L(y)`, which the paper records is at least the Azuma exponent `e_q(C)` of Theorem 9.1.

```lean
theorem one_sided_bound_kl {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y)
    {C q err : ℝ} (hC : 0 < C) (hq0 : 0 < q) (hqp : q < pC C) (hp1 : pC C < 1)
    (herr : 0 ≤ err) {d : ℕ}
    (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d) (hH : OneSidedShare y (scaleL N₀ y) q err d) :
    ((oddFailures y).card : ℝ) ≤
      tilt (pC C) q / (1 + (tilt (pC C) q - 1) * q) * (cylinder y 0 []).card
          * Real.exp (-(d * klDiv (pC C) q))
        + (tilt (pC C) q - 1) * err * ((d : ℝ) - 1) * (2 * tilt (pC C) q) ^ (d - 1)
          / tilt (pC C) q ^ (pC C * d)
```

## 30. `J-cycle-itinerary-length-ge-fourteen` &mdash; covers 0.17

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.31; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is at least 14. Strengthened through J-cycle-itinerary-length-eighty-four-or-ge-eighty-five: lengths 14–83 except the named leftovers along the way are excluded, so the laboratory leftover is period 84 or at least 85. Lean theorem cycle_itinerary_length_ge_fourteen. This is not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `cycle_itinerary_length_ge_fourteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:352`

> If a nontrivial cycle exists, its period is at least `14`. Corollary of the floor-`53` leftover; lengths `14`–`18` and `20`–`29` are excluded separately.

```lean
theorem cycle_itinerary_length_ge_fourteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : 14 ≤ w.length
```

## 31. `J-fate-collapse-bias` &mdash; covers 0.17

*Reads as: the claim asserts more than the declarations state (0.86).*

*Claim broader 0.86; declaration narrower 0.43; different result 0.19.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The collapsed component is nearly fair, exact layer (Paper C Section 10(d), after the cylinder-energy measurement). For a finite set S of starts and a depth t, fiber S t v = #{n in S : J^t(n) = v}, window S t a b = the starts whose t-th iterate lies in [a, b], and windowBias S t a b = #{odd iterate} - #{even iterate} in the window, the bias of the next letter. windowBias = - sum over v in [a, b] of (-1)^v fiber(v) (windowBias_eq_sum, on card_filter_window), hence |windowBias| <= sum over v in [a, b) of |fiber(v+1) - fiber(v)| + fiber(b) (abs_windowBias_le), by summation by parts on alternating sums with the partial sums of (-1)^i bounded by 1 (abs_alt_sum_le). One step of the map: fiber(t+1, v) = sum of fiber(t, u) over the preimages u of v, all below (v+1)^2 (fiber_succ, lt_sq_succ_of_flo  *(truncated; read the ledger row)*

**Declarations.** `collapse_bias_le` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:395`

> **The collapsed component is nearly fair.** If the depth-`t` fiber profile lies between `m v` and `M v` on the double block `[v², (v+2)²)` for every `v` in `[a, b)`, the next-letter bias of the starts whose `(t+1)`-st iterate lies in `[a, b]` is at most `Σ_{v ∈ [a,b)} ((v+1)(M v - m v) + 2 M v)`, plus twice the mass arriving through odd preimages, plus one fiber.

```lean
theorem collapse_bias_le (S : Finset ℕ) (t a b : ℕ) (hab : a ≤ b)
    (m M : ℕ → ℕ)
    (hlo : ∀ v ∈ Ico a b, ∀ u ∈ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)),
      m v ≤ fiber S t u)
    (hhi : ∀ v ∈ Ico a b, ∀ u ∈ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)),
      fiber S t u ≤ M v) :
    |windowBias S (t + 1) a b|
      ≤ ∑ v ∈ Ico a b, ((v + 1) * ((M v : ℝ) - m v) + 2 * M v)
        + 2 * ∑ v ∈ Icc a b, oddPart S t v + fiber S (t + 1) b
```

**And.** `card_filter_window` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:65`

> The starts of the window whose iterate satisfies `p` are counted by the fibers over the values of `[a, b]` satisfying `p`.

```lean
theorem card_filter_window (S : Finset ℕ) (t a b : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((window S t a b).filter fun n => p (floorPower^[t] n)).card
      = ∑ v ∈ (Icc a b).filter p, fiber S t v
```

**And.** `windowBias_eq_sum` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:92`

> The bias is the alternating sum of the fibers.

```lean
theorem windowBias_eq_sum (S : Finset ℕ) (t a b : ℕ) :
    windowBias S t a b = -∑ v ∈ Icc a b, (-1 : ℝ) ^ v * fiber S t v
```

**And.** `abs_alt_sum_le` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:125`

> Summation by parts: `|Σ_{i<n} (-1)^i h_i| ≤ Σ_{i<n-1} |h_{i+1} - h_i| + h_{n-1}` for nonnegative `h`.

```lean
theorem abs_alt_sum_le (h : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hh : ∀ i < n, 0 ≤ h i) :
    |∑ i ∈ range n, (-1 : ℝ) ^ i * h i|
      ≤ ∑ i ∈ range (n - 1), |h (i + 1) - h i| + h (n - 1)
```

**And.** `abs_windowBias_le` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:161`

> **The bias is bounded by the variation of the fiber profile.**

```lean
theorem abs_windowBias_le (S : Finset ℕ) (t a b : ℕ) (hab : a ≤ b) :
    |windowBias S t a b|
      ≤ ∑ v ∈ Ico a b, |(fiber S t (v + 1) : ℝ) - fiber S t v| + fiber S t b
```

**And.** `lt_sq_succ_of_floorPower_eq` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:187`

> A preimage of `v` under the map lies below `(v+1)²`.

```lean
theorem lt_sq_succ_of_floorPower_eq {u v : ℕ} (h : floorPower u = v) :
    u < (v + 1) * (v + 1)
```

**And.** `fiber_succ` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:204`

> The fiber at depth `t+1` is the sum of the depth-`t` fibers over the preimages.

```lean
theorem fiber_succ (S : Finset ℕ) (t v : ℕ) :
    fiber S (t + 1) v = ∑ u ∈ pre v, fiber S t u
```

**And.** `pre_filter_even` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:225`

> The even preimages of `v` are the even numbers of `[v², (v+1)²)` (Lemma 3.1's even block, in fiber form).

```lean
theorem pre_filter_even (v : ℕ) :
    (pre v).filter (fun u => u % 2 = 0)
      = (Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0)
```

**And.** `fiber_succ_eq` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:251`

> `fiber(t+1, v) = blockSum + oddPart`.

```lean
theorem fiber_succ_eq (S : Finset ℕ) (t v : ℕ) :
    (fiber S (t + 1) v : ℝ) = blockSum S t v + oddPart S t v
```

**And.** `evenCount_le` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:270`

```lean
theorem evenCount_le (v : ℕ) : evenCount v ≤ v + 1
```

**And.** `le_evenCount` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:288`

```lean
theorem le_evenCount (v : ℕ) : v ≤ evenCount v
```

**And.** `blockSum_sub_le` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:307`

> **The even branch smooths.** If the depth-`t` profile lies between `m` and `M` on the double block `[v², (v+2)²)`, consecutive block sums differ by at most `(v+1)(M-m) + 2M`.

```lean
theorem blockSum_sub_le (S : Finset ℕ) (t v : ℕ) {m M : ℕ}
    (hlo : ∀ u ∈ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)), m ≤ fiber S t u)
    (hhi : ∀ u ∈ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)), fiber S t u ≤ M) :
    |blockSum S t (v + 1) - blockSum S t v| ≤ (v + 1) * ((M : ℝ) - m) + 2 * M
```

**And.** `sum_abs_oddPart_sub_le` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:361`

> The variation of the odd branch over a window is at most twice its mass.

```lean
theorem sum_abs_oddPart_sub_le (S : Finset ℕ) (t a b : ℕ) :
    ∑ v ∈ Ico a b, |oddPart S t (v + 1) - oddPart S t v|
      ≤ 2 * ∑ v ∈ Icc a b, oddPart S t v
```

**And.** `fiber_succ_sandwich` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:434`

> **A sandwich propagates through an even step.** If the depth-`t` profile lies between `m` and `M` on the block `[v², (v+1)²)` and the odd branch at `v` carries at most `P`, then `v m ≤ fiber(t+1, v) ≤ (v+1) M + P`.

```lean
theorem fiber_succ_sandwich (S : Finset ℕ) (t v : ℕ) {m M P : ℕ}
    (hlo : ∀ u ∈ Ico (v * v) ((v + 1) * (v + 1)), m ≤ fiber S t u)
    (hhi : ∀ u ∈ Ico (v * v) ((v + 1) * (v + 1)), fiber S t u ≤ M)
    (hP : oddPart S t v ≤ P) :
    v * m ≤ fiber S (t + 1) v ∧ fiber S (t + 1) v ≤ (v + 1) * M + P
```

**And.** `collapse_bias_two_step` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:481`

> **Two even steps.** If the depth-`t` profile lies between `m w` and `M w` on the block `[w⁴, (w+2)⁴)` and the odd branch at depth `t` is at most `P w` on `[w², (w+2)²)`, for every `w` in `[a, b)`, the next-letter bias of the starts whose `(t+2)`-nd iterate lies in `[a, b]` is bounded by the propagated sandwich `w² m w ≤ fiber(t+1, ·) ≤ (w+2)² M w + P w`: the relative oscillation of the profile is not amplified by an even step, and the loss is a relative `O(1/w)`.

```lean
theorem collapse_bias_two_step (S : Finset ℕ) (t a b : ℕ) (hab : a ≤ b) (m M P : ℕ → ℕ)
    (hlo : ∀ w ∈ Ico a b, ∀ u ∈ Ico (w * w * (w * w)) ((w + 1 + 1) * (w + 1 + 1)
      * ((w + 1 + 1) * (w + 1 + 1))), m w ≤ fiber S t u)
    (hhi : ∀ w ∈ Ico a b, ∀ u ∈ Ico (w * w * (w * w)) ((w + 1 + 1) * (w + 1 + 1)
      * ((w + 1 + 1) * (w + 1 + 1))), fiber S t u ≤ M w)
    (hP : ∀ w ∈ Ico a b, ∀ v ∈ Ico (w * w) ((w + 1 + 1) * (w + 1 + 1)),
      oddPart S t v ≤ P w) :
    |windowBias S (t + 1 + 1) a b|
      ≤ ∑ w ∈ Ico a b, ((w + 1) * ((((w + 1 + 1) * (w + 1 + 1) * M w + P w : ℕ) : ℝ)
            - ((w * w * m w : ℕ) : ℝ))
          + 2 * (((w + 1 + 1) * (w + 1 + 1) * M w + P w : ℕ) : ℝ))
        + 2 * ∑ w ∈ Icc a b, oddPart S (t + 1) w + fiber S (t + 1 + 1) b
```

## 32. `J-small-cycle-census-eighteen` &mdash; covers 0.17

*Reads as: the claim asserts more than the declarations state (0.86).*

*Claim broader 0.86; declaration narrower 0.28; different result 0.5.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** No itinerary of length at most 18 is a Juggler cycle itinerary at any n ≥ 2, except that length 19 is not excluded here. Lengths ≤ 11 are J-small-cycle-census-eleven; lengths 12, 13, and 16 remain excluded at the residual floor 12; lengths 14, 15, 17, and 18 are excluded by cycle_finance_min_fifty_three (finance_excludes_length_fourteen and companions, packaged as no_cycle_itinerary_length_le_eighteen). Strengthened by J-small-cycle-census-nineteen. This is a Lean companion to Paper A Theorem 4.6, not a leftover-itinerary census, not an exclusion of length 19, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declarations.** `no_cycle_itinerary_length_le_eighteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:436`

> Census extension: no cycle itinerary of length at most `18`. Length `11` is the near-convergent killed by the floor `53`; `14`–`18` die by the same comparison.

```lean
theorem no_cycle_itinerary_length_le_eighteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 18) : ¬CycleItinerary n w
```

**And.** `cycle_finance_min_fifty_three` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:288`

> Finance at the rotated odd minimum after the residual floor `53`: `(371/2)(3^o - 2^L) ≤ L 3^o`, because the minimum is at least `53` and `53 log 53 > 371/2`.

```lean
theorem cycle_finance_min_fifty_three {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (371 / 2 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w
```

**And.** `finance_excludes_length_fourteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:429`

> Finance alone excludes cycle itineraries of length exactly `14`.

```lean
theorem finance_excludes_length_fourteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 14) : ¬CycleItinerary n w
```

**And.** `cycle_finance_min_thirteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:81`

> Finance at the rotated odd minimum: every cycle itinerary satisfies `(65/2)(3^o - 2^L) ≤ L 3^o`, because the minimum is at least `13` and `13 log 13 > 65/2`.

```lean
theorem cycle_finance_min_thirteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (65 / 2 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w
```

## 33. `J-small-cycle-census-eleven` &mdash; covers 0.17

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.3; different result 0.17.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** No itinerary of length at most eleven is a Juggler cycle itinerary at any n ≥ 2; equivalently a nontrivial Juggler cycle, if one exists, has period at least twelve, and in fact at least fourteen by J-cycle-itinerary-length-ge-fourteen. Strengthened by J-small-cycle-census-eighteen. Length 11 is the first near-convergent (2^11 < 3^7); the residual floor 53 plus cycle_finance_min_fifty_three excludes it (finance_excludes_length_eleven, packaged as no_cycle_itinerary_length_le_eleven). This is a Lean companion to Paper A Theorem 4.6, not a leftover-itinerary census of the thirty length-11 short-gap families, not a theorem named no_cycle_itinerary_length_eleven, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declarations.** `no_cycle_itinerary_length_le_eleven` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:342`

> Census extension: no cycle itinerary of length at most `11`. Lengths `≤ 10` are the prior census; `11` is finance at the residual floor `53`.

```lean
theorem no_cycle_itinerary_length_le_eleven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 11) : ¬CycleItinerary n w
```

**And.** `finance_excludes_length_eleven` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:319`

> Finance excludes length `11`: `o ≥ 7` forces `(371/2)(3^o - 2048) > 11 · 3^o`. Not a leftover-itinerary census.

```lean
theorem finance_excludes_length_eleven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 11) : ¬CycleItinerary n w
```

**And.** `cycleItinerary_iterate_not_lt_fifty_three` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:248`

> Residual class `{1,…,52}` is disjoint from a nontrivial cycle.

```lean
theorem cycleItinerary_iterate_not_lt_fifty_three {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    53 ≤ floorPower^[i] n
```

## 34. `J-cycle-short-return-cells` &mdash; covers 0.18

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.38; different result 0.45.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Appendix E.1, formal subset. The prescribed OE return equals y iff y^4<=x^3<(y+1)^4. Every prescribed OOE return v satisfies v^8<=x^9<(v+2)^8; relative to an eighth-root cell y it is y or y-1. If v is odd, it is the greatest odd integer whose eighth power is at most x^9. The family s^4->s^6->s^3 has all three states odd when s is odd, so endpoint parities do not imply the hidden E guard. Actual OE/OOE composition bridges retain every source-parity premise. Kernel verified; no arbitrary-root or OOEOE projection theorem is claimed by this row.

**Declarations.** `ooe_odd_maximal` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:135`

```lean
theorem ooe_odd_maximal {x y : ℕ} (hx : ooe x % 2 = 1)
    (hy : y % 2 = 1) (hpow : y ^ 8 ≤ x ^ 9) :
    y ≤ ooe x
```

**And.** `oe` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:12`

> The prescribed O then E return, without a source-parity assumption.

```lean
def oe (x : ℕ) : ℕ
```

**And.** `ooe` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:15`

> The prescribed O, O, E return.

```lean
def ooe (x : ℕ) : ℕ
```

**And.** `oe_eq_iff` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:17`

```lean
theorem oe_eq_iff {x y : ℕ} :
    oe x = y ↔ y ^ 4 ≤ x ^ 3 ∧ x ^ 3 < (y + 1) ^ 4
```

**And.** `oe_cell` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:21`

```lean
theorem oe_cell (x : ℕ) :
    oe x ^ 4 ≤ x ^ 3 ∧ x ^ 3 < (oe x + 1) ^ 4
```

**And.** `oe_actual` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:25`

```lean
theorem oe_actual {x : ℕ} (hx : x % 2 = 1)
    (hu : (x ^ 3).sqrt % 2 = 0) :
    floorPower (floorPower x) = oe x
```

**And.** `ooe_actual` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:31`

```lean
theorem ooe_actual {x : ℕ} (hx : x % 2 = 1)
    (hu : (x ^ 3).sqrt % 2 = 1)
    (hv : (((x ^ 3).sqrt) ^ 3).sqrt % 2 = 0) :
    floorPower (floorPower (floorPower x)) = ooe x
```

**And.** `ooe_upper_pow` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:79`

```lean
theorem ooe_upper_pow (x : ℕ) : ooe x ^ 8 ≤ x ^ 9
```

**And.** `ooe_lower_pow` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:105`

```lean
theorem ooe_lower_pow (x : ℕ) : x ^ 9 < (ooe x + 2) ^ 8
```

**And.** `ooe_two_cell` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:117`

```lean
theorem ooe_two_cell (x : ℕ) :
    ooe x ^ 8 ≤ x ^ 9 ∧ x ^ 9 < (ooe x + 2) ^ 8
```

**And.** `ooe_one_integer` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:121`

```lean
theorem ooe_one_integer {x y : ℕ}
    (hy : y ^ 8 ≤ x ^ 9 ∧ x ^ 9 < (y + 1) ^ 8) :
    ooe x = y ∨ ooe x + 1 = y
```

**And.** `oe_perfect_power` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:143`

```lean
theorem oe_perfect_power (s : ℕ) :
    ((s ^ 4) ^ 3).sqrt = s ^ 6 ∧ oe (s ^ 4) = s ^ 3
```

**And.** `oe_perfect_power_hidden_odd` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:155`

```lean
theorem oe_perfect_power_hidden_odd {s : ℕ} (hs : s % 2 = 1) :
    (s ^ 4) % 2 = 1 ∧ (((s ^ 4) ^ 3).sqrt) % 2 = 1 ∧
      oe (s ^ 4) % 2 = 1
```

## 35. `C-no-uniform-L-descent` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.61; different result 0.21.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every L≥1, n=2^L-1 realises L odd shortcut steps and C^L(n)=3^L-1>n. No residual n mod 2^L with blocks of length at most L certifies strict descent.

**Declarations.** `shortcutC_no_uniform_L_descent` &mdash; kernel-checked, `Problems/Collatz/Shortcut.lean:110`

> For every ``L ≥ 1``, ``n = 2^L - 1`` realises ``L`` odd steps and expands.

```lean
theorem shortcutC_no_uniform_L_descent {L : ℕ} (hL : 0 < L) :
    2 ^ L - 1 < shortcutCIter L (2 ^ L - 1)
```

**And.** `shortcutC_all_odd_iter` &mdash; kernel-checked, `Problems/Collatz/Shortcut.lean:97`

```lean
theorem shortcutC_all_odd_iter {L k : ℕ} (hk : k ≤ L) :
    shortcutCIter k (2 ^ L - 1) = 3 ^ k * 2 ^ (L - k) - 1
```

## 36. `J-above-anchor-hug-domination` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.3; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** AboveAnchor walk nonnegativity and hug domination: the Section 5 discrete walk layer ported from cycles to open trajectories. If AboveAnchor(n,w) with n >= 2, then every prefix length k <= |w| satisfies 2^k <= 3^{oddCount(w.take k)} (aboveAnchor_prefix_pow_le, AboveAnchorWalk.lean): a never-descending orbit segment keeps the exponent walk u_k >= 0, exactly the CycleMin hypothesis of cycleMin_prefix_pow_le with no cycle, by composing the defect-free upper envelope power_bound_contracts with the anchor hypothesis. Composed with hug minimality (hugOdds_least), every above-anchor prefix dominates the exact hug itinerary in odd count: hugOdds k <= oddCount(w.take k) (aboveAnchor_prefix_odds_ge_hug; full-word form aboveAnchor_odds_ge_hug). Hence a hypothetical descent-free flight carries odd den  *(truncated; read the ledger row)*

**Declarations.** `aboveAnchor_prefix_odds_ge_hug` &mdash; kernel-checked, `Problems/Juggler/AboveAnchorWalk.lean:38`

> **Open trajectories dominate the hug itinerary.** Every prefix of a never-descending trajectory segment carries at least as many odd letters as the exact hug itinerary of the same length. The open-trajectory form of `cycleMin_prefix_odds_ge_hug`: the hug adversary prices not only hypothetical cycles but every hypothetical descent-free flight.

```lean
theorem aboveAnchor_prefix_odds_ge_hug {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : AboveAnchor n w) :
    ∀ k, k ≤ w.length → hugOdds k ≤ oddCount (w.take k)
```

**And.** `aboveAnchor_odds_ge_hug` &mdash; kernel-checked, `Problems/Juggler/AboveAnchorWalk.lean:45`

> Full-itinerary instance: an above-anchor itinerary of length `L` has at least `hugOdds L` odd letters.

```lean
theorem aboveAnchor_odds_ge_hug {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : AboveAnchor n w) :
    hugOdds w.length ≤ oddCount w
```

## 37. `J-cycle-itinerary-length-eleven-or-ge-fourteen` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.3; different result 0.19.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 11 or at least 14. Lengths ≤ 10 are J-small-cycle-census-ten; lengths 12 and 13 are excluded by the same finance comparison (no_cycle_itinerary_length_twelve, no_cycle_itinerary_length_thirteen); length 16 is likewise excluded (no_cycle_itinerary_length_sixteen) but is absorbed into the ≥ 14 residual. Lean theorem cycle_itinerary_length_eleven_or_ge_fourteen. Strengthened by J-cycle-itinerary-length-ge-fourteen, which kills the length-11 disjunct. This is not a leftover-itinerary length-11 census, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declarations.** `cycle_itinerary_length_eleven_or_ge_fourteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:235`

> If a nontrivial cycle exists, its period is `11` or at least `14`: lengths `≤ 10`, `12`, and `13` are impossible.

```lean
theorem cycle_itinerary_length_eleven_or_ge_fourteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 11 ∨ 14 ≤ w.length
```

**And.** `no_cycle_itinerary_length_twelve` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:157`

> No cycle itinerary of length `12`: `o ≥ 8` forces `(65/2)(3^o - 4096) > 12 · 3^o` (margin `6561 > 6494`).

```lean
theorem no_cycle_itinerary_length_twelve {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 12) : ¬CycleItinerary n w
```

**And.** `no_cycle_itinerary_length_thirteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:179`

> No cycle itinerary of length `13`: `o ≥ 9` forces `(65/2)(3^o - 8192) > 13 · 3^o`.

```lean
theorem no_cycle_itinerary_length_thirteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 13) : ¬CycleItinerary n w
```

**And.** `no_cycle_itinerary_length_sixteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:201`

> No cycle itinerary of length `16`: `o ≥ 11` forces `(65/2)(3^o - 65536) > 16 · 3^o`.

```lean
theorem no_cycle_itinerary_length_sixteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 16) : ¬CycleItinerary n w
```

## 38. `J-cycle-itinerary-length-thirty-eight-or-ge-thirty-nine` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.81).*

*Claim broader 0.81; declaration narrower 0.32; different result 0.31.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 38 or at least 39. Lengths ≤ 19 are J-small-cycle-census-nineteen; lengths 20–29 remain excluded at the residual floor 53; lengths 30–37 are excluded by cycle_finance_min_two_hundred_fifty_seven. This row is the leftover before the 61/11 log certificate. Strengthened by J-cycle-itinerary-length-fifty-seven-or-ge-fifty-eight, which kills the length-38 disjunct. Lean theorems cycle_itinerary_length_thirty_eight_or_ge_thirty_nine and no_cycle_itinerary_length_lt_thirty_eight. This is not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declarations.** `cycle_itinerary_length_thirty_eight_or_ge_thirty_nine` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:686`

> If a nontrivial cycle exists, its period is `38` or at least `39`. Weaker leftover: `log 257 > 61/11` also kills `38`.

```lean
theorem cycle_itinerary_length_thirty_eight_or_ge_thirty_nine
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 38 ∨ 39 ≤ w.length
```

**And.** `no_cycle_itinerary_length_lt_thirty_eight` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:662`

> No cycle itinerary of length below `38` except possibly `38`.

```lean
theorem no_cycle_itinerary_length_lt_thirty_eight {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hLt : w.length < 38) : ¬CycleItinerary n w
```

**And.** `cycle_finance_min_two_hundred_fifty_seven` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:550`

> Finance at the rotated odd minimum after the residual floor `257`: `(15677/11)(3^o - 2^L) ≤ L 3^o`, because the minimum is at least `257` and `257 log 257 > 15677/11`.

```lean
theorem cycle_finance_min_two_hundred_fifty_seven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (15677 / 11 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w
```

**And.** `no_cycle_itinerary_length_lt_thirty_ne_nineteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:454`

> No cycle itinerary of length below `30` except possibly `19`.

```lean
theorem no_cycle_itinerary_length_lt_thirty_ne_nineteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hLt : w.length < 30) (hne : w.length ≠ 19) :
    ¬CycleItinerary n w
```

## 39. `J-cycle-ooe-family-chain-bound` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.83).*

*Claim broader 0.83; declaration narrower 0.4; different result 0.24.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Theorem E.4. For X(r)=r^8+8 and odd parameters r>=3, the exact three-step Juggler image is r^9+9r-1. A family transition r->s is equivalent to s^8+9=r^9+9r and forces r=1 modulo48. Between continuing sources, nu2(s-1)=nu2(r-1)-2. For a finite actual J^3 chain of k transitions through odd parameters >=3, k<=(nu2(r0-1)-2)/2 with natural-number subtraction and division; this is max(0,floor((nu2(r0-1)-2)/2)) in integer notation. No valuation drop is assumed after the final destination. ooeFamily_no_infinite_juggler_chain excludes an infinite exact family chain. These are direct actual-Juggler wrappers, not merely an assumed polynomial recurrence. The supplementary 3-adic identity is written and six terminating sample traces are computations. No universal family termination, general esc  *(truncated; read the ledger row)*

**Declarations.** `ooeFamily_juggler_chain_bound` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:270`

```lean
theorem ooeFamily_juggler_chain_bound (r : ℕ → ℕ) (k : ℕ)
    (hr : ∀ i, i ≤ k → 3 ≤ r i)
    (ho : ∀ i, i ≤ k → r i % 2 = 1)
    (hstep : ∀ i, i < k →
      (floorPower^[3]) (ooeFamilySource (r i)) = ooeFamilySource (r (i+1))) :
    k ≤ (padicValNat 2 (r 0 - 1) - 2) / 2
```

**And.** `ooeFamilyReturn` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:98`

```lean
def ooeFamilyReturn (r s : ℕ) : Prop
```

**And.** `ooeFamilyReturn_iff` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:100`

```lean
theorem ooeFamilyReturn_iff {r s : ℕ} (_hr : 3 ≤ r) :
    ooeFamilyExit r = ooeFamilySource s ↔ ooeFamilyReturn r s
```

**And.** `ooeFamilyReturn_mod_fortyeight` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:152`

```lean
theorem ooeFamilyReturn_mod_fortyeight {r s : ℕ}
    (hr : r % 2 = 1) (hs : s % 2 = 1) (h : ooeFamilyReturn r s) :
    r % 48 = 1
```

**And.** `ooeFamilyReturn_valuation_drop` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:210`

```lean
theorem ooeFamilyReturn_valuation_drop {r s : ℕ} (hr : 3 ≤ r) (hs : 3 ≤ s)
    (hrm : r % 16 = 1) (hsm : s % 16 = 1) (h : ooeFamilyReturn r s) :
    padicValNat 2 (s - 1) + 2 = padicValNat 2 (r - 1)
```

**And.** `ooeFamily_no_infinite_juggler_chain` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:282`

```lean
theorem ooeFamily_no_infinite_juggler_chain (r : ℕ → ℕ)
    (hr : ∀ i, 3 ≤ r i) (ho : ∀ i, r i % 2 = 1) :
    ¬ ∀ i, (floorPower^[3]) (ooeFamilySource (r i)) =
      ooeFamilySource (r (i+1))
```

## 40. `J-cycle-upper-charge-monotonicity` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.82).*

*Claim broader 0.82; declaration narrower 0.54; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For fixed positive primitive length L and odd count o, all three nonlinear, finite geometric and closed geometric upper-cell charge bounds decrease strictly with the minimum m>1. If the selected bound at a real cutoff m0>1 is at most logGridSurplus L o, any FullUpperCellChargeBounds certificate at the same counts has m<m0. OrbitUpperChargeCertificate adapters use its own true least period and odd count. The nonlinear bound is at most the finite geometric bound, which is strictly below the closed geometric bound at positive scale. This formalizes symbolic cutoff propagation only; the 520-million numerical interval comparison and UC3 asymptotics remain outside Lean. No descent floor or period bound is changed.

**Declarations.** `nonlinearChargeBound_strictAntiOn_minimum` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:123`

> The nonlinear bound decreases with the minimum when both counts are held fixed.

```lean
theorem nonlinearChargeBound_strictAntiOn_minimum (L : ℕ) [NeZero L] (o : ℕ) :
    StrictAntiOn (fun m => nonlinearChargeBound L (logGridScale (L
```

**And.** `finiteGeometricChargeBound_strictAntiOn_minimum` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:130`

```lean
theorem finiteGeometricChargeBound_strictAntiOn_minimum (L : ℕ) [NeZero L] (o : ℕ) :
    StrictAntiOn (fun m => finiteGeometricChargeBound L (logGridScale (L
```

**And.** `closedGeometricChargeBound_strictAntiOn_minimum` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:137`

```lean
theorem closedGeometricChargeBound_strictAntiOn_minimum (L : ℕ) [NeZero L] (o : ℕ) :
    StrictAntiOn (fun m => closedGeometricChargeBound L (logGridScale (L
```

**And.** `nonlinearChargeBound_le_finiteGeometric` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:99`

> The named finite majorants retain the original nonlinear-to-geometric comparison.

```lean
theorem nonlinearChargeBound_le_finiteGeometric (L : ℕ) [NeZero L]
    {A : ℝ} (hA : 0 < A) :
    nonlinearChargeBound L A ≤ finiteGeometricChargeBound L A
```

**And.** `finiteGeometricChargeBound_lt_closed` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:105`

> The finite majorant is strictly sharper than the closed geometric bound.

```lean
theorem finiteGeometricChargeBound_lt_closed (L : ℕ) [NeZero L]
    {A : ℝ} (hA : 0 < A) :
    finiteGeometricChargeBound L A < closedGeometricChargeBound L A
```

**And.** `nonlinear_cutoff_excludes` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:179`

```lean
theorem nonlinear_cutoff_excludes (h : FullUpperCellChargeBounds (L
```

**And.** `closedGeometric_cutoff_excludes` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:185`

```lean
theorem closedGeometric_cutoff_excludes (h : FullUpperCellChargeBounds (L
```

**And.** `minimum_lt_of_nonlinear_cutoff` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:196`

> A symbolic nonlinear cutoff uses the counts of this same ordinary-orbit certificate.

```lean
theorem minimum_lt_of_nonlinear_cutoff {m M k : ℕ}
    (Q : OrbitUpperChargeCertificate m M k) {m0 : ℝ} (hm0 : 1 < m0)
    (hcut : let : NeZero Q.length
```

**And.** `minimum_lt_of_finiteGeometric_cutoff` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:204`

```lean
theorem minimum_lt_of_finiteGeometric_cutoff {m M k : ℕ}
    (Q : OrbitUpperChargeCertificate m M k) {m0 : ℝ} (hm0 : 1 < m0)
    (hcut : let : NeZero Q.length
```

**And.** `minimum_lt_of_closedGeometric_cutoff` &mdash; kernel-checked, `Problems/Juggler/CubicChargeMonotonicity.lean:212`

```lean
theorem minimum_lt_of_closedGeometric_cutoff {m M k : ℕ}
    (Q : OrbitUpperChargeCertificate m M k) {m0 : ℝ} (hm0 : 1 < m0)
    (hcut : let : NeZero Q.length
```

## 41. `J-fate-pressure-conjecture` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.77).*

*Claim broader 0.77; declaration narrower 0.52; different result 0.12.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Section 9.2's consequences: the pressure hypothesis P_theta(C) and the no-momentum hypothesis M_{theta,q}(C) each imply the conjecture, in the pattern of Corollary 8.4. Bridge: above a certified floor N_0, an odd failure of (y, 2y] is a start of {1, ..., 2y} that stays above N_0 for every number of steps (oddFailures_subset_live), so the live weight of LiveCountWeight, on which Theorem 9.2 (live_count_le_of_pressure) and Proposition 9.3 under no momentum (juggler_count_le_of_noMomentum) are stated, counts the failures. PressureBound N_0 C eps y is P_theta(C) at the scale y with the paper's e^{o(d)} quantified as (log y)^eps: the live pressure of {1, ..., 2y} at the tilt x = p_C/(1 - p_C) and depth d(y) = ceil(C L(y)) is at most 2y a_theta^{d(y)} (log y)^eps. NoMomentumBound N_0 C q  *(truncated; read the ledger row)*

**Declarations.** `pressure_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:219`

> **Theorem 9.2's corollary with nothing else assumed.** The pressure hypothesis `P_θ(C)` at all large scales above a certified floor, with `C ≥ 5` and a loss `ε` such that `27/40 < e < e(C) - ε` for some `e` (a negative `ε` is a stronger hypothesis), gives that every positive integer reaches `1`.

```lean
theorem pressure_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε) (he7 : 27 / 40 < e)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `oddFailures_subset_live` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:40`

> **Failures never enter the floor.** Above a certified floor `N₀`, an odd failure of `(y, 2y]` is a start of `{1, …, 2y}` that is live to every depth.

```lean
theorem oddFailures_subset_live {N₀ : ℕ}
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y d : ℕ) :
    oddFailures y ⊆ (Icc 1 (2 * y)).filter (fun n => liveTo N₀ n d)
```

**And.** `PressureBound` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:56`

> The pressure hypothesis `P_θ(C)` at the scale `y`, with the paper's `e^{o(d)}` quantified as `(log y)^ε`: the live pressure of `{1, …, 2y}` at the tilt `x = p_C/(1-p_C)` and depth `d(y) = ⌈C L(y)⌉` is at most `2y a_θ^{d(y)} (log y)^ε`.

```lean
def PressureBound (N₀ : ℕ) (C ε : ℝ) (y : ℕ) : Prop
```

**And.** `NoMomentumBound` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:63`

> The no-momentum hypothesis `M_{θ,q}(C)` at the scale `y`: on the live weight of `{1, …, 2y}` at the re-centring tilt `x = p_C(1-q)/(q(1-p_C))`, the excess odd shares `(s_x(t) - q)^+` over the depths `t < d(y)` sum to at most `δ d(y)`.

```lean
def NoMomentumBound (N₀ : ℕ) (C q δ : ℝ) (y : ℕ) : Prop
```

**And.** `absorb` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:75`

> **The shared absorption.** A bound `2y e^{-d(y) D} (log y)^ε` on the odd failures of `(y, 2y]` at all large scales, with `d(y) = ⌈C L(y)⌉` and `D ≥ 0`, is below `y (log y)^{-e}` for every `e < C D / log 2 - ε` and all large `y`.

```lean
theorem absorb {N₀ : ℕ} (hN : 2 ≤ N₀) (C D ε e : ℝ) (hC : 0 < C) (hD : 0 ≤ D)
    (he : e < C * D / Real.log 2 - ε)
    (hb : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → ((oddFailures y).card : ℝ) ≤
      2 * y * Real.exp (-(depth C N₀ y * D)) * Real.log y ^ ε) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)
```

**And.** `oddFailures_le_of_pressure` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:162`

> **Theorem 9.2 absorbed.** Under `P_θ(C)` at all large scales with the loss `ε`, the odd failures in `(y, 2y]` number at most `y (log y)^{-e}` for every `e < e(C) - ε` and all large `y`.

```lean
theorem oddFailures_le_of_pressure {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)
```

**And.** `pressure_conj_of_contagion` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:203`

> **Theorem 9.2's corollary, with the contagion bound as a hypothesis.**

```lean
theorem pressure_conj_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `oddFailures_le_of_noMomentum` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:231`

> **Proposition 9.3 absorbed.** Under `M_{θ,q}(C)` at all large scales with the momentum `δ`, the odd failures in `(y, 2y]` number at most `y (log y)^{-e}` for every `0 ≤ e < C (D(p_C ‖ q) - c_x δ) / log 2` and all large `y`.

```lean
theorem oddFailures_le_of_noMomentum {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he0 : 0 ≤ e)
    (he : e < momentumExponent C q δ)
    (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)
```

**And.** `noMomentum_conj_of_contagion` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:307`

> **Proposition 9.3's corollary, with the contagion bound as a hypothesis.**

```lean
theorem noMomentum_conj_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he : e < momentumExponent C q δ)
    (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `noMomentum_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:324`

> **Proposition 9.3's corollary with nothing else assumed.** The no-momentum hypothesis `M_{θ,q}(C)` at all large scales above a certified floor, at the re-centring tilt, with `C ≥ 5`, `0 < q < p_C` and a momentum `δ` such that `27/40 < e < C (D(p_C ‖ q) - c_x δ) / log 2` for some `e`, gives that every positive integer reaches `1`.

```lean
theorem noMomentum_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q δ e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C) (he : e < momentumExponent C q δ)
    (he7 : 27 / 40 < e) (hM : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → NoMomentumBound N₀ C q δ y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 42. `BTN-sdsh-truncated-mod` &mdash; covers 0.2

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.29; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If 3^L divides s-t and |w|≤L, then the lsd streams of F_{λ,U} from s and t agree on w. A remaining-horizon L controller therefore merges (s,q_L) and (t,q_L) whenever that congruence holds.

**Declarations.** `truncated_3adic_agree` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitShortHorizon.lean:28`

> A short horizon cannot see a deep congruence: if `3^L | s - t`, the signed traces from `s` and `t` agree on every word of length at most `L`.

```lean
theorem truncated_3adic_agree {gain s t : ℤ} {L : ℕ} {w : List ℤ}
    (hdvd : (3 : ℤ) ^ L ∣ s - t) (hw : w.length ≤ L) :
    signedTrace gain s w = signedTrace gain t w
```

**And.** `truncated_3adic_equiv` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitShortHorizon.lean:71`

```lean
theorem truncated_3adic_equiv {gain s t : ℤ} {L : ℕ} {w : List ℤ}
    (hdvd : (3 : ℤ) ^ L ∣ s - t) (hw : w.length ≤ L) :
    signedTrace gain s w = signedTrace gain t w
```

**And.** `short_horizon_equiv` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitShortHorizon.lean:76`

```lean
theorem short_horizon_equiv {gain s t : ℤ} {L : ℕ} {w : List ℤ}
    (hdvd : (3 : ℤ) ^ L ∣ s - t) (hw : w.length ≤ L) :
    signedTrace gain s w = signedTrace gain t w
```

## 43. `J-gapped-cycle-itinerary-eoe` &mdash; covers 0.21

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.36; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every n ≥ 2, a ≥ 2, and b ≥ 3, the gapped three-even leftover O^a E O^b EOE is not a Juggler cycle itinerary. The same rotation classes apply: first-E CycleMin at k=0; bootstrap O^b EOE O^a E at k=a+1 (last-gap ≥ 2, with n=3 and b=3 failing after OOOE at 6); start OE at k=a+b+2; every other rotation ends odd. Lean theorem no_cycle_itinerary_gapped_three_even_eoe. This upgrades the CycleMin theorem to CycleItinerary; it is not first-E transport at a non-minimum start, not a bunched-tail theorem, not a length-8 or length-9 census, and not a halt theorem.

**Declarations.** `no_cycle_itinerary_gapped_three_even_eoe` &mdash; kernel-checked, `Problems/Juggler/LeftoverFamilies.lean:2950`

> The gapped three-even leftover `gappedThreeEvenEOE a b` is not a Juggler cycle itinerary at any `n >= 2`, for `a >= 2` and `b >= 3`.

```lean
theorem no_cycle_itinerary_gapped_three_even_eoe {n a b : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (hb : 3 ≤ b) :
    ¬CycleItinerary n (gappedThreeEvenEOE a b)
```

**And.** `gapped_eoe_rotate_succ_a` &mdash; kernel-checked, `Problems/Juggler/LeftoverFamilies.lean:2802`

```lean
theorem gapped_eoe_rotate_succ_a {a b : ℕ} :
    rotateItinerary (gappedThreeEvenEOE a b) (a + 1) = gappedEOEBootstrap a b
```

**And.** `no_cycleMin_gapped_eoe_bootstrap` &mdash; kernel-checked, `Problems/Juggler/LeftoverFamilies.lean:2897`

```lean
theorem no_cycleMin_gapped_eoe_bootstrap {n a b : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (hb : 3 ≤ b)
    (h : CycleMin n (gappedEOEBootstrap a b)) : False
```

**And.** `no_follows_three_eoe_bootstrap` &mdash; kernel-checked, `Problems/Juggler/LeftoverFamilies.lean:2845`

```lean
theorem no_follows_three_eoe_bootstrap {b : ℕ} (hb : 3 ≤ b) :
    ¬follows 3 (gappedEOEBootstrap 2 b)
```

**And.** `cycleMin_rotate_start_OE` &mdash; kernel-checked, `Problems/Juggler/LeftoverFamilies.lean:2540`

```lean
theorem cycleMin_rotate_start_OE {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (hk : k + 1 < w.length)
    (ho : w[k] = Branch.odd) (he : w[k + 1] = Branch.even)
    (h : CycleMin n (rotateItinerary w k)) : False
```

**And.** `cycleMin_of_rotate_ends_odd` &mdash; kernel-checked, `Problems/Juggler/LeftoverFamilies.lean:2525`

```lean
theorem cycleMin_of_rotate_ends_odd {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k ≤ w.length)
    (hodd : w[k - 1]'(Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt hk0) hk) =
      Branch.odd)
    (h : CycleMin n (rotateItinerary w k)) : False
```

**And.** `gappedThreeEvenEOE_pred_odd` &mdash; kernel-checked, `Problems/Juggler/LeftoverFamilies.lean:2750`

```lean
theorem gappedThreeEvenEOE_pred_odd {a b k : ℕ}
    (hk0 : 0 < k) (hk : k < a + b + 4) (hne1 : k ≠ a + 1)
    (hne2 : k ≠ a + b + 2) :
    (gappedThreeEvenEOE a b)[k - 1]'(by
```

## 44. `J-mixed-oe-eighth` &mdash; covers 0.21

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.49; different result 0.42.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If x is odd and T(x) is even, then T^2(x) < n^2 if and only if x^3 < n^8. This is the mixed odd-cube / even-square cell. It is strictly sharper than composing a cube-band bound x < n^3 into T^2(x)^4 < n^9. An eighth-cell even lift that returns even is FiniteProgress; on MinimalNonTerm that return is odd. This is not a claim that every leftover landing stays below n^8, not a defect restriction, and not a halt theorem.

**Declarations.** `odd_even_eighth_lt_sq` &mdash; kernel-checked, `Problems/Juggler/CubeCorridor.lean:131`

> Mixed OE cell: an odd cube step followed by an even square step is the eighth-power comparison. This is strictly sharper than composing `x < n^3` into `T^2(x) < n^{9/4}`. Not a one-step envelope and not a defect restriction.

```lean
theorem odd_even_eighth_lt_sq {x n : ℕ}
    (hodd : x % 2 = 1) (he : floorPower x % 2 = 0) :
    floorPower (floorPower x) < n ^ 2 ↔ x ^ 3 < n ^ 8
```

**And.** `cube_lift_even_reset_fourth` &mdash; kernel-checked, `Problems/Juggler/CubeCorridor.lean:111`

> Scale form of the even return: `T^2(x)^4 < n^9`, i.e. below `n^{9/4}`.

```lean
theorem cube_lift_even_reset_fourth {x n : ℕ}
    (h : CubeOddLanding n x) (he : floorPower x % 2 = 0) :
    floorPower (floorPower x) ^ 4 < n ^ 9
```

## 45. `J-fate-contagion-conditional` &mdash; covers 0.22

*Reads as: the claim asserts more than the declarations state (0.81).*

*Claim broader 0.81; declaration narrower 0.43; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Theorem 5.3 (contagion) given the production inequality (5.2), for every 0 < λ ≤ 0.49. Data: productionRate/productionCoeff are the eight productions (e_i, c_i) = (1/2, 1), (3/8, 1/9), (3/4, 2/9), (9/32, 1/27), (27/128, 1/81), (81/512, 1/243), (243/2048, 1/729), (729/8192, 1/2187); zeta λ = Σ c_i e_i^λ − 1 is antitone in λ (zeta_antitone) and zeta (49/100) > 0 (zeta_pos_49): each e_i^{49/100} is bounded below by a five-digit rational r_i through r_i^100 ≤ e_i^49 in exact integer arithmetic (le_rpow_div_of_pow_le), and Σ c_i r_i − 1 = 0.00168 > 0 (the exact value of ζ(0.49) is 0.001683; the paper's root is λ** = 0.4926). gA A t = halfLogMass A ⌊e^t⌋₊ is the paper's g_A(t) (the integers in (√x, x] are those in (⌊√⌊x⌋⌋, ⌊x⌋]); gA_seed is Lemma 5.2 in the form g_A(t) ≥ c_A for t ≥ 4 lo  *(truncated; read the ledger row)*

**Declarations.** `contagion_of_production_inequality` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:253`

> **Paper C Theorem 5.3, given the production inequality (5.2).** Let `A` be backward-closed with a positive member, `0 < λ ≤ 0.49`, and suppose `g_A(t) ≥ Σ_i (c_i - η_i(t)) g_A(e_i t) - η₀(t)` for all `t ≥ t₀`, with errors `η_i(t), η₀(t) ≥ 0` that tend to `0`. Then `g_A(t) ≥ K t^λ` for all large `t`, some `K > 0`. The proof is the paper's: the seed of Lemma 5.2 on `[e_min t₁, t₁]`, the recursion lemma with `ζ(λ) ≥ ζ(0.49) > 0`, and `t₁` large enough that the errors are below `ζ/24` and `(2ζ/3) c_A`.

```lean
theorem contagion_of_production_inequality {A : ℕ → Prop} (hA : BackwardClosed A)
    {a : ℕ} (ha : 1 ≤ a) (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 49 / 100)
    (η : Fin 8 → ℝ → ℝ) (η₀ : ℝ → ℝ) (t₀ : ℝ)
    (hη_lo : ∀ t, t₀ ≤ t → ∀ i, 0 ≤ η i t)
    (hvanish : ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → (∀ i, η i t ≤ ε) ∧ η₀ t ≤ ε)
    (hrec : ∀ t, t₀ ≤ t →
      ∑ i, (productionCoeff i - η i t) * gA A (productionRate i * t) - η₀ t ≤ gA A t) :
    ∃ K : ℝ, 0 < K ∧ ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t, t₁ ≤ t → K * t ^ lam ≤ gA A t
```

**And.** `productionRate_ge` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:77`

```lean
theorem productionRate_ge (i : Fin 8) : 729 / 8192 ≤ productionRate i
```

**And.** `productionRate_le` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:80`

```lean
theorem productionRate_le (i : Fin 8) : productionRate i ≤ 3 / 4
```

**And.** `zeta_antitone` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:134`

> `ζ` is antitone: every `e_i ≤ 1`.

```lean
theorem zeta_antitone {lam lam' : ℝ} (h : lam ≤ lam') : zeta lam' ≤ zeta lam
```

**And.** `zeta_pos_49` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:153`

> `ζ(0.49) > 0`: the eight production terms at `λ = 49/100` sum to more than `1`, by exact rational lower bounds (`e_i^{49} ≥ r_i^{100}`). The paper's root is `λ** = 0.4926…`.

```lean
theorem zeta_pos_49 : 0 < zeta (49 / 100)
```

**And.** `le_rpow_div_of_pow_le` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:143`

> A rational lower bound for a rational power: `r ≤ x^{p/q}` from `r^q ≤ x^p`.

```lean
theorem le_rpow_div_of_pow_le {x r : ℝ} (hx : 0 < x) {p q : ℕ} (hq : 0 < q)
    (h : r ^ q ≤ x ^ p) : r ≤ x ^ ((p : ℝ) / q)
```

**And.** `gA_seed` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:218`

> Lemma 5.2 in the form `g_A(t) ≥ c_A` for `t ≥ 4 log(m+1)`.

```lean
theorem gA_seed {A : ℕ → Prop} (hA : BackwardClosed A) {m : ℕ} (hm : 3 ≤ m) (hmA : A m)
    {t : ℝ} (ht : 4 * Real.log ((m : ℝ) + 1) ≤ t) : seedConst m ≤ gA A t
```

**And.** `logMass_ge_gA` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:232`

> `g_A(log x)` is at most the full log-mass up to `x`.

```lean
theorem logMass_ge_gA (A : ℕ → Prop) {x : ℕ} (hx : 1 ≤ x) : gA A (Real.log x) ≤ logMass A x
```

**And.** `logMass_contagion_of_production` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:316`

> Theorem 5.3 given (5.2), in the form Theorem 7.2 consumes: `Σ_{n ≤ x, n ∈ A} 1/n ≥ K (log x)^λ` for all large `x`.

```lean
theorem logMass_contagion_of_production {A : ℕ → Prop} (hA : BackwardClosed A)
    {a : ℕ} (ha : 1 ≤ a) (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 49 / 100)
    (η : Fin 8 → ℝ → ℝ) (η₀ : ℝ → ℝ) (t₀ : ℝ)
    (hη_lo : ∀ t, t₀ ≤ t → ∀ i, 0 ≤ η i t)
    (hvanish : ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → (∀ i, η i t ≤ ε) ∧ η₀ t ≤ ε)
    (hrec : ∀ t, t₀ ≤ t →
      ∑ i, (productionCoeff i - η i t) * gA A (productionRate i * t) - η₀ t ≤ gA A t) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → K * Real.log x ^ lam ≤ logMass A x
```

**And.** `conjecture_of_cylinder_bound_of_production` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:370`

> **Corollary 8.4 with Theorem 5.3 discharged through the production inequality.** If the cylinder hypothesis `H(C, A)` holds at all large scales with `C ≥ 5`, `A > C + e(C)` and `1 - λ < e(C)` for some `0 < λ ≤ 0.49`, and the failure set (if nonempty) satisfies the production inequality (5.2) with vanishing errors, then every positive integer reaches `1`.

```lean
theorem conjecture_of_cylinder_bound_of_production {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C A : ℝ) (hC : 5 ≤ C)
    (hA : C + chernoffExponent C < A)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ C A y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 49 / 100) (hlamC : 1 - lam < chernoffExponent C)
    (η : Fin 8 → ℝ → ℝ) (η₀ : ℝ → ℝ) (t₀ : ℝ)
    (hη_lo : ∀ t, t₀ ≤ t → ∀ i, 0 ≤ η i t)
    (hvanish : ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → (∀ i, η i t ≤ ε) ∧ η₀ t ≤ ε)
    (hrec : ∀ t, t₀ ≤ t →
      ∑ i, (productionCoeff i - η i t) * gA (fun n => ¬ReachesOne n) (productionRate i * t) -
        η₀ t ≤ gA (fun n => ¬ReachesOne n) t) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 46. `J-fate-one-sided-atoms` &mdash; covers 0.22

*Reads as: the claim asserts more than the declarations state (0.67).*

*Claim broader 0.67; declaration narrower 0.65; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Section 10(d), first paragraph: Theorem 9.1 with exceptional atoms, on the exponential-moment proof. OneSidedShareExc y L q err exc d: at each depth 1 <= t < d there is a set E of words of total cylinder mass at most exc such that every L-bad word outside E sends at most q #[w] + err of its members to an odd next letter; the original hypothesis is the case E empty (oneSidedShareExc_of_share). An exceptional bad atom sends at most its whole mass to its odd child, which costs (x - a_q) #[w] x^{o(w)} = (x-1)(1-q) #[w] x^{o(w)} in the tilted mass, so badMass(t+1) <= a_q badMass(t) + (x-1)(err (2x)^t + (1-q) exc x^t) (badMass_succ_le_exc), unrolled to x a_q^t N + (x-1) t (err (2x)^t + (1-q) exc x^t) (badMass_le_exc), and with Lemma 8.1 and the Markov tilt the odd failures of (y, 2y] num  *(truncated; read the ledger row)*

**Declarations.** `exc_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:619`

> **Section 10(d)'s corollary with nothing else assumed.** The one-sided hypothesis with exceptional atoms of mass `y (log y)^{-B}` at all large scales above a certified floor, with `C ≥ 5`, `0 < q < p_C`, `A > C(1 + log₂ x) + 1 + e`, `B > C log₂ x + 1 + e` and `27/40 < e < e_{C,q}`, gives that every positive integer reaches `1`.

```lean
theorem exc_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A B e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A)
    (hB : C * Real.logb 2 (tilt (pC C) q) + 1 + e < B) (he : e < oneSidedExponent C q)
    (he7 : 27 / 40 < e)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBoundExc N₀ C q A B y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `OneSidedShareExc` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:42`

> The one-sided hypothesis with exceptional atoms: at each depth `1 ≤ t < d` there is a set `E` of words of total cylinder mass at most `exc` such that every `L`-bad word outside `E` sends at most the share `q` of its members, plus `err`, to an odd next letter.

```lean
def OneSidedShareExc (y : ℕ) (L q err exc : ℝ) (d : ℕ) : Prop
```

**And.** `oneSidedShareExc_of_share` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:49`

> The original hypothesis is the case of no exceptional atoms.

```lean
theorem oneSidedShareExc_of_share {y : ℕ} {L q err exc : ℝ} {d : ℕ}
    (h : OneSidedShare y L q err d) (hexc : 0 ≤ exc) : OneSidedShareExc y L q err exc d
```

**And.** `badMass_succ_le_exc` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:67`

> **One depth, with exceptional atoms.** Under the hypothesis at depth `1 ≤ t < d`, `badMass (t+1) ≤ a_q · badMass t + (x - 1) (err (2x)^t + (1 - q) exc x^t)`.

```lean
theorem badMass_succ_le_exc {y : ℕ} {L x q err exc : ℝ} {d t : ℕ} (hx : 1 ≤ x)
    (hq1 : q ≤ 1) (herr : 0 ≤ err) (hH : OneSidedShareExc y L q err exc d) (ht1 : 1 ≤ t)
    (htd : t < d) :
    badMass y L x (t + 1)
      ≤ (1 + (x - 1) * q) * badMass y L x t
        + (x - 1) * (err * (2 * x) ^ t + (1 - q) * exc * x ^ t)
```

**And.** `badMass_le_exc` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:175`

> **Unrolled.** For `t + 1 ≤ d`, `badMass (t+1) ≤ x a_q^t N + (x-1) t (err (2x)^t + (1-q) exc x^t)`, using `a_q ≤ 2x` and `a_q ≤ x`.

```lean
theorem badMass_le_exc {y : ℕ} {L x q err exc : ℝ} {d : ℕ} (hx : 1 ≤ x) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (herr : 0 ≤ err) (hexc : 0 ≤ exc) (hH : OneSidedShareExc y L q err exc d) :
    ∀ t, t + 1 ≤ d → badMass y L x (t + 1)
      ≤ x * (1 + (x - 1) * q) ^ t * (cylinder y 0 []).card
        + (x - 1) * t * (err * (2 * x) ^ t + (1 - q) * exc * x ^ t)
```

**And.** `one_sided_bound_exc` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:219`

> **Theorem 9.1 with exceptional atoms, exact.**

```lean
theorem one_sided_bound_exc {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y)
    {C x q err exc : ℝ} (hC : 0 < C) (hx : 1 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (herr : 0 ≤ err) (hexc : 0 ≤ exc) {d : ℕ} (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d)
    (hH : OneSidedShareExc y (scaleL N₀ y) q err exc d) :
    ((oddFailures y).card : ℝ) ≤
      (x * (1 + (x - 1) * q) ^ (d - 1) * (cylinder y 0 []).card
        + (x - 1) * ((d : ℝ) - 1) * (err * (2 * x) ^ (d - 1) + (1 - q) * exc * x ^ (d - 1)))
        / x ^ (pC C * d)
```

**And.** `main_term_eq` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:238`

> The main term at the re-centring tilt, split off: `(x a^{d-1} N + R) / x^{p d} = (x/a) N e^{-d D(p ‖ q)} + R / x^{p d}`.

```lean
theorem main_term_eq {p q : ℝ} (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) {d : ℕ}
    (hd1 : 1 ≤ d) (N R : ℝ) :
    (tilt p q * (1 + (tilt p q - 1) * q) ^ (d - 1) * N + R) / tilt p q ^ (p * d)
      = tilt p q / (1 + (tilt p q - 1) * q) * N * Real.exp (-(d * klDiv p q))
        + R / tilt p q ^ (p * d)
```

**And.** `one_sided_bound_kl_exc` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:256`

> **Theorem 9.1 with exceptional atoms at the re-centring tilt.**

```lean
theorem one_sided_bound_kl_exc {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {y : ℕ} (hy : 1 ≤ y)
    {C q err exc : ℝ} (hC : 0 < C) (hq0 : 0 < q) (hqp : q < pC C) (hp1 : pC C < 1)
    (herr : 0 ≤ err) (hexc : 0 ≤ exc) {d : ℕ} (hd1 : 1 ≤ d) (hd : C * scaleL N₀ y ≤ d)
    (hH : OneSidedShareExc y (scaleL N₀ y) q err exc d) :
    ((oddFailures y).card : ℝ) ≤
      tilt (pC C) q / (1 + (tilt (pC C) q - 1) * q) * (cylinder y 0 []).card
          * Real.exp (-(d * klDiv (pC C) q))
        + (tilt (pC C) q - 1) * ((d : ℝ) - 1)
          * (err * (2 * tilt (pC C) q) ^ (d - 1) + (1 - q) * exc * tilt (pC C) q ^ (d - 1))
          / tilt (pC C) q ^ (pC C * d)
```

**And.** `tail_le` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:296`

> **One tail term.** At a scale `y ≥ max(N₀, 2)`, with `d = ⌈C L(y)⌉` and `z ≥ 1`, `(d-1) z^{d-1} · y (log y)^{-A} ≤ K_d M_z · y (log y)^{C log₂ z + 1 - A}`.

```lean
theorem tail_le {N₀ y : ℕ} (hN : 2 ≤ N₀) (hyN : N₀ ≤ y) (hy2 : 2 ≤ y) {C z A : ℝ}
    (hC : 0 < C) (hz : 1 ≤ z) :
    ((depth C N₀ y : ℝ) - 1) * z ^ (depth C N₀ y - 1) * ((y : ℝ) / Real.log y ^ A)
      ≤ 2 * C / (Real.log 2 * Real.log N₀) * (2 / Real.log N₀) ^ (C * Real.logb 2 z)
        * y * Real.log y ^ (C * Real.logb 2 z + 1 - A)
```

**And.** `oddFailures_le_of_exc` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:378`

> **The absorption with exceptional atoms.** Under `H_q(C, A)` with exceptional atoms of mass `y (log y)^{-B}` at all large scales, with `q < p_C`, `A > C(1 + log₂ x) + 1 + e`, `B > C log₂ x + 1 + e` and `e < e_{C,q}`, the odd failures in `(y, 2y]` number at most `y (log y)^{-e}` for all large `y`.

```lean
theorem oddFailures_le_of_exc {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A B e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A)
    (hB : C * Real.logb 2 (tilt (pC C) q) + 1 + e < B) (he : e < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBoundExc N₀ C q A B y) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y →
      ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)
```

**And.** `exc_conj_of_contagion` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:601`

> **Section 10(d)'s corollary, with the contagion bound as a hypothesis.**

```lean
theorem exc_conj_of_contagion {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A B e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A)
    (hB : C * Real.logb 2 (tilt (pC C) q) + 1 + e < B) (he : e < oneSidedExponent C q)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBoundExc N₀ C q A B y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) →
      ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 47. `J-cycle-branch-offset-obstruction` &mdash; covers 0.23

*Reads as: the claim asserts more than the declarations state (0.76).*

*Claim broader 0.76; declaration narrower 0.5; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Let G(1)=1, G(x)=J(x)-1 for odd x>=3, and G(x)=J(x) for even x. Exact integer square-cell inequalities certify the primitive cycle 13,45,300,17,69,572,23,109,1136,33,188,13, with (L,o,e)=(11,7,4) and maximum 1136<13^3. It is also an R_11 cycle. For any two odd sources >=3, or two positive even sources, G(x')-G(x)=J(x')-J(x). All same-branch higher finite differences on sources >1 therefore agree as well. Even strict nearest-even smooth-gap tests hold for same-parity successor pairs. Hence correct source parity, global rank order and exact within-branch image differences restricted to sources >1 alone cannot exclude cycles: an additive branch constant is lost. Differences involving 1 are excluded because they could anchor the odd-branch constant. This is a cycle of a different map, not a Ju  *(truncated; read the ledger row)*

**Declarations.** `branchOffset_same_branch_difference` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:326`

> All same-branch differences above one coincide, as integer differences.

```lean
theorem branchOffset_same_branch_difference {x y : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hp : x % 2 = y % 2) :
    (branchOffset y : ℤ) - branchOffset x = (floorPower y : ℤ) - floorPower x
```

**And.** `branchOffset_same_branch_smooth_gap` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:368`

> The strict smooth gap test survives the constant shift on a whole branch.

```lean
theorem branchOffset_same_branch_smooth_gap {x y : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hp : x % 2 = y % 2) :
    |((branchOffset y : ℝ) - branchOffset x) -
      (cubicBranchValue y - cubicBranchValue x)| < 1
```

**And.** `branchOffset_nearest_even_gap` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:393`

> Whenever the shifted successors have equal parity, their gap passes the unique-even test.

```lean
theorem branchOffset_nearest_even_gap {x y : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hp : x % 2 = y % 2)
    (hs : branchOffset x % 2 = branchOffset y % 2) :
    ∀ k : ℤ, k % 2 = 0 →
      |(k : ℝ) - (cubicBranchValue y - cubicBranchValue x)| < 1 →
      k = (branchOffset y : ℤ) - branchOffset x
```

**And.** `branchOffsetCycle_primitive` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:439`

```lean
theorem branchOffsetCycle_primitive :
    ∀ i j : Fin 11, branchOffset^[i.val] 13 = branchOffset^[j.val] 13 → i = j
```

**And.** `branchOffsetCycle_cells` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:414`

```lean
theorem branchOffsetCycle_cells :
    branchOffsetCycle.map floorPower = [46,301,17,70,573,23,110,1137,33,189,13]
```

**And.** `branchOffset` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:322`

> The shifted odd branch preserves the fixed point at one.

```lean
def branchOffset (x : ℕ) : ℕ
```

**And.** `branchOffsetCycle` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:406`

> The literal shifted cycle, listed before its return.

```lean
def branchOffsetCycle : List ℕ
```

**And.** `branchOffsetCycle_edges` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:408`

```lean
theorem branchOffsetCycle_edges :
    branchOffsetCycle.map branchOffset = branchOffsetCycle.tail ++ [13]
```

**And.** `branchOffsetCycle_distinct` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:412`

```lean
theorem branchOffsetCycle_distinct : branchOffsetCycle.Nodup
```

**And.** `branchOffsetCycle_counts` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:427`

```lean
theorem branchOffsetCycle_counts :
    branchOffsetCycle.length = 11 ∧
    (branchOffsetCycle.filter (fun x => x % 2 = 1)).length = 7 ∧
    (branchOffsetCycle.filter (fun x => x % 2 = 0)).length = 4 ∧ 1136 < 13 ^ 3
```

**And.** `branchOffsetCycle_bounds` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:422`

```lean
theorem branchOffsetCycle_bounds :
    ∀ x ∈ branchOffsetCycle, 13 ≤ x ∧ x ≤ 1136 ∧ cubicParityDomain 11 x
```

**And.** `branchOffsetCycle_rounding` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:418`

```lean
theorem branchOffsetCycle_rounding :
    branchOffsetCycle.map (cubicRounding 11) = branchOffsetCycle.tail ++ [13]
```

**And.** `branchOffsetCycle_iterate` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:433`

```lean
theorem branchOffsetCycle_iterate : branchOffset^[11] 13 = 13
```

**And.** `branchOffsetCycle_iterates` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:435`

```lean
theorem branchOffsetCycle_iterates :
    (List.range 11).map (fun k => branchOffset^[k] 13) = branchOffsetCycle
```

**And.** `branchOffsetCycle_rank_rotation` &mdash; kernel-checked, `Problems/Juggler/CubicRounding.lean:443`

```lean
theorem branchOffsetCycle_rank_rotation :
    [13,17,23,33,45,69,109,188,300,572,1136].map branchOffset =
    [45,69,109,188,300,572,1136,13,17,23,33]
```

## 48. `J-cycle-upper-charge-least-period` &mdash; covers 0.23

*Reads as: the claim asserts more than the declarations state (0.81).*

*Claim broader 0.81; declaration narrower 0.47; different result 0.16.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** An actual positive closed orbit with minimum m>1, attained maximum M<m^3 and all states in [m,M] supplies an OrbitUpperChargeCertificate extending one complete PeriodicOrbitModel. The same sorted states and successor permutation retain full coverage, extrema, the exact odd count, parity and threshold cuts, rank rotation, coprimality, true least period, RealizedGridBounds and FullUpperCellChargeBounds. The latter retains the stronger finite nonlinear charge before its finite geometric and closed scalar relaxations. An existing model can be strengthened with equality of the projected base, so terminal and charge data share one witness. The CycleMin adapter handles repeated itineraries; older existential interfaces are unchanged projections. No numerical cutoff, asymptotic estimate or cycle e  *(truncated; read the ledger row)*

**Declarations.** `periodicOrbit_upper_charge` &mdash; kernel-checked, `Problems/Juggler/CubicOrbitCharge.lean:109`

> An ordinary finite actual orbit yields the complete grid and charge at its true least period.

```lean
theorem periodicOrbit_upper_charge {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m) (hm : 1 < m) (hM : M < m ^ 3)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    ∃ (L : ℕ) (hL : 0 < L) (c : Fin L → ℕ),
      let : NeZero L
```

**And.** `cycleMin_upper_charge` &mdash; kernel-checked, `Problems/Juggler/CubicOrbitCharge.lean:139`

> A minimum-based closed itinerary is normalized to its least period before applying the charge.

```lean
theorem cycleMin_upper_charge {m M : ℕ} {w : List Branch}
    (hcycle : CycleMin m w) (hm : 1 < m) (hM : M < m ^ 3)
    (hbound : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    ∃ (L : ℕ) (hL : 0 < L) (c : Fin L → ℕ),
      let : NeZero L
```

**And.** `OrbitUpperChargeCertificate` &mdash; kernel-checked, `Problems/Juggler/CubicOrbitCharge.lean:8`

> The same complete ordinary-orbit model, retaining its rotation and all charge bounds.

```lean
structure OrbitUpperChargeCertificate (m M k : ℕ)
    extends ReturnSeams.PeriodicOrbitModel m M k where
  oddCount : ℕ
  oddCount_le : oddCount ≤ length
  oddCount_card : (Finset.univ.filter (fun i => state i % 2 = 1)).card = oddCount
  odd_cut : ∀ i, state i % 2 = 1 ↔ i.val < oddCount
  threshold_cut : ∀ i, state i < m ^ 2 ↔ i.val < oddCount
  rotation : ∀ i, (next i).val = (i.val + (length - oddCount)) % length
  coprime : Nat.Coprime length oddCount
  period_eq : length = Function.minimalPeriod floorPower m
  band : ∀ i, InCubicBand m (state i)
  grid :
```

**And.** `orbitModel_upper_charge` &mdash; kernel-checked, `Problems/Juggler/CubicOrbitCharge.lean:38`

> Strengthen an existing model without choosing a second sorted state set or permutation.

```lean
theorem orbitModel_upper_charge {m M k : ℕ}
    (S : ReturnSeams.PeriodicOrbitModel m M k) (hm : 1 < m) (hM : M < m ^ 3) :
    ∃ Q : OrbitUpperChargeCertificate m M k, Q.toPeriodicOrbitModel = S
```

**And.** `periodicOrbit_upper_charge_certificate` &mdash; kernel-checked, `Problems/Juggler/CubicOrbitCharge.lean:99`

> One ordinary periodic orbit produces one complete rotation-and-charge certificate.

```lean
theorem periodicOrbit_upper_charge_certificate {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m) (hm : 1 < m) (hM : M < m ^ 3)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    Nonempty (OrbitUpperChargeCertificate m M k)
```

**And.** `cycleMin_upper_charge_certificate` &mdash; kernel-checked, `Problems/Juggler/CubicOrbitCharge.lean:128`

> A minimum-based itinerary retains the same full certificate at its true least period.

```lean
theorem cycleMin_upper_charge_certificate {m M : ℕ} {w : List Branch}
    (hcycle : CycleMin m w) (hm : 1 < m) (hM : M < m ^ 3)
    (hbound : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    Nonempty (OrbitUpperChargeCertificate m M w.length)
```

## 49. `J-fate-certified-thirty` &mdash; covers 0.24

*Reads as: the claim asserts more than the declarations state (0.86).*

*Claim broader 0.86; declaration narrower 0.42; different result 0.25.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** A certified instance of the side condition of Paper C's unconditional criteria, at C = 30, with no audit script in the chain. Device: a logarithm is certified by an integer power comparison. If E <= e and x^n <= E^m then n log x <= m (log_le_of_pow_le); if e <= E and E^m <= x^n then m <= n log x (le_log_of_pow_le); and the base-two pair logb_two_le, le_logb_two. With Mathlib's Real.exp_one_gt_d9 and exp_one_lt_d9 pinning 2.718 <= e <= 2.719 (e_ge, e_le), six comparisons closed by norm_num give: log 2 <= 7/10 (from 2^10 <= 2.718^7), 2/3 <= log 2 (2.719^2 <= 2^3), 84/53 <= log_2 3 (2^84 <= 3^53), log_2 3 <= 149/94 (3^94 <= 2^149), 19/100 <= log(3049/2500) (2.719^19 <= (3049/2500)^100) and log(39/50) >= -1/4 ((50/39)^4 <= 2.718). Hence p_30 = pC 30 lies in [3049/5000, 61/100] (pC_thirty_ge, p  *(truncated; read the ledger row)*

**Declarations.** `chernoffExponent_thirty_gt` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:261`

> **The certified instance.** `e(30) > 39/50`, with no audit script in the chain; in particular `e(30) > 39/50`, comfortably past the `27/40` side condition of every unconditional criterion.

```lean
theorem chernoffExponent_thirty_gt : 39 / 50 < chernoffExponent 30
```

**And.** `e_ge` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:60`

```lean
theorem e_ge : (2718 : ℝ) / 1000 ≤ Real.exp 1
```

**And.** `e_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:63`

```lean
theorem e_le : Real.exp 1 ≤ (2719 : ℝ) / 1000
```

**And.** `log_le_of_pow_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:68`

> **An upper bound on a logarithm, certified by integers.** If `E ≤ e` and `x^n ≤ E^m` then `n log x ≤ m`.

```lean
theorem log_le_of_pow_le {x E : ℝ} (hx : 0 < x) (hE : 0 < E) (hEe : E ≤ Real.exp 1)
    {m n : ℕ} (h : x ^ n ≤ E ^ m) : (n : ℝ) * Real.log x ≤ m
```

**And.** `le_log_of_pow_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:79`

> **A lower bound on a logarithm, certified by integers.** If `e ≤ E` and `E^m ≤ x^n` then `m ≤ n log x`.

```lean
theorem le_log_of_pow_le {x E : ℝ} (hEe : Real.exp 1 ≤ E)
    {m n : ℕ} (h : E ^ m ≤ x ^ n) : (m : ℝ) ≤ n * Real.log x
```

**And.** `logb_two_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:90`

> The same for a base-two logarithm: `x^n ≤ 2^m` gives `log₂ x ≤ m/n`.

```lean
theorem logb_two_le {x : ℝ} (hx : 0 < x) {m n : ℕ} (hn : 0 < n) (h : x ^ n ≤ 2 ^ m) :
    Real.logb 2 x ≤ m / n
```

**And.** `le_logb_two` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:100`

> And `2^m ≤ x^n` gives `m/n ≤ log₂ x`.

```lean
theorem le_logb_two {x : ℝ} {m n : ℕ} (hn : 0 < n) (h : (2 : ℝ) ^ m ≤ x ^ n) :
    (m : ℝ) / n ≤ Real.logb 2 x
```

**And.** `log_two_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:112`

> `log 2 ≤ 7/10`, from `2^10 = 1024 ≤ 1095 < 2.718^7`.

```lean
theorem log_two_le : Real.log 2 ≤ 7 / 10
```

**And.** `le_log_two` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:119`

> `2/3 ≤ log 2`, from `2.719^2 < 8 = 2^3`.

```lean
theorem le_log_two : (2 : ℝ) / 3 ≤ Real.log 2
```

**And.** `le_logb_three` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:126`

> `84/53 ≤ log₂ 3`, from `2^84 ≤ 3^53`.

```lean
theorem le_logb_three : (84 : ℝ) / 53 ≤ Real.logb 2 3
```

**And.** `logb_three_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:132`

> `log₂ 3 ≤ 149/94`, from `3^94 ≤ 2^149`.

```lean
theorem logb_three_le : Real.logb 2 3 ≤ 149 / 94
```

**And.** `le_log_lo` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:138`

> `19/100 ≤ log (3049/2500)`, from `2.719^19 ≤ (3049/2500)^100`.

```lean
theorem le_log_lo : (19 : ℝ) / 100 ≤ Real.log (3049 / 2500)
```

**And.** `le_log_hi` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:145`

> `-(1/4) ≤ log (39/50)`, from `(50/39)^4 ≤ 2.718`.

```lean
theorem le_log_hi : -(1 : ℝ) / 4 ≤ Real.log (39 / 50)
```

**And.** `log_lo_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:156`

> `log (61/50) ≤ 1/5`, from `(61/50)^5 ≤ 2.718`.

```lean
theorem log_lo_le : Real.log (61 / 50) ≤ 1 / 5
```

**And.** `log_hi_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:163`

> `log (1951/2500) ≤ -(6/25)`, from `2.719^6 ≤ (2500/1951)^25`.

```lean
theorem log_hi_le : Real.log (1951 / 2500) ≤ -(6 : ℝ) / 25
```

**And.** `pC_thirty_ge` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:180`

> `0.6098 ≤ p_30`.

```lean
theorem pC_thirty_ge : (3049 : ℝ) / 5000 ≤ pC 30
```

**And.** `pC_thirty_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:187`

> `p_30 ≤ 0.61`.

```lean
theorem pC_thirty_le : pC 30 ≤ 61 / 100
```

**And.** `klHalf_ge_of` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:194`

> **A sandwich on `p` gives a lower bound on `D(p ‖ 1/2)`.**

```lean
theorem klHalf_ge_of {p plo phi A B : ℝ} (hlo : plo ≤ p) (hhi : p ≤ phi)
    (hplo : 0 < plo) (hphi : phi < 1) (hA0 : 0 ≤ A) (hA : A ≤ Real.log (2 * plo))
    (hB0 : B ≤ 0) (hB : B ≤ Real.log (2 * (1 - phi))) :
    plo * A + (1 - plo) * B ≤ klHalf p
```

**And.** `klHalf_le_of` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:215`

> **A sandwich on `p` gives an upper bound on `D(p ‖ 1/2)`.**

```lean
theorem klHalf_le_of {p plo phi A B : ℝ} (hlo : plo ≤ p) (hhi : p ≤ phi)
    (hplo : 1 / 2 < plo) (hphi : phi < 1) (hA : Real.log (2 * phi) ≤ A)
    (hB0 : B ≤ 0) (hB : Real.log (2 * (1 - plo)) ≤ B) :
    klHalf p ≤ phi * A + (1 - phi) * B
```

**And.** `klHalf_thirty_ge` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:239`

> `D(p_30 ‖ 1/2) ≥ 0.018312`.

```lean
theorem klHalf_thirty_ge : (9156 : ℝ) / 500000 ≤ klHalf (pC 30)
```

**And.** `klHalf_thirty_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:249`

> `D(p_30 ‖ 1/2) ≤ 0.0284`.

```lean
theorem klHalf_thirty_le : klHalf (pC 30) ≤ (71 : ℝ) / 2500
```

**And.** `chernoffExponent_thirty_lt` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:270`

> `e(30) < 13/10`, so the side condition `A > C + e(C)` is met by `A ≥ 32`.

```lean
theorem chernoffExponent_thirty_lt : chernoffExponent 30 < 13 / 10
```

**And.** `cylinder_bound_thirty` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:283`

> **The conjecture from a cylinder bound at `C = 30`.** If every `O`-rooted `L(y)`-bad cylinder of depth `⌈30 L(y)⌉` holds at most its fair share plus `y (log y)^{-A}`, at all large scales above a certified floor, for some `A ≥ 32`, then every positive integer reaches `1`.

```lean
theorem cylinder_bound_thirty {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {A : ℝ} (hA : 32 ≤ A)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ 30 A y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `pressure_thirty` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:293`

> **The conjecture from the pressure hypothesis at `C = 30`.** If the live pressure at the tilt `p_30/(1 - p_30)` and depth `⌈30 L(y)⌉` is at most `2y a_θ^{d(y)}` at all large scales above a certified floor, then every positive integer reaches `1`.

```lean
theorem pressure_thirty {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → Pressure.PressureBound N₀ 30 0 y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `klDiv_half` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:303`

> At `q = 1/2` the relative entropy is the paper's `D(p ‖ 1/2)`.

```lean
theorem klDiv_half {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    OneSided.klDiv p (1 / 2) = klHalf p
```

**And.** `oneSidedExponent_half` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:310`

> Hence the one-sided exponent at `q = 1/2` is the Chernoff exponent.

```lean
theorem oneSidedExponent_half {C : ℝ} (hC : 5 ≤ C) :
    OneSided.oneSidedExponent C (1 / 2) = chernoffExponent C
```

**And.** `logb_tilt_thirty_le` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:317`

> `log₂` of the re-centring tilt at `C = 30`, `q = 1/2`, is at most `13/20`: from `(61/39)^20 ≤ 2^13`.

```lean
theorem logb_tilt_thirty_le : Real.logb 2 (OneSided.tilt (pC 30) (1 / 2)) ≤ 13 / 20
```

**And.** `one_sided_thirty` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:344`

> **The conjecture from the one-sided hypothesis at `C = 30`, `q = 1/2`.** If no `L(y)`-bad cylinder of depth below `⌈30 L(y)⌉` sends more than half of its members, plus `y (log y)^{-A}`, to an odd next letter, at all large scales above a certified floor, for some `A ≥ 52`, then every positive integer reaches `1`.

```lean
theorem one_sided_thirty {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) {A : ℝ} (hA : 52 ≤ A)
    (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSided.OneSidedBound N₀ 30 (1 / 2) A y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 50. `J-fate-classes-density-averaged` &mdash; covers 0.24

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.37; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Corollary 5.5 (fate contagion) at every 0 < lambda <= 100/203, each clause in its log-mass form and its dyadic-block form, as named theorems: (1) the reach-one class R, backward-closed and containing 1, has sum_{n in R, n <= x} 1/n >= K (log x)^lambda for x >= x_0 (Density.reachesOne_logMass_averaged) and natural density >= c (log y)^(lambda-1) on a dyadic block inside every large shell (reachesOne_natDensity_averaged); (2) if some start fails, the failures have the same bounds (Production.failures_logMass_averaged, Density.failures_natDensity_averaged); (3) the basin of any state m >= 1, the starts whose orbit passes through m, has them (basin_logMass_averaged, basin_natDensity_averaged) -- the paper's clause is the case of a periodic m, the basin of that cycle -- and so do the di  *(truncated; read the ledger row)*

**Declarations.** `reachesOne_natDensity_averaged` &mdash; kernel-checked, `Problems/Juggler/FateDyadicDensity.lean:290`

> **Corollary 5.5(1), dyadic-block form.**

```lean
theorem reachesOne_natDensity_averaged {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount ReachesOne y : ℝ)
```

**And.** `reachesOne_logMass_averaged` &mdash; kernel-checked, `Problems/Juggler/FateDyadicDensity.lean:283`

> **Corollary 5.5(1), log-mass form.** The reach-one class `R` is backward-closed and contains `1`, so `Σ_{n ∈ R, n ≤ x} 1/n ≥ K (log x)^λ` for every `0 < λ ≤ 100/203`.

```lean
theorem reachesOne_logMass_averaged {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass ReachesOne x
```

**And.** `failures_natDensity_averaged` &mdash; kernel-checked, `Problems/Juggler/FateDyadicDensity.lean:299`

> **Corollary 5.5(2), dyadic-block form.** If some start `a` does not reach `1`, the failures have natural density at least `c (log y)^{λ-1}` on a dyadic block inside every large shell; the log-mass form is `Production.failures_logMass_averaged`.

```lean
theorem failures_natDensity_averaged {a : ℕ} (ha : 1 ≤ a) (hfail : ¬ReachesOne a) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount (fun n => ¬ReachesOne n) y : ℝ)
```

**And.** `basin_logMass_averaged` &mdash; kernel-checked, `Problems/Juggler/FateDyadicDensity.lean:308`

> **Corollary 5.5(3) for a cycle, log-mass form.** The basin of a state `m ≥ 1`, the starts whose orbit passes through `m`, is backward-closed and contains `m`; for a periodic `m` it is the basin of that cycle.

```lean
theorem basin_logMass_averaged {m : ℕ} (hm : 1 ≤ m) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam ≤ 100 / 203) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => Ancestor n m) x
```

**And.** `basin_natDensity_averaged` &mdash; kernel-checked, `Problems/Juggler/FateDyadicDensity.lean:316`

> **Corollary 5.5(3) for a cycle, dyadic-block form.**

```lean
theorem basin_natDensity_averaged {m : ℕ} (hm : 1 ≤ m) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount (fun n => Ancestor n m) y : ℝ)
```

**And.** `escapes_logMass_averaged` &mdash; kernel-checked, `Problems/Juggler/FateDyadicDensity.lean:324`

> **Corollary 5.5(3) for divergence, log-mass form.** If some orbit diverges, the divergent starts carry log-mass at least `K (log x)^λ`.

```lean
theorem escapes_logMass_averaged {a : ℕ} (ha : 1 ≤ a) (hesc : EscapesToInfinity a) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass EscapesToInfinity x
```

**And.** `escapes_natDensity_averaged` &mdash; kernel-checked, `Problems/Juggler/FateDyadicDensity.lean:331`

> **Corollary 5.5(3) for divergence, dyadic-block form.**

```lean
theorem escapes_natDensity_averaged {a : ℕ} (ha : 1 ≤ a) (hesc : EscapesToInfinity a)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount EscapesToInfinity y : ℝ)
```

## 51. `J-paper-b-E-is-the-exponent-walk` &mdash; covers 0.24

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.35; different result 0.1.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** Paper B section 7's composed map is the exponent walk of the Paper C collision work, and its linearisation criterion is a unit climb of that walk. With the notation of J-paper-b-defect-coefficient-chain, e_t = 3^(o_t) / 2^t exactly, where o_t is the number of odd letters up to t (`iter_eq_pow`). Taking log base 2 gives e_t = 2^(u_t) with u_t = o_t log2(3) - t, which is the walk J-live-set-ladder-factorisation splits at, J-damping-at-running-minimum is about, and J-dominant-defect-at-walk-minimum measures the climb of. Hence E = e_{t-1}/e_s = 2^(u_{t-1} - u_s), and E < 2 says exactly that the walk climbs by less than one unit between the defect at letter s and the wave at letter t. Two consequences. (i) The criterion is an exact integer inequality in the counts: with a odd and b even letter  *(truncated; read the ledger row)*

**Declarations.** `iter_eq_pow` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:167`

> **The exponent walk, exactly.** `e_t = 3^(o_t) / 2^t`. Taking `log₂` gives `u_t = o_t log₂ 3 - t`, the walk the Paper C work is built on; this is that statement before any logarithm, so it is exact.

```lean
theorem iter_eq_pow (w : List Letter) :
    iter w = 3 ^ (oddCount w) / 2 ^ w.length
```

**And.** `lt_two_iff_counts` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:187`

> **The criterion in the counts.** `E < 2` is the exact integer inequality `3^a < 2^(a+b+1)`, with `a` the odd letters of the block and `a + b` its length. No real logarithm and no floating point anywhere.

```lean
theorem lt_two_iff_counts (w : List Letter) :
    iter w < 2 ↔ (3 : ℚ) ^ (oddCount w) < 2 ^ (w.length + 1)
```

**And.** `iter_eq_of_counts` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:195`

> **Order independence.** The criterion does not see the order of the block, only how many of each letter it holds. Immediate from `iter_eq_pow`, and not obvious from the product form.

```lean
theorem iter_eq_of_counts (v w : List Letter)
    (ho : oddCount v = oddCount w) (hl : v.length = w.length) :
    iter v = iter w
```

**And.** `lt_two_congr` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:201`

> The same statement for the criterion itself.

```lean
theorem lt_two_congr (v w : List Letter)
    (ho : oddCount v = oddCount w) (hl : v.length = w.length) :
    iter v < 2 ↔ iter w < 2
```

**And.** `oddCount` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:151`

> The number of odd letters in a word: `o_t`.

```lean
def oddCount : List Letter → ℕ
  | [] => 0
  | Letter.O :: w => oddCount w + 1
  | Letter.E :: w => oddCount w

@[simp] theorem oddCount_nil : oddCount [] = 0
```

## 52. `J-tao-rate-implies-conjecture` &mdash; covers 0.24

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.41; different result 0.18.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** Theorem A of the Tao-reduction note. If for some e > 1 − λ** = 0.5074… and all sufficiently large y, #{n odd in (y, 2y] : n does not reach 1} ≤ y (log y)^{−e}, then every positive integer reaches 1. Proof: every failure lies in the E-tree of an odd failure (forward closure), each E-tree level has log-mass ≤ 2/n₀ and at most 1 + log₂ log x levels meet [1, x], so the log-count of the failure set is ≪ (log x)^{1−e} log log x, contradicting fate contagion (J-fate-log-density) for any λ ∈ (1 − e, λ**). The E-tree bound, the dyadic sum and the contradiction given a contagion lower bound K (log x)^λ are Lean (tao_rate_implies_conjecture in FateTaoReduction.lean); the contagion bound itself (Theorem 5.3) stays a human proof, so this row is not Lean-verified. The same holds for the hypothesis state  *(truncated; read the ledger row)*

**Declarations.** `tao_rate_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateTaoReduction.lean:691`

> **Paper C Theorem 7.2 on the failure set.** If the contagion bound holds for the failure set whenever it is nonempty, and the odd failures satisfy the Tao-type rate with `e > 1 - λ`, then every positive integer reaches `1`.

```lean
theorem tao_rate_implies_conjecture {lam e : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (he : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) → ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x)
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `logMass_le_treeLevels` &mdash; kernel-checked, `Problems/Juggler/FateTaoReduction.lean:262`

> Every member of a forward-closed class excluding `1` lies at a level `j ≤ log₂ log₂ x` of the `E`-tree of an odd member `n₀ ≤ x`.

```lean
theorem logMass_le_treeLevels {A : ℕ → Prop} (hF : ForwardClosed A) (h1 : ¬A 1) (x : ℕ) :
    logMass A x ≤ ∑ n₀ ∈ {n₀ ∈ Icc 1 x | n₀ % 2 = 1 ∧ A n₀},
      ∑ j ∈ range (Nat.log 2 (Nat.log 2 x) + 1), ∑ n ∈ treeLevel n₀ j x, (1 : ℝ) / n
```

**And.** `logMass_le_oddLogMass` &mdash; kernel-checked, `Problems/Juggler/FateTaoReduction.lean:307`

> **The `E`-tree bound.** The log-mass of a forward-closed class excluding `1` is at most `(3/2)(1 + log₂ log₂ x)` times its odd log-mass.

```lean
theorem logMass_le_oddLogMass {A : ℕ → Prop} (hF : ForwardClosed A) (h1 : ¬A 1) (x : ℕ) :
    logMass A x ≤ 3 / 2 * ((Nat.log 2 (Nat.log 2 x) : ℝ) + 1) * oddLogMass A x
```

**And.** `oddLogMass_le_of_dyadic` &mdash; kernel-checked, `Problems/Juggler/FateTaoReduction.lean:444`

> **The dyadic sum.** A rate `y (log y)^{-e}` on the odd members of every block `(y, 2y]`, `y ≥ y₀ ≥ 2`, bounds the odd log-mass up to `x` by `oddLogMass y₀ + (log 2)^{-e} (log₂ x + 1)^{1-e}/(1-e)`.

```lean
theorem oddLogMass_le_of_dyadic {A : ℕ → Prop} {y₀ : ℕ} (hy₀ : 2 ≤ y₀) {e : ℝ} (he0 : 0 < e)
    (he1 : e < 1)
    (hdy : ∀ y : ℕ, y₀ ≤ y → ((oddMembers A y).card : ℝ) ≤ y * Real.log y ^ (-e)) (x : ℕ) :
    oddLogMass A x ≤ oddLogMass A y₀ +
      Real.log 2 ^ (-e) * ((Nat.log 2 x : ℝ) + 1) ^ (1 - e) / (1 - e)
```

**And.** `logMass_le_rpow` &mdash; kernel-checked, `Problems/Juggler/FateTaoReduction.lean:511`

> The upper bound at every `x ≥ 3`: `logMass A x ≤ D (log x)^{δ + 1 - e}` for an explicit `D`, once the dyadic rate holds with `0 < e < 1` from `y₀ ≥ 2` and `0 < δ ≤ 1`.

```lean
theorem logMass_le_rpow {A : ℕ → Prop} (hF : ForwardClosed A) (h1 : ¬A 1) {y₀ : ℕ}
    (hy₀ : 2 ≤ y₀) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (hdy : ∀ y : ℕ, y₀ ≤ y → ((oddMembers A y).card : ℝ) ≤ y * Real.log y ^ (-e))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℕ, 3 ≤ x → logMass A x ≤ D * Real.log x ^ (δ + (1 - e))
```

**And.** `tao_rate_implies_empty` &mdash; kernel-checked, `Problems/Juggler/FateTaoReduction.lean:621`

> **Paper C Theorem 7.2 (Theorem A of the Tao-reduction note), given the contagion bound.** Let `A` be forward-closed and exclude `1`. Suppose the contagion bound holds for `A` whenever it is nonempty — `Σ_{n ≤ x, n ∈ A} 1/n ≥ K (log x)^λ` for all large `x`, some `K > 0` — and that its odd members satisfy the Tao-type rate `#{n odd in (y, 2y] : n ∈ A} ≤ y (log y)^{-e}` for all large `y`, with `e > 1 - λ`. Then `A` has no positive member.

```lean
theorem tao_rate_implies_empty {A : ℕ → Prop} (hF : ForwardClosed A) (h1 : ¬A 1)
    {lam e : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (he : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ A n) → ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass A x)
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((oddMembers A y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ¬A n
```

**Doubtful from here: coverage between 0.25 and 0.5.**

## 53. `J-cubic-remainder-assembly` &mdash; covers 0.25

*Reads as: the claim asserts more than the declarations state (0.74).*

*Claim broader 0.74; declaration narrower 0.55; different result 0.27.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** An OrbitUpperChargeCertificate with 1<m and M<m^3 has evenCount < oddCount, positive lifted gaps, square remainders and odd numerators. Off the last-odd cut and wrap, the signed RC68 correction equals the adjacent remainder difference. If m<520000000 then every gap has 2-adic valuation at most 86. Given an even-denominator hypothesis off the reset set and a three-block deviation cover, leftover_rc70_of_cover yields L<=87*(3+2S); at L=780239 this forces S>=4483. The Result 20 consumer leftover_run_critical_of_blocks, from supplied positive even-gap block lengths summing 780237, runCost inequalities and totalGap<=519999999^3-519999999, forces C>=14569, and the numeric adapters give T>=14571 and S>=7284 from their explicit support hypotheses. These statements do not prove the even-denominator  *(truncated; read the ledger row)*

**Declarations.** `evenCount_lt_oddCount` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:46`

> Surplus `o log 3 > L log 2` and `log 3 < 2 log 2` force `e < o`.

```lean
theorem evenCount_lt_oddCount (Q : OrbitUpperChargeCertificate m M k)
    (_hm : 1 < m) : evenCount Q < Q.oddCount
```

**And.** `gap_pos` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:197`

```lean
theorem gap_pos (Q : OrbitUpperChargeCertificate m M k)
    (hM : M < m ^ 3) (i : Fin Q.length) : 0 < gap Q i
```

**And.** `rem_add` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:251`

```lean
theorem rem_add (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) :
    (if i.val < Q.oddCount then Q.state i ^ 3 else Q.state i) =
      Q.state (Q.next i) ^ 2 + rem Q i
```

**And.** `numer_odd` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:285`

```lean
theorem numer_odd (Q : OrbitUpperChargeCertificate m M k)
    (i : Fin Q.length) : numer Q i % 2 = 1
```

**And.** `rem_diff_ordinary` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:429`

```lean
theorem rem_diff_ordinary (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) {i : Fin Q.length}
    (hnext : i.val + 1 < Q.length) (hcut : i.val + 1 ≠ Q.oddCount) :
    corr Q i = (rem Q (succIdx Q i) : ℤ) - rem Q i
```

**And.** `leftover_gap_val_le` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:246`

```lean
theorem leftover_gap_val_le (Q : OrbitUpperChargeCertificate m M k)
    (hM : M < m ^ 3) (hmin : m < 520000000) (i : Fin Q.length) :
    padicValNat 2 (gap Q i) ≤ 86
```

**And.** `leftover_rc70_of_cover` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:531`

> Leftover RC70 from an assembled even-denominator and deviation cover.

```lean
theorem leftover_rc70_of_cover (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) (hmin : m < 520000000)
    (βOO βOE βEO : ℕ)
    (heven : ∀ i, i ∉ resets Q → denom Q i % 2 = 0)
    (hcover : resets Q ⊆
      boundary Q hm hM ∪ deviations Q βOO βOE βEO ∪
        (deviations Q βOO βOE βEO).image (predIdx Q)) :
    Q.length ≤ (86 + 1) * (3 + 2 * (deviations Q βOO βOE βEO).card)
```

**And.** `leftover_deviation_lower_of_cover` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:558`

```lean
theorem leftover_deviation_lower_of_cover
    (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) (hmin : m < 520000000)
    (hL : Q.length = 780239)
    (βOO βOE βEO : ℕ)
    (heven : ∀ i, i ∉ resets Q → denom Q i % 2 = 0)
    (hcover : resets Q ⊆
      boundary Q hm hM ∪ deviations Q βOO βOE βEO ∪
        (deviations Q βOO βOE βEO).image (predIdx Q)) :
    4483 ≤ (deviations Q βOO βOE βEO).card
```

**And.** `leftover_reset_lower_of_count` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:587`

```lean
theorem leftover_reset_lower_of_count {H T : ℕ} (hH : H ≤ 86)
    (hcount : 780239 ≤ (H + 1) * T) : 8969 ≤ T
```

**And.** `leftover_run_critical_of_blocks` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:575`

> Result 20 conditional consumer: supplied even-gap block lengths and `runCost` inequalities at the leftover tuple yield RC79.

```lean
theorem leftover_run_critical_of_blocks
    {ι : Type*} [Fintype ι]
    (length cost : ι → ℕ)
    (hlength : ∀ i, 0 < length i)
    (hsum : ∑ i, length i = 780237)
    (hcost : ∀ i, runCost (length i) ≤ cost i)
    (hbudget : 4 + ∑ i, cost i ≤ m ^ 3 - m)
    (hgap : m ^ 3 - m ≤ 519999999 ^ 3 - 519999999) :
    14569 ≤ Fintype.card ι
```

**And.** `leftover_run_nonzero_of_blocks` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:591`

```lean
theorem leftover_run_nonzero_of_blocks {C T : ℕ}
    (hC : 14569 ≤ C) (hfilter : C + 2 ≤ T) : 14571 ≤ T
```

**And.** `leftover_run_deviation_of_blocks` &mdash; kernel-checked, `Problems/Juggler/CubicRemainderAssembly.lean:595`

```lean
theorem leftover_run_deviation_of_blocks {C S : ℕ}
    (hC : 14569 ≤ C) (hcover : C ≤ 1 + 2 * S) : 7284 ≤ S
```

## 54. `J-cycle-cubic-band-order` &mdash; covers 0.25

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.65; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Conditional cycle-order theorem. Let C be a primitive nontrivial Juggler cycle with minimum m>1, maximum M<m^3, length L and o odd states; set e=L-o. If c_0=m<...<c_(L-1) lists its states, the odd states are exactly those below m^2 and J(c_i)=c_((i+e) mod L). Hence gcd(L,o)=1 and the odd count in the first k steps from m is ceil(k o/L), for 0<=k<=L: the exact ceiling mechanical word. Proof separates odd/even states and images, uses injectivity to eliminate possible floor ties, then ranks the resulting cyclic permutation. A non-mechanical primitive cycle or one with gcd(L,o)>1 must instead have M>=m^3+1. The height hypothesis is essential to this argument; no unconditional Christoffel claim, no parity obstruction, no new period exclusion. Consolidated in Paper A Section 3.10 and formalized   *(truncated; read the ledger row)*

**Declaration.** `cubicBand_mechanical_itinerary` &mdash; kernel-checked, `Problems/Juggler/CubicConsequences.lean:50`

> A primitive cubic-band orbit has the exact ceiling-mechanical odd prefixes.

```lean
theorem cubicBand_mechanical_itinerary {m L : ℕ} (hL : 0 < L)
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand m (c i))
    (hstep : ∀ i, c (p i) = floorPower (c i))
    (hcycle : p.IsCycleOn (↑(Finset.univ : Finset (Fin L)))) :
    ∃ o ≤ L, Nat.Coprime L o ∧
      (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
      (∀ i, (p i).val = (i.val + (L - o)) % L) ∧
      ∀ k, (∑ j ∈ Finset.range k,
        if floorPower^[j] (c ⟨0, hL⟩) % 2 = 1 then 1 else 0) =
          (k * o + L - 1) / L
```

## 55. `BTL-zero-output` &mdash; covers 0.26

*Reads as: the claim asserts more than the declarations state (0.81).*

*Claim broader 0.81; declaration narrower 0.34; different result 0.09.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** 3^k divides f(n_w) iff every output trit of the residual machine along w is 0, so the solution tree of f(x) = 0 mod 3^k is the zero-output subtree; balanced digits are what force the partial sum below the modulus

**Declaration.** `lift_iff_outputs_zero` &mdash; kernel-checked, `BTCalculus/PadicLifting.lean:82`

> `3^k` divides `f(n_w)` exactly when every output trit along `w` is `0`. The word itself need not consist of trits: the outputs are trits whatever the sections are, and that is all the packing bound needs.

```lean
theorem lift_iff_outputs_zero (w : List ℤ) (f : ℤ[X]) :
    IsRootMod w.length f (packWord w) ↔
      outputAlong w f = List.replicate w.length (0 : ℤ)
```

## 56. `J-cycle-itinerary-eliahou-leftover` &mdash; covers 0.26

*Reads as: the claim asserts more than the declarations state (0.67).*

*Claim broader 0.67; declaration narrower 0.34; different result 0.18.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, and every length in [30, 10^5) outside a named list of near-convergents is already excluded, then the period is 84, or belongs to that list, or is at least 10^5. Lean theorem cycle_itinerary_eliahou_leftover: bookkeeping on cycle_itinerary_length_eighty_four_or_ge_eighty_five plus EliahouTable, not a new inequality. This is the Collatz Eliahou leftover shape (period ≥ X, or a named convergent family) on the floor-power map. Paper A prints the floor-10^6 instance as Theorem 4.6; leftover 84 is Appendix A companion. This is not a proof of the finance table, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declarations.** `cycle_itinerary_eliahou_leftover` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:873`

> Bookkeeping: the Lean leftover `84` or `≥ 85`, plus the finance table, is the Eliahou leftover. Not a new inequality.

```lean
theorem cycle_itinerary_eliahou_leftover {n : ℕ} {w : List Branch}
    {exceptions : List ℕ} (hn : 2 ≤ n) (h : CycleItinerary n w)
    (hTable : EliahouTable exceptions) :
    EliahouLeftover w.length exceptions
```

**And.** `EliahouTable` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:866`

> Every length in `[30, cutoff)` outside the named family is already excluded. Instantiated by the computational gap table.

```lean
def EliahouTable (exceptions : List ℕ) : Prop
```

**And.** `EliahouLeftover` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:861`

> Eliahou leftover: period `84`, a listed near-convergent, or at least the finance table cutoff.

```lean
def EliahouLeftover (L : ℕ) (exceptions : List ℕ) : Prop
```

**And.** `eliahouTableCutoff` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:857`

> Finance table cutoff used by the Eliahou leftover.

```lean
def eliahouTableCutoff : ℕ
```

## 57. `J-cycle-itinerary-length-eighty-four-or-ge-eighty-five` &mdash; covers 0.26

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.3; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 84 or at least 85. Lengths ≤ 56 are excluded at floor 257; lengths 57–83 are excluded by cycle_finance_min_two_hundred_sixty_one at 15921/11 (finance_excludes_length_fiftyseven, finance_excludes_length_seventysix, and companions, packaged as no_cycle_itinerary_length_lt_eighty_four). Length 84 is the next record near-convergent (need ≈ 40269). Lean theorem cycle_itinerary_length_eighty_four_or_ge_eighty_five. Strengthened by J-cycle-itinerary-length-eighty-four-m-ge-three-or-ge-eighty-five, which kills length 84 with at most two odd-runs, and by J-cycle-itinerary-eliahou-leftover, which rewrites the length leftover plus the finance table as period 84, a listed near-convergent, or at least 10^5. This is not a no-cycle-of  *(truncated; read the ledger row)*

**Declarations.** `cycle_itinerary_length_eighty_four_or_ge_eighty_five` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:847`

> If a nontrivial cycle exists, its period is `84` or at least `85`. The cheap leftovers `57` and `76` die at the residual floor `261`; `58`–`75` and `77`–`83` die by the same comparison. `L=84` is the next record near-convergent.

```lean
theorem cycle_itinerary_length_eighty_four_or_ge_eighty_five
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 84 ∨ 85 ≤ w.length
```

**And.** `cycle_finance_min_two_hundred_sixty_one` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:725`

> Finance at the rotated odd minimum after the residual floor `261`: `(15921/11)(3^o - 2^L) ≤ L 3^o`, because the minimum is at least `261` and `261 log 257 > 15921/11`.

```lean
theorem cycle_finance_min_two_hundred_sixty_one {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (15921 / 11 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w
```

**And.** `finance_excludes_length_fiftyseven` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:823`

> Finance excludes length `57` (also killed by the floor `261` residual). Named leftover milestone.

```lean
theorem finance_excludes_length_fiftyseven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 57) : ¬CycleItinerary n w
```

**And.** `finance_excludes_length_seventysix` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:829`

> Finance excludes length `76` (also killed by the floor `261` residual). Named leftover milestone.

```lean
theorem finance_excludes_length_seventysix {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 76) : ¬CycleItinerary n w
```

**And.** `no_cycle_itinerary_length_lt_eighty_four` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:834`

> No cycle itinerary of length below `84`.

```lean
theorem no_cycle_itinerary_length_lt_eighty_four {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hLt : w.length < 84) : ¬CycleItinerary n w
```

## 58. `J-cyclemin-walk-transport-envelope` &mdash; covers 0.26

*Reads as: the claim asserts more than the declarations state (0.81).*

*Claim broader 0.81; declaration narrower 0.39; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The transport inequality of Paper A Theorem 5.3, Lean end to end in log form. On a CycleMin cycle with minimum n ≥ 400, every state satisfies walkWeight w k · (log n − D) ≤ log x_k with walkWeight w k = 3^(a_k)/2^k (the walk weight 2^(u_k), rational — no real exponentiation) and D = 1.05·e/n + 0.7·o/(n·√n) (cycleMin_transport, WalkTransport.lean); exponentiating gives x_k ≥ (n e^(−D))^(w_k). Ingredients all Lean: per-step floor losses log T(x) ≥ (3/2)·log x − 1.05/(x√x) (odd, x ≥ 9) and log T(x) ≥ (1/2)·log x − 1.05/√x (even, x ≥ 441) from the floor cells and −log(1−t) ≤ 1.05t on t ≤ 1/21 (log_floorPower_odd_ge, log_floorPower_even_ge, neg_log_one_sub_le); the exact weight recursion w_{k+1} = (3/2)w_k (odd), w_k/2 (even); odd injections priced at x_j ≥ n (cycleMin_iterate_ge) against w_{j+  *(truncated; read the ledger row)*

**Declarations.** `cycleMin_transport` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:453`

> **Transport to a reduced base** (Paper A Theorem 5.3, log form): on a minimum-based cycle with minimum `n ≥ 400`, every state satisfies `w_k·(log n − D) ≤ log x_k` with `D = 1.05·e/n + 0.7·o/(n·√n)`. Exponentiating gives `x_k ≥ (n e^{−D})^{w_k}`. Closed instance of `aboveAnchor_transport`.

```lean
theorem cycleMin_transport {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w) {k : ℕ} (hk : k ≤ w.length) :
    walkWeight w k * (Real.log n - transportDeficit n w) ≤
      Real.log (floorPower^[k] n)
```

**And.** `log_floorPower_odd_ge` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:129`

> Odd step, lower side: for odd `x ≥ 9`, `log T(x) ≥ (3/2)·log x − 1.05/(x·√x)`.

```lean
theorem log_floorPower_odd_ge {x : ℕ} (hx : 9 ≤ x) (ho : x % 2 = 1) :
    3 * Real.log x / 2 - 1.05 / (x * Real.sqrt x) ≤
      Real.log (floorPower x)
```

**And.** `log_floorPower_even_ge` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:89`

> Even step, lower side: for even `x ≥ 441`, `log T(x) ≥ (1/2)·log x − 1.05/√x`.

```lean
theorem log_floorPower_even_ge {x : ℕ} (hx : 441 ≤ x) (he : x % 2 = 0) :
    Real.log x / 2 - 1.05 / Real.sqrt x ≤ Real.log (floorPower x)
```

**And.** `neg_log_one_sub_le` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:79`

> `−log(1−t) ≤ 1.05·t` for `0 ≤ t ≤ 1/21`.

```lean
theorem neg_log_one_sub_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 21) :
    -Real.log (1 - t) ≤ 1.05 * t
```

**And.** `one_le_walkWeight` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:220`

> Cycle minimality forces `u_k ≥ 0`, that is `w_k ≥ 1` (`cycleMin_prefix_pow_le` in weight form).

```lean
theorem one_le_walkWeight {n : ℕ} {w : List Branch} (hn : 2 ≤ n)
    (h : CycleMin n w) {k : ℕ} (hk : k ≤ w.length) :
    1 ≤ walkWeight w k
```

## 59. `J-fate-share-law-layer` &mdash; covers 0.26

*Reads as: the claim asserts more than the declarations state (0.82).*

*Claim broader 0.82; declaration narrower 0.48; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The exact layer of Paper C Section 4.3, the share law (Lemma 4.5) and Corollary 4.6. The expansion: along a fiber n_j = n_1 + 2(j-1) the phase x_j = n_j^{3/2}/2 (xval) equals x_1 + (3/2) sqrt(n_1) (j-1) + (3/4) (j-1)^2 / sqrt(n_1) + E_j with |E_j| <= (1/4)(j-1)^3 n_1^{-3/2} (xval_expansion); the Taylor step is, after v = sqrt(1+u), the polynomial inequality 0 <= 1 + (3/2)(v^2-1) + (3/8)(v^2-1)^2 - v^3 <= (v^2-1)^3/16 (taylor_three_halves), no derivative taken; on a fiber Phi(m) the remainder is at most (2/27)(m+1)/m^2 (xval_expansion_fiber), the paper's O(1/m) with a constant. The range: phi_beta(s) = beta s + s^2/3 has on [0,1] the range beta + 1/3 for beta >= 0, -beta - 1/3 for beta <= -2/3, and max(0, beta + 1/3) + (3/4) beta^2 between (phiRange; never exceeded, phi_sub_le; attained, ex  *(truncated; read the ledger row)*

**Declarations.** `xval_expansion` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:60`

> **The fiber phase expanded about its first term.** With `x_j = xval n_j = n_j^{3/2}/2` and `n_j = n₁ + 2d`: `x_j = x₁ + (3/2)√n₁ d + (3/4) d²/√n₁ + E` where `|E| ≤ (1/4) d³/n₁^{3/2}`.

```lean
theorem xval_expansion {n₁ : ℕ} (hn : 1 ≤ n₁) (d : ℕ) :
    |xval (n₁ + 2 * d) - (xval n₁ + 3 / 2 * Real.sqrt n₁ * d + 3 / 4 * (d : ℝ) ^ 2 / Real.sqrt n₁)|
      ≤ 1 / 4 * (d : ℝ) ^ 3 / Real.sqrt n₁ ^ 3
```

**And.** `taylor_three_halves` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:49`

> Second-order Taylor of `(1+u)^{3/2}` in `u = v² - 1`, with the cubic remainder, as polynomial algebra: `0 ≤ 1 + (3/2)u + (3/8)u² - v³ ≤ u³/16` for `v ≥ 1`. In `w = v - 1` the middle expression is `w³/2 + 3w⁴/8` and the right side is that plus `3w⁴/8 + 3w⁵/8 + w⁶/16`.

```lean
theorem taylor_three_halves {v : ℝ} (hv : 1 ≤ v) :
    0 ≤ 1 + 3 / 2 * (v ^ 2 - 1) + 3 / 8 * (v ^ 2 - 1) ^ 2 - v ^ 3 ∧
      1 + 3 / 2 * (v ^ 2 - 1) + 3 / 8 * (v ^ 2 - 1) ^ 2 - v ^ 3 ≤ (v ^ 2 - 1) ^ 3 / 16
```

**And.** `xval_expansion_fiber` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:103`

> On a fiber `Φ(m)`, `m ≥ 1`, the remainder is at most `(2/27)(m+1)/m²`: `d ≤ (2/3)(m+1)^{1/3}` since both ends lie in the fiber, and `√n₁³ = n₁^{3/2} ≥ m²`. The paper's `|E_j| ≪ m^{-1}`.

```lean
theorem xval_expansion_fiber {m n₁ d : ℕ} (hm : 1 ≤ m) (h₁ : n₁ ∈ oeFiber m)
    (h₂ : n₁ + 2 * d ∈ oeFiber m) :
    |xval (n₁ + 2 * d) - (xval n₁ + 3 / 2 * Real.sqrt n₁ * d + 3 / 4 * (d : ℝ) ^ 2 / Real.sqrt n₁)|
      ≤ 2 / 27 * ((m : ℝ) + 1) / (m : ℝ) ^ 2
```

**And.** `phi_sub_le` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:157`

> Two values of `φ_β` on `[0, 1]` differ by at most the range.

```lean
theorem phi_sub_le (β : ℝ) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    phi β s - phi β t ≤ phiRange β
```

**And.** `exists_phi_sub_eq` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:183`

> The range is attained: two points of `[0, 1]` realize it.

```lean
theorem exists_phi_sub_eq (β : ℝ) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1, phi β s - phi β t = phiRange β
```

**And.** `phiRange_le_half_iff` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:199`

> **Corollary 4.6(2), the arithmetic.** The range is at most `1/2` exactly for `β ∈ [-5/6, 1/6]`; in the middle case it never exceeds `1/3`.

```lean
theorem phiRange_le_half_iff (β : ℝ) : phiRange β ≤ 1 / 2 ↔ -(5 / 6) ≤ β ∧ β ≤ 1 / 6
```

**And.** `extremeMeasure_eq_zero` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:221`

> Outside `[-5/6, 1/6]` no fiber is extreme.

```lean
theorem extremeMeasure_eq_zero {β : ℝ} (h : β < -(5 / 6) ∨ 1 / 6 < β) :
    extremeMeasure β = 0
```

**And.** `extremeMeasure_piece1` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:230`

```lean
theorem extremeMeasure_piece1 {β : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) (1 / 6)) :
    extremeMeasure β = 1 / 6 - β
```

**And.** `extremeMeasure_piece2` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:236`

```lean
theorem extremeMeasure_piece2 {β : ℝ} (hβ : β ∈ Set.Icc (-(1 / 3) : ℝ) 0) :
    extremeMeasure β = 1 / 6 - β - 3 / 4 * β ^ 2
```

**And.** `extremeMeasure_piece3` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:246`

```lean
theorem extremeMeasure_piece3 {β : ℝ} (hβ : β ∈ Set.Icc (-(2 / 3) : ℝ) (-(1 / 3))) :
    extremeMeasure β = 1 / 2 - 3 / 4 * β ^ 2
```

**And.** `extremeMeasure_piece4` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:256`

```lean
theorem extremeMeasure_piece4 {β : ℝ} (hβ : β ∈ Set.Icc (-(5 / 6) : ℝ) (-(2 / 3))) :
    extremeMeasure β = 5 / 6 + β
```

**And.** `integral_extremeMeasure` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:265`

> **Corollary 4.6(3), the arithmetic.** `∫ max(0, 1/2 - range) dβ = 25/108`, as `1/72 + 11/108 + 11/108 + 1/72` over the four pieces `[-5/6, -2/3]`, `[-2/3, -1/3]`, `[-1/3, 0]`, `[0, 1/6]`.

```lean
theorem integral_extremeMeasure :
    ∫ β in (-(5 / 6) : ℝ)..(1 / 6), extremeMeasure β = 25 / 108
```

## 60. `J-small-cycle-census-seven` &mdash; covers 0.26

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.35; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** No itinerary of length at most seven is a Juggler cycle itinerary at any n ≥ 2; equivalently a nontrivial Juggler cycle, if one exists, has period at least eight (Paper A Theorem 3.8). Assembly: the length-≤6 census, the formal-expansion filter on length seven, the odd-run exclusion of O^6E, the internal-E bootstrap exclusions of OOEOOOE and OOOEOOE, rotation of EOOOOOE and OEOOOOE onto the leftovers, and the leftover exclusions of OOOOEOE and OOOOOEE (Lemma 3.7). Lean theorem no_cycle_itinerary_length_le_seven. Strengthened by Paper A Theorem 3.22 / Corollary 3.23 (even-count at most three is impossible, so the period is at least eleven). This is not an exclusion of all cycles and not a halt theorem.

**Declaration.** `no_cycle_itinerary_length_le_seven` &mdash; kernel-checked, `Problems/Juggler/SmallCycleCensus.lean:220`

> **Small-cycle census.** No `n ≥ 2` realizes a cycle itinerary of length at most seven. Length eight and beyond is open.

```lean
theorem no_cycle_itinerary_length_le_seven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 7) : ¬CycleItinerary n w
```

## 61. `BTA-x3-Q-def` &mdash; covers 0.27

*Reads as: the claim asserts more than the declarations state (0.65).*

*Claim broader 0.65; declaration narrower 0.33; different result 0.11.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Q_t(u)=D^t(u^3), the integer cubic quotient (qCubic). The paper's Q_{t,K,W} is its residue modulo 3^K on u∈P_W; that reduction is stated in the congruence rows BTA-x3-Q-eq and BTA-x3-Q-visible, not here.

**Declaration.** `qCubic_def` &mdash; kernel-checked, `BTCalculus/MismatchedCubicQuotient.lean:23`

```lean
theorem qCubic_def (t : Nat) (u : Int) :
    qCubic t u = iterDZ t (u ^ 3)
```

## 62. `J-cycle-quartic-formal-projection` &mdash; covers 0.27

*Reads as: a declaration is a different result (0.83).*

*Claim broader 0.71; declaration narrower 0.47; different result 0.83.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For a supplied finite modular rank component with injective ambient ranks, collapse<=rank and the stated lifted return, the total collapse displacement Delta satisfies e*p+Delta=s*n and gcd(e,s) divides Delta. Under coprime e,s, nonempty component and an omitted ambient rank, Delta is positive. The module proves predecessor geometry, selected displacement and distinct-partner bounds, and an adjacent-gap consequence from a normalized interval gap. It does not construct the full anchor/rank model from an arbitrary primitive cycle or prove common component periods.

**Declarations.** `ofModular` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:71`

> A modular two-block return determines its exact zero-or-one wrap lift.

```lean
def ofModular {r : ℕ} (he : e = r + s)
    (rank : ι → ℕ) (hrank : ∀ i, rank i < e)
    (hinj : Function.Injective rank) (σ : Equiv.Perm ι) (f : ℕ → ℕ)
    (hle : ∀ i, f (rank i) ≤ rank i)
    (hupper : ∀ i, r ≤ rank i → f (rank i) = rank i)
    (hstep : ∀ i, rank (σ i) = (f (rank i) + s) % e) :
    RankComponent ι e s where
  rank
```

**And.** `displacement_balance` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:113`

> The periodic permutation cancels rank coordinates in the summed lift.

```lean
theorem displacement_balance (C : RankComponent ι e s) :
    C.totalDisplacement + e * C.upper.card = s * Fintype.card ι
```

**And.** `totalDisplacement_pos_of_omitted` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:201`

```lean
theorem totalDisplacement_pos_of_omitted (C : RankComponent ι e s)
    [Nonempty ι] (hcop : Nat.Coprime e s) {j : ℕ}
    (hj : j < e) (homit : ∀ i, C.rank i ≠ j) :
    0 < C.totalDisplacement
```

**And.** `adjacent_gap_of_ratio` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:340`

```lean
theorem adjacent_gap_of_ratio (z : ℕ → ℝ) {a g i : ℕ} {τ : ℝ}
    (hag : a ≤ g) (hgi : g < i) (hτ : 0 ≤ τ)
    (hgap : τ < (z i - z g) / (i - a : ℕ)) :
    ∃ j, g ≤ j ∧ j < i ∧ τ < z (j + 1) - z j
```

**And.** `RankComponent` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:55`

> An embedded finite periodic component together with its exact rank lift.

```lean
structure RankComponent (ι : Type*) [Fintype ι] [DecidableEq ι] (e s : ℕ) where
  rank : ι → ℕ
  rank_lt : ∀ i, rank i < e
  rank_injective : Function.Injective rank
  next : Equiv.Perm ι
  collapse : ℕ → ℕ
  collapse_le : ∀ i, collapse (rank i) ≤ rank i
  upper : Finset ι
  lift_eq : ∀ i,
    rank (next i) + e * (if i ∈ upper then 1 else 0) = collapse (rank i) + s

namespace RankComponent
```

**And.** `gcd_dvd_totalDisplacement` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:144`

```lean
theorem gcd_dvd_totalDisplacement (C : RankComponent ι e s) :
    Nat.gcd e s ∣ C.totalDisplacement
```

**And.** `predecessor_le` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:11`

```lean
theorem predecessor_le (anchors : Finset ℕ) (i : ℕ) :
    predecessor anchors i ≤ i
```

**And.** `predecessor_monotone` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:17`

```lean
theorem predecessor_monotone (anchors : Finset ℕ) : Monotone (predecessor anchors)
```

**And.** `predecessor_eq_self` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:25`

```lean
theorem predecessor_eq_self (anchors : Finset ℕ) {i : ℕ} (hi : i ∈ anchors) :
    predecessor anchors i = i
```

**And.** `predecessor_mem` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:31`

```lean
theorem predecessor_mem (anchors : Finset ℕ) (hzero : 0 ∈ anchors) (i : ℕ) :
    predecessor anchors i ∈ anchors
```

**And.** `predecessor_eq_on_cell` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:43`

> The predecessor is constant until the next selected anchor.

```lean
theorem predecessor_eq_on_cell (anchors : Finset ℕ) {a i : ℕ}
    (ha : a ∈ anchors) (hai : a ≤ i)
    (hgap : ∀ b ∈ anchors, b ≤ i → b ≤ a) :
    predecessor anchors i = a
```

**And.** `selected_displacement_le` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:211`

```lean
theorem selected_displacement_le (C : RankComponent ι e s) (S : Finset ι) :
    ∑ i ∈ S, C.displacement i ≤ C.totalDisplacement
```

**And.** `selected_displacement_cast_le` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:242`

```lean
theorem selected_displacement_cast_le (C : RankComponent ι e s) (S : Finset ι) :
    ∑ i ∈ S, (C.displacement i : ℝ) ≤ (C.totalDisplacement : ℝ)
```

**And.** `negative_card_le` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:216`

> Every selected negative substitution spends at least one rank unit.

```lean
theorem negative_card_le (C : RankComponent ι e s) (S : Finset ι)
    (hneg : ∀ i ∈ S, C.collapse (C.rank i) < C.rank i) :
    S.card ≤ C.totalDisplacement
```

**And.** `partner_interval_sum_le` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:229`

> A partner after the block start cannot increase the charged interval length.

```lean
theorem partner_interval_sum_le (C : RankComponent ι e s) (S : Finset ι)
    (partnerRank : ι → ℕ)
    (hstart : ∀ i ∈ S, C.collapse (C.rank i) ≤ partnerRank i) :
    ∑ i ∈ S, (C.rank i - partnerRank i) ≤ C.totalDisplacement
```

**And.** `partner_injOn` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:249`

> Equal projected targets make a chosen partner map injective on a periodic set.

```lean
theorem partner_injOn {α β γ : Type*} {P : Set α}
    {T : α → γ} {R : β → γ} {partner : α → β}
    (hT : Set.InjOn T P)
    (hpartner : ∀ x ∈ P, R (partner x) = T x) :
    Set.InjOn partner P
```

**And.** `partner_not_mem` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:259`

> A different point with the same projected successor cannot also be periodic.

```lean
theorem partner_not_mem {α β : Type*} {P : Set α} {T : α → β}
    (hT : Set.InjOn T P) {x y : α} (hx : x ∈ P)
    (hxy : x ≠ y) (ht : T x = T y) : y ∉ P
```

**And.** `block_injOn` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:266`

> Constancy on blocks and periodic injectivity allow at most one point per block.

```lean
theorem block_injOn {α β γ : Type*} {P : Set α} {T : α → β} {block : α → γ}
    (hT : Set.InjOn T P)
    (hblock : ∀ x y, block x = block y → T x = T y) :
    Set.InjOn block P
```

**And.** `component_target_injective` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:274`

> An embedded component obtains projected injectivity from its actual permutation.

```lean
theorem component_target_injective {ι α : Type*}
    (embed : ι → α) (σ : Equiv.Perm ι) (T : α → α)
    (hembed : Function.Injective embed)
    (hstep : ∀ i, T (embed i) = embed (σ i)) :
    Function.Injective (fun i => T (embed i))
```

**And.** `component_partner_injective` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:284`

```lean
theorem component_partner_injective {ι α β : Type*}
    (embed : ι → α) (σ : Equiv.Perm ι) (T : α → α)
    (R : β → α) (partner : ι → β)
    (hembed : Function.Injective embed)
    (hstep : ∀ i, T (embed i) = embed (σ i))
    (hpartner : ∀ i, R (partner i) = T (embed i)) :
    Function.Injective partner
```

**And.** `component_partner_not_in_range` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:296`

```lean
theorem component_partner_not_in_range {ι α : Type*}
    (embed : ι → α) (σ : Equiv.Perm ι) (T : α → α)
    (hembed : Function.Injective embed)
    (hstep : ∀ i, T (embed i) = embed (σ i))
    {i : ι} {y : α} (hneq : y ≠ embed i)
    (hsame : T y = T (embed i)) : y ∉ Set.range embed
```

**And.** `component_block_injective` &mdash; kernel-checked, `Problems/Juggler/QuarticProjection.lean:306`

```lean
theorem component_block_injective {ι α β : Type*}
    (embed : ι → α) (σ : Equiv.Perm ι) (T : α → α) (block : α → β)
    (hembed : Function.Injective embed)
    (hstep : ∀ i, T (embed i) = embed (σ i))
    (hblock : ∀ x y, block x = block y → T x = T y) :
    Function.Injective (fun i => block (embed i))
```

## 63. `OST-np-particular-s3` &mdash; covers 0.27

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.44; different result 0.18.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, from the origin the third coordinate of the control particular equals minus the MSD consumed valuation: (particularSum ws)_3 = -consumedSum |ws| ws, so val(B)=0 iff c_B lies on F={s_3=0}; this is energy_telescope at n=0, not a bound on L_0

**Declaration.** `particular_s3` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:556`

> From the origin, `(c_B)₃ = -val(B)`. KNOWN energy at `n=0`, not `L₀`.

```lean
theorem particular_s3 (ws : List ℤ) :
    (particularSum ws).2.2 = -consumedSum ws.length ws
```

## 64. `J-cycle-cubic-sorted-grid` &mdash; covers 0.28

*Reads as: the claim asserts more than the declarations state (0.63).*

*Claim broader 0.63; declaration narrower 0.58; different result 0.43.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For a primitive S_b cycle, or an actual Juggler cycle with minimum m>1 and maximum M<m^3, sort its states c_i and set T=log 3, Lambda=o log 3-L log 2>0, v_i=log(log c_i/log m), v_(i+L)=v_i+T and w_i=v_i-iT/L. Then osc(w)<= (1-1/L)Lambda and |w_i|<= (1-1/L)Lambda. The lifted adjacent gaps h_i=v_(i+1)-v_i satisfy range(h)<=Lambda and |h_i-T/L|<=(1-1/L)Lambda. The proof uses nonnegative logarithmic rounding defects summing to Lambda and the coprime rank rotation, with no factor L loss. The bounds do not resolve integer parity or exclude cycles. Consolidated in Paper A Section 3.10 and formalized in the seven Cubic modules. The cited declarations and supporting modules are compiled kernel proofs. The illustrative asymptotic comparison and universal wrong-parity question are not promoted; no ne  *(truncated; read the ledger row)*

**Declarations.** `threshold_cycle_grid` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:443`

> Standard connectedness of the exact threshold orbit supplies transitivity automatically.

```lean
theorem threshold_cycle_grid [NeZero L]
    {b : ℕ} (hb : 3 ≤ b) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand b (c i))
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, (thresholdMap b)^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i < b ^ 2)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o
```

**And.** `cubicBand_cycle_grid` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:454`

> Full quantitative bounds for an actual connected Juggler cycle in a cubic band.

```lean
theorem cubicBand_cycle_grid [NeZero L]
    {m : ℕ} (hm : 3 ≤ m) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand m (c i))
    (hstep : ∀ i, c (σ i) = floorPower (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, floorPower^[k] (c i) = c j) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o
```

**And.** `logCellDefect_nonneg` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:61`

> The lower square-cell inequality is enough for the one-step logarithmic loss sign.

```lean
theorem logCellDefect_nonneg
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o : ℕ)
    (hc : ∀ i, 1 < c i)
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (i : Fin L) : 0 ≤ logCellDefect c σ o i
```

**And.** `logCellDefect_sum` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:126`

> The total loss is obtained by permutation summation of the exact coordinates.

```lean
theorem logCellDefect_sum [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L) :
    ∑ i, logCellDefect c σ o i = logGridSurplus L o
```

**And.** `rank_rotation_real` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:79`

> The modular rank equation has the expected single-wrap form in real coordinates.

```lean
theorem rank_rotation_real
    (σ : Equiv.Perm (Fin L)) (o e : ℕ) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L) (i : Fin L) :
    ((σ i).val : ℝ) - (i.val : ℝ) =
      (e : ℝ) - if i.val < o then 0 else (L : ℝ)
```

**And.** `log_grid_of_power_cells` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:135`

> A realized power-cell cycle satisfies the claimed sharp log-log grid at every rank.

```lean
theorem log_grid_of_power_cells [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (i : Fin L) :
    |Real.log (Real.log (c i) / Real.log (c 0)) -
      (i.val : ℝ) * Real.log 3 / (L : ℝ)| ≤
        (1 - 1 / (L : ℝ)) * logGridSurplus L o
```

**And.** `logGridSurplus_pos_of_power_cells` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:171`

> A realized cycle has strictly positive logarithmic surplus.

```lean
theorem logGridSurplus_pos_of_power_cells [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1)) :
    0 < logGridSurplus L o
```

**And.** `log_gap_bounds_of_power_cells` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:250`

> Both claimed adjacent-gap estimates hold for realized power-cell cycles.

```lean
theorem log_gap_bounds_of_power_cells [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1))
    (i j : Fin L) :
    |liftedLogGap c j - liftedLogGap c i| ≤ logGridSurplus L o ∧
      |liftedLogGap c i - Real.log 3 / (L : ℝ)| ≤
        (1 - 1 / (L : ℝ)) * logGridSurplus L o
```

**And.** `threshold_log_grid` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:288`

> The universal grid bound specialized to an exact threshold cycle.

```lean
theorem threshold_log_grid [NeZero L]
    {b o : ℕ} (hb : 3 ≤ b) (ho : o ≤ L)
    (c : Fin L → ℕ) (hc : StrictMono c) (σ : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand b (c i))
    (hcut : ∀ i, c i < b ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i))
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (i : Fin L) :
    |Real.log (Real.log (c i) / Real.log (c 0)) -
      (i.val : ℝ) * Real.log 3 / (L : ℝ)| ≤
        (1 - 1 / (L : ℝ)) * logGridSurplus L o
```

**And.** `cubicBand_log_grid` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:309`

> The same bound holds for the actual map under cubic-band closure.

```lean
theorem cubicBand_log_grid [NeZero L]
    {m o : ℕ} (hm : 3 ≤ m) (ho : o ≤ L)
    (c : Fin L → ℕ) (hc : StrictMono c) (σ : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand m (c i))
    (hcut : ∀ i, c i < m ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (σ i) = floorPower (c i))
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (i : Fin L) :
    |Real.log (Real.log (c i) / Real.log (c 0)) -
      (i.val : ℝ) * Real.log 3 / (L : ℝ)| ≤
        (1 - 1 / (L : ℝ)) * logGridSurplus L o
```

**And.** `threshold_invariant_grid` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:417`

> The cutoff and all quantitative bounds follow for an exact threshold invariant cycle.

```lean
theorem threshold_invariant_grid [NeZero L]
    {b : ℕ} (hb : 3 ≤ b) (c : Fin L → ℕ) (hc : StrictMono c)
    (σ : Equiv.Perm (Fin L)) (hband : ∀ i, InCubicBand b (c i))
    (hstep : ∀ i, c (σ i) = thresholdMap b (c i))
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L)))) :
    ∃ o ≤ L, (Finset.univ.filter (fun i => c i < b ^ 2)).card = o ∧
      RealizedGridBounds (fun i => (c i : ℝ)) o
```

**And.** `realized_grid_bounds_of_power_cells` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:400`

> Full realization of both grid and gap bounds from power cells and sorted rank rotation.

```lean
theorem realized_grid_bounds_of_power_cells [NeZero L]
    (c : Fin L → ℝ) (σ : Equiv.Perm (Fin L)) (o e : ℕ)
    (hc : ∀ i, 1 < c i) (hsorted : StrictMono c)
    (hheight : ∀ i, c i < c 0 ^ 3) (hlen : L = o + e)
    (hrank : ∀ i, (σ i).val = (i.val + e) % L)
    (hcycle : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcell : ∀ i, c (σ i) ^ 2 ≤ c i ^ (if i.val < o then 3 else 1)) :
    RealizedGridBounds c o
```

**And.** `RealizedGridBounds` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:328`

> The complete quantitative conclusion, including positivity and the lifted seam.

```lean
def RealizedGridBounds [NeZero L] (c : Fin L → ℝ) (o : ℕ) : Prop
```

**And.** `surplus_pos` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:372`

```lean
theorem surplus_pos : 0 < logGridSurplus L o
```

**And.** `grid_bound` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:374`

```lean
theorem grid_bound (i : Fin L) :
    |logGridError c (c 0) i| ≤ (1 - 1 / (L : ℝ)) * logGridSurplus L o
```

**And.** `error_oscillation` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:377`

```lean
theorem error_oscillation (i j : Fin L) :
    |logGridError c (c 0) j - logGridError c (c 0) i| ≤
      (1 - 1 / (L : ℝ)) * logGridSurplus L o
```

**And.** `gap_range` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:383`

```lean
theorem gap_range (i j : Fin L) :
    |liftedLogGap c j - liftedLogGap c i| ≤ logGridSurplus L o
```

**And.** `gap_mean_bound` &mdash; kernel-checked, `Problems/Juggler/CubicLogGrid.lean:387`

```lean
theorem gap_mean_bound (i : Fin L) :
    |liftedLogGap c i - Real.log 3 / (L : ℝ)| ≤
      (1 - 1 / (L : ℝ)) * logGridSurplus L o
```

## 65. `J-envelope-lt-pow` &mdash; covers 0.28

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.67; different result 0.24.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If n ≥ 2, A > 0, x^A ≤ n^B, and B < k·A, then x < n^k. EnvelopeState n x packages the free inequality x^A ≤ n^B, with even (A,B)→(2A,B) and odd (A,B)→(2A,3B). PowerBound is the special case A=2^|w|, B=3^{oddCount w}. A realized itinerary with 3^{oddCount w} < k·2^{|w|} therefore has T_w(n) < n^k. power_bound_contracts is the k=1 case. Escape square and cube cells are k=2 and k=3 instances. The leftover itinerary OOEOOEOOEOEOO has the cube gap 3^9 < 3·2^13 and not the square gap 3^9 < 2·2^13. This is not a halt theorem and not a cycle-exclusion theorem.

**Declarations.** `power_bound_lt_pow` &mdash; kernel-checked, `Problems/Juggler/Envelope.lean:312`

> Word-stat form: `3^{oddCount w} < k · 2^{|w|}` yields `T_w(n) < n^k`. Implemented by `EnvelopeState.of_follows`. `power_bound_contracts` is the `k = 1` case.

```lean
theorem power_bound_lt_pow {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (hw : follows n w)
    (hgap : 3 ^ oddCount w < k * 2 ^ w.length) :
    image n w < n ^ k
```

**And.** `envelope_lt_pow` &mdash; kernel-checked, `Problems/Juggler/Envelope.lean:292`

> Cell comparison: `x^A ≤ n^B` and `B < k·A` force `x < n^k`.

```lean
theorem envelope_lt_pow {x n A B k : ℕ}
    (hn : 2 ≤ n) (_hA : 0 < A) (h : x ^ A ≤ n ^ B) (hgap : B < k * A) :
    x < n ^ k
```

**And.** `PowerBound` &mdash; kernel-checked, `Problems/Juggler/Envelope.lean:108`

> Weak one-sided bound `m^{2^k} ≤ n^{3^o}`. Equality is allowed.

```lean
def PowerBound (m n k o : ℕ) : Prop
```

**And.** `EnvelopeState` &mdash; kernel-checked, `Problems/Juggler/Envelope.lean:171`

> Free-exponent envelope `x^A ≤ n^B`. `PowerBound` is the special case `A = 2^k`, `B = 3^o`. Word algebra only.

```lean
structure EnvelopeState (n x : ℕ) where
  A : ℕ
  B : ℕ
  le : x ^ A ≤ n ^ B

/-- Even letter: `(A, B) → (2A, B)` from `T(x)^2 ≤ x`. -/
def EnvelopeState.even {n x : ℕ} (h : EnvelopeState n x) (heven : x % 2 = 0) :
    EnvelopeState n (floorPower x) where
  A
```

**And.** `EnvelopeState.even` &mdash; kernel-checked, `Problems/Juggler/Envelope.lean:177`

> Even letter: `(A, B) → (2A, B)` from `T(x)^2 ≤ x`.

```lean
def EnvelopeState.even {n x : ℕ} (h : EnvelopeState n x) (heven : x % 2 = 0) :
    EnvelopeState n (floorPower x) where
  A
```

**And.** `EnvelopeState.odd` &mdash; kernel-checked, `Problems/Juggler/Envelope.lean:189`

> Odd letter: `(A, B) → (2A, 3B)` from `T(x)^2 ≤ x^3`.

```lean
def EnvelopeState.odd {n x : ℕ} (h : EnvelopeState n x) (hodd : x % 2 = 1) :
    EnvelopeState n (floorPower x) where
  A
```

**And.** `power_bound_contracts` &mdash; kernel-checked, `Problems/Juggler/Envelope.lean:327`

> Strict block contraction from the exponent gap. Domain `n ≥ 2`. The `k = 1` case of `power_bound_lt_pow`. Not a claim that every trajectory meets a negative-drift word.

```lean
theorem power_bound_contracts {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : follows n w)
    (hgap : 3 ^ oddCount w < 2 ^ w.length) :
    floorPower^[w.length] n < n
```

## 66. `J-fate-tao-union-bound` &mdash; covers 0.28

*Reads as: the claim asserts more than the declarations state (0.61).*

*Claim broader 0.61; declaration narrower 0.48; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Theorem 8.3 (Tao-type bound from the cylinder hypothesis), exact and explicit forms. cylinder y d w is the set of odd n in (y, 2y] with itinerary n d = w; oddFailures y the odd n in (y, 2y] with ¬ReachesOne n; EnvelopeBad N₀ Y w says N₀^{2^t} < Y^{3^{o_t(w)}} for every prefix t ≤ |w|. (i) oddFailures_subset_bad_cylinders: if every start up to N₀ reaches 1, then oddFailures y ⊆ ⋃ {cylinder y d w : w ∈ allWords d, EnvelopeBad N₀ (2y) w} — Lemma 8.1 (reachesOne_of_itinerary_envelope) in covering form, using n ≤ 2y. (ii) oddFailures_card_le: if every envelope-bad cylinder has at most M starts then #oddFailures y ≤ #{envelope-bad words} · M. (iii) LBad_of_envelopeBad: for N₀, Y ≥ 2, envelope-bad at scale Y implies L-bad with L = log_2(log Y / log N₀). (iv) oddFailures_card_le_chernoff:   *(truncated; read the ledger row)*

**Declarations.** `oddFailures_card_le_explicit` &mdash; kernel-checked, `Problems/Juggler/FateChernoff.lean:403`

> **Theorem 8.3, explicit form.** Floor `N₀ ≥ 2`, scale `y ≥ 2`, `C ≥ 5`, depth `d = ⌈C L(y)⌉ ≥ 1`. If every `O`-rooted `L(y)`-bad cylinder of depth `d` holds at most `2^{-(d-1)} y/2 + y (log y)^{-A}` starts (the hypothesis `H(C, A)` at this `y`), then the odd failures in `(y, 2y]` number at most `y Λ^{-e(C)} + 2 Λ^C y (log y)^{-A}`, `Λ = log 2y / log N₀`. The paper's `(y/2) Λ^{-(e(C)-ε)}` for large `y` follows by absorbing the factor `2` into `Λ^ε` and the second term into the first when `A > C + e(C)`; that absorption is not formalized.

```lean
theorem oddFailures_card_le_explicit {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y : ℕ) (hy : 2 ≤ y)
    (C A : ℝ) (hC : 5 ≤ C) (hd1 : 1 ≤ depth C N₀ y)
    (hcyl : ∀ w ∈ allWords (depth C N₀ y), w.head? = some .odd → LBad (scaleL N₀ y) w →
      ((cylinder y (depth C N₀ y) w).card : ℝ) ≤
        2 ^ (-((depth C N₀ y : ℝ) - 1)) * y / 2 + y / Real.log y ^ A) :
    ((oddFailures y).card : ℝ) ≤
      y * scaleRatio N₀ y ^ (-chernoffExponent C) +
        2 * scaleRatio N₀ y ^ C * y / Real.log y ^ A
```

**And.** `EnvelopeBad` &mdash; kernel-checked, `Problems/Juggler/FateChernoff.lean:253`

> `w` fails the envelope comparison against the floor `N₀` at the scale `Y` at every prefix: `N₀^{2^t} < Y^{3^{o_t}}` for all `t ≤ |w|`. This is the integer form of `L(Y)`-badness.

```lean
def EnvelopeBad (N₀ Y : ℕ) (w : List Branch) : Prop
```

**And.** `oddFailures_subset_bad_cylinders` &mdash; kernel-checked, `Problems/Juggler/FateChernoff.lean:258`

> **Lemma 8.1 in covering form.** If every start up to `N₀` reaches `1`, an odd failure in `(y, 2y]` lies in the cylinder of an envelope-bad word.

```lean
theorem oddFailures_subset_bad_cylinders {N₀ : ℕ}
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y d : ℕ) :
    oddFailures y ⊆
      ({w ∈ allWords d | EnvelopeBad N₀ (2 * y) w}).biUnion (cylinder y d)
```

**And.** `oddFailures_card_le` &mdash; kernel-checked, `Problems/Juggler/FateChernoff.lean:285`

> **Theorem 8.3, the union bound.** Under a floor `N₀` and a bound `M` on every envelope-bad cylinder of depth `d`, the odd failures in `(y, 2y]` number at most (the number of envelope-bad words) times `M`.

```lean
theorem oddFailures_card_le {N₀ : ℕ}
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y d M : ℕ)
    (hcyl : ∀ w ∈ allWords d, EnvelopeBad N₀ (2 * y) w → (cylinder y d w).card ≤ M) :
    (oddFailures y).card ≤ #{w ∈ allWords d | EnvelopeBad N₀ (2 * y) w} * M
```

**And.** `LBad_of_envelopeBad` &mdash; kernel-checked, `Problems/Juggler/FateChernoff.lean:300`

> Envelope-badness at the scale `Y` is `L`-badness with `L = log₂ (log Y / log N₀)`, for `N₀ ≥ 2` and `Y ≥ 2`.

```lean
theorem LBad_of_envelopeBad {N₀ Y : ℕ} (hN : 2 ≤ N₀) (hY : 2 ≤ Y) {w : List Branch}
    (h : EnvelopeBad N₀ Y w) :
    LBad (Real.logb 2 (Real.log Y / Real.log N₀)) w
```

**And.** `oddFailures_card_le_chernoff` &mdash; kernel-checked, `Problems/Juggler/FateChernoff.lean:337`

> **Theorem 8.3, exact composite.** Floor `N₀ ≥ 2`, scale `y ≥ 1`, depth `d ≥ 1` with `d ≥ C L`, `L = log₂ (log 2y / log N₀)`, `C ≥ 5`; if every `L`-bad cylinder of depth `d` holds at most `M` starts, then the odd failures in `(y, 2y]` number at most `2^d · 2^{-e(C) L} · M`.

```lean
theorem oddFailures_card_le_chernoff {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (y d : ℕ) (hy : 1 ≤ y) (hd1 : 1 ≤ d)
    (C M : ℝ) (hC : 5 ≤ C) (hM : 0 ≤ M)
    (hd : C * Real.logb 2 (Real.log (2 * y) / Real.log N₀) ≤ d)
    (hcyl : ∀ w ∈ allWords d, LBad (Real.logb 2 (Real.log (2 * y) / Real.log N₀)) w →
      ((cylinder y d w).card : ℝ) ≤ M) :
    ((oddFailures y).card : ℝ) ≤
      2 ^ d * (2 : ℝ) ^ (-(chernoffExponent C *
        Real.logb 2 (Real.log (2 * y) / Real.log N₀))) * M
```

**And.** `cylinder_even_root_empty` &mdash; kernel-checked, `Problems/Juggler/FateChernoff.lean:386`

> Odd starts have first letter `O`: an `E`-rooted cylinder of positive depth is empty.

```lean
theorem cylinder_even_root_empty (y d : ℕ) (w : List Branch) (hd : 1 ≤ d)
    (hw : w.head? = some .even) : cylinder y d w = ∅
```

## 67. `BTC-op-fragment-nd-semantic` &mdash; covers 0.29

*Reads as: the claim asserts more than the declarations state (0.77).*

*Claim broader 0.77; declaration narrower 0.41; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** irreducibles of the enlarged operator-fragment TRS (tree rules plus N(D(x))→D(N(x))) are unique representatives of integer operator functions on {D, I_a, S, N}

**Declarations.** `eval_eq_unique_nf` &mdash; kernel-checked, `BTCalculus/OpFragSemantic.lean:497`

> Semantically equal terms share the same irreducible.

```lean
theorem eval_eq_unique_nf {t u n₁ n₂ : OpFrag}
    (h : ∀ n, eval t n = eval u n)
    (hn₁ : Normal n₁) (hn₂ : Normal n₂)
    (ht : ReflTransGen Step t n₁) (hu : ReflTransGen Step u n₂) : n₁ = n₂
```

**And.** `irreducible_eval_injective` &mdash; kernel-checked, `BTCalculus/OpFragSemantic.lean:481`

> Distinct irreducibles denote distinct maps `ℤ → ℤ`.

```lean
theorem irreducible_eval_injective {t u : OpFrag}
    (ht : Normal t) (hu : Normal u)
    (h : ∀ n : ℤ, eval t n = eval u n) : t = u
```

## 68. `J-cycle-quartic-formal-return` &mdash; covers 0.29

*Reads as: the claim asserts more than the declarations state (0.78).*

*Claim broader 0.78; declaration narrower 0.45; different result 0.17.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For bounded actual periodic extrema with m>=5 and M<m^4, the selected section x<m^2, m^4<=x^3 has guarded F/G/B returns. The return map preserves the section, is injective there, and admits a strictly sorted complete enumeration with a return permutation. If m^3<=M, an actual guarded F source exists. PeriodicExtrema need not be a single primitive orbit: this statement does not identify the enumeration size with the original even count, assert permutation transitivity, or derive the complete rank shuffle.

**Declarations.** `sorted_return_model` &mdash; kernel-checked, `Problems/Juggler/QuarticBand.lean:286`

> Sorting the actual selected section gives a genuine guarded return permutation.

```lean
theorem sorted_return_model (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) :
    ∃ (e : ℕ) (c : Fin e → ℕ) (p : Equiv.Perm (Fin e)),
      0 < e ∧ StrictMono c ∧
      (∀ i, c i ∈ C ∧ Section m (c i)) ∧
      (∀ x ∈ C, Section m x → ∃ i, c i = x) ∧
      (∀ i, c (p i) = returnMap m (c i))
```

**And.** `exists_F_source` &mdash; kernel-checked, `Problems/Juggler/QuarticBand.lean:243`

> The taller slab supplies a genuinely guarded F tower in the section.

```lean
theorem exists_F_source (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) (htall : m ^ 3 ≤ M) :
    ∃ x ∈ C, Section m x ∧ O x % 2 = 1 ∧ follows x [.odd, .odd, .even]
```

**And.** `Section` &mdash; kernel-checked, `Problems/Juggler/QuarticBand.lean:9`

```lean
def Section (m x : ℕ) : Prop
```

**And.** `returnMap` &mdash; kernel-checked, `Problems/Juggler/QuarticBand.lean:160`

```lean
def returnMap (m x : ℕ) : ℕ
```

**And.** `returnMap_closed` &mdash; kernel-checked, `Problems/Juggler/QuarticBand.lean:165`

```lean
theorem returnMap_closed (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) {x : ℕ} (hx : x ∈ C) (hs : Section m x) :
    returnMap m x ∈ C ∧ Section m (returnMap m x)
```

**And.** `returnMap_inj` &mdash; kernel-checked, `Problems/Juggler/QuarticBand.lean:203`

```lean
theorem returnMap_inj (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) {x y : ℕ} (hx : x ∈ C) (hy : y ∈ C)
    (hsx : Section m x) (hsy : Section m y)
    (h : returnMap m x = returnMap m y) : x = y
```

**And.** `guarded_return_cases` &mdash; kernel-checked, `Problems/Juggler/QuarticBand.lean:225`

```lean
theorem guarded_return_cases (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) {x : ℕ} (hx : x ∈ C) (hs : Section m x) :
    (follows x [.odd, .odd, .even] ∧ returnMap m x = ReturnCells.ooe x) ∨
    (follows x [.odd, .even, .odd] ∧ returnMap m x = O (ReturnCells.oe x)) ∨
    (follows x [.odd, .even] ∧ returnMap m x = ReturnCells.oe x)
```

## 69. `J-log-two-hundred-fifty-seven-gt-sixty-one-elevenths` &mdash; covers 0.29

*Reads as: the claim asserts more than the declarations state (0.83).*

*Claim broader 0.83; declaration narrower 0.49; different result 0.57.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** log 257 > 61/11, via e < 2.7182818286 and e^61 < 257^11 (log_two_hundred_fifty_seven_gt). Combined with the residual floor 257 this gives n log n > 15677/11 on a CycleMin, which excludes cycle length 38. The weaker half-integer bound 11/2 was enough for length 19 but not for 38. This is a numeric certificate, not a halt theorem.

**Declarations.** `log_two_hundred_fifty_seven_gt` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:527`

> Numeric certificate `log 257 > 61/11`, via `e < 2.7182818286` and `e^61 < 257^11`.

```lean
theorem log_two_hundred_fifty_seven_gt : (61 / 11 : ℝ) < Real.log 257
```

**And.** `cycleItinerary_iterate_not_lt_two_hundred_fifty_seven` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:486`

> Residual class `{1,…,256}` is disjoint from a nontrivial cycle.

```lean
theorem cycleItinerary_iterate_not_lt_two_hundred_fifty_seven
    {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    257 ≤ floorPower^[i] n
```

**And.** `finance_excludes_length_thirtyeight` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:697`

> Finance excludes length `38`: `2^38 < 3^24` and `(15677/11)(3^{24} - 2^{38}) > 38 · 3^{24}`.

```lean
theorem finance_excludes_length_thirtyeight {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length = 38) : ¬CycleItinerary n w
```

## 70. `BTN-confluence` &mdash; covers 0.3

*Reads as: the claim asserts more than the declarations state (0.81).*

*Claim broader 0.81; declaration narrower 0.56; different result 0.28.  Tag EXACT — LEAN VERIFIED, trust mixed.*

**Row.** stripped coefficient rewrite is locally and globally confluent; unique NF is encodeZ(value); [-5,2] joins after stripHigh

**Declarations.** `stripped_trits_eq_encodeZ` &mdash; kernel-checked, `BTCalculus/Confluence.lean:243`

```lean
theorem stripped_trits_eq_encodeZ :
    ∀ cs : List ℤ, allTrits cs → stripHigh cs = cs → cs = encodeZ (coeffValue cs)
  | [], _ht, hs => by
```

**And.** `reaches_encodeZ` &mdash; kernel-checked, `BTCalculus/Confluence.lean:432`

```lean
theorem reaches_encodeZ (cs : List ℤ) :
    ReflTransGen Step (stripHigh cs) (encodeZ (coeffValue cs))
```

**And.** `confluence` &mdash; kernel-checked, `BTCalculus/Confluence.lean:514`

```lean
theorem confluence {a b c : List ℤ}
    (hb : ReflTransGen Step (stripHigh a) b)
    (hc : ReflTransGen Step (stripHigh a) c) :
    Join (ReflTransGen Step) b c
```

**And.** `locally_confluent` &mdash; kernel-checked, `BTCalculus/Confluence.lean:530`

```lean
theorem locally_confluent {a b c : List ℤ} (ha : stripHigh a = a)
    (hb : Step a b) (hc : Step a c) :
    Join (ReflTransGen Step) b c
```

**And.** `overlap_minus5_two_raw` &mdash; compiler-checked, `BTCalculus/Confluence.lean:550`

> Raw Lean lists of the overlapping pair are not equal; stripping joins them.

```lean
theorem overlap_minus5_two_raw :
    step [-5, 2] 0 = [1, 0] ∧
      step (step (step [-5, 2] 1) 0) 1 = [1, 0, 0]
```

**And.** `overlap_minus5_two_stripped` &mdash; compiler-checked, `BTCalculus/Confluence.lean:555`

```lean
theorem overlap_minus5_two_stripped :
    rewriteAt [-5, 2] 0 = [1] ∧
      rewriteAt (rewriteAt (rewriteAt [-5, 2] 1) 0) 1 = [1]
```

## 71. `J-cycle-quartic-formal-gap-separation` &mdash; covers 0.3

*Reads as: the claim asserts more than the declarations state (0.57).*

*Claim broader 0.57; declaration narrower 0.54; different result 0.3.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** A supplied nonnegative finite transitive cocycle commuting with adjacent rotation, with total Lambda, gives adjacent gap at least [A-(e-1)*Lambda]/e. Applied to a strictly sorted integer array with source and OE-cell minima at least m>1, and the stated small-product condition, the exact floor-cell bound proves B injective on the array. The module derives the gap bound from the cocycle rather than assuming gap oscillation. The lower-power section predicate supplies the B-cell minimum. Full extraction of the positive sorted cocycle and original counts from an arbitrary primitive quartic Juggler cycle remains a separate written assembly, not an unconditional no-cycle theorem.

**Declarations.** `adjacent_gap_lower` &mdash; kernel-checked, `Problems/Juggler/QuarticGapSeparation.lean:18`

```lean
theorem adjacent_gap_lower {L : ℕ}
    (σ τ : Equiv.Perm (Fin L))
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcomm : Function.Commute σ τ) (w δ : Fin L → ℝ) (A Λ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hw : ∀ i, w (σ i) - w i = Λ / (L : ℝ) - δ i) (i : Fin L) :
    (A - ((L : ℝ) - 1) * Λ) / (L : ℝ) ≤
      w (τ i) - w i + A / (L : ℝ)
```

**And.** `B_injective_of_adjacent_gaps` &mdash; kernel-checked, `Problems/Juggler/QuarticGapSeparation.lean:50`

```lean
theorem B_injective_of_adjacent_gaps {L m : ℕ} (c : Fin L → ℕ)
    (hmono : StrictMono c) (hm : 1 < m)
    (hmin : ∀ i, m ≤ c i) (hBmin : ∀ i, m ≤ B (c i))
    (hgap : ∀ i j : Fin L, j.val = i.val + 1 →
      logEta m ≤ Real.log (Real.log (c j : ℝ)) -
        Real.log (Real.log (c i : ℝ))) : Function.Injective (fun i => B (c i))
```

**And.** `B_injective_of_cocycle` &mdash; kernel-checked, `Problems/Juggler/QuarticGapSeparation.lean:79`

```lean
theorem B_injective_of_cocycle {L m : ℕ} [NeZero L]
    (c : Fin L → ℕ) (hmono : StrictMono c) (hm : 1 < m)
    (hmin : ∀ i, m ≤ c i) (hBmin : ∀ i, m ≤ B (c i))
    (σ : Equiv.Perm (Fin L))
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcomm : Function.Commute σ (finRotate L)) (δ : Fin L → ℝ) (A Λ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hw : ∀ i, logError c A (σ i) - logError c A i = Λ / (L : ℝ) - δ i)
    (hsmall : ((L : ℝ) - 1) * Λ + (L : ℝ) * logEta m ≤ A) :
    Function.Injective (fun i => B (c i))
```

**And.** `B_ge_of_lower_power` &mdash; kernel-checked, `Problems/Juggler/QuarticGapSeparation.lean:100`

```lean
theorem B_ge_of_lower_power {m x : ℕ} (h : m ^ 4 ≤ x ^ 3) : m ≤ B x
```

**And.** `section_B_injective_of_cocycle` &mdash; kernel-checked, `Problems/Juggler/QuarticGapSeparation.lean:107`

```lean
theorem section_B_injective_of_cocycle {L m : ℕ} [NeZero L]
    (c : Fin L → ℕ) (hmono : StrictMono c) (hm : 1 < m)
    (hmin : ∀ i, m ≤ c i) (hsection : ∀ i, m ^ 4 ≤ c i ^ 3)
    (σ : Equiv.Perm (Fin L))
    (hσ : σ.IsCycleOn (↑(Finset.univ : Finset (Fin L))))
    (hcomm : Function.Commute σ (finRotate L)) (δ : Fin L → ℝ) (A Λ : ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hsum : ∑ i, δ i = Λ)
    (hw : ∀ i, logError c A (σ i) - logError c A i = Λ / (L : ℝ) - δ i)
    (hsmall : ((L : ℝ) - 1) * Λ + (L : ℝ) * logEta m ≤ A) :
    Function.Injective (fun i => B (c i))
```

## 72. `J-cycle-itinerary-length-nineteen-or-ge-thirty` &mdash; covers 0.31

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.25; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 19 or at least 30. Lengths ≤ 18 are J-small-cycle-census-eighteen; lengths 20–29 are excluded by the same floor-53 finance comparison. Length 19 is the next near-convergent (2^19 < 3^12) and survives 371/2; length 30 also survives 371/2. Lean theorems cycle_itinerary_length_nineteen_or_ge_thirty and the weaker corollary cycle_itinerary_length_nineteen_or_ge_twenty. This row is the floor-53 leftover. Strengthened by J-cycle-itinerary-length-thirty-eight-or-ge-thirty-nine, which kills the length-19 disjunct at the residual floor 257. This is not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declarations.** `cycle_itinerary_length_nineteen_or_ge_thirty` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:469`

> If a nontrivial cycle exists, its period is `19` or at least `30`. The gap `20..29` dies by finance at the residual floor `53`; `19` is the next near-convergent (`2^19 < 3^12`).

```lean
theorem cycle_itinerary_length_nineteen_or_ge_thirty {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 19 ∨ 30 ≤ w.length
```

**And.** `cycle_itinerary_length_nineteen_or_ge_twenty` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:478`

> Weaker leftover: period is `19` or at least `20`.

```lean
theorem cycle_itinerary_length_nineteen_or_ge_twenty {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 19 ∨ 20 ≤ w.length
```

## 73. `J-cyclemin-prefix-bunched-eoee` &mdash; covers 0.31

*Reads as: the claim asserts more than the declarations state (0.71).*

*Claim broader 0.71; declaration narrower 0.18; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every n ≥ 2, every a ≥ 5, and every prefix u, the itinerary u ++ O^a EOEE is not a Juggler CycleMin at n. The leftover cell lifts to y = T_u(n) ≥ n against the EOEE tail at y. Large y is y ≥ 314 at a = 5 and y ≥ 256 at a ≥ 6. Below those cutoffs the argument is returnsIntoB tables and seven-odd for a ≥ 7. The case y = n reduces to no_cycle_itinerary_three_even_eoee. Lean theorem no_cycleMin_prefix_eoee. This excludes that one bunched family only; it is not a bunched-short attack, not a length-11 census, and not a halt theorem.

**Declaration.** `no_cycleMin_prefix_eoee` &mdash; kernel-checked, `Problems/Juggler/PrefixBunched.lean:254`

> No CycleMin word ends in the bunched leftover `threeEvenEOEE a`, `a >= 5`, after any prefix `u`.

```lean
theorem no_cycleMin_prefix_eoee {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 5 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEOEE a)
```

## 74. `J-fate-first-letter-split` &mdash; covers 0.31

*Reads as: the claim asserts more than the declarations state (0.67).*

*Claim broader 0.67; declaration narrower 0.34; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The exact layer of Paper C's first-letter identity (6.1). For a two-way closed class A (ForwardClosed and BackwardClosed), any weight w and any finite index set s, the weighted mass of A splits exactly into three pieces by first letter: the even members, the odd members with even image (OE-type) and the odd members with odd image (OO-type), each piece indexed by its image lying in A as the paper indexes it (first_letter_split); shellLogMass_split is the log-mass form on a shell (y, x]. The map J is strictly increasing on the odd integers (floorPower_odd_lt), hence injective there (floorPower_odd_injective), so the paper's odd preimage n(m) of the free term is well defined, and sum_image_ooPiece rewrites the OO-type piece as a sum over the odd images. This is the partition, with no error te  *(truncated; read the ledger row)*

**Declarations.** `first_letter_split` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:120`

> The members of `A` in a finite index set, weighted by `w`, split by first letter into the three pieces of Section 6.2: even, `OE`-type, `OO`-type. Each piece is indexed by its image lying in `A`, as the paper's `⊔_{m ∈ A}` writes it; that is the same set of `n` by two-way closure. The identity is exact: it is the partition, with no error term.

```lean
theorem first_letter_split {A : ℕ → Prop} (hF : ForwardClosed A) (hB : BackwardClosed A)
    (w : ℕ → ℝ) (s : Finset ℕ) :
    ∑ n ∈ {n ∈ s | A n}, w n =
      (∑ n ∈ {n ∈ s | n % 2 = 0 ∧ A (floorPower n)}, w n)
      + (∑ n ∈ {n ∈ s | n % 2 = 1 ∧ floorPower n % 2 = 0 ∧ A (floorPower n)}, w n)
      + (∑ n ∈ {n ∈ s | n % 2 = 1 ∧ floorPower n % 2 = 1 ∧ A (floorPower n)}, w n)
```

**And.** `shellLogMass_split` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:145`

> **The exact layer of identity (6.1).** On any shell the log-mass of a two-way closed class is the sum of the log-masses of its even, `OE`-type and `OO`-type members. The paper's (6.1) is this identity after each piece is normalized (`φ_A`, `φ^fib_A`, `ψ_A`) and the boundary term of Lemma 3.1 is estimated; the normalization and the error `O(e^{-t/4}/t)` are not formalized.

```lean
theorem shellLogMass_split {A : ℕ → Prop} (hF : ForwardClosed A) (hB : BackwardClosed A)
    (y x : ℕ) :
    shellLogMass A y x =
      (∑ n ∈ {n ∈ Finset.Ioc y x | n % 2 = 0 ∧ A (floorPower n)}, (1 : ℝ) / n)
      + (∑ n ∈ {n ∈ Finset.Ioc y x | n % 2 = 1 ∧ floorPower n % 2 = 0 ∧ A (floorPower n)},
          (1 : ℝ) / n)
      + (∑ n ∈ {n ∈ Finset.Ioc y x | n % 2 = 1 ∧ floorPower n % 2 = 1 ∧ A (floorPower n)},
          (1 : ℝ) / n)
```

**And.** `floorPower_odd_lt` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:159`

> `J` is strictly increasing on the odd integers: two odd states differ by at least two, and `(⌊√(n³)⌋ + 1)² ≤ n³ + 2n² + 1 ≤ (n + 2)³`.

```lean
theorem floorPower_odd_lt {n m : ℕ} (hn : n % 2 = 1) (hm : m % 2 = 1) (hnm : n < m) :
    floorPower n < floorPower m
```

**And.** `floorPower_odd_injective` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:177`

> The odd preimage is unique: `J` is injective on the odd integers, so each odd image `m` of an odd `n` determines its `n(m)`.

```lean
theorem floorPower_odd_injective {n m : ℕ} (hn : n % 2 = 1) (hm : m % 2 = 1)
    (h : floorPower n = floorPower m) : n = m
```

**And.** `sum_image_ooPiece` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:191`

> **The free term as a sum over the odd images.** Summing any weight over the odd images of the `OO`-type members is summing it over those members through `J`: the paper's `Σ_{m ∈ A ∩ S_odd} 1/n(m)`, with `n(m)` well defined by `floorPower_odd_injective`.

```lean
theorem sum_image_ooPiece {A : ℕ → Prop} (y x : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ (ooPiece A y x).image floorPower, f m = ∑ n ∈ ooPiece A y x, f (floorPower n)
```

## 75. `J-residual-floor-fifty-three` &mdash; covers 0.31

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.44; different result 0.21.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Every positive integer strictly below 53 reaches 1 under the Juggler map (reachesOne_of_lt_fifty_three). Evens below 144 already reduce to the residual class {1,…,11}; the odd seeds 13,15,…,51 are finite orbit certificates. This is a finite certificate, not a halt theorem. Combined with cycleMin_finance it excludes cycle length 11.

**Declarations.** `reachesOne_of_lt_fifty_three` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:174`

> Every positive residual strictly below `53` is `ReachesOne`. This is a finite certificate, not a halt theorem. Combined with `cycleMin_finance` it excludes cycle length `11`.

```lean
theorem reachesOne_of_lt_fifty_three {y : ℕ} (hpos : 1 ≤ y) (hy : y < 53) :
    ReachesOne y
```

**And.** `reachesOne_of_lt_twelve` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:75`

> Every positive residual strictly below `12` is `ReachesOne`. This is a finite certificate, not a halt theorem.

```lean
theorem reachesOne_of_lt_twelve {y : ℕ} (hpos : 1 ≤ y) (hy : y < 12) :
    ReachesOne y
```

**And.** `even_lt_sq_twelve_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:100`

> One even step into `{1,…,11}`: every even `n` with `1 ≤ n < 144` is `ReachesOne`. Not a halt theorem.

```lean
theorem even_lt_sq_twelve_reachesOne {n : ℕ} (heven : n % 2 = 0)
    (hpos : 1 ≤ n) (hn : n < 144) : ReachesOne n
```

**And.** `thirteen_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:111`

```lean
theorem thirteen_reachesOne : ReachesOne 13
```

**And.** `fifteen_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:114`

```lean
theorem fifteen_reachesOne : ReachesOne 15
```

**And.** `seventeen_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:117`

```lean
theorem seventeen_reachesOne : ReachesOne 17
```

**And.** `nineteen_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:120`

```lean
theorem nineteen_reachesOne : ReachesOne 19
```

**And.** `twentyone_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:123`

```lean
theorem twentyone_reachesOne : ReachesOne 21
```

**And.** `twentythree_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:126`

```lean
theorem twentythree_reachesOne : ReachesOne 23
```

**And.** `twentyfive_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:129`

```lean
theorem twentyfive_reachesOne : ReachesOne 25
```

**And.** `twentyseven_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:132`

```lean
theorem twentyseven_reachesOne : ReachesOne 27
```

**And.** `twentynine_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:135`

```lean
theorem twentynine_reachesOne : ReachesOne 29
```

**And.** `thirtyone_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:138`

```lean
theorem thirtyone_reachesOne : ReachesOne 31
```

**And.** `thirtythree_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:141`

```lean
theorem thirtythree_reachesOne : ReachesOne 33
```

**And.** `thirtyfive_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:144`

```lean
theorem thirtyfive_reachesOne : ReachesOne 35
```

**And.** `thirtyseven_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:147`

```lean
theorem thirtyseven_reachesOne : ReachesOne 37
```

**And.** `thirtynine_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:150`

```lean
theorem thirtynine_reachesOne : ReachesOne 39
```

**And.** `fortyone_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:153`

```lean
theorem fortyone_reachesOne : ReachesOne 41
```

**And.** `fortythree_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:156`

```lean
theorem fortythree_reachesOne : ReachesOne 43
```

**And.** `fortyfive_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:159`

```lean
theorem fortyfive_reachesOne : ReachesOne 45
```

**And.** `fortyseven_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:162`

```lean
theorem fortyseven_reachesOne : ReachesOne 47
```

**And.** `fortynine_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:165`

```lean
theorem fortynine_reachesOne : ReachesOne 49
```

**And.** `fiftyone_reachesOne` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:168`

```lean
theorem fiftyone_reachesOne : ReachesOne 51
```

## 76. `J-residual-floor-two-hundred-sixty-one` &mdash; covers 0.31

*Reads as: the claim asserts more than the declarations state (0.82).*

*Claim broader 0.82; declaration narrower 0.36; different result 0.11.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Every positive integer strictly below 261 reaches 1 under the Juggler map (reachesOne_of_lt_two_hundred_sixty_one). The floor-257 class plus the two odd seeds 257 and 259 (five steps each) raise the floor. Exact log 257 cannot kill length 57 (257 ln 257 ≈ 1426 < 1430.8). Combined with cycleMin_finance and 261 log 257 > 15921/11 this excludes the cheap leftovers 57 and 76, so the named leftover is the record near-convergent 84. This is a finite certificate, not a halt theorem.

**Declarations.** `reachesOne_of_lt_two_hundred_sixty_one` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:480`

> Every positive residual strictly below 261 is ReachesOne. Two extra odd seeds; evens below 261 already reduce via `even_lt_sq_fifty_three`. Combined with cycleMin_finance this excludes the cheap leftovers 57 and 76, so the named leftover is the record near-convergent 84.

```lean
theorem reachesOne_of_lt_two_hundred_sixty_one {y : ℕ}
    (hpos : 1 ≤ y) (hy : y < 261) : ReachesOne y
```

**And.** `reachesOne_n257` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:469`

```lean
theorem reachesOne_n257 : ReachesOne 257
```

**And.** `reachesOne_n259` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:472`

```lean
theorem reachesOne_n259 : ReachesOne 259
```

## 77. `BTC-add-requires-carry-state` &mdash; covers 0.32

*Reads as: a declaration is narrower than the claim (0.73).*

*Claim broader 0.52; declaration narrower 0.73; different result 0.49.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** the packaged Add boundary combines three exact statements: D(x+y) is not D-local, same-sign I_a is not a constructor identity, and the named carry-free S-through-Add push-in extension fails local confluence

**Declaration.** `add_requires_carry_state` &mdash; kernel-checked, `BTCalculus/RewriteAddBoundary.lean:237`

> Packaged Add boundary: `D ∘ Add` is not D-local, same-sign `I_a` is not a constructor identity, and the named carry-free push-in extension fails local confluence.

```lean
theorem add_requires_carry_state :
    ¬ DLocal (fun x y => DZ (x + y)) ∧
      (∀ W, ¬ AffineCtor.exactTriple .Ip .Ip W) ∧
      (∀ W, ¬ AffineCtor.exactTriple .Im .Im W) ∧
      PushInStep pushInPeak (.add .X .Y) ∧
      PushInStep pushInPeak (.D (.add (.S .X) (.S .Y))) ∧
      (∀ u, ¬ PushInStep (.add .X .Y) u) ∧
      (∀ u, ¬ PushInStep (.D (.add (.S .X) (.S .Y))) u)
```

## 78. `BTN-dadd-closure` &mdash; covers 0.32

*Reads as: the claim asserts more than the declarations state (0.76).*

*Claim broader 0.76; declaration narrower 0.61; different result 0.24.  Tag EXACT — LEAN VERIFIED, trust compiler.*

**Row.** If s,a,b are trits then D(s+a+b) is a trit. The streaming residual of trit addition is exactly {-1,0,1}. Three values occur on D(x)=D(y)=0, so the residual is minimal.

**Declarations.** `dAdd_minimal_residual` &mdash; compiler-checked, `Problems/BalancedTernary/DAddResidual.lean:53`

> On the slice ``D(x)=D(y)=0``, the observable ``D(x+y)`` takes three values, so no 1-state or 2-state residual can repair locality.

```lean
theorem dAdd_minimal_residual :
    DZ 0 = DZ 1 ∧ DZ 1 = DZ (-1) ∧
      DZ (0 + 0) ≠ DZ (1 + 1) ∧
      DZ (1 + 1) ≠ DZ ((-1 : ℤ) + (-1)) ∧
      DZ (0 + 0) ≠ DZ ((-1 : ℤ) + (-1))
```

**And.** `dAdd_residual_closure` &mdash; compiler-checked, `Problems/BalancedTernary/DAddResidual.lean:85`

> Closure: if `s`, `a`, `b` are trits then `dAddNext s a b` is a trit.

```lean
theorem dAdd_residual_closure {s a b : ℤ}
    (hs : isTrit s) (ha : isTrit a) (hb : isTrit b) :
    isTrit (dAddNext s a b)
```

**And.** `dAdd_fiber_three` &mdash; compiler-checked, `Problems/BalancedTernary/DAddResidual.lean:42`

> The three fibre values `D(0+0) = 0`, `D(1+1) = 1`, `D(-1 + -1) = -1`.

```lean
theorem dAdd_fiber_three :
    DZ (0 + 0) = 0 ∧
      DZ (1 + 1) = 1 ∧
      DZ ((-1 : ℤ) + (-1)) = -1 ∧
      DZ (0 : ℤ) = 0 ∧
      DZ (1 : ℤ) = 0 ∧
      DZ (-1) = 0
```

## 79. `BTN-sdrg-lambda2-evens` &mdash; covers 0.32

*Reads as: the claim asserts more than the declarations state (0.7).*

*Claim broader 0.7; declaration narrower 0.5; different result 0.11.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For λ=2 and U_m, every even 2n with 0≤n≤(m-1)_+ is reached from 0 by an admissible word; the explicit word uses letters k+2 at step k (lambda2_step_up). The negative half -2n is not claimed by this row.

**Declarations.** `lambda2_step_up` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidualGeometry.lean:111`

> One even ``λ=2`` step: from ``2k`` the letter ``k+2`` reaches ``2(k+1)``.

```lean
theorem lambda2_step_up (k : ℕ) :
    signedNext 2 (2 * (k : ℤ)) ((k : ℤ) + 2) = 2 * ((k : ℤ) + 1)
```

**And.** `lambda2_even_reachable` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidualGeometry.lean:161`

> Every nonnegative even point of the sharp ``λ=2`` box is reached.

```lean
theorem lambda2_even_reachable (m n : ℕ) (h : n ≤ m.pred) :
    ∃ word : List ℤ, (∀ u ∈ word, u.natAbs ≤ m) ∧
      foldSigned 2 word 0 = 2 * (n : ℤ)
```

## 80. `J-flight-height-law` &mdash; covers 0.32

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.43; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Walk-height law (divergence rate) on descent-free prefixes: if AboveAnchor(n,w) with n >= 400 and the exponent walk is at height >= B doublings at step k (2^(k+B) <= 3^{a_k} with a_k the odd count of the k-prefix), then 2^B (log n − D) <= log x_k with the transport deficit D = 1.05 e/n + 0.7 o/(n√n); exponentiating, x_k >= (n e^{−D})^{2^B} — heights along a descent-free prefix are doubly exponential in the walk height (aboveAnchor_height_of_walk, weight form two_pow_le_walkWeight, WalkTransport.lean). One-case composition of aboveAnchor_transport with 2^B <= w_k = 3^{a_k}/2^k; when log n < D the bound is vacuously true since x_k >= 1. Appearing corollary of the September 2026 re-rooting of transport on AboveAnchor: composed with the flight walk-divergence theorem (J-flight-walk-divergence,  *(truncated; read the ledger row)*

**Declarations.** `aboveAnchor_height_of_walk` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:502`

> **Walk-height law** (divergence rate): on a descent-free prefix with anchor `n ≥ 400`, a walk height of `B` doublings at step `k` (`2^(k+B) ≤ 3^{a_k}`) forces `2^B·(log n − D) ≤ log x_k`; exponentiating, `x_k ≥ (n·e^{−D})^{2^B}` — heights along a descent-free prefix are doubly exponential in the walk height. Composed with the walk-divergence theorem (`J-flight-walk-divergence`; human glue: pigeonhole plus `cycle_strict_envelope`), every descent-free flight realizes this rate along an unbounded walk. Not a halt theorem and not a divergence theorem.

```lean
theorem aboveAnchor_height_of_walk {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : AboveAnchor n w) {k B : ℕ} (hk : k ≤ w.length)
    (hB : 2 ^ (k + B) ≤ 3 ^ oddCount (w.take k)) :
    (2 : ℝ) ^ B * (Real.log n - transportDeficit n w) ≤
      Real.log (floorPower^[k] n)
```

**And.** `two_pow_le_walkWeight` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:483`

> Weight form of a walk-height hypothesis: `2^(k+B) ≤ 3^{a_k}` (the exponent walk is at height `≥ B` doublings at step `k`) gives `2^B ≤ w_k` for the walk weight `w_k = 3^{a_k}/2^k`.

```lean
theorem two_pow_le_walkWeight {w : List Branch} {k B : ℕ}
    (hB : 2 ^ (k + B) ≤ 3 ^ oddCount (w.take k)) :
    (2 : ℝ) ^ B ≤ walkWeight w k
```

**And.** `aboveAnchor_transport` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:425`

> **Transport on descent-free prefixes** (log form): on `AboveAnchor n w` with `n ≥ 400`, every state satisfies `w_k·(log n − D) ≤ log x_k` with `D = 1.05·e/n + 0.7·o/(n·√n)`.

```lean
theorem aboveAnchor_transport {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : AboveAnchor n w) {k : ℕ} (hk : k ≤ w.length) :
    walkWeight w k * (Real.log n - transportDeficit n w) ≤
      Real.log (floorPower^[k] n)
```

## 81. `BTN-doubled-minimality` &mdash; covers 0.33

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.34; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust compiler.*

**Row.** The three carries -1,0,1 have pairwise distinct Mealy output signatures, so the 3-state machine is minimal.

**Declaration.** `doubledTrit_outputSignatures_distinct` &mdash; compiler-checked, `Problems/BalancedTernary/FiniteStateDynamics.lean:160`

> The three carries `-1`, `0` and `1` have pairwise distinct Mealy output signatures, so the three-state machine is minimal.

```lean
theorem doubledTrit_outputSignatures_distinct :
    outSig 0 ≠ outSig 1 ∧ outSig 0 ≠ outSig (-1) ∧ outSig 1 ≠ outSig (-1)
```

## 82. `J-cycle-itinerary-length-fifty-seven-or-ge-fifty-eight` &mdash; covers 0.33

*Reads as: the claim asserts more than the declarations state (0.78).*

*Claim broader 0.78; declaration narrower 0.27; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 57 or at least 58. Lengths ≤ 19 are J-small-cycle-census-nineteen; lengths 20–56 are excluded at floor 257. This row is the leftover before the two extra odd seeds 257 and 259. Strengthened by J-cycle-itinerary-length-eighty-four-or-ge-eighty-five, which kills the length-57 disjunct at the residual floor 261. Lean theorem cycle_itinerary_length_fifty_seven_or_ge_fifty_eight. This is not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `cycle_itinerary_length_fifty_seven_or_ge_fifty_eight` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:713`

> If a nontrivial cycle exists, its period is `57` or at least `58`. Weaker leftover: the floor `261` also kills `57` and `76`.

```lean
theorem cycle_itinerary_length_fifty_seven_or_ge_fifty_eight
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 57 ∨ 58 ≤ w.length
```

## 83. `J-cyclemin-prefix-two-even-eoe` &mdash; covers 0.33

*Reads as: the claim asserts more than the declarations state (0.82).*

*Claim broader 0.82; declaration narrower 0.24; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every n ≥ 2, every k ≥ 6, and every prefix u, the itinerary u ++ O^{k-3}EOE is not a Juggler CycleMin at n. The same prefix transport applies: y ≥ n tightens the leftover cell against the shared two-even tail at y, using the last-odd cube reduction already used for O^{k-3}EOE. Large y is y ≥ 256. Below 256 the argument is returnsIntoB tables at k = 6,7,8,9 and seven-odd for k ≥ 10. The case y = n reduces to no_cycle_itinerary_two_even_eoe. Lean theorem no_cycleMin_prefix_two_even_eoe. This excludes that one last-cluster class only; it is not a CycleItinerary theorem at a non-minimum start, not a bunched-short attack, not a length-11 census, and not a halt theorem.

**Declaration.** `no_cycleMin_prefix_two_even_eoe` &mdash; kernel-checked, `Problems/Juggler/PrefixTwoEven.lean:363`

> No CycleMin word ends in the two-even leftover `twoEvenEOE k`, `k >= 6`, after any prefix `u`.

```lean
theorem no_cycleMin_prefix_two_even_eoe {n k : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hk : 6 ≤ k) :
    ¬CycleMin n (u ++ twoEvenEOE k)
```

## 84. `J-cycle-fixed-residue-witness` &mdash; covers 0.34

*Reads as: the claim asserts more than the declarations state (0.64).*

*Claim broader 0.64; declaration narrower 0.56; different result 0.23.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Appendix E.6, explicit formal witness. For every requested modulus q>0, c=512q-1 and b=c^3 yield two prescribed OOE first-return blocks in the same full cubic threshold band and the same section. The source, first image and endpoint are odd, all six threshold edges and first-return memberships are proved, and the final E-source parities differ. The records agree in source/first-image/endpoint/natural-aggregate residues modulo q, exact first remainder zero, and exact aggregate 2-adic valuation three. No classifier of this record can give both hidden parities correctly, even when supplied the exact common threshold and section boundary. The general positive free-b Taylor construction remains written. These blocks are not asserted periodic points; no impossibility for full absolute-va  *(truncated; read the ledger row)*

**Declarations.** `guardResidueFamily_no_record_classifier` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:691`

> The record cannot determine hidden parity even with the exact common band and section.

```lean
theorem guardResidueFamily_no_record_classifier (q : ℕ) (hq : 0 < q) :
    ¬ ∃ f : ℕ → ℕ → (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ,
      ∀ c : ℤ, 511 ≤ c → c%4=3 →
        f ((guardResidueTMinus c).toNat^2) ((guardResidueZPlus c).toNat+1)
          (guardResidueRecord q (guardResidueTPlus c).toNat
          (guardResidueZPlus c).toNat) = (guardResidueVPlus c).toNat%2 ∧
        f ((guardResidueTMinus c).toNat^2) ((guardResidueZPlus c).toNat+1)
          (guardResidueRecord q (guardResidueTMinus c).toNat
          (guardResidueZMinus c).toNat) = (guardResidueVMinus c).toNat%2
```

**And.** `guardResidueParameter` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:514`

```lean
def guardResidueParameter (q : ℕ) : ℤ
```

**And.** `guardResidueParameter_valid` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:516`

```lean
theorem guardResidueParameter_valid {q : ℕ} (hq : 0 < q) :
    511 ≤ guardResidueParameter q ∧ guardResidueParameter q % 4 = 3 ∧
    (q:ℤ) ∣ guardResidueParameter q + 1
```

**And.** `guardResidueFamily_every_modulus` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:523`

```lean
theorem guardResidueFamily_every_modulus (q : ℕ) (hq : 0 < q) :
    ∃ c : ℤ, 511 ≤ c ∧ c%4=3 ∧
      ((guardResidueTPlus c).toNat^2)%q=((guardResidueTMinus c).toNat^2)%q ∧
      ((guardResidueTPlus c).toNat^3)%q=((guardResidueTMinus c).toNat^3)%q ∧
      (guardResidueZPlus c).toNat%q=(guardResidueZMinus c).toNat%q ∧
      Int.ModEq (q:ℤ) ((guardResidueTPlus c^2)^9-guardResidueZPlus c^8)
        ((guardResidueTMinus c^2)^9-guardResidueZMinus c^8) ∧
      (guardResidueVPlus c).toNat%2=1 ∧
      (guardResidueVMinus c).toNat%2=0 ∧
      floorPower ((guardResidueTMinus c).toNat^2)=(guardResidueTMinus c).toNat^3 ∧
      floorPower ((guardResidueTMinus c).toNat^3)=(guardResidueVMinus c).toNat ∧
      floorPower (guardResidueVMinus c).toNat=(guardResidueZMinus c).toNat ∧
```

**And.** `guardResidueFamily_record_collision` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:674`

> Every positive fixed modulus gives equal records with opposite final guards.

```lean
theorem guardResidueFamily_record_collision (q : ℕ) (hq : 0 < q) :
    let c
```

**And.** `guardResidueRecord` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:669`

> The proposed finite residue record, with exact first remainder and aggregate valuation.

```lean
def guardResidueRecord (q a z : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
```

**And.** `guardResidue_ooe_traces` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:406`

```lean
theorem guardResidue_ooe_traces {c : ℤ} (hc : 511 ≤ c) (hm : c % 4 = 3) :
    Nat.sqrt (((guardResidueTPlus c).toNat ^ 2)^3) =
      (guardResidueTPlus c).toNat ^ 3 ∧
    Nat.sqrt (((guardResidueTPlus c).toNat ^ 3)^3) =
      (guardResidueVPlus c).toNat ∧
    Nat.sqrt (guardResidueVPlus c).toNat = (guardResidueZPlus c).toNat ∧
    Nat.sqrt (((guardResidueTMinus c).toNat ^ 2)^3) =
      (guardResidueTMinus c).toNat ^ 3 ∧
    Nat.sqrt (((guardResidueTMinus c).toNat ^ 3)^3) =
      (guardResidueVMinus c).toNat ∧
    Nat.sqrt (guardResidueVMinus c).toNat = (guardResidueZMinus c).toNat
```

**And.** `guardResidue_good_juggler_block` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:453`

```lean
theorem guardResidue_good_juggler_block {c : ℤ}
    (hc : 511 ≤ c) (hm : c % 4 = 3) :
    floorPower ((guardResidueTMinus c).toNat^2) =
      (guardResidueTMinus c).toNat^3 ∧
    floorPower ((guardResidueTMinus c).toNat^3) =
      (guardResidueVMinus c).toNat ∧
    floorPower (guardResidueVMinus c).toNat =
      (guardResidueZMinus c).toNat
```

**And.** `guardResidue_threshold_blocks` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:864`

> Both blocks execute their three prescribed edges under one full threshold map, even though their actual final source parities differ.

```lean
theorem guardResidue_threshold_blocks {c : ℤ}
    (hc : 511 ≤ c) (hm : c % 4 = 3) :
    let s
```

**And.** `guardResidue_common_band_and_section` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:783`

> The two residue-indistinguishable blocks share the same full threshold band and the same first-return section: all four endpoints are inside the section, and all four intermediate states are outside it.

```lean
theorem guardResidue_common_band_and_section {c : ℤ}
    (hc : 511 ≤ c) (hm : c % 4 = 3) :
    let s
```

**And.** `guardResidue_nat_parities` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:433`

```lean
theorem guardResidue_nat_parities {c : ℤ} (hc : 511 ≤ c) (hm : c % 4 = 3) :
    (guardResidueTPlus c).toNat % 2 = 1 ∧
    (guardResidueTMinus c).toNat % 2 = 1 ∧
    (guardResidueVPlus c).toNat % 2 = 1 ∧
    (guardResidueVMinus c).toNat % 2 = 0 ∧
    (guardResidueZPlus c).toNat % 2 = 1 ∧
    (guardResidueZMinus c).toNat % 2 = 1
```

**And.** `guardResidue_nat_record` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:486`

```lean
theorem guardResidue_nat_record {q : ℕ} {c : ℤ}
    (hc : 511 ≤ c) (hm : c % 4 = 3) (hq : (q:ℤ) ∣ c+1) :
    ((guardResidueTPlus c).toNat^2)%q=((guardResidueTMinus c).toNat^2)%q ∧
    ((guardResidueTPlus c).toNat^3)%q=((guardResidueTMinus c).toNat^3)%q ∧
    (guardResidueZPlus c).toNat%q=(guardResidueZMinus c).toNat%q ∧
    Int.ModEq (q:ℤ) ((guardResidueTPlus c^2)^9-guardResidueZPlus c^8)
      ((guardResidueTMinus c^2)^9-guardResidueZMinus c^8)
```

**And.** `guardResidue_nat_aggregate_record` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:644`

```lean
theorem guardResidue_nat_aggregate_record {q : ℕ} {c : ℤ}
    (hc : 511 ≤ c) (hm : c % 4 = 3) (hq : (q : ℤ) ∣ c + 1) :
    (((guardResidueTPlus c).toNat ^ 2) ^ 9 -
        (guardResidueZPlus c).toNat ^ 8) % q =
      (((guardResidueTMinus c).toNat ^ 2) ^ 9 -
        (guardResidueZMinus c).toNat ^ 8) % q
```

**And.** `guardResidue_first_remainders_zero` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:472`

```lean
theorem guardResidue_first_remainders_zero (c : ℤ) :
    ((guardResidueTPlus c).toNat^2)^3 -
      ((guardResidueTPlus c).toNat^3)^2 = 0 ∧
    ((guardResidueTMinus c).toNat^2)^3 -
      ((guardResidueTMinus c).toNat^3)^2 = 0
```

**And.** `guardResidue_aggregate_valuation` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:634`

```lean
theorem guardResidue_aggregate_valuation {c : ℤ}
    (hc : 511 ≤ c) (hm : c % 4 = 3) :
    padicValNat 2 (((guardResidueTPlus c).toNat ^ 2) ^ 9 -
        (guardResidueZPlus c).toNat ^ 8) = 3 ∧
      padicValNat 2 (((guardResidueTMinus c).toNat ^ 2) ^ 9 -
        (guardResidueZMinus c).toNat ^ 8) = 3
```

## 85. `J-cyclemin-fudge` &mdash; covers 0.34

*Reads as: the claim asserts more than the declarations state (0.72).*

*Claim broader 0.72; declaration narrower 0.42; different result 0.37.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The thirty first-expanding four-even short-gap leftovers O^{a0} E O^{a1} E O^{a2} E O^{a3} E are not CycleMin words. On a CycleMin every later state is >= n, so the exact cells compose by absorb_odd_step and absorb_even_step: n^A < (n+1)^B (x+1)^γ implies n^{A+γ} < (n+1)^{B+γ} (isqrt(x)+1)^{2γ}. After the prefix, cycle_trailing_evens_lt puts the image below (n+1)^{2^r}. Any 7-odd word that starts O keeps γ a power of two and raises on each later odd, so the slack is identically 3^7-2^{11}=139, independent of even placement. For n >= 30 and A <= 13905 the comparison is (n+1)^{A-139} < n^A; no n with 2 <= n < 30 follows any of the thirty prefixes. The eight leftovers whose only CycleMin-shaped rotation is themselves (OOOOOOOEEEE, OOOOOOEOEEE, OOOOOOEEEOE, OOOOOEOEEOE, OOOOOOEEOEE, OOOOOEOEOE  *(truncated; read the ledger row)*

**Declarations.** `no_cycleMin_cyclemin_fudge` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:806`

> The thirty first-expanding short-gap leftovers are not `CycleMin` words. Not a length-11 census.

```lean
theorem no_cycleMin_cyclemin_fudge {n : ℕ} {w : List Branch}
    (hw : w ∈ fudgeWords) (h : CycleMin n w) : False
```

**And.** `absorb_even_step` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:132`

> One CycleMin-crossing even step: `x < (T(x)+1)^2` and `(x+1)/x ≤ (n+1)/n`.

```lean
theorem absorb_even_step {n x A B γ : ℕ} (hn : 1 ≤ n)
    (h : n ^ A < (n + 1) ^ B * (x + 1) ^ γ)
    (hx : n ≤ x) (heven : x % 2 = 0) (hγ : γ ≠ 0) :
    n ^ (A + γ) <
      (n + 1) ^ (B + γ) * (floorPower x + 1) ^ (2 * γ)
```

**And.** `family_slack139` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:293`

```lean
theorem family_slack139 : (3 : ℕ) ^ 7 - 2 ^ 11 = 139
```

**And.** `no_cycle_itinerary_of_unique_fudge` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:832`

```lean
theorem no_cycle_itinerary_of_unique_fudge {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : w ∈ fudgeWords)
    (hu : onlySelfCycleMinShape w = true)
    (h : CycleItinerary n w) : False
```

**And.** `fourEvenWord` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:62`

```lean
def fourEvenWord (a0 a1 a2 a3 : ℕ) : List Branch
```

**And.** `plus_one_chain` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:548`

```lean
theorem plus_one_chain {n : ℕ} {pref : List Branch}
    (hn : 1 ≤ n) (h0 : pref.head? = some .odd) (hne : pref ≠ [])
    (hw : follows n pref)
    (hmin : ∀ j, j < pref.length → n ≤ floorPower^[j] n) :
    let s
```

**And.** `plus_one_vs_trailing` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:682`

```lean
theorem plus_one_vs_trailing {n : ℕ} {pref : List Branch} {r : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (h0 : pref.head? = some .odd)
    (hne : pref ≠ [])
    (h : CycleMin n (pref ++ List.replicate r Branch.even)) :
    let s
```

**And.** `exponents_starts_odd` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:227`

```lean
theorem exponents_starts_odd :
    ∀ w : List Branch, w.head? = some .odd →
      (exponentsAfter w).gamma = 2 ^ w.length ∧
        (exponentsAfter w).A =
          (exponentsAfter w).B + 3 ^ oddCount w
```

**And.** `slack139_of_seven_odd_length_eleven` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:741`

```lean
theorem slack139_of_seven_odd_length_eleven {pref : List Branch} {r : ℕ}
    (h0 : pref.head? = some .odd) (hodd : oddCount pref = 7)
    (hlen : pref.length + r = 11) :
    let s
```

**And.** `succ_pow_slack139_of_ge_30` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:618`

```lean
theorem succ_pow_slack139_of_ge_30 {n A : ℕ} (hn : 30 ≤ n)
    (hA : A ≤ 13905) (h139 : 139 ≤ A) :
    (n + 1) ^ (A - 139) < n ^ A
```

**And.** `no_follows_from2_below` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:665`

```lean
theorem no_follows_from2_below {w : List Branch} {N n : ℕ}
    (hn2 : 2 ≤ n) (hn : n < N)
    (h : noFollowsFrom2Below w N = true) : ¬follows n w
```

**And.** `unique_oooooooeeee` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:953`

```lean
theorem unique_oooooooeeee :
    onlySelfCycleMinShape (fourEvenWord 7 0 0 0) = true
```

**And.** `unique_ooooooeoeee` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:955`

```lean
theorem unique_ooooooeoeee :
    onlySelfCycleMinShape (fourEvenWord 6 1 0 0) = true
```

**And.** `unique_ooooooeeeoe` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:957`

```lean
theorem unique_ooooooeeeoe :
    onlySelfCycleMinShape (fourEvenWord 6 0 0 1) = true
```

**And.** `unique_oooooeoeeoe` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:959`

```lean
theorem unique_oooooeoeeoe :
    onlySelfCycleMinShape (fourEvenWord 5 1 0 1) = true
```

**And.** `unique_ooooooeeoee` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:961`

```lean
theorem unique_ooooooeeoee :
    onlySelfCycleMinShape (fourEvenWord 6 0 1 0) = true
```

**And.** `unique_oooooeoeoee` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:963`

```lean
theorem unique_oooooeoeoee :
    onlySelfCycleMinShape (fourEvenWord 5 1 1 0) = true
```

**And.** `unique_oooooeeoeoe` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:965`

```lean
theorem unique_oooooeeoeoe :
    onlySelfCycleMinShape (fourEvenWord 5 0 1 1) = true
```

**And.** `unique_ooooeoeoeoe` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:967`

```lean
theorem unique_ooooeoeoeoe :
    onlySelfCycleMinShape (fourEvenWord 4 1 1 1) = true
```

**And.** `no_cycle_itinerary_fudge_oooooooeeee` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:973`

> `OOOOOOOEEEE` closed by the fudge route, in `fourEvenWord` form like its seven siblings. `no_cycle_itinerary_oooooooeeee` in `O7EEEEGap` is stronger: it needs no `2 ≤ n`, and `itineraryO7EEEE` is this same list.

```lean
theorem no_cycle_itinerary_fudge_oooooooeeee {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 7 0 0 0)
```

**And.** `no_cycle_itinerary_ooooooeoeee` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:976`

```lean
theorem no_cycle_itinerary_ooooooeoeee {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 6 1 0 0)
```

**And.** `no_cycle_itinerary_ooooooeeeoe` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:979`

```lean
theorem no_cycle_itinerary_ooooooeeeoe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 6 0 0 1)
```

**And.** `no_cycle_itinerary_oooooeoeeoe` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:982`

```lean
theorem no_cycle_itinerary_oooooeoeeoe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 5 1 0 1)
```

**And.** `no_cycle_itinerary_ooooooeeoee` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:985`

```lean
theorem no_cycle_itinerary_ooooooeeoee {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 6 0 1 0)
```

**And.** `no_cycle_itinerary_oooooeoeoee` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:988`

```lean
theorem no_cycle_itinerary_oooooeoeoee {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 5 1 1 0)
```

**And.** `no_cycle_itinerary_oooooeeoeoe` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:991`

```lean
theorem no_cycle_itinerary_oooooeeoeoe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 5 0 1 1)
```

**And.** `no_cycle_itinerary_ooooeoeoeoe` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:994`

```lean
theorem no_cycle_itinerary_ooooeoeoeoe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 4 1 1 1)
```

## 86. `J-fate-cylinder-corollary` &mdash; covers 0.34

*Reads as: the claim asserts more than the declarations state (0.66).*

*Claim broader 0.66; declaration narrower 0.49; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Corollary 8.4 (the conjecture from a cylinder bound), as the composition of Theorem 8.3 in explicit form (row J-fate-tao-union-bound) with Theorem 7.2 (FateTaoReduction, tao_rate_implies_conjecture, the contagion bound of Theorem 5.3 as hypothesis). CylinderBound N₀ C A y is the paper's H(C, A) at the scale y: every O-rooted L(y)-bad cylinder of depth d(y) = ⌈C L(y)⌉ holds at most 2^{−(d−1)} y/2 + y (log y)^{−A} starts. (i) one_le_depth: d(y) ≥ 1 once 2y > N₀. (ii) oddFailures_eventually_le: for N₀ ≥ 2 with the floor, C ≥ 5, A > C + e(C), any e < e(C), and H(C, A) at all y ≥ y₁, there is y₀ with #{odd failures in (y, 2y]} ≤ y (log y)^{−e} for all y ≥ y₀; proof: Λ = log 2y / log N₀ satisfies log y / log N₀ ≤ Λ ≤ 2 log y / log N₀ for y ≥ 2, so the explicit bound y Λ^{−e(C)} + 2 Λ^C y  *(truncated; read the ledger row)*

**Declarations.** `cylinder_bound_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateCylinderCorollary.lean:185`

> **Corollary 8.4.** If the cylinder hypothesis `H(C, A)` holds at all large scales with `C ≥ 5` and `A > C + e(C)`, and the contagion bound of Theorem 5.3 holds for the failure set with an exponent `λ` satisfying `1 - λ < e(C)`, then every positive integer reaches `1`.

```lean
theorem cylinder_bound_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C A : ℝ) (hC : 5 ≤ C)
    (hA : C + chernoffExponent C < A)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ C A y)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hlam : 1 - lam < chernoffExponent C)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) → ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x) :
    ∀ n, 1 ≤ n → ReachesOne n
```

**And.** `CylinderBound` &mdash; kernel-checked, `Problems/Juggler/FateCylinderCorollary.lean:35`

> The cylinder hypothesis `H(C, A)` at the scale `y`: every `O`-rooted `L(y)`-bad cylinder of depth `d(y) = ⌈C L(y)⌉` holds at most `2^{-(d-1)} y/2 + y (log y)^{-A}` starts.

```lean
def CylinderBound (N₀ : ℕ) (C A : ℝ) (y : ℕ) : Prop
```

**And.** `one_le_depth` &mdash; kernel-checked, `Problems/Juggler/FateCylinderCorollary.lean:41`

> The depth is positive as soon as `2y > N₀`.

```lean
theorem one_le_depth {N₀ y : ℕ} (hN : 2 ≤ N₀) (hy : N₀ < 2 * y) {C : ℝ} (hC : 0 < C) :
    1 ≤ depth C N₀ y
```

**And.** `oddFailures_eventually_le` &mdash; kernel-checked, `Problems/Juggler/FateCylinderCorollary.lean:61`

> **The absorption.** Under `H(C, A)` at all large scales, with `A > C + e(C)`, the odd failures in `(y, 2y]` number at most `y (log y)^{-e}` for every `e < e(C)` and all large `y`.

```lean
theorem oddFailures_eventually_le {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C A e : ℝ) (hC : 5 ≤ C)
    (hA : C + chernoffExponent C < A) (he : e < chernoffExponent C)
    (hcyl : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → CylinderBound N₀ C A y) :
    ∃ y₀ : ℕ, ∀ y, y₀ ≤ y → ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)
```

## 87. `J-paper-b-defect-coefficient-chain` &mdash; covers 0.34

*Reads as: the claim asserts more than the declarations state (0.81).*

*Claim broader 0.81; declaration narrower 0.36; different result 0.13.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** Paper B section 7's per-letter coefficient rule, as an identity rather than a table. For a word w over {O,E} write p_q = 3/2 if letter q is O and 1/2 if it is E, and e_t = prod_{q<=t} p_q, so J^t(n) sits at scale n^{e_t}. For letters s < t the coefficient of the phase variable theta_s inside letter t's phase is (k/2) E at exponent e_{t-1} - e_s, where E = prod_{q=s+1}^{t-1} p_q. Proof: letter t's wave is e(k J^{t-1}/2), and J^{t-1} depends on theta_s only through the chain of power maps between them; composing power maps composes to a single power, so the chain contributes exactly the product of its step exponents. The identity that makes this a rule and not a table is E = e_{t-1}/e_s, checked on every word of length 3..10 and every pair s < t -- 75768 instances, no exception. It reproduce  *(truncated; read the ledger row)*

**Declarations.** `chain_rule` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:96`

> **The chain rule.** `E = e_{t-1} / e_s`: the product of the step exponents strictly between letters `s` and `t` is the ratio of the iterate exponents at `t-1` and at `s`. `pre` is the prefix of length `s`, so `iter pre = e_s`; `mid` is the block of letters `s+1 … t-1`, so `iter mid = E` and `iter (pre ++ mid) = e_{t-1}`.

```lean
theorem chain_rule (pre mid : List Letter) :
    iter mid = iter (pre ++ mid) / iter pre
```

**And.** `step` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:53`

> The per-letter power map `p_q`: `3/2` after an odd letter, `1/2` after an even one. These are the only two values a Juggler step contributes.

```lean
def step : Letter → ℚ
  | Letter.O => 3 / 2
  | Letter.E => 1 / 2

/-- `iter w = ∏ p_q` over the letters of `w`.  For a prefix of length `t` this is
the iterate exponent `e_t`, so that `J^t(n)` sits at scale `n^(e_t)`. -/
def iter (w : List Letter) : ℚ
```

**And.** `iter` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:59`

> `iter w = ∏ p_q` over the letters of `w`. For a prefix of length `t` this is the iterate exponent `e_t`, so that `J^t(n)` sits at scale `n^(e_t)`.

```lean
def iter (w : List Letter) : ℚ
```

**And.** `iter_pos` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:72`

> Every iterate exponent is positive. This is the only fact about the values `3/2` and `1/2` that the criterion below uses.

```lean
theorem iter_pos (w : List Letter) : 0 < iter w
```

**And.** `iter_split` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:83`

> **Splitting.** `e` over a concatenation is the product of the two pieces. This is the composition of power maps, and everything below is a consequence.

```lean
theorem iter_split (pre mid : List Letter) :
    iter (pre ++ mid) = iter pre * iter mid
```

**And.** `coeff` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:102`

> The coefficient of `θ_s` in letter `t`'s phase, in units of `k`: it is `E / 2`, with `E` the composed map of `chain_rule`.

```lean
def coeff (mid : List Letter) : ℚ
```

**And.** `coeffExponent` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:105`

> The exponent that coefficient sits at: `e_{t-1} - e_s`.

```lean
def coeffExponent (pre mid : List Letter) : ℚ
```

**And.** `printed_thm53` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:285`

> Theorem 5.3's kernel monomial `(3k/4) n^(9/8)`: coefficient `3/4` in units of `k`, at exponent `9/8`.

```lean
theorem printed_thm53 :
    coeff [O] = 3 / 4 ∧ coeffExponent [O, O] [O] = 9 / 8
```

**And.** `printed_thm63_C` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:290`

> Theorem 6.3's `C = (9k/16) n^(3/16)`.

```lean
theorem printed_thm63_C :
    coeff [O, O, E] = 9 / 16 ∧ coeffExponent [O] [O, O, E] = 3 / 16
```

**And.** `printed_thm63_B` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:295`

> Theorem 6.3's `B = (3k/4) v^(1/4)`.

```lean
theorem printed_thm63_B :
    coeff [O] = 3 / 4 ∧ coeffExponent [E] [O] = 1 / 4
```

## 88. `J-cycle-ooe-polynomial-block` &mdash; covers 0.35

*Reads as: the claim asserts more than the declarations state (0.71).*

*Claim broader 0.71; declaration narrower 0.48; different result 0.22.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Proposition E.3, formal polynomial-block subset. For every odd r>=3, x=r^8+8,u=r^12+12r^4,v=r^18+18r^10+54r^2-1,z=r^9+9r-1 satisfy all three adjacent-square cells, x,u,z odd and v even, and the actual Juggler steps x->u->v->z. The direct iterate-three identity is proved. Kernel verified; this row does not cover the real-power quotient substitution estimates or assert a closed orbit.

**Declarations.** `ooeFamily_juggler_block` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:81`

```lean
theorem ooeFamily_juggler_block {r : ℕ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    floorPower (ooeFamilySource r) = ooeFamilyFirst r ∧
    floorPower (ooeFamilyFirst r) = ooeFamilySecond r ∧
    floorPower (ooeFamilySecond r) = ooeFamilyExit r
```

**And.** `ooeFamilySource` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:6`

```lean
def ooeFamilySource (r : ℕ) : ℕ
```

**And.** `ooeFamilyFirst` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:7`

```lean
def ooeFamilyFirst (r : ℕ) : ℕ
```

**And.** `ooeFamilySecond` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:8`

```lean
def ooeFamilySecond (r : ℕ) : ℕ
```

**And.** `ooeFamilyExit` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:9`

```lean
def ooeFamilyExit (r : ℕ) : ℕ
```

**And.** `ooeFamily_square_cells` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:11`

```lean
theorem ooeFamily_square_cells {r : ℕ} (hr : 3 ≤ r) :
    ooeFamilyFirst r ^ 2 ≤ ooeFamilySource r ^ 3 ∧
    ooeFamilySource r ^ 3 < (ooeFamilyFirst r + 1) ^ 2 ∧
    ooeFamilySecond r ^ 2 ≤ ooeFamilyFirst r ^ 3 ∧
    ooeFamilyFirst r ^ 3 < (ooeFamilySecond r + 1) ^ 2 ∧
    ooeFamilyExit r ^ 2 ≤ ooeFamilySecond r ∧
    ooeFamilySecond r < (ooeFamilyExit r + 1) ^ 2
```

**And.** `ooeFamily_parities` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:58`

```lean
theorem ooeFamily_parities {r : ℕ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    ooeFamilySource r % 2 = 1 ∧ ooeFamilyFirst r % 2 = 1 ∧
    ooeFamilySecond r % 2 = 0 ∧ ooeFamilyExit r % 2 = 1
```

**And.** `ooeFamily_iterate_three` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:264`

```lean
theorem ooeFamily_iterate_three {r : ℕ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    (floorPower^[3]) (ooeFamilySource r) = ooeFamilyExit r
```

## 89. `J-fate-minimal-failure-oo` &mdash; covers 0.35

*Reads as: the claim asserts more than the declarations state (0.61).*

*Claim broader 0.61; declaration narrower 0.33; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Proposition 6.3(i) and the first-letter trichotomy of Section 6.2. If some positive n does not reach 1, the failure set has a least positive member (exists_minimal_failure), and that member is odd with an odd image, i.e. an OO-type start (minimal_failure_odd_odd): an even member n ≥ 2 has the smaller positive member floor(sqrt n) (floorPower_even_lt), and an odd member with even image has the smaller positive member floor(sqrt(floor(n^{3/2}))) < n (floorPower_odd_even_two_step_lt). Stated for any forward-closed class excluding 1 (minimalMember_odd, minimalMember_image_odd). For a two-way closed class A, A n iff exactly one of: n even with J(n) ∈ A; n odd, J(n) even, J(n) ∈ A; n odd, J(n) odd, J(n) ∈ A (first_letter_trichotomy, first_letter_pieces_disjoint) — the three pieces of the  *(truncated; read the ledger row)*

**Declarations.** `minimal_failure_odd_odd` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:63`

> Paper C Proposition 6.3(i): the least failure, if the failure set is nonempty, is odd with an odd image — an `OO`-type start.

```lean
theorem minimal_failure_odd_odd {n : ℕ} (hn : 1 ≤ n)
    (hmin : MinimalMember (fun k => ¬ReachesOne k) n) :
    n % 2 = 1 ∧ floorPower n % 2 = 1
```

**And.** `exists_minimal_failure` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:77`

> The failure set, if nonempty on the positive integers, has a minimal member.

```lean
theorem exists_minimal_failure {n : ℕ} (hn : 1 ≤ n) (h : ¬ReachesOne n) :
    ∃ m, 1 ≤ m ∧ MinimalMember (fun k => ¬ReachesOne k) m
```

**And.** `minimalMember_odd` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:33`

> A minimal member `n ≥ 2` of a forward-closed class is odd: an even member has the smaller positive member `⌊√n⌋`.

```lean
theorem minimalMember_odd {A : ℕ → Prop} (hF : ForwardClosed A) {n : ℕ}
    (hn : 2 ≤ n) (hmin : MinimalMember A n) : n % 2 = 1
```

**And.** `minimalMember_image_odd` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:46`

> A minimal member `n ≥ 2` of a forward-closed class has an odd image: if `⌊n^{3/2}⌋` were even, `⌊√⌊n^{3/2}⌋⌋ < n` would be a smaller positive member.

```lean
theorem minimalMember_image_odd {A : ℕ → Prop} (hF : ForwardClosed A) {n : ℕ}
    (hn : 2 ≤ n) (hmin : MinimalMember A n) : floorPower n % 2 = 1
```

**And.** `first_letter_trichotomy` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:88`

> The first-letter trichotomy of a two-way closed class (Section 6.2): every member is exactly one of even with image in the class, `OE`-type with image in the class, or `OO`-type with image in the class.

```lean
theorem first_letter_trichotomy {A : ℕ → Prop} (hF : ForwardClosed A)
    (hB : BackwardClosed A) (n : ℕ) :
    A n ↔ (n % 2 = 0 ∧ A (floorPower n)) ∨
      (n % 2 = 1 ∧ floorPower n % 2 = 0 ∧ A (floorPower n)) ∨
      (n % 2 = 1 ∧ floorPower n % 2 = 1 ∧ A (floorPower n))
```

**And.** `first_letter_pieces_disjoint` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:104`

> The three pieces are pairwise disjoint.

```lean
theorem first_letter_pieces_disjoint (n : ℕ) :
    ¬ (n % 2 = 0 ∧ n % 2 = 1) ∧
      ¬ (n % 2 = 1 ∧ floorPower n % 2 = 0 ∧ floorPower n % 2 = 1)
```

## 90. `OST-np-origin-particular` &mdash; covers 0.35

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.26; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, from the origin an MSD word ws unfolds by variation of constants: foldSteps ws origin equals the particular sum −∑ A^{k-1-j} e3 w_j; this is not a bound on L_0

**Declaration.** `origin_particular` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:537`

> From the origin, an MSD word unfolds by variation of constants: `foldSteps ws origin = particularSum ws`.

```lean
theorem origin_particular (ws : List ℤ) :
    foldSteps ws origin = particularSum ws
```

## 91. `C-shortcut-welldefined` &mdash; covers 0.36

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.71; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust mixed.*

**Row.** The shortcut map C(n)=n/2 (even) or (3n+1)/2 (odd) is well-defined on positive integers, and {1,2} is a 2-cycle.

**Declarations.** `shortcutC_even` &mdash; kernel-checked, `Problems/Collatz/Shortcut.lean:11`

```lean
theorem shortcutC_even {n : ℕ} (h : Even n) : shortcutC n = n / 2
```

**And.** `shortcutC_odd` &mdash; kernel-checked, `Problems/Collatz/Shortcut.lean:15`

```lean
theorem shortcutC_odd {n : ℕ} (h : Odd n) : shortcutC n = (3 * n + 1) / 2
```

**And.** `shortcutC_one` &mdash; compiler-checked, `Problems/Collatz/Shortcut.lean:19`

```lean
theorem shortcutC_one : shortcutC 1 = 2
```

**And.** `shortcutC_two` &mdash; compiler-checked, `Problems/Collatz/Shortcut.lean:22`

```lean
theorem shortcutC_two : shortcutC 2 = 1
```

**And.** `shortcutC_terminal_cycle` &mdash; kernel-checked, `Problems/Collatz/Shortcut.lean:25`

```lean
theorem shortcutC_terminal_cycle :
    shortcutC 1 = 2 ∧ shortcutC 2 = 1
```

## 92. `J-even-count-le-three` &mdash; covers 0.36

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.43; different result 0.13.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** No n ≥ 2 realizes a Juggler cycle itinerary with at most three even letters (Paper A Theorem 3.22). Every CycleItinerary has a CycleMin rotation that starts OO, ends E, and is formally expanding; those itineraries are the odd-run family, the two-even leftovers (Theorem 3.12), the internal-E bootstrap, the seven bunched leftovers (Theorems 3.14–3.20), or the gapped leftovers (Theorems 3.13 and 3.21). The corollary is that a nontrivial cycle itinerary has length at least eleven (Paper A Corollary 3.23). Lean theorems no_cycle_itinerary_even_count_le_three and cycle_itinerary_length_ge_eleven in EvenCountThree.lean. This is an even-count assembler, not a length-9 or length-10 itinerary census, and not a halt theorem.

**Declarations.** `no_cycle_itinerary_even_count_le_three` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:532`

> **Even-count assembler.** No `n ≥ 2` realizes a cycle itinerary with at most three even letters. This is not a length census and not a halt theorem.

```lean
theorem no_cycle_itinerary_even_count_le_three {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) (he : evenCount w ≤ 3) : False
```

**And.** `cycleMin_starts_two_odds` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:56`

```lean
theorem cycleMin_starts_two_odds {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ rest, w = Branch.odd :: Branch.odd :: rest
```

**And.** `cycleMin_getLast_even` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:73`

```lean
theorem cycleMin_getLast_even {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    w.getLast? = some Branch.even
```

**And.** `no_cycleMin_odd_run` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:140`

```lean
theorem no_cycleMin_odd_run {n a : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a)
    (h : CycleMin n (List.replicate a Branch.odd ++ [Branch.even])) : False
```

**And.** `no_cycleMin_bootstrap_last_gap` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:151`

```lean
theorem no_cycleMin_bootstrap_last_gap {n : ℕ} {u : List Branch} {c : ℕ}
    (hn : 2 ≤ n) (hc : 2 ≤ c)
    (h : CycleMin n
      (u ++ [Branch.even] ++ List.replicate c Branch.odd ++ [Branch.even])) :
    False
```

**And.** `no_cycleMin_two_even` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:301`

```lean
theorem no_cycleMin_two_even {n a c : ℕ} (hn : 2 ≤ n) (_ha : 2 ≤ a)
    (h : CycleMin n
      (List.replicate a Branch.odd ++ [.even] ++
        List.replicate c Branch.odd ++ [.even])) : False
```

**And.** `no_cycleMin_three_even` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:343`

```lean
theorem no_cycleMin_three_even {n a b c : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a)
    (h : CycleMin n
      (List.replicate a Branch.odd ++ [.even] ++
        List.replicate b Branch.odd ++ [.even] ++
          List.replicate c Branch.odd ++ [.even])) : False
```

**And.** `no_cycleMin_even_count_le_three` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:473`

```lean
theorem no_cycleMin_even_count_le_three {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) (he : evenCount w ≤ 3) : False
```

**And.** `cycle_itinerary_length_ge_eleven` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:547`

> A nontrivial cycle itinerary has length at least eleven: four evens plus the expansion demand \(2^{|w|}<3^{\#O}\).

```lean
theorem cycle_itinerary_length_ge_eleven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : 11 ≤ w.length
```

## 93. `J-fate-cylinder-energy` &mdash; covers 0.37

*No failure mode above the line; coverage itself is doubtful.*

*Claim broader 0.41; declaration narrower 0.37; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Section 10(d), the counting half of the Parseval display. For an arbitrary finite set S of starts, write #[w] for the starts of S whose length-|w| itinerary is w (wordCount), D(w) = #[wO] - #[w]/2 for the first-letter bias (bias) and C_t = sum over |w| = t of #[w]^2 for the cylinder energy (energy). A cylinder splits into its two children, #[w] = #[wE] + #[wO] (wordCount_split), because the (t+1)-st letter of an itinerary is the parity of the t-th image (itinerary_succ_append). Hence sum over |w| = t of D(w)^2 = C_{t+1}/2 - C_t/4 exactly (sum_bias_sq), which is the second equality of the note's display; the algebra behind it is (b - (a+b)/2)^2 = (a^2+b^2)/2 - (a+b)^2/4. NOT formalized: the first equality, Parseval for the Walsh sums on the same starts -- no Walsh transform appears   *(truncated; read the ledger row)*

**Declarations.** `sum_bias_sq` &mdash; kernel-checked, `Problems/Juggler/FateCylinderEnergy.lean:114`

> **The counting identity of Section 10(d).** `Σ_{|w|=t} D(w)² = C_{t+1}/2 - C_t/4`, exactly. The Parseval form of the same quantity in terms of Walsh sums is not formalized.

```lean
theorem sum_bias_sq (S : Finset ℕ) (t : ℕ) :
    ∑ w ∈ allWords t, bias S w ^ 2 = energy S (t + 1) / 2 - energy S t / 4
```

**And.** `wordCount_split` &mdash; kernel-checked, `Problems/Juggler/FateCylinderEnergy.lean:47`

> A cylinder is the disjoint union of its two children: `#[w] = #[wE] + #[wO]`.

```lean
theorem wordCount_split (S : Finset ℕ) (w : List Branch) :
    wordCount S w = wordCount S (w ++ [Branch.even]) + wordCount S (w ++ [Branch.odd])
```

**And.** `itinerary_succ_append` &mdash; kernel-checked, `Problems/Juggler/FateCylinderEnergy.lean:34`

> The `(d+1)`-st letter of an itinerary is the parity of the `d`-th image, so depth grows by appending on the right.

```lean
theorem itinerary_succ_append (n d : ℕ) :
    itinerary n (d + 1) = itinerary n d ++ [bit (floorPower^[d] n)]
```

## 94. `J-global-defect-identity` &mdash; covers 0.37

*Reads as: the claim asserts more than the declarations state (0.57).*

*Claim broader 0.57; declaration narrower 0.5; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every realized finite Juggler word w, n^{3^{#O(w)}} = T_w(n)^{2^{|w|}} + Δ_w(n), where Δ is the recursively lifted accumulation of local floor remainders. Δ ≥ 0, so the power envelope is a corollary; Δ = 0 iff every local remainder vanishes; concatenation is the two-term power-gap lift, not an additive sum.

**Declarations.** `global_defect_identity` &mdash; kernel-checked, `Problems/Juggler/GlobalDefect.lean:181`

> Core identity: `n^{3^o} = T_w(n)^{2^k} + Δ_w(n)`.

```lean
theorem global_defect_identity {n : ℕ} {w : List Branch} (hw : follows n w) :
    n ^ (3 ^ oddCount w) =
      image n w ^ (2 ^ w.length) + globalDefect n w
```

**And.** `globalDefect` &mdash; kernel-checked, `Problems/Juggler/GlobalDefect.lean:80`

```lean
def globalDefect (n : ℕ) (w : List Branch) : ℕ
```

**And.** `global_defect_nonneg` &mdash; kernel-checked, `Problems/Juggler/GlobalDefect.lean:83`

```lean
theorem global_defect_nonneg (n : ℕ) (w : List Branch) :
    0 ≤ globalDefect n w
```

**And.** `power_bound_of_global_defect` &mdash; kernel-checked, `Problems/Juggler/GlobalDefect.lean:190`

> The envelope is the nonnegativity of the accumulated defect.

```lean
theorem power_bound_of_global_defect {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    PowerBound (image n w) n w.length (oddCount w)
```

**And.** `global_defect_eq_zero_iff_locals` &mdash; kernel-checked, `Problems/Juggler/GlobalDefect.lean:345`

```lean
theorem global_defect_eq_zero_iff_locals {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    globalDefect n w = 0 ↔
      ∀ i, (hi : i < w.length) →
        branchDefect w[i] (floorPower^[i] n) = 0
```

**And.** `global_defect_append` &mdash; kernel-checked, `Problems/Juggler/GlobalDefect.lean:379`

> Exact composition law. Not an additive cocycle.

```lean
theorem global_defect_append {n : ℕ} {u v : List Branch}
    (hu : follows n u) (hv : follows (image n u) v) :
    globalDefect n (u ++ v) =
      powGap (image n u ^ (2 ^ u.length)) (globalDefect n u)
        (3 ^ oddCount v) +
      powGap (image (image n u) v ^ (2 ^ v.length))
        (globalDefect (image n u) v) (2 ^ u.length)
```

## 95. `BTL-reconstruct` &mdash; covers 0.39

*Reads as: a declaration is narrower than the claim (0.68).*

*Claim broader 0.64; declaration narrower 0.68; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** iterated reconstruction: f(n_w + 3^k x) = sum_{i<k} rho_i 3^i + 3^k (D_w f)(x) for every word w of length k

**Declaration.** `iterated_reconstruction` &mdash; kernel-checked, `BTCalculus/PadicLifting.lean:43`

> `f(n_w + 3^k x) = Σ ρ_i 3^i + 3^k (𝔇_w f)(x)`, in packed form.

```lean
theorem iterated_reconstruction (f : ℤ[X]) :
    ∀ (w : List ℤ) (x : ℤ),
      eval (packTrits w x) f =
        packTrits (outputAlong w f) (eval x (residualAlong w f))
  | [], x => by
```

## 96. `J-cyclemin-prefix-bunched-eeoe` &mdash; covers 0.39

*Reads as: the claim asserts more than the declarations state (0.74).*

*Claim broader 0.74; declaration narrower 0.2; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every n ≥ 2, every a ≥ 5, and every prefix u, the itinerary u ++ O^a EEOE is not a Juggler CycleMin at n. The leftover cell lifts to y ≥ n against the EOEE tail already used for O^a EEOE. Large y is y ≥ 314 at a = 5 and y ≥ 256 at a ≥ 6. Below those cutoffs the argument is returnsIntoB tables and seven-odd for a ≥ 7. The case y = n reduces to no_cycle_itinerary_three_even_eeoe. Lean theorem no_cycleMin_prefix_eeoe. This excludes that one bunched family only; it is not a bunched-short attack, not a length-11 census, and not a halt theorem.

**Declaration.** `no_cycleMin_prefix_eeoe` &mdash; kernel-checked, `Problems/Juggler/PrefixBunched.lean:407`

> No CycleMin word ends in the bunched leftover `threeEvenEEOE a`, `a >= 5`, after any prefix `u`.

```lean
theorem no_cycleMin_prefix_eeoe {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 5 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEEOE a)
```

## 97. `OST-np-impulse-place` &mdash; covers 0.39

*Reads as: the claim asserts more than the declarations state (0.56).*

*Claim broader 0.56; declaration narrower 0.33; different result 0.09.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, the origin impulse A^r e3 equals (3 q_{r-1}, 3 q_{r-2}+q_{r-1}, q_r) with q_j=0 for j<0; this is the place-value dictionary for origin_particular, not a bound on L_0

**Declaration.** `iterateA_e3` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:776`

> `A^r e₃ = (3 q_{r-1}, 3 q_{r-2}+q_{r-1}, q_r)`. KNOWN place-value dictionary for `origin_particular`, not `L₀`.

```lean
theorem iterateA_e3 (r : ℕ) : iterateA r e3 = impulsePlace r
```

## 98. `J-cubic-critical-run-kernels` &mdash; covers 0.4

*Reads as: a declaration is narrower than the claim (0.56).*

*Claim broader 0.5; declaration narrower 0.56; different result 0.22.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Conditional kernels: a signed correction from positive N*l-B*l' with odd N that is not Critical retains v2(B)+v2(l')<=v2(l). Even endpoints with a difference divisible by four have sum divisible by four. Unit valuation drops and supplied per-edge bonuses telescope along any finite path. At the fixed rank counts, the defined integer runCost has increasing increments and a universally proved affine lower bound touching lengths53 and54. Exact evaluations plus finite summation show any positive block lengths summing780237, supplied costs at least runCost, odd-gap allowance4 and totalGap<=519999999^3-519999999 require at least14569 blocks. Numerical support/filter adapters give S>=7284 and T>=14571 from their explicitly supplied cardinality hypotheses. These statements do not extract the critic  *(truncated; read the ledger row)*

**Declarations.** `Critical` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:17`

> The signed correction has the same lowest nonzero binary place as the gap.

```lean
def Critical (l : ℕ) (r : ℤ) : Prop
```

**And.** `valuation_sub_of_lt` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:21`

> A difference with unequal input valuations takes the smaller valuation.

```lean
theorem valuation_sub_of_lt {X Y : ℕ} (hX : 0 < X)
    (hlt : padicValNat 2 X < padicValNat 2 Y) :
    (X : ℤ) - Y ≠ 0 ∧
      padicValInt 2 ((X : ℤ) - Y) = padicValNat 2 X
```

**And.** `noncritical_valuation_budget` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:59`

> A noncritical correction retains the full denominator valuation budget.

```lean
theorem noncritical_valuation_budget {N B l l' : ℕ} {r : ℤ}
    (hN : 0 < N) (hB : 0 < B) (hl : 0 < l) (hl' : 0 < l')
    (hodd : N % 2 = 1)
    (hr : r = (N : ℤ) * l - (B : ℤ) * l')
    (hnoncritical : ¬Critical l r) :
    padicValNat 2 B + padicValNat 2 l' ≤ padicValNat 2 l
```

**And.** `even_sum_dvd_four_of_gap` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:84`

> An even pair whose difference is divisible by four also has such a sum.

```lean
theorem even_sum_dvd_four_of_gap {a b : ℕ} (hab : a ≤ b)
    (heven : a % 2 = 0 ∧ b % 2 = 0) (hgap : 4 ∣ b - a) :
    4 ∣ a + b
```

**And.** `weighted_run_budget` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:90`

> Per-edge unit drops and extra bonuses add along a finite path.

```lean
theorem weighted_run_budget (v bonus : ℕ → ℕ) (d : ℕ)
    (hstep : ∀ i < d, v (i + 1) + 1 + bonus i ≤ v i) :
    v d + d + ∑ i ∈ Finset.range d, bonus i ≤ v 0
```

**And.** `runIncrement` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:102`

> The marginal cost after the terminal even gap, at the fixed rank counts.

```lean
def runIncrement (t : ℕ) : ℕ
```

**And.** `runCost` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:105`

> Lower cost of a block of even gaps; the empty block has cost zero.

```lean
def runCost (n : ℕ) : ℕ
```

**And.** `runIncrement_monotone` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:108`

```lean
theorem runIncrement_monotone : Monotone runIncrement
```

**And.** `runCost_succ` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:114`

```lean
theorem runCost_succ {n : ℕ} (hn : 0 < n) :
    runCost (n + 1) = runCost n + runIncrement (n - 1)
```

**And.** `runCost_affine_53` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:125`

> A supporting affine line touches the block cost at lengths 53 and 54.

```lean
theorem runCost_affine_53 {n : ℕ} (hn : 0 < n) :
    runCost 53 + n * runIncrement 52 ≤ runCost n + 53 * runIncrement 52
```

**And.** `runIncrement_52` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:156`

```lean
theorem runIncrement_52 : runIncrement 52 = 9444732965739290427392
```

**And.** `runCost_53` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:159`

```lean
theorem runCost_53 : runCost 53 = 4387864922893216308702
```

**And.** `runCost_54` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:162`

```lean
theorem runCost_54 : runCost 54 = 13832597888632506736094
```

**And.** `affine_block_cost_sum` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:167`

> Sum a supplied affine lower cost over one finite family of blocks.

```lean
theorem affine_block_cost_sum {ι : Type*} [Fintype ι]
    (length cost : ι → ℕ) (A slope q oddGap totalGap : ℕ)
    (hcost : ∀ i, A + length i * slope ≤ cost i + q * slope)
    (hbudget : oddGap + ∑ i, cost i ≤ totalGap) :
    Fintype.card ι * A + (∑ i, length i) * slope + oddGap ≤
      totalGap + Fintype.card ι * (q * slope)
```

**And.** `run_cost_affine_budget` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:178`

> Consume actual block-cost lower bounds without assuming cyclic extraction.

```lean
theorem run_cost_affine_budget {ι : Type*} [Fintype ι]
    (length cost : ι → ℕ) (totalGap : ℕ)
    (hlength : ∀ i, 0 < length i)
    (hcost : ∀ i, runCost (length i) ≤ cost i)
    (hbudget : 4 + ∑ i, cost i ≤ totalGap) :
    Fintype.card ι * runCost 53 + (∑ i, length i) * runIncrement 52 + 4 ≤
      totalGap + Fintype.card ι * (53 * runIncrement 52)
```

**And.** `fixed_critical_count_lower` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:192`

> The exact fixed-tuple scalar budget forces at least 14569 blocks.

```lean
theorem fixed_critical_count_lower {C totalGap : ℕ}
    (hgap : totalGap ≤ 519999999 ^ 3 - 519999999)
    (hcost : C * runCost 53 + 780237 * runIncrement 52 + 4 ≤
      totalGap + C * (53 * runIncrement 52)) : 14569 ≤ C
```

**And.** `fixed_run_budget_critical_count_lower` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:201`

> Conditional arithmetic consumer for positive block lengths and gap costs.

```lean
theorem fixed_run_budget_critical_count_lower {ι : Type*} [Fintype ι]
    (length cost : ι → ℕ) (totalGap : ℕ)
    (hlength : ∀ i, 0 < length i) (hsum : ∑ i, length i = 780237)
    (hcost : ∀ i, runCost (length i) ≤ cost i)
    (hbudget : 4 + ∑ i, cost i ≤ totalGap)
    (hgap : totalGap ≤ 519999999 ^ 3 - 519999999) :
    14569 ≤ Fintype.card ι
```

**And.** `fixed_deviation_lower` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:213`

> Numerical support adapter; the support inequality is an explicit input.

```lean
theorem fixed_deviation_lower {C S : ℕ} (hC : 14569 ≤ C)
    (hcover : C ≤ 1 + 2 * S) : 7284 ≤ S
```

**And.** `fixed_nonzero_lower` &mdash; kernel-checked, `Problems/Juggler/CubicConstraintFusion.lean:218`

> Numerical filter adapter; the two additional corrections are explicit inputs.

```lean
theorem fixed_nonzero_lower {C T : ℕ} (hC : 14569 ≤ C)
    (hfilter : C + 2 ≤ T) : 14571 ≤ T
```

## 99. `J-cyclemin-closure-threshold` &mdash; covers 0.4

*Reads as: a declaration is narrower than the claim (0.74).*

*Claim broader 0.37; declaration narrower 0.74; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Closure threshold for the no-cycle problem. If a Diophantine budget C · L^{−p} ≤ Λ holds on every nontrivial Juggler cycle and cycle minima satisfy the matching lower bound n log n > (2/C) L^{p+1}, then every CycleMin word based at a minimum n ≥ 2 is empty: there is no nontrivial cycle (no_cycleMin_of_gap_and_minimum). Neither hypothesis is proved here; the theorem is the implication. It puts a number on the standing reopen condition of juggler_cycle_method_ceilings, "a lower bound on the cycle minimum in terms of the period": the unconditional target is n ≫ L^{5.1163051} via Wu–Wang, against n ≫ L^{14.3} via Rhin, and since p ≥ 1 for every irrational by Dirichlet no instance of the scheme ever asks for less than n ≫ L^{2}. The finance survivors sit at n log n ≍ L^{2} (ratio n log n / L^{2  *(truncated; read the ledger row)*

**Declaration.** `no_cycleMin_of_gap_and_minimum` &mdash; kernel-checked, `Problems/Juggler/GapTransferWW.lean:145`

> **The closure threshold.** If the Diophantine budget holds on every nontrivial cycle and cycle minima obey the matching lower bound `n log n > (2/C) L^{p+1}`, then every cycle word based at a minimum `n >= 2` is empty: there is no nontrivial cycle. This is the numerical content of the standing reopen condition "a lower bound on the cycle minimum in terms of the period" (`docs/problems/juggler_cycle_method_ceilings.md`). Neither hypothesis is proved here. The Wu-Wang instance `p = 4.1163051` sets the unconditional target at `n >> L^{5.1163051}`; since `p >= 1` for every irrational, no instance of this scheme can ask for less than `n >> L^{2}`.

```lean
theorem no_cycleMin_of_gap_and_minimum {C p : ℝ}
    (hC0 : 0 < C) (hC1 : C ≤ 1) (hp : 0 ≤ p)
    (hgap : ∀ (m : ℕ) (v : List Branch), 2 ≤ m → CycleMin m v → 0 < v.length →
      C * (v.length : ℝ) ^ (-p) ≤
        (oddCount v : ℝ) * Real.log 3 - (v.length : ℝ) * Real.log 2)
    (hmin : ∀ (m : ℕ) (v : List Branch), 2 ≤ m → CycleMin m v → 0 < v.length →
      2 / C * (v.length : ℝ) ^ (p + 1) < (m : ℝ) * Real.log m)
    {n : ℕ} {w : List Branch} (hn : 2 ≤ n) (h : CycleMin n w) :
    w.length = 0
```

## 100. `J-cyclemin-period-lower-bound` &mdash; covers 0.4

*Reads as: a declaration is narrower than the claim (0.72).*

*Claim broader 0.61; declaration narrower 0.72; different result 0.09.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Floor-free period lower bound. Under the same budget C · L^{−p} ≤ Λ, a nontrivial Juggler cycle of minimum n has period L ≥ (C n log n / 2)^{1/(p+1)} (cycleMin_period_ge; Wu–Wang form cycleMin_period_ge_wuWang). This is Paper A Corollary 4.11 read as a bound on the period rather than the minimum, and it is the only proved statement in which a cycle's period grows with its minimum — the descent floor is a constant. The exponent in n rises from 1/14.3 = 0.0699 with Rhin to 1/5.1163051 = 0.1954 with Wu–Wang (wu-wang-2014-irrationality-measure-log3, |a + b log 2 + c log 3| ≥ H^{−4.1163051−ε} at a = 0, H = max(L, o) = L). Distinct from the fan-width cap of juggler_cycle_walk_fan_growth and from the REFUTED floor-level Baker transfer of juggler_cycle_gap_baker: no floor enters and nothing is exc  *(truncated; read the ledger row)*

**Declarations.** `cycleMin_period_ge` &mdash; kernel-checked, `Problems/Juggler/GapTransferWW.lean:106`

> **The same inequality read as a period lower bound.** Under the same Diophantine budget, a nontrivial cycle of minimum `n` has period at least `(C * n log n / 2)^{1/(p+1)}`. No descent floor enters: the bound grows with the minimum, which is the one direction the finite tables cannot supply. At `p = 13.3` (Rhin) the exponent in `n` is `1/14.3 = 0.0699...`; at `p = 4.1163051` (Wu-Wang) it is `1/5.1163051 = 0.1954...`.

```lean
theorem cycleMin_period_ge {n : ℕ} {w : List Branch} {C p : ℝ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hL : 0 < w.length)
    (hC0 : 0 < C) (hC1 : C ≤ 1) (hp : 0 ≤ p)
    (hgap : C * (w.length : ℝ) ^ (-p) ≤
              (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) :
    (C / 2 * ((n : ℝ) * Real.log n)) ^ (1 / (p + 1)) ≤ (w.length : ℝ)
```

**And.** `cycleMin_period_ge_wuWang` &mdash; kernel-checked, `Problems/Juggler/GapTransferWW.lean:175`

> **Wu-Wang period lower bound.** Every nontrivial cycle has `L >= (C n log n / 2)^{1/5.1163051}`, floor-free.

```lean
theorem cycleMin_period_ge_wuWang {n : ℕ} {w : List Branch} {C : ℝ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hL : 0 < w.length)
    (hC0 : 0 < C) (hC1 : C ≤ 1)
    (hWW : C * (w.length : ℝ) ^ (-(4.1163051 : ℝ)) ≤
             (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) :
    (C / 2 * ((n : ℝ) * Real.log n)) ^ (1 / (5.1163051 : ℝ)) ≤ (w.length : ℝ)
```

## 101. `J-fate-block-average-layer` &mdash; covers 0.4

*Reads as: the claim asserts more than the declarations state (0.74).*

*Claim broader 0.74; declaration narrower 0.45; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The exact layer of Paper C Proposition 4.4, the slow sum, the block count, and equation (4.1) given the paper's two remaining exponential-sum bounds as hypotheses. The block: the odd n of I(m') = [m'^{8/3}, (m'+1)^{8/3}) are exactly the odd n with m'^2 <= floor(n^{3/4}) < (m'+1)^2 (mem_oddBlock, through the landing window of Appendix D.1). The decomposition: U(m') is the disjoint union of the even-image parts of the fibers Phi(m) over the even m of the block, so |U(m')| is the sum of Lemma 4.2's evenImageCount over E(m') (U_card_eq); the whole block is the disjoint union of the fibers (oddBlock_card_eq). The expansion: 4|U(m')| = M + S1 + S2 + S12 exactly (four_card_U). The slow sum S1 = sum psi(floor(n^{3/4})) is the alternating sum of fiber sizes over the block (slowSum_eq_fibers); the f  *(truncated; read the ledger row)*

**Declarations.** `block_average_two_bounds` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:436`

> **Proposition 4.4, equation (4.1), given the two exponential-sum bounds.** The slow sum is proved (`slowSum_abs_le`); the fast sum and the product sum remain hypotheses.

```lean
theorem block_average_two_bounds {m' : ℕ} (hm : 1 ≤ m') {B : ℝ}
    (h₂ : |(fastSum m' : ℝ)| ≤ B) (h₁₂ : |(productSum m' : ℝ)| ≤ B) :
    |((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4| ≤ B / 2 + (m' + 1)
```

**And.** `oddBlock` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:69`

> The odd integers of the paper's `I(m') = [m'^{8/3}, (m'+1)^{8/3})`, written exactly with the landing window of Appendix D.1.

```lean
def oddBlock (m' : ℕ) : Finset ℕ
```

**And.** `mem_oddBlock` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:73`

> Membership in the block is the exact condition `m'² ≤ ⌊n^{3/4}⌋ < (m'+1)²`.

```lean
theorem mem_oddBlock {m' n : ℕ} :
    n ∈ oddBlock m' ↔ n % 2 = 1 ∧ m' ^ 2 ≤ cell34 n ∧ cell34 n < (m' + 1) ^ 2
```

**And.** `blockE` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:65`

> The paper's `E(m')`: the even `m` with `m'² ≤ m < (m'+1)²`.

```lean
def blockE (m' : ℕ) : Finset ℕ
```

**And.** `U` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:88`

> `U(m')`: the odd `n` of the block whose two floors are both even.

```lean
def U (m' : ℕ) : Finset ℕ
```

**And.** `U_card_eq` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:116`

> **The proposition's first sentence, exactly.** `U(m')` is the disjoint union of the even-image parts of the fibers `Φ(m)` over the even `m` of the block, so its size is the sum of the even-image counts of Lemma 4.2.

```lean
theorem U_card_eq (m' : ℕ) :
    (U m').card = ∑ m ∈ blockE m', FiberParity.evenImageCount m
```

**And.** `oddBlock_card_eq` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:93`

```lean
theorem oddBlock_card_eq (m' : ℕ) :
    (oddBlock m').card
      = ∑ m ∈ Finset.Ico (m' ^ 2) ((m' + 1) ^ 2), (FiberParity.oeFiber m).card
```

**And.** `four_card_U` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:156`

> **Expanding the two indicators**, exactly: `4|U(m')| = M + S₁ + S₂ + S₁₂`, where `M` is the number of odd integers of the block. This is the identity the paper's proof starts from; the three sums are what its exponential-sum estimates bound.

```lean
theorem four_card_U (m' : ℕ) :
    4 * ((U m').card : ℤ) = ((oddBlock m').card : ℤ) + slowSum m' + fastSum m' + productSum m'
```

**And.** `slowSum` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:145`

> `Σ ψ(n^{3/4})`, the slow sum.

```lean
def slowSum (m' : ℕ) : ℤ
```

**And.** `slowSum_eq_fibers` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:242`

> **The slow sum, fiber by fiber.** `S₁ = Σ_{m'² ≤ m < (m'+1)²} ψ(m) |Φ(m)|`: the parity of `⌊n^{3/4}⌋` is constant on a fiber, so the slow sum is an alternating sum of fiber sizes.

```lean
theorem slowSum_eq_fibers (m' : ℕ) :
    slowSum m' = ∑ m ∈ Finset.Ico (m' ^ 2) ((m' + 1) ^ 2),
      psi m * ((FiberParity.oeFiber m).card : ℤ)
```

**And.** `oeFiber_card_succ_diff` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:259`

> Consecutive fibers differ by at most two members (`m ≥ 1`): the fiber bounds `(2/3)m^{1/3} - 1 ≤ |Φ(m)| ≤ (2/3)(m+1)^{1/3} + 1` overlap, and `(m+2)^{1/3} - m^{1/3} ≤ (2/3) m^{-2/3} ≤ 2/3` by Bernoulli.

```lean
theorem oeFiber_card_succ_diff {m : ℕ} (hm : 1 ≤ m) :
    |((FiberParity.oeFiber m).card : ℤ) - ((FiberParity.oeFiber (m + 1)).card : ℤ)| ≤ 2
```

**And.** `slowSum_abs_le` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:312`

> **The slow sum is `O(m')`.** `|S₁| ≤ 2m' + (2/3)(m'+1)^{2/3} + 1`: the block is `m'` pairs of consecutive fibers, each contributing at most `2`, plus one fiber left over. This is the paper's "pair consecutive fibers, whose odd-point counts differ by at most 3, and bound the remaining end fiber", with `2` in place of `3`.

```lean
theorem slowSum_abs_le {m' : ℕ} (hm : 1 ≤ m') :
    |(slowSum m' : ℝ)| ≤ 2 * m' + (2 / 3 * ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1)
```

**And.** `oddBlock_card_ge` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:380`

> `(2m'+1)((2/3)m'^{2/3} - 1) ≤ M`: every fiber of the block has at least `(2/3)(m'²)^{1/3} - 1` members.

```lean
theorem oddBlock_card_ge {m' : ℕ} (hm : 1 ≤ m') :
    (2 * m' + 1) * (2 / 3 * (m' : ℝ) ^ ((2 : ℝ) / 3) - 1) ≤ ((oddBlock m').card : ℝ)
```

**And.** `oddBlock_card_le` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:355`

> `M ≤ (2m'+1)((2/3)(m'+1)^{2/3} + 1)`: every fiber of the block has at most `(2/3)((m'+1)²)^{1/3} + 1` members.

```lean
theorem oddBlock_card_le (m' : ℕ) :
    ((oddBlock m').card : ℝ) ≤ (2 * m' + 1) * (2 / 3 * ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1)
```

**And.** `oddBlock_quarter_close` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:403`

> A quarter of the block is `m'^{5/3}/3` up to `m' + 1`: the "in particular" of the proposition, before the parity sums enter.

```lean
theorem oddBlock_quarter_close {m' : ℕ} (hm : 1 ≤ m') :
    |((oddBlock m').card : ℝ) / 4 - (m' : ℝ) ^ ((5 : ℝ) / 3) / 3| ≤ m' + 1
```

**And.** `block_average_asymptotic` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:463`

> **The asymptotic form of Proposition 4.4 with an explicit error**, given the two bounds: `|U(m')|` is within `B/2 + 2(m'+1)` of `m'^{5/3}/3`. With `B = C m'^{11/9} log(m'+1)` this is the paper's `|U(m')| = m'^{5/3}/3 (1 + O(m'^{-4/9} log(m'+1)))`.

```lean
theorem block_average_asymptotic {m' : ℕ} (hm : 1 ≤ m') {B : ℝ}
    (h₂ : |(fastSum m' : ℝ)| ≤ B) (h₁₂ : |(productSum m' : ℝ)| ≤ B) :
    |((U m').card : ℝ) - (m' : ℝ) ^ ((5 : ℝ) / 3) / 3| ≤ B / 2 + 2 * (m' + 1)
```

**And.** `block_average_bound_two` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:479`

> Proposition 4.4 in the paper's shape with only the two exponential-sum hypotheses: for `m' ≥ 2` and both remaining sums at most `C m'^{11/9} log(m'+1)`, equation (4.1) holds with `C_B = C/2 + 2`.

```lean
theorem block_average_bound_two {m' : ℕ} (hm : 2 ≤ m') {C : ℝ}
    (h₂ : |(fastSum m' : ℝ)| ≤ C * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1))
    (h₁₂ : |(productSum m' : ℝ)| ≤ C * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1)) :
    |((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4|
      ≤ (C / 2 + 2) * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1)
```

## 102. `J-cycle-direction-change-contraction` &mdash; covers 0.42

*Reads as: the claim asserts more than the declarations state (0.77).*

*Claim broader 0.77; declaration narrower 0.54; different result 0.46.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For the prescribed return C=OOEOOEOE and every integer x>=2^24, 0<=x^(243/256)-F_C(x)<9/8. The kernel-checked seven-tail majorant is 63121/524288<1/8. For integers z>w>=2^24 with d=z-w>=2, 0<=F_C(z)-F_C(w)<(243/256)w^(-13/256)d+9/8<d. No parity hypothesis is needed for this prescribed-map inequality. The compiled even-gap and actual-cycle transfer layers supply its cycle use. Paper A Section3.12 and AppendixF; no no-cycle claim.

**Declarations.** `c_contract` &mdash; kernel-checked, `Problems/Juggler/ReturnWordBounds.lean:132`

```lean
theorem c_contract {x y : ℕ} (hx : 2 ^ 24 ≤ x) (hxy : x + 2 ≤ y) :
    (eval wordC y : ℝ) - eval wordC x < (y : ℝ) - x
```

**And.** `c_certificate` &mdash; kernel-checked, `Problems/Juggler/ReturnWordBounds.lean:14`

```lean
theorem c_certificate : DyadicCertificate 24 wordC cShifts
```

**And.** `c_dyadic_sum` &mdash; kernel-checked, `Problems/Juggler/ReturnWordBounds.lean:25`

```lean
theorem c_dyadic_sum : dyadicSum wordC cShifts = 1 + (63121 : ℝ) / 524288
```

**And.** `c_budget_lt` &mdash; kernel-checked, `Problems/Juggler/ReturnWordBounds.lean:35`

```lean
theorem c_budget_lt {m : ℝ} (hm : (2 : ℝ) ^ 24 ≤ m) : budget m wordC < 9 / 8
```

**And.** `c_loss` &mdash; kernel-checked, `Problems/Juggler/ReturnWordBounds.lean:46`

```lean
theorem c_loss {x : ℕ} (hx : 2 ^ 24 ≤ x) :
    0 ≤ (x : ℝ) ^ ((243 : ℝ) / 256) - eval wordC x ∧
      (x : ℝ) ^ ((243 : ℝ) / 256) - eval wordC x < 9 / 8
```

**And.** `c_slope_lt` &mdash; kernel-checked, `Problems/Juggler/ReturnWordBounds.lean:62`

```lean
theorem c_slope_lt {m : ℝ} (hm : (2 : ℝ) ^ 24 ≤ m) :
    (243 : ℝ) / 256 * m ^ ((-13 : ℝ) / 256) < 27 / 64
```

**And.** `c_pair_from_floor` &mdash; kernel-checked, `Problems/Juggler/ReturnWordBounds.lean:102`

```lean
theorem c_pair_from_floor {m : ℝ} (hm : (2 : ℝ) ^ 24 ≤ m) {x y : ℕ}
    (hmx : m ≤ x) (hxy : x ≤ y) :
    (eval wordC y : ℝ) - eval wordC x <
      ((243 : ℝ) / 256) * m ^ ((-13 : ℝ) / 256) * ((y : ℝ) - x) + 9 / 8
```

## 103. `J-cycle-itinerary-length-eighty-four-m-ge-three-or-ge-eighty-five` &mdash; covers 0.42

*Reads as: the claim asserts more than the declarations state (0.62).*

*Claim broader 0.62; declaration narrower 0.41; different result 0.21.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 84 with at least three odd-runs on a CycleMin rotation, or at least 85. At residual floor 261 the inv-sum form of cycleMin_finance (constant 1) plus a uniform odd-run height cap excludes every length-84 CycleMin with cycleCircuitCount ≤ 2: valleys ≤ m/n, first odds ≤ m/4217, later odds ≤ o/273845, evens ≤ e/n², using floorPower 261 = 4216 and floorPower 4217 = 273845. Lean theorems no_cycleMin_length_eighty_four_of_circuit_le_two and cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five in CycleHeightFinance.lean. This is not the 6/5 greedy packing of J-cycle-position-finance, not an exclusion of length 84 at m ≥ 3, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declarations.** `cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five` &mdash; kernel-checked, `Problems/Juggler/CycleHeightFinance.lean:921`

> If a nontrivial cycle exists, it is period `84` with at least three odd-runs on a `CycleMin` rotation, or else length at least `85`.

```lean
theorem cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (w.length = 84 ∧ ∃ k < w.length,
        CycleMin (floorPower^[k] n) (rotateItinerary w k) ∧
          3 ≤ cycleCircuitCount (rotateItinerary w k)) ∨
      85 ≤ w.length
```

**And.** `no_cycleMin_length_eighty_four_of_circuit_le_two` &mdash; kernel-checked, `Problems/Juggler/CycleHeightFinance.lean:824`

```lean
theorem no_cycleMin_length_eighty_four_of_circuit_le_two
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) (hL : w.length = 84)
    (hm : cycleCircuitCount w ≤ 2) : False
```

**And.** `no_length_eighty_four_circuit_le_two` &mdash; kernel-checked, `Problems/Juggler/CycleHeightFinance.lean:906`

> Length `84` with at most two odd-runs is impossible.

```lean
theorem no_length_eighty_four_circuit_le_two
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hL : w.length = 84) (h : CycleItinerary n w)
    {k : ℕ} (hk : k < w.length)
    (hmin : CycleMin (floorPower^[k] n) (rotateItinerary w k))
    (hm : cycleCircuitCount (rotateItinerary w k) ≤ 2) : False
```

**And.** `cycleMin_inv_sum_le_pack` &mdash; kernel-checked, `Problems/Juggler/CycleHeightFinance.lean:664`

```lean
theorem cycleMin_inv_sum_le_pack {n : ℕ} {w : List Branch}
    (hn : 261 ≤ n) (h : CycleMin n w) :
    ∑ i ∈ Finset.range w.length, (1 : ℝ) / (floorPower^[i + 1] n) ≤
      (cycleCircuitCount w : ℝ) / n +
        (cycleCircuitCount w : ℝ) / 4217 +
          (oddCount w : ℝ) / 273845 +
            ((w.length - oddCount w : ℕ) : ℝ) / (n * n)
```

**And.** `cycleMin_l84_inv_sum_le_cap` &mdash; kernel-checked, `Problems/Juggler/CycleHeightFinance.lean:787`

```lean
theorem cycleMin_l84_inv_sum_le_cap {n : ℕ} {w : List Branch}
    (hn : 261 ≤ n) (h : CycleMin n w)
    (hL : w.length = 84) (hm : cycleCircuitCount w ≤ 2)
    (ho : 53 ≤ oddCount w) :
    ∑ i ∈ Finset.range w.length, (1 : ℝ) / (floorPower^[i + 1] n) ≤
      (2 : ℝ) / 261 + (2 : ℝ) / 4217 + (84 : ℝ) / 273845 +
        (31 : ℝ) / 68121
```

**And.** `floorPower_two_hundred_sixty_one` &mdash; kernel-checked, `Problems/Juggler/CycleHeightFinance.lean:75`

```lean
theorem floorPower_two_hundred_sixty_one :
    floorPower 261 = 4216
```

**And.** `floorPower_four_thousand_two_hundred_seventeen` &mdash; kernel-checked, `Problems/Juggler/CycleHeightFinance.lean:79`

```lean
theorem floorPower_four_thousand_two_hundred_seventeen :
    floorPower 4217 = 273845
```

## 104. `BTN-expanding-right-inverse` &mdash; covers 0.43

*Reads as: the claim asserts more than the declarations state (0.64).*

*Claim broader 0.64; declaration narrower 0.26; different result 0.23.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Laboratory DZ is a left inverse of T: DZ(T(n))=n. Canonical T is the section I_{-lsd(n)}(n), not a constant-section I_a.

**Declarations.** `expandingD_eq_IZ_shape` &mdash; kernel-checked, `Problems/BalancedTernary/ExpandingD.lean:26`

> The expanding map in section shape: `T n = -lsdZ n + 3 * n`, i.e. the section `I_a` taken at the varying digit `a = -lsdZ n` rather than at a constant one.

```lean
theorem expandingD_eq_IZ_shape (n : ℤ) :
    expandingD n = -lsdZ n + 3 * n
```

**And.** `DZ_expandingD` &mdash; kernel-checked, `Problems/BalancedTernary/ExpandingD.lean:53`

> Laboratory `DZ` is a left inverse of `T`: `DZ (T n) = n`.

```lean
theorem DZ_expandingD (n : ℤ) : DZ (expandingD n) = n
```

## 105. `J-cycle-quartic-formal-defect` &mdash; covers 0.43

*Reads as: the claim asserts more than the declarations state (0.6).*

*Claim broader 0.6; declaration narrower 0.48; different result 0.37.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For actual periodic extrema with m>=5 and M<m^4, every selected quartic return has nonnegative loglog defect using multiplier 9/8 on lower cells and 3/4 on upper cells. Every actual F source has strictly positive defect, proved from the final guarded even-to-odd square step. Any finite actual return permutation has total defect card*log(9/8)-upper_count*log(3/2), and a selected family containing an F has positive total. The identification with the original chronological cycle counts remains a separate assembly obligation.

**Declarations.** `F_strict_upper_pow` &mdash; kernel-checked, `Problems/Juggler/QuarticDefect.lean:43`

```lean
theorem F_strict_upper_pow {C : Set ℕ} {m M x : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 4)
    (hx : x ∈ C) (hs : QuarticBand.Section m x) (ho : O x % 2 = 1) :
    F x ^ 8 < x ^ 9
```

**And.** `blockDefect_nonneg` &mdash; kernel-checked, `Problems/Juggler/QuarticDefect.lean:87`

```lean
theorem blockDefect_nonneg {C : Set ℕ} {m M x : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 4)
    (hx : x ∈ C) (hs : QuarticBand.Section m x) : 0 ≤ blockDefect m x
```

**And.** `blockDefect_pos_F` &mdash; kernel-checked, `Problems/Juggler/QuarticDefect.lean:115`

```lean
theorem blockDefect_pos_F {C : Set ℕ} {m M x : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 4)
    (hx : x ∈ C) (hs : QuarticBand.Section m x) (ho : O x % 2 = 1) :
    0 < blockDefect m x
```

**And.** `blockDefect_sum` &mdash; kernel-checked, `Problems/Juggler/QuarticDefect.lean:145`

```lean
theorem blockDefect_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (c : ι → ℕ) (p : Equiv.Perm ι)
    (hstep : ∀ i, c (p i) = QuarticBand.returnMap m (c i)) :
    ∑ i, blockDefect m (c i) =
      (Fintype.card ι : ℝ) * Real.log ((9 : ℝ) / 8) -
      ((upperIndices m c).card : ℝ) * Real.log ((3 : ℝ) / 2)
```

**And.** `selected_defect_sum_pos` &mdash; kernel-checked, `Problems/Juggler/QuarticDefect.lean:178`

```lean
theorem selected_defect_sum_pos {ι : Type*} [Fintype ι]
    {C : Set ℕ} {m M : ℕ} (D : PeriodicExtrema C m M)
    (hm : 5 ≤ m) (hM : M < m ^ 4) (c : ι → ℕ)
    (hc : ∀ i, c i ∈ C ∧ QuarticBand.Section m (c i))
    (hF : ∃ i, O (c i) % 2 = 1) : 0 < ∑ i, blockDefect m (c i)
```

**And.** `actual_sorted_positive_surplus` &mdash; kernel-checked, `Problems/Juggler/QuarticDefect.lean:189`

```lean
theorem actual_sorted_positive_surplus {C : Set ℕ} {m M : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) (htall : m ^ 3 ≤ M) :
    ∃ (e : ℕ) (c : Fin e → ℕ) (p : Equiv.Perm (Fin e)),
      0 < e ∧ StrictMono c ∧
      (∀ i, c i ∈ C ∧ QuarticBand.Section m (c i)) ∧
      (∀ x ∈ C, QuarticBand.Section m x → ∃ i, c i = x) ∧
      (∀ i, c (p i) = QuarticBand.returnMap m (c i)) ∧
      (∀ i, 0 ≤ blockDefect m (c i)) ∧
      (∃ i, O (c i) % 2 = 1 ∧ 0 < blockDefect m (c i)) ∧
      0 < (e : ℝ) * Real.log ((9 : ℝ) / 8) -
        ((upperIndices m c).card : ℝ) * Real.log ((3 : ℝ) / 2)
```

## 106. `BTA-fn-congr` &mdash; covers 0.45

*Reads as: the claim asserts more than the declarations state (0.56).*

*Claim broader 0.56; declaration narrower 0.27; different result 0.16.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** f equiv_k g iff 3^k divides (f-g)(n) for every integer n

**Declaration.** `equivK_iff_functionCongr` &mdash; kernel-checked, `BTCalculus/PolynomialFunctionsMod.lean:64`

> Prefix locality plus congruence preservation: ``≡_k`` is function congruence on all of ``ℤ``. Packed length-``k`` prefixes are a complete residue system modulo ``3^k``.

```lean
theorem equivK_iff_functionCongr (k : ℕ) (f g : ℤ[X]) :
    equivK k f g ↔ functionCongr k f g
```

## 107. `BTA-x3-Q-visible` &mdash; covers 0.45

*Reads as: the claim asserts more than the declarations state (0.66).*

*Claim broader 0.66; declaration narrower 0.57; different result 0.39.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** D^t(u^3) mod 3^K is determined by u mod 3^{max(1,t+K-1)}

**Declaration.** `q_visible_mod` &mdash; kernel-checked, `BTCalculus/MismatchedCubicQuotient.lean:66`

> `qCubic t u` modulo `3^K` sees only `u` modulo `3^s` once `t + K - 1 <= s`: congruent inputs give congruent cubic quotients.

```lean
theorem q_visible_mod {t K s : Nat}
    (hs : t + K - 1 ≤ s) (hs1 : 1 ≤ s) {u v : Int}
    (h : (3 : Int) ^ s ∣ u - v) :
    (3 : Int) ^ K ∣ qCubic t u - qCubic t v
```

## 108. `J-cyclemin-prefix-bunched-eooee` &mdash; covers 0.45

*Reads as: the claim asserts more than the declarations state (0.55).*

*Claim broader 0.55; declaration narrower 0.18; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every n ≥ 2, every a ≥ 4, and every prefix u, the itinerary u ++ O^a EOOEE is not a Juggler CycleMin at n. The leftover cell lifts to y ≥ n against the shared two-even tail at length a+2, which holds for y ≥ 256. Below 256 the argument is Fin 256 returnsIntoB tables at a = 4,5,6 and seven-odd thereafter. The case y = n reduces to no_cycle_itinerary_three_even_eooee. Lean theorem no_cycleMin_prefix_eooee. This excludes that one bunched family only; it is not a bunched-short attack, not a length-11 census, and not a halt theorem.

**Declaration.** `no_cycleMin_prefix_eooee` &mdash; kernel-checked, `Problems/Juggler/PrefixBunched.lean:559`

> No CycleMin word ends in the bunched leftover `threeEvenEOOEE a`, `a >= 4`, after any prefix `u`.

```lean
theorem no_cycleMin_prefix_eooee {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 4 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEOOEE a)
```

## 109. `J-fate-seed` &mdash; covers 0.45

*Reads as: the claim asserts more than the declarations state (0.74).*

*Claim broader 0.74; declaration narrower 0.36; different result 0.19.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Lemma 5.2 (seed). Every nonempty backward-closed A with a positive member contains some m ≥ 3 (exists_ge_three_of_backwardClosed: 1 maps to 2 maps to 4 through even blocks). For any such m and every y ≥ (m+1)^4, the log-mass of A on (√y, y] is at least c_A = (1 − 2/m^4)(3/8 · 1/(m+1) − 1/((m+1)^2 − 1)) (seed_lemma), and c_A > 0 (seed_constant_pos). Proof as in the paper: the even-block tree S_k of m lies in A and in [m^{2^k}, (m+1)^{2^k}); its log-mass grows by at least 1 − 2 m^{-2^k} per level; the product is at least 3/4 by the geometric series 1/(m^2 − 1) ≤ 1/8; at scale k = log2 log_{m+1} y the tree splits at floor(√y) into members above √y, members whose even blocks lie there, and at most one member equal to floor(√y). The integer form y = floor(x) is the paper's g_A(log x). K  *(truncated; read the ledger row)*

**Declarations.** `seed_lemma` &mdash; kernel-checked, `Problems/Juggler/FateSeed.lean:288`

> **Paper C Lemma 5.2 (seed).** If `A` is backward-closed and contains `m ≥ 3`, then for every `y ≥ (m+1)⁴`, `Σ_{√y < n ≤ y, n ∈ A} 1/n ≥ (1 - 2/m⁴) (3/8 · 1/(m+1) - 1/((m+1)² - 1))`.

```lean
theorem seed_lemma {A : ℕ → Prop} (hA : BackwardClosed A) {m : ℕ} (hm : 3 ≤ m) (hmA : A m)
    {y : ℕ} (hy : (m + 1) ^ 4 ≤ y) :
    (1 - 2 / (m : ℝ) ^ 4) * (3 / 8 / ((m : ℝ) + 1) - 1 / (((m : ℝ) + 1) ^ 2 - 1)) ≤
      halfLogMass A y
```

**And.** `exists_ge_three_of_backwardClosed` &mdash; kernel-checked, `Problems/Juggler/FateSeed.lean:40`

> Every nonempty backward-closed class (with a positive member) contains some `m ≥ 3`: `1 ↦ 2 ↦ 4` through even blocks.

```lean
theorem exists_ge_three_of_backwardClosed {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) : ∃ m, 3 ≤ m ∧ A m
```

**And.** `seed_constant_pos` &mdash; kernel-checked, `Problems/Juggler/FateSeed.lean:480`

> The seed constant is positive for `m ≥ 3`, so the seed is a usable `c₀ > 0` for `recursion_lemma`.

```lean
theorem seed_constant_pos {m : ℕ} (hm : 3 ≤ m) :
    0 < (1 - 2 / (m : ℝ) ^ 4) * (3 / 8 / ((m : ℝ) + 1) - 1 / (((m : ℝ) + 1) ^ 2 - 1))
```

**And.** `blockTree_mem` &mdash; kernel-checked, `Problems/Juggler/FateSeed.lean:62`

> The tree of a member lies in the class (Lemma 3.1).

```lean
theorem blockTree_mem {A : ℕ → Prop} (hA : BackwardClosed A) {m : ℕ} (hm : A m) :
    ∀ k, ∀ n ∈ blockTree m k, A n
```

**And.** `blockTree_bounds` &mdash; kernel-checked, `Problems/Juggler/FateSeed.lean:78`

> Level `k` of the tree lies in `[m^{2^k}, (m+1)^{2^k})`.

```lean
theorem blockTree_bounds (m : ℕ) : ∀ k, ∀ n ∈ blockTree m k,
    m ^ (2 ^ k) ≤ n ∧ n < (m + 1) ^ (2 ^ k)
```

**And.** `blockTree_logMass_succ_ge` &mdash; kernel-checked, `Problems/Juggler/FateSeed.lean:144`

> One level up multiplies the log-mass by at least `1 - 2 m^{-2^k}`.

```lean
theorem blockTree_logMass_succ_ge {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (1 - 2 * (1 / (m : ℝ)) ^ (2 ^ k)) * ∑ n ∈ blockTree m k, (1 : ℝ) / n ≤
      ∑ n ∈ blockTree m (k + 1), (1 : ℝ) / n
```

**And.** `sum_inv_pow_two_pow_le` &mdash; kernel-checked, `Problems/Juggler/FateSeed.lean:178`

> `Σ_{j=1}^{k} m^{-2^j} ≤ 1/(m² - 1)` for `m ≥ 2`.

```lean
theorem sum_inv_pow_two_pow_le {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    ∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1)) ≤ 1 / ((m : ℝ) ^ 2 - 1)
```

**And.** `blockTree_logMass_ge` &mdash; kernel-checked, `Problems/Juggler/FateSeed.lean:257`

> `ℓ(S_{k+1}) ≥ (3/4) ℓ(S_1) ≥ 0.375/(m+1)` for `m ≥ 3`.

```lean
theorem blockTree_logMass_ge {m : ℕ} (hm : 3 ≤ m) (k : ℕ) :
    3 / 8 / ((m : ℝ) + 1) ≤ ∑ n ∈ blockTree m (k + 1), (1 : ℝ) / n
```

## 110. `J-four-block-persistent-expanding` &mdash; covers 0.45

*No failure mode above the line; coverage itself is doubtful.*

*Claim broader 0.46; declaration narrower 0.32; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Four consecutive persistent expanding Juggler residual blocks exist: 1999 follows OOE to 5169, 5169 follows OOOOEE to 50093, 50093 follows OOE to 193753, and 193753 follows OOE to 887471. Each step is PersistentExpandingResidual.

**Declarations.** `four_consecutive_persistent_expanding_exists` &mdash; kernel-checked, `Problems/Juggler/ExpansionSlack.lean:246`

> Four consecutive persistent expanding residual blocks exist: `1999` to `5169` by `OOE`, `5169` to `50093` by `OOOOEE`, then `50093` to `193753` and `193753` to `887471` by `OOE`. Each step is a `PersistentExpandingResidual`.

```lean
theorem four_consecutive_persistent_expanding_exists :
    ∃ x y z u v,
      PersistentExpandingResidual x y ∧
        PersistentExpandingResidual y z ∧
          PersistentExpandingResidual z u ∧
            PersistentExpandingResidual u v
```

**And.** `four_block_pe_1999` &mdash; kernel-checked, `Problems/Juggler/ExpansionSlack.lean:215`

> Four consecutive expanding persistent residual blocks. This kills any uniform run bound `M ≤ 4`.

```lean
theorem four_block_pe_1999 :
    PersistentExpandingResidual 1999 5169 ∧
      PersistentExpandingResidual 5169 50093 ∧
      PersistentExpandingResidual 50093 193753 ∧
      PersistentExpandingResidual 193753 887471
```

## 111. `J-period-family-arithmetic-in-lean` &mdash; covers 0.45

*Reads as: the claim asserts more than the declarations state (0.6).*

*Claim broader 0.6; declaration narrower 0.42; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The integer arithmetic behind the cycle period-bound sequence is now kernel-checked. PeriodFamily.lean carries the convergent denominators q_0..q_15 of BETA = log2/log3 as a list, checks every one from q_2 on against the recurrence q_k = a_k q_(k-1) + q_(k-2) so the list is generated rather than asserted (denomsRec), and proves the facts the period sequence rests on: q_13 = 176251, q_14 = 301994, a_15 = 55, the family closure 176251 + 55 x 301994 = 16785921 (familyClosed), the identification of the three published bounds as j = 0, 1, 2 (periodBoundsAreFamily, over fanMember, giving 176251, 478245, 780239), the next member 1082233 (nextMember), the partial quotient itself (a15), that fanMember(55) is q_15 (lastMember), and that the family is strictly increasing (member_strictMono) so its me  *(truncated; read the ledger row)*

**Declarations.** `familyClosed` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:71`

> **The family closes.** The semiconvergents `q₁₃ + j q₁₄` reach `q₁₅` exactly at `j = 55`, which is why the family is finite and has `56` members rather than continuing indefinitely.

```lean
theorem familyClosed : 176251 + 55 * 301994 = 16785921
```

**And.** `betaQuotients` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:41`

> Partial quotients `a₁ … a₁₅` of `β = log 2 / log 3`, after the leading `a₀ = 0`. Stable to eighty terms across 200- and 400-digit arithmetic; only these are used.

```lean
def betaQuotients : List ℕ
```

**And.** `betaDenoms` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:44`

> Convergent denominators `q₀ … q₁₅` of `β`.

```lean
def betaDenoms : List ℕ
```

**And.** `recStep` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:48`

> One step of the convergent recurrence.

```lean
def recStep (a qk qkm1 : ℕ) : ℕ
```

**And.** `denomsRec` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:52`

> **The list is generated, not asserted.** Every denominator from `q₂` on is `a_k q_{k-1} + q_{k-2}`, so `betaDenoms` is determined by `betaQuotients`.

```lean
theorem denomsRec :
    ∀ k, 2 ≤ k → k < betaDenoms.length →
      betaDenoms.getD k 0
        = recStep (betaQuotients.getD (k - 1) 0)
            (betaDenoms.getD (k - 1) 0) (betaDenoms.getD (k - 2) 0)
```

**And.** `q13` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:60`

> `q₁₃`, the first member of the family and the first published period bound.

```lean
theorem q13 : betaDenoms.getD 13 0 = 176251
```

**And.** `q14` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:63`

> `q₁₄`, the step of the family.

```lean
theorem q14 : betaDenoms.getD 14 0 = 301994
```

**And.** `a15` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:66`

> `a₁₅ = 55`, the partial quotient that fixes the family's length.

```lean
theorem a15 : betaQuotients.getD 14 0 = 55
```

**And.** `fanMember` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:74`

> The `j`-th member of the family.

```lean
def fanMember (j : ℕ) : ℕ
```

**And.** `periodBoundsAreFamily` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:78`

> **The three published period bounds are `j = 0, 1, 2`.** `J-cyclemin-walk-charge-instance` at `176251`, then `478245`, then `780239`.

```lean
theorem periodBoundsAreFamily :
    (fanMember 0, fanMember 1, fanMember 2) = (176251, 478245, 780239)
```

**And.** `nextMember` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:83`

> The next member, which a certified floor at `554000000` would bank.

```lean
theorem nextMember : fanMember 3 = 1082233
```

**And.** `lastMember` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:86`

> The family's last member is `q₁₅`.

```lean
theorem lastMember : fanMember 55 = betaDenoms.getD 15 0
```

**And.** `member_strictMono` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:94`

> The family is strictly increasing, so the members really are successive bounds rather than a set to be searched in any order.

```lean
theorem member_strictMono : StrictMono fanMember
```

## 112. `OST-np-reset-prefix` &mdash; covers 0.45

*Reads as: the claim asserts more than the declarations state (0.65).*

*Claim broader 0.65; declaration narrower 0.31; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, if T_R(0)=0 then T_{RU}(0)=T_U(0); origin-reset prefixes do not create new terminals. This is particular_concat at c_R=0, not a bound on L_0

**Declaration.** `reset_prefix` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:609`

> Origin reset prefixes do not change the particular of a suffix. KNOWN `particular_concat` at `c_R=0`, not `L₀`.

```lean
theorem reset_prefix (r u : List ℤ) (hr : particularSum r = origin) :
    particularSum (r ++ u) = particularSum u
```

## 113. `BTA-x3-x` &mdash; covers 0.46

*Reads as: the claim asserts more than the declarations state (0.64).*

*Claim broader 0.64; declaration narrower 0.48; different result 0.55.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** x^3-x vanishes modulo 3 and its leading coefficient is not divisible by 3

**Declarations.** `X_pow_three_sub_X_vanishes_one` &mdash; kernel-checked, `BTCalculus/PolynomialFunctionsMod.lean:240`

> The first invisible cubic: ``X^3 - X`` vanishes modulo ``3``, but its leading coefficient is a unit.

```lean
theorem X_pow_three_sub_X_vanishes_one :
    vanishesMod 1 ((X : ℤ[X]) ^ 3 - X)
```

**And.** `not_three_dvd_coeff_X_pow_three_sub_X` &mdash; kernel-checked, `BTCalculus/PolynomialFunctionsMod.lean:246`

> `X^3 - X` vanishes as a function mod `3` while its degree-3 coefficient does not: vanishing is not coefficientwise.

```lean
theorem not_three_dvd_coeff_X_pow_three_sub_X :
    ¬ (3 : ℤ) ∣ coeff ((X : ℤ[X]) ^ 3 - X) 3
```

## 114. `BTN-expanding-lambda` &mdash; covers 0.46

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.25; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For T_λ(n)=3n-λ lsd(n), lsd(T_2(n))=lsd(n) and lsd(T_3(n))=0. The observational residual remains a trit; λ changes the residue map, not the need for the full integer.

**Declarations.** `lsdZ_expandingDGain_two` &mdash; kernel-checked, `Problems/BalancedTernary/ExpandingD.lean:141`

> Gain `2` fixes the digit rather than flipping it: `lsdZ (T_2 n) = lsdZ n`.

```lean
theorem lsdZ_expandingDGain_two (n : ℤ) :
    lsdZ (expandingDGain 2 n) = lsdZ n
```

**And.** `lsdZ_expandingDGain_three` &mdash; kernel-checked, `Problems/BalancedTernary/ExpandingD.lean:152`

> Gain `3` annihilates the digit: `lsdZ (T_3 n) = 0`.

```lean
theorem lsdZ_expandingDGain_three (n : ℤ) :
    lsdZ (expandingDGain 3 n) = 0
```

## 115. `J-paper-b-linearisation-E-lt-2` &mdash; covers 0.46

*Reads as: the claim asserts more than the declarations state (0.84).*

*Claim broader 0.84; declaration narrower 0.4; different result 0.14.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** The E < 2 linearisation criterion of Paper B section 7, as an identity. With the notation of J-paper-b-defect-coefficient-chain, the squared-defect term in letter t's phase sits at exponent e_{t-1} - 2 e_s, and since e_{t-1} = e_s E this equals e_s (E - 2). As e_s > 0 always, the second-order exponent is negative exactly when E < 2: linearising theta_s inside letter t is safe precisely on that condition. The criterion is therefore not a threshold fitted to the words that happen to survive -- it is the point at which the second-order term stops growing, and 2 is forced by the squaring and nothing else. Checked as an identity on every word of length 3..10 and every pair s < t (75768 instances, no exception), with the sign of the second-order exponent agreeing with E < 2 in every instance. Po  *(truncated; read the ledger row)*

**Declarations.** `linearise_iff` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:117`

> **The `E < 2` criterion.** The second-order exponent is negative exactly when `E < 2`. The equivalence is one-line given `second_order` and `iter_pos`, and that is the point: `2` is where the squared term stops growing, forced by the squaring and by nothing about which words survive.

```lean
theorem linearise_iff (pre mid : List Letter) :
    iter (pre ++ mid) - 2 * iter pre < 0 ↔ iter mid < 2
```

**And.** `second_order` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:109`

> **The second-order identity.** The squared-defect term sits at `e_{t-1} - 2 e_s`, and that equals `e_s (E - 2)`.

```lean
theorem second_order (pre mid : List Letter) :
    iter (pre ++ mid) - 2 * iter pre = iter pre * (iter mid - 2)
```

**And.** `no_linearise_iff` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:127`

> The companion direction, stated positively: a defect whose composed map reaches `2` has a second-order term that does not decay.

```lean
theorem no_linearise_iff (pre mid : List Letter) :
    0 ≤ iter (pre ++ mid) - 2 * iter pre ↔ 2 ≤ iter mid
```

**And.** `two_odd_not_safe` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:302`

> A worked instance of the criterion: two odd letters give `E = 9/4 ≥ 2`, so the defect two letters back may not be linearised — this is the `9/4` shape the screen's other threshold also names, here as a statement about `E` alone.

```lean
theorem two_odd_not_safe : ¬ (iter [O, O] < 2)
```

**And.** `odd_even_safe` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:306`

> One odd and one even give `E = 3/4 < 2`, which is safe.

```lean
theorem odd_even_safe : iter [O, E] < 2
```

## 116. `BTN-carry-gain-3` &mdash; covers 0.47

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.56; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The synthetic map T_3(c,d)=3 DZ(c+2d) satisfies c_n=3n along the all-+1 word, so the residual set is unbounded. This is not value-preserving normalization.

**Declarations.** `carryGain3_eq` &mdash; kernel-checked, `Problems/BalancedTernary/FiniteStateDynamics.lean:143`

> `carryGain3 n = 3n` along the all-`+1` word.

```lean
theorem carryGain3_eq (n : ℕ) : carryGain3 n = 3 * (n : ℤ)
```

**And.** `carryGain3_unbounded` &mdash; kernel-checked, `Problems/BalancedTernary/FiniteStateDynamics.lean:150`

> `carryGain3` is unbounded: no `B` bounds every `|carryGain3 n|`.

```lean
theorem carryGain3_unbounded (B : ℕ) :
    ∃ n : ℕ, B < (carryGain3 n).natAbs
```

## 117. `J-cycle-induced-count-determinant` &mdash; covers 0.48

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.61; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every word pair induced from (OOE,OE) by the two Euclidean substitutions, o(U)e(V)-o(V)e(U)=1 as an integer identity. Each word has coprime odd/even counts. For arbitrary natural section populations a,b, the expanded totals L=a|U|+b|V| and o=a o(U)+b o(V) satisfy gcd(L,o)=gcd(a,b). These count identities preserve the guards in separate actual-return interfaces; they alone do not construct a cycle.

**Declarations.** `InducedPair.count_determinant` &mdash; kernel-checked, `Problems/Juggler/ReturnWordFactorization.lean:36`

> Substitution preserves the unimodular matrix of letter counts.

```lean
theorem InducedPair.count_determinant {U V : List Branch} (h : InducedPair U V) :
    oddCount U * evenCount V = oddCount V * evenCount U + 1
```

**And.** `InducedPair.count_coprime` &mdash; kernel-checked, `Problems/Juggler/ReturnWordFactorization.lean:44`

> Both columns of the induced count matrix are primitive.

```lean
theorem InducedPair.count_coprime {U V : List Branch} (h : InducedPair U V) :
    Nat.Coprime (oddCount U) (evenCount U) ∧
      Nat.Coprime (oddCount V) (evenCount V)
```

**And.** `InducedPair.expanded_count_gcd` &mdash; kernel-checked, `Problems/Juggler/ReturnWordFactorization.lean:67`

> Expanded counts recover exactly the gcd of the two branch populations.

```lean
theorem InducedPair.expanded_count_gcd {U V : List Branch} (h : InducedPair U V)
    (a b : ℕ) :
    Nat.gcd (a * oddCount U + b * oddCount V)
      (a * evenCount U + b * evenCount V) = Nat.gcd a b
```

## 118. `J-fate-monotone-pairing-repair` &mdash; covers 0.49

*Reads as: the claim asserts more than the declarations state (0.69).*

*Claim broader 0.69; declaration narrower 0.43; different result 0.22.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Lemma 4.1' (monotone pairing), with a corrected proof and the same constant. Hypotheses of Lemma 4.1 (steps in [a, b], 0 < a ≤ b ≤ 1/2, b ≤ 21a/20, (H−1) a ≥ 12) plus monotone steps: each half-cell colour receives at least H/3 − 2 terms, in both cell conventions. The proof printed until 2026-09-08 claimed every pair of consecutive cells (ρ, ρ') has min ≥ (ρ+ρ')/3, deduced from a step scale that 'drops by at most X/21 spread over the cells'; monotonicity does not give gradual change, and a = 10/41, b = 21/82 with points −2a, −a, 0, a, 2a, 2a+b, 2a+2b, … (nondecreasing steps) has the interior pair (3, 1), ratio 1/4. It also paired the two partial end cells as if interior. Corrected proof: (a) for interior i < j, ρ_j ≤ ρ_i + 1, because the ρ_i + 1 steps across cell i span more than 1/  *(truncated; read the ledger row)*

**Declarations.** `sweep_monotone_fract_lt_half` &mdash; kernel-checked, `Problems/Juggler/FateSweepMonotone.lean:2357`

> Paper C Lemma 4.1′: at least `H/3 - 2` of the terms have `{x_j} < 1/2`.

```lean
theorem sweep_monotone_fract_lt_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | Int.fract (x j) < 1 / 2}
```

**And.** `sweep_monotone_cell` &mdash; kernel-checked, `Problems/Juggler/FateSweepMonotone.lean:2294`

> Paper C Lemma 4.1′ (monotone pairing), closed half-cells: each colour of `⌊2 x_j⌋` has at least `H/3 - 2` terms.

```lean
theorem sweep_monotone_cell (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : Steps x H a b) (hmono : MonoSteps x H ∨ AntiSteps x H) (v : ℤ) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ range H | cell (x j) ≡ v [ZMOD 2]}
```

**And.** `sweep_monotone_fract_ge_half` &mdash; kernel-checked, `Problems/Juggler/FateSweepMonotone.lean:2373`

> Paper C Lemma 4.1′: at least `H/3 - 2` of the terms have `{x_j} ≥ 1/2`.

```lean
theorem sweep_monotone_fract_ge_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | 1 / 2 ≤ Int.fract (x j)}
```

**And.** `sweep_monotone_ceil` &mdash; kernel-checked, `Problems/Juggler/FateSweepMonotone.lean:2389`

> Paper C Lemma 4.1′, left-open cells, by reflection `j ↦ -x_{H-1-j}`.

```lean
theorem sweep_monotone_ceil (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) (v : ℤ) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | ⌈2 * x j⌉ ≡ v [ZMOD 2]}
```

**And.** `sweep_monotone_rep_le_half` &mdash; kernel-checked, `Problems/Juggler/FateSweepMonotone.lean:2423`

> Paper C Lemma 4.1′, left-open cells: representative at most `1/2`.

```lean
theorem sweep_monotone_rep_le_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | x j - ⌈x j⌉ + 1 ≤ 1 / 2}
```

**And.** `sweep_monotone_rep_gt_half` &mdash; kernel-checked, `Problems/Juggler/FateSweepMonotone.lean:2438`

> Paper C Lemma 4.1′, left-open cells: representative above `1/2`.

```lean
theorem sweep_monotone_rep_gt_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | 1 / 2 < x j - ⌈x j⌉ + 1}
```

**And.** `fiber_card_le_succ` &mdash; kernel-checked, `Problems/Juggler/FateSweepMonotone.lean:113`

> **Fact (a).** With nondecreasing steps in `[a, b]`, `b ≤ 1/2`, a cell `j` after an interior cell `i` holds at most one point more than `i`.

```lean
theorem fiber_card_le_succ (hs : Steps x H a b) (hmono : MonoSteps x H) (ha : 0 < a)
    (_hb : b ≤ 1 / 2) (hH : 1 ≤ H) {i j : ℤ}
    (hi₀ : cell (x 0) < i) (hiH : i < cell (x (H - 1))) (hij : i < j) :
    #{r ∈ range H | cell (x r) = j} ≤ #{r ∈ range H | cell (x r) = i} + 1
```

