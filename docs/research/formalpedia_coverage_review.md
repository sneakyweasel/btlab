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

Jev (jev-1.13.0, last asked 2026-09-21) has answered
248 of the 248 resolved rows: 88 covered,
58 doubtful, 102 not covered; 160 are
listed below.

Short claims filed as not covered, the likeliest mis-joins: `BTN-sdr-finite-condition` (0.07), `BTA-x3-Q-def` (0.08), `BTN-sdr-lambda1-radius` (0.1), `BTA-x3-x` (0.12), `BTN-sdrg-lambda2-evens` (0.12), `BTN-carry-bound` (0.14), `BTA-x3-n1-sign` (0.19), `BTJ-comp` (0.23), `C-endpoint` (0.23).

## 1. `J-cycle-oe-quotient-parity-carry` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.96).*

*Claim broader 0.96; declaration narrower 0.66; different result 0.21.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Proposition E.2. For positive y and y^4<=N<(y+1)^4, let u=isqrt(N), c=u-y^2, d=(N-y^4) div (2y^2), h=min(d,2y). Then 0<=c<=2y and c<=h<=c+2. The exact 0/1/2 correction is recovered by the two adjacent square comparisons (baseline_zero_iff, baseline_one_iff, baseline_two_iff). For odd y, the hidden source u is even iff c is odd (square_guard_iff). With N=x^3 and an odd OE source, this is the exact internal guard. Kernel-verified quantified bounds and recovery; the sharpness example 93->896->29 is separately checked finite arithmetic. No arbitrary-word closure or cycle theorem is asserted.

**Declaration.** `baseline_bounds` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:17`

```lean
theorem baseline_bounds {N y : ℕ} (hy : 0 < y)
    (hc : y ^ 4 ≤ N ∧ N < (y + 1) ^ 4) :
    N.sqrt ≤ baseline N y ∧ baseline N y ≤ N.sqrt + 2
```

## 2. `J-cycle-periodic-return-height-strip` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.6; different result 0.12.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Theorem 3.39. For every actual cycle with attained minimum m>=5 and maximum M<m^3, t=isqrt(M) and z=F_OOE(m) satisfy t^3+2<=[z(z-2)]^2 and M+2<=(t+1)^2 (cycleMin_exact_return_seam). The periodic E-image section is exactly C intersect [m,O(m)); its extrema return images have a strict odd gap, derived from actual periodicity and injectivity rather than assumed. For m>=7, m^15<(m^3-M)^8 (cycleMin_height_strip), equivalently M<m^3-m^(15/8); the all-states version is cycleMin_all_states_height_strip. Every threshold cycle in the complementary top strip has a wrong-parity state (threshold_cycle_wrong_parity). Exact OE/OOE cells identify the odd endpoint z. The sharper fractional bound for t, maximum-odd-integer ceiling restatement, and full rank adjacency are separately written consequen  *(truncated; read the ledger row)*

**Declaration.** `cycleMin_height_strip` &mdash; kernel-checked, `Problems/Juggler/CubicReturnStrip.lean:24`

> A cycle spelled by the repository's exact `CycleMin` predicate has the same height restriction, without an additional parity or return hypothesis.

```lean
theorem cycleMin_height_strip {m M : ℕ} {w : List Branch}
    (h : CycleMin m w) (hm : 7 ≤ m) (hM : M < m ^ 3)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) :
    m ^ 15 < (m ^ 3 - M) ^ 8
```

## 3. `J-cyclemin-rotation-average` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.67; different result 0.17.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The rotation average Laplace bound (Paper A Proposition 5.5, quantitative half, previously human). For every ν > 0 the rotation average C*(ν) = (1/log 3)·∫_1^3 e^{ν(1−t)} t⁻² dt satisfies C*(ν) < 1/(log 3·ν) and the sharper Laplace bound C*(ν) ≤ (1 − 2/ν + 6/ν²)/(log 3·ν), hence the gap form (2/ν − 6/ν²)/(log 3·ν) ≤ 1/(log 3·ν) − C*(ν) consumed by the Theorem 5.8 window computation (rotation_average_lt, rotation_average_le, rotationAverage_lt, rotationAverage_le, rotationAverage_gap, RotationAverage.lean). No quadrature: the quadratic majorant 1/t² ≤ 1 − 2(t−1) + 3(t−1)² on [1,3] (inv_sq_le_quad; the product with t² is 1 + 4(t−1)³ + 3(t−1)⁴) turns the bound into an exact fundamental-theorem-of-calculus evaluation with explicit antiderivative (quadPrim, hasDerivAt_quadPrim), whose boundary   *(truncated; read the ledger row)*

**Declaration.** `hugCharge_sub_rotationAverage_le` &mdash; kernel-checked, `Problems/Juggler/RotationAverage.lean:361`

> **Theorem 5.7's printed display.** `|C_L − C_*(n')| ≤ 2 s(L)/L` with `C_*` the rotation average.

```lean
theorem hugCharge_sub_rotationAverage_le {n' : ℝ} (hn : 1 < n') {L : ℕ}
    (hL : 0 < L) :
    |hugCharge n' L - rotationAverage (Real.log n')|
      ≤ 2 * ((∑ i ∈ Finset.range 13, ostroDigit thetaDenomFn L 12 i : ℕ) : ℝ)
          / L
```

## 4. `J-fate-certified-thirty` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.64; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** A certified instance of the side condition of Paper C's unconditional criteria, at C = 30, with no audit script in the chain. Device: a logarithm is certified by an integer power comparison. If E <= e and x^n <= E^m then n log x <= m (log_le_of_pow_le); if e <= E and E^m <= x^n then m <= n log x (le_log_of_pow_le); and the base-two pair logb_two_le, le_logb_two. With Mathlib's Real.exp_one_gt_d9 and exp_one_lt_d9 pinning 2.718 <= e <= 2.719 (e_ge, e_le), six comparisons closed by norm_num give: log 2 <= 7/10 (from 2^10 <= 2.718^7), 2/3 <= log 2 (2.719^2 <= 2^3), 84/53 <= log_2 3 (2^84 <= 3^53), log_2 3 <= 149/94 (3^94 <= 2^149), 19/100 <= log(3049/2500) (2.719^19 <= (3049/2500)^100) and log(39/50) >= -1/4 ((50/39)^4 <= 2.718). Hence p_30 = pC 30 lies in [3049/5000, 61/100] (pC_thirty_ge, p  *(truncated; read the ledger row)*

**Declaration.** `chernoffExponent_thirty_gt` &mdash; kernel-checked, `Problems/Juggler/FateCertified.lean:261`

> **The certified instance.** `e(30) > 39/50`, with no audit script in the chain; in particular `e(30) > 39/50`, comfortably past the `27/40` side condition of every unconditional criterion.

```lean
theorem chernoffExponent_thirty_gt : 39 / 50 < chernoffExponent 30
```

## 5. `J-fate-classes-density-averaged` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.96).*

*Claim broader 0.96; declaration narrower 0.61; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Corollary 5.5 (fate contagion) at every 0 < lambda <= 100/203, each clause in its log-mass form and its dyadic-block form, as named theorems: (1) the reach-one class R, backward-closed and containing 1, has sum_{n in R, n <= x} 1/n >= K (log x)^lambda for x >= x_0 (Density.reachesOne_logMass_averaged) and natural density >= c (log y)^(lambda-1) on a dyadic block inside every large shell (reachesOne_natDensity_averaged); (2) if some start fails, the failures have the same bounds (Production.failures_logMass_averaged, Density.failures_natDensity_averaged); (3) the basin of any state m >= 1, the starts whose orbit passes through m, has them (basin_logMass_averaged, basin_natDensity_averaged) -- the paper's clause is the case of a periodic m, the basin of that cycle -- and so do the di  *(truncated; read the ledger row)*

**Declaration.** `reachesOne_natDensity_averaged` &mdash; kernel-checked, `Problems/Juggler/FateDyadicDensity.lean:290`

> **Corollary 5.5(1), dyadic-block form.**

```lean
theorem reachesOne_natDensity_averaged {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount ReachesOne y : ℝ)
```

## 6. `J-fate-share-law-layer` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.63; different result 0.04.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The exact layer of Paper C Section 4.3, the share law (Lemma 4.5) and Corollary 4.6. The expansion: along a fiber n_j = n_1 + 2(j-1) the phase x_j = n_j^{3/2}/2 (xval) equals x_1 + (3/2) sqrt(n_1) (j-1) + (3/4) (j-1)^2 / sqrt(n_1) + E_j with |E_j| <= (1/4)(j-1)^3 n_1^{-3/2} (xval_expansion); the Taylor step is, after v = sqrt(1+u), the polynomial inequality 0 <= 1 + (3/2)(v^2-1) + (3/8)(v^2-1)^2 - v^3 <= (v^2-1)^3/16 (taylor_three_halves), no derivative taken; on a fiber Phi(m) the remainder is at most (2/27)(m+1)/m^2 (xval_expansion_fiber), the paper's O(1/m) with a constant. The range: phi_beta(s) = beta s + s^2/3 has on [0,1] the range beta + 1/3 for beta >= 0, -beta - 1/3 for beta <= -2/3, and max(0, beta + 1/3) + (3/4) beta^2 between (phiRange; never exceeded, phi_sub_le; attained, ex  *(truncated; read the ledger row)*

**Declaration.** `xval_expansion` &mdash; kernel-checked, `Problems/Juggler/FateShareLaw.lean:60`

> **The fiber phase expanded about its first term.** With `x_j = xval n_j = n_j^{3/2}/2` and `n_j = n₁ + 2d`: `x_j = x₁ + (3/2)√n₁ d + (3/4) d²/√n₁ + E` where `|E| ≤ (1/4) d³/n₁^{3/2}`.

```lean
theorem xval_expansion {n₁ : ℕ} (hn : 1 ≤ n₁) (d : ℕ) :
    |xval (n₁ + 2 * d) - (xval n₁ + 3 / 2 * Real.sqrt n₁ * d + 3 / 4 * (d : ℝ) ^ 2 / Real.sqrt n₁)|
      ≤ 1 / 4 * (d : ℝ) ^ 3 / Real.sqrt n₁ ^ 3
```

## 7. `J-paper-b-count-is-the-level-zero-bad-count` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.27; different result 0.08.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** Paper B's non-contracting word count and Paper C's bad-word count are one function at two levels. N_d of Proposition 7.1 counts length-d words whose walk u_t = o_t log2(3) - t stays at or above 0; bad_word_count(L, d) counts those whose walk never reaches -L. Both are the same dynamic program over (steps, odd letters), written independently in paper_b_prefix_count and collision_large_sieve, and N_d = bad_word_count(0, d) exactly for d = 1 to 16 (1, 1, 2, 3, 4, 8, 13, 19, 38, 64, 128, 226, 367, 734, 1295, 2114). The agreement is exact and not approximate although one bound is strict and the other is not, because u_t = 0 would need 3^(o_t) = 2^t, which forces o_t = t = 0 (`three_pow_eq_two_pow`, `iter_eq_one_iff`, kernel-checked): the walk is never back at its starting level after a letter,   *(truncated; read the ledger row)*

**Declaration.** `iter_eq_one_iff` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:226`

> The walk is never back at its starting level after a letter: `e_t = 1` only for the empty word.

```lean
theorem iter_eq_one_iff (w : List Letter) : iter w = 1 ↔ w = []
```

## 8. `J-paper-b-screen-is-a-walk-condition` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.62; different result 0.07.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** All three conditions of Paper B section 7's screen are functions of the exponent walk u_t = o_t log2(3) - t alone, and two of them are unit conditions on it. With e_t = 2^(u_t) (J-paper-b-E-is-the-exponent-walk): the branch-run condition e_{s-1} < 2 is u_{s-1} < 1, an absolute height; the linearisation criterion E < 2 is u_{t-1} - u_s < 1, a climb; and the 9/4 stopping threshold e_{t-1} - e_s > 9/4 is 2^(u_{t-1}) - 2^(u_s) > 9/4. Checked over every word of length 3 to 11: 4204 letters with a blocked defect, no mismatch on any of the three. Non-contraction is a condition on the same walk (1 <= e_t, i.e. u_t >= 0), so the property defining a contractor and the property tripping the branch-run hypothesis are one constraint at thresholds 0 and 1. At step two the first forces the second: a pref  *(truncated; read the ledger row)*

**Declaration.** `noncontracting_two_forces` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:260`

> A prefix that has not contracted by step two is `OO`, and then `e_2 = 9/4`, which already exceeds the branch-run threshold `2`.

```lean
theorem noncontracting_two_forces (c d : Letter)
    (h₁ : 1 ≤ iter [c]) (h₂ : 1 ≤ iter [c, d]) :
    c = Letter.O ∧ d = Letter.O ∧ iter [c, d] = 9 / 4
```

## 9. `J-period-family-arithmetic-in-lean` &mdash; covers 0.03

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.57; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The integer arithmetic behind the cycle period-bound sequence is now kernel-checked. PeriodFamily.lean carries the convergent denominators q_0..q_15 of BETA = log2/log3 as a list, checks every one from q_2 on against the recurrence q_k = a_k q_(k-1) + q_(k-2) so the list is generated rather than asserted (denomsRec), and proves the facts the period sequence rests on: q_13 = 176251, q_14 = 301994, a_15 = 55, the family closure 176251 + 55 x 301994 = 16785921 (familyClosed), the identification of the three published bounds as j = 0, 1, 2 (periodBoundsAreFamily, over fanMember, giving 176251, 478245, 780239), the next member 1082233 (nextMember), the partial quotient itself (a15), that fanMember(55) is q_15 (lastMember), and that the family is strictly increasing (member_strictMono) so its me  *(truncated; read the ledger row)*

**Declaration.** `familyClosed` &mdash; kernel-checked, `Problems/Juggler/PeriodFamily.lean:71`

> **The family closes.** The semiconvergents `q₁₃ + j q₁₄` reach `q₁₅` exactly at `j = 55`, which is why the family is finite and has `56` members rather than continuing indefinitely.

```lean
theorem familyClosed : 176251 + 55 * 301994 = 16785921
```

## 10. `J-cycle-cubic-sorted-grid` &mdash; covers 0.04

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.63; different result 0.6.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 11. `J-cycle-ooe-exact-remainder-repair` &mdash; covers 0.04

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.62; different result 0.16.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Proposition E.5 and ER1. For an exact first root u=isqrt(x^3)>=3, retained remainder R=x^3-u^2, and validated OE suffix endpoint z, the correction error C-Delta=eta^2(t+2u)/(4z^2) is in [0,5/6). The signed corrected floor q is d or d-1, where d=floor((u^3-z^4)/(2z^2)). corrected_quotient_integer proves q=(isqrt(K^2*x^3)-2z^4) floor-divided by 4z^2, K=2x^3-3R. endpoint_validation certifies z via z^8<=(x^3-R)^3<(z+1)^8; record_initializes checks an independently supplied square/remainder witness. The executable recoverPeak evaluates this integer quotient and the four candidate fourth-power cells; recoverPeak_eq proves exact recovery of v=isqrt(u^3). For odd initial x, both hidden OOE source guards hold iff R is even and recoverPeak is even. Initial record and endpoint validity are ex  *(truncated; read the ledger row)*

**Declaration.** `recoverPeak_guard_iff` &mdash; kernel-checked, `Problems/Juggler/RemainderCarry.lean:473`

```lean
theorem recoverPeak_guard_iff {x u z R : ℕ}
    (hu : u = (x ^ 3).sqrt) (hz : z = ReturnCells.oe u)
    (hmin : 3 ≤ u) (hR : R = x ^ 3 - u ^ 2) (hx : x % 2 = 1) :
    (u % 2 = 1 ∧ (u ^ 3).sqrt % 2 = 0) ↔
      (R % 2 = 0 ∧ recoverPeak x z R % 2 = 0)
```

## 12. `J-cycle-short-return-cells` &mdash; covers 0.04

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.63; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Appendix E.1, formal subset. The prescribed OE return equals y iff y^4<=x^3<(y+1)^4. Every prescribed OOE return v satisfies v^8<=x^9<(v+2)^8; relative to an eighth-root cell y it is y or y-1. If v is odd, it is the greatest odd integer whose eighth power is at most x^9. The family s^4->s^6->s^3 has all three states odd when s is odd, so endpoint parities do not imply the hidden E guard. Actual OE/OOE composition bridges retain every source-parity premise. Kernel verified; no arbitrary-root or OOEOE projection theorem is claimed by this row.

**Declaration.** `ooe_odd_maximal` &mdash; kernel-checked, `Problems/Juggler/ReturnCells.lean:135`

```lean
theorem ooe_odd_maximal {x y : ℕ} (hx : ooe x % 2 = 1)
    (hy : y % 2 = 1) (hpow : y ^ 8 ≤ x ^ 9) :
    y ≤ ooe x
```

## 13. `J-fate-energy-atoms` &mdash; covers 0.04

*Reads as: the claim asserts more than the declarations state (0.84).*

*Claim broader 0.84; declaration narrower 0.61; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Section 10(d): the bias energy of the L-bad words supplies the exceptional atoms. energyOn y t S = sum over w in S of bias(w)^2 with bias(w) = #[wO] - #[w]/2 over the odd starts of (y, 2y]; biasEnergy y t is the sum over all words of length t, equal to the paper's C_{t+1}/2 - C_t/4 with C_t = sum of #[w]^2 (biasEnergy_eq, on CylinderEnergy.sum_bias_sq; wordCount_cylinder identifies the word count over the odd starts with the cylinder); badEnergy y L t is the sum over the L-bad words, at most the unrestricted one (badEnergy_le_biasEnergy). For a share q > 1/2, a bad atom violating #[wO] <= q #[w] has bias(w) > (q - 1/2) #[w], so the squared masses of the bad violators sum to at most badEnergy / (q - 1/2)^2, and Cauchy-Schwarz over the at most 2^t atoms of depth t (card_allWords) giv  *(truncated; read the ledger row)*

**Declaration.** `energy_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateEnergyAtoms.lean:234`

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

## 14. `J-fate-pressure-conjecture` &mdash; covers 0.04

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.74; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Section 9.2's consequences: the pressure hypothesis P_theta(C) and the no-momentum hypothesis M_{theta,q}(C) each imply the conjecture, in the pattern of Corollary 8.4. Bridge: above a certified floor N_0, an odd failure of (y, 2y] is a start of {1, ..., 2y} that stays above N_0 for every number of steps (oddFailures_subset_live), so the live weight of LiveCountWeight, on which Theorem 9.2 (live_count_le_of_pressure) and Proposition 9.3 under no momentum (juggler_count_le_of_noMomentum) are stated, counts the failures. PressureBound N_0 C eps y is P_theta(C) at the scale y with the paper's e^{o(d)} quantified as (log y)^eps: the live pressure of {1, ..., 2y} at the tilt x = p_C/(1 - p_C) and depth d(y) = ceil(C L(y)) is at most 2y a_theta^{d(y)} (log y)^eps. NoMomentumBound N_0 C q  *(truncated; read the ledger row)*

**Declaration.** `pressure_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FatePressureCorollary.lean:219`

> **Theorem 9.2's corollary with nothing else assumed.** The pressure hypothesis `P_θ(C)` at all large scales above a certified floor, with `C ≥ 5` and a loss `ε` such that `27/40 < e < e(C) - ε` for some `e` (a negative `ε` is a stronger hypothesis), gives that every positive integer reaches `1`.

```lean
theorem pressure_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C ε e : ℝ) (hC : 5 ≤ C)
    (he : e < chernoffExponent C - ε) (he7 : 27 / 40 < e)
    (hP : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → PressureBound N₀ C ε y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 15. `J-fate-sweep-lemma` &mdash; covers 0.04

*Reads as: the claim asserts more than the declarations state (0.96).*

*Claim broader 0.96; declaration narrower 0.63; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Lemma 4.1 (sweep). Let x_0 < x_1 < ... < x_{H-1} be reals with consecutive gaps in [a, b], 0 < a ≤ b ≤ 1/2, b ≤ (21/20) a and (H-1) a ≥ 12. Then at least H/7 of the terms have {x_j} < 1/2 and at least H/7 have {x_j} ≥ 1/2 (sweep_fract_lt_half, sweep_fract_ge_half); with the left-open half-cells (k/2, (k+1)/2], i.e. the representative x - ceil(x) + 1 in (0, 1], at least H/7 have representative ≤ 1/2 and at least H/7 have representative > 1/2 (sweep_rep_le_half, sweep_rep_gt_half). Both are instances of sweep_cell: each residue class of the half-cell index floor(2x_j) mod 2 holds at least H/7 terms. Proof as in the paper with one simplification: every cell holds at most G = floor(1/(2a)) + 1 terms (fiber_card_le), every strictly interior cell at least g = floor(1/(2b)) (fiber_card_ge  *(truncated; read the ledger row)*

**Declaration.** `sweep_fract_lt_half` &mdash; kernel-checked, `Problems/Juggler/FateSweep.lean:430`

> Paper C Lemma 4.1 (sweep), first half: at least `H/7` of the terms have `{x_j} < 1/2`.

```lean
theorem sweep_fract_lt_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a) (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b) :
    (H : ℝ) / 7 ≤ #{j ∈ Finset.range H | Int.fract (x j) < 1 / 2}
```

## 16. `J-cycle-direction-change-contraction` &mdash; covers 0.05

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.74; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For the prescribed return C=OOEOOEOE and every integer x>=2^24, 0<=x^(243/256)-F_C(x)<9/8. The kernel-checked seven-tail majorant is 63121/524288<1/8. For integers z>w>=2^24 with d=z-w>=2, 0<=F_C(z)-F_C(w)<(243/256)w^(-13/256)d+9/8<d. No parity hypothesis is needed for this prescribed-map inequality. The compiled even-gap and actual-cycle transfer layers supply its cycle use. Paper A Section3.12 and AppendixF; no no-cycle claim.

**Declaration.** `c_contract` &mdash; kernel-checked, `Problems/Juggler/ReturnWordBounds.lean:132`

```lean
theorem c_contract {x y : ℕ} (hx : 2 ^ 24 ≤ x) (hxy : x + 2 ≤ y) :
    (eval wordC y : ℝ) - eval wordC x < (y : ℝ) - x
```

## 17. `J-fate-thin-fibers` &mdash; covers 0.05

*Reads as: the claim asserts more than the declarations state (0.96).*

*Claim broader 0.96; declaration narrower 0.31; different result 0.04.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Lemma 4.3 (bad fibers are thin), badness being ¬Good of row J-fate-fiber-parity. (i) bad_count_le: for u ≥ 10^6, #{m ∈ (u, 2u] : ¬Good m} ≤ 63 u^{2/3}. (ii) bad_logMass_le: for U ≥ 10^6 and every N, Σ_{m ∈ (U, N], ¬Good m} 1/m ≤ 306 U^{−1/3} (the paper's infinite sum, as a bound on every partial sum). Proof of (i): the increments of A_m = (3/2) m^{2/3} lie in [(m+1)^{−1/3}, m^{−1/3}] by Bernoulli both ways (Am_step_ge, Am_step_le); a bad m > u has {A_m + 22 u^{−1/3}} < 44 u^{−1/3} or {A_m} ∈ [1/2 − 2u^{−1/3}, 1/2 + 2u^{−1/3}) (bad_mem_arc; the shift makes the wrap-around arc a single arc); arc_count_le: a sequence increasing by at least d per step on (u, v] has at most (⌊φ(v)⌋ − ⌊φ(u+1)⌋ + 1)(w/d + 1) indices with fractional part in an arc [c, c+w) ⊆ [0, 1), by the fibre-per-intege  *(truncated; read the ledger row)*

**Declaration.** `bad_logMass_le` &mdash; kernel-checked, `Problems/Juggler/FateThinFibers.lean:364`

> **Lemma 4.3, the log-mass.** For `U ≥ 10^6` and every `N`, the bad `m ∈ (U, N]` carry log-mass at most `306 U^{-1/3}`.

```lean
theorem bad_logMass_le {U N : ℕ} (hU : 10 ^ 6 ≤ U) :
    (∑ m ∈ {m ∈ Finset.Ioc U N | ¬ Good m}, (1 : ℝ) / m) ≤ 306 * eps U
```

## 18. `J-residual-floor-two-hundred-fifty-seven` &mdash; covers 0.05

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.4; different result 0.09.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Every positive integer strictly below 257 reaches 1 under the Juggler map (reachesOne_of_lt_two_hundred_fifty_seven). Evens below 2809 already reduce to the residual class {1,…,52}; the odd seeds 53,55,…,255 are finite orbit certificates. This is a finite certificate, not a halt theorem. Combined with cycleMin_finance and log 257 > 61/11 it excludes cycle lengths 19 and 38. The Lean constant 1 only needs n ln n > 1411.63 to kill length 19, so the smallest such n is 255; the Python 6/5 table has n_max(19) = 297.

**Declaration.** `reachesOne_of_lt_two_hundred_fifty_seven` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:325`

> Every positive residual strictly below 257 is ReachesOne. This is a finite certificate, not a halt theorem. Combined with cycleMin_finance it excludes cycle length 19.

```lean
theorem reachesOne_of_lt_two_hundred_fifty_seven {y : ℕ}
    (hpos : 1 ≤ y) (hy : y < 257) : ReachesOne y
```

## 19. `J-cycle-absolute-cell-grid-charge` &mdash; covers 0.06

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.58; different result 0.22.  Tag EXACT — HUMAN PROOF, trust kernel.*

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

## 20. `J-cycle-direction-change-height` &mdash; covers 0.06

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.4; different result 0.18.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Theorem3.40(i): Every actual Juggler cycle with minimum m>=2^24 and maximum M<m^3 satisfies M<m^3-(1/2)m^(253/128), and m^253<[2(m^3-M)]^128. The compiled companion dc_cycle_gap proves d0=F_OOE(m)-F_OE(sqrt M)>=6 and d0>(26240/59049)m^(13/128). The actual section, guards, forced batches, two genuine transfers, analytic bounds and exact extremal cells are derived internally. Ordinary periodic-orbit and CycleMin wrappers are included. The remaining cubic region and taller cycles remain open; period780239 and descent floor350000000 are unchanged.

**Declaration.** `dc_cycle_height` &mdash; kernel-checked, `Problems/Juggler/ReturnTransferHeight.lean:131`

> The unconditional actual-cycle DC height strip, including its integer form.

```lean
theorem dc_cycle_height {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^24 ≤ m) (hM : M<m^3) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(253/128 : ℝ) ∧
      m^253 < (2*(m^3-M))^128
```

## 21. `J-cycle-later-return-height` &mdash; covers 0.06

*Reads as: the claim asserts more than the declarations state (0.96).*

*Claim broader 0.96; declaration narrower 0.43; different result 0.13.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Theorem3.40(ii): Every actual Juggler cycle with minimum m>=2^128 and maximum M<m^3 satisfies M<m^3-(1/2)m^theta, theta=381/128-3^41/2^65>127/64, also M<m^3-(1/2)m^(127/64) and m^127<[2(m^3-M)]^64. The forced next batch has r=3s+u,0<u<s. The unconditional 65-letter W=D^3C loss is below6/5 and its genuine third transfer forces d0>=8 and d0>(2/5)m^(13/128+1-3^41/2^65). The full actual placement, guards and cell transport are kernel checked; ordinary periodic-orbit and CycleMin wrappers are included. This theorem retains its much larger cutoff and does not exclude all cubic or taller cycles or increase the period/descent floor.

**Declaration.** `lr_cycle_height` &mdash; kernel-checked, `Problems/Juggler/ReturnTransferHeight.lean:139`

> The unconditional actual-cycle LR strip with exact and clean exponents.

```lean
theorem lr_cycle_height {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^128 ≤ m) (hM : M<m^3) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(381/128-(3:ℝ)^41/2^65) ∧
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(127/64 : ℝ) ∧
      m^127 < (2*(m^3-M))^64
```

## 22. `J-cycle-quartic-formal-budget` &mdash; covers 0.06

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.55; different result 0.45.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 23. `J-log-two-hundred-fifty-seven-gt-sixty-one-elevenths` &mdash; covers 0.06

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.23; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** log 257 > 61/11, via e < 2.7182818286 and e^61 < 257^11 (log_two_hundred_fifty_seven_gt). Combined with the residual floor 257 this gives n log n > 15677/11 on a CycleMin, which excludes cycle length 38. The weaker half-integer bound 11/2 was enough for length 19 but not for 38. This is a numeric certificate, not a halt theorem.

**Declaration.** `log_two_hundred_fifty_seven_gt` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:527`

> Numeric certificate `log 257 > 61/11`, via `e < 2.7182818286` and `e^61 < 257^11`.

```lean
theorem log_two_hundred_fifty_seven_gt : (61 / 11 : ℝ) < Real.log 257
```

## 24. `J-paper-b-E-is-the-exponent-walk` &mdash; covers 0.06

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.31; different result 0.07.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** Paper B section 7's composed map is the exponent walk of the Paper C collision work, and its linearisation criterion is a unit climb of that walk. With the notation of J-paper-b-defect-coefficient-chain, e_t = 3^(o_t) / 2^t exactly, where o_t is the number of odd letters up to t (`iter_eq_pow`). Taking log base 2 gives e_t = 2^(u_t) with u_t = o_t log2(3) - t, which is the walk J-live-set-ladder-factorisation splits at, J-damping-at-running-minimum is about, and J-dominant-defect-at-walk-minimum measures the climb of. Hence E = e_{t-1}/e_s = 2^(u_{t-1} - u_s), and E < 2 says exactly that the walk climbs by less than one unit between the defect at letter s and the wave at letter t. Two consequences. (i) The criterion is an exact integer inequality in the counts: with a odd and b even letter  *(truncated; read the ledger row)*

**Declaration.** `iter_eq_pow` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:167`

> **The exponent walk, exactly.** `e_t = 3^(o_t) / 2^t`. Taking `log₂` gives `u_t = o_t log₂ 3 - t`, the walk the Paper C work is built on; this is that statement before any logarithm, so it is exact.

```lean
theorem iter_eq_pow (w : List Letter) :
    iter w = 3 ^ (oddCount w) / 2 ^ w.length
```

## 25. `BTN-sdr-finite-condition` &mdash; covers 0.07

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.91; different result 0.09.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For F_{λ,U_m}(s,u)=λ·D(s+u) and every integer λ≥0, a finite invariant box containing 0 exists if and only if λ≤2 or m≤1.

**Declaration.** `finite_residual_condition` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidual.lean:125`

> Finite invariant box for ``F_{λ,U_m}`` iff ``λ≤2`` or trit forcing ``m≤1``. The matching unbounded witnesses are ``signedIterate_unbounded_of_ge_three``.

```lean
theorem finite_residual_condition {gain m : ℕ}
    (h : gain ≤ 2 ∨ m ≤ 1) :
    ∃ R : ℕ, ∀ s u : ℤ, s.natAbs ≤ R → u.natAbs ≤ m →
      ((gain : ℤ) * DZ (s + u)).natAbs ≤ R
```

## 26. `J-cycle-subtractive-return-step` &mdash; covers 0.07

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.77; different result 0.18.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Appendix E.2, formal core. For rankStep(a,b,i)=i+b when i<a and i-a otherwise, a>b gives the first return on [0,a) as rankStep(a-b,b), in one or two iterations with every earlier positive iterate outside. For b>a the first return on [0,b) is rankStep(a,b-a); equal counts give a two-step identity. Weighted word lengths and O/E statistics are preserved by A,AB or AB,B substitution. Kernel-verified return iterates and first-visit properties; full accelerated towers and their global partition remain written.

**Declaration.** `left_subtractive_first_return` &mdash; kernel-checked, `Problems/Juggler/ReturnInduction.lean:15`

> Exact positive first return to the prefix of length `a`, when `b<a`. The words on the two new branches are respectively `A` and `AB`.

```lean
theorem left_subtractive_first_return {a b i : ℕ}
    (_hb : 0 < b) (hba : b < a) (hi : i < a) :
    let k
```

## 27. `J-cycle-threshold-common-period` &mdash; covers 0.07

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.59; different result 0.28.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 28. `J-fate-minimal-failure-oo` &mdash; covers 0.07

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.5; different result 0.04.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Proposition 6.3(i) and the first-letter trichotomy of Section 6.2. If some positive n does not reach 1, the failure set has a least positive member (exists_minimal_failure), and that member is odd with an odd image, i.e. an OO-type start (minimal_failure_odd_odd): an even member n ≥ 2 has the smaller positive member floor(sqrt n) (floorPower_even_lt), and an odd member with even image has the smaller positive member floor(sqrt(floor(n^{3/2}))) < n (floorPower_odd_even_two_step_lt). Stated for any forward-closed class excluding 1 (minimalMember_odd, minimalMember_image_odd). For a two-way closed class A, A n iff exactly one of: n even with J(n) ∈ A; n odd, J(n) even, J(n) ∈ A; n odd, J(n) odd, J(n) ∈ A (first_letter_trichotomy, first_letter_pieces_disjoint) — the three pieces of the  *(truncated; read the ledger row)*

**Declaration.** `minimal_failure_odd_odd` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:63`

> Paper C Proposition 6.3(i): the least failure, if the failure set is nonempty, is odd with an odd image — an `OO`-type start.

```lean
theorem minimal_failure_odd_odd {n : ℕ} (hn : 1 ≤ n)
    (hmin : MinimalMember (fun k => ¬ReachesOne k) n) :
    n % 2 = 1 ∧ floorPower n % 2 = 1
```

## 29. `J-fate-one-sided-atoms` &mdash; covers 0.07

*Reads as: the claim asserts more than the declarations state (0.76).*

*Claim broader 0.76; declaration narrower 0.73; different result 0.12.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Section 10(d), first paragraph: Theorem 9.1 with exceptional atoms, on the exponential-moment proof. OneSidedShareExc y L q err exc d: at each depth 1 <= t < d there is a set E of words of total cylinder mass at most exc such that every L-bad word outside E sends at most q #[w] + err of its members to an odd next letter; the original hypothesis is the case E empty (oneSidedShareExc_of_share). An exceptional bad atom sends at most its whole mass to its odd child, which costs (x - a_q) #[w] x^{o(w)} = (x-1)(1-q) #[w] x^{o(w)} in the tilted mass, so badMass(t+1) <= a_q badMass(t) + (x-1)(err (2x)^t + (1-q) exc x^t) (badMass_succ_le_exc), unrolled to x a_q^t N + (x-1) t (err (2x)^t + (1-q) exc x^t) (badMass_le_exc), and with Lemma 8.1 and the Markov tilt the odd failures of (y, 2y] num  *(truncated; read the ledger row)*

**Declaration.** `exc_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedAtoms.lean:619`

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

## 30. `J-fate-recursion-lemma` &mdash; covers 0.07

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

## 31. `J-odd-odd-remainder-mod-eight` &mdash; covers 0.07

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.51; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If y is odd and T(y) is odd, then the local remainder ρ=y³-T(y)² satisfies ρ≡y-1 (mod 8). Consequently v₂(ρ)=1 when y≡3 or 7 (mod 8), v₂(ρ)=2 when y≡5 (mod 8), and v₂(ρ)≥3 when y≡1 (mod 8) and ρ≠0. The same congruences hold for any odd square below y³; the floor T(y)=⌊y^{3/2}⌋ is not used beyond selecting an odd landing.

**Declaration.** `odd_odd_remainder_mod_eight` &mdash; kernel-checked, `Problems/Juggler/LandingValuation.lean:56`

```lean
theorem odd_odd_remainder_mod_eight {y : ℕ} (h : oddOddLanding y) :
    landingRemainder y % 8 = (y - 1) % 8
```

## 32. `OST-np-adjoint-window-det` &mdash; covers 0.07

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.66; different result 0.19.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP and n≥2, the determinant of consecutive adjoints (u_n, u_{n-1}, u_{n-2}) equals 3^{n-2}, so neighboring energies invert s over Q; this is not a bound on L_0

**Declaration.** `adjointDet_eq` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:335`

> Consecutive adjoints are independent: `det = 3^{n-2}` for `n ≥ 2`. Neighboring energies invert `s` over `ℚ`. Not a bound on `L₀`.

```lean
theorem adjointDet_eq (n : ℕ) (hn : 2 ≤ n) :
    adjointDet n = (3 : ℤ) ^ (n - 2)
```

## 33. `BTA-x3-Q-def` &mdash; covers 0.08

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.74; different result 0.53.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Q_{t,K,W}(u)=D^t(u^3) mod 3^K on u∈P_W

**Declaration.** `qCubic_def` &mdash; kernel-checked, `BTCalculus/MismatchedCubicQuotient.lean:23`

```lean
theorem qCubic_def (t : Nat) (u : Int) :
    qCubic t u = iterDZ t (u ^ 3)
```

## 34. `J-global-defect-identity` &mdash; covers 0.08

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.69; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every realized finite Juggler word w, n^{3^{#O(w)}} = T_w(n)^{2^{|w|}} + Δ_w(n), where Δ is the recursively lifted accumulation of local floor remainders. Δ ≥ 0, so the power envelope is a corollary; Δ = 0 iff every local remainder vanishes; concatenation is the two-term power-gap lift, not an additive sum.

**Declaration.** `global_defect_identity` &mdash; kernel-checked, `Problems/Juggler/GlobalDefect.lean:181`

> Core identity: `n^{3^o} = T_w(n)^{2^k} + Δ_w(n)`.

```lean
theorem global_defect_identity {n : ℕ} {w : List Branch} (hw : follows n w) :
    n ^ (3 ^ oddCount w) =
      image n w ^ (2 ^ w.length) + globalDefect n w
```

## 35. `J-ooo-residual-cube` &mdash; covers 0.08

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

## 36. `J-residual-floor-fifty-three` &mdash; covers 0.08

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.44; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Every positive integer strictly below 53 reaches 1 under the Juggler map (reachesOne_of_lt_fifty_three). Evens below 144 already reduce to the residual class {1,…,11}; the odd seeds 13,15,…,51 are finite orbit certificates. This is a finite certificate, not a halt theorem. Combined with cycleMin_finance it excludes cycle length 11.

**Declaration.** `reachesOne_of_lt_fifty_three` &mdash; kernel-checked, `Problems/Juggler/Termination.lean:174`

> Every positive residual strictly below `53` is `ReachesOne`. This is a finite certificate, not a halt theorem. Combined with `cycleMin_finance` it excludes cycle length `11`.

```lean
theorem reachesOne_of_lt_fifty_three {y : ℕ} (hpos : 1 ≤ y) (hy : y < 53) :
    ReachesOne y
```

## 37. `J-cubic-equal-gap-oo-triple` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.48; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every odd t>=9, the three sources t^2-4, t^2, t^2+4 and images t^3-6t, t^3, t^3+6t are odd, CubicReturn.O hits those images, the lower remainders are 12t^2-64, 0, 12t^2+64, and the three upper complements are 2t^3-12t^2-12t+65, 2t^3+1, 2t^3-12t^2+12t-63. Adjacent pairs have source gap 4, image gap 6t and gcd 2. The two raw complement changes 12t^2+12t-64 and 12t^2-12t+64 are positive and each plus its matching complement equals 2t^3+1. This is the integer content of the Result 15 OO family only. The normalized log-log comparison RC48, signed orientation and any cycle theorem remain written.

**Declaration.** `oo_equal_gap_triple` &mdash; kernel-checked, `Problems/Juggler/CriticalCostKernel.lean:279`

> Exact equal-gap OO triple of Result 15. Integer cells, remainders, complements and opposite raw complement signs; the log-log comparison RC48 remains written.

```lean
theorem oo_equal_gap_triple {t : ℕ} (ht : 9 ≤ t) (hodd : t % 2 = 1) :
    let xm
```

## 38. `J-cycle-later-return-certificate` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.49; different result 0.08.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** For a prescribed word with full ideal exponent 0<p<1 and every proper tail q_j=p/p_j<1, two traces whose sources and proper states are at least m>=1 satisfy 0<=F(z)-F(w)<p*m^(p-1)*(z-w)+K_W(m), where K_W=1+sum(q_j*m^(q_j-1)). The condition 2*p*m^(p-1)+K_W<=2 forces strict contraction on gaps at least two. For p>1/2 and a proper prefix this sufficient certificate requires m>(2p)^(1/(1-p)); hence it cannot hold uniformly at a fixed minimum for a family with p approaching one from below. This is a limitation of the one-sided error estimate, not a counterexample to true paired contraction or a claim that every possible later upper word has these exponents. The exact transported loss, paired bound and necessary finite minimum threshold are kernel checked in ReturnWordLoss, retaining the publish  *(truncated; read the ledger row)*

**Declaration.** `certificate_requires_large_minimum` &mdash; kernel-checked, `Problems/Juggler/ReturnWordLoss.lean:408`

```lean
theorem certificate_requires_large_minimum {m : ℝ} (hm : 0 < m)
    {w : List Branch} (hw : 2 ≤ w.length) (hp : exponent w < 1)
    (hc : 2 * (exponent w * m ^ (exponent w - 1)) + budget m w ≤ 2) :
    (2 * exponent w) ^ (1 / (1 - exponent w)) < m
```

## 39. `J-cycle-threshold-relaxation` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.69; different result 0.19.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 40. `J-cycle-unit-perturbation` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.61; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 41. `J-fate-block-average-layer` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.35; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The exact layer of Paper C Proposition 4.4, the slow sum, the block count, and equation (4.1) given the paper's two remaining exponential-sum bounds as hypotheses. The block: the odd n of I(m') = [m'^{8/3}, (m'+1)^{8/3}) are exactly the odd n with m'^2 <= floor(n^{3/4}) < (m'+1)^2 (mem_oddBlock, through the landing window of Appendix D.1). The decomposition: U(m') is the disjoint union of the even-image parts of the fibers Phi(m) over the even m of the block, so |U(m')| is the sum of Lemma 4.2's evenImageCount over E(m') (U_card_eq); the whole block is the disjoint union of the fibers (oddBlock_card_eq). The expansion: 4|U(m')| = M + S1 + S2 + S12 exactly (four_card_U). The slow sum S1 = sum psi(floor(n^{3/4})) is the alternating sum of fiber sizes over the block (slowSum_eq_fibers); the f  *(truncated; read the ledger row)*

**Declaration.** `block_average_two_bounds` &mdash; kernel-checked, `Problems/Juggler/FateBlockAverage.lean:436`

> **Proposition 4.4, equation (4.1), given the two exponential-sum bounds.** The slow sum is proved (`slowSum_abs_le`); the fast sum and the product sum remain hypotheses.

```lean
theorem block_average_two_bounds {m' : ℕ} (hm : 1 ≤ m') {B : ℝ}
    (h₂ : |(fastSum m' : ℝ)| ≤ B) (h₁₂ : |(productSum m' : ℝ)| ≤ B) :
    |((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4| ≤ B / 2 + (m' + 1)
```

## 42. `J-fate-one-sided-conjecture` &mdash; covers 0.09

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.68; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Theorem 9.1's consequence, the conjecture from the one-sided hypothesis, in the pattern of Corollary 8.4. OneSidedBound N_0 C q A y is H_q(C, A) at the scale y: every L(y)-bad cylinder of depth 1 <= t < ceil(C L(y)) sends at most q #[w] + y (log y)^{-A} of its members to an odd next letter; oneSidedExponent C q = C D(p_C || q) / log 2 is the Chernoff exponent of Proposition 9.3. Absorption (oddFailures_le_of_one_sided): under H_q(C, A) at all large scales, with C >= 5, 0 < q < p_C, A > C (1 + log_2 x) + 1 + e for the re-centring tilt x = p_C (1-q)/(q (1-p_C)), and e < C D(p_C || q) / log 2, the odd failures in (y, 2y] number at most y (log y)^{-e} for all large y; on Gibbs' inequality D(p || q) >= 0 (klDiv_nonneg), exp(-d D) <= Lambda^{-C D / log 2} for d >= C log_2 Lambda (exp_le_  *(truncated; read the ledger row)*

**Declaration.** `one_sided_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateOneSidedCorollary.lean:356`

> **Theorem 9.1's corollary with nothing else assumed.** If `H_q(C, A)` holds at all large scales above a certified floor, with `C ≥ 5`, `0 < q < p_C`, `A > C(1 + log₂ x) + 1 + e` and `27/40 < e < e_{C,q}`, then every positive integer reaches `1`; the contagion side is the unconditional Theorem 5.3 at exponent `13/40`.

```lean
theorem one_sided_implies_conjecture {N₀ : ℕ} (hN : 2 ≤ N₀)
    (hfloor : ∀ m, 1 ≤ m → m ≤ N₀ → ReachesOne m) (C q A e : ℝ) (hC : 5 ≤ C)
    (hq0 : 0 < q) (hqp : q < pC C)
    (hA : C * (1 + Real.logb 2 (tilt (pC C) q)) + 1 + e < A) (he : e < oneSidedExponent C q)
    (he7 : 27 / 40 < e) (hH : ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → OneSidedBound N₀ C q A y) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 43. `BTN-sdr-lambda1-radius` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.73; different result 0.46.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For λ=1 and |u|≤m, if |s|≤⌊m/2⌋ then |D(s+u)|≤⌊m/2⌋. The looser radius ⌈(m+1)/2⌉ from 3|D n|≤|n|+1 is not required.

**Declaration.** `lambda1_radius_div` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidual.lean:45`

> Sharp ``λ=1`` reachable/invariant radius ``⌊m/2⌋``. The looser ``⌈(m+1)/2⌉`` from ``3|DZ n|≤|n|+1`` is not required.

```lean
theorem lambda1_radius_div (m : ℕ) :
    (m / 2 + m + 1) / 3 ≤ m / 2
```

## 44. `C-no-uniform-L-descent` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.76; different result 0.12.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every L≥1, n=2^L-1 realises L odd shortcut steps and C^L(n)=3^L-1>n. No residual n mod 2^L with blocks of length at most L certifies strict descent.

**Declaration.** `shortcutC_no_uniform_L_descent` &mdash; kernel-checked, `Problems/Collatz/Shortcut.lean:110`

> For every ``L ≥ 1``, ``n = 2^L - 1`` realises ``L`` odd steps and expands.

```lean
theorem shortcutC_no_uniform_L_descent {L : ℕ} (hL : 0 < L) :
    2 ^ L - 1 < shortcutCIter L (2 ^ L - 1)
```

## 45. `J-cycle-direction-change-batches` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.48; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For a guarded sorted OOE/OE return model with positive counts a,b and least source at least m>=2^24, the first maximal left and right batches have quotient2 and nonzero remainders: a=2b+r,b=2r+s,0<s<r<b. dc_rank_stages proves this from exact guarded rank equations and compiled growth/decrease inequalities, including terminal equality. periodicExtrema_return_model constructs this model for an actual cycle with M<m^3. periodicExtrema_dc_transfers proves that the left steps recycle one seam and the next two right steps genuinely transfer it through C. The broader unguarded threshold-model version remains written; this Lean row states the guarded version.

**Declaration.** `dc_rank_stages` &mdash; kernel-checked, `Problems/Juggler/ReturnQuotients.lean:77`

> The first two accelerated batches are forced by exact map inequalities.

```lean
theorem dc_rank_stages {a b m : ℕ} {y : ℕ → ℕ}
    (h : RankedReturn a b y wordA wordB) (ha : 0 < a) (hb : 0 < b)
    (hm : 2 ^ 24 ≤ m) (hy : m ≤ y 0) :
    ∃ r s, 0 < s ∧ s < r ∧ r < b ∧ a = 2 * b + r ∧ b = 2 * r + s ∧
      RankedReturn r b y wordA wordC ∧ RankedReturn r s y wordD wordC
```

## 46. `J-cycle-finance-inequality` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.32; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** On a Juggler CycleMin start n ≥ 2 with word w of length L and oddCount o, the dyadic-cell logarithm bound log z ≤ 2 log y + 2/y unrolls to n · log n · (3^o − 2^L) ≤ L · 3^o (Paper A Theorem 4.4; Lean cycleMin_finance). Every cycle state is at least 12 and the rotated minimum is odd, so the minimum is at least 13 and 13 log 13 > 65/2, hence (65/2)(3^o − 2^L) ≤ L · 3^o for every CycleItinerary (cycle_finance_min_thirteen). This is the whole-cycle financing of the formal expansion 2^L < 3^o by relative floor defects. It is not a halt theorem, not an exclusion of every length, and not the computational 6/5 table used for L ≤ 10^5.

**Declaration.** `cycleMin_finance` &mdash; kernel-checked, `Problems/Juggler/CycleFinance.lean:210`

> **Cycle finance inequality.** For any cycle taken at its minimum: `n log n (3^o - 2^L) ≤ L 3^o`.

```lean
theorem cycleMin_finance {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    (n : ℝ) * Real.log n *
        ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (w.length : ℝ) * (3 : ℝ) ^ oddCount w
```

## 47. `J-cycle-ooe-family-chain-bound` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.45; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Theorem E.4. For X(r)=r^8+8 and odd parameters r>=3, the exact three-step Juggler image is r^9+9r-1. A family transition r->s is equivalent to s^8+9=r^9+9r and forces r=1 modulo48. Between continuing sources, nu2(s-1)=nu2(r-1)-2. For a finite actual J^3 chain of k transitions through odd parameters >=3, k<=(nu2(r0-1)-2)/2 with natural-number subtraction and division; this is max(0,floor((nu2(r0-1)-2)/2)) in integer notation. No valuation drop is assumed after the final destination. ooeFamily_no_infinite_juggler_chain excludes an infinite exact family chain. These are direct actual-Juggler wrappers, not merely an assumed polynomial recurrence. The supplementary 3-adic identity is written and six terminating sample traces are computations. No universal family termination, general esc  *(truncated; read the ledger row)*

**Declaration.** `ooeFamily_juggler_chain_bound` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:270`

```lean
theorem ooeFamily_juggler_chain_bound (r : ℕ → ℕ) (k : ℕ)
    (hr : ∀ i, i ≤ k → 3 ≤ r i)
    (ho : ∀ i, i ≤ k → r i % 2 = 1)
    (hstep : ∀ i, i < k →
      (floorPower^[3]) (ooeFamilySource (r i)) = ooeFamilySource (r (i+1))) :
    k ≤ (padicValNat 2 (r 0 - 1) - 2) / 2
```

## 48. `J-cycle-upper-charge-monotonicity` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.6; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 49. `J-cyclemin-hug-prefix-bound` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.36; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Cycle itineraries dominate the hug itinerary (Paper A Section 5.3 remark). On any minimum-based cycle itinerary w at minimum n ≥ 2, every length-k prefix carries at least hugOdds k = o_min(k) odd letters (cycleMin_prefix_odds_ge_hug; full word cycleMin_odds_ge_hug), by composing the formalized cycle prefix envelope 2^k ≤ 3^(oddCount (w.take k)) (cycleMin_prefix_pow_le, CycleFinance) with hug minimality (hugOdds_least). Strict window 2^k < 3^(hugOdds k) for k ≥ 1 (hugOdds_pow_gt, powers of 2 and 3 never meet) identifies hugOdds with the finance table's strict o_min. The survivor-lattice generators of Proposition 4.9 lie on the hug diagonal o = hugOdds L: (1054, 665), (25781, 16266), (50508, 31867) (hugOdds_1054, hugOdds_lattice_base, hugOdds_seed), and the hug counts along the certified con  *(truncated; read the ledger row)*

**Declaration.** `cycleMin_prefix_odds_ge_hug` &mdash; kernel-checked, `Problems/Juggler/WalkChargeItineraries.lean:154`

> **Cycle itineraries dominate the hug itinerary** (corollary of `cycleMin_prefix_pow_le` and `hugOdds_least`): on a minimum-based cycle itinerary, every prefix carries at least as many odd letters as the exact hug itinerary of the same length. This is the cycle-native form of the hug adversary — the rotation itinerary is the pointwise cheapest odd-count profile any hypothetical cycle can present.

```lean
theorem cycleMin_prefix_odds_ge_hug {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∀ k, k ≤ w.length → hugOdds k ≤ oddCount (w.take k)
```

## 50. `J-fate-collapse-bias` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.36; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The collapsed component is nearly fair, exact layer (Paper C Section 10(d), after the cylinder-energy measurement). For a finite set S of starts and a depth t, fiber S t v = #{n in S : J^t(n) = v}, window S t a b = the starts whose t-th iterate lies in [a, b], and windowBias S t a b = #{odd iterate} - #{even iterate} in the window, the bias of the next letter. windowBias = - sum over v in [a, b] of (-1)^v fiber(v) (windowBias_eq_sum, on card_filter_window), hence |windowBias| <= sum over v in [a, b) of |fiber(v+1) - fiber(v)| + fiber(b) (abs_windowBias_le), by summation by parts on alternating sums with the partial sums of (-1)^i bounded by 1 (abs_alt_sum_le). One step of the map: fiber(t+1, v) = sum of fiber(t, u) over the preimages u of v, all below (v+1)^2 (fiber_succ, lt_sq_succ_of_flo  *(truncated; read the ledger row)*

**Declaration.** `collapse_bias_le` &mdash; kernel-checked, `Problems/Juggler/FateCollapse.lean:395`

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

## 51. `J-flight-height-law` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.55; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Walk-height law (divergence rate) on descent-free prefixes: if AboveAnchor(n,w) with n >= 400 and the exponent walk is at height >= B doublings at step k (2^(k+B) <= 3^{a_k} with a_k the odd count of the k-prefix), then 2^B (log n − D) <= log x_k with the transport deficit D = 1.05 e/n + 0.7 o/(n√n); exponentiating, x_k >= (n e^{−D})^{2^B} — heights along a descent-free prefix are doubly exponential in the walk height (aboveAnchor_height_of_walk, weight form two_pow_le_walkWeight, WalkTransport.lean). One-case composition of aboveAnchor_transport with 2^B <= w_k = 3^{a_k}/2^k; when log n < D the bound is vacuously true since x_k >= 1. Appearing corollary of the September 2026 re-rooting of transport on AboveAnchor: composed with the flight walk-divergence theorem (J-flight-walk-divergence,  *(truncated; read the ledger row)*

**Declaration.** `aboveAnchor_height_of_walk` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:502`

> **Walk-height law** (divergence rate): on a descent-free prefix with anchor `n ≥ 400`, a walk height of `B` doublings at step `k` (`2^(k+B) ≤ 3^{a_k}`) forces `2^B·(log n − D) ≤ log x_k`; exponentiating, `x_k ≥ (n·e^{−D})^{2^B}` — heights along a descent-free prefix are doubly exponential in the walk height. Composed with the walk-divergence theorem (`J-flight-walk-divergence`; human glue: pigeonhole plus `cycle_strict_envelope`), every descent-free flight realizes this rate along an unbounded walk. Not a halt theorem and not a divergence theorem.

```lean
theorem aboveAnchor_height_of_walk {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : AboveAnchor n w) {k B : ℕ} (hk : k ≤ w.length)
    (hB : 2 ^ (k + B) ≤ 3 ^ oddCount (w.take k)) :
    (2 : ℝ) ^ B * (Real.log n - transportDeficit n w) ≤
      Real.log (floorPower^[k] n)
```

## 52. `J-four-block-persistent-expanding` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.82).*

*Claim broader 0.82; declaration narrower 0.37; different result 0.13.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Four consecutive persistent expanding Juggler residual blocks exist: 1999 follows OOE to 5169, 5169 follows OOOOEE to 50093, 50093 follows OOE to 193753, and 193753 follows OOE to 887471. Each step is PersistentExpandingResidual.

**Declaration.** `four_consecutive_persistent_expanding_exists` &mdash; kernel-checked, `Problems/Juggler/ExpansionSlack.lean:246`

> Four consecutive persistent expanding residual blocks exist: `1999` to `5169` by `OOE`, `5169` to `50093` by `OOOOEE`, then `50093` to `193753` and `193753` to `887471` by `OOE`. Each step is a `PersistentExpandingResidual`.

```lean
theorem four_consecutive_persistent_expanding_exists :
    ∃ x y z u v,
      PersistentExpandingResidual x y ∧
        PersistentExpandingResidual y z ∧
          PersistentExpandingResidual z u ∧
            PersistentExpandingResidual u v
```

## 53. `J-odd-run-recursive` &mdash; covers 0.1

*Reads as: the claim asserts more than the declarations state (0.95).*

*Claim broader 0.95; declaration narrower 0.67; different result 0.13.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Write oddLanding y for y odd and T(y) odd, and oddRun 0 y = oddLanding y, oddRun (r+1) y = oddLanding y and oddRun r (T(y)). Then oddRun (r+1) y if and only if y is odd and oddRun r (T(y)). The odd-landing cylinder of a fixed m contains at most one integer.

**Declaration.** `oddRun_recursive` &mdash; kernel-checked, `Problems/Juggler/OddLandingSets.lean:70`

> Exact set recursion: `P_{r+1} = {y odd : T(y) ∈ P_r}`.

```lean
theorem oddRun_recursive {r y : ℕ} :
    oddRun (r + 1) y ↔ y % 2 = 1 ∧ oddRun r (floorPower y)
```

## 54. `J-cycle-terminal-mixed-gap` &mdash; covers 0.11

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.51; different result 0.53.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 55. `J-cyclemin-walk-ostrowski-arithmetic` &mdash; covers 0.11

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.41; different result 0.25.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 56. `J-fate-contagion-elementary` &mdash; covers 0.11

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.5; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The production inequality of Paper C Section 5.1 without its exponential sums, and the unconditional theorem it yields. Of the three families of members of A on (sqrt x, x], the E-images of the members at scale t/2 (Lemma 3.1; Production.family_E) and the OE-fibers of the members at scale 3t/4 (Lemma 4.2 on good fibers, Lemma 4.3 for the bad; Production.family_OE, on the per-fiber bound (2/9)(1 - (25/2) m^{-1/3})/m) need no analysis. With the paper's sqrt x read as floor(e^{t/2}) (sqrt_floor_exp) they give, for t >= 40, g_A(t) >= (1 - 4e^{-t/4}) g_A(t/2) + (2/9 - (50/9)e^{-t/8}) g_A(3t/4) - eta_0(t) with eta_0(t) = 2e^{-t/2} + (4/9)e^{-3t/4} + 136 e^{-t/8}, every error explicit (production_two). Lemma 5.1 (recursion_lemma) on these two productions, with 2^{-13/40} + (2/9)(3/4)^{13/40} > 1   *(truncated; read the ledger row)*

**Declaration.** `logMass_contagion_elementary` &mdash; kernel-checked, `Problems/Juggler/FateProduction.lean:630`

> **Elementary contagion, as a log-mass bound.** For every nonempty backward-closed `A` and `0 < λ ≤ 13/40` there are `K > 0` and `x₀` with `Σ_{n ∈ A, n ≤ x} 1/n ≥ K (log x)^λ` for all `x ≥ x₀`. This is Theorem 5.3 of the paper with `13/40` in place of `λ** ≈ 0.4926`, and with no hypothesis: the block-average family and the ladder, which need the exponential sums, are what lift the exponent.

```lean
theorem logMass_contagion_elementary {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 13 / 40) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → K * Real.log x ^ lam ≤ logMass A x
```

## 57. `J-minimal-prefix-noncontracting` &mdash; covers 0.11

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.73; different result 0.17.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If MinimalNonTerm n and n follows w, then w is not an exponent-gap itinerary, and every prefix of w is noncontracting. Contrapositive of power_bound_contracts plus minimal_nonterm_no_descent. Concatenating expanding residual blocks therefore cannot create an exponent certificate on a CE. This is not a proof that escape is impossible and not a halt theorem.

**Declaration.** `minimal_nonterm_prefix_noncontracting` &mdash; kernel-checked, `Problems/Juggler/Escape.lean:245`

> Every realized prefix of a CE is prefix-noncontracting. Concatenating expanding residual blocks therefore cannot create an exponent certificate on a CE. This is not a halt theorem.

```lean
theorem minimal_nonterm_prefix_noncontracting {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w) : prefixNoncontracting w
```

## 58. `BTA-x3-x` &mdash; covers 0.12

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.65; different result 0.57.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** x^3-x vanishes modulo 3 and its leading coefficient is not divisible by 3

**Declaration.** `X_pow_three_sub_X_vanishes_one` &mdash; kernel-checked, `BTCalculus/PolynomialFunctionsMod.lean:240`

> The first invisible cubic: ``X^3 - X`` vanishes modulo ``3``, but its leading coefficient is a unit.

```lean
theorem X_pow_three_sub_X_vanishes_one :
    vanishesMod 1 ((X : ℤ[X]) ^ 3 - X)
```

## 59. `BTN-sdrg-lambda2-evens` &mdash; covers 0.12

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.89; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For λ=2 and U_m, every even 2n with |n|≤(m-1)_+ is reached from 0 by an admissible word. The explicit nonnegative word uses letters k+2 at step k.

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

## 60. `J-cycle-fixed-residue-witness` &mdash; covers 0.12

*Reads as: the claim asserts more than the declarations state (0.82).*

*Claim broader 0.82; declaration narrower 0.64; different result 0.12.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Appendix E.6, explicit formal witness. For every requested modulus q>0, c=512q-1 and b=c^3 yield two prescribed OOE first-return blocks in the same full cubic threshold band and the same section. The source, first image and endpoint are odd, all six threshold edges and first-return memberships are proved, and the final E-source parities differ. The records agree in source/first-image/endpoint/natural-aggregate residues modulo q, exact first remainder zero, and exact aggregate 2-adic valuation three. No classifier of this record can give both hidden parities correctly, even when supplied the exact common threshold and section boundary. The general positive free-b Taylor construction remains written. These blocks are not asserted periodic points; no impossibility for full absolute-va  *(truncated; read the ledger row)*

**Declaration.** `guardResidueFamily_no_record_classifier` &mdash; kernel-checked, `Problems/Juggler/GuardResidueFamily.lean:691`

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

## 61. `J-cycle-quartic-formal-cells` &mdash; covers 0.12

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.52; different result 0.21.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 62. `J-cycle-quartic-formal-projection` &mdash; covers 0.12

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.57; different result 0.77.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 63. `J-fate-seed` &mdash; covers 0.12

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.41; different result 0.04.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Lemma 5.2 (seed). Every nonempty backward-closed A with a positive member contains some m ≥ 3 (exists_ge_three_of_backwardClosed: 1 maps to 2 maps to 4 through even blocks). For any such m and every y ≥ (m+1)^4, the log-mass of A on (√y, y] is at least c_A = (1 − 2/m^4)(3/8 · 1/(m+1) − 1/((m+1)^2 − 1)) (seed_lemma), and c_A > 0 (seed_constant_pos). Proof as in the paper: the even-block tree S_k of m lies in A and in [m^{2^k}, (m+1)^{2^k}); its log-mass grows by at least 1 − 2 m^{-2^k} per level; the product is at least 3/4 by the geometric series 1/(m^2 − 1) ≤ 1/8; at scale k = log2 log_{m+1} y the tree splits at floor(√y) into members above √y, members whose even blocks lie there, and at most one member equal to floor(√y). The integer form y = floor(x) is the paper's g_A(log x). K  *(truncated; read the ledger row)*

**Declaration.** `seed_lemma` &mdash; kernel-checked, `Problems/Juggler/FateSeed.lean:288`

> **Paper C Lemma 5.2 (seed).** If `A` is backward-closed and contains `m ≥ 3`, then for every `y ≥ (m+1)⁴`, `Σ_{√y < n ≤ y, n ∈ A} 1/n ≥ (1 - 2/m⁴) (3/8 · 1/(m+1) - 1/((m+1)² - 1))`.

```lean
theorem seed_lemma {A : ℕ → Prop} (hA : BackwardClosed A) {m : ℕ} (hm : 3 ≤ m) (hmA : A m)
    {y : ℕ} (hy : (m + 1) ^ 4 ≤ y) :
    (1 - 2 / (m : ℝ) ^ 4) * (3 / 8 / ((m : ℝ) + 1) - 1 / (((m : ℝ) + 1) ^ 2 - 1)) ≤
      halfLogMass A y
```

## 64. `J-cycle-itinerary-eliahou-leftover` &mdash; covers 0.13

*Reads as: the claim asserts more than the declarations state (0.84).*

*Claim broader 0.84; declaration narrower 0.39; different result 0.16.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, and every length in [30, 10^5) outside a named list of near-convergents is already excluded, then the period is 84, or belongs to that list, or is at least 10^5. Lean theorem cycle_itinerary_eliahou_leftover: bookkeeping on cycle_itinerary_length_eighty_four_or_ge_eighty_five plus EliahouTable, not a new inequality. This is the Collatz Eliahou leftover shape (period ≥ X, or a named convergent family) on the floor-power map. Paper A prints the floor-10^6 instance as Theorem 4.6; leftover 84 is Appendix A companion. This is not a proof of the finance table, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `cycle_itinerary_eliahou_leftover` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:873`

> Bookkeeping: the Lean leftover `84` or `≥ 85`, plus the finance table, is the Eliahou leftover. Not a new inequality.

```lean
theorem cycle_itinerary_eliahou_leftover {n : ℕ} {w : List Branch}
    {exceptions : List ℕ} (hn : 2 ≤ n) (h : CycleItinerary n w)
    (hTable : EliahouTable exceptions) :
    EliahouLeftover w.length exceptions
```

## 65. `J-cycle-itinerary-length-eleven-or-ge-fourteen` &mdash; covers 0.13

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.28; different result 0.12.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 11 or at least 14. Lengths ≤ 10 are J-small-cycle-census-ten; lengths 12 and 13 are excluded by the same finance comparison (no_cycle_itinerary_length_twelve, no_cycle_itinerary_length_thirteen); length 16 is likewise excluded (no_cycle_itinerary_length_sixteen) but is absorbed into the ≥ 14 residual. Lean theorem cycle_itinerary_length_eleven_or_ge_fourteen. Strengthened by J-cycle-itinerary-length-ge-fourteen, which kills the length-11 disjunct. This is not a leftover-itinerary length-11 census, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `cycle_itinerary_length_eleven_or_ge_fourteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:235`

> If a nontrivial cycle exists, its period is `11` or at least `14`: lengths `≤ 10`, `12`, and `13` are impossible.

```lean
theorem cycle_itinerary_length_eleven_or_ge_fourteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 11 ∨ 14 ≤ w.length
```

## 66. `J-fate-landing-window` &mdash; covers 0.13

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.26; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Appendix D.1, equations (D.1) and (D.2), the exact landing windows of the nested productions. Write F(u) = floor(u^{3/4}) as the integer operation cell34 n = sqrt(sqrt(n^3)), which is J^2 on an OE step (cell34_eq_floorPower_two), and Phi(a) = ceil(a^{4/3}) as windowStart a, the least n with a^4 <= n^3 -- which is what the ceiling means in exact arithmetic. The two are a Galois connection: windowStart a <= n and a <= cell34 n are both a^4 <= n^3 (windowStart_le_iff, le_cell34_iff). Hence (D.1): {n : a <= F(n) < b} = [Phi(a), Phi(b)) exactly (exact_endpoints, setOf_cell34_mem_Ico), and by induction the nested window (D.2) for the i-fold image (exact_endpoints_iterate, setOf_iterate_mem_Ico). Exact, with no error term and no real number. What Appendix D does with the window is not for  *(truncated; read the ledger row)*

**Declaration.** `exact_endpoints` &mdash; kernel-checked, `Problems/Juggler/FateLandingWindow.lean:70`

> **Equation (D.1), the exact endpoints.** `a ≤ F(n) < b` exactly when `Φ(a) ≤ n < Φ(b)`.

```lean
theorem exact_endpoints {a b n : ℕ} :
    (a ≤ cell34 n ∧ cell34 n < b) ↔ (windowStart a ≤ n ∧ n < windowStart b)
```

## 67. `J-fate-one-sided-moments` &mdash; covers 0.13

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.52; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Theorem 9.1 (the one-sided form) in exact form, by exponential moments and without the martingale, carrying out the paper's remark after Proposition 9.3. For a tilt x >= 1 let badMass(t) be the sum over the L-bad words w of length t of #[w] x^{o(w)}, the tilted mass of the bad cylinders of depth t. Under the one-sided hypothesis OneSidedShare (every L-bad cylinder of depth 1 <= t < d sends at most q #[w] + err of its members to an odd next letter), bad words being prefix-closed and a cylinder splitting into its two children, badMass(t+1) <= (1 + (x-1) q) badMass(t) + (x-1) err (2x)^t (badMass_succ_le), which unrolls to badMass(t+1) <= x (1 + (x-1) q)^t N + (x-1) err t (2x)^t with N the odd starts of (y, 2y] (badMass_le). Lemma 8.1 and the Markov tilt put every odd failure of (y, 2y  *(truncated; read the ledger row)*

**Declaration.** `one_sided_bound` &mdash; kernel-checked, `Problems/Juggler/FateOneSided.lean:366`

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

## 68. `J-fate-tao-union-bound` &mdash; covers 0.13

*Reads as: the claim asserts more than the declarations state (0.8).*

*Claim broader 0.8; declaration narrower 0.58; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Theorem 8.3 (Tao-type bound from the cylinder hypothesis), exact and explicit forms. cylinder y d w is the set of odd n in (y, 2y] with itinerary n d = w; oddFailures y the odd n in (y, 2y] with ¬ReachesOne n; EnvelopeBad N₀ Y w says N₀^{2^t} < Y^{3^{o_t(w)}} for every prefix t ≤ |w|. (i) oddFailures_subset_bad_cylinders: if every start up to N₀ reaches 1, then oddFailures y ⊆ ⋃ {cylinder y d w : w ∈ allWords d, EnvelopeBad N₀ (2y) w} — Lemma 8.1 (reachesOne_of_itinerary_envelope) in covering form, using n ≤ 2y. (ii) oddFailures_card_le: if every envelope-bad cylinder has at most M starts then #oddFailures y ≤ #{envelope-bad words} · M. (iii) LBad_of_envelopeBad: for N₀, Y ≥ 2, envelope-bad at scale Y implies L-bad with L = log_2(log Y / log N₀). (iv) oddFailures_card_le_chernoff:   *(truncated; read the ledger row)*

**Declaration.** `oddFailures_card_le_explicit` &mdash; kernel-checked, `Problems/Juggler/FateChernoff.lean:403`

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

## 69. `J-residual-floor-two-hundred-sixty-one` &mdash; covers 0.13

*Reads as: the claim asserts more than the declarations state (0.83).*

*Claim broader 0.83; declaration narrower 0.4; different result 0.09.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Every positive integer strictly below 261 reaches 1 under the Juggler map (reachesOne_of_lt_two_hundred_sixty_one). The floor-257 class plus the two odd seeds 257 and 259 (five steps each) raise the floor. Exact log 257 cannot kill length 57 (257 ln 257 ≈ 1426 < 1430.8). Combined with cycleMin_finance and 261 log 257 > 15921/11 this excludes the cheap leftovers 57 and 76, so the named leftover is the record near-convergent 84. This is a finite certificate, not a halt theorem.

**Declaration.** `reachesOne_of_lt_two_hundred_sixty_one` &mdash; kernel-checked, `Problems/Juggler/TerminationFloor257.lean:480`

> Every positive residual strictly below 261 is ReachesOne. Two extra odd seeds; evens below 261 already reduce via `even_lt_sq_fifty_three`. Combined with cycleMin_finance this excludes the cheap leftovers 57 and 76, so the named leftover is the record near-convergent 84.

```lean
theorem reachesOne_of_lt_two_hundred_sixty_one {y : ℕ}
    (hpos : 1 ≤ y) (hy : y < 261) : ReachesOne y
```

## 70. `BTN-carry-bound` &mdash; covers 0.14

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.6; different result 0.2.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** 3|DZ n| ≤ |n|+1 and |q| ≤ (B+1)/3 on |c|≤B

**Declaration.** `DZ_carry_bound` &mdash; kernel-checked, `BTCalculus/Normalization.lean:145`

> Algebraic single-coefficient carry bound: `3 |q| ≤ |c| + 1`.

```lean
theorem DZ_carry_bound (n : ℤ) :
    3 * (DZ n).natAbs ≤ n.natAbs + 1
```

## 71. `J-above-anchor-hug-domination` &mdash; covers 0.14

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.35; different result 0.04.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** AboveAnchor walk nonnegativity and hug domination: the Section 5 discrete walk layer ported from cycles to open trajectories. If AboveAnchor(n,w) with n >= 2, then every prefix length k <= |w| satisfies 2^k <= 3^{oddCount(w.take k)} (aboveAnchor_prefix_pow_le, AboveAnchorWalk.lean): a never-descending orbit segment keeps the exponent walk u_k >= 0, exactly the CycleMin hypothesis of cycleMin_prefix_pow_le with no cycle, by composing the defect-free upper envelope power_bound_contracts with the anchor hypothesis. Composed with hug minimality (hugOdds_least), every above-anchor prefix dominates the exact hug itinerary in odd count: hugOdds k <= oddCount(w.take k) (aboveAnchor_prefix_odds_ge_hug; full-word form aboveAnchor_odds_ge_hug). Hence a hypothetical descent-free flight carries odd den  *(truncated; read the ledger row)*

**Declaration.** `aboveAnchor_prefix_odds_ge_hug` &mdash; kernel-checked, `Problems/Juggler/AboveAnchorWalk.lean:38`

> **Open trajectories dominate the hug itinerary.** Every prefix of a never-descending trajectory segment carries at least as many odd letters as the exact hug itinerary of the same length. The open-trajectory form of `cycleMin_prefix_odds_ge_hug`: the hug adversary prices not only hypothetical cycles but every hypothetical descent-free flight.

```lean
theorem aboveAnchor_prefix_odds_ge_hug {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : AboveAnchor n w) :
    ∀ k, k ≤ w.length → hugOdds k ≤ oddCount (w.take k)
```

## 72. `J-even-count-le-three` &mdash; covers 0.14

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.25; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** No n ≥ 2 realizes a Juggler cycle itinerary with at most three even letters (Paper A Theorem 3.22). Every CycleItinerary has a CycleMin rotation that starts OO, ends E, and is formally expanding; those itineraries are the odd-run family, the two-even leftovers (Theorem 3.12), the internal-E bootstrap, the seven bunched leftovers (Theorems 3.14–3.20), or the gapped leftovers (Theorems 3.13 and 3.21). The corollary is that a nontrivial cycle itinerary has length at least eleven (Paper A Corollary 3.23). Lean theorems no_cycle_itinerary_even_count_le_three and cycle_itinerary_length_ge_eleven in EvenCountThree.lean. This is an even-count assembler, not a length-9 or length-10 itinerary census, and not a halt theorem.

**Declaration.** `no_cycle_itinerary_even_count_le_three` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:532`

> **Even-count assembler.** No `n ≥ 2` realizes a cycle itinerary with at most three even letters. This is not a length census and not a halt theorem.

```lean
theorem no_cycle_itinerary_even_count_le_three {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) (he : evenCount w ≤ 3) : False
```

## 73. `J-gapped-cycle-itinerary-eoe` &mdash; covers 0.14

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.23; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For every n ≥ 2, a ≥ 2, and b ≥ 3, the gapped three-even leftover O^a E O^b EOE is not a Juggler cycle itinerary. The same rotation classes apply: first-E CycleMin at k=0; bootstrap O^b EOE O^a E at k=a+1 (last-gap ≥ 2, with n=3 and b=3 failing after OOOE at 6); start OE at k=a+b+2; every other rotation ends odd. Lean theorem no_cycle_itinerary_gapped_three_even_eoe. This upgrades the CycleMin theorem to CycleItinerary; it is not first-E transport at a non-minimum start, not a bunched-tail theorem, not a length-8 or length-9 census, and not a halt theorem.

**Declaration.** `no_cycle_itinerary_gapped_three_even_eoe` &mdash; kernel-checked, `Problems/Juggler/LeftoverFamilies.lean:2950`

> The gapped three-even leftover `gappedThreeEvenEOE a b` is not a Juggler cycle itinerary at any `n >= 2`, for `a >= 2` and `b >= 3`.

```lean
theorem no_cycle_itinerary_gapped_three_even_eoe {n a b : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (hb : 3 ≤ b) :
    ¬CycleItinerary n (gappedThreeEvenEOE a b)
```

## 74. `J-envelope-lt-pow` &mdash; covers 0.15

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.8; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If n ≥ 2, A > 0, x^A ≤ n^B, and B < k·A, then x < n^k. EnvelopeState n x packages the free inequality x^A ≤ n^B, with even (A,B)→(2A,B) and odd (A,B)→(2A,3B). PowerBound is the special case A=2^|w|, B=3^{oddCount w}. A realized itinerary with 3^{oddCount w} < k·2^{|w|} therefore has T_w(n) < n^k. power_bound_contracts is the k=1 case. Escape square and cube cells are k=2 and k=3 instances. The leftover itinerary OOEOOEOOEOEOO has the cube gap 3^9 < 3·2^13 and not the square gap 3^9 < 2·2^13. This is not a halt theorem and not a cycle-exclusion theorem.

**Declaration.** `power_bound_lt_pow` &mdash; kernel-checked, `Problems/Juggler/Envelope.lean:312`

> Word-stat form: `3^{oddCount w} < k · 2^{|w|}` yields `T_w(n) < n^k`. Implemented by `EnvelopeState.of_follows`. `power_bound_contracts` is the `k = 1` case.

```lean
theorem power_bound_lt_pow {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (hw : follows n w)
    (hgap : 3 ^ oddCount w < k * 2 ^ w.length) :
    image n w < n ^ k
```

## 75. `J-cubic-critical-localization-kernels` &mdash; covers 0.16

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

## 76. `J-tao-rate-implies-conjecture` &mdash; covers 0.16

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.39; different result 0.06.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** Theorem A of the Tao-reduction note. If for some e > 1 − λ** = 0.5074… and all sufficiently large y, #{n odd in (y, 2y] : n does not reach 1} ≤ y (log y)^{−e}, then every positive integer reaches 1. Proof: every failure lies in the E-tree of an odd failure (forward closure), each E-tree level has log-mass ≤ 2/n₀ and at most 1 + log₂ log x levels meet [1, x], so the log-count of the failure set is ≪ (log x)^{1−e} log log x, contradicting fate contagion (J-fate-log-density) for any λ ∈ (1 − e, λ**). The E-tree bound, the dyadic sum and the contradiction given a contagion lower bound K (log x)^λ are Lean (tao_rate_implies_conjecture in FateTaoReduction.lean); the contagion bound itself (Theorem 5.3) stays a human proof, so this row is not Lean-verified. The same holds for the hypothesis state  *(truncated; read the ledger row)*

**Declaration.** `tao_rate_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateTaoReduction.lean:691`

> **Paper C Theorem 7.2 on the failure set.** If the contagion bound holds for the failure set whenever it is nonempty, and the odd failures satisfy the Tao-type rate with `e > 1 - λ`, then every positive integer reaches `1`.

```lean
theorem tao_rate_implies_conjecture {lam e : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (he : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) → ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x)
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n
```

## 77. `BTC-op-fragment-nd-semantic` &mdash; covers 0.17

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.65; different result 0.16.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** irreducibles of the enlarged operator-fragment TRS (tree rules plus N(D(x))→D(N(x))) are unique representatives of integer operator functions on {D, I_a, S, N}

**Declaration.** `eval_eq_unique_nf` &mdash; kernel-checked, `BTCalculus/OpFragSemantic.lean:497`

> Semantically equal terms share the same irreducible.

```lean
theorem eval_eq_unique_nf {t u n₁ n₂ : OpFrag}
    (h : ∀ n, eval t n = eval u n)
    (hn₁ : Normal n₁) (hn₂ : Normal n₂)
    (ht : ReflTransGen Step t n₁) (hu : ReflTransGen Step u n₂) : n₁ = n₂
```

## 78. `BTN-sdrm-separation` &mdash; covers 0.17

*Reads as: the claim asserts more than the declarations state (0.94).*

*Claim broader 0.94; declaration narrower 0.55; different result 0.11.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If λ is not divisible by 3 and s≠t, the constant word of any letter of length v_3(s-t)+1 distinguishes the output streams of F_{λ,U}(s,u)=λ·D(s+u) with output lsd(s+u). Distinct residuals are therefore Mealy-inequivalent, so M(λ,U)=|R_{λ,U}| on every nonempty origin-reachable machine in this regime.

**Declaration.** `residual_separation` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidualMinimality.lean:166`

> Distinct residuals are Mealy-inequivalent. For `gain` not divisible by `3` and `s != t`, the constant word of length `v3 (s - t) + 1` already separates the signed traces from `s` and from `t`.

```lean
theorem residual_separation {gain s t u : ℤ}
    (hgain : ¬ (3 : ℤ) ∣ gain) (hne : s ≠ t) :
    signedTrace gain s (List.replicate (intVal3 (s - t) + 1) u) ≠
      signedTrace gain t (List.replicate (intVal3 (s - t) + 1) u)
```

## 79. `J-cycle-branch-offset-obstruction` &mdash; covers 0.17

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.47; different result 0.22.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 80. `J-cycle-itinerary-length-ge-fourteen` &mdash; covers 0.17

*Reads as: the claim asserts more than the declarations state (0.92).*

*Claim broader 0.92; declaration narrower 0.31; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is at least 14. Strengthened through J-cycle-itinerary-length-eighty-four-or-ge-eighty-five: lengths 14–83 except the named leftovers along the way are excluded, so the laboratory leftover is period 84 or at least 85. Lean theorem cycle_itinerary_length_ge_fourteen. This is not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `cycle_itinerary_length_ge_fourteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:352`

> If a nontrivial cycle exists, its period is at least `14`. Corollary of the floor-`53` leftover; lengths `14`–`18` and `20`–`29` are excluded separately.

```lean
theorem cycle_itinerary_length_ge_fourteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : 14 ≤ w.length
```

## 81. `J-cycle-itinerary-length-thirty-eight-or-ge-thirty-nine` &mdash; covers 0.18

*Reads as: the claim asserts more than the declarations state (0.81).*

*Claim broader 0.81; declaration narrower 0.26; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 38 or at least 39. Lengths ≤ 19 are J-small-cycle-census-nineteen; lengths 20–29 remain excluded at the residual floor 53; lengths 30–37 are excluded by cycle_finance_min_two_hundred_fifty_seven. This row is the leftover before the 61/11 log certificate. Strengthened by J-cycle-itinerary-length-fifty-seven-or-ge-fifty-eight, which kills the length-38 disjunct. Lean theorems cycle_itinerary_length_thirty_eight_or_ge_thirty_nine and no_cycle_itinerary_length_lt_thirty_eight. This is not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `cycle_itinerary_length_thirty_eight_or_ge_thirty_nine` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:686`

> If a nontrivial cycle exists, its period is `38` or at least `39`. Weaker leftover: `log 257 > 61/11` also kills `38`.

```lean
theorem cycle_itinerary_length_thirty_eight_or_ge_thirty_nine
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 38 ∨ 39 ≤ w.length
```

## 82. `OST-np-energy-step` &mdash; covers 0.18

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.84; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, the unread-tail energy E_i(s) = s1 q_{i-2} + s2 q_{i-1} + s3 q_i (with q_j = 0 for j < 0) satisfies E_{i-1}(T_w s) = E_i(s) - w q_{i-1} for i ≥ 1, equivalently the adjoint covariance u_{i-1} A = u_i

**Declaration.** `energy_step` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:134`

> Constructional identity: `E_{i-1}(T_w s) = E_i(s) - w q_{i-1}`.

```lean
theorem energy_step (i : ℕ) (hi : 0 < i) (w s1 s2 s3 : ℤ) :
    energy (i - 1) (step w (s1, s2, s3)) =
      energy i (s1, s2, s3) - w * q (i - 1)
```

## 83. `BTA-x3-n1-sign` &mdash; covers 0.19

*Reads as: a declaration is narrower than the claim (0.77).*

*Claim broader 0.48; declaration narrower 0.77; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** p ~ -p after N2+N1 iff 3^r | p

**Declaration.** `n21_sign_iff` &mdash; kernel-checked, `BTCalculus/CubicN1Valuation.lean:312`

> `p` and `-p` agree in both the `N2` and `N1` layers exactly when `3^r` divides `p`.

```lean
theorem n21_sign_iff {k r : Nat} (hk1 : 1 ≤ k) (hk : r + 1 ≤ k) (p : Int) :
    ((3 : Int) ^ k ∣ n2Resid (k - 1 - r) p - n2Resid (k - 1 - r) (-p)) ∧
        ((3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) (-p)) ↔
      (3 : Int) ^ r ∣ p
```

## 84. `BTN-sdsh-truncated-mod` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.51; different result 0.13.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If 3^L divides s-t and |w|≤L, then the lsd streams of F_{λ,U} from s and t agree on w. A remaining-horizon L controller therefore merges (s,q_L) and (t,q_L) whenever that congruence holds.

**Declaration.** `truncated_3adic_agree` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitShortHorizon.lean:28`

> A short horizon cannot see a deep congruence: if `3^L | s - t`, the signed traces from `s` and `t` agree on every word of length at most `L`.

```lean
theorem truncated_3adic_agree {gain s t : ℤ} {L : ℕ} {w : List ℤ}
    (hdvd : (3 : ℤ) ^ L ∣ s - t) (hw : w.length ≤ L) :
    signedTrace gain s w = signedTrace gain t w
```

## 85. `J-cycle-itinerary-length-eighty-four-m-ge-three-or-ge-eighty-five` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.31; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 84 with at least three odd-runs on a CycleMin rotation, or at least 85. At residual floor 261 the inv-sum form of cycleMin_finance (constant 1) plus a uniform odd-run height cap excludes every length-84 CycleMin with cycleCircuitCount ≤ 2: valleys ≤ m/n, first odds ≤ m/4217, later odds ≤ o/273845, evens ≤ e/n², using floorPower 261 = 4216 and floorPower 4217 = 273845. Lean theorems no_cycleMin_length_eighty_four_of_circuit_le_two and cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five in CycleHeightFinance.lean. This is not the 6/5 greedy packing of J-cycle-position-finance, not an exclusion of length 84 at m ≥ 3, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five` &mdash; kernel-checked, `Problems/Juggler/CycleHeightFinance.lean:921`

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

## 86. `J-fate-cylinder-corollary` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.78).*

*Claim broader 0.78; declaration narrower 0.47; different result 0.04.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Corollary 8.4 (the conjecture from a cylinder bound), as the composition of Theorem 8.3 in explicit form (row J-fate-tao-union-bound) with Theorem 7.2 (FateTaoReduction, tao_rate_implies_conjecture, the contagion bound of Theorem 5.3 as hypothesis). CylinderBound N₀ C A y is the paper's H(C, A) at the scale y: every O-rooted L(y)-bad cylinder of depth d(y) = ⌈C L(y)⌉ holds at most 2^{−(d−1)} y/2 + y (log y)^{−A} starts. (i) one_le_depth: d(y) ≥ 1 once 2y > N₀. (ii) oddFailures_eventually_le: for N₀ ≥ 2 with the floor, C ≥ 5, A > C + e(C), any e < e(C), and H(C, A) at all y ≥ y₁, there is y₀ with #{odd failures in (y, 2y]} ≤ y (log y)^{−e} for all y ≥ y₀; proof: Λ = log 2y / log N₀ satisfies log y / log N₀ ≤ Λ ≤ 2 log y / log N₀ for y ≥ 2, so the explicit bound y Λ^{−e(C)} + 2 Λ^C y  *(truncated; read the ledger row)*

**Declaration.** `cylinder_bound_implies_conjecture` &mdash; kernel-checked, `Problems/Juggler/FateCylinderCorollary.lean:185`

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

## 87. `J-paper-b-defect-coefficient-chain` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.83).*

*Claim broader 0.83; declaration narrower 0.28; different result 0.05.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** Paper B section 7's per-letter coefficient rule, as an identity rather than a table. For a word w over {O,E} write p_q = 3/2 if letter q is O and 1/2 if it is E, and e_t = prod_{q<=t} p_q, so J^t(n) sits at scale n^{e_t}. For letters s < t the coefficient of the phase variable theta_s inside letter t's phase is (k/2) E at exponent e_{t-1} - e_s, where E = prod_{q=s+1}^{t-1} p_q. Proof: letter t's wave is e(k J^{t-1}/2), and J^{t-1} depends on theta_s only through the chain of power maps between them; composing power maps composes to a single power, so the chain contributes exactly the product of its step exponents. The identity that makes this a rule and not a table is E = e_{t-1}/e_s, checked on every word of length 3..10 and every pair s < t -- 75768 instances, no exception. It reproduce  *(truncated; read the ledger row)*

**Declaration.** `chain_rule` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:96`

> **The chain rule.** `E = e_{t-1} / e_s`: the product of the step exponents strictly between letters `s` and `t` is the ratio of the iterate exponents at `t-1` and at `s`. `pre` is the prefix of length `s`, so `iter pre = e_s`; `mid` is the block of letters `s+1 … t-1`, so `iter mid = E` and `iter (pre ++ mid) = e_{t-1}`.

```lean
theorem chain_rule (pre mid : List Letter) :
    iter mid = iter (pre ++ mid) / iter pre
```

## 88. `J-paper-b-linearisation-E-lt-2` &mdash; covers 0.19

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.38; different result 0.2.  Tag EXACT — HUMAN PROOF, trust kernel.*

**Row.** The E < 2 linearisation criterion of Paper B section 7, as an identity. With the notation of J-paper-b-defect-coefficient-chain, the squared-defect term in letter t's phase sits at exponent e_{t-1} - 2 e_s, and since e_{t-1} = e_s E this equals e_s (E - 2). As e_s > 0 always, the second-order exponent is negative exactly when E < 2: linearising theta_s inside letter t is safe precisely on that condition. The criterion is therefore not a threshold fitted to the words that happen to survive -- it is the point at which the second-order term stops growing, and 2 is forced by the squaring and nothing else. Checked as an identity on every word of length 3..10 and every pair s < t (75768 instances, no exception), with the sign of the second-order exponent agreeing with E < 2 in every instance. Po  *(truncated; read the ledger row)*

**Declaration.** `linearise_iff` &mdash; kernel-checked, `Problems/Juggler/PaperBChainRule.lean:117`

> **The `E < 2` criterion.** The second-order exponent is negative exactly when `E < 2`. The equivalence is one-line given `second_order` and `iter_pos`, and that is the point: `2` is where the squared term stops growing, forced by the squaring and by nothing about which words survive.

```lean
theorem linearise_iff (pre mid : List Letter) :
    iter (pre ++ mid) - 2 * iter pre < 0 ↔ iter mid < 2
```

## 89. `BTC-op-fragment-nd-nf` &mdash; covers 0.2

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.22; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** the operator-fragment tree TRS {D, I_a, S, N} including N(D(x))→D(N(x)) is terminating and locally confluent; every term has a unique syntactic normal form

**Declaration.** `unique_normal_form` &mdash; kernel-checked, `BTCalculus/OpFragNewman.lean:381`

> Unique syntactic normal form of an operator-fragment term.

```lean
theorem unique_normal_form (t : OpFrag) :
    ∃ n, Normal n ∧ ReflTransGen Step t n ∧
      ∀ n', Normal n' → ReflTransGen Step t n' → n' = n
```

## 90. `J-mixed-oe-eighth` &mdash; covers 0.2

*Reads as: the claim asserts more than the declarations state (0.75).*

*Claim broader 0.75; declaration narrower 0.34; different result 0.11.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If x is odd and T(x) is even, then T^2(x) < n^2 if and only if x^3 < n^8. This is the mixed odd-cube / even-square cell. It is strictly sharper than composing a cube-band bound x < n^3 into T^2(x)^4 < n^9. An eighth-cell even lift that returns even is FiniteProgress; on MinimalNonTerm that return is odd. This is not a claim that every leftover landing stays below n^8, not a defect restriction, and not a halt theorem.

**Declaration.** `odd_even_eighth_lt_sq` &mdash; kernel-checked, `Problems/Juggler/CubeCorridor.lean:131`

> Mixed OE cell: an odd cube step followed by an even square step is the eighth-power comparison. This is strictly sharper than composing `x < n^3` into `T^2(x) < n^{9/4}`. Not a one-step envelope and not a defect restriction.

```lean
theorem odd_even_eighth_lt_sq {x n : ℕ}
    (hodd : x % 2 = 1) (he : floorPower x % 2 = 0) :
    floorPower (floorPower x) < n ^ 2 ↔ x ^ 3 < n ^ 8
```

## 91. `J-rate-free-prop-j-finite` &mdash; covers 0.21

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.3; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Finite Proposition J. If every length-d parity class w satisfies classCount w N * 2^d <= N + E * 2^d, then the number of starts in 1..N whose length-d itinerary is prefix-noncontracting obeys uncertifiedCount d N * 2^d <= neverNegCount d * (N + E * 2^d). Any finite set of starts in 1..N with no coefficient stop sits inside that uncertified set. Lean theorem propJ_count. Not a density-one claim and not a halt theorem.

**Declaration.** `propJ_count` &mdash; kernel-checked, `Problems/Juggler/RateFreeDensity.lean:216`

> Finite Proposition J. One-sided class bounds `#w(N) · 2^d ≤ N + E · 2^d` lift to the uncertified count.

```lean
theorem propJ_count (d N E : ℕ)
    (h : ∀ w ∈ allWords d, classCount w N * 2 ^ d ≤ N + E * 2 ^ d) :
    uncertifiedCount d N * 2 ^ d ≤ neverNegCount d * (N + E * 2 ^ d)
```

## 92. `J-small-cycle-census-eleven` &mdash; covers 0.21

*Reads as: the claim asserts more than the declarations state (0.93).*

*Claim broader 0.93; declaration narrower 0.38; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** No itinerary of length at most eleven is a Juggler cycle itinerary at any n ≥ 2; equivalently a nontrivial Juggler cycle, if one exists, has period at least twelve, and in fact at least fourteen by J-cycle-itinerary-length-ge-fourteen. Strengthened by J-small-cycle-census-eighteen. Length 11 is the first near-convergent (2^11 < 3^7); the residual floor 53 plus cycle_finance_min_fifty_three excludes it (finance_excludes_length_eleven, packaged as no_cycle_itinerary_length_le_eleven). This is a Lean companion to Paper A Theorem 4.6, not a leftover-itinerary census of the thirty length-11 short-gap families, not a theorem named no_cycle_itinerary_length_eleven, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `no_cycle_itinerary_length_le_eleven` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:342`

> Census extension: no cycle itinerary of length at most `11`. Lengths `≤ 10` are the prior census; `11` is finance at the residual floor `53`.

```lean
theorem no_cycle_itinerary_length_le_eleven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 11) : ¬CycleItinerary n w
```

## 93. `J-cycle-ooe-polynomial-block` &mdash; covers 0.22

*Reads as: the claim asserts more than the declarations state (0.85).*

*Claim broader 0.85; declaration narrower 0.53; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper A Proposition E.3, formal polynomial-block subset. For every odd r>=3, x=r^8+8,u=r^12+12r^4,v=r^18+18r^10+54r^2-1,z=r^9+9r-1 satisfy all three adjacent-square cells, x,u,z odd and v even, and the actual Juggler steps x->u->v->z. The direct iterate-three identity is proved. Kernel verified; this row does not cover the real-power quotient substitution estimates or assert a closed orbit.

**Declaration.** `ooeFamily_juggler_block` &mdash; kernel-checked, `Problems/Juggler/FamilyChains.lean:81`

```lean
theorem ooeFamily_juggler_block {r : ℕ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    floorPower (ooeFamilySource r) = ooeFamilyFirst r ∧
    floorPower (ooeFamilyFirst r) = ooeFamilySecond r ∧
    floorPower (ooeFamilySecond r) = ooeFamilyExit r
```

## 94. `J-cycle-quartic-formal-return` &mdash; covers 0.22

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.53; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 95. `J-fate-first-letter-split` &mdash; covers 0.22

*Reads as: the claim asserts more than the declarations state (0.76).*

*Claim broader 0.76; declaration narrower 0.34; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The exact layer of Paper C's first-letter identity (6.1). For a two-way closed class A (ForwardClosed and BackwardClosed), any weight w and any finite index set s, the weighted mass of A splits exactly into three pieces by first letter: the even members, the odd members with even image (OE-type) and the odd members with odd image (OO-type), each piece indexed by its image lying in A as the paper indexes it (first_letter_split); shellLogMass_split is the log-mass form on a shell (y, x]. The map J is strictly increasing on the odd integers (floorPower_odd_lt), hence injective there (floorPower_odd_injective), so the paper's odd preimage n(m) of the free term is well defined, and sum_image_ooPiece rewrites the OO-type piece as a sum over the odd images. This is the partition, with no error te  *(truncated; read the ledger row)*

**Declaration.** `first_letter_split` &mdash; kernel-checked, `Problems/Juggler/FateFirstLetter.lean:120`

> The members of `A` in a finite index set, weighted by `w`, split by first letter into the three pieces of Section 6.2: even, `OE`-type, `OO`-type. Each piece is indexed by its image lying in `A`, as the paper's `⊔_{m ∈ A}` writes it; that is the same set of `n` by two-way closure. The identity is exact: it is the partition, with no error term.

```lean
theorem first_letter_split {A : ℕ → Prop} (hF : ForwardClosed A) (hB : BackwardClosed A)
    (w : ℕ → ℝ) (s : Finset ℕ) :
    ∑ n ∈ {n ∈ s | A n}, w n =
      (∑ n ∈ {n ∈ s | n % 2 = 0 ∧ A (floorPower n)}, w n)
      + (∑ n ∈ {n ∈ s | n % 2 = 1 ∧ floorPower n % 2 = 0 ∧ A (floorPower n)}, w n)
      + (∑ n ∈ {n ∈ s | n % 2 = 1 ∧ floorPower n % 2 = 1 ∧ A (floorPower n)}, w n)
```

## 96. `BTJ-comp` &mdash; covers 0.23

*Reads as: the claim asserts more than the declarations state (0.59).*

*Claim broader 0.59; declaration narrower 0.37; different result 0.48.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** sectionDeriv_a(f.comp g)=sectionDeriv_{rho_a g} f compose sectionDeriv_a g

**Declaration.** `section_comp` &mdash; kernel-checked, `BTCalculus/Composition.lean:100`

> Section chain rule: `sectionDeriv a (f.comp g) = (sectionDeriv (lsd (eval a g)) f) .comp (sectionDeriv a g)` -- the outer factor is taken at the inner map's least significant digit, not at `a`.

```lean
theorem section_comp (f g : ℤ[X]) (a : ℤ) :
    sectionDeriv a (f.comp g) =
      (sectionDeriv (lsdZ (eval a g)) f).comp (sectionDeriv a g)
```

## 97. `C-endpoint` &mdash; covers 0.23

*Reads as: the claim asserts more than the declarations state (0.78).*

*Claim broader 0.78; declaration narrower 0.61; different result 0.52.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Kramer endpoint / 2-adic endpoint congruences

**Declaration.** `kramer_endpoint_congruence_zmod` &mdash; kernel-checked, `Problems/Collatz/Endpoint.lean:42`

> The affine endpoint equation gives Kramer's exact 3-adic endpoint congruence `2^K * x = C (mod 3^m)`.

```lean
theorem kramer_endpoint_congruence_zmod
    (m K R C x : ℕ)
    (hEndpoint : 3 ^ m * R + C = 2 ^ K * x) :
    ((2 ^ K * x : ℕ) : ZMod (3 ^ m)) =
      ((C : ℕ) : ZMod (3 ^ m))
```

## 98. `J-cycle-upper-charge-least-period` &mdash; covers 0.23

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

## 99. `J-exponent-expanding-append` &mdash; covers 0.23

*Reads as: the claim asserts more than the declarations state (0.84).*

*Claim broader 0.84; declaration narrower 0.35; different result 0.19.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If u and v are expanding itineraries (2^{|u|} < 3^{#O(u)} and 2^{|v|} < 3^{#O(v)}), then u ++ v is expanding: 2^{|u|+|v|} = 2^{|u|} 2^{|v|} < 3^{#O(u)} 3^{#O(v)}. A concatenation of expanding residual blocks is never an exponent-gap certificate. This is not a finite PE-run bound and not a halt theorem.

**Declaration.** `exponentExpanding_append` &mdash; kernel-checked, `Problems/Juggler/ItineraryStats.lean:189`

> Expanding itineraries are closed under concatenation. A concatenation of expanding residual blocks is never an exponent-gap certificate.

```lean
theorem exponentExpanding_append {u v : List Branch}
    (hu : exponentExpanding u) (hv : exponentExpanding v) :
    exponentExpanding (u ++ v)
```

## 100. `J-fate-contagion-conditional` &mdash; covers 0.23

*Reads as: the claim asserts more than the declarations state (0.78).*

*Claim broader 0.78; declaration narrower 0.43; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Theorem 5.3 (contagion) given the production inequality (5.2), for every 0 < λ ≤ 0.49. Data: productionRate/productionCoeff are the eight productions (e_i, c_i) = (1/2, 1), (3/8, 1/9), (3/4, 2/9), (9/32, 1/27), (27/128, 1/81), (81/512, 1/243), (243/2048, 1/729), (729/8192, 1/2187); zeta λ = Σ c_i e_i^λ − 1 is antitone in λ (zeta_antitone) and zeta (49/100) > 0 (zeta_pos_49): each e_i^{49/100} is bounded below by a five-digit rational r_i through r_i^100 ≤ e_i^49 in exact integer arithmetic (le_rpow_div_of_pow_le), and Σ c_i r_i − 1 = 0.00168 > 0 (the exact value of ζ(0.49) is 0.001683; the paper's root is λ** = 0.4926). gA A t = halfLogMass A ⌊e^t⌋₊ is the paper's g_A(t) (the integers in (√x, x] are those in (⌊√⌊x⌋⌋, ⌊x⌋]); gA_seed is Lemma 5.2 in the form g_A(t) ≥ c_A for t ≥ 4 lo  *(truncated; read the ledger row)*

**Declaration.** `contagion_of_production_inequality` &mdash; kernel-checked, `Problems/Juggler/FateContagionBound.lean:253`

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

## 101. `J-fate-dyadic-pigeonhole` &mdash; covers 0.23

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.25; different result 0.04.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Corollary 5.4 (natural density, infinitely often): the dyadic pigeonhole, from a shell bound. If K (log X)^lambda <= sum_{sqrt X < n <= X, n in A} 1/n with 0 < lambda <= 1, K > 0 and X >= 3, then some y with sqrt X < y <= X has #(A cap (y/2, y]) >= (K/12) y (log y)^(lambda-1) (Density.exists_block_of_shell; the block is Ioc (y/2) y in the natural numbers, blockCount). PROOF, the manuscript's: the shell (sqrt X, X] is covered by the blocks (X/2^(j+1), X/2^j] for j <= log_2 X, at most 3 log X of them since log 2 > 1/2 (halfLogMass_le_blocks, through Finset.sum_fiberwise_of_maps_to on j = floor(log_2(X/n)), block_index); a block's log-mass is at most 2 #/y because every member exceeds y/2 (block_logMass_le); the best block is at least the average (Finset.exists_le_of_sum_le); and y^2   *(truncated; read the ledger row)*

**Declaration.** `exists_block_of_shell` &mdash; kernel-checked, `Problems/Juggler/FateDyadicDensity.lean:127`

> **Paper C Corollary 5.4, the pigeonhole.** If the shell log-mass of `A` at `X ≥ 3` is at least `K (log X)^λ` with `0 < λ ≤ 1`, then some block `(y/2, y]` with `√X < y ≤ X` holds at least `(K/12) y (log y)^{λ-1}` members of `A`.

```lean
theorem exists_block_of_shell (A : ℕ → Prop) {K lam : ℝ} (hK : 0 < K) (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) {X : ℕ} (hX : 3 ≤ X)
    (h : K * Real.log X ^ lam ≤ halfLogMass A X) :
    ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      K / 12 * y * Real.log y ^ (lam - 1) ≤ (blockCount A y : ℝ)
```

## 102. `BTN-sdsh-maxlen` &mdash; covers 0.24

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.85; different result 0.09.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If λ is not divisible by 3 and s≠t, the lsd streams of F_{λ,U} agree on a word w if and only if |w|≤v_3(s-t). A finite control language therefore merges (s,q) and (t,q) exactly when every legal word is shorter than v_3(s-t)+1.

**Declaration.** `control_language_separation` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitShortHorizon.lean:100`

> The separating length is `v3 (s - t) + 1`: for `gain` not divisible by `3` and `s != t`, any word that long distinguishes the signed traces. With `truncated_3adic_agree` this pins agreement to exactly `|w| <= v3 (s - t)`.

```lean
theorem control_language_separation {gain s t : ℤ} {w : List ℤ}
    (hgain : ¬ (3 : ℤ) ∣ gain) (hne : s ≠ t)
    (hw : intVal3 (s - t) + 1 ≤ w.length) :
    signedTrace gain s w ≠ signedTrace gain t w
```

**Doubtful from here: coverage between 0.25 and 0.5.**

## 103. `BTA-x3-n1-fibre` &mdash; covers 0.25

*Reads as: the claim asserts more than the declarations state (0.71).*

*Claim broader 0.71; declaration narrower 0.65; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** every nontrivial N2+N1 fibre on P_m lies in 3^r Z

**Declaration.** `n21_fibre_in_pow` &mdash; kernel-checked, `BTCalculus/CubicN1Valuation.lean:265`

> Every nontrivial `N2`-then-`N1` fibre lies in `3^r ZZ`: distinct `p != q` of balanced width `k-1-r` that agree in both layers force `3^r | p`.

```lean
theorem n21_fibre_in_pow {k r : Nat} (hr : 1 ≤ r) (hk : r + 1 ≤ k)
    {p q : Int}
    (hpw : balWidth (k - 1 - r) p) (hqw : balWidth (k - 1 - r) q)
    (hne : p ≠ q)
    (hN2 : (3 : Int) ^ r ∣ p - q)
    (hN1 : (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q) :
    (3 : Int) ^ r ∣ p
```

## 104. `BTN-dadd-closure` &mdash; covers 0.25

*Reads as: the claim asserts more than the declarations state (0.8).*

*Claim broader 0.8; declaration narrower 0.65; different result 0.22.  Tag EXACT — LEAN VERIFIED, trust compiler.*

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

## 105. `BTN-step-value` &mdash; covers 0.25

*Reads as: the claim asserts more than the declarations state (0.69).*

*Claim broader 0.69; declaration narrower 0.61; different result 0.43.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** value(P → P') = value(P)

**Declaration.** `step_value` &mdash; kernel-checked, `BTCalculus/Normalization.lean:98`

> The normalising step at any index preserves the value.

```lean
theorem step_value (cs : List ℤ) (i : ℕ) :
    coeffValue (step cs i) = coeffValue cs
```

## 106. `J-cubic-remainder-assembly` &mdash; covers 0.25

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

## 107. `J-cycle-cubic-band-order` &mdash; covers 0.25

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

## 108. `J-cyclemin-fudge` &mdash; covers 0.25

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.36; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The thirty first-expanding four-even short-gap leftovers O^{a0} E O^{a1} E O^{a2} E O^{a3} E are not CycleMin words. On a CycleMin every later state is >= n, so the exact cells compose by absorb_odd_step and absorb_even_step: n^A < (n+1)^B (x+1)^γ implies n^{A+γ} < (n+1)^{B+γ} (isqrt(x)+1)^{2γ}. After the prefix, cycle_trailing_evens_lt puts the image below (n+1)^{2^r}. Any 7-odd word that starts O keeps γ a power of two and raises on each later odd, so the slack is identically 3^7-2^{11}=139, independent of even placement. For n >= 30 and A <= 13905 the comparison is (n+1)^{A-139} < n^A; no n with 2 <= n < 30 follows any of the thirty prefixes. The eight leftovers whose only CycleMin-shaped rotation is themselves (OOOOOOOEEEE, OOOOOOEOEEE, OOOOOOEEEOE, OOOOOEOEEOE, OOOOOOEEOEE, OOOOOEOEOE  *(truncated; read the ledger row)*

**Declaration.** `no_cycleMin_cyclemin_fudge` &mdash; kernel-checked, `Problems/Juggler/CycleMinFudge.lean:806`

> The thirty first-expanding short-gap leftovers are not `CycleMin` words. Not a length-11 census.

```lean
theorem no_cycleMin_cyclemin_fudge {n : ℕ} {w : List Branch}
    (hw : w ∈ fudgeWords) (h : CycleMin n w) : False
```

## 109. `BTA-x3-n1-diff` &mdash; covers 0.26

*Reads as: the claim asserts more than the declarations state (0.74).*

*Claim broader 0.74; declaration narrower 0.66; different result 0.3.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** after N2, N1 agrees iff 3^{k-1-r} | δ(p+q+3^m)

**Declaration.** `n1_after_n2_iff` &mdash; kernel-checked, `BTCalculus/CubicN1Valuation.lean:46`

> Once `N2` is fixed, the depth-`k-1-r` `N1` residuals agree to order `3^k` exactly when `3^(k-1-r)` divides `d * (p + q + 3^(k-1-r))`, where `p - q = 3^r * d`.

```lean
theorem n1_after_n2_iff {k r : Nat} (hk : 1 ≤ k) (hr : r + 1 ≤ k)
    {p q d : Int} (hd : p - q = (3 : Int) ^ r * d) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q ↔
      (3 : Int) ^ (k - 1 - r) ∣ d * (p + q + (3 : Int) ^ (k - 1 - r))
```

## 110. `BTL-zero-output` &mdash; covers 0.26

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

## 111. `J-small-cycle-census-seven` &mdash; covers 0.26

*Reads as: the claim asserts more than the declarations state (0.91).*

*Claim broader 0.91; declaration narrower 0.35; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** No itinerary of length at most seven is a Juggler cycle itinerary at any n ≥ 2; equivalently a nontrivial Juggler cycle, if one exists, has period at least eight (Paper A Theorem 3.8). Assembly: the length-≤6 census, the formal-expansion filter on length seven, the odd-run exclusion of O^6E, the internal-E bootstrap exclusions of OOEOOOE and OOOEOOE, rotation of EOOOOOE and OEOOOOE onto the leftovers, and the leftover exclusions of OOOOEOE and OOOOOEE (Lemma 3.7). Lean theorem no_cycle_itinerary_length_le_seven. Strengthened by Paper A Theorem 3.22 / Corollary 3.23 (even-count at most three is impossible, so the period is at least eleven). This is not an exclusion of all cycles and not a halt theorem.

**Declaration.** `no_cycle_itinerary_length_le_seven` &mdash; kernel-checked, `Problems/Juggler/SmallCycleCensus.lean:220`

> **Small-cycle census.** No `n ≥ 2` realizes a cycle itinerary of length at most seven. Length eight and beyond is open.

```lean
theorem no_cycle_itinerary_length_le_seven {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 7) : ¬CycleItinerary n w
```

## 112. `J-cyclemin-period-lower-bound` &mdash; covers 0.27

*Reads as: a declaration is narrower than the claim (0.74).*

*Claim broader 0.57; declaration narrower 0.74; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Floor-free period lower bound. Under the same budget C · L^{−p} ≤ Λ, a nontrivial Juggler cycle of minimum n has period L ≥ (C n log n / 2)^{1/(p+1)} (cycleMin_period_ge; Wu–Wang form cycleMin_period_ge_wuWang). This is Paper A Corollary 4.11 read as a bound on the period rather than the minimum, and it is the only proved statement in which a cycle's period grows with its minimum — the descent floor is a constant. The exponent in n rises from 1/14.3 = 0.0699 with Rhin to 1/5.1163051 = 0.1954 with Wu–Wang (wu-wang-2014-irrationality-measure-log3, |a + b log 2 + c log 3| ≥ H^{−4.1163051−ε} at a = 0, H = max(L, o) = L). Distinct from the fan-width cap of juggler_cycle_walk_fan_growth and from the REFUTED floor-level Baker transfer of juggler_cycle_gap_baker: no floor enters and nothing is exc  *(truncated; read the ledger row)*

**Declaration.** `cycleMin_period_ge` &mdash; kernel-checked, `Problems/Juggler/GapTransferWW.lean:106`

> **The same inequality read as a period lower bound.** Under the same Diophantine budget, a nontrivial cycle of minimum `n` has period at least `(C * n log n / 2)^{1/(p+1)}`. No descent floor enters: the bound grows with the minimum, which is the one direction the finite tables cannot supply. At `p = 13.3` (Rhin) the exponent in `n` is `1/14.3 = 0.0699...`; at `p = 4.1163051` (Wu-Wang) it is `1/5.1163051 = 0.1954...`.

```lean
theorem cycleMin_period_ge {n : ℕ} {w : List Branch} {C p : ℝ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hL : 0 < w.length)
    (hC0 : 0 < C) (hC1 : C ≤ 1) (hp : 0 ≤ p)
    (hgap : C * (w.length : ℝ) ^ (-p) ≤
              (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) :
    (C / 2 * ((n : ℝ) * Real.log n)) ^ (1 / (p + 1)) ≤ (w.length : ℝ)
```

## 113. `OST-np-particular-s3` &mdash; covers 0.27

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.44; different result 0.18.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, from the origin the third coordinate of the control particular equals minus the MSD consumed valuation: (particularSum ws)_3 = -consumedSum |ws| ws, so val(B)=0 iff c_B lies on F={s_3=0}; this is energy_telescope at n=0, not a bound on L_0

**Declaration.** `particular_s3` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:556`

> From the origin, `(c_B)₃ = -val(B)`. KNOWN energy at `n=0`, not `L₀`.

```lean
theorem particular_s3 (ws : List ℤ) :
    (particularSum ws).2.2 = -consumedSum ws.length ws
```

## 114. `BTN-confluence` &mdash; covers 0.3

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

## 115. `BTN-sdrg-lambda1-interval` &mdash; covers 0.31

*Reads as: the claim asserts more than the declarations state (0.9).*

*Claim broader 0.9; declaration narrower 0.5; different result 0.11.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For λ=1 and U_m, every integer s with |s|≤⌊m/2⌋ is reached from 0 by an admissible word. The explicit positive word is u=2,4,...,2n.

**Declarations.** `lambda1_interval_reachable` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidualGeometry.lean:80`

> Every nonnegative point of the ``λ=1`` box is reached by an admissible word.

```lean
theorem lambda1_interval_reachable (m n : ℕ) (h : n ≤ m / 2) :
    ∃ word : List ℤ, (∀ u ∈ word, u.natAbs ≤ m) ∧ foldSigned 1 word 0 = n
```

**And.** `lambda1_interval_reachable_neg` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidualGeometry.lean:96`

> Every nonpositive point of the `lambda=1` box is reached by an admissible word; the negative half of `lambda1_interval_reachable`.

```lean
theorem lambda1_interval_reachable_neg (m n : ℕ) (h : n ≤ m / 2) :
    ∃ word : List ℤ, (∀ u ∈ word, u.natAbs ≤ m) ∧
      foldSigned 1 word 0 = - (n : ℤ)
```

## 116. `J-cyclemin-prefix-bunched-eoee` &mdash; covers 0.31

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

## 117. `OST-np-fold-s3` &mdash; covers 0.31

*Reads as: the claim asserts more than the declarations state (0.79).*

*Claim broader 0.79; declaration narrower 0.4; different result 0.1.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, after an MSD word B from any residual s, (T_B(s))_3 = E_|B|(s) - val(B), so T_B(s) lies on F iff E_|B|(s)=val(B); this is energy_telescope at remaining 0, not a bound on L_0

**Declaration.** `fold_s3` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:565`

> From any start state, `(T_B(s))₃ = E_{|B|}(s) - val(B)`. KNOWN `energy_telescope` at remaining 0, not `L₀`.

```lean
theorem fold_s3 (ws : List ℤ) (s : State) :
    (foldSteps ws s).2.2 =
      energy ws.length s - consumedSum ws.length ws
```

## 118. `BTA-x3-inter-lift` &mdash; covers 0.32

*Reads as: the claim asserts more than the declarations state (0.8).*

*Claim broader 0.8; declaration narrower 0.39; different result 0.16.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** horizon k refines k-1 at depth k-2; unit signs split

**Declaration.** `inter_horizon_refines` &mdash; kernel-checked, `BTCalculus/CubicIntermediateLayer.lean:143`

> Horizon refinement at depth `k-2`: agreement of the `N2`, `N1` and `N0` residuals to order `3^k` carries down to order `3^(k-1)` for each of the three.

```lean
theorem inter_horizon_refines {k : ℕ} (_hk : 1 ≤ k) (p q : ℤ)
    (h2 : (3 : ℤ) ^ k ∣ n2Resid (k - 2) p - n2Resid (k - 2) q)
    (h1 : (3 : ℤ) ^ k ∣ n1Resid (k - 2) p - n1Resid (k - 2) q)
    (h0 : (3 : ℤ) ^ k ∣ n0Resid (k - 2) p - n0Resid (k - 2) q) :
    ((3 : ℤ) ^ (k - 1) ∣ n2Resid (k - 2) p - n2Resid (k - 2) q) ∧
      ((3 : ℤ) ^ (k - 1) ∣ n1Resid (k - 2) p - n1Resid (k - 2) q) ∧
        ((3 : ℤ) ^ (k - 1) ∣ n0Resid (k - 2) p - n0Resid (k - 2) q)
```

## 119. `BTC-add-requires-carry-state` &mdash; covers 0.32

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

## 120. `J-cyclemin-walk-transport-envelope` &mdash; covers 0.32

*Reads as: the claim asserts more than the declarations state (0.79).*

*Claim broader 0.79; declaration narrower 0.33; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** The transport inequality of Paper A Theorem 5.3, Lean end to end in log form. On a CycleMin cycle with minimum n ≥ 400, every state satisfies walkWeight w k · (log n − D) ≤ log x_k with walkWeight w k = 3^(a_k)/2^k (the walk weight 2^(u_k), rational — no real exponentiation) and D = 1.05·e/n + 0.7·o/(n·√n) (cycleMin_transport, WalkTransport.lean); exponentiating gives x_k ≥ (n e^(−D))^(w_k). Ingredients all Lean: per-step floor losses log T(x) ≥ (3/2)·log x − 1.05/(x√x) (odd, x ≥ 9) and log T(x) ≥ (1/2)·log x − 1.05/√x (even, x ≥ 441) from the floor cells and −log(1−t) ≤ 1.05t on t ≤ 1/21 (log_floorPower_odd_ge, log_floorPower_even_ge, neg_log_one_sub_le); the exact weight recursion w_{k+1} = (3/2)w_k (odd), w_k/2 (even); odd injections priced at x_j ≥ n (cycleMin_iterate_ge) against w_{j+  *(truncated; read the ledger row)*

**Declaration.** `cycleMin_transport` &mdash; kernel-checked, `Problems/Juggler/WalkTransport.lean:453`

> **Transport to a reduced base** (Paper A Theorem 5.3, log form): on a minimum-based cycle with minimum `n ≥ 400`, every state satisfies `w_k·(log n − D) ≤ log x_k` with `D = 1.05·e/n + 0.7·o/(n·√n)`. Exponentiating gives `x_k ≥ (n e^{−D})^{w_k}`. Closed instance of `aboveAnchor_transport`.

```lean
theorem cycleMin_transport {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w) {k : ℕ} (hk : k ≤ w.length) :
    walkWeight w k * (Real.log n - transportDeficit n w) ≤
      Real.log (floorPower^[k] n)
```

## 121. `J-fate-pressure-form` &mdash; covers 0.32

*Reads as: the claim asserts more than the declarations state (0.56).*

*Claim broader 0.56; declaration narrower 0.28; different result 0.04.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Theorem 9.2 (pressure form), exact. On the live weight of LiveCountWeight (starts n in {1, …, N} with J^i(n) > N₀ for i ≤ d, liveTo): livePressure N₀ N x d := weightGen (liveWeight N₀ N) x d = Σ_{n live} x^{o_d(n)}; the Markov step live_count_le_pressure gives #{n live, o_d(n) ≥ k} ≤ livePressure / x^k for x ≥ 1 (weight_markov on the live weight, liveCount_sum_oddCount); Lemma 8.1 on live starts: a live n ≤ N has an itinerary that fails the envelope comparison at scale N at every prefix (envelopeBad_of_liveTo, from iterate_le_of_envelope), hence is L(N)-bad with L(N) = log_2(log N / log N₀) (LBad_of_liveTo) and has o_d ≥ p_C d when d ≥ C L(N) (live_oddCount_ge). Theorem: N₀ ≥ 2, N ≥ 2, C ≥ 5, d ≥ 1, d ≥ C L(N), tilt x = p_C/(1 − p_C), a = (1 + x)/2; if livePressure N₀ N x d ≤ N a^d  *(truncated; read the ledger row)*

**Declaration.** `live_count_le_of_pressure` &mdash; kernel-checked, `Problems/Juggler/FatePressure.lean:83`

> **Theorem 9.2 (pressure form), exact.** Floor `N₀ ≥ 2`, scale `N ≥ 2`, `C ≥ 5`, depth `d ≥ 1` with `d ≥ C L(N)`, tilt `x = p_C/(1-p_C)`, `a = (1 + x)/2`. If the live pressure at depth `d` is at most `N a^d E`, then the starts in `{1, …, N}` that stay above `N₀` for `d` steps number at most `N exp(-d D(p_C ‖ 1/2)) E`.

```lean
theorem live_count_le_of_pressure (N₀ N : ℕ) (hN : 2 ≤ N₀) (hNN : 2 ≤ N) (C : ℝ)
    (hC : 5 ≤ C) (d : ℕ) (hd1 : 1 ≤ d)
    (hd : C * Real.logb 2 (Real.log N / Real.log N₀) ≤ d) (E : ℝ)
    (hP : livePressure N₀ N (pC C / (1 - pC C)) d ≤
      N * ((1 + pC C / (1 - pC C)) / 2) ^ d * E) :
    (((Icc 1 N).filter (fun n => liveTo N₀ n d)).card : ℝ) ≤
      N * Real.exp (-(d * klHalf (pC C))) * E
```

## 122. `BTN-doubled-minimality` &mdash; covers 0.33

*Reads as: the claim asserts more than the declarations state (0.89).*

*Claim broader 0.89; declaration narrower 0.34; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust compiler.*

**Row.** The three carries -1,0,1 have pairwise distinct Mealy output signatures, so the 3-state machine is minimal.

**Declaration.** `doubledTrit_outputSignatures_distinct` &mdash; compiler-checked, `Problems/BalancedTernary/FiniteStateDynamics.lean:160`

> The three carries `-1`, `0` and `1` have pairwise distinct Mealy output signatures, so the three-state machine is minimal.

```lean
theorem doubledTrit_outputSignatures_distinct :
    outSig 0 ≠ outSig 1 ∧ outSig 0 ≠ outSig (-1) ∧ outSig 1 ≠ outSig (-1)
```

## 123. `BTN-sdr-escape-general` &mdash; covers 0.33

*Reads as: the claim asserts more than the declarations state (0.79).*

*Claim broader 0.79; declaration narrower 0.3; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If λ≥3 and |u|≥2 then the constant-control orbit of F_{λ,U} from 0 is unbounded: at λ=3 one has s'=s+u-lsd(s+u) so each step moves by at least 1; at λ≥4 the step is strictly expanding on the matching ray.

**Declaration.** `signedIterate_unbounded_of_ge_three` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidual.lean:330`

> Escape at every gain `>= 3`: if `|u| >= 2`, the constant-control orbit from `0` is unbounded -- for each bound `B` some iterate exceeds it. This is the witness matching `finite_residual_condition`.

```lean
theorem signedIterate_unbounded_of_ge_three {gain u : ℤ}
    (hg : (3 : ℤ) ≤ gain) (hu : 2 ≤ u ∨ u ≤ -2) (B : ℕ) :
    ∃ n : ℕ, B < (signedIterate gain u n).natAbs
```

## 124. `J-cycle-itinerary-length-eighty-four-or-ge-eighty-five` &mdash; covers 0.33

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.23; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 84 or at least 85. Lengths ≤ 56 are excluded at floor 257; lengths 57–83 are excluded by cycle_finance_min_two_hundred_sixty_one at 15921/11 (finance_excludes_length_fiftyseven, finance_excludes_length_seventysix, and companions, packaged as no_cycle_itinerary_length_lt_eighty_four). Length 84 is the next record near-convergent (need ≈ 40269). Lean theorem cycle_itinerary_length_eighty_four_or_ge_eighty_five. Strengthened by J-cycle-itinerary-length-eighty-four-m-ge-three-or-ge-eighty-five, which kills length 84 with at most two odd-runs, and by J-cycle-itinerary-eliahou-leftover, which rewrites the length leftover plus the finance table as period 84, a listed near-convergent, or at least 10^5. This is not a no-cycle-of  *(truncated; read the ledger row)*

**Declaration.** `cycle_itinerary_length_eighty_four_or_ge_eighty_five` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:847`

> If a nontrivial cycle exists, its period is `84` or at least `85`. The cheap leftovers `57` and `76` die at the residual floor `261`; `58`–`75` and `77`–`83` die by the same comparison. `L=84` is the next record near-convergent.

```lean
theorem cycle_itinerary_length_eighty_four_or_ge_eighty_five
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 84 ∨ 85 ≤ w.length
```

## 125. `J-cycle-itinerary-length-fifty-seven-or-ge-fifty-eight` &mdash; covers 0.33

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

## 126. `J-cycle-quartic-formal-gap-separation` &mdash; covers 0.33

*Reads as: the claim asserts more than the declarations state (0.64).*

*Claim broader 0.64; declaration narrower 0.59; different result 0.3.  Tag EXACT — LEAN VERIFIED, trust kernel.*

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

## 127. `J-cyclemin-prefix-two-even-eoe` &mdash; covers 0.33

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

## 128. `J-fate-cylinder-energy` &mdash; covers 0.33

*No failure mode above the line; coverage itself is doubtful.*

*Claim broader 0.34; declaration narrower 0.3; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Section 10(d), the counting half of the Parseval display. For an arbitrary finite set S of starts, write #[w] for the starts of S whose length-|w| itinerary is w (wordCount), D(w) = #[wO] - #[w]/2 for the first-letter bias (bias) and C_t = sum over |w| = t of #[w]^2 for the cylinder energy (energy). A cylinder splits into its two children, #[w] = #[wE] + #[wO] (wordCount_split), because the (t+1)-st letter of an itinerary is the parity of the t-th image (itinerary_succ_append). Hence sum over |w| = t of D(w)^2 = C_{t+1}/2 - C_t/4 exactly (sum_bias_sq), which is the second equality of the note's display; the algebra behind it is (b - (a+b)/2)^2 = (a^2+b^2)/2 - (a+b)^2/4. NOT formalized: the first equality, Parseval for the Walsh sums on the same starts -- no Walsh transform appears   *(truncated; read the ledger row)*

**Declaration.** `sum_bias_sq` &mdash; kernel-checked, `Problems/Juggler/FateCylinderEnergy.lean:114`

> **The counting identity of Section 10(d).** `Σ_{|w|=t} D(w)² = C_{t+1}/2 - C_t/4`, exactly. The Parseval form of the same quantity in terms of Walsh sums is not formalized.

```lean
theorem sum_bias_sq (S : Finset ℕ) (t : ℕ) :
    ∑ w ∈ allWords t, bias S w ^ 2 = energy S (t + 1) / 2 - energy S t / 4
```

## 129. `BTL-trichotomy` &mdash; covers 0.34

*Reads as: the claim asserts more than the declarations state (0.82).*

*Claim broader 0.82; declaration narrower 0.35; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** KNOWN, restated: for k >= 1 a level-k node has 1 child if 3 does not divide f'(n), 3 children if 3 divides f'(n) and v_3(f(n)) >= k+1, and none otherwise; the hypothesis k >= 1 is needed, since x^2 + x has two children at the root with a unit derivative

**Declaration.** `lift_trichotomy` &mdash; kernel-checked, `BTCalculus/PadicLifting.lean:259`

> The trichotomy in one statement: at a level-`k` node with `k ≥ 1` the set of lifting trits is a singleton, all of `{-1,0,1}`, or empty.

```lean
theorem lift_trichotomy (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) {x c : ℤ}
    (hc : eval x f = 3 ^ k * c) :
    (∃! t : ℤ, isTrit t ∧ IsRootMod (k + 1) f (x + 3 ^ k * t)) ∨
      (∀ t : ℤ, IsRootMod (k + 1) f (x + 3 ^ k * t)) ∨
      (∀ t : ℤ, ¬ IsRootMod (k + 1) f (x + 3 ^ k * t))
```

## 130. `J-cycle-itinerary-length-nineteen-or-ge-thirty` &mdash; covers 0.35

*Reads as: the claim asserts more than the declarations state (0.86).*

*Claim broader 0.86; declaration narrower 0.25; different result 0.05.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** If a nontrivial Juggler cycle itinerary exists at n ≥ 2, its period is 19 or at least 30. Lengths ≤ 18 are J-small-cycle-census-eighteen; lengths 20–29 are excluded by the same floor-53 finance comparison. Length 19 is the next near-convergent (2^19 < 3^12) and survives 371/2; length 30 also survives 371/2. Lean theorems cycle_itinerary_length_nineteen_or_ge_thirty and the weaker corollary cycle_itinerary_length_nineteen_or_ge_twenty. This row is the floor-53 leftover. Strengthened by J-cycle-itinerary-length-thirty-eight-or-ge-thirty-nine, which kills the length-19 disjunct at the residual floor 257. This is not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `cycle_itinerary_length_nineteen_or_ge_thirty` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:469`

> If a nontrivial cycle exists, its period is `19` or at least `30`. The gap `20..29` dies by finance at the residual floor `53`; `19` is the next near-convergent (`2^19 < 3^12`).

```lean
theorem cycle_itinerary_length_nineteen_or_ge_thirty {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    w.length = 19 ∨ 30 ≤ w.length
```

## 131. `OST-np-origin-particular` &mdash; covers 0.35

*Reads as: the claim asserts more than the declarations state (0.87).*

*Claim broader 0.87; declaration narrower 0.26; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, from the origin an MSD word ws unfolds by variation of constants: foldSteps ws origin equals the particular sum −∑ A^{k-1-j} e3 w_j; this is not a bound on L_0

**Declaration.** `origin_particular` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:537`

> From the origin, an MSD word unfolds by variation of constants: `foldSteps ws origin = particularSum ws`.

```lean
theorem origin_particular (ws : List ℤ) :
    foldSteps ws origin = particularSum ws
```

## 132. `C-shortcut-welldefined` &mdash; covers 0.36

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

## 133. `C-T-welldefined` &mdash; covers 0.37

*Reads as: a declaration is narrower than the claim (0.74).*

*Claim broader 0.67; declaration narrower 0.74; different result 0.13.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Accelerated T is well-defined on positive odd integers.

**Declaration.** `acceleratedT_odd` &mdash; kernel-checked, `Problems/Collatz/Accelerated.lean:41`

> ``T`` sends a positive odd integer to a positive odd integer.

```lean
theorem acceleratedT_odd {n : ℕ} (_hn : Odd n) (hpos : 0 < n) :
    Odd (acceleratedT n)
```

## 134. `OST-np-same-energy-same-OnF` &mdash; covers 0.37

*Reads as: the claim asserts more than the declarations state (0.75).*

*Claim broader 0.75; declaration narrower 0.41; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, if E_|v|(s)=E_|v|(t) then T_v(s) lands on F iff T_v(t) does; length-n suffix acceptance is classified by E_n, not by residual coordinates. This is fold_on_F_iff, not a bound on L_0

**Declaration.** `fold_on_F_iff` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:575`

> Length-`n` suffix acceptance is classified by the energy, not by residual coordinates: `foldSteps ws s` lands on `F` exactly when `energy |ws| s` equals the consumed sum of `ws`.

```lean
theorem fold_on_F_iff (ws : List ℤ) (s : State) :
    OnF (foldSteps ws s) ↔
      energy ws.length s = consumedSum ws.length ws
```

## 135. `J-fate-monotone-pairing-repair` &mdash; covers 0.38

*Reads as: the claim asserts more than the declarations state (0.57).*

*Claim broader 0.57; declaration narrower 0.38; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Lemma 4.1' (monotone pairing), with a corrected proof and the same constant. Hypotheses of Lemma 4.1 (steps in [a, b], 0 < a ≤ b ≤ 1/2, b ≤ 21a/20, (H−1) a ≥ 12) plus monotone steps: each half-cell colour receives at least H/3 − 2 terms, in both cell conventions. The proof printed until 2026-09-08 claimed every pair of consecutive cells (ρ, ρ') has min ≥ (ρ+ρ')/3, deduced from a step scale that 'drops by at most X/21 spread over the cells'; monotonicity does not give gradual change, and a = 10/41, b = 21/82 with points −2a, −a, 0, a, 2a, 2a+b, 2a+2b, … (nondecreasing steps) has the interior pair (3, 1), ratio 1/4. It also paired the two partial end cells as if interior. Corrected proof: (a) for interior i < j, ρ_j ≤ ρ_i + 1, because the ρ_i + 1 steps across cell i span more than 1/  *(truncated; read the ledger row)*

**Declaration.** `sweep_monotone_fract_lt_half` &mdash; kernel-checked, `Problems/Juggler/FateSweepMonotone.lean:2357`

> Paper C Lemma 4.1′: at least `H/3 - 2` of the terms have `{x_j} < 1/2`.

```lean
theorem sweep_monotone_fract_lt_half (x : ℕ → ℝ) (H : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) (hba : b ≤ 21 / 20 * a)
    (h12 : 12 ≤ ((H : ℝ) - 1) * a)
    (hs : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ b)
    (hmono : MonoSteps x H ∨ AntiSteps x H) :
    (H : ℝ) / 3 - 2 ≤ #{j ∈ Finset.range H | Int.fract (x j) < 1 / 2}
```

## 136. `J-odd-image-upper-square-gap` &mdash; covers 0.38

*Reads as: a declaration is narrower than the claim (0.64).*

*Claim broader 0.56; declaration narrower 0.64; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** For odd natural numbers x and y with x^3<(y+1)^2, one has x^3+3<=(y+1)^2. If the positive odd upper-square complement were one, then y(y+2)=x^3; coprimality forces two positive cubes differing by two, which is impossible. Specialized in Lean to every actual odd-to-odd floorPower edge. This is a local arithmetic refinement only; no no-cycle conclusion, period or descent-floor improvement, or external novelty is claimed. The subsequent logarithmic cap comparison and global symbolic audits are written analysis, outside this Lean claim.

**Declarations.** `cube_add_one_ne_odd_succ_sq` &mdash; kernel-checked, `Problems/Juggler/UpperSquareGap.lean:45`

> A cube cannot be one below the successor square of an odd natural number.

```lean
theorem cube_add_one_ne_odd_succ_sq {x y : ℕ} (hy : y % 2 = 1) :
    x ^ 3 + 1 ≠ (y + 1) ^ 2
```

**And.** `floorPower_odd_image_upper_gap` &mdash; kernel-checked, `Problems/Juggler/UpperSquareGap.lean:69`

> Every actual odd-to-odd Juggler edge has upper square complement at least three.

```lean
theorem floorPower_odd_image_upper_gap {x : ℕ}
    (hx : x % 2 = 1) (hy : floorPower x % 2 = 1) :
    x ^ 3 + 3 ≤ (floorPower x + 1) ^ 2
```

## 137. `BTA-x3-def2-crit` &mdash; covers 0.39

*Reads as: the claim asserts more than the declarations state (0.51).*

*Claim broader 0.51; declaration narrower 0.44; different result 0.14.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** m=k-3 fibres iff p≡q (mod 9) and 3^{k-1}|(p-q)(p+q+3^{k-3}) and N0 agrees

**Declaration.** `deficitTwo_equiv_iff` &mdash; kernel-checked, `BTCalculus/CubicDeficitTwo.lean:134`

> The deficit-two fibre criterion: `N2` and `N1` agreement at depth `k-3` together, spelled out as the congruence modulo `9`, the order-`(k-1)` product condition, and `N0`.

```lean
theorem deficitTwo_equiv_iff {k : Nat} (hk : 3 ≤ k) (p q : Int) :
    ((3 : Int) ^ k ∣ n2Resid (k - 3) p - n2Resid (k - 3) q) ∧
        ((3 : Int) ^ k ∣ n1Resid (k - 3) p - n1Resid (k - 3) q) ∧
          ((3 : Int) ^ k ∣ n0Resid (k - 3) p - n0Resid (k - 3) q) ↔
      ((3 : Int) ^ 2 ∣ p - q) ∧
        ((3 : Int) ^ (k - 1) ∣ (p - q) * (p + q + (3 : Int) ^ (k - 3))) ∧
          ((3 : Int) ^ k ∣ n0Resid (k - 3) p - n0Resid (k - 3) q)
```

## 138. `BTL-reconstruct` &mdash; covers 0.39

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

## 139. `J-cyclemin-prefix-bunched-eeoe` &mdash; covers 0.39

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

## 140. `J-small-cycle-census-eighteen` &mdash; covers 0.39

*Reads as: the claim asserts more than the declarations state (0.83).*

*Claim broader 0.83; declaration narrower 0.25; different result 0.07.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** No itinerary of length at most 18 is a Juggler cycle itinerary at any n ≥ 2, except that length 19 is not excluded here. Lengths ≤ 11 are J-small-cycle-census-eleven; lengths 12, 13, and 16 remain excluded at the residual floor 12; lengths 14, 15, 17, and 18 are excluded by cycle_finance_min_fifty_three (finance_excludes_length_fourteen and companions, packaged as no_cycle_itinerary_length_le_eighteen). Strengthened by J-small-cycle-census-nineteen. This is a Lean companion to Paper A Theorem 4.6, not a leftover-itinerary census, not an exclusion of length 19, not a no-cycle-of-any-length theorem, and not a halt theorem.

**Declaration.** `no_cycle_itinerary_length_le_eighteen` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:436`

> Census extension: no cycle itinerary of length at most `18`. Length `11` is the near-convergent killed by the floor `53`; `14`–`18` die by the same comparison.

```lean
theorem no_cycle_itinerary_length_le_eighteen {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 18) : ¬CycleItinerary n w
```

## 141. `OST-np-impulse-place` &mdash; covers 0.39

*Reads as: the claim asserts more than the declarations state (0.56).*

*Claim broader 0.56; declaration narrower 0.33; different result 0.09.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, the origin impulse A^r e3 equals (3 q_{r-1}, 3 q_{r-2}+q_{r-1}, q_r) with q_j=0 for j<0; this is the place-value dictionary for origin_particular, not a bound on L_0

**Declaration.** `iterateA_e3` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:776`

> `A^r e₃ = (3 q_{r-1}, 3 q_{r-2}+q_{r-1}, q_r)`. KNOWN place-value dictionary for `origin_particular`, not `L₀`.

```lean
theorem iterateA_e3 (r : ℕ) : iterateA r e3 = impulsePlace r
```

## 142. `BTA-x3-n0-sign` &mdash; covers 0.4

*Reads as: the claim asserts more than the declarations state (0.61).*

*Claim broader 0.61; declaration narrower 0.58; different result 0.12.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** N0(p)≡N0(-p) iff 3^k | N0(p)

**Declaration.** `n0_sign_survives` &mdash; kernel-checked, `BTCalculus/CubicN0Reduction.lean:118`

> `N0(p)` and `N0(-p)` agree modulo `3^k` exactly when `3^k` divides `N0(p)`: the sign survives the reduction only where the residual already vanishes.

```lean
theorem n0_sign_survives {k m : Nat} {p : Int} :
    (3 : Int) ^ k ∣ n0Resid m p - n0Resid m (-p) ↔
      (3 : Int) ^ k ∣ n0Resid m p
```

## 143. `J-cubic-critical-run-kernels` &mdash; covers 0.4

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

## 144. `J-cyclemin-closure-threshold` &mdash; covers 0.4

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

## 145. `BTA-x3-n3gate` &mdash; covers 0.43

*Reads as: the claim asserts more than the declarations state (0.76).*

*Claim broader 0.76; declaration narrower 0.74; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** cross-depth N3 agrees iff k<=2 min(m,n)+1 or m=n

**Declaration.** `n3_dvd_iff` &mdash; kernel-checked, `BTCalculus/CubicFibres.lean:139`

> Cross-depth `N3` criterion: for `m <= n`, `3^k` divides `N3(m) - N3(n)` exactly when `k <= 2m + 1` or the depths coincide.

```lean
theorem n3_dvd_iff {k m n : ℕ} (hmn : m ≤ n) :
    (3 : ℤ) ^ k ∣ n3Resid m - n3Resid n ↔
      k ≤ 2 * m + 1 ∨ m = n
```

## 146. `BTN-expanding-right-inverse` &mdash; covers 0.43

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

## 147. `J-cycle-quartic-formal-defect` &mdash; covers 0.43

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

## 148. `BTA-x3-Q-inv-one` &mdash; covers 0.44

*Reads as: a declaration is narrower than the claim (0.68).*

*Claim broader 0.38; declaration narrower 0.68; different result 0.06.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for t>=1, Q(1+3^t b)=Q(1+3^t c) iff 3^{K-1} divides b-c

**Declaration.** `q_one_family_dvd` &mdash; kernel-checked, `BTCalculus/MismatchedCubicInvariant.lean:125`

> On the family `1 + 3^t b` with `t >= 1` and `K >= 1`, `Q` values agree modulo `3^K` exactly when `3^(K-1)` divides `b - c`: one power of three is lost to the bracket unit.

```lean
theorem q_one_family_dvd {t K : Nat} (ht : 1 ≤ t) (hK : 1 ≤ K)
    (b c : Int) :
    (3 : Int) ^ K ∣ qCubic t (1 + (3 : Int) ^ t * b) -
        qCubic t (1 + (3 : Int) ^ t * c) ↔
      (3 : Int) ^ (K - 1) ∣ b - c
```

## 149. `BTA-fn-congr` &mdash; covers 0.45

*Reads as: the claim asserts more than the declarations state (0.56).*

*Claim broader 0.56; declaration narrower 0.27; different result 0.16.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** f equiv_k g iff 3^k divides (f-g)(n) for every integer n

**Declaration.** `equivK_iff_functionCongr` &mdash; kernel-checked, `BTCalculus/PolynomialFunctionsMod.lean:64`

> Prefix locality plus congruence preservation: ``≡_k`` is function congruence on all of ``ℤ``. Packed length-``k`` prefixes are a complete residue system modulo ``3^k``.

```lean
theorem equivK_iff_functionCongr (k : ℕ) (f g : ℤ[X]) :
    equivK k f g ↔ functionCongr k f g
```

## 150. `BTA-x3-Q-visible` &mdash; covers 0.45

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

## 151. `J-cyclemin-prefix-bunched-eooee` &mdash; covers 0.45

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

## 152. `OST-np-reset-prefix` &mdash; covers 0.45

*Reads as: the claim asserts more than the declarations state (0.65).*

*Claim broader 0.65; declaration narrower 0.31; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** for Γ_NP, if T_R(0)=0 then T_{RU}(0)=T_U(0); origin-reset prefixes do not create new terminals. This is particular_concat at c_R=0, not a bound on L_0

**Declaration.** `reset_prefix` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:609`

> Origin reset prefixes do not change the particular of a suffix. KNOWN `particular_concat` at `c_R=0`, not `L₀`.

```lean
theorem reset_prefix (r u : List ℤ) (hr : particularSum r = origin) :
    particularSum (r ++ u) = particularSum u
```

## 153. `PRC-section-I0-composite` &mdash; covers 0.45

*Reads as: the claim asserts more than the declarations state (0.62).*

*Claim broader 0.62; declaration narrower 0.27; different result 0.12.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** I_0(x)=3x. If |x|>1 then 3|x| is composite.

**Declaration.** `i0_not_prime_of_natAbs` &mdash; kernel-checked, `Problems/Primes/Residual.lean:28`

> If ``|x| > 1`` then ``3|x|`` is composite.

```lean
theorem i0_not_prime_of_natAbs {x : ℤ} (hx : 1 < x.natAbs) :
    ¬ Nat.Prime (3 * x.natAbs)
```

## 154. `BTC-word-simp-nf` &mdash; covers 0.46

*Reads as: the claim asserts more than the declarations state (0.88).*

*Claim broader 0.88; declaration narrower 0.18; different result 0.08.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** the simplifying-only fragment of WORD_REWRITE_RULES (the sixteen rules with simplifying=True: cancellations, the W/K3 stock, and I0→S) is terminating and locally confluent; every word has a unique syntactic normal form

**Declaration.** `unique_normal_form` &mdash; kernel-checked, `BTCalculus/WordSimpNewman.lean:329`

> Unique syntactic normal form of a simplifying-fragment word. Semantic canonicity of that irreducible is not claimed.

```lean
theorem unique_normal_form (t : Word) :
    ∃ n, Normal n ∧ ReflTransGen Step t n ∧
      ∀ n', Normal n' → ReflTransGen Step t n' → n' = n
```

## 155. `BTN-expanding-lambda` &mdash; covers 0.46

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

## 156. `BTN-carry-gain-3` &mdash; covers 0.47

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

## 157. `J-fate-chernoff-count` &mdash; covers 0.47

*Reads as: the claim asserts more than the declarations state (0.54).*

*Claim broader 0.54; declaration narrower 0.3; different result 0.04.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** Paper C Lemma 8.2 (Chernoff), exact form. A word w of length d is L-bad if o_t(w) log_2 3 − t > −L for every 1 ≤ t ≤ d (LBad). For C ≥ 5, p_C = (1 − 1/C)/log_2 3, e(C) = C D(p_C‖1/2)/log 2, and every d ≥ 1 with d ≥ C L: #{L-bad words of length d} ≤ 2^d · 2^{−e(C) L} (LBad_count_le). Engine: the constant weight has weightGen (1+x)^d (weightGen_one), so the Markov tilt weight_markov of RateFreeDensity gives #{o(w) ≥ k} ≤ (1+x)^d/x^k for x ≥ 1 (count_oddCount_ge_le), hence #{o(w) ≥ p d} ≤ (1+x)^d/x^{pd} with a real exponent (count_oddCount_ge_real_le); at x = p/(1−p) this is exp(d h(p)) with h the binary entropy (tilt_value, count_oddCount_ge_le_exp), i.e. 2^d exp(−d D(p‖1/2)) (count_oddCount_ge_le_kl); D(p‖1/2) ≥ 0 by log x ≤ x − 1 (klHalf_nonneg); an L-bad word has o_d ≥ p_C d when d ≥ CL (  *(truncated; read the ledger row)*

**Declaration.** `LBad_count_le` &mdash; kernel-checked, `Problems/Juggler/FateChernoff.lean:212`

> **Lemma 8.2 (Chernoff), exact form.** For `C ≥ 5` and `d ≥ C L` with `d ≥ 1`, the number of `L`-bad words of length `d` is at most `2^d · 2^{-e(C) L}`.

```lean
theorem LBad_count_le (L C : ℝ) (d : ℕ) (hC : 5 ≤ C) (hd : C * L ≤ d) (hd1 : 1 ≤ d) :
    (#{w ∈ allWords d | LBad L w} : ℝ) ≤ 2 ^ d * (2 : ℝ) ^ (-(chernoffExponent C * L))
```

## 158. `BTN-sdr-multi-trit` &mdash; covers 0.48

*Reads as: the claim asserts more than the declarations state (0.69).*

*Claim broader 0.69; declaration narrower 0.54; different result 0.15.  Tag EXACT — LEAN VERIFIED, trust mixed.*

**Row.** r-way trit addition s'=D(s+a_1+⋯+a_r) is F_{1,U_r}: a trit sum of length r has absolute value at most r, so the λ=1 box |s|≤⌊r/2⌋ is invariant. The count 2⌊r/2⌋+1 equals 1,3,3,5 for r=1,2,3,4.

**Declarations.** `multi_trit_carry_bound` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidual.lean:418`

> r-way trit addition is the ``λ=1`` family on ``U_r``.

```lean
theorem multi_trit_carry_bound {s : ℤ} {inputs : List ℤ}
    (hs : s.natAbs ≤ inputs.length / 2)
    (htrits : ∀ a ∈ inputs, isTrit a) :
    (DZ (s + inputs.sum)).natAbs ≤ inputs.length / 2
```

**And.** `multi_trit_carry_minimal` &mdash; compiler-checked, `Problems/BalancedTernary/SignedDigitResidual.lean:426`

> The residual state count `2 * (r / 2) + 1` at `r = 1, 2, 3, 4` is `1, 3, 3, 5`.

```lean
theorem multi_trit_carry_minimal :
    2 * (1 / 2) + 1 = 1 ∧
      2 * (2 / 2) + 1 = 3 ∧
      2 * (3 / 2) + 1 = 3 ∧
      2 * (4 / 2) + 1 = 5
```

## 159. `J-cycle-induced-count-determinant` &mdash; covers 0.48

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

## 160. `BTC-push-in-S-peak` &mdash; covers 0.49

*Reads as: the claim asserts more than the declarations state (0.77).*

*Claim broader 0.77; declaration narrower 0.4; different result 0.09.  Tag EXACT — LEAN VERIFIED, trust kernel.*

**Row.** the named carry-free push-in system (unary D(S(t))→t plus S(Add(t,u))→Add(S(t),S(u)) and congruence, no D-through-Add) is not locally confluent: D(S(Add(X,Y))) has two distinct irreducibles Add(X,Y) and D(Add(S(X),S(Y))); both evaluate to X+Y

**Declaration.** `pushIn_not_locally_confluent` &mdash; kernel-checked, `BTCalculus/RewriteAddBoundary.lean:212`

> The named carry-free push-in system is not locally confluent: `D(S(X+Y))` has two distinct irreducibles.

```lean
theorem pushIn_not_locally_confluent :
    PushInStep pushInPeak (.add .X .Y) ∧
      PushInStep pushInPeak (.D (.add (.S .X) (.S .Y))) ∧
      AddTree.add .X .Y ≠ .D (.add (.S .X) (.S .Y)) ∧
      (∀ u, ¬ PushInStep (.add .X .Y) u) ∧
      (∀ u, ¬ PushInStep (.D (.add (.S .X) (.S .Y))) u)
```

