# Declaration review queue

Rows where one candidate leads its file clearly.  Each entry is the ledger row's own
statement beside the candidate's docstring; the question is only whether they say the
same thing.  Measured against all 142 resolved rows the scorer gets
55 of the 67 it fires on right, 82% precise, so roughly one in
6 below is wrong.
21 rows below, of 123 unresolved.


Two failure modes are not scored at all, and both record a part as the whole.

The row may be broader than the candidate: `BTC-select3` reads "select3 represents
every Trit->Z map; abs/min/max" -- four theorems, of which `select3_represents` is
one.  If a row says "and", ";" or lists several claims, it belongs in neither column.

Or the candidate may be narrower than the row, with nothing in the prose to say so.
`BTN-sdrg-lambda1-interval` claims every integer with |s| <= m/2 is reachable, and
`lambda1_interval_reachable` reads "every nonnegative point" -- true, and half of it;
its `n : ℕ` is the tell, and a sibling proves the rest.  That is why the statement is
printed below every candidate, docstring or not.

Answer by adding `decl` and `lean_trust` to the row in `docs/theory/theorem_ledger.json`.

## 1. `BTC-select3`

**Row.** select3 represents every Trit→ℤ map; abs/min/max

**Candidate.** `select3_represents` &mdash; kernel-checked, `BTCalculus/Select.lean:33`

> Every function ``Trit → ℤ`` is ``select3`` of its three values.

```lean
theorem select3_represents (f : Trit → ℤ) (c : Trit) :
    f c = select3 c (f Trit.minus) (f Trit.zero) (f Trit.plus)
```

*Runners-up: `select3_minus` (0.182), `select3_zero` (0.182)*

*If this row describes a definition rather than a theorem: `select3`, `absZ`*

## 2. `BTA-x3-newton`

**Row.** Newton coordinates of a cubic and of the residual family of x^3

**Candidate.** `newton_cubicResid` &mdash; kernel-checked, `BTCalculus/CubicResidual.lean:269`

> Newton coordinates of the residual family, written in terms of `m` and `p`.

```lean
theorem newton_cubicResid (m : ℕ) (p : ℤ) :
    newtonCoords ((3 : ℤ) ^ (2 * m)) ((3 : ℤ) ^ (m + 1) * p)
        (3 * p ^ 2) (iterDZ m (p ^ 3)) =
      (iterDZ m (p ^ 3),
        (3 : ℤ) ^ (2 * m) + (3 : ℤ) ^ (m + 1) * p + 3 * p ^ 2,
        2 * (3 : ℤ) ^ (m + 1) * (p + (3 : ℤ) ^ m),
        2 * (3 : ℤ) ^ (2 * m + 1))
```

*Runners-up: `eval_cubicResid_iter` (0.3), `residualAlong_cubic_family` (0.25)*

*If this row describes a definition rather than a theorem: `cubicResid`, `newtonCoords`*

## 3. `BTA-x3-n2`

**Row.** same-depth N2 is 3^{k-m-1}|(p-q); injective on P_m if 2m+1<=k

**Candidate.** `sameDepth_n2_injective` &mdash; kernel-checked, `BTCalculus/CubicFibres.lean:101`

```lean
theorem sameDepth_n2_injective {k m : ℕ} {p q : ℤ}
    (hp : balWidth m p) (hq : balWidth m q)
    (hmk : 2 * m + 1 ≤ k)
    (hN2 : (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m q) :
    p = q
```

*Runners-up: `sameDepth_n2` (0.5), `sameDepth_n2_of_le` (0.5)*

*Careful: `sameDepth_n2_injective` extends `sameDepth_n2`, and in this corpus a longer name is usually a special case of the shorter one. Twice the shorter name was the answer and the scorer ranked it second, because the specialisation happened to be the documented one.*

*If this row describes a definition rather than a theorem: `balWidth`, `n2Resid`*

## 4. `BTA-x3-sign`

**Row.** odd pair: N2 iff N1; N0 iff 3^k divides D^m(p^3)

**Candidate.** `n3_dvd_iff` &mdash; kernel-checked, `BTCalculus/CubicFibres.lean:128`

```lean
theorem n3_dvd_iff {k m n : ℕ} (hmn : m ≤ n) :
    (3 : ℤ) ^ k ∣ n3Resid m - n3Resid n ↔
      k ≤ 2 * m + 1 ∨ m = n
```

*Runners-up: `n2Resid_diff` (0.0), `n1Resid_diff` (0.0)*

*If this row describes a definition rather than a theorem: `balWidth`, `n2Resid`*

## 5. `BTA-x3-n0-vis`

**Row.** D^t(u^3) mod 3^k is determined by u mod 3^{max(1,t+k-1)}

**Candidate.** `n0_of_cube_mod` &mdash; kernel-checked, `BTCalculus/CubicN0Reduction.lean:148`

```lean
theorem n0_of_cube_mod {t k : Nat} {u v : Int}
    (h : (3 : Int) ^ (t + k) ∣ u ^ 3 - v ^ 3) :
    (3 : Int) ^ k ∣ n0Resid t u - n0Resid t v
```

*Runners-up: `n0_visible_mod` (0.111), `DZ_mul_three` (0.0)*

## 6. `BTL-block-shift`

**Row.** block shift law: for a word w of length j the section operators send the state (3^j d, 3^{j+i}) to (d + 3^i packWord(w), 3^{j+i}), every such word survives, and at i = 0, j = e the 3^e words of length e reach exactly the states d + t for t in the balanced window W_e = [-(3^e-1)/2, (3^e-1)/2]; the shift is the balanced value packWord(w) an

**Candidate.** `residualAlong_linState_pow` &mdash; kernel-checked, `BTCalculus/PadicLiftingState.lean:302`

> **Target 4.** The block shift law. A singular branch with derivative valuation at least `w.length` is fully ternary along `w`, and the state it reaches is shifted by the *balanced value* of the word, scaled by the excess `3 ^ i`: 𝔇_w (3^j d + 3^(j+i) x) = (d + 3^i · packWord w) + 3^(j+i) x, j = |w|. At `i = 0` this is the leaf law: the `3 ^ e` words of length `e` reach the states `d + packWord w`, and `packWord` is injective on words of a fixed length, so those shifts run over a complete residue system modulo `3 ^ e`. That is what makes the shifted family separate residues; note the shift is the balanced value of the word and not its digit sum.

```lean
theorem residualAlong_linState_pow :
    ∀ (w : List ℤ) (i : ℕ) (d : ℤ),
      residualAlong w (linState (3 ^ w.length * d) (3 ^ (w.length + i)))
        = linState (d + 3 ^ i * packWord w) (3 ^ (w.length + i))
  | [], i, d => by simp [residualAlong, packWord_nil]
  | a :: w, i, d => by
```

*Runners-up: `outputAlong_linState_pow` (0.109), `linState_root_iff` (0.083)*

*If this row describes a definition rather than a theorem: `linState`, `henselTrit`*

## 7. `BTM-x3-depth`

**Row.** for every balanced-Monna endpoint pair u=zeta+2*3^n, v=zeta-2*3^n one has u^3-v^3=4*3^n(3 zeta^2+4*3^{2n}) and therefore t=v_3(u^3-v^3)=n+min(1+2 v_3(zeta), 2n), or t=3n when zeta=0; the two arguments of the minimum have opposite parity whenever zeta is nonzero

**Candidate.** `monnaEndpoint_val_parity` &mdash; kernel-checked, `BTCalculus/MonnaEndpointCube.lean:93`

> The two arguments of the depth minimum have opposite parity when `ζ ≠ 0`.

```lean
theorem monnaEndpoint_val_parity (n : ℕ) {ζ : ℚ} (_hζ : ζ ≠ 0) :
    Odd (1 + 2 * padicValRat 3 ζ) ∧ Even (2 * (n : ℤ))
```

*Runners-up: `monnaEndpoint_cube_val_of_ne` (0.143), `monnaEndpoint_factor_ne` (0.133)*

*If this row describes a definition rather than a theorem: `monnaEndpointU`, `monnaEndpointV`*

## 8. `BTC-constructor-sum-class`

**Row.** for U,V,W in {S,I+,I-,N}, the identity U(x)+V(y)=W(x+y) holds for all integers iff it is one of the eight concrete triples (S,S,S), (N,N,N), (I+,S,I+), (S,I+,I+), (I-,S,I-), (S,I-,I-), (I+,I-,S), (I-,I+,S); same-sign I+ or I- and mixed N+S are not constructor identities

**Candidate.** `exactTriple_characterization` &mdash; kernel-checked, `BTCalculus/RewriteAddBoundary.lean:108`

> The six parameterized rows, written as the eight concrete triples (`I_a` is a parameter in the informal statement).

```lean
theorem exactTriple_characterization (U V W : AffineCtor) :
    exactTriple U V W ↔
      (U = S ∧ V = S ∧ W = S) ∨
      (U = N ∧ V = N ∧ W = N) ∨
      (U = Ip ∧ V = S ∧ W = Ip) ∨
      (U = S ∧ V = Ip ∧ W = Ip) ∨
      (U = Im ∧ V = S ∧ W = Im) ∨
      (U = S ∧ V = Im ∧ W = Im) ∨
```

*Runners-up: `apply_add_eq_iff` (0.077), `pushIn_peak_semantic` (0.059)*

*If this row describes a definition rather than a theorem: `exactTriple`, `DLocal`*

## 9. `BTN-carry-gain-3`

**Row.** The synthetic map T_3(c,d)=3 DZ(c+2d) satisfies c_n=3n along the all-+1 word, so the residual set is unbounded. This is not value-preserving normalization.

**Candidate.** `carryGain3_eq` &mdash; kernel-checked, `Problems/BalancedTernary/FiniteStateDynamics.lean:143`

> `carryGain3 n = 3n` along the all-`+1` word.

```lean
theorem carryGain3_eq (n : ℕ) : carryGain3 n = 3 * (n : ℤ)
```

*Runners-up: `carryGain3_unbounded` (0.071), `isTrit_natAbs` (0.062)*

*If this row describes a definition rather than a theorem: `doubledNext`, `doubledOut`*

## 10. `BTN-sdr-multi-trit`

**Row.** r-way trit addition s'=D(s+a_1+⋯+a_r) is F_{1,U_r}: a trit sum of length r has absolute value at most r, so the λ=1 box |s|≤⌊r/2⌋ is invariant. The count 2⌊r/2⌋+1 equals 1,3,3,5 for r=1,2,3,4.

**Candidate.** `multi_trit_carry_bound` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidual.lean:373`

> r-way trit addition is the ``λ=1`` family on ``U_r``.

```lean
theorem multi_trit_carry_bound {s : ℤ} {inputs : List ℤ}
    (hs : s.natAbs ≤ inputs.length / 2)
    (htrits : ∀ a ∈ inputs, isTrit a) :
    (DZ (s + inputs.sum)).natAbs ≤ inputs.length / 2
```

*Runners-up: `lambda2_box_invariant` (0.118), `DZ_of_trit` (0.083)*

*If this row describes a definition rather than a theorem: `signedNext`, `signedOut`*

## 11. `BTN-sdr-escape-general`

**Row.** If λ≥3 and |u|≥2 then the constant-control orbit of F_{λ,U} from 0 is unbounded: at λ=3 one has s'=s+u-lsd(s+u) so each step moves by at least 1; at λ≥4 the step is strictly expanding on the matching ray.

**Candidate.** `gain3_control2_unbounded` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidual.lean:105`

```lean
theorem gain3_control2_unbounded (B : ℕ) :
    ∃ n : ℕ, B < (carryGain3 n).natAbs
```

*Runners-up: `lsdZ_le_one` (0.083), `gain3_control2_eq` (0.077)*

*If this row describes a definition rather than a theorem: `signedNext`, `signedOut`*

## 12. `J-near-tight-scale-bounds`

**Row.** The local Juggler remainder satisfies 0≤ρ<2T+1, hence η=ρ/T^2 < 2/T + 1/T^2 and 1+η < ((T+1)/T)^2. For the mixed itinerary OOE, 1+q = (1+η0)^3 (1+η1)^2 (1+η2)^4, and 1+q is strictly below the successor-ratio product ((T0+1)/T0)^6 ((T1+1)/T1)^4 ((T2+1)/T2)^8. The same bound at a successor start y depends only on the itinerary of y.

**Candidate.** `large_lambda_successor_q_bound` &mdash; kernel-checked, `Problems/Juggler/NearTightScale.lean:201`

> The `OOE` successor bound depends only on the itinerary of `y`. A large-`λ` predecessor enters only by making `y` large.

```lean
theorem large_lambda_successor_q_bound {y : ℕ}
    (hw : follows y ooeWord) :
    slackNum y ooeWord *
        floorPower y ^ 6 *
        floorPower (floorPower y) ^ 4 *
        floorPower (floorPower (floorPower y)) ^ 8 <
      slackDen y ooeWord *
        (floorPower y + 1) ^ 6 *
```

*Runners-up: `ooe_one_plus_slack_lt_succ_ratio` (0.15), `even_remainder_bound` (0.118)*

## 13. `J-finite-progress-boundary`

**Row.** Universal FiniteProgress for starts above one implies universal reachability of one. Every even start n ≥ 2 and every odd start n ≥ 2 whose first image is even has FiniteProgress; consequently, any start without FiniteProgress is odd and has an odd first image. This isolates the automatic odd-to-odd frontier without proving universal prog

**Candidate.** `odd_even_finiteProgress` &mdash; kernel-checked, `Problems/Juggler/Progress.lean:78`

> Odd `n ≥ 2` whose first image is even has finite progress: `OE`.

```lean
theorem odd_even_finiteProgress {n : ℕ} (hn : 2 ≤ n)
    (hodd : n % 2 = 1) (heven : floorPower n % 2 = 0) :
    FiniteProgress n
```

*Runners-up: `finiteProgress_of_imageLt` (0.208), `finiteProgress_of_not_odd_odd` (0.2)*

*If this row describes a definition rather than a theorem: `FiniteProgress`*

## 14. `J-first-even-overshoots`

**Row.** On a MinimalNonTerm or CycleMin start, the first even residual always overshoots: T(O^a E)(n) > n and the even residual sits at or above (n+1)^2. The return-to-n cell of the first-even dichotomy is an even-count-1 cycle itinerary, now excluded by no_cycle_itinerary_even_count_le_three. Lean theorems minimal_first_even_overshoots and cycle

**Candidate.** `minimal_first_even_overshoots` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:649`

> On a `MinimalNonTerm` start the first even residual always overshoots. The return cell is an even-count-1 cycle itinerary. This is not a halt theorem.

```lean
theorem minimal_first_even_overshoots {n a : ℕ}
    (h : MinimalNonTerm n) (hw : follows n (oddEvenBlock a 1)) :
    (n + 1) ^ 2 ≤ image n (List.replicate a Branch.odd) ∧
      n < image n (oddEvenBlock a 1)
```

*Statement names: `minimal_first_even_overshoots`, `cycleMin_first_even_overshoots`*

*Runners-up: `cycleMin_first_even_overshoots` (0.3), `cycleMin_max_ge_succ_sq` (0.278)*

*If this row describes a definition rather than a theorem: `evenCount`*

## 15. `J-cyclemax-succ-sq`

**Row.** On a CycleMin start n ≥ 2 the cycle maximum satisfies (n+1)^2 ≤ M. Equivalently, on a CycleMax the rotated minimum m satisfies (m+1)^2 ≤ M, so T(M) > m. The first-cell family m^2 < M < (m+1)^2 is impossible. cycle_distinguished_order_succ_sq is the distinguished-order package with that scale. Corollary of cycleMin_first_even_overshoots: t

**Candidate.** `cycleMin_max_ge_succ_sq` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:734`

> On a cycle minimum the maximum sits at or above `(n+1)^2`. The first even residual already overshoots, so the first-cell family `n^2 < M < (n+1)^2` is impossible. Not a halt theorem.

```lean
theorem cycleMin_max_ge_succ_sq {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ i < w.length,
      (∀ j < w.length, floorPower^[j] n ≤ floorPower^[i] n) ∧
        floorPower^[i] n % 2 = 0 ∧
          (n + 1) ^ 2 ≤ floorPower^[i] n
```

*Statement names: `cycle_distinguished_order_succ_sq`, `cycleMin_first_even_overshoots`, `cycleMin_max_ge_succ_sq`, `cycleMax_min_succ_sq_le`, `cycleMax_landing_gt_min`, `cycleMax_exists_min_succ_sq`*

*Runners-up: `cycleMax_min_succ_sq_le` (0.222), `minimal_first_even_overshoots` (0.214)*

*If this row describes a definition rather than a theorem: `evenCount`*

## 16. `J-cyclemin-transport-oo`

**Row.** On a CycleMin, after the first O^a E with a ≥ 2, an immediate odd run of length at least two overshoots the landing y = T_{O^a E}(n) > n: the next two-odd residual is at least (y+1)^2, hence at least (n+2)^2. Lean: cycleMin_transport_second_oo, cycleMin_transport_second_oo_ge in CycleMinObstruction.lean. The second residual lies outside t

**Candidate.** `cycleMin_transport_second_oo` &mdash; kernel-checked, `Problems/Juggler/CycleMinObstruction.lean:60`

> After the first `O^a E` on a `CycleMin`, an immediate odd run of length at least two overshoots the landing `y`: the next two-odd residual is at least `(y+1)^2`.

```lean
theorem cycleMin_transport_second_oo {n a b : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (_ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : CycleMin n
      (oddEvenBlock a 1 ++ List.replicate b Branch.odd ++ v)) :
    (image n (oddEvenBlock a 1) + 1) ^ 2 ≤
      image (image n (oddEvenBlock a 1)) (List.replicate 2 Branch.odd)
```

*Statement names: `cycleMin_transport_second_oo`, `cycleMin_transport_second_oo_ge`*

*Runners-up: `cycleMin_transport_second_oo_ge` (0.27), `follows_replicate_odd_of_le` (0.029)*

## 17. `J-ce-third-residual-preimages`

**Row.** If n ≥ 2 follows OOEOOEOO, then T_OOEOOEOO(n) < n^3 because x^{256} ≤ n^{729} forbids n^3 ≤ x (768 > 729). If n follows OOEOOEOOE, then T_OOEOOEOOE(n) < n^2 because y^{512} ≤ n^{729} forbids n^2 ≤ y (1024 > 729). A CE that follows OOEOOE follows OOEOOEOO. On MinimalNonTerm a completed third OOE cannot land even: an even landing below n^2 

**Candidate.** `minimal_ooeooeooe_not_even_landing` &mdash; kernel-checked, `Problems/Juggler/Escape.lean:309`

> On a CE, a completed third `OOE` cannot land even: the landing is below `n^2`, so an even landing is descent. This is not a PE theorem.

```lean
theorem minimal_ooeooeooe_not_even_landing {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOEOOE) :
    image n itineraryOOEOOEOOE % 2 = 1
```

*Runners-up: `minimal_ooeooeooeoe_not_even_landing` (0.32), `minimal_ooeooeooeoeo_not_even` (0.222)*

*If this row describes a definition rather than a theorem: `itineraryOOEOOEOO`, `itineraryOOEOOEOOE`*

## 18. `J-cube-odd-even-reset`

**Row.** If n ≥ 2 and n^2 ≤ x < n^3 with x odd, then n^3 ≤ T(x) < n^5 and T(x)^2 < n^9. If T(x) is even, the first return satisfies n ≤ T^2(x) < x < n^3 and T^2(x)^4 < n^9. If T(x) is odd, then x < T^2(x) and n^4 ≤ T^2(x). An even reset that is itself even and already below n^2 is FiniteProgress; on MinimalNonTerm that case is impossible. This is 

**Candidate.** `aboveAnchor_not_odd_even` &mdash; kernel-checked, `Problems/Juggler/MinimumRelative.lean:103`

> An `OE` start cannot stay at or above the anchor: the first even residual is below `n^2`.

```lean
theorem aboveAnchor_not_odd_even {n : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (h : AboveAnchor n (.odd :: .even :: v)) : False
```

*Runners-up: `aboveAnchor_isolatedOddSurvival` (0.037), `even_ge_sq_of_aboveAnchor` (0.032)*

*If this row describes a definition rather than a theorem: `AboveAnchor`*

## 19. `J-small-cycle-census-ten`

**Row.** No itinerary of length at most ten is a Juggler cycle itinerary at any n ≥ 2; equivalently a nontrivial Juggler cycle, if one exists, has period at least eleven. Lengths ≤ 8 are the census J-small-cycle-census-eight; lengths 9 and 10 are excluded by the finance inequality at the residual floor 12 (no_cycle_itinerary_length_nine, no_cycle_

**Candidate.** `no_cycle_itinerary_length_le_ten` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:224`

> Census extension: no cycle itinerary of length at most `10`. Lengths `≤ 8` are the Lean census; `9` and `10` are the finance inequality.

```lean
theorem no_cycle_itinerary_length_le_ten {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 10) : ¬CycleItinerary n w
```

*Statement names: `no_cycle_itinerary_length_nine`, `no_cycle_itinerary_length_ten`, `no_cycle_itinerary_length_le_ten`*

*Runners-up: `finance_excludes_length_eleven` (0.207), `finance_contradicts_min_two_hundred_sixty_one` (0.206)*

*If this row describes a definition rather than a theorem: `financeRows53`, `financeRows257`*

## 20. `J-cyclemin-defect-finance-kill`

**Row.** The defect-sum finance inequality (the certified identity of Paper A Theorem 4.6, previously human) and the walk-charge kill criterion (Theorem 5.9 mechanism), Lean end to end (DefectFinance.lean). Finance: on a CycleMin cycle with minimum n ≥ 400, 1 − 2^L/3^o ≤ (6/5)·Σ_k 1/(x_k·log x_k) (cycleMin_defect_finance). Ingredients all Lean: pe

**Candidate.** `cycleMin_hug_kill_criterion` &mdash; kernel-checked, `Problems/Juggler/DefectFinance.lean:439`

> **The walk-charge kill criterion** (Paper A Theorem 5.9 mechanism, Lean form): every minimum-based cycle at `n ≥ 400` with positive reduced log-base `ν = log n − D` must satisfy `1 − 2^L/3^o ≤ (6/5) · Σ_k g(hugWeight k)` with the charge evaluated at the reduced base. The kill tables verify the numeric failure of this inequality per surviving length; that evaluation stays verified computation, the implication is Lean.

```lean
theorem cycleMin_hug_kill_criterion {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w)
    (hν : 0 < Real.log n - transportDeficit n w) :
    1 - (2 : ℝ) ^ w.length / 3 ^ oddCount w ≤
      1.2 * ∑ k ∈ Finset.range w.length,
        stateCharge (Real.log n - transportDeficit n w) (hugWeight k)
```

*Statement names: `cycleMin_defect_finance`, `neg_log_one_sub_le_sixth`, `log_floorPower_even_ge_sub`, `log_floorPower_odd_ge_sub`, `log_floorPower_even_le`, `log_floorPower_odd_le`, `cycleMin_log_le_weight`, `cycleMin_charge_prefix`, `cycleMin_hug_kill_criterion`*

*Runners-up: `cycleMin_defect_finance` (0.134), `log_floorPower_even_ge_sub` (0.11)*

## 21. `J-loglog-clock-band-word-forced-lean`

**Row.** Inside the hug band the parity letter is forced. band_step_forced_odd: from u < 1 a step staying in [0, 1 + alphaClock) must be the odd one, v = u + alphaClock (the even step goes negative). band_step_forced_even: from 1 <= u it must be the even one, v = u - 1 (the odd step exceeds the band). band_successor_unique: a band-confined walk ha

**Candidate.** `band_successor_unique` &mdash; kernel-checked, `Problems/Juggler/LogLogClock.lean:152`

> **The band walk is the rotation by `alphaClock`.** A walk confined to the hug band has a single admissible successor at every point, given by the lift of the rotation: `u + alphaClock` below `1`, `u - 1` above. So the parity word of a band-confined orbit is determined by nothing but the starting walk — it is the mechanical word of the rotation, the hug itinerary.

```lean
theorem band_successor_unique {u v w : ℝ} (_h0 : 0 ≤ u) (_h1 : u < 1 + alphaClock)
    (hv : WalkStep u v) (hvin : 0 ≤ v ∧ v < 1 + alphaClock)
    (hw : WalkStep u w) (hwin : 0 ≤ w ∧ w < 1 + alphaClock) : v = w
```

*Statement names: `band_step_forced_odd`, `band_step_forced_even`, `band_successor_unique`*

*Runners-up: `band_step_forced_odd` (0.263), `band_step_forced_even` (0.263)*

*If this row describes a definition rather than a theorem: `WalkStep`*

